# Copyright (c) 2013-2017 Wind River Systems, Inc.
#
# SPDX-License-Identifier: Apache-2.0
#

# vim: tabstop=4 shiftwidth=4 softtabstop=4

# All Rights Reserved.
#

"""
Glance RAW caching feature ache
"""

import logging
from oslo_config import cfg

from glance.common import exception
from glance.common import imageutils
from glance.context import RequestContext
import glance.registry.client.v1.api as registry
from glance_store._drivers import rbd as rbd_store_driver
from glance_store import exceptions as store_exceptions
from keystoneclient.v2_0 import client as keystoneclient
from oslo_concurrency import lockutils
from oslo_concurrency import processutils
from oslo_utils import encodeutils
from oslo_utils import timeutils
from oslo_utils import units

try:
    import rados
    import rbd
except ImportError:
    rados = None
    rbd = None

import errno
import os
import shutil
import signal
import stat
import sys
import time
import traceback
import urllib

import eventlet
import json

from ctypes import c_bool
from ctypes import c_char
from multiprocessing import Array
from multiprocessing import Condition
from multiprocessing import Event
from multiprocessing import Queue
from multiprocessing.queues import Empty
from multiprocessing import Value

try:
    from fm_api import constants as fm_const
    from fm_api import fm_api
except ImportError:
    fm_const = None
    fm_api = None

from glance import i18n

_ = i18n._
_LE = i18n._LE
_LI = i18n._LI
_LW = i18n._LW

LOG = logging.getLogger(__name__)

cache_raw_task_opts = [
    cfg.StrOpt('cache_raw_conversion_dir',
               default=None,
               help="The temporary folder for doing conversions."
                    " Warning: Content of this folder is removed"
                    " when glance-api starts"),
]

CONF = cfg.CONF
CONF.register_opts(cache_raw_task_opts)

_RBD_STORE = 'rbd'
_RETRY_COUNT_BEFORE_ERROR = 30
_RETRY_SLEEP_S = 10
_WAIT_FOR_IMAGE_RELEASE = 1200

try:
    LOCK_DIR = rbd_store_driver.LOCK_DIR
    LOCK_PREFIX = rbd_store_driver.LOCK_PREFIX
    LOCK_RBD_USAGE = rbd_store_driver.LOCK_PREFIX
    DEFAULT_POOL_RESERVATION_FILE = \
        rbd_store_driver.DEFAULT_POOL_RESERVATION_FILE
except AttributeError:
    # For unit tests, upstream RBD driver does not have these
    LOCK_DIR = "/tmp"
    LOCK_PREFIX = "glance_"
    LOCK_RBD_USAGE = "rbd_cluster_usage"
    DEFAULT_POOL_RESERVATION_FILE = '/tmp/glance-space-reservations'

# keep all the caching jobs arguments in a small list and execute them
# serially, also keep context info about current conversion, useful for delete
g_job_queue = None    # remaining conversion jobs
g_image_id = None     # image id for current conversion, needed by image delete
g_done_event = None   # sent when conversion is finished, needed by image del
g_is_cache_raw_enabled = None  # feature is enabled or not
g_delete_lock = None  # Wait for images that are caching before deleting them


def initialize():
    global g_job_queue, g_done_event, g_image_id
    global g_is_cache_raw_enabled, g_delete_lock
    g_job_queue = Queue()
    g_done_event = Event()
    g_image_id = Array(c_char, 100)
    g_is_cache_raw_enabled = Value(c_bool, False)
    g_delete_lock = Condition()


def _clean_dir_content(path):
    """Delete everything from a folder or create it if non-existent"""
    if not os.path.exists(path):
        os.makedirs(path)
    for f in os.listdir(path):
        file_path = os.path.join(path, f)
        try:
            if os.path.isfile(file_path):
                os.unlink(file_path)
            elif os.path.isdir(file_path):
                shutil.rmtree(file_path)
        except OSError as e:
            LOG.error(_LE("Error cleaning %(path)s content: %(reason)s"),
                      {"path": path, "reason": e})


def _is_blk_device(dev):
    try:
        if stat.S_ISBLK(os.stat(dev).st_mode):
            return True
        return False
    except Exception:
        LOG.debug('Path %s not found in is_blk_device check', dev)
        return False


def _check_for_odirect_support(src, dest, flag='oflag=direct'):
    """Check whether O_DIRECT flag is supported"""
    try:
        cmd = ('dd', 'count=0', 'if=%s' % src, 'of=%s' % dest, flag)
        processutils.execute(*cmd)
        return True
    except processutils.ProcessExecutionError:
        return False


def _convert_image(source, dest, out_format):
    """Convert image to other format.

    Modified from Cinder
    """

    cmd = ('env', 'LC_ALL=C', 'qemu-img', 'convert',
           '-O', out_format, source, dest)

    # Check whether O_DIRECT is supported and set '-t none' if it is
    # This is needed to ensure that all data hit the device before
    # it gets unmapped remotely from the host for some backends
    # Reference Bug: #1363016

    # NOTE(jdg): In the case of file devices qemu does the
    # flush properly and more efficiently than would be done
    # setting O_DIRECT, so check for that and skip the
    # setting for non BLK devs
    if (_is_blk_device(dest) and
            _check_for_odirect_support(source, dest, 'oflag=direct')):
        cmd = ('env', 'LC_ALL=C', 'qemu-img', 'convert',
               '-t', 'none',
               '-O', out_format, source, dest)
    LOG.info(_LI("Converting source: %(source)s to dest: %(dest)s "
                 "type: %(out_format)s") %
             {'source': source, 'dest': dest, 'out_format': out_format})
    start_time = timeutils.utcnow()
    processutils.execute(*cmd)
    duration = timeutils.delta_seconds(start_time, timeutils.utcnow())

    # NOTE(jdg): use a default of 1, mostly for unit test, but in
    # some incredible event this is 0 (cirros image?) don't barf
    if duration < 1:
        duration = 1
    fsz_mb = os.stat(source).st_size / units.Mi
    mbps = (fsz_mb / duration)
    msg = ("Image conversion details: src %(src)s, size %(sz).2f MB, "
           "duration %(duration).2f sec, destination %(dest)s")
    LOG.debug(msg, {"src": source,
                    "sz": fsz_mb,
                    "duration": duration,
                    "dest": dest})

    msg = _("Converted %(sz).2f MB image at %(mbps).2f MB/s")
    LOG.info(msg, {"sz": fsz_mb, "mbps": mbps})


def _qemu_img_info(path):
    """Return a object containing the parsed output from qemu-img info."""
    cmd = ('env', 'LC_ALL=C', 'qemu-img', 'info', path)
    out, _err = processutils.execute(*cmd)
    return imageutils.QemuImgInfo(out)


def _convert_to_volume_format(src, dest, volume_format, image_id):
    """Do the conversion safely"""
    try:
        data = _qemu_img_info(src)
    except processutils.ProcessExecutionError:
        raise exception.CachingToRawException(
            reason=_("qemu-img is not installed. "
                     "caching of %s is aborted") % image_id)

    fmt = data.file_format
    if fmt is None:
        raise exception.ImageUnacceptable(
            reason=_("'qemu-img info' parsing failed."),
            image_id=image_id)

    backing_file = data.backing_file
    if backing_file is not None:
        raise exception.ImageUnacceptable(
            image_id=image_id,
            reason=_("fmt=%(fmt)s backed by:%(backing_file)s")
            % {'fmt': fmt, 'backing_file': backing_file, })

    if fmt == volume_format:
        raise exception.ConvertToSameFormat(
            image_id=image_id,
            fmt=fmt)

    LOG.debug("%s was %s, caching to %s ", image_id, fmt, volume_format)
    _convert_image(src, dest, volume_format)

    data = _qemu_img_info(dest)
    if data.file_format != volume_format:
        raise exception.ImageUnacceptable(
            image_id=image_id,
            reason=_("Converted to %(vol_format)s, but format is "
                     "now %(file_format)s") % {'vol_format': volume_format,
                                               'file_format': data.
                                               file_format})


def _get_sparse_file_size(file_name):
    """Get the real disk usage of a sparse file on disk, in bytes"""
    # Formula: (no of allocated blocks in 512 byte blocks) * 512 + 100MB
    # We append 100MB as sparse size on ext3 can be slightly different
    # than on RBD.
    return (os.stat(file_name).st_blocks * 512 + 100 * 2 ** 20)


def _get_context():
    k_cfg = CONF.keystone_authtoken
    auth = keystoneclient.Client(username=k_cfg.username,
                                 password=k_cfg.password,
                                 tenant_name=k_cfg.project_name,
                                 auth_url=k_cfg.auth_uri + "/v2.0")
    return RequestContext(auth_token=auth.session.get_token(),
                          user=k_cfg.username,
                          tenant=k_cfg.project_name,
                          show_deleted=True,
                          overwrite=False)


def _parse_rbd_location(location):
    prefix = 'rbd://'
    if not location.startswith(prefix):
        # Not stored in rbd
        return None
    pieces = map(urllib.unquote, location[len(prefix):].split('/'))
    if any(map(lambda p: p == '', pieces)):
        # Blank components
        return None
    if len(pieces) != 4:
        # Not an rbd snapshot
        return None
    return pieces


def _fetch_to_file(image_id, image_meta, dst):
    """Exports an image from glance to file"""

    # Check if we have a RBD store and get its location
    rbd_loc = None
    for location in image_meta['location_data']:
        rbd_loc = _parse_rbd_location(location['url'])
        if rbd_loc:
            break
    # TODO(oponcea): If source is not a RBD image download it from Glance
    # directly (http://docs.openstack.org/developer/python-glanceclient/)
    # TODO(oponcea): Use mapping of an image to a RBD block device instead
    # of import
    if not rbd_loc:
        reason = "Not a Ceph RBD image"
        raise exception.CachingToRawException(image_id=image_id, reason=reason)
    else:
        _prefix, pool, image, _snapshot = rbd_loc
        src = pool + "/" + image
        LOG.info(_LI("Fetching image from %(src)s to %(dst)s") %
                 {'src': src, 'dst': dst})
        cmd = ('env', 'LC_ALL=C', 'rbd', 'export', src, dst)
        _out, _err = processutils.execute(*cmd)
    if not os.path.exists(dst):
        reason = ("Export of the original image from glance to file failed: %s"
                  " does not exist") % dst
        raise exception.CachingToRawException(image_id=image_id, reason=reason)


def _import_from_file(src_file, dest_url, image_id):
    """import a file into RBD"""
    # Check if we have a RBD store and get its location
    # we only support ceph stores so no need to test for something else
    rbd_loc = _parse_rbd_location(dest_url)
    if not rbd_loc:
        reason = "Not a Ceph RBD location"
        raise exception.CachingToRawException(image_id=image_id, reason=reason)
    LOG.info(_LI("Importing %(src_file)s to %(dest_url)s") %
             {'src_file': src_file, 'dest_url': dest_url})
    _prefix, pool, image, snapshot = rbd_loc
    dst = pool + "/" + image
    cmd = ('env', 'LC_ALL=C', 'rbd', 'import', src_file, dst,
           '--image-format', '2',
           '--image-feature', 'layering,exclusive-lock,object-map,fast-diff')
    _out, _err = processutils.execute(*cmd)
    if snapshot:
        ceph_cfg_file = CONF.glance_store.rbd_store_ceph_conf
        with rados.Rados(conffile=ceph_cfg_file) as cluster:
            with cluster.open_ioctx(str(pool)) as ioctx:
                with rbd.Image(ioctx, str(image)) as image:
                    image.create_snap(str(snapshot))
                    image.protect_snap(str(snapshot))
                    # image.lock_exclusive('glance')


def _get_rbd_image_size(dest_url, image_id):
    """Get the size of an RBD image"""
    rbd_loc = _parse_rbd_location(dest_url)
    if not rbd_loc:
        reason = "Not a Ceph RBD image"
        raise exception.CachingToRawException(image_id=image_id, reason=reason)
    else:
        _prefix, pool, image, snapshot = rbd_loc
        image_str = "%s/%s@%s" % (pool, image, snapshot)
        cmd = ('env', 'LC_ALL=C', 'rbd', 'du', image_str,
               '--format', 'json')
        out, err = processutils.execute(*cmd)
        images = json.loads(out).get("images", [])
        if len(images) != 1 or "used_size" not in images[0]:
            reason = ("Image disk usage query failure."
                      "cmd: %(cmd)s, stdout: %(stdout)s, stderr: %(stderr)s" %
                      {"cmd": cmd, "stdout": out, "stderr": err})
            raise exception.CachingToRawException(image_id=image_id,
                                                  reason=reason)
        else:
            image_size = images[0]["used_size"]
            LOG.debug("Image %(id)s used RBD space is: %(used_size)s" %
                      {"id": image_id, "used_size": image_size})
            return image_size


def _del_rbd_image(dest_url, image_id):
    """Delete image from RBD"""
    rbd_loc = _parse_rbd_location(dest_url)
    if not rbd_loc:
        reason = "Not a Ceph RBD image"
        raise exception.InvalidRbdUrl(image_id=image_id, url=dest_url)
    else:
        _prefix, pool, image_name, snapshot = (str(x) for x in rbd_loc)
        ceph_cfg_file = CONF.glance_store.rbd_store_ceph_conf
        LOG.info(_LI("Deleting %(dest_url)s of %(image_id)s from RBD") %
                 {'dest_url': dest_url, 'image_id': image_id})
        with rados.Rados(conffile=ceph_cfg_file) as cluster:
            with cluster.open_ioctx(str(pool)) as ioctx:
                try:
                    # First remove snapshot.
                    if snapshot is not None:
                        with rbd.Image(ioctx, image_name) as image:
                            try:
                                if image.is_protected_snap(snapshot):
                                    image.unprotect_snap(snapshot)
                                    # image.unlock('glance')
                                image.remove_snap(snapshot)
                            except rbd.ImageBusy:
                                reason = _("snapshot %(image)s@%(snap)s could "
                                           "not be unprotected because it is "
                                           "in use") % {'image': image_name,
                                                        'snap': snapshot}
                                LOG.debug(reason)
                                raise store_exceptions.InUseByStore()
                            except rbd.ImageNotFound:
                                # Not an issue if it does not have snapshots
                                pass
                    # Then delete image.
                    # Note: A caching may be in progress on other controller
                    # when glance-api is started because sometimes glance-api
                    # process is not cleanly stopped and a 'rbd import' process
                    # keeps our image in use for some time - we just have to
                    # patiently wait here
                    retry_cnt = _WAIT_FOR_IMAGE_RELEASE
                    while True:
                        try:
                            rbd.RBD().remove(ioctx, image_name)
                            break
                        except rbd.ImageBusy:
                            if retry_cnt <= 0:
                                raise
                            else:
                                retry_cnt -= 5
                            reason = _("image %(image)s could not be "
                                       "removed because it is in use, "
                                       "waiting %(time)s seconds for its "
                                       "release") % {'image': image_name,
                                                     'time': retry_cnt}
                            LOG.debug(reason)
                            time.sleep(5)
                except rbd.ImageNotFound:
                    # If it does not exist then that's good!
                    pass
                except rbd.ImageBusy:
                    reason = _("image %s could not be removed "
                               "because it is in use")
                    LOG.debug(reason % image_name)
                    raise store_exceptions.InUseByStore()


class reserve_space(object):
    def __init__(self, image_id, size, pool):
        self.image_id = image_id
        self.size = size
        self.pool = pool

    @lockutils.synchronized(LOCK_RBD_USAGE, LOCK_PREFIX, True, LOCK_DIR)
    def __enter__(self):
        # This function is synchronized with glance's image creation to
        # provide correct free space computations
        # initialize ceph connection
        rbd_store = rbd_store_driver.Store(CONF)
        ceph_cfg_file = CONF.glance_store.rbd_store_ceph_conf
        with rados.Rados(conffile=ceph_cfg_file) as cluster:
            with cluster.open_ioctx(str(self.pool)) as ioctx:
                # Get quota
                ceph_quota_output = json.loads(
                    cluster.mon_command(
                        json.dumps({
                            "prefix": "osd pool get-quota",
                            "pool": self.pool,
                            "format": "json-pretty"}), "")[1])

                glance_ceph_quota = ceph_quota_output.get("quota_max_bytes", 0)

                rbd_store.validate_available_space(
                    ioctx, self.image_id, self.size, glance_ceph_quota)

        # Reserve space
        # NOTE: Conversions are done serially therefore we can safely replace
        # the old entry
        with open(DEFAULT_POOL_RESERVATION_FILE, "w+") as f:
            data = {"image_id": (self.image_id + '_raw'),
                    "reserved": self.size}
            f.write(str(data))
        return self

    def __exit__(self, dtype, value, traceback):
        self.unreserve()

    @staticmethod
    @lockutils.synchronized(LOCK_RBD_USAGE, LOCK_PREFIX, True, LOCK_DIR)
    def unreserve():
        with open(DEFAULT_POOL_RESERVATION_FILE, "w+") as f:
            f.write("{}")


def _cache_img_to_raw(context, image_id):
    """Cache an image to RAW"""

    # Start caching
    LOG.info(_LI("Caching image %s") % image_id)
    image_meta = registry.get_image_metadata(context, image_id)
    image_meta_to_update = {'properties': {'cache_raw_status': 'Caching'}}
    registry.update_image_metadata(context, image_id, image_meta_to_update)

    # Set the paths
    base = CONF.cache_raw_conversion_dir + "/" + image_id
    orig_file = base + "_orig"
    converted_file = base + "_raw"
    converted_image = image_id + "_raw"
    # Get cluster fsid
    ceph_cfg_file = CONF.glance_store.rbd_store_ceph_conf
    with rados.Rados(conffile=ceph_cfg_file) as cluster:
        fsid = cluster.get_fsid()
    dest_url = "rbd://%s/%s/%s/%s" % (fsid,
                                      CONF.glance_store.rbd_store_pool,
                                      converted_image,
                                      "snap")

    # Do the conversion
    _fetch_to_file(image_id, image_meta, orig_file)
    try:
        _convert_to_volume_format(orig_file, converted_file, 'raw', image_id)
    except exception.ConvertToSameFormat as ex:
        raise exception.ImageUncacheable(
            image_id=image_id,
            reason=_("The format of the image is (%(fmt)s) "
                     "not (%(orig)s), please specify the correct format "
                     "when creating the image") %
            {'fmt': ex.fmt, 'orig': image_meta.get('disk_format')})

    with reserve_space(image_id, _get_sparse_file_size(converted_file),
                       CONF.glance_store.rbd_store_pool):
        _import_from_file(converted_file, dest_url, image_id)

    # Cleanup
    os.unlink(orig_file)
    os.unlink(converted_file)

    # Finalize caching
    image_size = _get_rbd_image_size(dest_url, image_id)
    image_meta_to_update['properties']['cache_raw_status'] = 'Cached'
    image_meta_to_update['properties']['cache_raw_url'] = dest_url
    image_meta_to_update['properties']['cache_raw_size'] = image_size
    registry.update_image_metadata(context, image_id, image_meta_to_update)
    LOG.info(_LI("Caching completed for image: %s") % image_id)


def _log_to_fm(msg, poposed_fix='', instance_id='', cause=None):
    """Save an error in the customer log"""
    # TODO(oponcea): Test and enable it or remove the code if not wanted
    alarm_id = fm_const.FM_ALARM_ID_STORAGE_IMAGE
    alarm_state = fm_const.FM_ALARM_STATE_MSG
    entity_type_id = fm_const.FM_ALARM_TYPE_SERVICE
    severity = fm_const.FM_ALARM_SEVERITY_WARNING
    alarm_type = fm_const.FM_ALARM_TYPE_3
    probable_cause = cause or fm_const.ALARM_PROBABLE_CAUSE_UNKNOWN
    fix = poposed_fix
    fm_api.FaultAPIs().set_fault(fm_api.Fault(alarm_id=alarm_id,
                                              alarm_state=alarm_state,
                                              entity_type_id=entity_type_id,
                                              entity_instance_id=instance_id,
                                              severity=severity,
                                              reason_text=msg,
                                              alarm_type=alarm_type,
                                              probable_cause=probable_cause,
                                              proposed_repair_action=fix,
                                              service_affecting=True))


def _pipe_watcher(server):
    try:
        os.read(server.readpipe.fileno(), 1)
        LOG.info(_LI("RAW caching exit (parent died)"))
        os._exit(1)
    except Exception as e:
        LOG.error(_LE("RAW caching _pipe_watcher failed: %s"), str(e))


def start_raw_caching(server):
    """Spawn a worker process. Function does not block"""
    global g_is_cache_raw_enabled

    # Clean any Ceph reservations left from previous runs
    reserve_space.unreserve()

    # Check if this feature should be enabled or not
    if _RBD_STORE not in CONF.glance_store.stores:
        LOG.info(_LI("Not using %s. RAW caching is only "
                     "available for Ceph RBD") % _RBD_STORE)
        return None
    if not CONF.cache_raw_conversion_dir:
        LOG.error(_LE("Option cache_raw_conversion_dir is not defined."
                      "Caching of images to RAW is disabled!"))
        return None

    # Start the new process early, we want to avoid crashing glance if
    # something bad happens when initializing RAW caching
    LOG.info(_LI("RAW caching is enabled, starting it"))
    g_is_cache_raw_enabled.value = True
    p = os.fork()
    if p == 0:
        os.close(server.writepipe)
        # Register signal handlers for child
        if CONF.graceful_shutdown:
            signal.signal(signal.SIGHUP, _sig_handler)
            signal.signal(signal.SIGTERM, _sig_handler)
            signal.signal(signal.SIGUSR1, _sig_handler)
        # Start RAW caching main process
        LOG.info(_LI("RAW caching start _pipe_watcher"))
        eventlet.spawn(_pipe_watcher, server)
        _raw_caching_manager()
        LOG.info(_LI("RAW caching exit"))
        sys.exit(0)
    # Note: We have to keep track of RAW caching as WSGI think that
    # they are the only processes around
    server.raw_caching_pid = p
    return p


def _safe_update_image_metadata(context, image_id, image_meta):
    try:
        registry.update_image_metadata(context, image_id, image_meta)
    except Exception as e:
        err = encodeutils.exception_to_unicode(e)
        LOG.error(_LE("Error updating image metadata: "
                      "%(img)s, err: %(err)s") %
                  {'img': image_meta['id'], 'err': err})


def _raw_caching_manager():
    """Spawn a worker process. Function does not block"""
    global g_job_queue, g_image_id, g_done_event, g_delete_lock

    LOG.info(_LI('RAW caching manager starting'))
    # Communication between glance-api and glance-registry is done using REST
    # so we need admin authentication before accessing the registry
    retries = 0
    while True:  # keystone has the bad habit of starting late, retry
        try:
            admin_context = _get_context()
            break
        except Exception as e:
            retries += 1
            err = encodeutils.exception_to_unicode(e)
            duration = _RETRY_COUNT_BEFORE_ERROR * _RETRY_SLEEP_S
            LOG.info(_LI("Error getting admin context for %(duration)s s,"
                         " reason: %(reason)s") %
                     {'duration': duration, 'reason': err})
            if retries >= _RETRY_COUNT_BEFORE_ERROR:
                LOG.error(_LE("Error getting admin context for %(duration)s s,"
                              " reason: %(reason)s") %
                          {'duration': duration, 'reason': err})
                sys.exit()
            time.sleep(_RETRY_SLEEP_S)

    active_images = registry.get_images_detail(admin_context,
                                               filters={"is_public": 'None',
                                                        "deleted": "False"})
    # Cleaning invalid conversions
    _clean_dir_content(CONF.cache_raw_conversion_dir)

    LOG.info(_LI('RAW caching restore previous images'))
    # Restore previous images that were waiting to be cached
    for image_meta in active_images:
        if _is_caching_needed(image_meta):
            try:
                # Delete invalid conversion files
                converted_image = image_meta['id'] + "_raw"
                ceph_cfg_file = CONF.glance_store.rbd_store_ceph_conf
                with rados.Rados(conffile=ceph_cfg_file) as cluster:
                    fsid = cluster.get_fsid()
                    images_pool = CONF.glance_store.rbd_store_pool
                    dest_url = "rbd://%s/%s/%s/%s" % (fsid,
                                                      images_pool,
                                                      converted_image,
                                                      "snap")
                _del_rbd_image(dest_url, image_meta['id'])
            except store_exceptions.InUseByStore as e:
                # This is important and should not happen for an uncached
                # img, as we don't really know what to do in this case we
                # should at least make sure that we don't crash the main
                # process and log the message properly
                err = encodeutils.exception_to_unicode(e)
                image_meta_u = {'properties': {'cache_raw_status': 'Error',
                                               'cache_raw_error': err}}
                _safe_update_image_metadata(admin_context,
                                            image_meta['id'],
                                            image_meta_u)
                LOG.error(_LE("Error resuming caching for image:%(id)s"
                              " reason: %(reason)s") %
                          {'id': image_meta['id'],
                           'reason': encodeutils.exception_to_unicode(e)})
                # TODO(oponcea): _log_to_fm(err)
                continue
            try:
                LOG.info(_LI("Found image that is not cached: %s "
                             "enqueuing it for caching") %
                         image_meta['id'])
                create_image_cache(admin_context, image_meta['id'])
            except Exception as e:
                err = encodeutils.exception_to_unicode(e)
                image_meta_u = {'properties': {'cache_raw_status': 'Error',
                                               'cache_raw_error': err}}
                _safe_update_image_metadata(admin_context,
                                            image_meta['id'],
                                            image_meta_u)
                LOG.error(_LE("Error creating RAW cache for image: "
                              "%(img)s, err: %(err)s") %
                          {'img': image_meta['id'], 'err': err})
                # TODO(oponcea): _log_to_fm(err)
                continue

    # Start the main loop
    while True:
        LOG.info(_LI("RAW caching waiting for request"))
        try:
            # multiprocessing.Queue.put() uses a background thread to pickle
            # and enqueue object to internal queue; yield from current eventlet
            # to give that thread a chance to run
            image_id = None
            while not image_id:
                eventlet.sleep(0)
                try:
                    image_id = g_job_queue.get(True, 5)
                except Empty:
                    pass
            LOG.info(_LI("RAW caching got job for: %s") % image_id)
        except IOError as e:
            # Remove the exceptions generated by EINTR from logs
            if e.errno != errno.EINTR:
                raise
            continue
        try:
            # Set current caching image
            with g_delete_lock:
                # Do not start a new caching if a delete is in progress.
                # Delete operations are short, this should not take long
                g_image_id.value = str(image_id)
            admin_context = _get_context()

            # Do the caching itself
            _cache_img_to_raw(admin_context, image_id)
        except Exception as e:
            # Execution needs to continue even if conversion
            # errors are encountered
            LOG.error(traceback.format_exc())
            err = encodeutils.exception_to_unicode(e)
            image_meta = {'properties': {'cache_raw_status': 'Error',
                                         'cache_raw_error': err}}
            _safe_update_image_metadata(admin_context,
                                        image_id,
                                        image_meta)
        finally:
            with g_delete_lock:
                # If delete is waiting for caching to complete tell it
                # that it's over.
                g_image_id.value = ""
                # notify_all as same image may be deleted twice
                g_delete_lock.notify_all()


def _is_caching_needed(m):
    """Check if image should be cached or not

    :param m: the meta-data dictionary of an image
    :return: False if it's not ok to cache or already cached
             True if is good to cache or previous caching failed
    """
    # Check main status and format
    if m['status'] != 'active' or m['disk_format'] == 'raw':
        return False

    # Check the caching properties
    p = m.get('properties', {})
    if p.get('cache_raw', '') == 'True':
        cache_raw_status = p.get('cache_raw_status', '')
        if cache_raw_status != 'Cached':
            return True  # we retry the conversion if the image is in Error
        return False
    return False


def create_image_cache(context, image_id):
    """Enqueue an image for caching if needed"""
    global g_job_queue, g_is_cache_raw_enabled
    if not g_is_cache_raw_enabled or not g_is_cache_raw_enabled.value:
        # Check & delete image cache only if RAW Caching is enabled
        # Note: UTs should pass without modifications
        return
    image_meta = registry.get_image_metadata(context, image_id)
    if not _is_caching_needed(image_meta):
        LOG.info(_LE("Caching not needed for:%s") % image_id)
        return

    # Schedule image for caching only if RAW Caching is enabled
    if not g_is_cache_raw_enabled.value:
        del image_meta['properties']['cache_raw']
        registry.update_image_metadata(context, image_id, image_meta,
                                       purge_props=True)
        return

    # Make sure we have all of the fields and that they are correctly set
    image_meta['properties']['cache_raw_status'] = 'Queued'
    image_meta['properties']['cache_raw_size'] = '-'
    if 'cache_raw_error' in image_meta['properties']:
        del image_meta['properties']['cache_raw_error']
    registry.update_image_metadata(context, image_id, image_meta,
                                   purge_props=True)

    LOG.info(_LI("Enqueuing image for conversion: %s") % image_id)
    g_job_queue.put(image_id)


def delete_image_cache(context, image_id, image_meta=None):
    """Deleting an image from cache"""
    global g_image_id, g_done_event, g_delete_lock, g_is_cache_raw_enabled
    if not g_is_cache_raw_enabled or not g_is_cache_raw_enabled.value:
        # Check & delete image cache only if RAW Caching is enabled
        # Note: UTs pass should pass without modifications
        return
    LOG.info(_LI("Deleting image %s from cache") % image_id)
    # Check if we are caching, race issues with cache_raw_status in the meta
    # so don't rely on it
    with g_delete_lock:
        if g_image_id.value == image_id:
            # We can't delete an image that it's caching.
            LOG.info(_LI("Image %s is caching, waiting for operation to "
                         "complete before deleting it") % image_id)
            g_delete_lock.wait(1200)  # wait for caching to complete
            image_meta = registry.get_image_metadata(context, image_id)
    if not image_meta:
        # Glance V2 API is providing a different metadata format,
        # therefore cannot be reused
        image_meta = registry.get_image_metadata(context, image_id)
    url = image_meta['properties'].get('cache_raw_url')
    if url:
        _del_rbd_image(url, image_meta['id'])


def _sig_handler(signum, frame):
    LOG.info(_LI("Signal handler called with signal %s") % signum)
    if signum in [signal.SIGTERM]:
        LOG.info(_LI("Exiting RAW Caching due to signal"))
        signal.signal(signum, signal.SIG_IGN)
        os._exit(0)
    # We are ignoring SIGHUP and SIGUSR1.
    # SIGHUP is used for configuration reload, and RAW caching does not
    # support it and SIGUSR1 is converted into a SIGTERM when the time
    # is right by the main process
    LOG.info(_LI("Ignoring signal %s") % signum)
