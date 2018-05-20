#!/usr/bin/env python

# Copyright 2010 United States Government as represented by the
# Administrator of the National Aeronautics and Space Administration.
# Copyright 2011 OpenStack Foundation
# All Rights Reserved.
#
#    Licensed under the Apache License, Version 2.0 (the "License"); you may
#    not use this file except in compliance with the License. You may obtain
#    a copy of the License at
#
#         http://www.apache.org/licenses/LICENSE-2.0
#
#    Unless required by applicable law or agreed to in writing, software
#    distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
#    WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
#    License for the specific language governing permissions and limitations
#    under the License.

"""
Glance API Server
"""

import os
import sys

import eventlet
from oslo_utils import encodeutils


# Monkey patch socket, time, select, threads
eventlet.patcher.monkey_patch(all=False, socket=True, time=True,
                              select=True, thread=True, os=True)

# If ../glance/__init__.py exists, add ../ to Python search path, so that
# it will override what happens to be installed in /usr/(local/)lib/python...
possible_topdir = os.path.normpath(os.path.join(os.path.abspath(sys.argv[0]),
                                   os.pardir,
                                   os.pardir))
if os.path.exists(os.path.join(possible_topdir, 'glance', '__init__.py')):
    sys.path.insert(0, possible_topdir)

import glance_store
from oslo_config import cfg
from oslo_log import log as logging
import osprofiler.initializer

from glance import cache_raw
from glance.common import config
from glance.common import exception
from glance.common import wsgi
from glance import notifier

CONF = cfg.CONF
CONF.import_group("profiler", "glance.common.wsgi")
logging.register_options(CONF)

KNOWN_EXCEPTIONS = (RuntimeError,
                    exception.WorkerCreationFailure,
                    glance_store.exceptions.BadStoreConfiguration,
                    ValueError)


def fail(e):
    global KNOWN_EXCEPTIONS
    return_code = KNOWN_EXCEPTIONS.index(type(e)) + 1
    sys.stderr.write("ERROR: %s\n" % encodeutils.exception_to_unicode(e))
    sys.exit(return_code)


def main():
    try:
        config.parse_args()
        config.set_config_defaults()
        wsgi.set_eventlet_hub()
        logging.setup(CONF, 'glance')
        notifier.set_defaults()

        # Shared data need to be initialized prior to fork()
        # so we need this before WSGI initialization in case it is
        # configured to use it
        cache_raw.initialize()

        if CONF.profiler.enabled:
            osprofiler.initializer.init_from_conf(
                conf=CONF,
                context={},
                project="glance",
                service="api",
                host=CONF.bind_host
            )

        server = wsgi.Server(initialize_glance_store=True)
        server.start(config.load_paste_app('glance-api'), default_port=9292)
        # Start RAW caching
        p = cache_raw.start_raw_caching(server)
        server.wait(p)

    except KNOWN_EXCEPTIONS as e:
        fail(e)


if __name__ == '__main__':
    main()
