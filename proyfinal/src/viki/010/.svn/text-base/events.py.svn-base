#!/usr/bin/env python
# encoding: utf-8
"""
PartitionEvent.py

Created by Guido Marucci Blas on 2011-01-29.
Copyright (c) 2011 __MyCompanyName__. All rights reserved.
"""

import sys
import os

from andrea.events   import Event
from andrea.utils    import secs2human

class PartitionEvent(Event):

    def __init__(self, tid, file_path, output_directory, scope, rels, curMax=0, level=0):
        Event.__init__(self, 'partitionate', tid, curMax=curMax, level=level)
        self.file_name = tid
        self.file_path = file_path
        self.output_directory = output_directory
        self.scope = scope
        self.rels = rels
        self.partitions = 0
        
    def __str__(self):
        fmt = '%s--%s  (%s)   partitioned file: %s   partitions: %d  scope: %d  max: %d  level: %d  rels: %s'
        return fmt % (secs2human(self.t_i, msecs=False), secs2human(self.t_f, msecs=False), secs2human(self.dur),
        self.file_name, self.partitions, self.scope, self.max, self.level, self.rels.values())