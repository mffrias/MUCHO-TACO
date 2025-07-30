#!/usr/bin/env python
# encoding: utf-8

"""
extended_queue.py

Created by Santiago Bermudez on 2011-02-06.
Copyright (c) 2011 __MyCompanyName__. All rights reserved.
"""

import settings
import sys
import os
from Queue import Queue

class ExtendedQueue(Queue):
    """
    def __nonzero__(self):
        return not self.empty
    """
    
    def __len__(self):
        return self.qsize()
    
    def append(self, item):
        #print("Appending");
        self.put(item)
        #print("App done")
            
    def pop(self, item):
        #print("Poping")
        if not self.empty():
            ret = self.get()
            #print("Pop done")
            return ret
        return None