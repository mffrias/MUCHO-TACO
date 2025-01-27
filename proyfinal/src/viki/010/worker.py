#!/usr/bin/env python
# encoding: utf-8
"""
worker.py

Created by Guido Marucci Blas on 2011-02-28.
Copyright (c) 2011 __MyCompanyName__. All rights reserved.
"""

from andrea.worker import Worker

import andrea.settings
import andrea.network

from andrea.process  import Process
from andrea.tools    import Alloy, Minisat220, Reason
from andrea.network  import WantMission, HaveMission, DoneMission
from andrea.network  import ExitToShell, Tag, Rank
from andrea.utils    import RoundRobin, write_file, secs2human
from andrea.events   import Event, TaskEvent, KillEvent
from time     import sleep
from os       import path
import settings

class InfiniteTimeoutWorker(Worker):
    
    def main_loop_idle(self):
        "This part of main_loop() only runs when worker is idle."
        if not self.mission_requested:
            andrea.network.send(WantMission())
            self.mission_requested = True
        elif andrea.network.msg_waiting(Rank.MASTER, Tag.HAVE_MISSION):
            msg = andrea.network.receive(Rank.MASTER, Tag.HAVE_MISSION)
            self.current_task = msg.body # (tid, ttype, tdata, infinite_timeout)
            if self.current_task[3] and settings.debug:
                print 'task %s will be solved with infinite timeout' % self.current_task[0]
            self.handle_mission(self.current_task)

    def main_loop_busy(self):
        "This part of main_loop() only runs when agent is busy."
        if self.current_tool.finished():
            self.current_event.stats = self.current_tool.stats
            if self.current_tool.finished_via() == Reason.EXIT_OK:
                ans = self.current_tool.veredict()
                self.current_event.res = 'SAT' if ans == True else 'UNSAT'
            elif self.current_tool.finished_via() == Reason.KILL_OK:
                self.current_event.res = 'TIMEOUT'
                self.current_event_kill.finish()
            elif self.current_tool.finished_via() == Reason.EXIT_KO:
                self.current_event.res = 'ERROR'
                self.current_event.stats['task.retcode'] = self.current_tool.returncode
            else:
                self.current_event.res = 'ERROR'
                self.current_event.stats['task.sigcode'] = self.current_tool.returncode

            (tid, ttype, tdata, infinite_timeout, curMax, level, timeout) = self.current_task
            elapsed = andrea.network.time() - self.tool_start_time
            if infinite_timeout and settings.debug:
                print 'task %s with infinite timeout was solved in %s' % (tid, secs2human(elapsed, msecs=False))
            
            if 'OutOfMemory' in self.current_event.stats.get('task.output'):
                self.current_event.res = 'MEMOUT'
        
            rcstrmap = self.rcstrs[self.current_task[1]]
            self.current_event.etc['exitcode'] = self.current_tool.returncode
            self.current_event.etc['exitstr'] = rcstrmap.get(self.current_tool.returncode, 'RC_Unknown')
            self.current_event.finish()
        
            self.current_event.stats['task.msecs'] = int(1000.0 * self.current_event.dur)

            msg_data = (self.current_task[0], # tid
                self.current_task[1], # ttype
                self.current_event.max, # current max (variables set)
                self.current_event.level, # current level (father, son, grandson, etc)
                self.infinite_timeout, # infinite timeout bool
                self.timeout, # task timeout
                self.current_event.res, # main result ('SAT', 'ERROR', etc..)
                self.current_event.etc['exitcode'],  # main exitcode or signal number
                self.current_event.etc['exitstr'],  # ascii version of it, if available
                self.current_event.stats, # dict w/task statistics and output
            )
            andrea.network.send(DoneMission(msg_data))
            self.clear_state()
        else:
            elapsed = andrea.network.time() - self.tool_start_time
            (tid, ttype, tdata, infinite_timeout, curMax, level, timeout) = self.current_task
            if (not infinite_timeout) and (elapsed > self.timeout):
                if not self.current_tool.aborting():
                    self.current_event_kill = self.bb.add(KillEvent(self.current_task[0]))
                    self.current_tool.abort()
    
    def handle_mission(self, task):
        tid, ttype, tdata, infinite_timeout, curMax, level, new_timeout = task
        self.infinite_timeout = infinite_timeout
        self.timeout = float(new_timeout)
        self.current_tool = self.tools[ttype]
        self.current_event = self.bb.add(TaskEvent('analysis', tid, timeout=new_timeout, curMax=curMax, level=level))
        handler = getattr(self, 'handle_mission_' + ttype)
        handler(tid, tdata)
    