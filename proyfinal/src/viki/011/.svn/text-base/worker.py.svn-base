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
from als2cnfmodutils import generate_artifacts, MinisatHotPipe, generate_new_cnf, separate_cnf_from_header

def memory_usage():
    """Memory usage of the current process in kilobytes."""
    status = None
    result = {'peak': 0, 'rss': 0}
    try:
        # This will only work on systems with a /proc file system
        # (like Linux).
        status = open('/proc/self/status')
        for line in status:
            parts = line.split()
            key = parts[0][2:-1].lower()
            if key in result:
                result[key] = int(parts[1])
    finally:
        if status is not None:
            status.close()
    return result


class InfiniteTimeoutWorker(Worker):
    
    def init_tools(self):
        # HACK PARA DEBUG
        if self.my_rank is 2:
            print 'Antes del bcast:', memory_usage()
        self.timeout = float(andrea.settings.experiment['timeout'])
        self.als, self.inv, self.cnf, self.cnf_inv, self.rels, self.rels_inv = None, None, None, None, None, None
                
        (self.als, self.inv, self.cnf, self.cnf_inv, self.rels, self.rels_inv) = \
        andrea.network.broadcast((self.als, self.inv, self.cnf, self.cnf_inv, self.rels, self.rels_inv))

        # HACK PARA DEBUG
        if self.my_rank is 2:
            print 'Despues del bcast:', memory_usage()
                
        als_path = path.join(self.my_dir, "initial.als")
        inv_path = path.join(self.my_dir, "initial.inv")
        cnf_path = path.join(self.my_dir, "initial.cnf")
        cnf_inv_path = path.join(self.my_dir, "initial_inv.cnf")
        rels_path = path.join(self.my_dir, "initial.rels")
        rels_inv_path = path.join(self.my_dir, "initial_inv.rels")
        
        
        fals = open(als_path, 'w')
        fals.write(self.als)
        fals.close()
        finv = open(inv_path, 'w')
        finv.write(self.inv)
        finv.close()
        fcnf = open(cnf_path, 'w')
        fcnf.write(self.cnf)
        fcnf.close()
        fcnfinv = open(cnf_inv_path, 'w')
        fcnfinv.write(self.cnf_inv)
        fcnfinv.close()
        frels = open(rels_path, 'w')
        frels.write(self.rels)
        frels.close()
        frelsinv = open(rels_inv_path, 'w')
        frelsinv.write(self.rels_inv)
        frelsinv.close()
        
        # HACK PARA DEBUG
        if self.my_rank is 2:
            print 'Antes de gen_artifacts:', memory_usage()

        (self.tuple2val, self.restrictions, self.cnf, self.cnf_inv, self.rels_sets, self.inv_tuple2val, self.rels_inv_sets, self.rels, self.rels_inv) = \
        generate_artifacts(als_path, inv_path, int(settings.scope), settings.rels.values(), andrea.settings, verbose=False, cnf_path=cnf_path, cnf_inv_path=cnf_inv_path, rels_arg_path=rels_path, rels_arg_inv_path=rels_inv_path)        
        
        # HACK PARA DEBUG
        if self.my_rank is 2:
            print 'Despues de gen_artifacts:', memory_usage()

        (self.cnf, self.cnf_vars, self.cnf_clauses) = separate_cnf_from_header(self.cnf)

        # HACK PARA DEBUG
        if self.my_rank is 2:
            print 'Despues de separate:', memory_usage()

        (self.cnf_inv, self.cnf_inv_vars, self.cnf_inv_clauses) = separate_cnf_from_header(self.cnf_inv)

        # HACK PARA DEBUG
        if self.my_rank is 2:
            print 'Despues de separate inv:', memory_usage()

        self.minisat = MinisatHotPipe(andrea.settings.paths['minisat_binary'])
        
        self.tools    = dict({'cnf': self.minisat})
        self.rcstrs   = dict({'cnf': Minisat220.RC_STR})
        self.proc_inv = True
        self.stats_inv = None
        self.overhead = 0.0
       
    def clear_state(self):
        Worker.clear_state(self)
        self.proc_inv = True
        self.stats_inv = None
        self.overhead = 0.0
        self.curMax = 0
        
    def main_loop_idle(self):
        "This part of main_loop() only runs when worker is idle."
        if not self.mission_requested:
            andrea.network.send(WantMission())
            self.mission_requested = True
            if self.my_rank is 2:
                print 'Tras mission request:', memory_usage()
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

            if 'OutOfMemory' in self.current_event.stats.get('task.output'):
                self.current_event.res = 'MEMOUT'

            rcstrmap = self.rcstrs[self.current_task[1]]
            self.current_event.etc['exitcode'] = self.current_tool.returncode
            self.current_event.etc['exitstr'] = rcstrmap.get(self.current_tool.returncode, 'RC_Unknown')
            

            # If the task finished was just the invariant
            if self.proc_inv:
            # PEND: handle other cases; just the strictly necessary for now
                assert self.current_event.res in ('SAT', 'UNSAT')
                if self.current_event.res == 'SAT':
            # Survived invariant pre-check! Prepare for full solving
                    #print "Dio SAT el invariante"
                    self.proc_inv = False
                    self.stats_inv = self.current_event.stats # keep a ref to stats dict from 1st pass
                    self.minisat = MinisatHotPipe(andrea.settings.paths['minisat_binary'])
                    self.tools = dict({'cnf': self.minisat})
                    self.handle_mission(self.current_task)
                    return
                else:
                    pass #print "Dio UNSAT el invariante"

            # A esta altura estamos cerrando la pasada definitiva, sea 1ra o 2da

            self.current_event.finish()
            self.current_event.stats['task.msecs'] = int(1000.0 * self.current_event.dur)

            (tid, ttype, tdata, infinite_timeout, curMax, level, timeout) = self.current_task
            elapsed = andrea.network.time() - self.tool_start_time
            if infinite_timeout and settings.debug:
                print 'task %s with infinite timeout was solved in %s' % (tid, secs2human(elapsed, msecs=False))
            
            if self.stats_inv:
            # If we kept a ref to a possible "first pass" stats dict, nest it within 2nd pass stats
            # This is not pretty, but should at least preserve some data w/no impact on the master for now
            # PEND: improve this; make the inv stats be always that, and full run stats always that.
                self.current_event.stats['stats_inv'] = self.stats_inv

            msg_data = (self.current_task[0], # tid
                self.current_task[1], # ttype
                self.current_event.max, # current max (variables set)
                self.current_event.level, # current level (father, son, grandson, etc)
                self.infinite_timeout, # infinite timeout bool
                self.timeout, # task timeout
                self.overhead, # task overhead
                self.proc_inv, # processing invariant?
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
            if (not infinite_timeout) and (elapsed > self.timeout) and not self.proc_inv:
                if not self.current_tool.aborting():
                    self.current_event_kill = self.bb.add(KillEvent(self.current_task[0]))
                    self.current_tool.abort()
    
    def handle_mission(self, task):
        tid, ttype, tdata, infinite_timeout, self.curMax, level, new_timeout = task
        self.infinite_timeout = infinite_timeout
        self.timeout = float(new_timeout)
        self.current_tool = self.minisat

        if self.proc_inv:
            self.current_event = self.bb.add(TaskEvent('analysis', tid, timeout=new_timeout, curMax=self.curMax, level=level, inv=True))
        else:
            self.current_event = self.bb.add(TaskEvent('analysis', tid, timeout=new_timeout, curMax=self.curMax, level=level, inv=False))
            
        self.handler_res(tid, tdata)
             
        #handler = getattr(self, 'handle_mission_' + ttype)
        #handler(tid, tdata)
    
    def handler_res(self, tid, tdata):
        ti = andrea.network.time()
        if self.proc_inv == True: 
            tinv = andrea.network.time()
            (header, cnf, res) = generate_new_cnf(self.cnf_inv, tdata, self.rels_inv_sets, self.inv_tuple2val, self.curMax, self.cnf_inv_vars, self.cnf_inv_clauses)
            #print "Overhead generate new cnf inv = " + str(andrea.network.time() - tinv)
            #out_path = path.join(andrea.settings.paths['local_storage'], str(tid) + ".inv.cnf.out")     
            cnf_path = path.join(self.my_dir, str(tid) + ".inv.cnf")     
        else:
            tinv = andrea.network.time()
            (header, cnf, res) = generate_new_cnf(self.cnf, tdata, self.rels_sets, self.tuple2val, self.curMax, self.cnf_vars, self.cnf_clauses)
            #print "Overhead generate new cnf no inv = " + str(andrea.network.time() - tinv)
            #out_path = path.join(andrea.settings.paths['local_storage'], str(tid) + ".cnf.out")
            cnf_path = path.join(self.my_dir, str(tid) + ".cnf")

        #Correr primero el invariante y si da sat, correr lo de abajo
        self.tool_start_time = andrea.network.time()

        if settings.flush2disk:
            fcnf = open(cnf_path, 'w')
            fcnf.write(header)
            fcnf.write(res)
            fcnf.write(cnf)
            fcnf.close()
     
        self.minisat.launch(cnf_path, header=header, cnf=cnf, res=res, flush2disk=settings.flush2disk)
        self.overhead += andrea.network.time() - ti
        #print ("Overhead launch inv = " if self.proc_inv else "Overhead launch = ") + str(andrea.network.time() - self.tool_start_time)
