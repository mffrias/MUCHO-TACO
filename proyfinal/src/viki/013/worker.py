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
from als2cnfmodutils import generate_artifacts, MinisatHotPipe, generate_new_cnf

class InfiniteTimeoutWorker(Worker):
    
    def receive_broadcast(self):
        while (not andrea.network.msg_waiting(Rank.MASTER, Tag.HAVE_MISSION)):
            sleep(0.002)
            continue
        
        (als_string, inv_string) = andrea.network.receive(Rank.MASTER, Tag.HAVE_MISSION).body
        
        return (als_string, inv_string)
        
    def init_tools(self):
        self.timeout = float(andrea.settings.experiment['timeout'])
        print("Debug-mfrias4, worker.py line 39, timeout = ", self.timeout, " I am worker ", self.my_rank)

        (als_string, inv_string) = self.receive_broadcast()
        print("Debug-mfrias4, worker.py line 42, als_string = ", als_string, " inv_string = ", inv_string)
        
        #als = path.join(andrea.settings.paths['local_storage'], "initial.als")
        #inv = path.join(andrea.settings.paths['local_storage'], "initial.inv")
        als = path.join(self.my_dir, "initial.als")
        inv = path.join(self.my_dir, "initial.inv")
        
        fals = open(als, 'w')
        fals.write(als_string)
        fals.close()
        finv = open(inv, 'w')
        finv.write(inv_string)
        finv.close()
        (self.tuple2val, self.restrictions, self.cnf, self.cnf_inv, self.rels_sets, self.inv_tuple2val, self.rels_inv_sets) = generate_artifacts(als, inv, int(settings.scope), settings.rels.values(), andrea.settings.paths, verbose=False)
        
        self.minisat = MinisatHotPipe(andrea.settings.paths['minisat_binary'])
        
        self.tools    = dict({'cnf': self.minisat})
        self.rcstrs   = dict({'cnf': Minisat220.RC_STR})
        self.proc_inv = True
        self.stats_inv = None
        self.overhead = 0.0
       
    def clear_state(self):
        print("Debug-mfrias4: worker.py line 66. Enters clear_state. I am worker ", self.my_rank )
        Worker.clear_state(self)
        self.proc_inv = True
        self.stats_inv = None
        self.overhead = 0.0
        
    def main_loop_idle(self):
        print("Debug-mfrias4: worker.py line 71. Entered main_loop_idle. I am worker ", self.my_rank)
        if not self.mission_requested:
            print("Debug-mfrias4, worker.py line 73. Case not self.mission_requested")
            andrea.network.send(WantMission())
            self.mission_requested = True
        elif andrea.network.msg_waiting(Rank.MASTER, Tag.HAVE_MISSION):
            print("Debug-mfrias4, worker.py line 79. About to assign task")
            msg = andrea.network.receive(Rank.MASTER, Tag.HAVE_MISSION)
            self.current_task = msg.body # (tid, ttype, tdata, infinite_timeout)
            if self.current_task[3] and settings.debug:
                print ('Debug-mfrias4, worker.py line 80, task %s will be solved with infinite timeout' % self.current_task[0])
            self.handle_mission(self.current_task)

    def main_loop_busy(self):

        print("Debug-mfrias4, worker.py line 88. main_loop_busy(self). I am worker ", self.my_rank)
        if self.current_tool.finished():
            print("Debug-mfrias4, worker.py line 90. After self.current_tool.finished()")
            self.current_event.stats = self.current_tool.stats
            if self.current_tool.finished_via() == Reason.EXIT_OK:
                print("Debug-mfrias4, worker.py line 93. Reason.EXIT_OK.")
                ans = self.current_tool.veredict()
                print("Debug-mfrias4, worker.py line 93. ans = ", ans)
                self.current_event.res = 'SAT' if ans == True else 'UNSAT'
            elif self.current_tool.finished_via() == Reason.KILL_OK:
                print("Debug-mfrias4, worker.py line 96. Reason.KILL_OK")
                self.current_event.res = 'TIMEOUT'
                self.current_event_kill.finish()
            elif self.current_tool.finished_via() == Reason.EXIT_KO:
                print("Debug-mfrias4, worker.py line 100. Reason.EXIT_KO")
                self.current_event.res = 'ERROR'
                self.current_event.stats['task.retcode'] = self.current_tool.returncode
            else:
                print("Debug-mfrias4, worker.py line 104. Reason is ERROR")
                self.current_event.res = 'ERROR'
                self.current_event.stats['task.sigcode'] = self.current_tool.returncode

            if 'OutOfMemory' in self.current_event.stats.get('task.output'):
                print("Debug-mfrias4, worker.py line 110. Reason is MEMOUT")
                self.current_event.res = 'MEMOUT'

            rcstrmap = self.rcstrs[self.current_task[1]]
            self.current_event.etc['exitcode'] = self.current_tool.returncode
            self.current_event.etc['exitstr'] = rcstrmap.get(self.current_tool.returncode, 'RC_Unknown')
            
            # tid, ttype, curMax, level, infto, timeout, overhead, inv, tres, tecode, testr, tstatdict
            msg_data = (self.current_task[0], self.current_task[1], self.current_event.max, self.current_event.level, self.infinite_timeout, self.timeout, self.overhead, self.proc_inv, self.current_event.res, self.current_event.etc['exitcode'], self.current_event.etc['exitstr'], self.current_event.stats)
            # If the task finished was just the invariant
            if self.proc_inv:
                print("Debug-mfrias4, worker.py line 119. Processed inv")
	        # PEND: handle other cases; just the strictly necessary for now
                assert self.current_event.res in ('SAT', 'UNSAT')
                if self.current_event.res == 'SAT':
                    print("Debug-mfrias4, worker.py line 123. Inv was SAT")
		    # Survived invariant pre-check! Prepare for full solving
                    #print "Dio SAT el invariante"
                    self.proc_inv = False
                    self.stats_inv = self.current_event.stats # keep a ref to stats dict from 1st pass
                    self.minisat = MinisatHotPipe(andrea.settings.paths['minisat_binary'])
                    self.tools = dict({'cnf': self.minisat})
                    print("Debug-mfrias4, worker.py line 130, before sending new cnf task to minisat after inv task was SAT")
                    self.handle_mission(self.current_task)

                    return
                else:
                    print("Debug-mfrias4, worker.py line 135, Inv was UNSAT")
                    pass #print "Dio UNSAT el invariante"

            # A esta altura estamos cerrando la pasada definitiva, sea 1ra o 2da

            print("Debug-mfrias4, worker.py line 140, Was the finished task an Inv? = ", self.proc_inv)

            self.current_event.finish()
            self.current_event.stats['task.msecs'] = int(1000.0 * self.current_event.dur)

            (tid, ttype, tdata, infinite_timeout, curMax, level, timeout) = self.current_task
            elapsed = andrea.network.time() - self.tool_start_time
            print ("Debug-mfrias4 worker.py line 148, elapsed = ", elapsed)
            
            if self.stats_inv:
                # If we kept a ref to a possible "first pass" stats dict, nest it within 2nd pass stats
            # This is not pretty, but should at least preserve some data w/no impact on the master for now
            # PEND: improve this; make the inv stats be always that, and full run stats always that.
            # tid, ttype, curMax, level, infto, timeout, overhead, inv, tres, tecode, testr, tstatdict
                self.current_event.stats['stats_inv'] = self.stats_inv
                msg_data = (self.current_task[0], self.current_task[1], self.current_event.max, self.current_event.level, self.infinite_timeout, self.timeout, self.overhead, self.proc_inv, self.current_event.res, self.current_event.etc['exitcode'], self.current_event.etc['exitstr'], self.current_event.stats)
                #self.current_event
                #self.timeout, # task timeoutneMission(msg_data))
            print("Debug-mfrias4, worker.py line 169. moved following 2 lines one tab left")
            andrea.network.send(DoneMission(msg_data))
            self.clear_state()
        else:
            elapsed = andrea.network.time() - self.tool_start_time
            (tid, ttype, tdata, infinite_timeout, curMax, level, timeout) = self.current_task
            print("Debug-mfrias4, worker.py line 172, main_loop_busy. elapsed = ", elapsed, "Infinite TO = ", infinite_timeout, "timeout = ", self.timeout, " I am worker ", self.my_rank)
            if (not infinite_timeout) and (elapsed > self.timeout) and not self.proc_inv:
                if not self.current_tool.aborting():
                    print("Debug-mfrias4, worker.py line 174, main_loop_busy. Non inf TO and elapsed>TO and not already aborting. I am worker ", self.my_rank)
                    print("Debug-mfrias4, worker.py line 175, about to send KillEvent on task ", self.current_task[0])
                    self.current_event_kill = self.bb.add(KillEvent(self.current_task[0]))
                    self.current_tool.abort()
            print("Debug-mfrias4, worker.py line 178, TO expired but not to be stopped (infinite TO?)", self.my_rank)
    
    def handle_mission(self, task):
        print("Debug-mfrias4, worker.py line 177, handle_mission self = ", self, " task = ", task, " I am worker ", self.my_rank)
        tid, ttype, tdata, infinite_timeout, curMax, level, new_timeout = task
        self.infinite_timeout = infinite_timeout
        self.timeout = float(new_timeout)
        self.current_tool = self.minisat

        print("Debug-mfrias4, worker.py line 170, handle_mission self.current_tool is minisat")

        if self.proc_inv:
            self.current_event = self.bb.add(TaskEvent('analysis', tid, timeout=new_timeout, curMax=curMax, level=level, inv=True))
        else:
            self.current_event = self.bb.add(TaskEvent('analysis', tid, timeout=new_timeout, curMax=curMax, level=level, inv=False))
            
        self.handler_res(tid, tdata)
             
        #handler = getattr(self, 'handle_mission_' + ttype)
        #handler(tid, tdata)
        #Cd
    
    def handler_res(self, tid, tdata):
        print("Debug-mfrias4, worker.py line 200, entered handler_res. I am worker ", self.my_rank)
        ti = andrea.network.time()
        if self.proc_inv == True: 
            #tinv = andrea.network.time()
            (header, count, res) = generate_new_cnf(self.cnf_inv, tdata, self.rels_inv_sets, self.inv_tuple2val)
            #print "Overhead generate new cnf inv = " + str(andrea.network.time() - tinv)
            #out_path = path.join(andrea.settings.paths['local_storage'], str(tid) + ".inv.cnf.out")     
            cnf_path = path.join(self.my_dir, str(tid) + ".inv.cnf")     
            self.cnf_effective = self.cnf_inv
            print("Debug-mfrias4, worker.py line 209, inside handler_res, was invariant and cnf path is", cnf_path)

        else:
            #tinv = andrea.network.time()
            (header, count, res) = generate_new_cnf(self.cnf, tdata, self.rels_sets, self.tuple2val)
            #print "Overhead generate new cnf no inv = " + str(andrea.network.time() - tinv)
            #out_path = path.join(andrea.settings.paths['local_storage'], str(tid) + ".cnf.out")
            cnf_path = path.join(self.my_dir, str(tid) + ".cnf")
            self.cnf_effective = self.cnf
            print("Debug-mfrias4, worker.py line 218, inside handler_res, was NOT invariant and cnf path is", cnf_path)


        #Correr primero el invariante y si da sat, correr lo de abajo
        self.tool_start_time = andrea.network.time()
        print("Debug-mfrias4, worker.py line 223, inside handler_res, minisat is about to be launched on cnf")
        self.minisat.launch(header, self.cnf_effective, count, res, cnf_path)
        self.overhead = andrea.network.time() - ti
        #print ("Overhead launch inv = " if self.proc_inv else "Overhead launch = ") + str(andrea.network.time() - self.tool_start_time)
