import settings
import network

from process  import Process
from tools    import Alloy, Minisat220, Reason
#from tools   import HackyPipe
from network  import WantMission, HaveMission, DoneMission
from network  import ExitToShell, Tag, Rank
from utils    import RoundRobin, write_file, secs2human
from events   import Event
from time     import sleep
from os       import path


class Worker(Process):

    def start(self):
        print("Debug-mfrias4, andrea.worker.py line 18, entered start(self)")
        self.init_tools()
        self.clear_state()
        self.main_loop()

    def init_tools(self):
        print("Debug-mfrias4, andrea.worker.py line 24, entered init_tools(self)")
        self.timeout = float(settings.experiment['timeout'])
        java_home = settings.paths['java_home']

        def make_tool(tool, sett):
            cp, cn, lp = [sett[k] for k in ['class_path', 'class_name', 'shlib_path']]
            return tool(java_home, cp, cn, lp)

	#self.alloy = HackyPipe() # experimento als2cnf | minisat220.exe
        #self.rcstrs   = dict({'als': HackyPipe.RC_STR, 'cnf': Minisat220.RC_STR})

        self.alloy    = make_tool(Alloy, settings.alloy)
        self.minisat  = Minisat220(settings.paths['minisat_binary']) if \
                      'minisat_binary' in settings.paths  else None
        self.tools    = dict({'als': self.alloy, 'cnf': self.minisat})
        self.rcstrs   = dict({'als': Alloy.RC_STR, 'cnf': Minisat220.RC_STR})

    def clear_state(self):
        print("Debug-mfrias4, andrea.worker.py line 42, entered clear_state(self)")
        "Get ready for a new mission: reset flags, etc."
        self.mission_requested = False
        self.current_task = None
        self.current_event = None
        self.current_tool = None
        self.tool_start_time = None

    def main_loop(self):
        print("Debug-mfrias4, andrea.worker.py line 51, entered main_loop(self). I am worker ", self.my_rank)
        "Main event loop for the worker."
        while not self.finished:
            print("Debug-mfrias4, andrea.worker.py line 54, in main_loop(self) and not self.finished. I am worker ", self.my_rank)
            if self.current_tool and self.current_tool.running:
                print("Debug-mfrias4, andrea.worker.py line 56, about to call main_loop_busy. self.current_tool = ", self.current_tool)
                self.main_loop_busy()
            else:
                print("Debug-mfrias4, andrea.worker.py line 59, about to call main_loop_idle. self.current_tool = ", self.current_tool, "self.current_tool.running = ", self.current_tool.running if self.current_tool else 'No tool')
                self.main_loop_idle()
            # either way, check whether we should exit
            if network.msg_waiting(Rank.MASTER, Tag.EXIT_TO_SHELL):
                network.receive(Rank.MASTER, Tag.EXIT_TO_SHELL)
                if self.current_tool and self.current_tool.running:
                    self.current_tool.abort()
                self.finished = True
            # and let's not make this that tight
            sleep(0.005)

    def main_loop_idle(self):
        print("Debug-mfrias4, andrea.worker.py line 71, entered main_loop_idle. I am worker ", self.my_rank)
        "This part of main_loop() only runs when worker is idle."
        if not self.mission_requested:
            print("Debug-mfrias4, andrea.worker.py line 74, in main_loop_idle about to WantMission. I am worker ", self.my_rank)
            network.send(WantMission())
            self.mission_requested = True
        elif network.msg_waiting(Rank.MASTER, Tag.HAVE_MISSION):
            print("Debug-mfrias4, andrea.worker.py line 78, in main_loop_idle about to HAVE_MISSION. I am worker ", self.my_rank)
            msg = network.receive(Rank.MASTER, Tag.HAVE_MISSION)
            self.current_task = msg.body # (tid, ttype, tdata)
            self.handle_mission(self.current_task)

    def main_loop_busy(self):
        print("Debug-mfrias4, andrea.worker.py line 84, entered main_loop_busy. I am worker ", self.my_rank)
        "This part of main_loop() only runs when agent is busy."
        if self.current_tool.finished():
            print("Debug-mfrias4, andrea.worker.py line 87 self.current_tool.finished() = ", self.current_tool.finished())
            self.current_event.stats = self.current_tool.stats
            if self.current_tool.finished_via() == Reason.EXIT_OK:
                print("Debug-mfrias4, andrea.worker.py line 90 self.current_tool.finished_via() = ", self.current_tool.finished_via(), " with reason EXIT_OK")
                ans = self.current_tool.veredict()
                self.current_event.res = 'SAT' if ans == True else 'UNSAT'
                print("Debug-mfrias4, andrea.worker.py line 93 self.current_tool.veredict() = ", self.current_tool.veredict(), " with result ", self.current_event.res)
            elif self.current_tool.finished_via() == Reason.KILL_OK:
                print("Debug-mfrias4, andrea.worker.py line 95 self.current_tool.finished_via() = ", self.current_tool.finished_via(), " with result KILL_OK (TIMEOUT)")
                self.current_event.res = 'TIMEOUT'
                self.current_event_kill.finish()
            elif self.current_tool.finished_via() == Reason.EXIT_KO:
                print("Debug-mfrias4, andrea.worker.py line 99 self.current_tool.finished_via() = ", self.current_tool.finished_via(), " with result EXIT_KO (ERROR)")
                self.current_event.res = 'ERROR'
                self.current_event.stats['task.retcode'] = self.current_tool.returncode
            else:
                print("Debug-mfrias4, andrea.worker.py line 103 tool finished for some unexpected reason which is an ERROR)")
                self.current_event.res = 'ERROR'
                self.current_event.stats['task.sigcode'] = self.current_tool.returncode
    
            if 'OutOfMemory' in self.current_event.stats.get('task.output'):
                print("Debug-mfrias4, andrea.worker.py line 108, tool finished by MEMOUT ")
                self.current_event.res = 'MEMOUT'
        
            rcstrmap = self.rcstrs[self.current_task[1]]
            self.current_event.etc['exitcode'] = self.current_tool.returncode
            self.current_event.etc['exitstr'] = rcstrmap.get(self.current_tool.returncode, 'RC_Unknown')
            self.current_event.finish()
        
            self.current_event.stats['task.msecs'] = int(1000.0 * self.current_event.dur)


            #DoneMission missing args tidY, ttypeY, curMax, level, infto, timeout, overhead, inv, tresY, tecodeY, testrY, tstatdictY
            #self, map.my_rank, Rank.MASTER, Tag.DONE_MISSION, results
            print("Debug-mfrias4, andrea.worker.py line 121, self.current_task = ", self.current_task)
            msg_data = (self.current_task[0], # tid
                self.current_task[1], # ttype
                
                self.current_event.res, # main result ('SAT', 'ERROR', etc..)
                self.current_event.etc['exitcode'],  # main exitcode or signal number
                self.current_event.etc['exitstr'],  # ascii version of it, if available
                self.current_event.stats, # dict w/task statistics and output
            )
            print("Debug-mfrias4, andrea.worker.py line 125, about to send DoneMission")
            network.send(DoneMission(msg_data))
            self.clear_state()
        else:
            print("Debug-mfrias4, andrea.worker.py line 128, tool not yet finished. Elapsed time = ", network.time() - self.tool_start_time, " TO = ", self.timeout)
            elapsed = network.time() - self.tool_start_time
            if elapsed > self.timeout:
                print("Debug-mfrias4, andrea.worker.py line 131, tool must abort")
                if not self.current_tool.aborting():
                    self.current_event_kill = self.bb.add(KillEvent(self.current_task[0]))
                    self.current_tool.abort()

    def handle_mission(self, task):
        print("Debug-mfrias4, andrea.worker.py line 136, entered handle_mission. I am worker ", self.my_rank)
        tid, ttype, tdata = task
        self.current_tool = self.tools[ttype]
        self.current_event = self.bb.add(TaskEvent('analysis', tid))
        handler = getattr(self, 'handle_mission_' + ttype)
        print("Debug-mfrias4, andrea.worker.py line 141, in handle_mission. I am worker ", self.my_rank, " handling mission handle_mission_", ttype)
        handler(tid, tdata)

    def handle_mission_als(self, tid, spec_contents):
        print("Debug-mfrias4, andrea.worker.py line 141, entered handle_mission_als. I am worker ", self.my_rank)
        my_local_dir = settings.local_store_dir(self.my_rank)
        als_path = path.join(my_local_dir, tid)
        write_file(als_path, spec_contents)
        self.current_tool.launch(als_path)
        #self.current_tool.launch([als_path], als_path + '.out')
        self.tool_start_time = network.time()

    def handle_mission_cnf(self, tid, dimacs_contents):
        print("Debug-mfrias4, andrea.worker.py line 132 entering handle_mission_cnf. I am worker ", self.my_rank)
        my_local_dir = settings.local_store_dir(self.my_rank)
        cnf_path = path.join(my_local_dir, tid)
        write_file(cnf_path, dimacs_contents)
        print("Debug-mfrias4, andrea.worker.py line 154 before lunching current_tool = ", self.current_tool)
        print("Debug-mfrias4, andrea.worker.py line 155 before lunching current_tool with cnf_path = ", cnf_path)
        self.current_tool.launch(cnf_path)
        self.tool_start_time = network.time()
    
