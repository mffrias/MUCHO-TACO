import settings
import network

from process  import Process
from tools    import Alloy, Minisat220, Reason
#from tools   import HackyPipe
from network  import WantMission, HaveMission, DoneMission
from network  import ExitToShell, Tag, Rank
from utils    import RoundRobin, write_file, secs2human
from events   import Event, TaskEvent, KillEvent
from time     import sleep
from os       import path


class Worker(Process):

    def start(self):
        self.init_tools()
        self.clear_state()
        self.main_loop()

    def init_tools(self):
        self.timeout = float(settings.experiment['timeout'])
        java_home = settings.paths['java_home']

        def make_tool(tool, sett):
            cp, cn, lp = [sett[k] for k in
            'class_path', 'class_name', 'shlib_path']
            return tool(java_home, cp, cn, lp)

	#self.alloy = HackyPipe() # experimento als2cnf | minisat220.exe
        #self.rcstrs   = dict({'als': HackyPipe.RC_STR, 'cnf': Minisat220.RC_STR})

        self.alloy    = make_tool(Alloy, settings.alloy)
        self.minisat  = Minisat220(settings.paths['minisat_binary']) if \
                      'minisat_binary' in settings.paths  else None
        self.tools    = dict({'als': self.alloy, 'cnf': self.minisat})
        self.rcstrs   = dict({'als': Alloy.RC_STR, 'cnf': Minisat220.RC_STR})

    def clear_state(self):
        "Get ready for a new mission: reset flags, etc."
        self.mission_requested = False
        self.current_task = None
        self.current_event = None
        self.current_tool = None
        self.tool_start_time = None

    def main_loop(self):
        "Main event loop for the worker."
        while not self.finished:
            if self.current_tool and self.current_tool.running:
                self.main_loop_busy()
            else:
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
        "This part of main_loop() only runs when worker is idle."
        if not self.mission_requested:
            network.send(WantMission())
            self.mission_requested = True
        elif network.msg_waiting(Rank.MASTER, Tag.HAVE_MISSION):
            msg = network.receive(Rank.MASTER, Tag.HAVE_MISSION)
            self.current_task = msg.body # (tid, ttype, tdata)
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
            self.current_event.finish()
        
            self.current_event.stats['task.msecs'] = int(1000.0 * self.current_event.dur)

            msg_data = (self.current_task[0], # tid
                self.current_task[1], # ttype
                self.current_event.res, # main result ('SAT', 'ERROR', etc..)
                self.current_event.etc['exitcode'],  # main exitcode or signal number
                self.current_event.etc['exitstr'],  # ascii version of it, if available
                self.current_event.stats, # dict w/task statistics and output
            )
            network.send(DoneMission(msg_data))
            self.clear_state()
        else:
            elapsed = network.time() - self.tool_start_time
            if elapsed > self.timeout:
                if not self.current_tool.aborting():
                    self.current_event_kill = self.bb.add(KillEvent(self.current_task[0]))
                    self.current_tool.abort()

    def handle_mission(self, task):
        tid, ttype, tdata = task
        self.current_tool = self.tools[ttype]
        self.current_event = self.bb.add(TaskEvent('analysis', tid))
        handler = getattr(self, 'handle_mission_' + ttype)
        handler(tid, tdata)

    def handle_mission_als(self, tid, spec_contents):
        my_local_dir = settings.local_store_dir(self.my_rank)
        als_path = path.join(my_local_dir, tid)
        write_file(als_path, spec_contents)
        self.current_tool.launch(als_path)
        #self.current_tool.launch([als_path], als_path + '.out')
        self.tool_start_time = network.time()

    def handle_mission_cnf(self, tid, dimacs_contents):
        my_local_dir = settings.local_store_dir(self.my_rank)
        cnf_path = path.join(my_local_dir, tid)
        write_file(cnf_path, dimacs_contents)
        self.current_tool.launch(cnf_path)
        self.tool_start_time = network.time()
    
