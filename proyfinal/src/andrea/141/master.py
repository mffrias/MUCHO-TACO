import settings
import network
import csv
import os

from process import Process
from utils   import write_file
from network import WantMission, HaveMission, DoneMission
from network import ExitToShell
from utils   import RoundRobin, list_all_files, read_file
from events  import Event, WeatherEvent
from pprint  import pformat
from time    import sleep


class Master(Process):

    def start(self):

        self.tasks_idle = []
        self.tasks_busy = set()
        self.tasks_done = set()
        self.workers_idle = []
        self.workers_busy = dict()

        self.donetask_outcomes = {'SAT': 0, 'UNSAT': 0, 'TIMEOUT': 0, 'MEMOUT': 0, 'ERROR': 0}

        self.tasklog_file = open(settings.outdir_path('andrea.tlog.csv'), 'w')
        self.tasklog_file.write('#task_id,task_type,worker_rank,outcome,rc_num,rc_str,tot_msec_solv,tot_msec_task\n')
        self.tasklog = csv.writer(self.tasklog_file)

        self.weather_reports = settings.logging['weather_reports']

        if self.weather_reports: # Force wrep before populating task queue
            self.weather_every = float(settings.logging['weather_every'])
            self.bb.add(WeatherEvent('preinit', self.get_stats()))
            self.last_weather = network.time()

        self.populate_task_queue() # Load all task files into main memory (!)

        if self.weather_reports: # Force wrep when ready to start working
            self.bb.add(WeatherEvent('initial', self.get_stats()))
            self.last_weather = network.time()

        self.main_loop() # Run main event loop until done

        self.send_exit_messages() # Tell everyone to quit

        if self.weather_reports: # Force a final weather report just before exiting
            self.bb.add(WeatherEvent('final', self.get_stats()))
        
        self.tasklog_file.close()


    def main_loop(self):

        while not self.finished:

            if network.msg_waiting():
                self.handle_message(network.receive())

            if self.workers_idle and self.tasks_idle:
                worker, task = self.assign_mission()
                network.send(HaveMission(worker, task))

            if not (self.tasks_idle or self.workers_busy):
                self.finished = True

            if self.weather_reports:
                current_time = network.time()
                if current_time - self.last_weather > self.weather_every:
                    self.last_weather = current_time
                    self.bb.add(WeatherEvent('update', self.get_stats()))
        
        sleep(0.002)


    def handle_message(self, msg):
        if isinstance(msg, WantMission):
            self.mission_requested(msg.src)
        elif isinstance(msg, DoneMission):
            tid, ttype, tres, tecode, testr, tstatdict = msg.body
            self.mission_finished(msg.src, tid, ttype, tres, tecode, testr, tstatdict)
        else:
            raise Exception("Master received an unknown message.")


    def mission_requested(self, worker):
        
        """
        Event handler: called when idle worker announces WANT_MISSION.
        
        This handler marks a nonbusy but not-yet-idle worker as idle.
        If known, worker should not be 'busy' anymore (see DONE_MISSION)
        and should not be idle yet (and will be after this call).
        """
        
        if worker in self.workers_busy:
            raise Exception("Got WANT_MISSION from busy worker!?")
        if worker in self.workers_idle:
            raise Exception("Got WANT_MISSION from already idle worker!?")

        self.workers_idle.append(worker)


    def assign_mission(self):
        
        """
        Event handler: called when a new mission is needed.
        
        Returns (worker_id, (tid, ttype, tdata)) tuple.
        """
        
        tid, ttype, tdata = self.tasks_idle.pop(0)
        self.tasks_busy.add(tid)
        worker = self.workers_idle.pop(0)
        self.workers_busy[worker] = tid
        return worker, (tid, ttype, tdata)


    def mission_finished(self, worker, tid, ttype, tres, tecode, testr, tstats):
        
        """
        Event handler: called when busy worker announces DONE_MISSION.
    
        Worker should be busy (and, of course, not idle); this call
        moves its status to nonbusy (but not yet idle, see WANT_MISSION).
        The associated task is moved from busy to done status.
    
        tres is a string summarizing the final outcome of the task,
        e.g. 'SAT', 'UNSAT', 'TIMEOUT', 'MEMOUT', or 'ERROR'.

        tecode is a numerical exit code (or signal if tool died w/one)
        e.g. 0, 1, etc.

        testr is its interpretation as a string (from the tool driver)
  
        tstats is a dict with stats about the task, which

        MUST contain, at the very least:
            a 'task.msecs' entry with the complete task duration in ms
            a 'task.output' entry with any stdout/err of task (text)
        
        MAY contain lots of other stuff, see below (and de-hack :p )
        """
        
        # Remove worker from workers_busy.
        # Do not add to workers_idle yet! (until WANT_MISSION rcvd)
        
        if worker in self.workers_busy:
            if self.workers_busy[worker] == tid:
                del self.workers_busy[worker]
            else:
                raise Exception("Inconsistency in workers_busy map!?")
        else:
            raise Exception("Got DONE_MISSION from nonbusy worker!?")
        
        
        if tid in self.tasks_busy and tid not in self.tasks_done:
            self.tasks_busy.remove(tid)
            self.tasks_done.add(tid)
        else:
            raise Exception("Got DONE_MISSION involving nonbusy or done task!?")
    
        # write full output, if present. to task.foo.out
        # and remove it from the dict
        if tstats and tstats.get('task.output'):
            write_file(settings.outdir_path(tid + '.out'), tstats['task.output'])
            del tstats['task.output']

        # write rest of stats, if any, to task.foo.dat
        if tstats and len(tstats) > 0:
            write_file(settings.outdir_path(tid + '.dat'), pformat(tstats) + '\n')
    
        # write a row to the tasklog: remove ext from tid ...
        if tid.endswith('.als'):
            tid = tid[:-4]
        elif tid.endswith('.jf'):
            tid = tid[:-3]
    
        # find out total_time_task and total_time_solving
        tt_task = tstats['task.msecs'] # mandatory for any driver
        tt_solv = None
        if tres == 'TIMEOUT':
            tt_solv = 1000 * int(settings.experiment['timeout'])
        else:
            tt_solv = tstats.get('solver.msecs', '0')

        row = [tid, ttype, worker, tres, tecode, testr, tt_solv, tt_task]
        self.tasklog.writerow(row)
        self.tasklog_file.flush()

        # increment one of the outcome counters
        if tres in self.donetask_outcomes:
            self.donetask_outcomes[tres] += 1
        else:
            raise Exception("Unknown outcome: " + tres)


    def get_stats(self):
        attribs = ['tasks_idle', 'tasks_busy', 'tasks_done', 'workers_idle', 'workers_busy']
        quantities = [len(getattr(self, a)) for a in attribs]
        done_attribs = ['SAT', 'UNSAT', 'TIMEOUT', 'MEMOUT', 'ERROR']
        done_quantities = [self.donetask_outcomes[a] for a in done_attribs]
        return dict(zip(attribs + done_attribs, quantities + done_quantities))


    def populate_task_queue(self):
        queue_create_phase = self.bb.add(Event('main', 'queue.create'))
        task_paths = list_all_files(settings.experiment['tasks'], ('.als', '.cnf'))
        #print task_paths
        for task_path in task_paths:
            tid = os.path.basename(task_path)
            ext = os.path.splitext(tid)[1]
            ttype = ext.lstrip('.')
            tbody = read_file(task_path)
            self.tasks_idle.append((tid, ttype, tbody))

        # hack para garantizar q el menor scope vaya siempre antes en el scheduling
        #f = lambda string: string[string.find('-s')+2:string.find('-s')+4]+string
        #self.tasks_idle = sorted(self.tasks_idle, key=lambda t: f(t[0]))

        queue_create_phase.result('%d tasks' % len(self.tasks_idle))
        queue_create_phase.finish()


    def send_exit_messages(self):
        "Send an EXIT message to every process except our own."
        for rank in (network.map.ranks() - set([self.my_rank])):
            network.send(ExitToShell(rank))

