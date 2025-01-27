import network
import settings

from utils import secs2human
from sys import stdout


class Event:
    def __init__(self, group_id, event_id, task_id=None, timeout=0, curMax=0, level=0):
        self.t_i = network.time()
        self.t_f = None
        self.gid = group_id
        self.eid = event_id
        self.tid = task_id
        self.src = network.map.my_rank
        self.res = None
        self.etc = dict()
        self.timeout = timeout
        self.max = curMax
        self.level = level
    
    def finish(self):
        self.t_f = network.time()
        self.dur = self.t_f - self.t_i
        filter = settings.logging['filter_stdout']
        if filter.match(self.gid) or filter.match(self.eid):
            if self.eid != 'kill': stdout.write(str(self))
    
    def finished(self):
        return self.t_f != None
    
    def result(self, result):
        self.res = result
        return self
    
    # for sort() key usage
    def get_event(self):   return self.gid + self.eid
    def get_start(self):   return self.t_i
    def get_end(self):     return self.t_f
    def get_dur(self):     return self.dur
    def get_tid(self):     return self.tid


class TaskEvent(Event):
    def __init__(self, eid, tid, timeout=0, curMax=0, level=0):
        Event.__init__(self, 'task', eid, tid, timeout=timeout, curMax=curMax, level=level)

    def __str__(self):
        if self.stats:
            #      ti  tf  dur   rank  tid    max     lev        res  to       solvt
            fmt = '%s--%s  (%s)  %3d   %-30s  max: %2d lev: %2d  %8s  to: %-3s  %s st  %5d pv  %6d tv  %6d cl\n'
	    
	    solver_time = 'TO'

        if 'solver.msecs' in self.stats:
            solver_time = secs2human(int(self.stats.get('solver.msecs', '0')) / 1000.0)
            pv, tv = self.stats.get('cnf.privars', '0'), self.stats.get('cnf.totvars', '0')
            cl = self.stats.get('cnf.clauses', '0')
            row = fmt % (
            secs2human(self.t_i, msecs=False), secs2human(self.t_f, msecs=False), secs2human(self.dur), self.src, 
            self.tid, int(self.max), int(self.level), self.res, self.timeout, solver_time, int(pv), int(tv), int(cl))
        elif self.res == 'ERROR':
            #      ti  tf  dur   rank  tid    max       lev      res  to
            fmt = '%s--%s  (%s)  %3d   %-30s  max: %2d lev: %2d  %8s  to: %s %20s\n'
            row = fmt % (
            secs2human(self.t_i, msecs=False), secs2human(self.t_f, msecs=False), secs2human(self.dur),
            self.src, self.tid, int(self.max), int(self.level), self.res, self.timeout, str(self.etc))
        else:
            #      ti  tf  dur   rank  tid    max      lev       res  to
            fmt = '%s--%s  (%s)  %3d   %-30s  max: %2d lev: %2d  %8s  to: %s\n'
            row = fmt % (
            secs2human(self.t_i, msecs=False), secs2human(self.t_f, msecs=False), secs2human(self.dur),
            self.src, self.tid, int(self.max), int(self.level), self.res, self.timeout)
        return row


class KillEvent(TaskEvent):
    def __init__(self, tid):
        TaskEvent.__init__(self, 'kill', tid)

    def __str__(self):
        return '%s--%s  (%s)   %3d   %4s.%-22s                    %s\n' % (
        secs2human(self.t_i, msecs=False), secs2human(self.t_f, msecs=False), secs2human(self.dur),
        self.src, self.gid, self.eid, self.tid)


class WeatherEvent(Event):
    def __init__(self, eid, stats_dict):
        Event.__init__(self, 'wrep', eid)
        self.etc = stats_dict
        self.finish()

    def __str__(self):
        #fmt = '%d:qued  %d:actv  %d:free  %d:done  ( %dxS  %dxU  %dxTO  %dxMO  %dxErr )'
        fmt = 'Tasks:  %d queued,  %d active,  %d done ( %d Sat, %d Uns, %d TO, %d MO, %d Err )  Wks: %d busy, %d idle\n'
        info = fmt % (self.etc['tasks_idle'],
                self.etc['tasks_busy'],
                self.etc['tasks_done'],
                self.etc['SAT'], self.etc['UNSAT'], 
                self.etc['TIMEOUT'], self.etc['MEMOUT'], self.etc['ERROR'],
                self.etc.get('workers_busy', 0),
                self.etc.get('workers_idle', 0))
        return '          %-32s %s' % (secs2human(self.t_i, msecs=False), info)

