import andrea.network
import andrea.settings

from utils import secs2human
from sys import stdout


class Event:
    def __init__(self, group_id, event_id, task_id=None, timeout=0, curMax=0, level=0, inv=False):
        self.t_i = andrea.network.time()
        self.t_f = None
        self.gid = group_id
        self.eid = event_id
        self.tid = task_id
        self.src = andrea.network.map.my_rank
        self.res = None
        self.etc = dict()
        self.timeout = timeout
        self.max = curMax
        self.level = level
        self.inv = inv
    
    def finish(self):
        self.t_f = andrea.network.time()
        self.dur = self.t_f - self.t_i
        print("Debug-mfrias4 events.py line 26. Entered finish after duration = ", self.dur, " for event ", self)
        filter = andrea.settings.logging['filter_stdout']
        if filter.match(self.gid) or filter.match(self.eid):
            print("Debug-mfrias4 events.py line 28. Entered filter.match(self.gid) or filter.match(self.eid)")
            if self.eid != 'kill': 
                stdout.write(str(self))
    
    def finished(self):
        print("Debug-mfrias4 events.py line 32. finished = ", self.t_f != None)
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


class WeatherEvent(Event):
    def __init__(self, eid, stats_dict):
        print("Debug-mfrias4, events.py line 47. Constructor WeatherEvent")
        Event.__init__(self, 'wrep', eid)
        self.etc = stats_dict
        self.finish()

    def __str__(self):
        print("Debug-mfrias4, events.py line 53. WeatherEvent toString")
        #fmt = '%d:qued  %d:actv  %d:free  %d:done  ( %dxS  %dxU  %dxTO  %dxMO  %dxErr )'
        fmt = 'Tasks:  %d queued,  %d active,  %d done ( %d Sat, %d Uns, %d TO, %d MO, %d Err )  Wks: %d busy, %d idle\n'
        info = fmt % (self.etc['tasks_idle'], self.etc['tasks_busy'], self.etc['tasks_done'], self.etc['SAT'], self.etc['UNSAT'], self.etc['TIMEOUT'], self.etc['MEMOUT'], self.etc['ERROR'], self.etc.get('workers_busy', 0), self.etc.get('workers_idle', 0))
        return '          %-32s %s' % (secs2human(self.t_i, msecs=False), info)


class TaskEvent(Event):
    def __init__(self, eid, tid, timeout=0, curMax=0, level=0, inv=False):
        print("Debug-mfrias4, events.py line 62. constructor TaskEvent")
        Event.__init__(self, 'task', eid, tid, timeout=timeout, curMax=curMax, level=level, inv=inv)

    def __str__(self):
        #      ti  tf  dur   rank  tid        max    lev    res  inv     to
        print("Debug-mfrias4, events.py line 67. TaskEvent toString")
        fmtbase = '%s--%s  (%s)  %3d   %-40.40s   m%-3d  L%-3d  %8s  %5s     %6.1f to     '
        inv = '(inv)' if self.inv else ''
        if self.stats:
            print("Debug-mfrias4, events.py line 72. TaskEvent toString, self.stats = ", self.stats)
            fmt = fmtbase + '%s st  %5d pv  %6d tv  %6d cl\n'
        solver_time = 'TO'
        if 'solver.msecs' in self.stats:
            print("Debug-mfrias4, events.py line 76. solver.msecs in self.stats")
            floatingseconds = int(self.stats.get('solver.msecs', '0')) / 1000.0
            print("Debug-mfrias4, events.py line 78. seconds = ", floatingseconds)
            solver_time = secs2human(floatingseconds)
            print("Debug-mfrias4, events.py line 80. solver_time = ", solver_time, " floatingseconds = ", floatingseconds)
            pv, tv = self.stats.get('cnf.privars', '0'), self.stats.get('cnf.totvars', '0')
            cl = self.stats.get('cnf.clauses', '0')
            row = fmt % (
            secs2human(self.t_i, msecs=False), secs2human(self.t_f, msecs=False), secs2human(self.dur), self.src, 
            self.tid, int(self.max), int(self.level), self.res, inv, float(self.timeout), solver_time, int(pv), int(tv), int(cl))
        elif self.res == 'ERROR':
            print("Debug-mfrias4, events.py line 83. self.res == ERROR")
            fmt = fmtbase + '%20s\n'
            row = fmt % (
            secs2human(self.t_i, msecs=False), secs2human(self.t_f, msecs=False), secs2human(self.dur),
            self.src, self.tid, int(self.max), int(self.level), self.res, inv, float(self.timeout), str(self.etc))
        else:
            print("Debug-mfrias4, events.py line 89. not solver.msecs and not self.res == ERROR")
            fmt = fmtbase + '\n'
            row = fmt % (
            secs2human(self.t_i, msecs=False), secs2human(self.t_f, msecs=False), secs2human(self.dur),
            self.src, self.tid, int(self.max), int(self.level), self.res, inv, float(self.timeout))
        return row


class KillEvent(TaskEvent):
    def __init__(self, tid):
        print("Debug-mfrias4, events.py line 95. constructor KillEvent")
        TaskEvent.__init__(self, 'kill', tid)

    def __str__(self):
        print("Debug-mfrias4, events.py line 99. toString KillEvent")
        return '%s--%s  (%s)   %3d   %4s.%-22s                    %s\n' % (
        secs2human(self.t_i, msecs=False), secs2human(self.t_f, msecs=False), secs2human(self.dur),
        self.src, self.gid, self.eid, self.tid)



