import andrea.network
import andrea.settings
from andrea.network import *

from utils import ensure_directory


class Process:

    """
    ABC for any process that will get an MPI rank.
    """

    def __init__(self):
        self.init_local_dirs()
        andrea.network.sync()
        self.finished = False
        self.my_rank = andrea.network.map.my_rank
        self.my_host = andrea.network.map.my_host
        self.my_dir  = andrea.settings.local_store_dir(self.my_rank)
        self.bb = BigBrother(self.my_dir + '/events_' + str(self.my_rank) + '.pck')
        print("Debug-mfrias4: process.py line 21. Dir in BigBrother bb = ", self.my_dir + '/events_' + str(self.my_rank) + '.pck')

    def init_local_dirs(self):
        "Ensure all necessary local storage dirs exist on our host."

        print("Debug-mfrias4: process.py line 26. network_map = ", andrea.network.map)

        if andrea.network.map.am_host_leader():
            print("Debug-mfrias4: process.py line 28. I am the host leader (the one with smallest rank within the host)")
            # To avoid race conditions, one process makes all.
            ensure_directory(andrea.settings.local_store())
            for rank in andrea.network.map.ranks_of(andrea.network.map.my_host):
                print("Debug-mfrias4 process.py line 32. Rank is ", rank)
                ensure_directory(andrea.settings.local_store_dir(rank))

    def cleanup(self):
        try:
            self.bb.dump_update()
        except AttributeError:
            pass


from _pickle import dump

class BigBrother:

    def __init__(self, pickle_path):
        self.events = []
        self.path = pickle_path
        f = open(self.path, 'w')
        f.close()

    def add(self, event):
        self.events.append(event)
        if len(self.events) > 20:
            #before = len(self.events)
            self.dump_update()
            #after = len(self.events)
            #print 'BB:updated %s ; %d -> %d' % (self.path, before, after)
        return event

    def dump_update(self):
        evts_finished = [e for e in self.events if e.finished()]
        if len(evts_finished) > 0:
            evts_active = [e for e in self.events if not e.finished()] # could do 1 pass only
            f = open(self.path, 'ab')
            dump(evts_finished, f)
            f.close()
            self.events = evts_active

