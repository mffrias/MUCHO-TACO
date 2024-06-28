from mpi4py import MPI


map = None

t_0 = None



class Rank:
    """
    Constants to identify special processes (singleton, fixed rank).
    """
    MASTER = 0


class Role:
    """
    Constants to identify roles and dict to translate them back to string.
    """
    M, W = range(2)
    initials = dict(zip(range(2), ('m', 'w')))
    fullname = dict(zip(range(2), ('Master', 'Worker')))


class Tag:
    """
    Constants required by MPI to identify different message types, and
    dicts mapping their values back to (short and long) name strings.
    """
    (WANT_MISSION, HAVE_MISSION, DONE_MISSION, EXIT_TO_SHELL) = range(4)

    initials = dict(zip(range(4),
     ('WM', 'HM', 'DM', 'Ex')))
    fullname = dict(zip(range(4),
     ('WANT_MISSION', 'HAVE_MISSION', 'DONE_MISSION', 'EXIT_TO_SHELL')))


class ProcessMap:
    """
    Provides a simple interface to find out details about all processes
    involved in the current experiment (including self), such as their
    ranks, roles, physical machine where they are located, etc.
    """
    def __init__(self):

        # start by obtaining the essential info about self
        self.my_rank = MPI.COMM_WORLD.Get_rank()
        self.my_host = MPI.Get_processor_name()
        self.my_role = None
        self.comm_size = MPI.COMM_WORLD.Get_size()

        # now exchange that info with all other process
        self.rank_list = range(self.comm_size)
        self.host_list = MPI.COMM_WORLD.allgather(self.my_host)
        self.rank_set  = set(self.rank_list)
        self.host_set  = set(self.host_list)

        # precompute inverse map (host -> set of ranks)
        self.ranks_on_host = dict()
        for host in self.host_set:
            ranks = []
            for r in self.rank_set:
                if self.host_of(r) == host:
                    ranks.append(r)
            self.ranks_on_host[host] = ranks

        # and assign roles to ranks
        self.role_of_rank = dict()
        for host in self.host_set:
            ranks_here = self.ranks_on_host[host]
            for r in ranks_here:
                self.role_of_rank[r] = Role.W
        self.role_of_rank[0] = Role.M
        self.my_role = self.role_of_rank[self.my_rank]


    def ranks(self):
        "The set of all participating ranks."
        return self.rank_set

    def hosts(self):
        "The set of all participating machines."
        return self.host_set

    def ranks_of(self, host):
        "List all ranks running on a given host."
        return self.ranks_on_host[host]

    def host_of(self, rank):
        "Find out the host where a given rank is running."
        return self.host_list[rank]

    def role_of(self, rank):
        "Find out the role of a given rank."
        return self.role_of_rank[rank]

    def workers(self):
        "The set of all ranks acting as workers."
        return filter(
          lambda r: self.role_of(r) == Role.W,
          self.rank_set)

    def workers_of(self, host):
        "List all worker processes on a given host."
        return filter(
          lambda r: self.role_of(r) == Role.W,
          self.ranks_of(host))

    def leader_of(self, host):
        "Return the lowest-ranked process on a given host."
        return min(self.ranks_of(host))

    def am_host_leader(self):
        "Determine whether I have the lowest rank within my host."
        return self.my_rank == self.leader_of(self.my_host)

    def am_master(self):
        "Determine whether I have the lowest possible rank."
        return self.my_rank == Rank.MASTER

    def write_table(self, output):
        """Make a nicely formatted table describing the complete
        environment configuration (hosts, ranks, roles..) and
        write it to the given file-like object."""
        from utils import ProcessTable
        pt = ProcessTable(output, self.ranks_on_host, self.role_of_rank)
        del pt

    def root(self):
        return MPI.ROOT
    
    def myRank(self):
        comm = MPI.COMM_WORLD
        return comm.Get_rank()

class Message:
    """
    Domain-specific wrapper around MPI messages (base class), with
    the dual purpose of added convenience (clever defaults, etc.)
    and improved readability of higher-level code.
    """

    def __init__(self, source, dest, tag, body=None):
        self.src  = source
        self.dest = dest
        self.tag  = tag
        self.body = body

    def __str__(self):
        return "<Message from %d to %d>" % (self.src, self.dest)


class WantMission(Message):
    def __init__(self):
        Message.__init__(self, map.my_rank, Rank.MASTER, Tag.WANT_MISSION, '')

class HaveMission(Message):
    def __init__(self, worker, task): # task is a (tid, ttype, tdata) tuple
        Message.__init__(self, Rank.MASTER, worker, Tag.HAVE_MISSION, task)

class DoneMission(Message):
    def __init__(self, results): # results is a (tid, ttype, tres, trc, tstats) tuple
        Message.__init__(self, map.my_rank, Rank.MASTER, Tag.DONE_MISSION, results)

class ExitToShell(Message):
    def __init__(self, worker):
        Message.__init__(self, Rank.MASTER, worker, Tag.EXIT_TO_SHELL, '')


def sync():
    """Force an immediate rendezvous of all processes (blocking every caller
    until all have called, then releasing them all concurrently)."""
    MPI.COMM_WORLD.Barrier()

def sync_zero_time():
    """Same as above, but with the specific purpose of clock sync. On clusters
    that lack (real, absolute) synchronization between system clocks, this can
    be useful to simulate a (rough) replacement via subtraction."""
    global t_0
    MPI.COMM_WORLD.Barrier()
    t_0 = MPI.Wtime()

def time():
    global t_0
    return MPI.Wtime() - t_0

def send(msg):
    """Send a message --any instance of a Message subclass-- to another process."""
    MPI.COMM_WORLD.send(msg, msg.dest, msg.tag)

    """Receive a new message from another process. Both the sender rank and
    the message tag filters are optional (default is 'any'). Note that, if no
    suitable message is waiting to be received, this function will block until
    one arrives (see msg_waiting() for an alternative)."""
def receive(source_filter=MPI.ANY_SOURCE, tag_filter=MPI.ANY_TAG):
    return MPI.COMM_WORLD.recv(None, source_filter, tag_filter)

    """Test for availability of a (matching) newly arrived message. This call
    may return True or False, but won't block in either case. If the result is
    True, a subsequent receive() with same filters will not block either."""
def msg_waiting(source_filter=MPI.ANY_SOURCE, tag_filter=MPI.ANY_TAG):
    return MPI.COMM_WORLD.Iprobe(source_filter, tag_filter)

def broadcast(msg):
    comm = MPI.COMM_WORLD
    rank = comm.Get_rank()

    res = comm.bcast(msg, root=0)

    return res