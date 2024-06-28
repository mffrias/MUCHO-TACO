import os
import datetime


def secs2human(s, msecs=True):
    """
    Convert a duration in secs to human-readable text e.g. '02:15:03.847'.
    """
    if msecs:
        ms = int((s - int(s)) * 1000)
    s = int(s)
    while s >= 24*60*60: s -= 24*60*60
    h = s / (60*60)
    s -= h*60*60
    m = s / 60
    s -= m*60
    if msecs:
        return '%s.%03d' % ( str(datetime.time(h, m, s)), ms )
    else:
        return str(datetime.time(h, m, s))


def secs2human_old(seconds, use_msecs=False):
    "Convert a duration in seconds to human-readable text, e.g. '02:15:03'."
    if use_msecs and seconds < 0.95:
        return '%3d msec' % round(seconds * 1000.0)
    else:
        s = int(round(seconds))
        t = []
        h = s / 3600 ; s = s % 3600
        m = s /   60 ; s = s % 60
        return '%2d:%02d:%02d' % (h, m, s) if h > 0 else \
               '   %2d:%02d' % (m, s) if m > 0 else \
               '    0:%02d' % s
        """
        lengths = [60*60, 60, 1]
        for length in lengths:
            value = seconds / length
            seconds = seconds % length
            if value > 0:
                time.append('%02d' % value)
            else:
                time.append('  ')
        return ':'.join(time)
        """


def secs2human_older(seconds):
    "Convert a duration in seconds to human-readable text, e.g. '2m35s'."
    if seconds < 0.95:
        return '%dms' % round(seconds * 1000.0)
    else:
        seconds = int(round(seconds))
        time = []
        parts = [('d', 60*60*24), ('h', 60*60), ('m', 60), ('s', 1)]
        for suffix, length in parts:
            value = seconds / length
            if value > 0:
                seconds = seconds % length
                time.append('%s%s' % (str(value), suffix))
            if seconds < 1:
                break
        return ''.join(time)


def read_file(path):
    "Read a file from disk and return its whole contents as a string."
    file = open(path, 'r')
    result = file.read()
    file.close()
    return result


def write_file(path, contents):
    "Write a string to a file on disk, overwriting any existing file."
    file = open(path, 'w')
    file.write(contents)
    file.close()


def list_all_files(path, exts):
    """
    Recursively search the given path for files ending in (any of the)
    given extensions; return a list of matches. If path is a regular
    file (not a directory), it will be the only candidate for a match.
    """
    if os.path.isfile(path):
        return [path] if path.endswith(exts) else []
    elif os.path.isdir(path):
        result = []
        for (dir, subdirs, files) in os.walk(path):
            result += map(lambda f: dir + "/" + f,
                       filter(lambda f: f.endswith(exts), files))
        return result
    else:
        raise Exception("Neither file nor directory: " + path)


def ensure_directory(path):
    """
    If path exists and is a directory, return False. If path does not
    exist, create it (as well as any other parent dirs as needed) and
    return True. TODO: handle "exists but is not a directory" case.
    """
    if os.path.isdir(path):
        return False
    else:
        os.makedirs(path, 0o744)
        return True


class RoundRobin:
    """
    Iterate a given list endlessly, in a round-robin fashion, wrapping
    around back to the first element after returning the last one.
    
    (This could be rewritten using generators in a much more Pythonic way.)
    """
    def __init__(self, seq):
        if len(seq) == 0:
            raise Exception("Cowardly refusing to round-robin an empty list.")
        self.base = seq
        self.size = len(seq)
        self.iter = 0

    def next(self):
        result = self.base[self.iter]
        self.iter += 1
        if self.iter == self.size:
            self.iter = 0
        return result


class Tabulator:

    def __init__(self, output, titles, widths, aligns):
        self.num_cols = len(aligns)
        if not (self.num_cols == len(widths)):
            raise Exception, "Widths and aligns must have equal length."
            # And each elem of titles same as well, and same as that one.
        self.titles = titles
        self.widths = widths
        self.aligns = aligns
        self.output = output
        self.options = self.default_options()
        self.char = self.options['chars']
        self.padd = self.options['padding']

    def add_row(self, values):
        self.output.write(self.make_row(values))
        self.output.flush()

    def add_header(self):
        thin_line = self.make_hline()
        thick_line = self.make_hline(True)
        self.output.write(thin_line + self.make_titles() + thick_line)
        self.output.flush()

    def add_line(self):
        self.output.write(self.make_hline())

    def make_row(self, values):
        cells = [ali(str(val), wid) for (val, wid, ali) in
                 zip(values, self.widths, self.aligns)]
        p   = self.padd['cell'] * self.padd['pad']
        v   = self.char['v']
        vp  = v + p
        pv  = p + v
        pvp = v.join((p, p))
        return vp + pvp.join(cells) + pv + '\n'

    def make_hline(self, thick = False):
        h = self.char['h'] if not thick else self.char['ht']
        x = self.char['x']
        p = self.padd['cell']
        segments = [h * (w + 2 * p) for w in self.widths]
        return x + x.join(segments) + x + '\n'

    def make_titles(self):
        return '\n'.join([self.make_row(ts) for ts in self.titles])

    def default_options(self):
        return {'chars': dict(v = '|', h = '-', ht = '=', x = '+'),
                'padding': dict(cell = 1, table = 1, pad = ' ')}



class ProcessTable(Tabulator):

    def __init__(self, output, ranks_on_host, role_of_rank):
        from network import Role
        Tabulator.__init__(self, output,
          [('Hostname', 'Rank', 'Role')],
          (40, 12, 24), (str.ljust, str.ljust, str.ljust))
        role_list = [role for (rank, role) in role_of_rank.items()]
        workers = len([r for r in role_list if r == Role.W])
        self.add_header()
        for h in ranks_on_host.keys():
            for r in ranks_on_host[h]:
               self.add_row((h, r, Role.fullname[role_of_rank[r]]))
            self.add_line()
        self.add_row(('%d hosts' % len(ranks_on_host),
                      '%d ranks' % len(role_of_rank),
                      '1 master, %d workers' % workers))
        self.add_line()


