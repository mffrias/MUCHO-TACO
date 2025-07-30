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
          (12, 12, 24), (str.ljust, str.ljust, str.ljust))
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

