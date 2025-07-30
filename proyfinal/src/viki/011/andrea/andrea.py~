#!/usr/bin/env python

import settings
import network
import sys, os

from utils    import ensure_directory
from utils    import secs2human_older
from master   import Master
from worker   import Worker
from network  import Role
from time     import sleep
from shutil   import copyfile
from datetime import datetime


def main():

    network.map = network.ProcessMap()

    config_path = parse_cmd_line()
    config_path = os.path.abspath(config_path)
    settings.read(config_path)

    network.sync_zero_time()
    sleep(network.map.my_rank * 0.01)

    create_output_file(config_path, show_welcome_banner, config_path, ANDREA_LOGO)

    role2class = dict({Role.M: Master, Role.W: Worker})

    my_class = role2class[network.map.my_role]
    me = my_class()
    me.start()
    me.cleanup()

    if network.map.am_master():
        print '\n', 'andrea', ANDREA_VERSION, \
          'closing bolich after', secs2human_older(network.time())
    
def show_welcome_banner(config_path, app_logo):
    # Show a welcome message
    takestr = '(take %s of %s) on %d CPUs' % \
      (settings.experiment['take'], settings.experiment['id'],
       network.map.comm_size)
    print 'launching', settings.experiment['full_id'], takestr
    print app_logo
    print '      date:   ', datetime.now().isoformat()
    print '  hardware:   ', settings.experiment.get('hardware', 'unspecified')
    print '      goal:   ', settings.experiment.get('goal', 'unspecified')
    print '  comments:   ', settings.experiment.get('comments', 'none')
    print '\n'
    print ' conf_file:   ', config_path
    print ' tasks_dir:   ', os.path.abspath(settings.experiment['tasks'])
    print 'output_dir:   ', settings.outdir_path()
    print '   conflog:   ', settings.outdir_path('andrea.conf')
    print '   tasklog:   ', settings.outdir_path('andrea.tlog.csv')
    print '\n'
    
def create_output_file(config_path, on_success, *args):
    had_to_create = False;
    if network.map.am_master():
        had_to_create = ensure_directory(settings.outdir_path())
        if had_to_create:
            # Write process map file to the results dir
            mapfile = open(settings.outdir_path('andrea.pmap'), 'w')
            network.map.write_table(mapfile)
            mapfile.close()
            # Store a copy of the .conf file in the results dir
            # (unless the given one is there already!)
            if config_path != settings.outdir_path('andrea.conf'):
                copyfile(config_path, settings.outdir_path('andrea.conf'))
        	on_success(*args)
        else:
            print '\nRefusing to clobber existing outdir (for safety).\n'
            print 'Please do any of the following:'
            print '  a) rename or remove previous output directory,'
            print '    ', settings.outdir_path()
            print '  b) change expID and/or increment takeID in your config file,'
            print '    ', config_path
            print '  c) or add "allow_clobbering: Yes" to your config file.'
            print ''
            exit(2) # revisar esto	
    
def parse_cmd_line():

    if len(sys.argv) != 2:
        if network.map.am_master():
            show_usage()
        sys.exit(1)

    modes = ((('-h', '--h'), show_help),
             (('-v', '--v'), show_version),
             (('-m', '--m'), show_process_map))

    for switch, function in modes:
        if sys.argv[1].startswith(switch):
            if network.map.am_master():
                function()
            sys.exit(0)

    conf_path = sys.argv[1]
    if not os.path.isfile(conf_path):
        if network.map.am_master():
            sys.stderr.write("Couldn't open " + conf_path + '\n')
        sys.exit(2)
    else:
        return conf_path


def show_process_map():
    print ''
    network.map.write_table(sys.stdout)
    print ''

def show_usage():
    print '\nPlease specify a configuration file, or\n'
    print '   -v, --version    for version information'
    print '   -h, --help       if you need some help'
    print '   -m, --map        to see the process map'
    print ''

def show_help():
    print '\nusage:\n\n    ', 'mpiexec -np NUM_CORES python andrea.py CONF_FILE\n'

def show_version():
    print ANDREA_LOGO


ANDREA_VERSION = '1.4.1b6 (lo-fat, hi-doc)'

ANDREA_LOGO = """
                  _
                 | |
   __ _ _ __   __| |_ __ ___  __ _
  / _` | '_ \ / _` | '__/ _ \/ _` |
 | (_| | | | | (_| | | |  __/ (_| |
  \__,_|_| |_|\__,_|_|  \___|\__,_|  vVERSION


""".replace('VERSION', ANDREA_VERSION)


if __name__ == '__main__':
    main()

