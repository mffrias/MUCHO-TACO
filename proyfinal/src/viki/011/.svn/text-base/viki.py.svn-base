#!/usr/bin/env python

import andrea.settings
import andrea.network
import sys, os, getopt, time

from andrea.andrea   import *
from andrea.utils    import ensure_directory
from andrea.utils    import secs2human_older
from andrea.worker   import Worker
from andrea.network  import Role
from time            import sleep
from shutil          import copyfile

from master          import AlsPartitionerMaster
from worker          import InfiniteTimeoutWorker
import settings

def main():

    andrea.network.map = andrea.network.ProcessMap()

    config_path = parse_cmd_line()
    config_path = os.path.abspath(config_path)
    andrea.settings.read(config_path)
    settings.trola_output_dir = os.path.join(andrea.settings.local_store(), andrea.settings.experiment['full_id'], "trola")

    andrea.network.sync_zero_time()
    sleep(andrea.network.map.my_rank * 0.05)

    create_output_file(config_path, show_welcome_banner, config_path, VIKI_LOGO)

    role2class = dict({Role.M: AlsPartitionerMaster, Role.W: InfiniteTimeoutWorker})

    my_class = role2class[andrea.network.map.my_role]
    me = my_class()
    me.start()
    me.cleanup()

    if andrea.network.map.am_master():
        print '\n', 'viki', VIKI_VERSION, \
          'closing after', secs2human_older(andrea.network.time())

def parse_cmd_line():

    """
    Punto de entrada.
    """
    if len(sys.argv) < 1:
        if andrea.network.map.am_master():
            show_usage()
        sys.exit(1)

    modes = ((('-h', '--help'), show_usage),
             (('-v', '--version'), show_version),
             (('-p', '--process-map'), show_process_map))

    for switch, function in modes:
        if sys.argv[1].startswith(switch):
            if andrea.network.map.am_master():
                if function():
                    sys.exit(0)
   
    opts, argv = getopt.getopt(sys.argv[1:],
         'm:M:r:c:satf',
        ['max=', 'scope=', 'rel=', 'conf=', 'stats=', 'aliasing=', 'astimeout=', 'flush2disk='])
        
    nrels = 0
    
    for opt, val in opts:
        if opt in ('-r', '--rel'):
            settings.rels[nrels] = val
            nrels += 1
        elif opt in ('-m', '--max'):
            settings.max = int(val)
        elif opt in ('-a', '--aliasing'):
            settings.aliasing = True
        elif opt in ('-M', '--scope'):
            if int(val) == 0:
                raise IOError("Scope can not be zero")
            settings.scope = int(val)
        elif opt in ('-c', '--conf'):
            conf_path = val
        elif opt in ('-s', '--stats'):
            settings.statistics = True
        elif opt in ('-t', '--astimeout'):
            settings.autosensing_timeout = True
        elif opt in ('-f', '--flush2disk'):
            settings.flush2disk = True

    if settings.max > settings.scope:
        raise IOError("Scope can not be smaller than max")
        
    if not conf_path:
        raise IOError("-c parameter mandatory!\n")
    if not os.path.isfile(conf_path):
        if andrea.network.map.am_master():
            raise IOError("Couldn't open " + conf_path + '\n')
            sys.exit(2)
    else:
        return conf_path

def show_process_map():
    print ''
    andrea.network.map.write_table(sys.stdout)
    print ''
    return True

def show_usage():
    print '\nPlease specify a configuration file, or\n'
    print '   -v, --version    for version information'
    print '   -h, --help       if you need some help'
    print '   -m, --map        to see the process map'
    print ''
    return True

def show_version():
    print VIKI_LOGO
    return True

VIKI_VERSION = '0.1.2_sab (sin bug cnf + sin artifact overdose + mod timeout + sin leak + sin bug header + con units _antes_ de cnf + con trola reachplanch)'

VIKI_LOGO = """

__      _______ _  _______ 
\ \    / /_   _| |/ /_   _|
 \ \  / /  | | | ' /  | |  
  \ \/ /   | | |  <   | |  
   \  /   _| |_| . \ _| |_ 
    \/   |_____|_|\_\_____|  vVERSION


""".replace('VERSION', VIKI_VERSION)


if __name__ == '__main__':
    main()
