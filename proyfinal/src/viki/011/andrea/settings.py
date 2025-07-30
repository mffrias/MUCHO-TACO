import ConfigParser
from re import compile as compile_regex
from os import path, pathsep


experiment  = dict()
logging     = dict()
paths       = dict()
alloy       = dict()


def read(conf_path):

    """
    Parse andrea configuration from a .conf text file.
    
    Uses several sections and stores conf settings into global dicts
    under the section name, e.g. [experiment] -> an 'experiment' dict.
    This should be much more flexible and w/better error checking...
    """

    conf = ConfigParser.ConfigParser()
    conf_path = path.abspath(conf_path) # normalize/absolutize this path
    conf.read(conf_path) # and parse the .conf file

    global experiment, queues, logging, paths, alloy
    experiment   = dict(conf.items('experiment'))
    logging      = dict(conf.items('logging'))
    paths        = dict(conf.items('paths'))
    alloy        = dict(conf.items('alloy'))

    experiment['take_id'] = 'take' + experiment['take']
    experiment['full_id'] = experiment['id'] + '.' + experiment['take_id']

    # pathname to output dir (ensured and only used by master)
    experiment['outdir'] = path.join(path.dirname(conf_path), experiment['full_id'] + '.output')
    
    # regexp for stdout (human) event logging filtering
    logging['filter_stdout'] = compile_regex(logging['events_stdout'])



def outdir_path(filename=None):
    global experiment
    if filename is None:
        return path.abspath(experiment['outdir'])
    else:
        return path.abspath(path.join(experiment['outdir'], filename))


def local_store():
    """
    Return path to the base directory for local storage.
    
    This includes the current experiment ID's dir, as well as
    a take subsubdir if one was given. This does NOT include
    a subsubsubdir specific to any worker.
    """
    global paths
    return paths['local_storage']


def local_store_dir(rank):
    """
    Return path to the work subsub(sub)directory for the
    given rank number within local storage.
    """
    global experiment
    directory = path.join(local_store(), experiment['full_id'])
    subdir = 'worker_%d' % rank if rank > 0 else 'master'
    return path.join(directory, subdir)

