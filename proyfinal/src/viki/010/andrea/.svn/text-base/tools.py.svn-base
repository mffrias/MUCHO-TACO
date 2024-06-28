from subprocess import Popen, STDOUT
from signal import SIGINT, SIGTERM
from utils import read_file
from os import path, pathsep
import fileinput
import settings


class Reason:
    
    """
    These constants explain why a Tool is no longer running.
    """

    EXIT_OK = 0
    "Exited normally, after complete execution."
    KILL_OK = 1
    "Killed intentionally, as per our own request."
    EXIT_KO = 2
    "Exited abnormally, due to some error condition."
    KILL_KO = 3
    "Killed by the operating system, e.g. segfault."
    KILL_KO_POSSIBLY = 5
    "The fucking grey zone."


class Abort:

    """
    These constants represent the possible abort() situations of a Tool.
    """

    NOT_CALLED  = 0
    "abort() has not been called since launch()."
    IN_PROGRESS = 1
    "abort() has been called but not completed."
    COMPLETED   = 2
    "abort() has been called and was completed."



class ExternalToolDriver:

    """
    Base class for a Tool that drives any external program.
    """

    def __init__(self, exe_path):
        self.exe_path = exe_path
        self.process = None
        self.running = False
        self.abort_status = Abort.NOT_CALLED
        
    def launch(self, args=None, out_path=None):
        if self.running:
            raise Exception("Can't launch while already running.")
        self.running = True
        self.abort_status = Abort.NOT_CALLED
        self.out_file = open(out_path, 'w') if out_path else None
        cmd = self.make_command_line(args if args else [])
        #print "\n" + ' '.join(cmd) + "\n"
        self.process = Popen(cmd, stdout=self.out_file, stderr=self.out_file)

    def abort(self, signal=SIGINT):
        if not self.running:
            raise Exception("Can't abort when not running.")
        if not self.abort_status == Abort.IN_PROGRESS:
            self.process.send_signal(signal)
            self.abort_status = Abort.IN_PROGRESS # we never re-signal

    def aborting(self):
        if not self.running:
            raise Exception("Question makes no sense before running.")
        return self.abort_status == Abort.IN_PROGRESS

    def finished(self):
        if self.process.poll() == None: # this may have side effects!
            return False                # if True, reaps & sets retcode
        if self.out_file:
            self.out_file.close()
        if self.abort_status == Abort.IN_PROGRESS:
            self.abort_status = Abort.COMPLETED
        self.running = False
        self.returncode = self.process.returncode
        self.after_having_finished()
        return True

    def finished_via(self):
        if self.running or self.abort_status == Abort.IN_PROGRESS:
            raise Exception('Perhaps you should try exited() first.')
        # abort() was either completed or not called at all
        if self.abort_status == Abort.NOT_CALLED:
            if 0 <= self.returncode <= 128:
                # this cannot be a signal => tool voluntarily exited
                # let's find out whether it was EXIT_OK or EXIT_KO
                return self._exited_via()
            elif self.returncode < 0:
                # this can only be a signal, but we didn't send it
                return Reason.KILL_KO
            else:
                # CAN this be a signal at all? MUST it be a signal?
                # i think it's {yes, no} but am trying to confirm...
                return Reason.KILL_KO_POSSIBLY
        else:
            # means abort() was called and completed
            return Reason.KILL_OK

    def _exited_via(self):
        if self.returncode == 0:
            return Reason.EXIT_OK
        else:
            return Reason.EXIT_KO

    def make_command_line(self, args):
        return [self.exe_path].extend(args)


class JavaTool(ExternalToolDriver):
    
    """
    Base subclass for a Tool that drives a console-based Java program.

    Adds simple generic handling of usual suspects in such tools e.g.
    the Java classpath, JNI library path, entry point, JVM heap size, etc.
    """

    def __init__(self, java_home, class_path, class_name, library_path=None):
        ExternalToolDriver.__init__(self, path.join(java_home, 'bin/java'))
        self.java_home = java_home
        self.java_library_path = library_path
        self.java_class_path = class_path
        self.java_class_name = class_name

    def make_command_line(self, args=[]):
        cmd = [self.exe_path, '-cp', self.java_class_path]
        if self.java_library_path:
            cmd.append('-Djava.library.path=%s' % self.java_library_path)
        if 'jvm_heap_initial' in settings.experiment:
            cmd.append('-Xms%s' % settings.experiment['jvm_heap_initial'])
        if 'jvm_heap_maximum' in settings.experiment:
            cmd.append('-Xmx%s' % settings.experiment['jvm_heap_maximum'])
        if 'jvm_thread_stack' in settings.experiment:
            cmd.append('-Xss%s' % settings.experiment['jvm_thread_stack'])
        cmd.append(self.java_class_name)
        cmd.extend(args)
        return cmd

    def after_having_finished(self):
        self.output = read_file(self.out_path)
        self.stats  = dict()
        self.stats['task.output'] = self.output
        for line in self.output.splitlines():
            line = line.strip()
            if line.startswith('* '):
            # Parse and strip the key : value pair
                key, val = map(str.strip, line[2:].split(': ', 1))
                self.stats[key] = val


class Alloy(JavaTool):
    
    """
    Driver for the Alloy Analyzer via rfm.alloy.CLI.
    
    Compatible with Alloy 4 series and the 1.5.x CLIs.
    Tested and working with Alloy v4.1 and CLI v1.5.3.
    """

    MAGIC_SAT = 10
    MAGIC_UNSAT = 20
    MAGIC_NUMBERS = (MAGIC_SAT, MAGIC_UNSAT)
    
    RC_STR = {MAGIC_SAT: 'Alloy_CLI_DoneNormally_SAT',
      MAGIC_UNSAT: 'Alloy_CLI_DoneNormally_UNSAT',
      SIGTERM+128: 'Alloy_CLI_WasAborted'}

    
    def launch(self, als_path):
        arg_list = ['--bounds', '--disable-als-checks', als_path]
        self.out_path = als_path + '.out'
        JavaTool.launch(self, arg_list, self.out_path)

    def after_having_finished(self):
        JavaTool.after_having_finished(self)
        if 'Solving time' in self.stats:
            self.stats['solver.msecs'] = self.stats['Solving time']
        if 'Primary vars' in self.stats:
            self.stats['cnf.privars'] = self.stats['Primary vars']
        if 'Total vars' in self.stats:
            self.stats['cnf.totvars'] = self.stats['Total vars']
        if 'Clauses' in self.stats:
            self.stats['cnf.clauses'] = self.stats['Clauses']
            self.confirmed_S = self.returncode == Alloy.MAGIC_SAT
            self.confirmed_U = self.returncode == Alloy.MAGIC_UNSAT
            self.undefined = not (self.confirmed_S or self.confirmed_U)

    def abort(self):
        JavaTool.abort(self, SIGTERM)

    def _exited_via(self):
        if self.returncode in Alloy.MAGIC_NUMBERS:
            return Reason.EXIT_OK
        else:
            return Reason.EXIT_KO

    def veredict(self):
        if self.undefined:
            raise Exception('No confirmed veredict can be returned.')
        else:
            return self.returncode == Alloy.MAGIC_SAT  # XOR holds here



class Minisat220(ExternalToolDriver):

    """
    Driver for Minisat 2.2.0 (early 2010 release).
    """

    MAGIC_SAT = 10
    MAGIC_UNSAT = 20
    MAGIC_INDET = 30
    MAGIC_NUMBERS = (MAGIC_SAT, MAGIC_UNSAT, MAGIC_INDET)
    
    RC_STR = {MAGIC_SAT: 'Minisat220_DoneNormally_SAT',
      MAGIC_UNSAT: 'Minisat220_DoneNormally_UNSAT',
      MAGIC_INDET: 'Minisat220_WasAborted_INDET'}

    def launch(self, cnf_path):
        self.out_path = cnf_path + '.out'
        ExternalToolDriver.launch(self, [cnf_path], self.out_path)

    def make_command_line(self, args):
        return [self.exe_path] + args

    def after_having_finished(self):
        self.output = read_file(self.out_path)
        self.stats  = dict()
        self.stats['task.output'] = self.output
        for line in self.output.splitlines():
            line = line.strip()
            if ' : ' in line:
                # Parse and strip the key : value pair
                key, val = map(str.strip, line.split(':', 1))
                val = val.split()[0]
                if key == 'CPU time':
                    key = 'solver.msecs'
                    val = int(float(val) * 1000.0)
                elif key == 'Memory used':
                    key = 'memused.mb'
                self.stats[key] = val
            elif line.startswith('|  Number of '):
                # Parse and strip the key : value pair
                key, val = map(str.strip, line[13:-1].split(':', 1))
                if key == 'variables':
                    key = 'cnf.totvars'
                elif key == 'clauses':
                    key = 'cnf.clauses'
                self.stats[key] = val

        self.confirmed_S = self.returncode == Minisat220.MAGIC_SAT
        self.confirmed_U = self.returncode == Minisat220.MAGIC_UNSAT
        self.undefined = not (self.confirmed_S or self.confirmed_U)
        if self.confirmed_U:
            self.stats['outcome'] = 'UNSAT'
        elif self.confirmed_S:
            self.stats['outcome'] = 'SAT'
        else:
            self.stats['outcome'] = 'INDET'


    def _exited_via(self):
        if self.returncode in Minisat220.MAGIC_NUMBERS:
            return Reason.EXIT_OK
        else:
            return Reason.EXIT_KO

    def veredict(self):
        if self.undefined:
            raise Exception('No confirmed veredict can be returned.')
        else:
            return self.returncode == Minisat220.MAGIC_SAT  # XOR holds here



class HackyPipe:

    MAGIC_SAT = 10
    MAGIC_UNSAT = 20
    MAGIC_INDET = 30
    #MAGIC_BPIPE = 1
    #MAGIC_NUMBERS = (MAGIC_SAT, MAGIC_UNSAT, MAGIC_INDET, MAGIC_BPIPE)
    MAGIC_NUMBERS = (MAGIC_SAT, MAGIC_UNSAT, MAGIC_INDET)
    
    RC_STR = {MAGIC_SAT: 'HackyPipe_DoneNormally_SAT',
      MAGIC_UNSAT: 'HackyPipe_DoneNormally_UNSAT',
      MAGIC_INDET: 'HackyPipe_WasAborted_INDET',
      #MAGIC_BPIPE: 'HackyPipe_WasAborted_BPIPE',
      SIGINT+128: 'HackyPipe_WasAborted_FUNNY'}

    def __init__(self):
        self.process = None
        self.running = False
        self.abort_status = Abort.NOT_CALLED
        
    def launch(self, args=None, out_path=None):
        if self.running:
            raise Exception("Can't launch while already running.")
        self.running = True
        self.abort_status = Abort.NOT_CALLED
        self.out_path = out_path
        self.out_file = open(out_path, 'w') if out_path else None
        prog1 = '/home/jgaleotti/opt/jre/bin/java -jar /home/jgaleotti/als2cnf.jar -B -C'
        prog2 = '/home/jgaleotti/usr/bin/minisat220core'
        #prog1 = '/usr/bin/java -jar /Users/nrosner/als2cnf.jar -B -C'
        #prog2 = '/Users/nrosner/ms220core'
        pipelist = [prog1] + args + ['|', prog2]
        pipestr = ' '.join(pipelist)
        #print ' >>>> ' + pipestr # debug
        self.process = Popen(['-c', pipestr],
          shell=True, stdout=self.out_file, stderr=self.out_file)

    def abort(self, signal=SIGINT):
        if not self.running:
            raise Exception("Can't abort when not running.")
        if not self.abort_status == Abort.IN_PROGRESS:
            self.process.send_signal(signal)
            self.abort_status = Abort.IN_PROGRESS # we never re-signal

    def aborting(self):
        if not self.running:
            raise Exception("Question makes no sense before running.")
        return self.abort_status == Abort.IN_PROGRESS

    def finished(self):
        if self.process.poll() == None: # this may have side effects!
            return False                # if True, reaps & sets retcode
        if self.out_file:
            self.out_file.close()
        if self.abort_status == Abort.IN_PROGRESS:
            self.abort_status = Abort.COMPLETED
        self.running = False
        self.returncode = self.process.returncode
        self.after_having_finished()
        return True

    def finished_via(self):
        if self.running or self.abort_status == Abort.IN_PROGRESS:
            raise Exception('Perhaps you should try exited() first.')
        # abort() was either completed or not called at all
        if self.abort_status == Abort.NOT_CALLED:
            if 0 <= self.returncode <= 128:
                # this cannot be a signal => tool voluntarily exited
                # let's find out whether it was EXIT_OK or EXIT_KO
                return self._exited_via()
            elif self.returncode < 0:
                # this can only be a signal, but we didn't send it
                return Reason.KILL_KO
            else:
                # CAN this be a signal at all? MUST it be a signal?
                # i think it's {yes, no} but am trying to confirm...
                return Reason.KILL_KO_POSSIBLY
        else:
            # means abort() was called and completed
            return Reason.KILL_OK

    def after_having_finished(self):
        self.output = read_file(self.out_path)
        self.stats  = dict()
        self.stats['task.output'] = self.output
        for line in self.output.splitlines():
            line = line.strip()
            if ' : ' in line:
                # Parse and strip the key : value pair
                key, val = map(str.strip, line.split(':', 1))
                val = val.split()[0]
                if key == 'CPU time':
                    key = 'solver.msecs'
                    val = int(float(val) * 1000.0)
                elif key == 'Memory used':
                    key = 'memused.mb'
                self.stats[key] = val
            elif line.startswith('|  Number of '):
                # Parse and strip the key : value pair
                key, val = map(str.strip, line[13:-1].split(':', 1))
                if key == 'variables':
                    key = 'cnf.totvars'
                elif key == 'clauses':
                    key = 'cnf.clauses'
                self.stats[key] = val

        self.confirmed_S = self.returncode == HackyPipe.MAGIC_SAT
        self.confirmed_U = self.returncode == HackyPipe.MAGIC_UNSAT
        self.undefined = not (self.confirmed_S or self.confirmed_U)
        if self.confirmed_U:
            self.stats['outcome'] = 'UNSAT'
        elif self.confirmed_S:
            self.stats['outcome'] = 'SAT'
        else:
            self.stats['outcome'] = 'INDET'


    def _exited_via(self):
        if self.returncode in HackyPipe.MAGIC_NUMBERS:
            return Reason.EXIT_OK
        else:
            return Reason.EXIT_KO

    def veredict(self):
        if self.undefined:
            raise Exception('No confirmed veredict can be returned.')
        else:
            return self.returncode == HackyPipe.MAGIC_SAT  # XOR holds here

