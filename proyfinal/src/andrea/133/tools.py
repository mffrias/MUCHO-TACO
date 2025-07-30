from subprocess import Popen, STDOUT
from signal import SIGINT, SIGTERM
from utils import read_file
from os import path, pathsep
import fileinput
import settings


class Reason:
    
    """
    Constants explaining why a Tool is no longer running.
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
    Constants representing possible abort() situations of a Tool.
    """

    NOT_CALLED  = 0
    "abort() has not been called since launch()."
    IN_PROGRESS = 1
    "abort() has been called but not completed."
    COMPLETED   = 2
    "abort() has been called and was completed."



class ExternalToolDriver:

    """
    Base class for Tools that drive an external program.
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
    Base subclass for Tools that drive a console-based Java program.

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
    v2009.07.x (via rfm.jforge.CLI v0.4.x)
    """

    MAGIC_SAT = 10
    MAGIC_UNSAT = 20
    MAGIC_NUMBERS = (MAGIC_SAT, MAGIC_UNSAT)
    
    RC_STR = {MAGIC_SAT: 'Alloy_CLI_DoneNormally_SAT',
      MAGIC_UNSAT: 'Alloy_CLI_DoneNormally_UNSAT',
      SIGTERM+128: 'Alloy_CLI_WasAborted'}

    
    def launch(self, als_path):
        arg_list = ['--bounds', als_path]
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


class JForge(JavaTool):
    
    """
    Driver for the JForge tool via rfm.jforge.CLI.
    
    Compatible with JForge 2009 and the 0.4 CLIs.
    Being tested with JForge v2009.07.29 and CLI v0.4.3.
    """
    
    RC_OK, RC_PARSING_ERR, RC_CMNOTFOUND_ERR, RC_IO_ERR = 0, 1, 2, 3
    RC_USAGE, RC_VERSION = 10, 11

    MAGIC_NUMBERS = (RC_OK, RC_PARSING_ERR, RC_CMNOTFOUND_ERR, RC_IO_ERR,
                     RC_USAGE, RC_VERSION)

    RC_STR = {RC_OK: 'JForge_CLI_DoneNormally',
      RC_PARSING_ERR: 'JForge_CLI_ParseException',
      RC_CMNOTFOUND_ERR: 'JForge_CLI_ClassOrMethodNotFound',
      RC_IO_ERR: 'JForge_CLI_IOException',
      RC_USAGE: 'JForge_CLI_DoneShowingUsage',
      RC_VERSION: 'JForge_CLI_DoneShowingVersion',
      128+SIGTERM: 'JForge_CLI_WasAborted'}

    def launch(self, jf_path):
        arg_list = read_file(jf_path).split()
	# Hack! Agregamos el cp_forge (i.e. forge.jar) al -p interno
	# Esto es necesario por las clases edu.mit.sdg.csail.annotation.*
        pos = arg_list.index('-p') + 1
	arg_list[pos] += pathsep + settings.jforge['cp_forge']
        self.out_path = jf_path + '.out'
        JavaTool.launch(self, arg_list, self.out_path)

    def after_having_finished(self):
        self.output = read_file(self.out_path)
        self.stats  = dict()
	self.stats['task.output'] = self.output

	# Parse '*'-lines from the output into a dictionary
        
	for line in self.output.splitlines():
	    line = line.strip()
            if line.startswith('* '):

	        # Parse and strip the key : value pair
                key, val = map(str.strip, line[2:].split(': ', 1))

                # Beware of multiple keys! We'll use 3 cases:

		if not(key in self.stats):
		    # First time we see this key. Just store it.
		    self.stats[key] = val
		else:
		    # OK this is a repeated key.
		    mkey = '.'.join((key, 'multi'))
		    if not(mkey in self.stats):
		        # First repetition. Make the list.
			self.stats[mkey] = [self.stats[key], val]
		    else:
		        # wow, 3rd appearance or more.
			# Just append to existing list.
			self.stats[mkey] += [val]

	done_ok = self.returncode == JForge.RC_OK

	# Ensure at most 1 mode is in use (known limitation of driver)
	# (we don't really need to mix both right now)
	mode = None
	if 'compliant.outcome' in self.stats:
	    if 'consistent.outcome' in self.stats:
	        if done_ok:
	            raise Exception("UNSUPPORTED: Cons AND Comp!")
	    else:
	        mode = 'compliant.outcome'
	else:
	    if not('consistent.outcome' in self.stats):
	        if done_ok:
		    raise Exception("UNSUPPORTED: Neither Cons nor Comp!")
            else:
	        mode = 'consistent.outcome'

        for k,v in self.stats.iteritems():
	    if k.endswith('.multi'):
	        k1 = k[:-6]
		if k1 == mode:
		    if 'SAT' in v:
		        self.stats[k1] = 'SAT'
		elif k1.endswith('.msecs'):
		    self.stats[k1] = str(sum(map(int, v)))
		elif k1.endswith('.privars'):
		    self.stats[k1] = str(sum(map(int, v)))
		elif k1.endswith('.totvars'):
		    self.stats[k1] = str(sum(map(int, v)))
		elif k1.endswith('.clauses'):
		    self.stats[k1] = str(sum(map(int, v)))
		elif k1.endswith('.bytes'):
		    self.stats[k1] = str(sum(map(int, v)))

        if not('solver.msecs' in self.stats):
	    if done_ok or 'solver.msecs.multi' in self.stats:
	        raise Exception('This should never happen!!')
	    else:
	        self.stats['solver.msecs'] = '0'

        self.confirmed_S = done_ok and self.stats[mode] == 'SAT'
        self.confirmed_U = done_ok and self.stats[mode] == 'UNSAT'
        self.undefined = not (self.confirmed_S or self.confirmed_U)
        self.inconsistent = self.confirmed_S and self.confirmed_U

	if self.inconsistent:
            raise Exception('Both SAT and UNSAT? Congrats, nice bug.')

    def veredict(self):
        if self.undefined:
            raise Exception('No confirmed veredict can be returned.')
        else:
            return self.confirmed_S # since S XOR U must hold by now

    def abort(self):
        JavaTool.abort(self, SIGTERM)

    def _exited_via(self):
        if self.returncode == JForge.RC_OK:
            return Reason.EXIT_OK
        else:
            return Reason.EXIT_KO



"""

settings.read('testjf.conf')

def make_tool(tool, sett):
    java_home = settings.paths['java_home']
    cp, cn, lp = [sett[k] for k in
    'class_path', 'class_name', 'shlib_path']
    return tool(java_home, cp, cn, lp)

alloy = make_tool(Alloy, settings.alloy)
jforge = make_tool(JForge, settings.jforge)
tools = dict({'als': alloy, 'jf': jforge})

jforge.launch('try.jf')

from time import sleep
from sys import stdout

stdout.write('Waiting for tool to finish ...')

while not jforge.finished():
    stdout.write('.')
    stdout.flush()
    sleep(0.5)

print "\nFinished!"
print '\n', 'ver:', jforge.veredict()

"""
