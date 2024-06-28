#!/usr/bin/env python
# encoding: utf-8
"""
als2cnfmodeutils.py

Created by Guido Marucci Blas on 2011-04-09.
Copyright (c) 2011 __MyCompanyName__. All rights reserved.
"""

import sys
import os
from signal import SIGINT, SIGTERM
from time import sleep
from subprocess import Popen, PIPE, STDOUT
import re
from andrea.tools import Minisat220, Abort
import andrea
import cStringIO
import errno

def strip_restrictions(filename):
    als = file2string(filename)
    m = re.match(r"(?si).*//fact ffields_bfields(.*)// fact int_fields.*", als)
    return m.group(1)

def get_rels_var_limits(filename, rels):
    str_rels = ""
    for rel in rels:
        str_rels += rel + "|"
    str_rels = str_rels[:-1]

    ret = {}
    for line in open(filename, 'r').readlines():
        m = re.match("(?si)\[\s*(\d*)\s+..\s+(\d+)\s*\][^Q]*QF\.(" + str_rels + ")", line)
        if m:
            ret[m.group(3)] = (int(m.group(1)), int(m.group(2)))
            
    return ret
    
def get_rels_sets(string, rels):
    result = {}
    for rel in rels:
        result[rel] = parseQF(string, rel)
    return result
    
def get_colapsed_vals_map(scope, rels_sets):
    result = {}
    for rel in rels_sets.keys():
        offset = 0
        result[rel] = {}
        for i in range(0, scope):
            for j in range(0, scope + 1):
                if j == 0:
                    j = None
                else:
                    j -= 1
                if (i,j) not in (rels_sets[rel]):
                    offset += 1
                result[rel][(i,j)] = offset
    return result
                    
def get_tuple2val_function(string, rels, scope, rels_var_limits, rels_set=None):
    if not rels_set:
        rels_set = get_rels_sets(string, rels)
    colapsed_vals_map = get_colapsed_vals_map(scope, rels_set)

    def tuple2val(rel, t):
        result = None
        if rel in rels and t in rels_set[rel]:
            x, y = t
            if y == None:
                y = 0
            else:
                y += 1
            offset = colapsed_vals_map[rel][t]
            floor, ceiling = rels_var_limits[rel]
            result = floor + (scope+1)*x + y - offset
            assert result >= floor and result <= ceiling, ('error illegal tuple ' + str(t) + '->' + str(result))
        return result
    
    return tuple2val
            
def get_cnf_data(als_path, als_inv_path):
    Alloy2Cnf()
    return 0
                    
def regexQF(relname=None):
    """
    Devolver una expresion regular que matchea las expresiones
    Alloy de la pinta "QF.xxx_0 in tupla + tupla + ... + tupla".
    """
    if relname is None:
        relname = r"(\w+)"
    return r"QF\." + relname + r"_0\s+in\s+" + \
        r"(N\d+\s*->\s*\w+)" + r"(?:\s*\+\s*(N\d+\s*->\s*\w+))*\s*[^N]"

def parseQF(string, relname=None):
    """
    Dado el texto de una spec y el nombre de una rel, parsear
    "QF.relname_0 in ..." y devolver una lista de pares int, int/None
    asi como los offsets inicial y final del match en el texto.    
    """
    pattern = re.compile(regexQF(relname))
    hit = pattern.search(string)
    message = 'error: could not find rel "' + relname + '" in base spec.'
    if not hit:
        print message
        assert hit 
    pos, end = hit.start(), hit.end()
    pattern = re.compile(r"(N\w+\s*->\s*\w+)")
    result = set()
    pairs = [l.split('->') for l in pattern.findall(string[pos:end])]
    pairs = [result.add((int(x[1:]), (int(y[1:])) if y.startswith('N') else None)) \
        for x, y in pairs]
    return result

class Alloy2Rels:

    def __init__(self, java_home, class_path, jvm_heap_initial=None, jvm_heap_maximum=None, jvm_thread_stack=None):
         self.java_home = java_home
         self.java_class_path = class_path
         self.cmd = [java_home]
         if jvm_heap_initial:
             self.cmd.append('-Xms' + jvm_heap_initial)
         if jvm_heap_maximum:
             self.cmd.append('-Xmx' + jvm_heap_maximum)
         if jvm_thread_stack:
             self.cmd.append('-Xss' + jvm_thread_stack)
    
    def launch(self, path_als):
        path_rels = path_als + ".rels"
        cmd = list(self.cmd)
        cmd.append("-jar")
        cmd.append(self.java_class_path)
        cmd.append("-B")
        cmd.append("-C")
        cmd.append("-b")
        cmd.append(path_als)
        p = Popen(cmd, stdout=open(path_rels + ".out", "w"), stderr=open(path_rels + ".err", "w"))
        p.wait()

class Alloy2Cnf:
    
    def __init__(self, java_home, class_path, jvm_heap_initial=None, jvm_heap_maximum=None, jvm_thread_stack=None):
         self.java_home = java_home
         self.java_class_path = class_path
         self.cmd = [java_home]
         if jvm_heap_initial:
             self.cmd.append('-Xms' + jvm_heap_initial)
         if jvm_heap_maximum:
             self.cmd.append('-Xmx' + jvm_heap_maximum)
         if jvm_thread_stack:
             self.cmd.append('-Xss' + jvm_thread_stack)
    
    def launch(self, path_als):
        path_cnf = path_als + ".cnf"
        cmd = list(self.cmd)
        cmd.append("-jar")
        cmd.append(self.java_class_path)
        cmd.append("-B")
        cmd.append("-C")
        cmd.append(path_als)
        p = Popen(cmd, stdout=open(path_cnf, "w"), stderr=open(path_cnf + ".log", "w"))
        p.wait()

class MinisatHotPipe(Minisat220):

    def launch(self, cnf_path, header=None, cnf=None, res=None, flush2disk=False):
        if self.running:
            raise Exception("Can't launch while already running.")
        self.running = True
        self.abort_status = Abort.NOT_CALLED
        self.out_path = cnf_path + '.out'
        self.err_path = cnf_path + '.err'
        self.out_file = open(self.out_path, 'w')
        self.err_file = open(self.err_path, 'w')
        stdin_path = PIPE
	try:
            if flush2disk:
                stdin_path = open(cnf_path, 'r')
            self.process = Popen([self.exe_path], stdin=stdin_path, stdout=self.out_file, stderr=self.err_file, bufsize=32 * 1024)
            if not flush2disk:
                self.process.stdin.write(header)
                self.process.stdin.write(res)
                self.process.stdin.write(cnf)
                self.process.stdin.close()
	except IOError, e:
	    if e.errno == errno.EPIPE:
	        dump_path = self.out_path + ".dump.cnf"
                print "Warning: broken pipe ignored @ " + self.out_path
                dump = open(dump_path, 'w')
                dump.write(header)
                dump.flush()
                dump.write(res)
                dump.flush()
                dump.write(cnf)
                dump.close()
                print "EPIPE_DEBUG: Dumped CNF to " + dump_path
            else:
                print "Error: IOError: Something happened and it was not a broken pipe..."
                assert False, "This should not happen normally"

#THIS ONE DOES THE MAGIC!!!
#Returns a tuple = (tuple2val, mini_als, cnf, cnf_inv, rels_set)
#   tuple2val: a function that receives a relname and tuple -> tuple2val('fleft', (2, None)) fleft: N_2 -> Null
#       it returns the variable number
#   mini_als: the part of the als that contains the restricctions
#   cnf: als->cnf.
#   cnf_inv: als_inv ->cnf.
def generate_artifacts(als_path, als_inv_path, scope, rels, settings, verbose=False, cnf_path=None, cnf_inv_path=None, rels_arg_path=None, rels_arg_inv_path=None):
    java_home = settings.paths['java_home']
    als2cnf = settings.paths['als2cnf']
    als2rels = settings.paths['als2rels']
   
    tool = Alloy2Cnf(java_home, als2cnf, jvm_heap_initial=settings.experiment['jvm_heap_initial'], jvm_heap_maximum=settings.experiment['jvm_heap_maximum'], jvm_thread_stack=settings.experiment['jvm_thread_stack'])
    
    if not cnf_path:
        if verbose: 
            print "Converting als -> cnf ..."
    
            tool.launch(als_path)
            cnf = als_path + ".cnf"
    else:
        cnf = cnf_path
    
    if not cnf_inv_path:
        if verbose:
            print "Converting als_inv -> cnf ..."
    
        tool.launch(als_inv_path)
        cnf_inv = als_inv_path + ".cnf"
    else:
        cnf_inv = cnf_inv_path
        
    tool = Alloy2Rels(java_home, als2rels, jvm_heap_initial=settings.experiment['jvm_heap_initial'], jvm_heap_maximum=settings.experiment['jvm_heap_maximum'], jvm_thread_stack=settings.experiment['jvm_thread_stack'])
    
    if not rels_arg_path:
        if verbose:
            print "Generating rels ..."
        tool.launch(als_path)
        rels_path = als_path.replace(".als", ".rels")
    else:
        rels_path = rels_arg_path
    
    if not rels_arg_inv_path:
        if verbose:
            print "Generating rels inv ..."
        tool.launch(als_inv_path)
        rels_inv_path = als_inv_path.replace(".inv", ".inv.rels")
    else:
        rels_inv_path = rels_arg_inv_path

    if verbose:
        print "Generating rels sets ..."
    
    rels_sets = get_rels_sets(file2string(als_path), rels)
    rels_inv_sets = get_rels_sets(file2string(als_inv_path), rels)
    
    if verbose:
        print "Stripping down restrictions ..."
    
    restrictions = strip_restrictions(als_path)
    
    if verbose:
        print "Getting rels var limits ..."
    
    rels_var_limits = get_rels_var_limits(rels_path, rels)
    rels_inv_var_limits = get_rels_var_limits(rels_inv_path, rels)
    
    if verbose:
        print "Building tuple2val function ..."

    tuple2val = get_tuple2val_function(restrictions, rels, scope, rels_var_limits, rels_sets)
    inv_tuple2val = get_tuple2val_function(restrictions, rels, scope, rels_inv_var_limits, rels_inv_sets)

    if verbose:
        print "Done"
    
    return (tuple2val, restrictions, file2string(cnf), file2string(cnf_inv), rels_sets, inv_tuple2val, rels_inv_sets, file2string(rels_path), file2string(rels_inv_path))

def generate_cnf_restrictions(new_als_restrictions_file, rels_sets, tuple2val, cur_max):
    if type(new_als_restrictions_file) == file:
        new_als_restrictions = file2string(new_als_restrictions_file)
    else:
        new_als_restrictions = new_als_restrictions_file
    new_rels_sets = get_rels_sets(new_als_restrictions, rels_sets.keys());
    
    restrictions = ""
    count = 0
    for rel in rels_sets.keys():
        tuples = rels_sets[rel];
        for t in tuples:
            if t not in new_rels_sets[rel]:
                count += 1
                restrictions += "-" + str(tuple2val(rel, t)) + " 0\n"
            elif t[0] < cur_max:
                count += 1
                restrictions += str(tuple2val(rel,t)) + " 0\n"
    return (restrictions, count)

def file2string(filename):
    if type(filename) == file:
        f = filename
    else: 
        f = open(filename, "r")
        
    data = ""
    for line in f.readlines():
        data += line
    return data
    
def separete_cnf_from_header(cnf):
     header = ""
     count = len(cnf)
     for i in range(count-1, -1, -1):
         c = cnf[i]
         header += c
         count -= 1
         if c == 'p':
             break
     header = header[::-1].strip()
     m = re.match(r"p cnf (\d+) (\d+)", header)
     return (cnf.split(header)[0], m.group(1), m.group(2))   

def separate_cnf_from_header(cnf):
    """
    Recibe string monstruo en formato dimacs
    Devuelve terna (newcnf, strnvars, strnclauses)
      donde newcnf es cnf sin la p-line,
      y ambas cants se devuelven *como strings* (!)
    """
    e = r"p cnf (\d+) (\d+)"
    m = re.search(e, cnf)
    assert m, 'no p-line in cnf body!?'
    varstr, clastr = m.group(1), m.group(2)
    s = re.split(e, cnf, maxsplit=1)
    return s[0] + s[3], varstr, clastr


def generate_new_cnf(cnf, als_child, rels_sets, tuple2val, cur_max, vals, old_clauses):
    (res, clauses) = generate_cnf_restrictions(als_child, rels_sets, tuple2val, cur_max)
    header = "p cnf " + str(vals) + " " + str(int(old_clauses) + int(clauses)) + "\n"
    return (header, cnf, res)

def main():
    settings = {}
    settings['java_home'] = 'java'
    settings['als2cnf'] = 'als2cnf.jar'
    settings['als2rels'] = 'als2rels.jar'
    als = sys.argv[1]
    als_inv = sys.argv[2]
    scope = int(sys.argv[3])
    rels = []
    als_child = None
    resolve = False
    if (sys.argv[4] == "append" or sys.argv[4] == "append-resolve"):
        als_child = sys.argv[5]
        rels = sys.argv[6:]
        resolve = sys.argv[4] == "append-resolve"
    else:
        rels = sys.argv[4:]
        
    print "ALS: " + als
    print "INV: " + als_inv
    print "SCOPE: " + str(scope)
    print "RELS: " + str(rels)
    (tuple2val, restrictions, cnf, cnf_inv, rels_sets, inv_tuple2val, rels_inv_sets) = generate_artifacts(als, als_inv, scope, rels, settings)
    open("cotas-" + als, "w").write(restrictions)
    if als_child:
        print "Generating new restrictions ..."
        (header, count, res) = generate_new_cnf(cnf, open(als_child, "r"), rels_sets, tuple2val)
        filename = als_child + ".cnf"
        f = open(filename, "w")
        f.write(header)
        for i in range(0, count):
            f.write(cnf[i])
        f.write(res)
        print "The new cnf has been generated in " + filename
        if resolve:
            MinisatHotPipe("").launch(header, cnf, count, res, filename)

if __name__ == '__main__':
    main()

