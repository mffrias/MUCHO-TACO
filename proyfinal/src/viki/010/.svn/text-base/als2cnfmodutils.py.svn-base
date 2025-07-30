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
from subprocess import Popen
import re
from andrea.tools import ExternalToolDriver

def strip_restrictions(filename):
    als = ""
    for line in open(filename, 'r').readlines():
    	als += line
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
                if j == scope:
                    j = None
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
                y = scope
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

    def __init__(self, java_home, class_path):
         self.java_home = java_home
         self.java_class_path = class_path
    
    def launch(self, path_als):
        path_cnf = path_als + ".rels"
        p = Popen([self.java_home, "-jar", self.java_class_path, "-B", "-C", "-b", path_als])
        p.wait()

class Alloy2Cnf:
    
    def __init__(self, java_home, class_path):
         self.java_home = java_home
         self.java_class_path = class_path
    
    def launch(self, path_als):
        path_cnf = path_als + ".cnf"
        p = Popen([self.java_home, "-jar", self.java_class_path, "-B", "-C", path_als], stdout=open(path_cnf, "w"))
        p.wait()

class MinisatHotPipe(ExternalToolDriver):
    
    def launch(self, header, cnf, count, res, args=None, out_path=None):
        if self.running:
            raise Exception("Can't launch while already running.")
        self.running = True
        self.abort_status = Abort.NOT_CALLED
        self.out_file = open(out_path, 'w') if out_path else None
        cmd = self.make_command_line(args if args else [])
        self.process = Popen(cmd, stdin=PIPE, stderr=self.out_file)
        self.process.stdin.write(header)
        for i in range(0, count):
            self.process.stdin.write(cnf[i])
        self.process.stdin.write(res)
        self.process.stdin.close()

#THIS ONE DOES THE MAGIC!!!
#Returns a tuple = (tuple2val, mini_als, cnf, cnf_inv, rels_set)
#   tuple2val: a function that receives a relname and tuple -> tuple2val('fleft', (2, None)) fleft: N_2 -> Null
#       it returns the variable number
#   mini_als: the part of the als that contains the restricctions
#   cnf: als->cnf.
#   cnf_inv: als_inv ->cnf.
def generate_artifacts(als_path, als_inv_path, scope, rels, settings):
    java_home = settings['java_home']
    als2cnf = settings['als2cnf']
    als2rels = settings['als2rels']
    
    tool = Alloy2Cnf(java_home, als2cnf)
    print "Converting als -> cnf ..."
    tool.launch(als_path)
    cnf = als_path + ".cnf"
    print "Converting als_inv -> cnf ..."
    tool.launch(als_inv_path)
    cnf_inv = als_inv_path + ".cnf"
    tool = Alloy2Rels(java_home, als2rels)
    print "Generating rels ..."
    tool.launch(als_path)
    rels_path = als_path.replace("als", "rels")
    
    data = ""
    for line in open(als_path, "r").readlines():
        data += line
    print "Generating rels sets ..."
    rels_sets = get_rels_sets(data, rels)
    print "Stripping down restrictions ..."
    restrictions = strip_restrictions(als_path)
    print "Getting rels var limits ..."
    rels_var_limits = get_rels_var_limits(rels_path, rels)
    print "Building tuple2val function ..."
    tuple2val = get_tuple2val_function(restrictions, rels, scope, rels_var_limits, rels_sets)
    
    return (tuple2val, restrictions, file2string(cnf), file2string(cnf_inv), rels_sets)

def generate_cnf_restrictions(new_als_restrictions_file, rels_sets, tuple2val):
    if type(new_als_restrictions) == file:
        new_als_restrictions = ""
        for line in new_als_restrictions_file.readlines():
            new_als_restrictions += line
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
    return (restrictions, count)

def file2string(filename):
    data = ""
    for line in open(filename, "r").readlines():
        data += line
    return data
    
def generate_new_cnf(cnf, als_child, rels_sets, tuple2val):
    (res, clauses) = generate_cnf_restrictions(als_child, rels_sets, tuple2val)
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
    header = "p cnf " + m.group(1) + " " + str(int(m.group(2)) + clauses) + "\n"
    return (header, count, res)

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
    (tuple2val, restrictions, cnf, cnf_inv, rels_sets) = generate_artifacts(als, als_inv, scope, rels, settings)
    open("cotas-" + als, "w").write(restrictions)
    if als_child:
        print "Generating new restricctions ..."
        (header, count, res) = generate_new_cnf(cnf, open(als_child, "r"), rels_sets, tuple2val)
        filename = als_child + ".cnf"
        f = open(filename, "w")
        f.write(header)
        for i in range(0, count):
            f.write(cnf[i])
        f.write(res)
        print "The new cnf has been generated in " + filename
        if resolve:
            MinisatHotPipe("").launch(filename, header, cnf, count, res)

if __name__ == '__main__':
    main()

