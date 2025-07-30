#!/home/nrosner/usr/bin/python

"""
Traductor de andrea.tlog.csv a varios csv separados por scope de mutantes.
Correr sin parametros para ayuda de sintaxis.
"""

import sys, csv

if len(sys.argv) is not 2:
    print '\nUsage:\n    tlogsplit tlogfile\n'
    print '  where tlogfile is an input file in andrea.tlog.csv format\n'
    print 'Output files will be named "andrea.muts.NN.csv" and written to current directory.\n'
    exit(1)

tlog_path = sys.argv[1]
tlog_file = open(tlog_path)

# consumimos la 1ra linea del tlog.csv (es un comment)
dummy = tlog_file.readline()

# mapearemos cada scope relevante (como string p/preservar '00' etc)
# a una lista no vacia de listas (rows traducidas que CSV'earemos al final)
scope2rows = dict()

for row in csv.reader(tlog_file):
    # Levantamos las partes del tasklog segun formato andrea 1.3.0b7
    tid, ext, rank, outcome, exitcode, exitstr, tsolv, ttask = row    
    # Separamos el tid en terna (mutante, '-s',  scope)
    if tid[-4:-2] != '-s': raise Exception(tid + " no termina en -sXX!")
    mutante, sep, scope = tid.partition('-s')
    # Armamos una nueva fila traducida al formato que pidio Juan
    newrow = [mutante, outcome, tsolv, ttask]
    # Y la agregamos al dicc, bajo el scope correspondiente
    scope2rows[scope] = scope2rows.get(scope, []) + [newrow]

for scope in sorted(scope2rows.keys()):
    csv_path = ''.join(('andrea.muts.', scope, '.csv'))
    print 'generando .csv para scope', scope, '..'
    csv_file = open(csv_path, 'w')
    csv_writer = csv.writer(csv_file)
    for row in sorted(scope2rows[scope]):
        csv_writer.writerow(row)



