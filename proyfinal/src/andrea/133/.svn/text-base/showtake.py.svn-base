#! /usr/bin/env python
#
#  Dado un output dir, muestra algunas stats para humanos
#  provenientes del .conf y .tlog.csv.
#

import sys
import csv
import os

if len(sys.argv) is not 2:
	print 'usage: python showtake.py name_of_take_outputdir'
	print 'e.g.:  python showtake.py AList.take1.output'
	exit(1)


#task_id,task_type,worker_rank,outcome,rc_num,rc_str,tot_msec_solv,tot_msec_task

takedir = sys.argv[1]
conf_path = os.path.join(takedir, 'andrea.conf')
csv_path = os.path.join(takedir, 'andrea.tlog.csv')

print conf_path
os.system('grep -m 1 tasks ' + conf_path)
print '# of .als files in taskdir:'
os.system('grep -m 1 tasks ' + conf_path + ' | cut -c 15- | xargs ls | grep "als$" | wc -w')
os.system('grep -m 1 timeout ' + conf_path)

print csv_path

lecter = csv.reader(open(csv_path))

num_of    = { 'UNSAT': 0, 'SAT': 0, 'TIMEOUT': 0, 'ERROR': 0, 'OTHER': 0 }
msec_solv = { 'UNSAT': 0, 'SAT': 0, 'TIMEOUT': 0, 'ERROR': 0, 'OTHER': 0 }
msec_task = { 'UNSAT': 0, 'SAT': 0, 'TIMEOUT': 0, 'ERROR': 0, 'OTHER': 0 }

header_consumed = False

for row in lecter:
	if header_consumed:
		outcome = row[3]
		if outcome in ('UNSAT', 'SAT', 'TIMEOUT'):
			num_of[outcome] += 1
			msec_solv[outcome] += int(row[6])
			msec_task[outcome] += int(row[7])
		elif outcome == 'ERROR':
			num_of[outcome] += 1
		else:
			num_of['OTHER'] += 1
	else:
		header_consumed = True
		assert row[0] == '#task_id'


min_ok = ((msec_solv['UNSAT'] + msec_solv['SAT']) / 60000.0)
min_to = (msec_solv['TIMEOUT'] / 60000.0)

print '%10.2f min solving SAT/UNSAT tasks' % min_ok
print '%10.2f min solving TIMEOUT tasks' % min_to

min_tst = ((msec_solv['UNSAT'] + msec_solv['SAT'] + msec_solv['TIMEOUT']) / 60000.0)
min_ttt = ((msec_task['UNSAT'] + msec_task['SAT'] + msec_task['TIMEOUT']) / 60000.0)

print '%10.2f min total solver time' % min_tst
print '%10.2f min total task time' % min_ttt
print '%10.2f min overhead' % (min_ttt - min_tst)


t = 0
for k,v in num_of.iteritems():
	if v > 0:
		t += v
		print '%10d %s tasks' % (v, k)

print '%10d %s tasks' % (t, 'TOTAL')
