#!/usr/bin/env python
# encoding: utf-8

"""
AlsPartitionerMaster.py

Created by Guido Marucci Blas on 2011-01-29.
Copyright (c) 2011 __MyCompanyName__. All rights reserved.
"""
from andrea.master          import Master
from events                 import PartitionEvent, Event
from trola.trola            import partition
from andrea.utils           import list_all_files, read_file
from andrea.network         import HaveMission
from andrea.events          import WeatherEvent
from time                   import sleep

import random
import math
import andrea.network
import andrea.settings
import settings
import sys
import os
from extended_queue         import ExtendedQueue
import time
import threading

MAX_TASKS_DIFF = 10

class AlsPartitionerMaster(Master):
    
    def __init__(self):
        Master.__init__(self)
        self.partition_tasks = ExtendedQueue()
        self.run = True
        self.partitioning = False
        self.total_produced = 0
        self.total_processed = 0
        self.start_time = andrea.network.time()
        self.sp_relation = 0.95 #BE WARNED WHEN CHANGING THIS
        self.workers = len(andrea.network.map.ranks()) - 1
        self.beta = 12
        self.lower = 0
        self.upper = 0
        self.seq_finished = False
        self.par_finished = False
        self.main_task_tid = ''
        self.finished_amm = 0
        self.total_st = 0.0
        random.seed()
        
    def cleanup(self):
        self.run = False
        self.partitioner_thread.join()
        Master.cleanup(self)
    
    def partitioner(self):
        result = 1
        try:
            secs = 1.1
            while self.run:
                if self.partition_tasks:
                    #print "Starting a partition work..."
                    self.partitioning = True
                    result = self.partitionate()
                    self.partitioning= False
                    if result == -1:
                        secs = secs * 1.1
                        #print "Voy a dormir " + str(secs) + " segundos"
                        time.sleep(secs)
                    elif result == 0:
                        time.sleep(0.5)
                    else:
                        secs = 1.1
                    #print "The partition was made."
                else:
                    time.sleep(1)
        except Exception as e:
            print e

    def start(self):
        print "Launching thread init"
        self.partitioner_thread = threading.Thread(target=self.partitioner, name='partitioner')
        self.partitioner_thread.start()
        Master.start(self)
        
    def main_loop(self):
        auxQueue = ExtendedQueue()
        while self.tasks_idle:
            auxQueue.append(self.tasks_idle.pop(0))
        self.tasks_idle = auxQueue
        
        self.total_produced = len(self.tasks_idle)    

        while not self.finished:

            if andrea.network.msg_waiting():
                self.handle_message(andrea.network.receive())
                            
            if self.workers_idle and self.tasks_idle:
                worker, task = self.assign_mission()
#                tid, ttype, tdata, infinite_timeout, curMax, level, new_timeout = task
#                print curMax
#                print level
                andrea.network.send(HaveMission(worker, task))

            if not (self.tasks_idle or self.workers_busy or self.partition_tasks or self.partitioning):
                self.finished = True

            if self.weather_reports:
                current_time = andrea.network.time()
                if current_time - self.last_weather > self.weather_every:
                    self.last_weather = current_time
                    self.bb.add(WeatherEvent('update', self.get_stats()))
            
            sleep(0.002)
        
        while andrea.network.msg_waiting():
            andrea.network.receive()
        
        if self.seq_finished:
            print "Se termino de procesar la tarea en secuencial antes que en paralelo"
        elif self.par_finished:
            print "Se terminó de procesar la tarea en paralelo antes que en secuencial"
    
    def mission_finished(self, worker, tid, ttype, curMax, level, infto, timeout, tres, tecode, testr, tstats):
        Master.mission_finished(self, worker, tid, ttype, timeout, curMax, level, tres, tecode, testr, tstats)
        if settings.autosensing_timeout and not infto and (tres == 'SAT' or tres == 'UNSAT' or tres == 'TIMEOUT'):
            self.total_st += (timeout * 2) if tstats.get('solver.msecs', '0') == 0 else (float(tstats.get('solver.msecs', '0')) / 1000) + 20
            self.finished_amm += 1
            andrea.settings.experiment['timeout'] = str(int(3 * self.total_st / self.finished_amm))
            #print "Timeout = %d" % timeout
            #print "New Timeout = " + str(4 * self.total_st / self.finished_amm)
            
        
        # if the task is an als, it checks whether 
        # the task gave timeout. In such case it should
        # be passed to T.R.O.L.A. to partionate the file
        # and feedback the partitions to Andrea.

        #IF SOME JOB OF THE PARALLEL ANALISYS FAILS (MEMOUT OR ERROR) AND ALL PARALLEL TASKS FINISH, THIS YET DOESN'T
        #CONTINUE WITH THE SEQUENTIAL JOB, AND INSTEAD IT EXITS AS IF THE PARALLEL ANALISYS ENDED CORRECTLY BEFORE
        #THE SEQUENTIAL ONE

        self.total_processed += 1
        
        if ttype == 'als' and tres == 'TIMEOUT':
            self.partition_tasks.append(PartitionEvent(tid, os.path.join(settings.trola_output_dir, "als", tid), 
                settings.trola_output_dir, settings.scope, settings.rels, curMax=curMax, level=level))
        elif tres != 'MEMOUT' and tres != 'ERROR' and tid == self.main_task_tid:
            self.seq_finished = True
            self.finished = True
        # versión más robusta que no asume nada especial
        elif tres != 'MEMOUT' and tres != 'ERROR' and len(self.tasks_busy) is 1 and len(self.tasks_idle) is 0:
            # solo hay 1 tarea activa y no queda ninguna pendiente
            assert len(self.workers_busy) is 1
            # tomamos el significado de la unica clave de este dict
            last_busy_tid = self.workers_busy.values()[0]
            # que ademas deberia ser el unico elem de este otro set
            assert len(self.tasks_busy) is 1 and last_busy_tid in self.tasks_busy
            # ahora veamos si es la tarea inicial o no...
            if last_busy_tid == self.main_task_tid:
                # solo queda la tarea raiz
                self.par_finished = True
                self.finished = True
            #else:
            #ACA SOLO ENTRA SI EL SECUENCIAL TERMINO MAL Y AHORA SOLO QUEDA 1 TAREA DEL PARALELO PARA TERMINAR
            #print "Queda 1 sola tarea pero no es la secuencial, asique esto no puede estar ocurriendo"
        elif len(self.tasks_idle) is 0 and len(self.workers_busy) is 0 and len(self.partition_tasks) is 0:
            #No pregunto por self.partitioning porque creo que es por esa variable que tuve que hacer esta validacion
            self.par_finished = True
            self.finished = True
        else:
            #SI NO ES EL SECUENCIAL, BORRO EL ALS
            if tid != self.main_task_tid:
                os.remove(os.path.join(settings.trola_output_dir, "als", tid))

    def enqueue_partition(self, partition, infinite_timeout=False, curMax=0, level=0):
        tid = os.path.basename(partition)
        ext = os.path.splitext(tid)[1]
        ttype = ext.lstrip('.')
        tbody = read_file(partition)
        self.tasks_idle.append((tid, ttype, tbody, infinite_timeout, curMax, level))
        self.total_produced += 1
        if infinite_timeout:
            print 'file %s will be enqueued to be resolved with infinite timeout' % tid

    def assign_mission(self):

        """
        Event handler: called when a new mission is needed.

        Returns (worker_id, (tid, ttype, tdata)) tuple.
        """

        tid, ttype, tdata, infinite_timeout, curMax, level = self.tasks_idle.pop(0)
        self.tasks_busy.add(tid)
        worker = self.workers_idle.pop(0)
        self.workers_busy[worker] = tid
        return worker, (tid, ttype, tdata, infinite_timeout, curMax, level, andrea.settings.experiment['timeout'])

    def populate_task_queue(self):
        queue_create_phase = self.bb.add(Event('main', 'queue.create'))
        task_paths = list_all_files(andrea.settings.experiment['tasks'], ('.als', '.cnf'))
        #print task_paths
        for task_path in task_paths:
            tid = os.path.basename(task_path)
            ext = os.path.splitext(tid)[1]
            ttype = ext.lstrip('.')
            tbody = read_file(task_path)
            self.tasks_idle.append((tid, ttype, tbody, True, 0, 0))
            self.partition_tasks.append(PartitionEvent(tid, task_path, 
                settings.trola_output_dir, settings.scope, 
                settings.rels, curMax=0, level=0))
            self.main_task_tid = tid

        # hack para garantizar q el menor scope vaya siempre antes en el scheduling
        #f = lambda string: string[string.find('-s')+2:string.find('-s')+4]+string
        #self.tasks_idle = sorted(self.tasks_idle, key=lambda t: f(t[0]))

        queue_create_phase.result('%d tasks' % len(self.tasks_idle))
        queue_create_phase.finish()

    def partitionate(self):
        """
        if event.scope == 0:
            raise IOError("Scope can not be zero")
        """
        amm = self.upper_lower()
        old_amm = amm

        if amm > len(self.partition_tasks):
            amm = len(self.partition_tasks)
        
        self.upper = self.upper * amm / old_amm
        
        if self.upper < 20 * amm:
            return -1
        
        if settings.statistics == True:
            #print "Producidos: " + str(self.total_produced)
            #print "Consumidos: " + str(self.total_processed)
            #print "ST/PT: " + str(st/pt)
            #print "Alpha: " + str(alpha)
            print "Upper: " + str(self.upper)
            #print "Lower: " + str(self.lower)
            print "To Part: " + str(len(self.partition_tasks))
            print "Will Part: " + str(amm)
            print "AVG Parts: " + str(self.upper / amm)
        
        aux = ExtendedQueue()
        max_sum = 0
        rang = range(0, amm)
        
        for i in rang:
            partition_event = self.partition_tasks.pop(0)
            max_sum += partition_event.max
            aux.append(partition_event)
        
        #upToSum = 0 #DEBUG
        res = 0
        
        for i in rang:
            event = aux.pop(0)
            upTo = ((self.upper * max_sum) / (amm * amm * event.max)) if max_sum > 0 else self.upper / amm
            #upToSum += upTo
            #if upTo == 0: #DEBUG
            #    print "upTo dio 0!!! con self.upper = %d, max_sum = %d, amm = %d, event.max = %d" % (upTo, self.upper, max_sum, amm, event.max) #DEBUG
            (event.partitions, event.max, event.level) = partition(event.file_path, event.output_directory, event.scope, event.rels, self.enqueue_partition, settings.aliasing, upto=upTo, level=event.level)      
        
            if event.partitions == 1 or event.partitions == 0:
                if settings.debug:
                    print 'file %s will be enqueued to be resolved with infinite timeout' % os.path.basename(event.file_path)
                tid = os.path.basename(event.file_path)
                ext = os.path.splitext(tid)[1]
                ttype = ext.lstrip('.')
                tbody = read_file(event.file_path)
                self.tasks_done.remove(tid)
                self.tasks_idle.append((tid, ttype, tbody, True, event.max, event.level))
                event.finish()
            #elif event.partitions == -1:
            #    self.partition_tasks.append(event)
            #    event.finish()
            #    return 1
                #sacar event.finish() de donde esta
            else:
                res = 1
                event.finish()
                print event
        
        #print "self.upper = %d, upToSum = %d" % (self.upper, upToSum) #DEBUG

        return res
        
    def upper_lower(self):
        time = (andrea.network.time() - self.start_time)
        st = self.total_processed / time
        pt = self.total_produced / time
        tq = len(self.tasks_idle)
        
        rand = random.random()
        alpha = 0
        amm = 1
        
        if rand < 0.02:
            alpha = 1000000 * rand
            amm = 5
        elif rand < 0.08:
            alpha = 100000 * rand
            amm = 4
        elif rand < 0.2:
            alpha = 15000 * rand
            amm = 3
        elif rand < 0.5:
            alpha = 2500 * rand
            amm = 2
        else:
            alpha = 500 * rand
            amm = 1
        
        if tq < 1:
            tq = 1
        
        self.upper = (self.workers * st * alpha) / (pt * tq)
        self.lower = (self.total_processed + self.beta * self.workers - self.total_produced) * (st / pt)
        if self.upper < self.lower:
            self.upper = self.lower
        
        #self.lower = 6 * self.workers * st / pt - len(tasks_idle)
        #PRUEBA DE COTA SUPERIOR
        #
            
        ##if self.upper > 3 * self.workers * st * 60:
        ##    self.upper = 3 * self.workers * st * 60

        if self.total_processed == 0:
            self.upper = 32 * self.workers
        
        if self.upper > 32 * self.workers:
            self.upper = 32 * self.workers
        
        return amm
