#!/bin/sh

#
# This seems to work OK on Linux amd64 (tried on clyde)
#

echo "Compiling ..."
g++ -c -Wall -Wno-parentheses \
 -O3 -DNDEBUG \
 -D __STDC_LIMIT_MACROS -D __STDC_FORMAT_MACROS \
 -fPIC -shared \
 --friend-injection \
 -I /usr/lib/jvm/java-6-openjdk/include \
  *.cc

echo "Linking ..."
g++ -shared \
 -o libminisat220simp.so \
 -I /usr/lib/jvm/java-6-openjdk/include \
  kodkod_engine_satlab_MiniSat220Simp.o Solver.o System.o

