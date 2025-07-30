#include <iostream>
#include <cstdlib>
#include <cstdio>
#include <cstring>
#include <cassert>

#include <map>
#include <set>
#include <vector>
#include <list>
#include <string>
#include <algorithm>
#include <queue>

using namespace std;

#include "SimpSolver.h"

using namespace Minisat;


#include <jni.h>
#include "kodkod_engine_satlab_MiniSat220Simp.h"

/*
 * Class:     kodkod_engine_satlab_MiniSat220Simp
 * Method:    make
 * Signature: ()J
 */
JNIEXPORT jlong JNICALL Java_kodkod_engine_satlab_MiniSat220Simp_make
  (JNIEnv *, jclass) {
  SimpSolver* solver = new SimpSolver();
//  cout << "  kodkod_engine_satlab_MiniSat220Simp (via JNI): created SimpSolver @ " << solver << endl;
//  cout << "kodkod_engine_satlab_MiniSat220Simp: new solver has " << solver->nVars() << " variables" << endl;
  return ((jlong) solver);
}

/*
 * Class:     kodkod_engine_satlab_MiniSat220Simp
 * Method:    free
 * Signature: (J)V
 */
JNIEXPORT void JNICALL Java_kodkod_engine_satlab_MiniSat220Simp_free
  (JNIEnv *, jobject, jlong solver) {
//  SimpSolver* solverPtr = (SimpSolver*) solver;
//  cout << "  kodkod_engine_satlab_MiniSat220Simp (via JNI): deleting SimpSolver @ " << solverPtr << endl;
  delete ((SimpSolver*)solver);  
}

/*
 * Class:     kodkod_engine_satlab_MiniSat220Simp
 * Method:    addVariables
 * Signature: (JI)V
 */
JNIEXPORT void JNICALL Java_kodkod_engine_satlab_MiniSat220Simp_addVariables
  (JNIEnv *, jobject, jlong solver, jint  numVars) {
  SimpSolver* solverPtr = (SimpSolver*) solver;
//  cout << "kodkod_engine_satlab_MiniSat220Simp: solver @ " << solverPtr << " has " << solverPtr->nVars() << " variables" << endl; 
//  cout << "  kodkod_engine_satlab_MiniSat220Simp: adding " << numVars << " vars to SimpSolver @ " << solverPtr << endl;
  for(int i = 0; i < numVars; ++i) {
     solverPtr->newVar();
  }
}

/*
 * Class:     kodkod_engine_satlab_MiniSat220Simp
 * Method:    addClause
 * Signature: (J[I)Z
 */
JNIEXPORT jboolean JNICALL Java_kodkod_engine_satlab_MiniSat220Simp_addClause
  (JNIEnv * env, jobject, jlong solver, jintArray clause) {
    jsize length = env->GetArrayLength(clause);
    jint* buf = env->GetIntArrayElements(clause, JNI_FALSE);
    SimpSolver* solverPtr = ((SimpSolver*)solver);
    vec<Lit> lits;
    for(int i = 0; i < length; ++i) {
        int tip = *(buf+i);
        int var = abs(tip) - 1;
        //lits.push((var > 0) ? Lit(var-1) : ~Lit(-var-1));
        // A ver...
        lits.push((tip > 0) ? mkLit(var) : ~mkLit(var));
//        cout << "kodkod_engine_satlab_MiniSat220Simp: addcl: pushl: tip=" << tip << " var=" << var << endl;
    }
//    cout << "kodkod_engine_satlab_MiniSat220Simp: addcl: lits.size=" << lits.size() << "" << endl << endl;
    solverPtr->addClause(lits);
    env->ReleaseIntArrayElements(clause, buf, 0);
    return solverPtr->okay();
 }

/*
 * Class:     kodkod_engine_satlab_MiniSat220Simp
 * Method:    solve
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_kodkod_engine_satlab_MiniSat220Simp_solve
  (JNIEnv *, jobject, jlong solver) {
      SimpSolver* solverPtr = ((SimpSolver*)solver);
      solverPtr->eliminate(true);
      if(!solverPtr->okay())
          return false;
      return ((SimpSolver*)solver)->solve();
  }

/*
 * Class:     kodkod_engine_satlab_MiniSat220Simp
 * Method:    valueOf
 * Signature: (JI)Z
 */
JNIEXPORT jboolean JNICALL Java_kodkod_engine_satlab_MiniSat220Simp_valueOf
  (JNIEnv *, jobject, jlong solver, jint var) {
  return ((SimpSolver*)solver)->model[var-1]==l_True;
 }

