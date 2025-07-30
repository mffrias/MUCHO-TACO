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

#include "Solver.h"

using namespace Minisat;


#include <jni.h>
#include "kodkod_engine_satlab_MiniSat220.h"

/*
 * Class:     kodkod_engine_satlab_MiniSat220
 * Method:    make
 * Signature: ()J
 */
JNIEXPORT jlong JNICALL Java_kodkod_engine_satlab_MiniSat220_make
  (JNIEnv *, jclass) {
  Solver* solver = new Solver();
//  cout << "  kodkod_engine_satlab_MiniSat220 (via JNI): created Solver @ " << solver << endl;
//  cout << "kodkod_engine_satlab_MiniSat220: new solver has " << solver->nVars() << " variables" << endl;
  return ((jlong) solver);
}

/*
 * Class:     kodkod_engine_satlab_MiniSat220
 * Method:    free
 * Signature: (J)V
 */
JNIEXPORT void JNICALL Java_kodkod_engine_satlab_MiniSat220_free
  (JNIEnv *, jobject, jlong solver) {
//  Solver* solverPtr = (Solver*) solver;
//  cout << "  kodkod_engine_satlab_MiniSat220 (via JNI): deleting Solver @ " << solverPtr << endl;
  delete ((Solver*)solver);  
}

/*
 * Class:     kodkod_engine_satlab_MiniSat220
 * Method:    addVariables
 * Signature: (JI)V
 */
JNIEXPORT void JNICALL Java_kodkod_engine_satlab_MiniSat220_addVariables
  (JNIEnv *, jobject, jlong solver, jint  numVars) {
  Solver* solverPtr = (Solver*) solver;
//  cout << "kodkod_engine_satlab_MiniSat220: solver @ " << solverPtr << " has " << solverPtr->nVars() << " variables" << endl; 
//  cout << "  kodkod_engine_satlab_MiniSat220: adding " << numVars << " vars to Solver @ " << solverPtr << endl;
  for(int i = 0; i < numVars; ++i) {
     solverPtr->newVar();
  }
}

/*
 * Class:     kodkod_engine_satlab_MiniSat220
 * Method:    addClause
 * Signature: (J[I)Z
 */
JNIEXPORT jboolean JNICALL Java_kodkod_engine_satlab_MiniSat220_addClause
  (JNIEnv * env, jobject, jlong solver, jintArray clause) {
    jsize length = env->GetArrayLength(clause);
    jint* buf = env->GetIntArrayElements(clause, JNI_FALSE);
    Solver* solverPtr = ((Solver*)solver);
    vec<Lit> lits;
    for(int i = 0; i < length; ++i) {
        int tip = *(buf+i);
        int var = abs(tip) - 1;
        //lits.push((var > 0) ? Lit(var-1) : ~Lit(-var-1));
        // A ver...
        lits.push((tip > 0) ? mkLit(var) : ~mkLit(var));
//        cout << "kodkod_engine_satlab_MiniSat220: addcl: pushl: tip=" << tip << " var=" << var << endl;
    }
//    cout << "kodkod_engine_satlab_MiniSat220: addcl: lits.size=" << lits.size() << "" << endl << endl;
    solverPtr->addClause(lits);
    env->ReleaseIntArrayElements(clause, buf, 0);
    return solverPtr->okay();
 }

/*
 * Class:     kodkod_engine_satlab_MiniSat220
 * Method:    solve
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_kodkod_engine_satlab_MiniSat220_solve
  (JNIEnv *, jobject, jlong solver) {
   return ((Solver*)solver)->solve();
  }

/*
 * Class:     kodkod_engine_satlab_MiniSat220
 * Method:    valueOf
 * Signature: (JI)Z
 */
JNIEXPORT jboolean JNICALL Java_kodkod_engine_satlab_MiniSat220_valueOf
  (JNIEnv *, jobject, jlong solver, jint var) {
  return ((Solver*)solver)->model[var-1]==l_True;
 }

