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

#include <jni.h>
#include "kodkod_engine_satlab_Lingeling.h"

#ifdef __cplusplus
extern "C" {
#endif

#include "lglib.h"

#ifdef __cplusplus
}
#endif


/*
 * Class:     kodkod_engine_satlab_Lingeling
 * Method:    make
 * Signature: ()J
 */
JNIEXPORT jlong JNICALL Java_kodkod_engine_satlab_Lingeling_make
  (JNIEnv *, jclass) {
      LGL * solver = lglinit();
//  cout << "  kodkod_engine_satlab_Lingeling (via JNI): created Solver @ " << solver << endl;
//  cout << "kodkod_engine_satlab_Lingeling: new solver has " << solver->nVars() << " variables" << endl;
  return ((jlong) solver);
}

/*
 * Class:     kodkod_engine_satlab_Lingeling
 * Method:    free
 * Signature: (J)V
 */
JNIEXPORT void JNICALL Java_kodkod_engine_satlab_Lingeling_free
  (JNIEnv *, jobject, jlong solver) {
      LGL * solverPtr = (LGL *) solver;
//  cout << "  kodkod_engine_satlab_Lingeling (via JNI): deleting Solver @ " << solverPtr << endl;
      lglrelease(solverPtr);
}

/*
 * Class:     kodkod_engine_satlab_Lingeling
 * Method:    addVariables
 * Signature: (JI)V
 */
JNIEXPORT void JNICALL Java_kodkod_engine_satlab_Lingeling_addVariables
  (JNIEnv *, jobject, jlong solver, jint  numVars) {
      //LGL * solverPtr = (LGL *) solver;
//  cout << "kodkod_engine_satlab_Lingeling: solver @ " << solverPtr << " has " << solverPtr->nVars() << " variables" << endl; 
//  cout << "  kodkod_engine_satlab_Lingeling: adding " << numVars << " vars to Solver @ " << solverPtr << endl;
//  for(int i = 0; i < numVars; ++i) {
//     solverPtr->newVar();
//  }
      // lglmaxvar(solverPtr);
}

/*
 * Class:     kodkod_engine_satlab_Lingeling
 * Method:    addClause
 * Signature: (J[I)Z
 */
JNIEXPORT jboolean JNICALL Java_kodkod_engine_satlab_Lingeling_addClause
  (JNIEnv * env, jobject, jlong solver, jintArray clause) {
    jsize length = env->GetArrayLength(clause);
    jint* buf = env->GetIntArrayElements(clause, JNI_FALSE);
    LGL * solverPtr = ((LGL *)solver);
    //vec<Lit> lits;
    for(int i = 0; i < length; ++i) {
        int tip = *(buf+i);
        int var = abs(tip);
        lgladd(solverPtr, (tip > 0) ? var : -var);
//        cout << "kodkod_engine_satlab_Lingeling: addcl: pushl: tip=" << tip << " var=" << var << endl;
    }
//    cout << "kodkod_engine_satlab_Lingeling: addcl: lits.size=" << lits.size() << "" << endl << endl;
    lgladd(solverPtr, 0);
    env->ReleaseIntArrayElements(clause, buf, 0);
    return true; // solverPtr->okay();
 }

/*
 * Class:     kodkod_engine_satlab_Lingeling
 * Method:    solve
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_kodkod_engine_satlab_Lingeling_solve
  (JNIEnv *, jobject, jlong solver) {
   int res = lglsat((LGL*)solver);
   if(res == 10) return true;
   if(res == 20) return false;
   assert(false); return false;
  }

/*
 * Class:     kodkod_engine_satlab_Lingeling
 * Method:    valueOf
 * Signature: (JI)Z
 */
JNIEXPORT jboolean JNICALL Java_kodkod_engine_satlab_Lingeling_valueOf
  (JNIEnv *, jobject, jlong solver, jint var) {
      return lglderef((LGL*)solver, var) > 0;
 }

