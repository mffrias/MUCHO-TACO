/* DO NOT EDIT THIS FILE - it is machine generated */
#include <jni.h>
/* Header for class kodkod_engine_satlab_MiniSat220 */

#ifndef _Included_kodkod_engine_satlab_MiniSat220
#define _Included_kodkod_engine_satlab_MiniSat220
#ifdef __cplusplus
extern "C" {
#endif
/*
 * Class:     kodkod_engine_satlab_MiniSat220
 * Method:    make
 * Signature: ()J
 */
JNIEXPORT jlong JNICALL Java_kodkod_engine_satlab_MiniSat220_make
  (JNIEnv *, jclass);

/*
 * Class:     kodkod_engine_satlab_MiniSat220
 * Method:    free
 * Signature: (J)V
 */
JNIEXPORT void JNICALL Java_kodkod_engine_satlab_MiniSat220_free
  (JNIEnv *, jobject, jlong);

/*
 * Class:     kodkod_engine_satlab_MiniSat220
 * Method:    addVariables
 * Signature: (JI)V
 */
JNIEXPORT void JNICALL Java_kodkod_engine_satlab_MiniSat220_addVariables
  (JNIEnv *, jobject, jlong, jint);

/*
 * Class:     kodkod_engine_satlab_MiniSat220
 * Method:    addClause
 * Signature: (J[I)Z
 */
JNIEXPORT jboolean JNICALL Java_kodkod_engine_satlab_MiniSat220_addClause
  (JNIEnv *, jobject, jlong, jintArray);

/*
 * Class:     kodkod_engine_satlab_MiniSat220
 * Method:    solve
 * Signature: (J)Z
 */
JNIEXPORT jboolean JNICALL Java_kodkod_engine_satlab_MiniSat220_solve
  (JNIEnv *, jobject, jlong);

/*
 * Class:     kodkod_engine_satlab_MiniSat220
 * Method:    valueOf
 * Signature: (JI)Z
 */
JNIEXPORT jboolean JNICALL Java_kodkod_engine_satlab_MiniSat220_valueOf
  (JNIEnv *, jobject, jlong, jint);

#ifdef __cplusplus
}
#endif
#endif