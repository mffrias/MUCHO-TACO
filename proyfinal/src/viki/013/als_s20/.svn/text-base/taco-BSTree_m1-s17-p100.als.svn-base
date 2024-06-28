/* 
 * DynAlloy translator options 
 * --------------------------- 
 * applySimplifications= true
 * assertionId= BSTree_m1
 * loopUnroll= 10
 * removeQuantifiers= true
 * strictUnrolling= false
 */ 

//-------------- prelude--------------//
module moduleId
open util/integer
open util/sequniv as sequniv
one sig null {}
fun fun_reach[h: univ, 
              type: set univ, 
              field: univ -> univ
]: set univ { 
  h.*(field & type->(type+null)) & type 
}
abstract sig boolean {}
one sig true extends boolean {}
one sig false extends boolean {}
abstract sig char {}
pred TruePred[] {} 
pred FalsePred[] { not TruePred[] } 
pred equ[l,r:univ] {l=r} 
pred neq[l,r:univ] {l!=r} 

fun shl[l,r: Int]: Int { l << r } 
fun sshr[l,r: Int]: Int { l >> r } 
fun ushr[l,r: Int]: Int { l >>> r } 

fun fun_univ_equals[
  l:univ, 
  r: univ 
]: boolean { 
  (equ[l,r]) => true else false 
} 

fun fun_set_add[
  l: set univ,
  e: univ
]: set univ { 
  l+e 
} 

fun fun_set_remove[
  l: set univ,
  e: univ
]: set univ {
  l-e
}
fun fun_set_contains[
  l: set univ,
  e: univ
]: boolean {
  (e in l) => true else false 
} 
pred isSubset[
  l: set univ,
  r: set univ
] {
  (l in r) 
} 
pred isNotSubset[
  l: set univ,
  r: set univ
] {
  (l !in r) 
} 
fun fun_set_size[s: set univ]: Int { #s } 

fun fun_not_empty_set[s: set univ]: boolean { (#s = 0) => false else true } 

pred pred_empty_set[l: set univ] { (no l) } 

pred pred_set_some[l: set univ] { some l } 

pred pred_set_one[l: set univ] { one l } 

pred pred_set_lone[l: set univ] { lone l } 

pred pred_Object_subset[
  s: set univ
] {
  s in java_lang_Object+null
}

fun fun_set_intersection[
  l: set univ,
  r: set univ
]: set univ {
  l & r 
} 
fun fun_set_difference[
  l: set univ,
  r: set univ
]: set univ {
  l - r 
} 
fun fun_set_sum[
  s: set Int
]: Int {
  sum s 
} 
pred pred_empty_list[l: seq univ] { (no l) } 

fun fun_list_add[
  l: seq univ,
  e: univ
]: seq univ {
  sequniv/add[l,e] 
} 

fun fun_list_get[
  l: seq univ, 
  index: Int
]: univ { 
  index.l 
} 

fun fun_list_contains[
  l: seq univ, 
  e: univ
]: boolean { 
  (e in Int.l) => true else false 
} 

fun fun_list_remove[
  l: seq univ, 
  index: Int
]: seq univ { 
  sequniv/delete[l,index] 
} 

fun fun_list_size[s: seq univ]: Int { #s } 

fun fun_list_equals[
  s1:seq univ, 
  s2: seq univ
]: boolean { 
  (s1=s2) => true else false 
} 

fun fun_list_empty[s: seq univ]: boolean { (#s = 0) => true else false } 

pred pred_empty_map[map: univ -> univ] { (no map) } 

fun fun_map_put[
  map: univ->univ, 
  k: univ, 
  v: univ
]: univ-> univ { 
  map ++ (k->v) 
}

fun fun_map_contains_key[
  map: univ -> univ, 
  k: univ
]: boolean { 
  (some k.map) => true else false 
}

fun fun_map_remove[
  map: univ -> univ, 
  k: univ
]: univ->univ {
  map - (k->univ) 
} 

fun fun_map_get[
  map: univ -> univ, 
  k: univ
]: univ { 
  (some k.map) => k.map else null 
} 

fun fun_map_is_empty[
  map: univ -> univ, 
]: boolean { 
  (some map) => false else true 
}

fun fun_map_clear[
  mapEntries1: univ -> univ -> univ, 
  map: univ
]: univ -> univ -> univ { 
  mapEntries1 - (map -> univ -> univ)
}

fun fun_map_size[
  map: univ -> univ, 
]: univ {
  #map 
} 

pred isEmptyOrNull[u: univ] { u in null } 
fun fun_closure[
  rel: univ -> univ 
]: univ -> univ {
  ^rel 
} 

fun fun_reflexive_closure[
  rel: univ -> univ 
]: univ -> univ {
  *rel 
} 

fun fun_transpose[
  rel: univ -> univ 
]: univ -> univ {
  ~rel 
} 

pred liftExpression[
  expr: univ 
] {
  expr=true 
} 

fun rel_override[
  r:univ->univ,
  k:univ, 
  v:univ
]: univ->univ { 
  r - (k->univ) + (k->v) 
} 

pred updateFieldPost[
  f1:univ->univ,
  f0:univ->univ,
  l:univ,
  r:univ
]{ 
  (r=none) => f1=f0-(l->univ) else f1 = f0 ++ (l->r) 
} 

pred havocVarPost[u:univ]{} 
pred havocVariable2Post[u:univ->univ]{}
pred havocVariable3Post[u:univ->(seq univ)]{}
pred havocFieldPost[f0,f1: univ->univ, u:univ]{ 
  u<:f0 = u<:f1 
  some u.f1  
} 

pred havocArrayContentsPost[array:  univ,
                            domain: set univ,
                            Object_Array_0: univ -> (seq univ),
                            Object_Array_1: univ -> (seq univ)
                           ] {
  Object_Array_1 - (array->(domain->univ)) = Object_Array_0 - (array->(domain->univ))
  (array.Object_Array_1).univ = (array.Object_Array_0).univ
}
pred havocFieldContentsPost[target: univ, 
                            field_0: univ -> univ, 
                            field_1: univ -> univ] { 
  field_1 - (target->univ) = field_0 - (target->univ) 
}
pred pred_in[n: univ, t: set univ] { n in t } 

pred instanceOf[n: univ, t: set univ] { n in t } 

pred isCasteableTo[n: univ, t: set univ] { (n in t) or (n = null) } 

pred getUnusedObjectPost[
  usedObjects1:set java_lang_Object, 
  usedObjects0:set java_lang_Object,
  n1: java_lang_Object+null
]{ 
  n1 !in usedObjects0 
  usedObjects1 = usedObjects0 + (n1)
}
//-------------- examples_bstree_Node--------------//
sig examples_bstree_Node extends java_lang_Object {}
{}




//-------------- java_lang_RuntimeException--------------//
abstract sig java_lang_RuntimeException extends java_lang_Exception {}
{}



one
sig java_lang_RuntimeExceptionLit extends java_lang_RuntimeException {}
{}

//-------------- java_lang_Exception--------------//
abstract sig java_lang_Exception extends java_lang_Throwable {}
{}




//-------------- java_lang_Throwable--------------//
abstract sig java_lang_Throwable {}
{}




//-------------- examples_bstree_BinTree--------------//
sig examples_bstree_BinTree extends java_lang_Object {}
{}




pred examples_bstree_BinTreeCondition1[
  thiz:univ
]{
   not (
     isEmptyOrNull[thiz])

}

pred examples_bstree_BinTreeCondition0[
  thiz:univ
]{
   isEmptyOrNull[thiz]

}

pred examples_bstree_BinTreeCondition7[
  examples_bstree_Node_key:univ->univ,
  var_3_current:univ,
  x:univ
]{
   not (
     equ[var_3_current.examples_bstree_Node_key,
        x]
   )

}

pred examples_bstree_BinTreeCondition6[
  examples_bstree_Node_key:univ->univ,
  var_3_current:univ,
  x:univ
]{
   equ[var_3_current.examples_bstree_Node_key,
      x]

}

pred examples_bstree_BinTree_nodes_abstraction[
  examples_bstree_BinTree_root:univ->univ,
  examples_bstree_Node_left:univ->univ,
  examples_bstree_Node_right:univ->univ,
  nodes:univ->univ,
  thiz:univ
]{
   equ[thiz.nodes,
      fun_set_difference[(thiz.examples_bstree_BinTree_root).(fun_reflexive_closure[examples_bstree_Node_left+examples_bstree_Node_right]),null]]

}

pred examples_bstree_BinTreeCondition4[
  var_3_current:univ
]{
   isEmptyOrNull[var_3_current]

}

pred examples_bstree_BinTreeCondition5[
  var_3_current:univ
]{
   not (
     isEmptyOrNull[var_3_current])

}

pred precondition_examples_bstree_BinTree_find_0[
  examples_bstree_BinTree_root:univ->univ,
  examples_bstree_Node_key:univ->univ,
  examples_bstree_Node_left:univ->univ,
  examples_bstree_Node_right:univ->univ,
  nodes:univ->univ,
  thiz:univ,
  throw:univ
]{
   examples_bstree_BinTree_nodes_abstraction[examples_bstree_BinTree_root,
                                            examples_bstree_Node_left,
                                            examples_bstree_Node_right,
                                            nodes,
                                            thiz]
   and 
   equ[throw,
      null]
   and 
   examples_bstree_BinTree_object_invariant[examples_bstree_BinTree_root,
                                           examples_bstree_Node_key,
                                           examples_bstree_Node_left,
                                           examples_bstree_Node_right,
                                           thiz]

}

pred examples_bstree_BinTreeCondition9[
  examples_bstree_Node_key:univ->univ,
  var_3_current:univ,
  x:univ
]{
   not (
     lt[x,
       var_3_current.examples_bstree_Node_key]
   )

}

pred examples_bstree_BinTree_ensures[
  examples_bstree_Node_key':univ->univ,
  nodes':univ->univ,
  return':univ,
  thiz:univ,
  throw':univ,
  x':univ
]{
   (
     equ[return',
        true]
     iff
     some n:examples_bstree_Node | {
       isSubset[n,
               thiz.nodes']
       and 
       equ[n.examples_bstree_Node_key',
          x']
     
     }
   )
   and 
   equ[throw',
      null]

}

pred examples_bstree_BinTreeCondition8[
  examples_bstree_Node_key:univ->univ,
  var_3_current:univ,
  x:univ
]{
   lt[x,
     var_3_current.examples_bstree_Node_key]

}

pred examples_bstree_BinTreeCondition13[
  nullDerefBool:univ,
  throw:univ
]{
   not (
     equ[nullDerefBool,
        true]
     and 
     equ[throw,
        null]
   )

}

pred examples_bstree_BinTreeCondition12[
  nullDerefBool:univ,
  throw:univ
]{
   equ[nullDerefBool,
      true]
   and 
   equ[throw,
      null]

}

pred postcondition_examples_bstree_BinTree_find_0[
  examples_bstree_Node_key':univ->univ,
  nodes':univ->univ,
  return':univ,
  thiz:univ,
  throw':univ,
  x':univ
]{
   examples_bstree_BinTree_ensures[examples_bstree_Node_key',
                                  nodes',
                                  return',
                                  thiz,
                                  throw',
                                  x']

}

pred examples_bstree_BinTree_object_invariant[
  examples_bstree_BinTree_root:univ->univ,
  examples_bstree_Node_key:univ->univ,
  examples_bstree_Node_left:univ->univ,
  examples_bstree_Node_right:univ->univ,
  thiz:univ
]{
   all n:examples_bstree_Node | {
     isSubset[n,
             (thiz.examples_bstree_BinTree_root).(fun_reflexive_closure[examples_bstree_Node_left+examples_bstree_Node_right])]
     implies 
             (
               isNotSubset[n,
                          n.(fun_closure[examples_bstree_Node_left+examples_bstree_Node_right])]
               and 
               (
                 all m:examples_bstree_Node | {
                   isSubset[m,
                           (n.examples_bstree_Node_left).(fun_reflexive_closure[examples_bstree_Node_left+examples_bstree_Node_right])]
                   implies 
                           lt[m.examples_bstree_Node_key,
                             n.examples_bstree_Node_key]
                 
                 }
               )
               and 
               (
                 all m:examples_bstree_Node | {
                   isSubset[m,
                           (n.examples_bstree_Node_right).(fun_reflexive_closure[examples_bstree_Node_left+examples_bstree_Node_right])]
                   implies 
                           lt[n.examples_bstree_Node_key,
                             m.examples_bstree_Node_key]
                 
                 }
               )
             )
   
   }

}

pred examples_bstree_BinTreeCondition2[
  exit_stmt_reached:univ
]{
   exit_stmt_reached=false

}

pred examples_bstree_BinTreeCondition3[
  exit_stmt_reached:univ
]{
   not (
     exit_stmt_reached=false)

}

pred examples_bstree_BinTreeCondition10[
  exit_stmt_reached:univ,
  var_4_ws_2:univ
]{
   liftExpression[var_4_ws_2]
   and 
   (
     exit_stmt_reached=false)

}

pred examples_bstree_BinTreeCondition11[
  exit_stmt_reached:univ,
  var_4_ws_2:univ
]{
   not (
     liftExpression[var_4_ws_2]
     and 
     (
       exit_stmt_reached=false)
   )

}
//-------------- java_lang_Object--------------//
abstract sig java_lang_Object {}
{}




//-------------- java_lang_NullPointerException--------------//
abstract one sig java_lang_NullPointerException extends java_lang_RuntimeException {}
{}



one
sig java_lang_NullPointerExceptionLit extends java_lang_NullPointerException {}
{}



pred updateVariable[
  l_1: univ,
  r_0: univ
]{
  TruePred[]
  and 
  equ[l_1,
     r_0]
}


pred getUnusedObject[
  n_1: java_lang_Object + null,
  usedObjects_0: set java_lang_Object,
  usedObjects_1: set java_lang_Object
]{
  TruePred[]
  and 
  getUnusedObjectPost[usedObjects_1,
                     usedObjects_0,
                     n_1]
}


pred havocVariable[
  v_1: univ
]{
  TruePred[]
  and 
  havocVarPost[v_1]
}


pred havocFieldContents[
  target_0: univ,
  field_0: univ -> univ,
  field_1: univ -> univ
]{
  TruePred[]
  and 
  havocFieldContentsPost[target_0,
                        field_0,
                        field_1]
}


pred havocVariable3[
  u_1: univ -> ( seq univ )
]{
  TruePred[]
  and 
  havocVariable3Post[u_1]
}


pred havocVariable2[
  u_1: univ -> univ
]{
  TruePred[]
  and 
  havocVariable2Post[u_1]
}


pred havocField[
  f_0: univ -> univ,
  f_1: univ -> univ,
  u_0: univ
]{
  TruePred[]
  and 
  havocFieldPost[f_0,
                f_1,
                u_0]
}


pred updateField[
  l_0: univ,
  f_0: univ -> univ,
  f_1: univ -> univ,
  r_0: univ
]{
  TruePred[]
  and 
  updateFieldPost[f_1,
                 f_0,
                 l_0,
                 r_0]
}


pred havocArrayContents[
  array_0: univ,
  domain_0: set univ,
  Object_Array_0: univ -> ( seq univ ),
  Object_Array_1: univ -> ( seq univ )
]{
  TruePred[]
  and 
  havocArrayContentsPost[array_0,
                        domain_0,
                        Object_Array_0,
                        Object_Array_1]
}


pred simulate_examples_bstree_BinTree_find_0[
  thiz_0: examples_bstree_BinTree,
  examples_bstree_BinTree_root_0: ( examples_bstree_BinTree ) -> one ( examples_bstree_Node + null ),
  x_0: Int,
  throw_0: java_lang_Throwable + null,
  throw_1: java_lang_Throwable + null,
  throw_2: java_lang_Throwable + null,
  examples_bstree_Node_right_0: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  return_0: boolean,
  return_1: boolean,
  return_2: boolean,
  return_3: boolean,
  return_4: boolean,
  return_5: boolean,
  return_6: boolean,
  return_7: boolean,
  return_8: boolean,
  return_9: boolean,
  return_10: boolean,
  return_11: boolean,
  nodes_0: ( examples_bstree_BinTree ) -> ( examples_bstree_Node ),
  examples_bstree_Node_key_0: ( examples_bstree_Node ) -> one ( Int ),
  examples_bstree_Node_left_0: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  l0_exit_stmt_reached_1: boolean,
  l0_exit_stmt_reached_2: boolean,
  l0_exit_stmt_reached_3: boolean,
  l0_exit_stmt_reached_4: boolean,
  l0_exit_stmt_reached_5: boolean,
  l0_exit_stmt_reached_6: boolean,
  l0_exit_stmt_reached_7: boolean,
  l0_exit_stmt_reached_8: boolean,
  l0_exit_stmt_reached_9: boolean,
  l0_exit_stmt_reached_10: boolean,
  l0_exit_stmt_reached_11: boolean,
  l0_exit_stmt_reached_12: boolean,
  l0_nullDerefBool_1: boolean,
  l0_nullDerefBool_2: boolean,
  l0_nullDerefBool_3: boolean,
  l0_nullDerefBool_4: boolean,
  l0_nullDerefBool_5: boolean,
  l0_nullDerefBool_6: boolean,
  l0_nullDerefBool_7: boolean,
  l0_nullDerefBool_8: boolean,
  l0_nullDerefBool_9: boolean,
  l0_nullDerefBool_10: boolean,
  l0_nullDerefBool_11: boolean,
  l0_nullDerefBool_12: boolean,
  l0_nullDerefBool_13: boolean,
  l0_nullDerefBool_14: boolean,
  l0_nullDerefBool_15: boolean,
  l0_nullDerefBool_16: boolean,
  l0_nullDerefBool_17: boolean,
  l0_nullDerefBool_18: boolean,
  l0_nullDerefBool_19: boolean,
  l0_nullDerefBool_20: boolean,
  l0_nullDerefBool_21: boolean,
  l0_nullDerefBool_22: boolean,
  l0_nullDerefBool_23: boolean,
  l0_nullDerefBool_24: boolean,
  l0_nullDerefBool_25: boolean,
  l0_nullDerefBool_26: boolean,
  l0_nullDerefBool_27: boolean,
  l0_nullDerefBool_28: boolean,
  l0_nullDerefBool_29: boolean,
  l0_nullDerefBool_30: boolean,
  l0_nullDerefBool_31: boolean,
  l0_nullDerefBool_32: boolean,
  l0_var_3_current_0: examples_bstree_Node + null,
  l0_var_3_current_1: examples_bstree_Node + null,
  l0_var_3_current_2: examples_bstree_Node + null,
  l0_var_3_current_3: examples_bstree_Node + null,
  l0_var_3_current_4: examples_bstree_Node + null,
  l0_var_3_current_5: examples_bstree_Node + null,
  l0_var_3_current_6: examples_bstree_Node + null,
  l0_var_3_current_7: examples_bstree_Node + null,
  l0_var_3_current_8: examples_bstree_Node + null,
  l0_var_3_current_9: examples_bstree_Node + null,
  l0_var_3_current_10: examples_bstree_Node + null,
  l0_var_3_current_11: examples_bstree_Node + null,
  l0_var_4_ws_2_0: boolean,
  l0_var_4_ws_2_1: boolean,
  l0_var_4_ws_2_2: boolean,
  l0_var_4_ws_2_3: boolean,
  l0_var_4_ws_2_4: boolean,
  l0_var_4_ws_2_5: boolean,
  l0_var_4_ws_2_6: boolean,
  l0_var_4_ws_2_7: boolean,
  l0_var_4_ws_2_8: boolean,
  l0_var_4_ws_2_9: boolean,
  l0_var_4_ws_2_10: boolean,
  l0_var_4_ws_2_11: boolean
]{
  precondition_examples_bstree_BinTree_find_0[examples_bstree_BinTree_root_0,
                                             examples_bstree_Node_key_0,
                                             examples_bstree_Node_left_0,
                                             examples_bstree_Node_right_0,
                                             nodes_0,
                                             thiz_0,
                                             throw_0]
  and 
  examples_bstree_BinTree_find_0[thiz_0,
                                throw_1,
                                throw_2,
                                return_0,
                                return_1,
                                return_2,
                                return_3,
                                return_4,
                                return_5,
                                return_6,
                                return_7,
                                return_8,
                                return_9,
                                return_10,
                                return_11,
                                x_0,
                                examples_bstree_Node_right_0,
                                examples_bstree_Node_key_0,
                                examples_bstree_BinTree_root_0,
                                examples_bstree_Node_left_0,
                                l0_exit_stmt_reached_1,
                                l0_exit_stmt_reached_2,
                                l0_exit_stmt_reached_3,
                                l0_exit_stmt_reached_4,
                                l0_exit_stmt_reached_5,
                                l0_exit_stmt_reached_6,
                                l0_exit_stmt_reached_7,
                                l0_exit_stmt_reached_8,
                                l0_exit_stmt_reached_9,
                                l0_exit_stmt_reached_10,
                                l0_exit_stmt_reached_11,
                                l0_exit_stmt_reached_12,
                                l0_var_3_current_0,
                                l0_var_3_current_1,
                                l0_var_3_current_2,
                                l0_var_3_current_3,
                                l0_var_3_current_4,
                                l0_var_3_current_5,
                                l0_var_3_current_6,
                                l0_var_3_current_7,
                                l0_var_3_current_8,
                                l0_var_3_current_9,
                                l0_var_3_current_10,
                                l0_var_3_current_11,
                                l0_nullDerefBool_1,
                                l0_nullDerefBool_2,
                                l0_nullDerefBool_3,
                                l0_nullDerefBool_4,
                                l0_nullDerefBool_5,
                                l0_nullDerefBool_6,
                                l0_nullDerefBool_7,
                                l0_nullDerefBool_8,
                                l0_nullDerefBool_9,
                                l0_nullDerefBool_10,
                                l0_nullDerefBool_11,
                                l0_nullDerefBool_12,
                                l0_nullDerefBool_13,
                                l0_nullDerefBool_14,
                                l0_nullDerefBool_15,
                                l0_nullDerefBool_16,
                                l0_nullDerefBool_17,
                                l0_nullDerefBool_18,
                                l0_nullDerefBool_19,
                                l0_nullDerefBool_20,
                                l0_nullDerefBool_21,
                                l0_nullDerefBool_22,
                                l0_nullDerefBool_23,
                                l0_nullDerefBool_24,
                                l0_nullDerefBool_25,
                                l0_nullDerefBool_26,
                                l0_nullDerefBool_27,
                                l0_nullDerefBool_28,
                                l0_nullDerefBool_29,
                                l0_nullDerefBool_30,
                                l0_nullDerefBool_31,
                                l0_nullDerefBool_32,
                                l0_var_4_ws_2_0,
                                l0_var_4_ws_2_1,
                                l0_var_4_ws_2_2,
                                l0_var_4_ws_2_3,
                                l0_var_4_ws_2_4,
                                l0_var_4_ws_2_5,
                                l0_var_4_ws_2_6,
                                l0_var_4_ws_2_7,
                                l0_var_4_ws_2_8,
                                l0_var_4_ws_2_9,
                                l0_var_4_ws_2_10,
                                l0_var_4_ws_2_11]
  and 
  postcondition_examples_bstree_BinTree_find_0[examples_bstree_Node_key_0,
                                              nodes_0,
                                              return_11,
                                              thiz_0,
                                              throw_2,
                                              x_0]

}



pred examples_bstree_BinTree_find_0[
  thiz_0: examples_bstree_BinTree,
  throw_1: java_lang_Throwable + null,
  throw_2: java_lang_Throwable + null,
  return_0: boolean,
  return_1: boolean,
  return_2: boolean,
  return_3: boolean,
  return_4: boolean,
  return_5: boolean,
  return_6: boolean,
  return_7: boolean,
  return_8: boolean,
  return_9: boolean,
  return_10: boolean,
  return_11: boolean,
  x_0: Int,
  examples_bstree_Node_right_0: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_key_0: ( examples_bstree_Node ) -> one ( Int ),
  examples_bstree_BinTree_root_0: ( examples_bstree_BinTree ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_0: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  exit_stmt_reached_1: boolean,
  exit_stmt_reached_2: boolean,
  exit_stmt_reached_3: boolean,
  exit_stmt_reached_4: boolean,
  exit_stmt_reached_5: boolean,
  exit_stmt_reached_6: boolean,
  exit_stmt_reached_7: boolean,
  exit_stmt_reached_8: boolean,
  exit_stmt_reached_9: boolean,
  exit_stmt_reached_10: boolean,
  exit_stmt_reached_11: boolean,
  exit_stmt_reached_12: boolean,
  var_3_current_0: examples_bstree_Node + null,
  var_3_current_1: examples_bstree_Node + null,
  var_3_current_2: examples_bstree_Node + null,
  var_3_current_3: examples_bstree_Node + null,
  var_3_current_4: examples_bstree_Node + null,
  var_3_current_5: examples_bstree_Node + null,
  var_3_current_6: examples_bstree_Node + null,
  var_3_current_7: examples_bstree_Node + null,
  var_3_current_8: examples_bstree_Node + null,
  var_3_current_9: examples_bstree_Node + null,
  var_3_current_10: examples_bstree_Node + null,
  var_3_current_11: examples_bstree_Node + null,
  nullDerefBool_1: boolean,
  nullDerefBool_2: boolean,
  nullDerefBool_3: boolean,
  nullDerefBool_4: boolean,
  nullDerefBool_5: boolean,
  nullDerefBool_6: boolean,
  nullDerefBool_7: boolean,
  nullDerefBool_8: boolean,
  nullDerefBool_9: boolean,
  nullDerefBool_10: boolean,
  nullDerefBool_11: boolean,
  nullDerefBool_12: boolean,
  nullDerefBool_13: boolean,
  nullDerefBool_14: boolean,
  nullDerefBool_15: boolean,
  nullDerefBool_16: boolean,
  nullDerefBool_17: boolean,
  nullDerefBool_18: boolean,
  nullDerefBool_19: boolean,
  nullDerefBool_20: boolean,
  nullDerefBool_21: boolean,
  nullDerefBool_22: boolean,
  nullDerefBool_23: boolean,
  nullDerefBool_24: boolean,
  nullDerefBool_25: boolean,
  nullDerefBool_26: boolean,
  nullDerefBool_27: boolean,
  nullDerefBool_28: boolean,
  nullDerefBool_29: boolean,
  nullDerefBool_30: boolean,
  nullDerefBool_31: boolean,
  nullDerefBool_32: boolean,
  var_4_ws_2_0: boolean,
  var_4_ws_2_1: boolean,
  var_4_ws_2_2: boolean,
  var_4_ws_2_3: boolean,
  var_4_ws_2_4: boolean,
  var_4_ws_2_5: boolean,
  var_4_ws_2_6: boolean,
  var_4_ws_2_7: boolean,
  var_4_ws_2_8: boolean,
  var_4_ws_2_9: boolean,
  var_4_ws_2_10: boolean,
  var_4_ws_2_11: boolean
]{
  TruePred[]
  and 
  (
    nullDerefBool_1=false)
  and 
  (
    throw_1=null)
  and 
  TruePred[]
  and 
  (
    exit_stmt_reached_1=false)
  and 
  TruePred[]
  and 
  (
    (
      examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
      and 
      (
        (
          examples_bstree_BinTreeCondition0[thiz_0]
          and 
          (
            nullDerefBool_2=true)
        )
        or 
        (
          (
            not (
              examples_bstree_BinTreeCondition0[thiz_0])
          )
          and 
          TruePred[]
          and 
          (
            nullDerefBool_1=nullDerefBool_2)
        )
      )
      and 
      (
        var_3_current_1=thiz_0.examples_bstree_BinTree_root_0)
    )
    or 
    (
      (
        not (
          examples_bstree_BinTreeCondition2[exit_stmt_reached_1])
      )
      and 
      TruePred[]
      and 
      (
        var_3_current_0=var_3_current_1)
      and 
      (
        nullDerefBool_1=nullDerefBool_2)
    )
  )
  and 
  TruePred[]
  and 
  (
    (
      examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
      and 
      (
        var_4_ws_2_1=(neq[var_3_current_1,
           null]=>(true)else(false))
      )
    )
    or 
    (
      (
        not (
          examples_bstree_BinTreeCondition2[exit_stmt_reached_1])
      )
      and 
      TruePred[]
      and 
      (
        var_4_ws_2_0=var_4_ws_2_1)
    )
  )
  and 
  (
    (
      examples_bstree_BinTreeCondition10[exit_stmt_reached_1,
                                        var_4_ws_2_1]
      and 
      (
        (
          examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
          and 
          (
            (
              examples_bstree_BinTreeCondition4[var_3_current_1]
              and 
              (
                nullDerefBool_3=true)
            )
            or 
            (
              (
                not (
                  examples_bstree_BinTreeCondition4[var_3_current_1])
              )
              and 
              TruePred[]
              and 
              (
                nullDerefBool_2=nullDerefBool_3)
            )
          )
          and 
          (
            (
              examples_bstree_BinTreeCondition6[examples_bstree_Node_key_0,
                                               var_3_current_1,
                                               x_0]
              and 
              (
                (
                  examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
                  and 
                  (
                    return_1=true)
                  and 
                  (
                    exit_stmt_reached_2=true)
                )
                or 
                (
                  (
                    not (
                      examples_bstree_BinTreeCondition2[exit_stmt_reached_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    return_0=return_1)
                  and 
                  (
                    exit_stmt_reached_1=exit_stmt_reached_2)
                )
              )
            )
            or 
            (
              (
                not (
                  examples_bstree_BinTreeCondition6[examples_bstree_Node_key_0,
                                                   var_3_current_1,
                                                   x_0]
                )
              )
              and 
              TruePred[]
              and 
              (
                exit_stmt_reached_1=exit_stmt_reached_2)
              and 
              (
                return_0=return_1)
            )
          )
        )
        or 
        (
          (
            not (
              examples_bstree_BinTreeCondition2[exit_stmt_reached_1])
          )
          and 
          TruePred[]
          and 
          (
            return_0=return_1)
          and 
          (
            nullDerefBool_2=nullDerefBool_3)
          and 
          (
            exit_stmt_reached_1=exit_stmt_reached_2)
        )
      )
      and 
      (
        (
          examples_bstree_BinTreeCondition2[exit_stmt_reached_2]
          and 
          (
            (
              examples_bstree_BinTreeCondition4[var_3_current_1]
              and 
              (
                nullDerefBool_4=true)
            )
            or 
            (
              (
                not (
                  examples_bstree_BinTreeCondition4[var_3_current_1])
              )
              and 
              TruePred[]
              and 
              (
                nullDerefBool_3=nullDerefBool_4)
            )
          )
          and 
          (
            (
              examples_bstree_BinTreeCondition8[examples_bstree_Node_key_0,
                                               var_3_current_1,
                                               x_0]
              and 
              (
                (
                  examples_bstree_BinTreeCondition2[exit_stmt_reached_2]
                  and 
                  (
                    (
                      examples_bstree_BinTreeCondition4[var_3_current_1]
                      and 
                      (
                        nullDerefBool_5=true)
                    )
                    or 
                    (
                      (
                        not (
                          examples_bstree_BinTreeCondition4[var_3_current_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_4=nullDerefBool_5)
                    )
                  )
                  and 
                  (
                    var_3_current_2=var_3_current_1.examples_bstree_Node_left_0)
                )
                or 
                (
                  (
                    not (
                      examples_bstree_BinTreeCondition2[exit_stmt_reached_2])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    var_3_current_1=var_3_current_2)
                  and 
                  (
                    nullDerefBool_4=nullDerefBool_5)
                )
              )
            )
            or 
            (
              (
                not (
                  examples_bstree_BinTreeCondition8[examples_bstree_Node_key_0,
                                                   var_3_current_1,
                                                   x_0]
                )
              )
              and 
              (
                (
                  examples_bstree_BinTreeCondition2[exit_stmt_reached_2]
                  and 
                  (
                    (
                      examples_bstree_BinTreeCondition4[var_3_current_1]
                      and 
                      (
                        nullDerefBool_5=true)
                    )
                    or 
                    (
                      (
                        not (
                          examples_bstree_BinTreeCondition4[var_3_current_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_4=nullDerefBool_5)
                    )
                  )
                  and 
                  (
                    var_3_current_2=var_3_current_1.examples_bstree_Node_right_0)
                )
                or 
                (
                  (
                    not (
                      examples_bstree_BinTreeCondition2[exit_stmt_reached_2])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    var_3_current_1=var_3_current_2)
                  and 
                  (
                    nullDerefBool_4=nullDerefBool_5)
                )
              )
            )
          )
        )
        or 
        (
          (
            not (
              examples_bstree_BinTreeCondition2[exit_stmt_reached_2])
          )
          and 
          TruePred[]
          and 
          (
            var_3_current_1=var_3_current_2)
          and 
          (
            nullDerefBool_3=nullDerefBool_5)
        )
      )
      and 
      (
        (
          examples_bstree_BinTreeCondition2[exit_stmt_reached_2]
          and 
          (
            var_4_ws_2_2=(neq[var_3_current_2,
               null]=>(true)else(false))
          )
        )
        or 
        (
          (
            not (
              examples_bstree_BinTreeCondition2[exit_stmt_reached_2])
          )
          and 
          TruePred[]
          and 
          (
            var_4_ws_2_1=var_4_ws_2_2)
        )
      )
    )
    or 
    (
      TruePred[]
      and 
      (
        exit_stmt_reached_1=exit_stmt_reached_2)
      and 
      (
        var_3_current_1=var_3_current_2)
      and 
      (
        return_0=return_1)
      and 
      (
        nullDerefBool_2=nullDerefBool_5)
      and 
      (
        var_4_ws_2_1=var_4_ws_2_2)
    )
  )
  and 
  (
    (
      examples_bstree_BinTreeCondition10[exit_stmt_reached_2,
                                        var_4_ws_2_2]
      and 
      (
        (
          examples_bstree_BinTreeCondition2[exit_stmt_reached_2]
          and 
          (
            (
              examples_bstree_BinTreeCondition4[var_3_current_2]
              and 
              (
                nullDerefBool_6=true)
            )
            or 
            (
              (
                not (
                  examples_bstree_BinTreeCondition4[var_3_current_2])
              )
              and 
              TruePred[]
              and 
              (
                nullDerefBool_5=nullDerefBool_6)
            )
          )
          and 
          (
            (
              examples_bstree_BinTreeCondition6[examples_bstree_Node_key_0,
                                               var_3_current_2,
                                               x_0]
              and 
              (
                (
                  examples_bstree_BinTreeCondition2[exit_stmt_reached_2]
                  and 
                  (
                    return_2=true)
                  and 
                  (
                    exit_stmt_reached_3=true)
                )
                or 
                (
                  (
                    not (
                      examples_bstree_BinTreeCondition2[exit_stmt_reached_2])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    return_1=return_2)
                  and 
                  (
                    exit_stmt_reached_2=exit_stmt_reached_3)
                )
              )
            )
            or 
            (
              (
                not (
                  examples_bstree_BinTreeCondition6[examples_bstree_Node_key_0,
                                                   var_3_current_2,
                                                   x_0]
                )
              )
              and 
              TruePred[]
              and 
              (
                exit_stmt_reached_2=exit_stmt_reached_3)
              and 
              (
                return_1=return_2)
            )
          )
        )
        or 
        (
          (
            not (
              examples_bstree_BinTreeCondition2[exit_stmt_reached_2])
          )
          and 
          TruePred[]
          and 
          (
            return_1=return_2)
          and 
          (
            nullDerefBool_5=nullDerefBool_6)
          and 
          (
            exit_stmt_reached_2=exit_stmt_reached_3)
        )
      )
      and 
      (
        (
          examples_bstree_BinTreeCondition2[exit_stmt_reached_3]
          and 
          (
            (
              examples_bstree_BinTreeCondition4[var_3_current_2]
              and 
              (
                nullDerefBool_7=true)
            )
            or 
            (
              (
                not (
                  examples_bstree_BinTreeCondition4[var_3_current_2])
              )
              and 
              TruePred[]
              and 
              (
                nullDerefBool_6=nullDerefBool_7)
            )
          )
          and 
          (
            (
              examples_bstree_BinTreeCondition8[examples_bstree_Node_key_0,
                                               var_3_current_2,
                                               x_0]
              and 
              (
                (
                  examples_bstree_BinTreeCondition2[exit_stmt_reached_3]
                  and 
                  (
                    (
                      examples_bstree_BinTreeCondition4[var_3_current_2]
                      and 
                      (
                        nullDerefBool_8=true)
                    )
                    or 
                    (
                      (
                        not (
                          examples_bstree_BinTreeCondition4[var_3_current_2])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_7=nullDerefBool_8)
                    )
                  )
                  and 
                  (
                    var_3_current_3=var_3_current_2.examples_bstree_Node_left_0)
                )
                or 
                (
                  (
                    not (
                      examples_bstree_BinTreeCondition2[exit_stmt_reached_3])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    var_3_current_2=var_3_current_3)
                  and 
                  (
                    nullDerefBool_7=nullDerefBool_8)
                )
              )
            )
            or 
            (
              (
                not (
                  examples_bstree_BinTreeCondition8[examples_bstree_Node_key_0,
                                                   var_3_current_2,
                                                   x_0]
                )
              )
              and 
              (
                (
                  examples_bstree_BinTreeCondition2[exit_stmt_reached_3]
                  and 
                  (
                    (
                      examples_bstree_BinTreeCondition4[var_3_current_2]
                      and 
                      (
                        nullDerefBool_8=true)
                    )
                    or 
                    (
                      (
                        not (
                          examples_bstree_BinTreeCondition4[var_3_current_2])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_7=nullDerefBool_8)
                    )
                  )
                  and 
                  (
                    var_3_current_3=var_3_current_2.examples_bstree_Node_right_0)
                )
                or 
                (
                  (
                    not (
                      examples_bstree_BinTreeCondition2[exit_stmt_reached_3])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    var_3_current_2=var_3_current_3)
                  and 
                  (
                    nullDerefBool_7=nullDerefBool_8)
                )
              )
            )
          )
        )
        or 
        (
          (
            not (
              examples_bstree_BinTreeCondition2[exit_stmt_reached_3])
          )
          and 
          TruePred[]
          and 
          (
            var_3_current_2=var_3_current_3)
          and 
          (
            nullDerefBool_6=nullDerefBool_8)
        )
      )
      and 
      (
        (
          examples_bstree_BinTreeCondition2[exit_stmt_reached_3]
          and 
          (
            var_4_ws_2_3=(neq[var_3_current_3,
               null]=>(true)else(false))
          )
        )
        or 
        (
          (
            not (
              examples_bstree_BinTreeCondition2[exit_stmt_reached_3])
          )
          and 
          TruePred[]
          and 
          (
            var_4_ws_2_2=var_4_ws_2_3)
        )
      )
    )
    or 
    (
      TruePred[]
      and 
      (
        exit_stmt_reached_2=exit_stmt_reached_3)
      and 
      (
        var_3_current_2=var_3_current_3)
      and 
      (
        return_1=return_2)
      and 
      (
        nullDerefBool_5=nullDerefBool_8)
      and 
      (
        var_4_ws_2_2=var_4_ws_2_3)
    )
  )
  and 
  (
    (
      examples_bstree_BinTreeCondition10[exit_stmt_reached_3,
                                        var_4_ws_2_3]
      and 
      (
        (
          examples_bstree_BinTreeCondition2[exit_stmt_reached_3]
          and 
          (
            (
              examples_bstree_BinTreeCondition4[var_3_current_3]
              and 
              (
                nullDerefBool_9=true)
            )
            or 
            (
              (
                not (
                  examples_bstree_BinTreeCondition4[var_3_current_3])
              )
              and 
              TruePred[]
              and 
              (
                nullDerefBool_8=nullDerefBool_9)
            )
          )
          and 
          (
            (
              examples_bstree_BinTreeCondition6[examples_bstree_Node_key_0,
                                               var_3_current_3,
                                               x_0]
              and 
              (
                (
                  examples_bstree_BinTreeCondition2[exit_stmt_reached_3]
                  and 
                  (
                    return_3=true)
                  and 
                  (
                    exit_stmt_reached_4=true)
                )
                or 
                (
                  (
                    not (
                      examples_bstree_BinTreeCondition2[exit_stmt_reached_3])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    return_2=return_3)
                  and 
                  (
                    exit_stmt_reached_3=exit_stmt_reached_4)
                )
              )
            )
            or 
            (
              (
                not (
                  examples_bstree_BinTreeCondition6[examples_bstree_Node_key_0,
                                                   var_3_current_3,
                                                   x_0]
                )
              )
              and 
              TruePred[]
              and 
              (
                exit_stmt_reached_3=exit_stmt_reached_4)
              and 
              (
                return_2=return_3)
            )
          )
        )
        or 
        (
          (
            not (
              examples_bstree_BinTreeCondition2[exit_stmt_reached_3])
          )
          and 
          TruePred[]
          and 
          (
            return_2=return_3)
          and 
          (
            nullDerefBool_8=nullDerefBool_9)
          and 
          (
            exit_stmt_reached_3=exit_stmt_reached_4)
        )
      )
      and 
      (
        (
          examples_bstree_BinTreeCondition2[exit_stmt_reached_4]
          and 
          (
            (
              examples_bstree_BinTreeCondition4[var_3_current_3]
              and 
              (
                nullDerefBool_10=true)
            )
            or 
            (
              (
                not (
                  examples_bstree_BinTreeCondition4[var_3_current_3])
              )
              and 
              TruePred[]
              and 
              (
                nullDerefBool_9=nullDerefBool_10)
            )
          )
          and 
          (
            (
              examples_bstree_BinTreeCondition8[examples_bstree_Node_key_0,
                                               var_3_current_3,
                                               x_0]
              and 
              (
                (
                  examples_bstree_BinTreeCondition2[exit_stmt_reached_4]
                  and 
                  (
                    (
                      examples_bstree_BinTreeCondition4[var_3_current_3]
                      and 
                      (
                        nullDerefBool_11=true)
                    )
                    or 
                    (
                      (
                        not (
                          examples_bstree_BinTreeCondition4[var_3_current_3])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_10=nullDerefBool_11)
                    )
                  )
                  and 
                  (
                    var_3_current_4=var_3_current_3.examples_bstree_Node_left_0)
                )
                or 
                (
                  (
                    not (
                      examples_bstree_BinTreeCondition2[exit_stmt_reached_4])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    var_3_current_3=var_3_current_4)
                  and 
                  (
                    nullDerefBool_10=nullDerefBool_11)
                )
              )
            )
            or 
            (
              (
                not (
                  examples_bstree_BinTreeCondition8[examples_bstree_Node_key_0,
                                                   var_3_current_3,
                                                   x_0]
                )
              )
              and 
              (
                (
                  examples_bstree_BinTreeCondition2[exit_stmt_reached_4]
                  and 
                  (
                    (
                      examples_bstree_BinTreeCondition4[var_3_current_3]
                      and 
                      (
                        nullDerefBool_11=true)
                    )
                    or 
                    (
                      (
                        not (
                          examples_bstree_BinTreeCondition4[var_3_current_3])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_10=nullDerefBool_11)
                    )
                  )
                  and 
                  (
                    var_3_current_4=var_3_current_3.examples_bstree_Node_right_0)
                )
                or 
                (
                  (
                    not (
                      examples_bstree_BinTreeCondition2[exit_stmt_reached_4])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    var_3_current_3=var_3_current_4)
                  and 
                  (
                    nullDerefBool_10=nullDerefBool_11)
                )
              )
            )
          )
        )
        or 
        (
          (
            not (
              examples_bstree_BinTreeCondition2[exit_stmt_reached_4])
          )
          and 
          TruePred[]
          and 
          (
            var_3_current_3=var_3_current_4)
          and 
          (
            nullDerefBool_9=nullDerefBool_11)
        )
      )
      and 
      (
        (
          examples_bstree_BinTreeCondition2[exit_stmt_reached_4]
          and 
          (
            var_4_ws_2_4=(neq[var_3_current_4,
               null]=>(true)else(false))
          )
        )
        or 
        (
          (
            not (
              examples_bstree_BinTreeCondition2[exit_stmt_reached_4])
          )
          and 
          TruePred[]
          and 
          (
            var_4_ws_2_3=var_4_ws_2_4)
        )
      )
    )
    or 
    (
      TruePred[]
      and 
      (
        exit_stmt_reached_3=exit_stmt_reached_4)
      and 
      (
        var_3_current_3=var_3_current_4)
      and 
      (
        return_2=return_3)
      and 
      (
        nullDerefBool_8=nullDerefBool_11)
      and 
      (
        var_4_ws_2_3=var_4_ws_2_4)
    )
  )
  and 
  (
    (
      examples_bstree_BinTreeCondition10[exit_stmt_reached_4,
                                        var_4_ws_2_4]
      and 
      (
        (
          examples_bstree_BinTreeCondition2[exit_stmt_reached_4]
          and 
          (
            (
              examples_bstree_BinTreeCondition4[var_3_current_4]
              and 
              (
                nullDerefBool_12=true)
            )
            or 
            (
              (
                not (
                  examples_bstree_BinTreeCondition4[var_3_current_4])
              )
              and 
              TruePred[]
              and 
              (
                nullDerefBool_11=nullDerefBool_12)
            )
          )
          and 
          (
            (
              examples_bstree_BinTreeCondition6[examples_bstree_Node_key_0,
                                               var_3_current_4,
                                               x_0]
              and 
              (
                (
                  examples_bstree_BinTreeCondition2[exit_stmt_reached_4]
                  and 
                  (
                    return_4=true)
                  and 
                  (
                    exit_stmt_reached_5=true)
                )
                or 
                (
                  (
                    not (
                      examples_bstree_BinTreeCondition2[exit_stmt_reached_4])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    return_3=return_4)
                  and 
                  (
                    exit_stmt_reached_4=exit_stmt_reached_5)
                )
              )
            )
            or 
            (
              (
                not (
                  examples_bstree_BinTreeCondition6[examples_bstree_Node_key_0,
                                                   var_3_current_4,
                                                   x_0]
                )
              )
              and 
              TruePred[]
              and 
              (
                exit_stmt_reached_4=exit_stmt_reached_5)
              and 
              (
                return_3=return_4)
            )
          )
        )
        or 
        (
          (
            not (
              examples_bstree_BinTreeCondition2[exit_stmt_reached_4])
          )
          and 
          TruePred[]
          and 
          (
            return_3=return_4)
          and 
          (
            nullDerefBool_11=nullDerefBool_12)
          and 
          (
            exit_stmt_reached_4=exit_stmt_reached_5)
        )
      )
      and 
      (
        (
          examples_bstree_BinTreeCondition2[exit_stmt_reached_5]
          and 
          (
            (
              examples_bstree_BinTreeCondition4[var_3_current_4]
              and 
              (
                nullDerefBool_13=true)
            )
            or 
            (
              (
                not (
                  examples_bstree_BinTreeCondition4[var_3_current_4])
              )
              and 
              TruePred[]
              and 
              (
                nullDerefBool_12=nullDerefBool_13)
            )
          )
          and 
          (
            (
              examples_bstree_BinTreeCondition8[examples_bstree_Node_key_0,
                                               var_3_current_4,
                                               x_0]
              and 
              (
                (
                  examples_bstree_BinTreeCondition2[exit_stmt_reached_5]
                  and 
                  (
                    (
                      examples_bstree_BinTreeCondition4[var_3_current_4]
                      and 
                      (
                        nullDerefBool_14=true)
                    )
                    or 
                    (
                      (
                        not (
                          examples_bstree_BinTreeCondition4[var_3_current_4])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_13=nullDerefBool_14)
                    )
                  )
                  and 
                  (
                    var_3_current_5=var_3_current_4.examples_bstree_Node_left_0)
                )
                or 
                (
                  (
                    not (
                      examples_bstree_BinTreeCondition2[exit_stmt_reached_5])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    var_3_current_4=var_3_current_5)
                  and 
                  (
                    nullDerefBool_13=nullDerefBool_14)
                )
              )
            )
            or 
            (
              (
                not (
                  examples_bstree_BinTreeCondition8[examples_bstree_Node_key_0,
                                                   var_3_current_4,
                                                   x_0]
                )
              )
              and 
              (
                (
                  examples_bstree_BinTreeCondition2[exit_stmt_reached_5]
                  and 
                  (
                    (
                      examples_bstree_BinTreeCondition4[var_3_current_4]
                      and 
                      (
                        nullDerefBool_14=true)
                    )
                    or 
                    (
                      (
                        not (
                          examples_bstree_BinTreeCondition4[var_3_current_4])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_13=nullDerefBool_14)
                    )
                  )
                  and 
                  (
                    var_3_current_5=var_3_current_4.examples_bstree_Node_right_0)
                )
                or 
                (
                  (
                    not (
                      examples_bstree_BinTreeCondition2[exit_stmt_reached_5])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    var_3_current_4=var_3_current_5)
                  and 
                  (
                    nullDerefBool_13=nullDerefBool_14)
                )
              )
            )
          )
        )
        or 
        (
          (
            not (
              examples_bstree_BinTreeCondition2[exit_stmt_reached_5])
          )
          and 
          TruePred[]
          and 
          (
            var_3_current_4=var_3_current_5)
          and 
          (
            nullDerefBool_12=nullDerefBool_14)
        )
      )
      and 
      (
        (
          examples_bstree_BinTreeCondition2[exit_stmt_reached_5]
          and 
          (
            var_4_ws_2_5=(neq[var_3_current_5,
               null]=>(true)else(false))
          )
        )
        or 
        (
          (
            not (
              examples_bstree_BinTreeCondition2[exit_stmt_reached_5])
          )
          and 
          TruePred[]
          and 
          (
            var_4_ws_2_4=var_4_ws_2_5)
        )
      )
    )
    or 
    (
      TruePred[]
      and 
      (
        exit_stmt_reached_4=exit_stmt_reached_5)
      and 
      (
        var_3_current_4=var_3_current_5)
      and 
      (
        return_3=return_4)
      and 
      (
        nullDerefBool_11=nullDerefBool_14)
      and 
      (
        var_4_ws_2_4=var_4_ws_2_5)
    )
  )
  and 
  (
    (
      examples_bstree_BinTreeCondition10[exit_stmt_reached_5,
                                        var_4_ws_2_5]
      and 
      (
        (
          examples_bstree_BinTreeCondition2[exit_stmt_reached_5]
          and 
          (
            (
              examples_bstree_BinTreeCondition4[var_3_current_5]
              and 
              (
                nullDerefBool_15=true)
            )
            or 
            (
              (
                not (
                  examples_bstree_BinTreeCondition4[var_3_current_5])
              )
              and 
              TruePred[]
              and 
              (
                nullDerefBool_14=nullDerefBool_15)
            )
          )
          and 
          (
            (
              examples_bstree_BinTreeCondition6[examples_bstree_Node_key_0,
                                               var_3_current_5,
                                               x_0]
              and 
              (
                (
                  examples_bstree_BinTreeCondition2[exit_stmt_reached_5]
                  and 
                  (
                    return_5=true)
                  and 
                  (
                    exit_stmt_reached_6=true)
                )
                or 
                (
                  (
                    not (
                      examples_bstree_BinTreeCondition2[exit_stmt_reached_5])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    return_4=return_5)
                  and 
                  (
                    exit_stmt_reached_5=exit_stmt_reached_6)
                )
              )
            )
            or 
            (
              (
                not (
                  examples_bstree_BinTreeCondition6[examples_bstree_Node_key_0,
                                                   var_3_current_5,
                                                   x_0]
                )
              )
              and 
              TruePred[]
              and 
              (
                exit_stmt_reached_5=exit_stmt_reached_6)
              and 
              (
                return_4=return_5)
            )
          )
        )
        or 
        (
          (
            not (
              examples_bstree_BinTreeCondition2[exit_stmt_reached_5])
          )
          and 
          TruePred[]
          and 
          (
            return_4=return_5)
          and 
          (
            nullDerefBool_14=nullDerefBool_15)
          and 
          (
            exit_stmt_reached_5=exit_stmt_reached_6)
        )
      )
      and 
      (
        (
          examples_bstree_BinTreeCondition2[exit_stmt_reached_6]
          and 
          (
            (
              examples_bstree_BinTreeCondition4[var_3_current_5]
              and 
              (
                nullDerefBool_16=true)
            )
            or 
            (
              (
                not (
                  examples_bstree_BinTreeCondition4[var_3_current_5])
              )
              and 
              TruePred[]
              and 
              (
                nullDerefBool_15=nullDerefBool_16)
            )
          )
          and 
          (
            (
              examples_bstree_BinTreeCondition8[examples_bstree_Node_key_0,
                                               var_3_current_5,
                                               x_0]
              and 
              (
                (
                  examples_bstree_BinTreeCondition2[exit_stmt_reached_6]
                  and 
                  (
                    (
                      examples_bstree_BinTreeCondition4[var_3_current_5]
                      and 
                      (
                        nullDerefBool_17=true)
                    )
                    or 
                    (
                      (
                        not (
                          examples_bstree_BinTreeCondition4[var_3_current_5])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_16=nullDerefBool_17)
                    )
                  )
                  and 
                  (
                    var_3_current_6=var_3_current_5.examples_bstree_Node_left_0)
                )
                or 
                (
                  (
                    not (
                      examples_bstree_BinTreeCondition2[exit_stmt_reached_6])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    var_3_current_5=var_3_current_6)
                  and 
                  (
                    nullDerefBool_16=nullDerefBool_17)
                )
              )
            )
            or 
            (
              (
                not (
                  examples_bstree_BinTreeCondition8[examples_bstree_Node_key_0,
                                                   var_3_current_5,
                                                   x_0]
                )
              )
              and 
              (
                (
                  examples_bstree_BinTreeCondition2[exit_stmt_reached_6]
                  and 
                  (
                    (
                      examples_bstree_BinTreeCondition4[var_3_current_5]
                      and 
                      (
                        nullDerefBool_17=true)
                    )
                    or 
                    (
                      (
                        not (
                          examples_bstree_BinTreeCondition4[var_3_current_5])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_16=nullDerefBool_17)
                    )
                  )
                  and 
                  (
                    var_3_current_6=var_3_current_5.examples_bstree_Node_right_0)
                )
                or 
                (
                  (
                    not (
                      examples_bstree_BinTreeCondition2[exit_stmt_reached_6])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    var_3_current_5=var_3_current_6)
                  and 
                  (
                    nullDerefBool_16=nullDerefBool_17)
                )
              )
            )
          )
        )
        or 
        (
          (
            not (
              examples_bstree_BinTreeCondition2[exit_stmt_reached_6])
          )
          and 
          TruePred[]
          and 
          (
            var_3_current_5=var_3_current_6)
          and 
          (
            nullDerefBool_15=nullDerefBool_17)
        )
      )
      and 
      (
        (
          examples_bstree_BinTreeCondition2[exit_stmt_reached_6]
          and 
          (
            var_4_ws_2_6=(neq[var_3_current_6,
               null]=>(true)else(false))
          )
        )
        or 
        (
          (
            not (
              examples_bstree_BinTreeCondition2[exit_stmt_reached_6])
          )
          and 
          TruePred[]
          and 
          (
            var_4_ws_2_5=var_4_ws_2_6)
        )
      )
    )
    or 
    (
      TruePred[]
      and 
      (
        exit_stmt_reached_5=exit_stmt_reached_6)
      and 
      (
        var_3_current_5=var_3_current_6)
      and 
      (
        return_4=return_5)
      and 
      (
        nullDerefBool_14=nullDerefBool_17)
      and 
      (
        var_4_ws_2_5=var_4_ws_2_6)
    )
  )
  and 
  (
    (
      examples_bstree_BinTreeCondition10[exit_stmt_reached_6,
                                        var_4_ws_2_6]
      and 
      (
        (
          examples_bstree_BinTreeCondition2[exit_stmt_reached_6]
          and 
          (
            (
              examples_bstree_BinTreeCondition4[var_3_current_6]
              and 
              (
                nullDerefBool_18=true)
            )
            or 
            (
              (
                not (
                  examples_bstree_BinTreeCondition4[var_3_current_6])
              )
              and 
              TruePred[]
              and 
              (
                nullDerefBool_17=nullDerefBool_18)
            )
          )
          and 
          (
            (
              examples_bstree_BinTreeCondition6[examples_bstree_Node_key_0,
                                               var_3_current_6,
                                               x_0]
              and 
              (
                (
                  examples_bstree_BinTreeCondition2[exit_stmt_reached_6]
                  and 
                  (
                    return_6=true)
                  and 
                  (
                    exit_stmt_reached_7=true)
                )
                or 
                (
                  (
                    not (
                      examples_bstree_BinTreeCondition2[exit_stmt_reached_6])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    return_5=return_6)
                  and 
                  (
                    exit_stmt_reached_6=exit_stmt_reached_7)
                )
              )
            )
            or 
            (
              (
                not (
                  examples_bstree_BinTreeCondition6[examples_bstree_Node_key_0,
                                                   var_3_current_6,
                                                   x_0]
                )
              )
              and 
              TruePred[]
              and 
              (
                exit_stmt_reached_6=exit_stmt_reached_7)
              and 
              (
                return_5=return_6)
            )
          )
        )
        or 
        (
          (
            not (
              examples_bstree_BinTreeCondition2[exit_stmt_reached_6])
          )
          and 
          TruePred[]
          and 
          (
            return_5=return_6)
          and 
          (
            nullDerefBool_17=nullDerefBool_18)
          and 
          (
            exit_stmt_reached_6=exit_stmt_reached_7)
        )
      )
      and 
      (
        (
          examples_bstree_BinTreeCondition2[exit_stmt_reached_7]
          and 
          (
            (
              examples_bstree_BinTreeCondition4[var_3_current_6]
              and 
              (
                nullDerefBool_19=true)
            )
            or 
            (
              (
                not (
                  examples_bstree_BinTreeCondition4[var_3_current_6])
              )
              and 
              TruePred[]
              and 
              (
                nullDerefBool_18=nullDerefBool_19)
            )
          )
          and 
          (
            (
              examples_bstree_BinTreeCondition8[examples_bstree_Node_key_0,
                                               var_3_current_6,
                                               x_0]
              and 
              (
                (
                  examples_bstree_BinTreeCondition2[exit_stmt_reached_7]
                  and 
                  (
                    (
                      examples_bstree_BinTreeCondition4[var_3_current_6]
                      and 
                      (
                        nullDerefBool_20=true)
                    )
                    or 
                    (
                      (
                        not (
                          examples_bstree_BinTreeCondition4[var_3_current_6])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_19=nullDerefBool_20)
                    )
                  )
                  and 
                  (
                    var_3_current_7=var_3_current_6.examples_bstree_Node_left_0)
                )
                or 
                (
                  (
                    not (
                      examples_bstree_BinTreeCondition2[exit_stmt_reached_7])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    var_3_current_6=var_3_current_7)
                  and 
                  (
                    nullDerefBool_19=nullDerefBool_20)
                )
              )
            )
            or 
            (
              (
                not (
                  examples_bstree_BinTreeCondition8[examples_bstree_Node_key_0,
                                                   var_3_current_6,
                                                   x_0]
                )
              )
              and 
              (
                (
                  examples_bstree_BinTreeCondition2[exit_stmt_reached_7]
                  and 
                  (
                    (
                      examples_bstree_BinTreeCondition4[var_3_current_6]
                      and 
                      (
                        nullDerefBool_20=true)
                    )
                    or 
                    (
                      (
                        not (
                          examples_bstree_BinTreeCondition4[var_3_current_6])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_19=nullDerefBool_20)
                    )
                  )
                  and 
                  (
                    var_3_current_7=var_3_current_6.examples_bstree_Node_right_0)
                )
                or 
                (
                  (
                    not (
                      examples_bstree_BinTreeCondition2[exit_stmt_reached_7])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    var_3_current_6=var_3_current_7)
                  and 
                  (
                    nullDerefBool_19=nullDerefBool_20)
                )
              )
            )
          )
        )
        or 
        (
          (
            not (
              examples_bstree_BinTreeCondition2[exit_stmt_reached_7])
          )
          and 
          TruePred[]
          and 
          (
            var_3_current_6=var_3_current_7)
          and 
          (
            nullDerefBool_18=nullDerefBool_20)
        )
      )
      and 
      (
        (
          examples_bstree_BinTreeCondition2[exit_stmt_reached_7]
          and 
          (
            var_4_ws_2_7=(neq[var_3_current_7,
               null]=>(true)else(false))
          )
        )
        or 
        (
          (
            not (
              examples_bstree_BinTreeCondition2[exit_stmt_reached_7])
          )
          and 
          TruePred[]
          and 
          (
            var_4_ws_2_6=var_4_ws_2_7)
        )
      )
    )
    or 
    (
      TruePred[]
      and 
      (
        exit_stmt_reached_6=exit_stmt_reached_7)
      and 
      (
        var_3_current_6=var_3_current_7)
      and 
      (
        return_5=return_6)
      and 
      (
        nullDerefBool_17=nullDerefBool_20)
      and 
      (
        var_4_ws_2_6=var_4_ws_2_7)
    )
  )
  and 
  (
    (
      examples_bstree_BinTreeCondition10[exit_stmt_reached_7,
                                        var_4_ws_2_7]
      and 
      (
        (
          examples_bstree_BinTreeCondition2[exit_stmt_reached_7]
          and 
          (
            (
              examples_bstree_BinTreeCondition4[var_3_current_7]
              and 
              (
                nullDerefBool_21=true)
            )
            or 
            (
              (
                not (
                  examples_bstree_BinTreeCondition4[var_3_current_7])
              )
              and 
              TruePred[]
              and 
              (
                nullDerefBool_20=nullDerefBool_21)
            )
          )
          and 
          (
            (
              examples_bstree_BinTreeCondition6[examples_bstree_Node_key_0,
                                               var_3_current_7,
                                               x_0]
              and 
              (
                (
                  examples_bstree_BinTreeCondition2[exit_stmt_reached_7]
                  and 
                  (
                    return_7=true)
                  and 
                  (
                    exit_stmt_reached_8=true)
                )
                or 
                (
                  (
                    not (
                      examples_bstree_BinTreeCondition2[exit_stmt_reached_7])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    return_6=return_7)
                  and 
                  (
                    exit_stmt_reached_7=exit_stmt_reached_8)
                )
              )
            )
            or 
            (
              (
                not (
                  examples_bstree_BinTreeCondition6[examples_bstree_Node_key_0,
                                                   var_3_current_7,
                                                   x_0]
                )
              )
              and 
              TruePred[]
              and 
              (
                exit_stmt_reached_7=exit_stmt_reached_8)
              and 
              (
                return_6=return_7)
            )
          )
        )
        or 
        (
          (
            not (
              examples_bstree_BinTreeCondition2[exit_stmt_reached_7])
          )
          and 
          TruePred[]
          and 
          (
            return_6=return_7)
          and 
          (
            nullDerefBool_20=nullDerefBool_21)
          and 
          (
            exit_stmt_reached_7=exit_stmt_reached_8)
        )
      )
      and 
      (
        (
          examples_bstree_BinTreeCondition2[exit_stmt_reached_8]
          and 
          (
            (
              examples_bstree_BinTreeCondition4[var_3_current_7]
              and 
              (
                nullDerefBool_22=true)
            )
            or 
            (
              (
                not (
                  examples_bstree_BinTreeCondition4[var_3_current_7])
              )
              and 
              TruePred[]
              and 
              (
                nullDerefBool_21=nullDerefBool_22)
            )
          )
          and 
          (
            (
              examples_bstree_BinTreeCondition8[examples_bstree_Node_key_0,
                                               var_3_current_7,
                                               x_0]
              and 
              (
                (
                  examples_bstree_BinTreeCondition2[exit_stmt_reached_8]
                  and 
                  (
                    (
                      examples_bstree_BinTreeCondition4[var_3_current_7]
                      and 
                      (
                        nullDerefBool_23=true)
                    )
                    or 
                    (
                      (
                        not (
                          examples_bstree_BinTreeCondition4[var_3_current_7])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_22=nullDerefBool_23)
                    )
                  )
                  and 
                  (
                    var_3_current_8=var_3_current_7.examples_bstree_Node_left_0)
                )
                or 
                (
                  (
                    not (
                      examples_bstree_BinTreeCondition2[exit_stmt_reached_8])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    var_3_current_7=var_3_current_8)
                  and 
                  (
                    nullDerefBool_22=nullDerefBool_23)
                )
              )
            )
            or 
            (
              (
                not (
                  examples_bstree_BinTreeCondition8[examples_bstree_Node_key_0,
                                                   var_3_current_7,
                                                   x_0]
                )
              )
              and 
              (
                (
                  examples_bstree_BinTreeCondition2[exit_stmt_reached_8]
                  and 
                  (
                    (
                      examples_bstree_BinTreeCondition4[var_3_current_7]
                      and 
                      (
                        nullDerefBool_23=true)
                    )
                    or 
                    (
                      (
                        not (
                          examples_bstree_BinTreeCondition4[var_3_current_7])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_22=nullDerefBool_23)
                    )
                  )
                  and 
                  (
                    var_3_current_8=var_3_current_7.examples_bstree_Node_right_0)
                )
                or 
                (
                  (
                    not (
                      examples_bstree_BinTreeCondition2[exit_stmt_reached_8])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    var_3_current_7=var_3_current_8)
                  and 
                  (
                    nullDerefBool_22=nullDerefBool_23)
                )
              )
            )
          )
        )
        or 
        (
          (
            not (
              examples_bstree_BinTreeCondition2[exit_stmt_reached_8])
          )
          and 
          TruePred[]
          and 
          (
            var_3_current_7=var_3_current_8)
          and 
          (
            nullDerefBool_21=nullDerefBool_23)
        )
      )
      and 
      (
        (
          examples_bstree_BinTreeCondition2[exit_stmt_reached_8]
          and 
          (
            var_4_ws_2_8=(neq[var_3_current_8,
               null]=>(true)else(false))
          )
        )
        or 
        (
          (
            not (
              examples_bstree_BinTreeCondition2[exit_stmt_reached_8])
          )
          and 
          TruePred[]
          and 
          (
            var_4_ws_2_7=var_4_ws_2_8)
        )
      )
    )
    or 
    (
      TruePred[]
      and 
      (
        exit_stmt_reached_7=exit_stmt_reached_8)
      and 
      (
        var_3_current_7=var_3_current_8)
      and 
      (
        return_6=return_7)
      and 
      (
        nullDerefBool_20=nullDerefBool_23)
      and 
      (
        var_4_ws_2_7=var_4_ws_2_8)
    )
  )
  and 
  (
    (
      examples_bstree_BinTreeCondition10[exit_stmt_reached_8,
                                        var_4_ws_2_8]
      and 
      (
        (
          examples_bstree_BinTreeCondition2[exit_stmt_reached_8]
          and 
          (
            (
              examples_bstree_BinTreeCondition4[var_3_current_8]
              and 
              (
                nullDerefBool_24=true)
            )
            or 
            (
              (
                not (
                  examples_bstree_BinTreeCondition4[var_3_current_8])
              )
              and 
              TruePred[]
              and 
              (
                nullDerefBool_23=nullDerefBool_24)
            )
          )
          and 
          (
            (
              examples_bstree_BinTreeCondition6[examples_bstree_Node_key_0,
                                               var_3_current_8,
                                               x_0]
              and 
              (
                (
                  examples_bstree_BinTreeCondition2[exit_stmt_reached_8]
                  and 
                  (
                    return_8=true)
                  and 
                  (
                    exit_stmt_reached_9=true)
                )
                or 
                (
                  (
                    not (
                      examples_bstree_BinTreeCondition2[exit_stmt_reached_8])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    return_7=return_8)
                  and 
                  (
                    exit_stmt_reached_8=exit_stmt_reached_9)
                )
              )
            )
            or 
            (
              (
                not (
                  examples_bstree_BinTreeCondition6[examples_bstree_Node_key_0,
                                                   var_3_current_8,
                                                   x_0]
                )
              )
              and 
              TruePred[]
              and 
              (
                exit_stmt_reached_8=exit_stmt_reached_9)
              and 
              (
                return_7=return_8)
            )
          )
        )
        or 
        (
          (
            not (
              examples_bstree_BinTreeCondition2[exit_stmt_reached_8])
          )
          and 
          TruePred[]
          and 
          (
            return_7=return_8)
          and 
          (
            nullDerefBool_23=nullDerefBool_24)
          and 
          (
            exit_stmt_reached_8=exit_stmt_reached_9)
        )
      )
      and 
      (
        (
          examples_bstree_BinTreeCondition2[exit_stmt_reached_9]
          and 
          (
            (
              examples_bstree_BinTreeCondition4[var_3_current_8]
              and 
              (
                nullDerefBool_25=true)
            )
            or 
            (
              (
                not (
                  examples_bstree_BinTreeCondition4[var_3_current_8])
              )
              and 
              TruePred[]
              and 
              (
                nullDerefBool_24=nullDerefBool_25)
            )
          )
          and 
          (
            (
              examples_bstree_BinTreeCondition8[examples_bstree_Node_key_0,
                                               var_3_current_8,
                                               x_0]
              and 
              (
                (
                  examples_bstree_BinTreeCondition2[exit_stmt_reached_9]
                  and 
                  (
                    (
                      examples_bstree_BinTreeCondition4[var_3_current_8]
                      and 
                      (
                        nullDerefBool_26=true)
                    )
                    or 
                    (
                      (
                        not (
                          examples_bstree_BinTreeCondition4[var_3_current_8])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_25=nullDerefBool_26)
                    )
                  )
                  and 
                  (
                    var_3_current_9=var_3_current_8.examples_bstree_Node_left_0)
                )
                or 
                (
                  (
                    not (
                      examples_bstree_BinTreeCondition2[exit_stmt_reached_9])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    var_3_current_8=var_3_current_9)
                  and 
                  (
                    nullDerefBool_25=nullDerefBool_26)
                )
              )
            )
            or 
            (
              (
                not (
                  examples_bstree_BinTreeCondition8[examples_bstree_Node_key_0,
                                                   var_3_current_8,
                                                   x_0]
                )
              )
              and 
              (
                (
                  examples_bstree_BinTreeCondition2[exit_stmt_reached_9]
                  and 
                  (
                    (
                      examples_bstree_BinTreeCondition4[var_3_current_8]
                      and 
                      (
                        nullDerefBool_26=true)
                    )
                    or 
                    (
                      (
                        not (
                          examples_bstree_BinTreeCondition4[var_3_current_8])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_25=nullDerefBool_26)
                    )
                  )
                  and 
                  (
                    var_3_current_9=var_3_current_8.examples_bstree_Node_right_0)
                )
                or 
                (
                  (
                    not (
                      examples_bstree_BinTreeCondition2[exit_stmt_reached_9])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    var_3_current_8=var_3_current_9)
                  and 
                  (
                    nullDerefBool_25=nullDerefBool_26)
                )
              )
            )
          )
        )
        or 
        (
          (
            not (
              examples_bstree_BinTreeCondition2[exit_stmt_reached_9])
          )
          and 
          TruePred[]
          and 
          (
            var_3_current_8=var_3_current_9)
          and 
          (
            nullDerefBool_24=nullDerefBool_26)
        )
      )
      and 
      (
        (
          examples_bstree_BinTreeCondition2[exit_stmt_reached_9]
          and 
          (
            var_4_ws_2_9=(neq[var_3_current_9,
               null]=>(true)else(false))
          )
        )
        or 
        (
          (
            not (
              examples_bstree_BinTreeCondition2[exit_stmt_reached_9])
          )
          and 
          TruePred[]
          and 
          (
            var_4_ws_2_8=var_4_ws_2_9)
        )
      )
    )
    or 
    (
      TruePred[]
      and 
      (
        exit_stmt_reached_8=exit_stmt_reached_9)
      and 
      (
        var_3_current_8=var_3_current_9)
      and 
      (
        return_7=return_8)
      and 
      (
        nullDerefBool_23=nullDerefBool_26)
      and 
      (
        var_4_ws_2_8=var_4_ws_2_9)
    )
  )
  and 
  (
    (
      examples_bstree_BinTreeCondition10[exit_stmt_reached_9,
                                        var_4_ws_2_9]
      and 
      (
        (
          examples_bstree_BinTreeCondition2[exit_stmt_reached_9]
          and 
          (
            (
              examples_bstree_BinTreeCondition4[var_3_current_9]
              and 
              (
                nullDerefBool_27=true)
            )
            or 
            (
              (
                not (
                  examples_bstree_BinTreeCondition4[var_3_current_9])
              )
              and 
              TruePred[]
              and 
              (
                nullDerefBool_26=nullDerefBool_27)
            )
          )
          and 
          (
            (
              examples_bstree_BinTreeCondition6[examples_bstree_Node_key_0,
                                               var_3_current_9,
                                               x_0]
              and 
              (
                (
                  examples_bstree_BinTreeCondition2[exit_stmt_reached_9]
                  and 
                  (
                    return_9=true)
                  and 
                  (
                    exit_stmt_reached_10=true)
                )
                or 
                (
                  (
                    not (
                      examples_bstree_BinTreeCondition2[exit_stmt_reached_9])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    return_8=return_9)
                  and 
                  (
                    exit_stmt_reached_9=exit_stmt_reached_10)
                )
              )
            )
            or 
            (
              (
                not (
                  examples_bstree_BinTreeCondition6[examples_bstree_Node_key_0,
                                                   var_3_current_9,
                                                   x_0]
                )
              )
              and 
              TruePred[]
              and 
              (
                exit_stmt_reached_9=exit_stmt_reached_10)
              and 
              (
                return_8=return_9)
            )
          )
        )
        or 
        (
          (
            not (
              examples_bstree_BinTreeCondition2[exit_stmt_reached_9])
          )
          and 
          TruePred[]
          and 
          (
            return_8=return_9)
          and 
          (
            nullDerefBool_26=nullDerefBool_27)
          and 
          (
            exit_stmt_reached_9=exit_stmt_reached_10)
        )
      )
      and 
      (
        (
          examples_bstree_BinTreeCondition2[exit_stmt_reached_10]
          and 
          (
            (
              examples_bstree_BinTreeCondition4[var_3_current_9]
              and 
              (
                nullDerefBool_28=true)
            )
            or 
            (
              (
                not (
                  examples_bstree_BinTreeCondition4[var_3_current_9])
              )
              and 
              TruePred[]
              and 
              (
                nullDerefBool_27=nullDerefBool_28)
            )
          )
          and 
          (
            (
              examples_bstree_BinTreeCondition8[examples_bstree_Node_key_0,
                                               var_3_current_9,
                                               x_0]
              and 
              (
                (
                  examples_bstree_BinTreeCondition2[exit_stmt_reached_10]
                  and 
                  (
                    (
                      examples_bstree_BinTreeCondition4[var_3_current_9]
                      and 
                      (
                        nullDerefBool_29=true)
                    )
                    or 
                    (
                      (
                        not (
                          examples_bstree_BinTreeCondition4[var_3_current_9])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_28=nullDerefBool_29)
                    )
                  )
                  and 
                  (
                    var_3_current_10=var_3_current_9.examples_bstree_Node_left_0)
                )
                or 
                (
                  (
                    not (
                      examples_bstree_BinTreeCondition2[exit_stmt_reached_10])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    var_3_current_9=var_3_current_10)
                  and 
                  (
                    nullDerefBool_28=nullDerefBool_29)
                )
              )
            )
            or 
            (
              (
                not (
                  examples_bstree_BinTreeCondition8[examples_bstree_Node_key_0,
                                                   var_3_current_9,
                                                   x_0]
                )
              )
              and 
              (
                (
                  examples_bstree_BinTreeCondition2[exit_stmt_reached_10]
                  and 
                  (
                    (
                      examples_bstree_BinTreeCondition4[var_3_current_9]
                      and 
                      (
                        nullDerefBool_29=true)
                    )
                    or 
                    (
                      (
                        not (
                          examples_bstree_BinTreeCondition4[var_3_current_9])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_28=nullDerefBool_29)
                    )
                  )
                  and 
                  (
                    var_3_current_10=var_3_current_9.examples_bstree_Node_right_0)
                )
                or 
                (
                  (
                    not (
                      examples_bstree_BinTreeCondition2[exit_stmt_reached_10])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    var_3_current_9=var_3_current_10)
                  and 
                  (
                    nullDerefBool_28=nullDerefBool_29)
                )
              )
            )
          )
        )
        or 
        (
          (
            not (
              examples_bstree_BinTreeCondition2[exit_stmt_reached_10])
          )
          and 
          TruePred[]
          and 
          (
            var_3_current_9=var_3_current_10)
          and 
          (
            nullDerefBool_27=nullDerefBool_29)
        )
      )
      and 
      (
        (
          examples_bstree_BinTreeCondition2[exit_stmt_reached_10]
          and 
          (
            var_4_ws_2_10=(neq[var_3_current_10,
               null]=>(true)else(false))
          )
        )
        or 
        (
          (
            not (
              examples_bstree_BinTreeCondition2[exit_stmt_reached_10])
          )
          and 
          TruePred[]
          and 
          (
            var_4_ws_2_9=var_4_ws_2_10)
        )
      )
    )
    or 
    (
      TruePred[]
      and 
      (
        exit_stmt_reached_9=exit_stmt_reached_10)
      and 
      (
        var_3_current_9=var_3_current_10)
      and 
      (
        return_8=return_9)
      and 
      (
        nullDerefBool_26=nullDerefBool_29)
      and 
      (
        var_4_ws_2_9=var_4_ws_2_10)
    )
  )
  and 
  (
    (
      examples_bstree_BinTreeCondition10[exit_stmt_reached_10,
                                        var_4_ws_2_10]
      and 
      (
        (
          examples_bstree_BinTreeCondition2[exit_stmt_reached_10]
          and 
          (
            (
              examples_bstree_BinTreeCondition4[var_3_current_10]
              and 
              (
                nullDerefBool_30=true)
            )
            or 
            (
              (
                not (
                  examples_bstree_BinTreeCondition4[var_3_current_10])
              )
              and 
              TruePred[]
              and 
              (
                nullDerefBool_29=nullDerefBool_30)
            )
          )
          and 
          (
            (
              examples_bstree_BinTreeCondition6[examples_bstree_Node_key_0,
                                               var_3_current_10,
                                               x_0]
              and 
              (
                (
                  examples_bstree_BinTreeCondition2[exit_stmt_reached_10]
                  and 
                  (
                    return_10=true)
                  and 
                  (
                    exit_stmt_reached_11=true)
                )
                or 
                (
                  (
                    not (
                      examples_bstree_BinTreeCondition2[exit_stmt_reached_10])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    return_9=return_10)
                  and 
                  (
                    exit_stmt_reached_10=exit_stmt_reached_11)
                )
              )
            )
            or 
            (
              (
                not (
                  examples_bstree_BinTreeCondition6[examples_bstree_Node_key_0,
                                                   var_3_current_10,
                                                   x_0]
                )
              )
              and 
              TruePred[]
              and 
              (
                exit_stmt_reached_10=exit_stmt_reached_11)
              and 
              (
                return_9=return_10)
            )
          )
        )
        or 
        (
          (
            not (
              examples_bstree_BinTreeCondition2[exit_stmt_reached_10])
          )
          and 
          TruePred[]
          and 
          (
            return_9=return_10)
          and 
          (
            nullDerefBool_29=nullDerefBool_30)
          and 
          (
            exit_stmt_reached_10=exit_stmt_reached_11)
        )
      )
      and 
      (
        (
          examples_bstree_BinTreeCondition2[exit_stmt_reached_11]
          and 
          (
            (
              examples_bstree_BinTreeCondition4[var_3_current_10]
              and 
              (
                nullDerefBool_31=true)
            )
            or 
            (
              (
                not (
                  examples_bstree_BinTreeCondition4[var_3_current_10])
              )
              and 
              TruePred[]
              and 
              (
                nullDerefBool_30=nullDerefBool_31)
            )
          )
          and 
          (
            (
              examples_bstree_BinTreeCondition8[examples_bstree_Node_key_0,
                                               var_3_current_10,
                                               x_0]
              and 
              (
                (
                  examples_bstree_BinTreeCondition2[exit_stmt_reached_11]
                  and 
                  (
                    (
                      examples_bstree_BinTreeCondition4[var_3_current_10]
                      and 
                      (
                        nullDerefBool_32=true)
                    )
                    or 
                    (
                      (
                        not (
                          examples_bstree_BinTreeCondition4[var_3_current_10])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_31=nullDerefBool_32)
                    )
                  )
                  and 
                  (
                    var_3_current_11=var_3_current_10.examples_bstree_Node_left_0)
                )
                or 
                (
                  (
                    not (
                      examples_bstree_BinTreeCondition2[exit_stmt_reached_11])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    var_3_current_10=var_3_current_11)
                  and 
                  (
                    nullDerefBool_31=nullDerefBool_32)
                )
              )
            )
            or 
            (
              (
                not (
                  examples_bstree_BinTreeCondition8[examples_bstree_Node_key_0,
                                                   var_3_current_10,
                                                   x_0]
                )
              )
              and 
              (
                (
                  examples_bstree_BinTreeCondition2[exit_stmt_reached_11]
                  and 
                  (
                    (
                      examples_bstree_BinTreeCondition4[var_3_current_10]
                      and 
                      (
                        nullDerefBool_32=true)
                    )
                    or 
                    (
                      (
                        not (
                          examples_bstree_BinTreeCondition4[var_3_current_10])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_31=nullDerefBool_32)
                    )
                  )
                  and 
                  (
                    var_3_current_11=var_3_current_10.examples_bstree_Node_right_0)
                )
                or 
                (
                  (
                    not (
                      examples_bstree_BinTreeCondition2[exit_stmt_reached_11])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    var_3_current_10=var_3_current_11)
                  and 
                  (
                    nullDerefBool_31=nullDerefBool_32)
                )
              )
            )
          )
        )
        or 
        (
          (
            not (
              examples_bstree_BinTreeCondition2[exit_stmt_reached_11])
          )
          and 
          TruePred[]
          and 
          (
            var_3_current_10=var_3_current_11)
          and 
          (
            nullDerefBool_30=nullDerefBool_32)
        )
      )
      and 
      (
        (
          examples_bstree_BinTreeCondition2[exit_stmt_reached_11]
          and 
          (
            var_4_ws_2_11=(neq[var_3_current_11,
               null]=>(true)else(false))
          )
        )
        or 
        (
          (
            not (
              examples_bstree_BinTreeCondition2[exit_stmt_reached_11])
          )
          and 
          TruePred[]
          and 
          (
            var_4_ws_2_10=var_4_ws_2_11)
        )
      )
    )
    or 
    (
      TruePred[]
      and 
      (
        exit_stmt_reached_10=exit_stmt_reached_11)
      and 
      (
        var_3_current_10=var_3_current_11)
      and 
      (
        return_9=return_10)
      and 
      (
        nullDerefBool_29=nullDerefBool_32)
      and 
      (
        var_4_ws_2_10=var_4_ws_2_11)
    )
  )
  and 
  examples_bstree_BinTreeCondition11[exit_stmt_reached_11,
                                    var_4_ws_2_11]
  and 
  (
    (
      examples_bstree_BinTreeCondition2[exit_stmt_reached_11]
      and 
      (
        return_11=false)
      and 
      (
        exit_stmt_reached_12=true)
    )
    or 
    (
      (
        not (
          examples_bstree_BinTreeCondition2[exit_stmt_reached_11])
      )
      and 
      TruePred[]
      and 
      (
        return_10=return_11)
      and 
      (
        exit_stmt_reached_11=exit_stmt_reached_12)
    )
  )
  and 
  (
    (
      examples_bstree_BinTreeCondition12[nullDerefBool_32,
                                        throw_1]
      and 
      (
        throw_2=java_lang_NullPointerExceptionLit)
    )
    or 
    (
      (
        not (
          examples_bstree_BinTreeCondition12[nullDerefBool_32,
                                            throw_1]
        )
      )
      and 
      TruePred[]
      and 
      (
        throw_1=throw_2)
    )
  )

}

one sig QF {
  examples_bstree_BinTree_root_0: ( examples_bstree_BinTree ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_key_0: ( examples_bstree_Node ) -> one ( Int ),
  bexamples_bstree_Node_left_0,fexamples_bstree_Node_left_0: ( examples_bstree_Node ) -> lone ( examples_bstree_Node + null ),
  bexamples_bstree_Node_right_0,fexamples_bstree_Node_right_0: ( examples_bstree_Node ) -> lone ( examples_bstree_Node + null ),
  l1_exit_stmt_reached_1: boolean,
  l1_exit_stmt_reached_10: boolean,
  l1_exit_stmt_reached_11: boolean,
  l1_exit_stmt_reached_12: boolean,
  l1_exit_stmt_reached_2: boolean,
  l1_exit_stmt_reached_3: boolean,
  l1_exit_stmt_reached_4: boolean,
  l1_exit_stmt_reached_5: boolean,
  l1_exit_stmt_reached_6: boolean,
  l1_exit_stmt_reached_7: boolean,
  l1_exit_stmt_reached_8: boolean,
  l1_exit_stmt_reached_9: boolean,
  l1_nullDerefBool_1: boolean,
  l1_nullDerefBool_10: boolean,
  l1_nullDerefBool_11: boolean,
  l1_nullDerefBool_12: boolean,
  l1_nullDerefBool_13: boolean,
  l1_nullDerefBool_14: boolean,
  l1_nullDerefBool_15: boolean,
  l1_nullDerefBool_16: boolean,
  l1_nullDerefBool_17: boolean,
  l1_nullDerefBool_18: boolean,
  l1_nullDerefBool_19: boolean,
  l1_nullDerefBool_2: boolean,
  l1_nullDerefBool_20: boolean,
  l1_nullDerefBool_21: boolean,
  l1_nullDerefBool_22: boolean,
  l1_nullDerefBool_23: boolean,
  l1_nullDerefBool_24: boolean,
  l1_nullDerefBool_25: boolean,
  l1_nullDerefBool_26: boolean,
  l1_nullDerefBool_27: boolean,
  l1_nullDerefBool_28: boolean,
  l1_nullDerefBool_29: boolean,
  l1_nullDerefBool_3: boolean,
  l1_nullDerefBool_30: boolean,
  l1_nullDerefBool_31: boolean,
  l1_nullDerefBool_32: boolean,
  l1_nullDerefBool_4: boolean,
  l1_nullDerefBool_5: boolean,
  l1_nullDerefBool_6: boolean,
  l1_nullDerefBool_7: boolean,
  l1_nullDerefBool_8: boolean,
  l1_nullDerefBool_9: boolean,
  l1_var_3_current_0: examples_bstree_Node + null,
  l1_var_3_current_1: examples_bstree_Node + null,
  l1_var_3_current_10: examples_bstree_Node + null,
  l1_var_3_current_11: examples_bstree_Node + null,
  l1_var_3_current_2: examples_bstree_Node + null,
  l1_var_3_current_3: examples_bstree_Node + null,
  l1_var_3_current_4: examples_bstree_Node + null,
  l1_var_3_current_5: examples_bstree_Node + null,
  l1_var_3_current_6: examples_bstree_Node + null,
  l1_var_3_current_7: examples_bstree_Node + null,
  l1_var_3_current_8: examples_bstree_Node + null,
  l1_var_3_current_9: examples_bstree_Node + null,
  l1_var_4_ws_2_0: boolean,
  l1_var_4_ws_2_1: boolean,
  l1_var_4_ws_2_10: boolean,
  l1_var_4_ws_2_11: boolean,
  l1_var_4_ws_2_2: boolean,
  l1_var_4_ws_2_3: boolean,
  l1_var_4_ws_2_4: boolean,
  l1_var_4_ws_2_5: boolean,
  l1_var_4_ws_2_6: boolean,
  l1_var_4_ws_2_7: boolean,
  l1_var_4_ws_2_8: boolean,
  l1_var_4_ws_2_9: boolean,
  nodes_0: ( examples_bstree_BinTree ) -> ( examples_bstree_Node ),
  return_0: boolean,
  return_1: boolean,
  return_10: boolean,
  return_11: boolean,
  return_2: boolean,
  return_3: boolean,
  return_4: boolean,
  return_5: boolean,
  return_6: boolean,
  return_7: boolean,
  return_8: boolean,
  return_9: boolean,
  thiz_0: examples_bstree_BinTree,
  throw_0: java_lang_Throwable + null,
  throw_1: java_lang_Throwable + null,
  throw_2: java_lang_Throwable + null,
  x_0: Int
}


fact {
  precondition_examples_bstree_BinTree_find_0[QF.examples_bstree_BinTree_root_0,
                                             QF.examples_bstree_Node_key_0,
                                             (QF.fexamples_bstree_Node_left_0+QF.bexamples_bstree_Node_left_0),
                                             (QF.fexamples_bstree_Node_right_0+QF.bexamples_bstree_Node_right_0),
                                             QF.nodes_0,
                                             QF.thiz_0,
                                             QF.throw_0]

}

fact {
  examples_bstree_BinTree_find_0[QF.thiz_0,
                                QF.throw_1,
                                QF.throw_2,
                                QF.return_0,
                                QF.return_1,
                                QF.return_2,
                                QF.return_3,
                                QF.return_4,
                                QF.return_5,
                                QF.return_6,
                                QF.return_7,
                                QF.return_8,
                                QF.return_9,
                                QF.return_10,
                                QF.return_11,
                                QF.x_0,
                                (QF.fexamples_bstree_Node_right_0+QF.bexamples_bstree_Node_right_0),
                                QF.examples_bstree_Node_key_0,
                                QF.examples_bstree_BinTree_root_0,
                                (QF.fexamples_bstree_Node_left_0+QF.bexamples_bstree_Node_left_0),
                                QF.l1_exit_stmt_reached_1,
                                QF.l1_exit_stmt_reached_2,
                                QF.l1_exit_stmt_reached_3,
                                QF.l1_exit_stmt_reached_4,
                                QF.l1_exit_stmt_reached_5,
                                QF.l1_exit_stmt_reached_6,
                                QF.l1_exit_stmt_reached_7,
                                QF.l1_exit_stmt_reached_8,
                                QF.l1_exit_stmt_reached_9,
                                QF.l1_exit_stmt_reached_10,
                                QF.l1_exit_stmt_reached_11,
                                QF.l1_exit_stmt_reached_12,
                                QF.l1_var_3_current_0,
                                QF.l1_var_3_current_1,
                                QF.l1_var_3_current_2,
                                QF.l1_var_3_current_3,
                                QF.l1_var_3_current_4,
                                QF.l1_var_3_current_5,
                                QF.l1_var_3_current_6,
                                QF.l1_var_3_current_7,
                                QF.l1_var_3_current_8,
                                QF.l1_var_3_current_9,
                                QF.l1_var_3_current_10,
                                QF.l1_var_3_current_11,
                                QF.l1_nullDerefBool_1,
                                QF.l1_nullDerefBool_2,
                                QF.l1_nullDerefBool_3,
                                QF.l1_nullDerefBool_4,
                                QF.l1_nullDerefBool_5,
                                QF.l1_nullDerefBool_6,
                                QF.l1_nullDerefBool_7,
                                QF.l1_nullDerefBool_8,
                                QF.l1_nullDerefBool_9,
                                QF.l1_nullDerefBool_10,
                                QF.l1_nullDerefBool_11,
                                QF.l1_nullDerefBool_12,
                                QF.l1_nullDerefBool_13,
                                QF.l1_nullDerefBool_14,
                                QF.l1_nullDerefBool_15,
                                QF.l1_nullDerefBool_16,
                                QF.l1_nullDerefBool_17,
                                QF.l1_nullDerefBool_18,
                                QF.l1_nullDerefBool_19,
                                QF.l1_nullDerefBool_20,
                                QF.l1_nullDerefBool_21,
                                QF.l1_nullDerefBool_22,
                                QF.l1_nullDerefBool_23,
                                QF.l1_nullDerefBool_24,
                                QF.l1_nullDerefBool_25,
                                QF.l1_nullDerefBool_26,
                                QF.l1_nullDerefBool_27,
                                QF.l1_nullDerefBool_28,
                                QF.l1_nullDerefBool_29,
                                QF.l1_nullDerefBool_30,
                                QF.l1_nullDerefBool_31,
                                QF.l1_nullDerefBool_32,
                                QF.l1_var_4_ws_2_0,
                                QF.l1_var_4_ws_2_1,
                                QF.l1_var_4_ws_2_2,
                                QF.l1_var_4_ws_2_3,
                                QF.l1_var_4_ws_2_4,
                                QF.l1_var_4_ws_2_5,
                                QF.l1_var_4_ws_2_6,
                                QF.l1_var_4_ws_2_7,
                                QF.l1_var_4_ws_2_8,
                                QF.l1_var_4_ws_2_9,
                                QF.l1_var_4_ws_2_10,
                                QF.l1_var_4_ws_2_11]

}

assert BSTree_m1{
  postcondition_examples_bstree_BinTree_find_0[QF.examples_bstree_Node_key_0,
                                              QF.nodes_0,
                                              QF.return_11,
                                              QF.thiz_0,
                                              QF.throw_2,
                                              QF.x_0]
}
check BSTree_m1 for 0 but 
                 exactly 1 examples_bstree_BinTree, 
                 exactly 17 examples_bstree_Node,
                 6 int  



one sig N0,N1,N2,N3,N4,N5,N6,N7,N8,N9,N10,N11,N12,N13,N14,N15,N16 extends examples_bstree_Node {}
fun node_next[]: (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16) -> lone (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16)  
{ 
  N0->N1 
  + 
  N1->N2 
  + 
  N2->N3 
  + 
  N3->N4 
  + 
  N4->N5 
  + 
  N5->N6 
  + 
  N6->N7 
  + 
  N7->N8 
  + 
  N8->N9 
  + 
  N9->N10 
  + 
  N10->N11 
  + 
  N11->N12 
  + 
  N12->N13 
  + 
  N13->N14 
  + 
  N14->N15 
  + 
  N15->N16 
} 
fun node_prevs[e: N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16] :set (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16) 
{ 
 e.( 
   N1 -> ( N0 ) 
   + 
   N2 -> ( N0+N1 ) 
   + 
   N3 -> ( N0+N1+N2 ) 
   + 
   N4 -> ( N0+N1+N2+N3 ) 
   + 
   N5 -> ( N0+N1+N2+N3+N4 ) 
   + 
   N6 -> ( N0+N1+N2+N3+N4+N5 ) 
   + 
   N7 -> ( N0+N1+N2+N3+N4+N5+N6 ) 
   + 
   N8 -> ( N0+N1+N2+N3+N4+N5+N6+N7 ) 
   + 
   N9 -> ( N0+N1+N2+N3+N4+N5+N6+N7+N8 ) 
   + 
   N10 -> ( N0+N1+N2+N3+N4+N5+N6+N7+N8+N9 ) 
   + 
   N11 -> ( N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10 ) 
   + 
   N12 -> ( N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11 ) 
   + 
   N13 -> ( N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12 ) 
   + 
   N14 -> ( N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13 ) 
   + 
   N15 -> ( N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14 ) 
   + 
   N16 -> ( N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15 ) 
 ) 
} 
































































































fun node_relprevs[] :( N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16 ) -> set ( N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16 ) 
{    N0 -> ( N0 ) 
   + 
   N1 -> ( N0+N1 ) 
   + 
   N2 -> ( N0+N1+N2 ) 
   + 
   N3 -> ( N0+N1+N2+N3 ) 
   + 
   N4 -> ( N0+N1+N2+N3+N4 ) 
   + 
   N5 -> ( N0+N1+N2+N3+N4+N5 ) 
   + 
   N6 -> ( N0+N1+N2+N3+N4+N5+N6 ) 
   + 
   N7 -> ( N0+N1+N2+N3+N4+N5+N6+N7 ) 
   + 
   N8 -> ( N0+N1+N2+N3+N4+N5+N6+N7+N8 ) 
   + 
   N9 -> ( N0+N1+N2+N3+N4+N5+N6+N7+N8+N9 ) 
   + 
   N10 -> ( N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10 ) 
   + 
   N11 -> ( N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11 ) 
   + 
   N12 -> ( N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12 ) 
   + 
   N13 -> ( N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13 ) 
   + 
   N14 -> ( N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14 ) 
   + 
   N15 -> ( N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15 ) 
   + 
   N16 -> ( N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16 ) 
} 
fun node_min [es: set ( N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16 )] : lone ( N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16 ) 
{ 
  es - es.( 
   N0 -> ( N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16 ) 
   + 
   N1 -> ( N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16 ) 
   + 
   N2 -> ( N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16 ) 
   + 
   N3 -> ( N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16 ) 
   + 
   N4 -> ( N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16 ) 
   + 
   N5 -> ( N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16 ) 
   + 
   N6 -> ( N7+N8+N9+N10+N11+N12+N13+N14+N15+N16 ) 
   + 
   N7 -> ( N8+N9+N10+N11+N12+N13+N14+N15+N16 ) 
   + 
   N8 -> ( N9+N10+N11+N12+N13+N14+N15+N16 ) 
   + 
   N9 -> ( N10+N11+N12+N13+N14+N15+N16 ) 
   + 
   N10 -> ( N11+N12+N13+N14+N15+N16 ) 
   + 
   N11 -> ( N12+N13+N14+N15+N16 ) 
   + 
   N12 -> ( N13+N14+N15+N16 ) 
   + 
   N13 -> ( N14+N15+N16 ) 
   + 
   N14 -> ( N15+N16 ) 
   + 
   N15 -> ( N16 ) 
  ) 
} 
fact { 
let entry=(QF.thiz_0).(QF.examples_bstree_BinTree_root_0),ff1=QF.fexamples_bstree_Node_left_0,ff2=QF.fexamples_bstree_Node_right_0,bf1=QF.bexamples_bstree_Node_left_0,bf2=QF.bexamples_bstree_Node_right_0 | { 
   -- forwardPlusBackwardAreFunctions 
   no ((ff1.univ) & (bf1.univ)) 
   no ((ff2.univ) & (bf2.univ)) 
   N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16 = ff1.univ + bf1.univ   
   N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16 = ff2.univ + bf2.univ   

  --forwardIsIndeedForward 
  entry in N0+null and 
  (all n : entry.*(ff1 + ff2) - null | ( 
   node_min[(ff1).n] in node_prevs[n]) and ( 
    node_min[(ff2).n] in node_prevs[n])) and 
  (all disj n1, n2 : entry.*((ff1) + (ff2)) - null | ( 
        (    some ((ff1).n1 + (ff2).n1) and 
            some ((ff1).n2 + (ff2).n2) and 
                node_min[(ff1).n1 + (ff2).n1] in node_prevs[node_min[(ff1).n2 + (ff2).n2]] 
             ) implies n1 in node_prevs[n2] 
   ) 
   and 
     let a = node_min[(ff1).n1 + (ff2).n1] | 
     let b = node_min[(ff1).n2 + (ff2).n2] | 
     (some ((ff1).n1 + (ff2).n1) and a = b and a.(ff1) = n1 and a.(ff2) = n2) implies n2 = n1.node_next[] 
   ) 

  --backwardsIsIndeedBackwards 
   (bf1 in node_relprevs) && (bf2 in node_relprevs) 

  --prefixReachableForward 
    all x : entry.*(ff1 +ff2) -null | node_prevs[x] in entry.*(ff1 + ff2) 

} 
} 
//fact ffields_bfields 
fact { 
QF.bexamples_bstree_Node_right_0 in none->none 
QF.bexamples_bstree_Node_left_0 in none->none 
QF.fexamples_bstree_Node_right_0 in N0->N1 
+N0->N2 
+N0->null 
+N1->N2 
+N1->N3 
+N1->N4 
+N1->null 
+N2->N3 
+N2->N4 
+N2->N5 
+N2->N6 
+N2->null 
+N3->N4 
+N3->N5 
+N3->N6 
+N3->N7 
+N3->N8 
+N3->null 
+N4->N5 
+N4->N6 
+N4->N7 
+N4->N8 
+N4->N9 
+N4->N10 
+N4->null 
+N5->N6 
+N5->N7 
+N5->N8 
+N5->N9 
+N5->N10 
+N5->N11 
+N5->N12 
+N5->null 
+N6->N7 
+N6->N8 
+N6->N9 
+N6->N10 
+N6->N11 
+N6->N12 
+N6->N13 
+N6->N14 
+N6->null 
+N7->N8 
+N7->N9 
+N7->N10 
+N7->N11 
+N7->N12 
+N7->N13 
+N7->N14 
+N7->N15 
+N7->N16 
+N7->null 
+N8->N9 
+N8->N10 
+N8->N11 
+N8->N12 
+N8->N13 
+N8->N14 
+N8->N15 
+N8->N16 
+N8->null 
+N9->N10 
+N9->N11 
+N9->N12 
+N9->N13 
+N9->N14 
+N9->N15 
+N9->N16 
+N9->null 
+N10->N11 
+N10->N12 
+N10->N13 
+N10->N14 
+N10->N15 
+N10->N16 
+N10->null 
+N11->N12 
+N11->N13 
+N11->N14 
+N11->N15 
+N11->N16 
+N11->null 
+N12->N13 
+N12->N14 
+N12->N15 
+N12->N16 
+N12->null 
+N13->N14 
+N13->N15 
+N13->N16 
+N13->null 
+N14->N15 
+N14->N16 
+N14->null 
+N15->N16 
+N15->null 
+N16->null 
 
QF.fexamples_bstree_Node_left_0 in N0->N1 
+N0->null 
+N1->N2 
+N1->N3 
+N1->null 
+N2->N3 
+N2->N4 
+N2->N5 
+N2->null 
+N3->N4 
+N3->N5 
+N3->N6 
+N3->N7 
+N3->null 
+N4->N5 
+N4->N6 
+N4->N7 
+N4->N8 
+N4->N9 
+N4->null 
+N5->N6 
+N5->N7 
+N5->N8 
+N5->N9 
+N5->N10 
+N5->N11 
+N5->null 
+N6->N7 
+N6->N8 
+N6->N9 
+N6->N10 
+N6->N11 
+N6->N12 
+N6->N13 
+N6->null 
+N7->N8 
+N7->N9 
+N7->N10 
+N7->N11 
+N7->N12 
+N7->N13 
+N7->N14 
+N7->N15 
+N7->null 
+N8->N9 
+N8->N10 
+N8->N11 
+N8->N12 
+N8->N13 
+N8->N14 
+N8->N15 
+N8->N16 
+N8->null 
+N9->N10 
+N9->N11 
+N9->N12 
+N9->N13 
+N9->N14 
+N9->N15 
+N9->N16 
+N9->null 
+N10->N11 
+N10->N12 
+N10->N13 
+N10->N14 
+N10->N15 
+N10->N16 
+N10->null 
+N11->N12 
+N11->N13 
+N11->N14 
+N11->N15 
+N11->N16 
+N11->null 
+N12->N13 
+N12->N14 
+N12->N15 
+N12->N16 
+N12->null 
+N13->N14 
+N13->N15 
+N13->N16 
+N13->null 
+N14->N15 
+N14->N16 
+N14->null 
+N15->N16 
+N15->null 
+N16->null 
 
} 
// fact int_fields 
fact { 
} 
//fact data_fields 
fact { 
QF.examples_bstree_Node_key_0 in N0->0 
+N0->1 
+N0->2 
+N0->3 
+N0->4 
+N0->5 
+N0->6 
+N0->7 
+N0->8 
+N0->9 
+N0->10 
+N0->11 
+N0->12 
+N0->13 
+N0->14 
+N0->15 
+N0->16 
+N1->0 
+N1->1 
+N1->2 
+N1->3 
+N1->4 
+N1->5 
+N1->6 
+N1->7 
+N1->8 
+N1->9 
+N1->10 
+N1->11 
+N1->12 
+N1->13 
+N1->14 
+N1->15 
+N1->16 
+N2->0 
+N2->1 
+N2->2 
+N2->3 
+N2->4 
+N2->5 
+N2->6 
+N2->7 
+N2->8 
+N2->9 
+N2->10 
+N2->11 
+N2->12 
+N2->13 
+N2->14 
+N2->15 
+N2->16 
+N3->0 
+N3->1 
+N3->2 
+N3->3 
+N3->4 
+N3->5 
+N3->6 
+N3->7 
+N3->8 
+N3->9 
+N3->10 
+N3->11 
+N3->12 
+N3->13 
+N3->14 
+N3->15 
+N3->16 
+N4->0 
+N4->1 
+N4->2 
+N4->3 
+N4->4 
+N4->5 
+N4->6 
+N4->7 
+N4->8 
+N4->9 
+N4->10 
+N4->11 
+N4->12 
+N4->13 
+N4->14 
+N4->15 
+N4->16 
+N5->0 
+N5->1 
+N5->2 
+N5->3 
+N5->4 
+N5->5 
+N5->6 
+N5->7 
+N5->8 
+N5->9 
+N5->10 
+N5->11 
+N5->12 
+N5->13 
+N5->14 
+N5->15 
+N5->16 
+N6->0 
+N6->1 
+N6->2 
+N6->3 
+N6->4 
+N6->5 
+N6->6 
+N6->7 
+N6->8 
+N6->9 
+N6->10 
+N6->11 
+N6->12 
+N6->13 
+N6->14 
+N6->15 
+N6->16 
+N7->0 
+N7->1 
+N7->2 
+N7->3 
+N7->4 
+N7->5 
+N7->6 
+N7->7 
+N7->8 
+N7->9 
+N7->10 
+N7->11 
+N7->12 
+N7->13 
+N7->14 
+N7->15 
+N7->16 
+N8->0 
+N8->1 
+N8->2 
+N8->3 
+N8->4 
+N8->5 
+N8->6 
+N8->7 
+N8->8 
+N8->9 
+N8->10 
+N8->11 
+N8->12 
+N8->13 
+N8->14 
+N8->15 
+N8->16 
+N9->0 
+N9->1 
+N9->2 
+N9->3 
+N9->4 
+N9->5 
+N9->6 
+N9->7 
+N9->8 
+N9->9 
+N9->10 
+N9->11 
+N9->12 
+N9->13 
+N9->14 
+N9->15 
+N9->16 
+N10->0 
+N10->1 
+N10->2 
+N10->3 
+N10->4 
+N10->5 
+N10->6 
+N10->7 
+N10->8 
+N10->9 
+N10->10 
+N10->11 
+N10->12 
+N10->13 
+N10->14 
+N10->15 
+N10->16 
+N11->0 
+N11->1 
+N11->2 
+N11->3 
+N11->4 
+N11->5 
+N11->6 
+N11->7 
+N11->8 
+N11->9 
+N11->10 
+N11->11 
+N11->12 
+N11->13 
+N11->14 
+N11->15 
+N11->16 
+N12->0 
+N12->1 
+N12->2 
+N12->3 
+N12->4 
+N12->5 
+N12->6 
+N12->7 
+N12->8 
+N12->9 
+N12->10 
+N12->11 
+N12->12 
+N12->13 
+N12->14 
+N12->15 
+N12->16 
+N13->0 
+N13->1 
+N13->2 
+N13->3 
+N13->4 
+N13->5 
+N13->6 
+N13->7 
+N13->8 
+N13->9 
+N13->10 
+N13->11 
+N13->12 
+N13->13 
+N13->14 
+N13->15 
+N13->16 
+N14->0 
+N14->1 
+N14->2 
+N14->3 
+N14->4 
+N14->5 
+N14->6 
+N14->7 
+N14->8 
+N14->9 
+N14->10 
+N14->11 
+N14->12 
+N14->13 
+N14->14 
+N14->15 
+N14->16 
+N15->0 
+N15->1 
+N15->2 
+N15->3 
+N15->4 
+N15->5 
+N15->6 
+N15->7 
+N15->8 
+N15->9 
+N15->10 
+N15->11 
+N15->12 
+N15->13 
+N15->14 
+N15->15 
+N15->16 
+N16->0 
+N16->1 
+N16->2 
+N16->3 
+N16->4 
+N16->5 
+N16->6 
+N16->7 
+N16->8 
+N16->9 
+N16->10 
+N16->11 
+N16->12 
+N16->13 
+N16->14 
+N16->15 
+N16->16 

} 
//fact root_int_fields 
fact { 
} 
//fact root_node_fields 
fact { 
} 



