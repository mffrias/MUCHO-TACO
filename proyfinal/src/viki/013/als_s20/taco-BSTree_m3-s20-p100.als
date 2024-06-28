/* 
 * DynAlloy translator options 
 * --------------------------- 
 * applySimplifications= true
 * assertionId= BSTree_m3
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




pred examples_bstree_NodeCondition2[
  exit_stmt_reached:univ
]{
   exit_stmt_reached=false

}

pred examples_bstree_NodeCondition0[
  thiz:univ
]{
   isEmptyOrNull[thiz]

}

pred examples_bstree_NodeCondition3[
  exit_stmt_reached:univ
]{
   not (
     exit_stmt_reached=false)

}

pred examples_bstree_NodeCondition1[
  thiz:univ
]{
   not (
     isEmptyOrNull[thiz])

}

pred examples_bstree_NodeCondition4[
  nullDerefBool:univ,
  throw:univ
]{
   equ[nullDerefBool,
      true]
   and 
   equ[throw,
      null]

}

pred examples_bstree_NodeCondition5[
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




pred examples_bstree_BinTreeCondition5[
  examples_bstree_BinTree_root:univ->univ,
  thiz:univ
]{
   not (
     equ[thiz.examples_bstree_BinTree_root,
        null]
   )

}

pred examples_bstree_BinTreeCondition4[
  examples_bstree_BinTree_root:univ->univ,
  thiz:univ
]{
   equ[thiz.examples_bstree_BinTree_root,
      null]

}

pred examples_bstree_BinTreeCondition9[
  examples_bstree_Node_left:univ->univ,
  var_1_current:univ
]{
   not (
     equ[var_1_current.examples_bstree_Node_left,
        null]
   )

}

pred examples_bstree_BinTreeCondition8[
  examples_bstree_Node_left:univ->univ,
  var_1_current:univ
]{
   equ[var_1_current.examples_bstree_Node_left,
      null]

}

pred examples_bstree_BinTree_ensures[
  examples_bstree_Node_key':univ->univ,
  nodes:univ->univ,
  nodes':univ->univ,
  thiz:univ,
  throw':univ,
  x':univ
]{
   (
     some n:examples_bstree_Node | {
       equ[(thiz.nodes)+n,
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

pred examples_bstree_BinTreeCondition10[
  examples_bstree_Node_right:univ->univ,
  var_1_current:univ
]{
   equ[var_1_current.examples_bstree_Node_right,
      null]

}

pred examples_bstree_BinTreeCondition11[
  examples_bstree_Node_right:univ->univ,
  var_1_current:univ
]{
   not (
     equ[var_1_current.examples_bstree_Node_right,
        null]
   )

}

pred examples_bstree_BinTreeCondition18[
  examples_bstree_BinTree_root:univ->univ,
  examples_bstree_Node_left:univ->univ,
  examples_bstree_Node_right:univ->univ,
  nodes:univ->univ,
  thiz:univ
]{
   examples_bstree_BinTree_nodes_abstraction[examples_bstree_BinTree_root,
                                            examples_bstree_Node_left,
                                            examples_bstree_Node_right,
                                            nodes,
                                            thiz]

}

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

pred examples_bstree_BinTreeCondition12[
  examples_bstree_Node_key:univ->univ,
  var_1_current:univ,
  x:univ
]{
   lt[x,
     var_1_current.examples_bstree_Node_key]

}

pred examples_bstree_BinTreeCondition13[
  examples_bstree_Node_key:univ->univ,
  var_1_current:univ,
  x:univ
]{
   not (
     lt[x,
       var_1_current.examples_bstree_Node_key]
   )

}

pred postcondition_examples_bstree_BinTree_add_0[
  examples_bstree_BinTree_root':univ->univ,
  examples_bstree_Node_key':univ->univ,
  examples_bstree_Node_left':univ->univ,
  examples_bstree_Node_right':univ->univ,
  nodes:univ->univ,
  nodes':univ->univ,
  thiz:univ,
  thiz':univ,
  throw':univ,
  x':univ
]{
   examples_bstree_BinTree_ensures[examples_bstree_Node_key',
                                  nodes,
                                  nodes',
                                  thiz,
                                  throw',
                                  x']
   and 
   examples_bstree_BinTree_object_invariant[examples_bstree_BinTree_root',
                                           examples_bstree_Node_key',
                                           examples_bstree_Node_left',
                                           examples_bstree_Node_right',
                                           thiz']

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

pred examples_bstree_BinTreeCondition6[
  var_1_current:univ
]{
   isEmptyOrNull[var_1_current]

}

pred examples_bstree_BinTreeCondition7[
  var_1_current:univ
]{
   not (
     isEmptyOrNull[var_1_current])

}

pred precondition_examples_bstree_BinTree_add_0[
  examples_bstree_BinTree_root:univ->univ,
  examples_bstree_Node_key:univ->univ,
  examples_bstree_Node_left:univ->univ,
  examples_bstree_Node_right:univ->univ,
  nodes:univ->univ,
  thiz:univ,
  throw:univ,
  usedObjects:set (java_lang_Object),
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

   and
   thiz.*(examples_bstree_BinTree_root + examples_bstree_Node_left + examples_bstree_Node_right) + null = usedObjects + null
}

pred examples_bstree_BinTreeCondition17[
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

pred examples_bstree_BinTreeCondition15[
  exit_stmt_reached:univ,
  var_2_ws_1:univ
]{
   not (
     liftExpression[var_2_ws_1]
     and 
     (
       exit_stmt_reached=false)
   )

}

pred examples_bstree_BinTreeCondition16[
  nullDerefBool:univ,
  throw:univ
]{
   equ[nullDerefBool,
      true]
   and 
   equ[throw,
      null]

}

pred examples_bstree_BinTreeCondition14[
  exit_stmt_reached:univ,
  var_2_ws_1:univ
]{
   liftExpression[var_2_ws_1]
   and 
   (
     exit_stmt_reached=false)

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


pred examples_bstree_BinTree_add_0[
  thiz_0: examples_bstree_BinTree,
  throw_1: java_lang_Throwable + null,
  throw_2: java_lang_Throwable + null,
  throw_3: java_lang_Throwable + null,
  throw_4: java_lang_Throwable + null,
  throw_5: java_lang_Throwable + null,
  throw_6: java_lang_Throwable + null,
  throw_7: java_lang_Throwable + null,
  throw_8: java_lang_Throwable + null,
  throw_9: java_lang_Throwable + null,
  throw_10: java_lang_Throwable + null,
  throw_11: java_lang_Throwable + null,
  throw_12: java_lang_Throwable + null,
  throw_13: java_lang_Throwable + null,
  throw_14: java_lang_Throwable + null,
  throw_15: java_lang_Throwable + null,
  throw_16: java_lang_Throwable + null,
  throw_17: java_lang_Throwable + null,
  throw_18: java_lang_Throwable + null,
  throw_19: java_lang_Throwable + null,
  throw_20: java_lang_Throwable + null,
  throw_21: java_lang_Throwable + null,
  throw_22: java_lang_Throwable + null,
  throw_23: java_lang_Throwable + null,
  throw_24: java_lang_Throwable + null,
  x_0: Int,
  examples_bstree_Node_right_0: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_1: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_2: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_3: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_4: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_5: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_6: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_7: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_8: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_9: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_10: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_11: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_12: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_13: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_14: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_15: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_16: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_17: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_18: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_19: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_20: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_21: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_22: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_23: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_24: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_25: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_26: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_27: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_28: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_29: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_30: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_31: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_32: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_key_0: ( examples_bstree_Node ) -> one ( Int ),
  examples_bstree_Node_key_1: ( examples_bstree_Node ) -> one ( Int ),
  examples_bstree_Node_key_2: ( examples_bstree_Node ) -> one ( Int ),
  examples_bstree_Node_key_3: ( examples_bstree_Node ) -> one ( Int ),
  examples_bstree_Node_key_4: ( examples_bstree_Node ) -> one ( Int ),
  examples_bstree_Node_key_5: ( examples_bstree_Node ) -> one ( Int ),
  examples_bstree_Node_key_6: ( examples_bstree_Node ) -> one ( Int ),
  examples_bstree_Node_key_7: ( examples_bstree_Node ) -> one ( Int ),
  examples_bstree_Node_key_8: ( examples_bstree_Node ) -> one ( Int ),
  examples_bstree_Node_key_9: ( examples_bstree_Node ) -> one ( Int ),
  examples_bstree_Node_key_10: ( examples_bstree_Node ) -> one ( Int ),
  examples_bstree_Node_key_11: ( examples_bstree_Node ) -> one ( Int ),
  examples_bstree_Node_key_12: ( examples_bstree_Node ) -> one ( Int ),
  examples_bstree_Node_key_13: ( examples_bstree_Node ) -> one ( Int ),
  examples_bstree_Node_key_14: ( examples_bstree_Node ) -> one ( Int ),
  examples_bstree_Node_key_15: ( examples_bstree_Node ) -> one ( Int ),
  examples_bstree_Node_key_16: ( examples_bstree_Node ) -> one ( Int ),
  examples_bstree_Node_key_17: ( examples_bstree_Node ) -> one ( Int ),
  examples_bstree_Node_key_18: ( examples_bstree_Node ) -> one ( Int ),
  examples_bstree_Node_key_19: ( examples_bstree_Node ) -> one ( Int ),
  examples_bstree_Node_key_20: ( examples_bstree_Node ) -> one ( Int ),
  examples_bstree_Node_key_21: ( examples_bstree_Node ) -> one ( Int ),
  examples_bstree_Node_key_22: ( examples_bstree_Node ) -> one ( Int ),
  examples_bstree_BinTree_root_0: ( examples_bstree_BinTree ) -> one ( examples_bstree_Node + null ),
  examples_bstree_BinTree_root_1: ( examples_bstree_BinTree ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_0: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_1: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_2: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_3: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_4: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_5: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_6: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_7: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_8: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_9: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_10: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_11: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_12: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_13: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_14: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_15: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_16: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_17: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_18: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_19: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_20: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_21: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_22: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_23: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_24: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_25: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_26: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_27: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_28: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_29: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_30: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_31: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_32: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  usedObjects_0: set ( java_lang_Object ),
  usedObjects_1: set ( java_lang_Object ),
  usedObjects_2: set ( java_lang_Object ),
  usedObjects_3: set ( java_lang_Object ),
  usedObjects_4: set ( java_lang_Object ),
  usedObjects_5: set ( java_lang_Object ),
  usedObjects_6: set ( java_lang_Object ),
  usedObjects_7: set ( java_lang_Object ),
  usedObjects_8: set ( java_lang_Object ),
  usedObjects_9: set ( java_lang_Object ),
  usedObjects_10: set ( java_lang_Object ),
  usedObjects_11: set ( java_lang_Object ),
  es_var__3_0: examples_bstree_Node + null,
  es_var__3_1: examples_bstree_Node + null,
  es_var__3_2: examples_bstree_Node + null,
  es_var__3_3: examples_bstree_Node + null,
  es_var__3_4: examples_bstree_Node + null,
  es_var__3_5: examples_bstree_Node + null,
  es_var__3_6: examples_bstree_Node + null,
  es_var__3_7: examples_bstree_Node + null,
  es_var__3_8: examples_bstree_Node + null,
  es_var__3_9: examples_bstree_Node + null,
  es_var__3_10: examples_bstree_Node + null,
  exit_stmt_reached_1: boolean,
  es_var__1_0: examples_bstree_Node + null,
  es_var__1_1: examples_bstree_Node + null,
  var_1_current_0: examples_bstree_Node + null,
  var_1_current_1: examples_bstree_Node + null,
  var_1_current_2: examples_bstree_Node + null,
  var_1_current_3: examples_bstree_Node + null,
  var_1_current_4: examples_bstree_Node + null,
  var_1_current_5: examples_bstree_Node + null,
  var_1_current_6: examples_bstree_Node + null,
  var_1_current_7: examples_bstree_Node + null,
  var_1_current_8: examples_bstree_Node + null,
  var_1_current_9: examples_bstree_Node + null,
  var_1_current_10: examples_bstree_Node + null,
  var_1_current_11: examples_bstree_Node + null,
  es_var__2_0: examples_bstree_Node + null,
  es_var__2_1: examples_bstree_Node + null,
  es_var__2_2: examples_bstree_Node + null,
  es_var__2_3: examples_bstree_Node + null,
  es_var__2_4: examples_bstree_Node + null,
  es_var__2_5: examples_bstree_Node + null,
  es_var__2_6: examples_bstree_Node + null,
  es_var__2_7: examples_bstree_Node + null,
  es_var__2_8: examples_bstree_Node + null,
  es_var__2_9: examples_bstree_Node + null,
  es_var__2_10: examples_bstree_Node + null,
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
  nullDerefBool_33: boolean,
  nullDerefBool_34: boolean,
  var_2_ws_1_0: boolean,
  var_2_ws_1_1: boolean,
  var_2_ws_1_2: boolean,
  var_2_ws_1_3: boolean,
  var_2_ws_1_4: boolean,
  var_2_ws_1_5: boolean,
  var_2_ws_1_6: boolean,
  var_2_ws_1_7: boolean,
  var_2_ws_1_8: boolean,
  var_2_ws_1_9: boolean,
  var_2_ws_1_10: boolean,
  var_2_ws_1_11: boolean,
  l9_exit_stmt_reached_0: boolean,
  l9_exit_stmt_reached_1: boolean,
  l8_nullDerefBool_0: boolean,
  l8_nullDerefBool_1: boolean,
  l8_nullDerefBool_2: boolean,
  l8_nullDerefBool_3: boolean,
  l8_nullDerefBool_4: boolean,
  l8_nullDerefBool_5: boolean,
  l8_nullDerefBool_6: boolean,
  l8_nullDerefBool_7: boolean,
  l13_nullDerefBool_0: boolean,
  l13_nullDerefBool_1: boolean,
  l13_nullDerefBool_2: boolean,
  l13_nullDerefBool_3: boolean,
  l13_nullDerefBool_4: boolean,
  l13_nullDerefBool_5: boolean,
  l13_nullDerefBool_6: boolean,
  l13_nullDerefBool_7: boolean,
  l0_exit_stmt_reached_0: boolean,
  l0_exit_stmt_reached_1: boolean,
  l6_exit_stmt_reached_0: boolean,
  l6_exit_stmt_reached_1: boolean,
  l16_nullDerefBool_0: boolean,
  l16_nullDerefBool_1: boolean,
  l16_nullDerefBool_2: boolean,
  l16_nullDerefBool_3: boolean,
  l16_nullDerefBool_4: boolean,
  l16_nullDerefBool_5: boolean,
  l16_nullDerefBool_6: boolean,
  l16_nullDerefBool_7: boolean,
  l3_exit_stmt_reached_0: boolean,
  l3_exit_stmt_reached_1: boolean,
  l18_exit_stmt_reached_0: boolean,
  l18_exit_stmt_reached_1: boolean,
  l5_exit_stmt_reached_0: boolean,
  l5_exit_stmt_reached_1: boolean,
  l11_nullDerefBool_0: boolean,
  l11_nullDerefBool_1: boolean,
  l11_nullDerefBool_2: boolean,
  l11_nullDerefBool_3: boolean,
  l11_nullDerefBool_4: boolean,
  l11_nullDerefBool_5: boolean,
  l11_nullDerefBool_6: boolean,
  l11_nullDerefBool_7: boolean,
  l0_nullDerefBool_0: boolean,
  l0_nullDerefBool_1: boolean,
  l0_nullDerefBool_2: boolean,
  l0_nullDerefBool_3: boolean,
  l0_nullDerefBool_4: boolean,
  l0_nullDerefBool_5: boolean,
  l0_nullDerefBool_6: boolean,
  l0_nullDerefBool_7: boolean,
  l12_exit_stmt_reached_0: boolean,
  l12_exit_stmt_reached_1: boolean,
  l2_nullDerefBool_0: boolean,
  l2_nullDerefBool_1: boolean,
  l2_nullDerefBool_2: boolean,
  l2_nullDerefBool_3: boolean,
  l2_nullDerefBool_4: boolean,
  l2_nullDerefBool_5: boolean,
  l2_nullDerefBool_6: boolean,
  l2_nullDerefBool_7: boolean,
  l7_nullDerefBool_0: boolean,
  l7_nullDerefBool_1: boolean,
  l7_nullDerefBool_2: boolean,
  l7_nullDerefBool_3: boolean,
  l7_nullDerefBool_4: boolean,
  l7_nullDerefBool_5: boolean,
  l7_nullDerefBool_6: boolean,
  l7_nullDerefBool_7: boolean,
  l16_exit_stmt_reached_0: boolean,
  l16_exit_stmt_reached_1: boolean,
  l20_exit_stmt_reached_0: boolean,
  l20_exit_stmt_reached_1: boolean,
  l4_exit_stmt_reached_0: boolean,
  l4_exit_stmt_reached_1: boolean,
  l15_exit_stmt_reached_0: boolean,
  l15_exit_stmt_reached_1: boolean,
  l14_nullDerefBool_0: boolean,
  l14_nullDerefBool_1: boolean,
  l14_nullDerefBool_2: boolean,
  l14_nullDerefBool_3: boolean,
  l14_nullDerefBool_4: boolean,
  l14_nullDerefBool_5: boolean,
  l14_nullDerefBool_6: boolean,
  l14_nullDerefBool_7: boolean,
  l19_nullDerefBool_0: boolean,
  l19_nullDerefBool_1: boolean,
  l19_nullDerefBool_2: boolean,
  l19_nullDerefBool_3: boolean,
  l19_nullDerefBool_4: boolean,
  l19_nullDerefBool_5: boolean,
  l19_nullDerefBool_6: boolean,
  l19_nullDerefBool_7: boolean,
  l1_exit_stmt_reached_0: boolean,
  l1_exit_stmt_reached_1: boolean,
  l2_exit_stmt_reached_0: boolean,
  l2_exit_stmt_reached_1: boolean,
  l14_exit_stmt_reached_0: boolean,
  l14_exit_stmt_reached_1: boolean,
  l4_nullDerefBool_0: boolean,
  l4_nullDerefBool_1: boolean,
  l4_nullDerefBool_2: boolean,
  l4_nullDerefBool_3: boolean,
  l4_nullDerefBool_4: boolean,
  l4_nullDerefBool_5: boolean,
  l4_nullDerefBool_6: boolean,
  l4_nullDerefBool_7: boolean,
  l19_exit_stmt_reached_0: boolean,
  l19_exit_stmt_reached_1: boolean,
  l8_exit_stmt_reached_0: boolean,
  l8_exit_stmt_reached_1: boolean,
  l13_exit_stmt_reached_0: boolean,
  l13_exit_stmt_reached_1: boolean,
  l9_nullDerefBool_0: boolean,
  l9_nullDerefBool_1: boolean,
  l9_nullDerefBool_2: boolean,
  l9_nullDerefBool_3: boolean,
  l9_nullDerefBool_4: boolean,
  l9_nullDerefBool_5: boolean,
  l9_nullDerefBool_6: boolean,
  l9_nullDerefBool_7: boolean,
  l5_nullDerefBool_0: boolean,
  l5_nullDerefBool_1: boolean,
  l5_nullDerefBool_2: boolean,
  l5_nullDerefBool_3: boolean,
  l5_nullDerefBool_4: boolean,
  l5_nullDerefBool_5: boolean,
  l5_nullDerefBool_6: boolean,
  l5_nullDerefBool_7: boolean,
  l11_exit_stmt_reached_0: boolean,
  l11_exit_stmt_reached_1: boolean,
  l6_nullDerefBool_0: boolean,
  l6_nullDerefBool_1: boolean,
  l6_nullDerefBool_2: boolean,
  l6_nullDerefBool_3: boolean,
  l6_nullDerefBool_4: boolean,
  l6_nullDerefBool_5: boolean,
  l6_nullDerefBool_6: boolean,
  l6_nullDerefBool_7: boolean,
  l17_exit_stmt_reached_0: boolean,
  l17_exit_stmt_reached_1: boolean,
  l18_nullDerefBool_0: boolean,
  l18_nullDerefBool_1: boolean,
  l18_nullDerefBool_2: boolean,
  l18_nullDerefBool_3: boolean,
  l18_nullDerefBool_4: boolean,
  l18_nullDerefBool_5: boolean,
  l18_nullDerefBool_6: boolean,
  l18_nullDerefBool_7: boolean,
  l3_nullDerefBool_0: boolean,
  l3_nullDerefBool_1: boolean,
  l3_nullDerefBool_2: boolean,
  l3_nullDerefBool_3: boolean,
  l3_nullDerefBool_4: boolean,
  l3_nullDerefBool_5: boolean,
  l3_nullDerefBool_6: boolean,
  l3_nullDerefBool_7: boolean,
  l20_nullDerefBool_0: boolean,
  l20_nullDerefBool_1: boolean,
  l20_nullDerefBool_2: boolean,
  l20_nullDerefBool_3: boolean,
  l20_nullDerefBool_4: boolean,
  l20_nullDerefBool_5: boolean,
  l20_nullDerefBool_6: boolean,
  l20_nullDerefBool_7: boolean,
  l15_nullDerefBool_0: boolean,
  l15_nullDerefBool_1: boolean,
  l15_nullDerefBool_2: boolean,
  l15_nullDerefBool_3: boolean,
  l15_nullDerefBool_4: boolean,
  l15_nullDerefBool_5: boolean,
  l15_nullDerefBool_6: boolean,
  l15_nullDerefBool_7: boolean,
  l1_nullDerefBool_0: boolean,
  l1_nullDerefBool_1: boolean,
  l1_nullDerefBool_2: boolean,
  l1_nullDerefBool_3: boolean,
  l1_nullDerefBool_4: boolean,
  l1_nullDerefBool_5: boolean,
  l1_nullDerefBool_6: boolean,
  l1_nullDerefBool_7: boolean,
  l12_nullDerefBool_0: boolean,
  l12_nullDerefBool_1: boolean,
  l12_nullDerefBool_2: boolean,
  l12_nullDerefBool_3: boolean,
  l12_nullDerefBool_4: boolean,
  l12_nullDerefBool_5: boolean,
  l12_nullDerefBool_6: boolean,
  l12_nullDerefBool_7: boolean,
  l7_exit_stmt_reached_0: boolean,
  l7_exit_stmt_reached_1: boolean,
  l17_nullDerefBool_0: boolean,
  l17_nullDerefBool_1: boolean,
  l17_nullDerefBool_2: boolean,
  l17_nullDerefBool_3: boolean,
  l17_nullDerefBool_4: boolean,
  l17_nullDerefBool_5: boolean,
  l17_nullDerefBool_6: boolean,
  l17_nullDerefBool_7: boolean,
  l10_exit_stmt_reached_0: boolean,
  l10_exit_stmt_reached_1: boolean,
  l10_nullDerefBool_0: boolean,
  l10_nullDerefBool_1: boolean,
  l10_nullDerefBool_2: boolean,
  l10_nullDerefBool_3: boolean,
  l10_nullDerefBool_4: boolean,
  l10_nullDerefBool_5: boolean,
  l10_nullDerefBool_6: boolean,
  l10_nullDerefBool_7: boolean
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
        var_1_current_1=thiz_0.examples_bstree_BinTree_root_0)
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
        var_1_current_0=var_1_current_1)
      and 
      (
        nullDerefBool_1=nullDerefBool_2)
    )
  )
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
            nullDerefBool_3=true)
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
            nullDerefBool_2=nullDerefBool_3)
        )
      )
      and 
      (
        (
          examples_bstree_BinTreeCondition4[examples_bstree_BinTree_root_0,
                                           thiz_0]
          and 
          TruePred[]
          and 
          (
            (
              examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
              and 
              getUnusedObject[es_var__1_1,
                             usedObjects_0,
                             usedObjects_1]
              and 
              instanceOf[es_var__1_1,
                        examples_bstree_Node]
              and 
              examples_bstree_Node_Constructor_0[es_var__1_1,
                                                throw_2,
                                                throw_3,
                                                x_0,
                                                examples_bstree_Node_right_0,
                                                examples_bstree_Node_right_1,
                                                examples_bstree_Node_right_2,
                                                examples_bstree_Node_key_0,
                                                examples_bstree_Node_key_1,
                                                examples_bstree_Node_key_2,
                                                examples_bstree_Node_left_0,
                                                examples_bstree_Node_left_1,
                                                examples_bstree_Node_left_2,
                                                l0_exit_stmt_reached_1,
                                                l0_nullDerefBool_1,
                                                l0_nullDerefBool_2,
                                                l0_nullDerefBool_3,
                                                l0_nullDerefBool_4,
                                                l0_nullDerefBool_5,
                                                l0_nullDerefBool_6,
                                                l0_nullDerefBool_7]
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
                throw_1=throw_3)
              and 
              (
                examples_bstree_Node_right_0=examples_bstree_Node_right_2)
              and 
              (
                l0_exit_stmt_reached_0=l0_exit_stmt_reached_1)
              and 
              (
                es_var__1_0=es_var__1_1)
              and 
              (
                l0_nullDerefBool_0=l0_nullDerefBool_7)
              and 
              (
                examples_bstree_Node_key_0=examples_bstree_Node_key_2)
              and 
              (
                examples_bstree_Node_left_0=examples_bstree_Node_left_2)
              and 
              (
                usedObjects_0=usedObjects_1)
            )
          )
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
                    nullDerefBool_4=true)
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
                    nullDerefBool_3=nullDerefBool_4)
                )
              )
              and 
              (
                examples_bstree_BinTree_root_1=(examples_bstree_BinTree_root_0)++((thiz_0)->(es_var__1_1)))
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
                nullDerefBool_3=nullDerefBool_4)
              and 
              (
                examples_bstree_BinTree_root_0=examples_bstree_BinTree_root_1)
            )
          )
        )
        or 
        (
          (
            not (
              examples_bstree_BinTreeCondition4[examples_bstree_BinTree_root_0,
                                               thiz_0]
            )
          )
          and 
          TruePred[]
          and 
          (
            l0_exit_stmt_reached_0=l0_exit_stmt_reached_1)
          and 
          (
            l0_nullDerefBool_0=l0_nullDerefBool_7)
          and 
          (
            nullDerefBool_3=nullDerefBool_4)
          and 
          (
            throw_1=throw_3)
          and 
          (
            examples_bstree_Node_right_0=examples_bstree_Node_right_2)
          and 
          (
            es_var__1_0=es_var__1_1)
          and 
          (
            examples_bstree_Node_key_0=examples_bstree_Node_key_2)
          and 
          (
            examples_bstree_Node_left_0=examples_bstree_Node_left_2)
          and 
          (
            usedObjects_0=usedObjects_1)
          and 
          (
            examples_bstree_BinTree_root_0=examples_bstree_BinTree_root_1)
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
        l0_exit_stmt_reached_0=l0_exit_stmt_reached_1)
      and 
      (
        l0_nullDerefBool_0=l0_nullDerefBool_7)
      and 
      (
        nullDerefBool_2=nullDerefBool_4)
      and 
      (
        examples_bstree_BinTree_root_0=examples_bstree_BinTree_root_1)
      and 
      (
        throw_1=throw_3)
      and 
      (
        examples_bstree_Node_right_0=examples_bstree_Node_right_2)
      and 
      (
        es_var__1_0=es_var__1_1)
      and 
      (
        examples_bstree_Node_key_0=examples_bstree_Node_key_2)
      and 
      (
        examples_bstree_Node_left_0=examples_bstree_Node_left_2)
      and 
      (
        usedObjects_0=usedObjects_1)
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
        var_2_ws_1_1=(neq[var_1_current_1.examples_bstree_Node_key_2,
           x_0]=>(true)else(false))
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
        var_2_ws_1_0=var_2_ws_1_1)
    )
  )
  and 
  (
    (
      examples_bstree_BinTreeCondition14[exit_stmt_reached_1,
                                        var_2_ws_1_1]
      and 
      (
        (
          examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
          and 
          (
            (
              examples_bstree_BinTreeCondition6[var_1_current_1]
              and 
              (
                nullDerefBool_5=true)
            )
            or 
            (
              (
                not (
                  examples_bstree_BinTreeCondition6[var_1_current_1])
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
            (
              examples_bstree_BinTreeCondition12[examples_bstree_Node_key_2,
                                                var_1_current_1,
                                                x_0]
              and 
              (
                (
                  examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
                  and 
                  (
                    (
                      examples_bstree_BinTreeCondition6[var_1_current_1]
                      and 
                      (
                        nullDerefBool_6=true)
                    )
                    or 
                    (
                      (
                        not (
                          examples_bstree_BinTreeCondition6[var_1_current_1])
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
                      examples_bstree_BinTreeCondition8[examples_bstree_Node_left_2,
                                                       var_1_current_1]
                      and 
                      TruePred[]
                      and 
                      (
                        (
                          examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
                          and 
                          getUnusedObject[es_var__2_1,
                                         usedObjects_1,
                                         usedObjects_2]
                          and 
                          instanceOf[es_var__2_1,
                                    examples_bstree_Node]
                          and 
                          examples_bstree_Node_Constructor_0[es_var__2_1,
                                                            throw_4,
                                                            throw_5,
                                                            x_0,
                                                            examples_bstree_Node_right_2,
                                                            examples_bstree_Node_right_3,
                                                            examples_bstree_Node_right_5,
                                                            examples_bstree_Node_key_2,
                                                            examples_bstree_Node_key_3,
                                                            examples_bstree_Node_key_4,
                                                            examples_bstree_Node_left_2,
                                                            examples_bstree_Node_left_3,
                                                            examples_bstree_Node_left_4,
                                                            l1_exit_stmt_reached_1,
                                                            l1_nullDerefBool_1,
                                                            l1_nullDerefBool_2,
                                                            l1_nullDerefBool_3,
                                                            l1_nullDerefBool_4,
                                                            l1_nullDerefBool_5,
                                                            l1_nullDerefBool_6,
                                                            l1_nullDerefBool_7]
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
                            es_var__2_0=es_var__2_1)
                          and 
                          (
                            throw_3=throw_5)
                          and 
                          (
                            examples_bstree_Node_right_2=examples_bstree_Node_right_5)
                          and 
                          (
                            l1_nullDerefBool_0=l1_nullDerefBool_7)
                          and 
                          (
                            l1_exit_stmt_reached_0=l1_exit_stmt_reached_1)
                          and 
                          (
                            examples_bstree_Node_key_2=examples_bstree_Node_key_4)
                          and 
                          (
                            examples_bstree_Node_left_2=examples_bstree_Node_left_4)
                          and 
                          (
                            usedObjects_1=usedObjects_2)
                        )
                      )
                      and 
                      (
                        (
                          examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
                          and 
                          (
                            (
                              examples_bstree_BinTreeCondition6[var_1_current_1]
                              and 
                              (
                                nullDerefBool_7=true)
                            )
                            or 
                            (
                              (
                                not (
                                  examples_bstree_BinTreeCondition6[var_1_current_1])
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
                            examples_bstree_Node_left_5=(examples_bstree_Node_left_4)++((var_1_current_1)->(es_var__2_1)))
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
                            nullDerefBool_6=nullDerefBool_7)
                          and 
                          (
                            examples_bstree_Node_left_4=examples_bstree_Node_left_5)
                        )
                      )
                      and 
                      (
                        var_1_current_1=var_1_current_2)
                    )
                    or 
                    (
                      (
                        not (
                          examples_bstree_BinTreeCondition8[examples_bstree_Node_left_2,
                                                           var_1_current_1]
                        )
                      )
                      and 
                      (
                        (
                          examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
                          and 
                          (
                            (
                              examples_bstree_BinTreeCondition6[var_1_current_1]
                              and 
                              (
                                nullDerefBool_7=true)
                            )
                            or 
                            (
                              (
                                not (
                                  examples_bstree_BinTreeCondition6[var_1_current_1])
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
                            var_1_current_2=var_1_current_1.examples_bstree_Node_left_2)
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
                            var_1_current_1=var_1_current_2)
                          and 
                          (
                            nullDerefBool_6=nullDerefBool_7)
                        )
                      )
                      and 
                      (
                        l1_nullDerefBool_0=l1_nullDerefBool_7)
                      and 
                      (
                        l1_exit_stmt_reached_0=l1_exit_stmt_reached_1)
                      and 
                      (
                        es_var__2_0=es_var__2_1)
                      and 
                      (
                        throw_3=throw_5)
                      and 
                      (
                        examples_bstree_Node_right_2=examples_bstree_Node_right_5)
                      and 
                      (
                        examples_bstree_Node_key_2=examples_bstree_Node_key_4)
                      and 
                      (
                        usedObjects_1=usedObjects_2)
                      and 
                      (
                        examples_bstree_Node_left_2=examples_bstree_Node_left_5)
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
                    l1_nullDerefBool_0=l1_nullDerefBool_7)
                  and 
                  (
                    l1_exit_stmt_reached_0=l1_exit_stmt_reached_1)
                  and 
                  (
                    nullDerefBool_5=nullDerefBool_7)
                  and 
                  (
                    es_var__2_0=es_var__2_1)
                  and 
                  (
                    throw_3=throw_5)
                  and 
                  (
                    examples_bstree_Node_right_2=examples_bstree_Node_right_5)
                  and 
                  (
                    var_1_current_1=var_1_current_2)
                  and 
                  (
                    examples_bstree_Node_key_2=examples_bstree_Node_key_4)
                  and 
                  (
                    examples_bstree_Node_left_2=examples_bstree_Node_left_5)
                  and 
                  (
                    usedObjects_1=usedObjects_2)
                )
              )
              and 
              (
                l2_exit_stmt_reached_0=l2_exit_stmt_reached_1)
              and 
              (
                l2_nullDerefBool_0=l2_nullDerefBool_7)
              and 
              (
                es_var__3_0=es_var__3_1)
            )
            or 
            (
              (
                not (
                  examples_bstree_BinTreeCondition12[examples_bstree_Node_key_2,
                                                    var_1_current_1,
                                                    x_0]
                )
              )
              and 
              (
                (
                  examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
                  and 
                  (
                    (
                      examples_bstree_BinTreeCondition6[var_1_current_1]
                      and 
                      (
                        nullDerefBool_6=true)
                    )
                    or 
                    (
                      (
                        not (
                          examples_bstree_BinTreeCondition6[var_1_current_1])
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
                      examples_bstree_BinTreeCondition10[examples_bstree_Node_right_2,
                                                        var_1_current_1]
                      and 
                      TruePred[]
                      and 
                      (
                        (
                          examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
                          and 
                          getUnusedObject[es_var__3_1,
                                         usedObjects_1,
                                         usedObjects_2]
                          and 
                          instanceOf[es_var__3_1,
                                    examples_bstree_Node]
                          and 
                          examples_bstree_Node_Constructor_0[es_var__3_1,
                                                            throw_4,
                                                            throw_5,
                                                            x_0,
                                                            examples_bstree_Node_right_2,
                                                            examples_bstree_Node_right_3,
                                                            examples_bstree_Node_right_4,
                                                            examples_bstree_Node_key_2,
                                                            examples_bstree_Node_key_3,
                                                            examples_bstree_Node_key_4,
                                                            examples_bstree_Node_left_2,
                                                            examples_bstree_Node_left_3,
                                                            examples_bstree_Node_left_5,
                                                            l2_exit_stmt_reached_1,
                                                            l2_nullDerefBool_1,
                                                            l2_nullDerefBool_2,
                                                            l2_nullDerefBool_3,
                                                            l2_nullDerefBool_4,
                                                            l2_nullDerefBool_5,
                                                            l2_nullDerefBool_6,
                                                            l2_nullDerefBool_7]
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
                            l2_nullDerefBool_0=l2_nullDerefBool_7)
                          and 
                          (
                            throw_3=throw_5)
                          and 
                          (
                            es_var__3_0=es_var__3_1)
                          and 
                          (
                            examples_bstree_Node_right_2=examples_bstree_Node_right_4)
                          and 
                          (
                            l2_exit_stmt_reached_0=l2_exit_stmt_reached_1)
                          and 
                          (
                            examples_bstree_Node_key_2=examples_bstree_Node_key_4)
                          and 
                          (
                            examples_bstree_Node_left_2=examples_bstree_Node_left_5)
                          and 
                          (
                            usedObjects_1=usedObjects_2)
                        )
                      )
                      and 
                      (
                        (
                          examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
                          and 
                          (
                            (
                              examples_bstree_BinTreeCondition6[var_1_current_1]
                              and 
                              (
                                nullDerefBool_7=true)
                            )
                            or 
                            (
                              (
                                not (
                                  examples_bstree_BinTreeCondition6[var_1_current_1])
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
                            examples_bstree_Node_right_5=(examples_bstree_Node_right_4)++((var_1_current_1)->(es_var__3_1)))
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
                            examples_bstree_Node_right_4=examples_bstree_Node_right_5)
                          and 
                          (
                            nullDerefBool_6=nullDerefBool_7)
                        )
                      )
                      and 
                      (
                        var_1_current_1=var_1_current_2)
                    )
                    or 
                    (
                      (
                        not (
                          examples_bstree_BinTreeCondition10[examples_bstree_Node_right_2,
                                                            var_1_current_1]
                        )
                      )
                      and 
                      (
                        (
                          examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
                          and 
                          (
                            (
                              examples_bstree_BinTreeCondition6[var_1_current_1]
                              and 
                              (
                                nullDerefBool_7=true)
                            )
                            or 
                            (
                              (
                                not (
                                  examples_bstree_BinTreeCondition6[var_1_current_1])
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
                            var_1_current_2=var_1_current_1.examples_bstree_Node_right_2)
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
                            var_1_current_1=var_1_current_2)
                          and 
                          (
                            nullDerefBool_6=nullDerefBool_7)
                        )
                      )
                      and 
                      (
                        l2_exit_stmt_reached_0=l2_exit_stmt_reached_1)
                      and 
                      (
                        l2_nullDerefBool_0=l2_nullDerefBool_7)
                      and 
                      (
                        throw_3=throw_5)
                      and 
                      (
                        es_var__3_0=es_var__3_1)
                      and 
                      (
                        examples_bstree_Node_key_2=examples_bstree_Node_key_4)
                      and 
                      (
                        examples_bstree_Node_left_2=examples_bstree_Node_left_5)
                      and 
                      (
                        usedObjects_1=usedObjects_2)
                      and 
                      (
                        examples_bstree_Node_right_2=examples_bstree_Node_right_5)
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
                    l2_exit_stmt_reached_0=l2_exit_stmt_reached_1)
                  and 
                  (
                    nullDerefBool_5=nullDerefBool_7)
                  and 
                  (
                    l2_nullDerefBool_0=l2_nullDerefBool_7)
                  and 
                  (
                    throw_3=throw_5)
                  and 
                  (
                    es_var__3_0=es_var__3_1)
                  and 
                  (
                    examples_bstree_Node_right_2=examples_bstree_Node_right_5)
                  and 
                  (
                    var_1_current_1=var_1_current_2)
                  and 
                  (
                    examples_bstree_Node_key_2=examples_bstree_Node_key_4)
                  and 
                  (
                    examples_bstree_Node_left_2=examples_bstree_Node_left_5)
                  and 
                  (
                    usedObjects_1=usedObjects_2)
                )
              )
              and 
              (
                l1_nullDerefBool_0=l1_nullDerefBool_7)
              and 
              (
                l1_exit_stmt_reached_0=l1_exit_stmt_reached_1)
              and 
              (
                es_var__2_0=es_var__2_1)
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
            l1_nullDerefBool_0=l1_nullDerefBool_7)
          and 
          (
            l1_exit_stmt_reached_0=l1_exit_stmt_reached_1)
          and 
          (
            l2_exit_stmt_reached_0=l2_exit_stmt_reached_1)
          and 
          (
            nullDerefBool_4=nullDerefBool_7)
          and 
          (
            es_var__2_0=es_var__2_1)
          and 
          (
            l2_nullDerefBool_0=l2_nullDerefBool_7)
          and 
          (
            es_var__3_0=es_var__3_1)
          and 
          (
            throw_3=throw_5)
          and 
          (
            examples_bstree_Node_right_2=examples_bstree_Node_right_5)
          and 
          (
            var_1_current_1=var_1_current_2)
          and 
          (
            examples_bstree_Node_key_2=examples_bstree_Node_key_4)
          and 
          (
            examples_bstree_Node_left_2=examples_bstree_Node_left_5)
          and 
          (
            usedObjects_1=usedObjects_2)
        )
      )
      and 
      (
        (
          examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
          and 
          (
            var_2_ws_1_2=(neq[var_1_current_2.examples_bstree_Node_key_4,
               x_0]=>(true)else(false))
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
            var_2_ws_1_1=var_2_ws_1_2)
        )
      )
    )
    or 
    (
      TruePred[]
      and 
      (
        l1_nullDerefBool_0=l1_nullDerefBool_7)
      and 
      (
        l1_exit_stmt_reached_0=l1_exit_stmt_reached_1)
      and 
      (
        l2_exit_stmt_reached_0=l2_exit_stmt_reached_1)
      and 
      (
        nullDerefBool_4=nullDerefBool_7)
      and 
      (
        es_var__2_0=es_var__2_1)
      and 
      (
        l2_nullDerefBool_0=l2_nullDerefBool_7)
      and 
      (
        es_var__3_0=es_var__3_1)
      and 
      (
        throw_3=throw_5)
      and 
      (
        examples_bstree_Node_right_2=examples_bstree_Node_right_5)
      and 
      (
        var_1_current_1=var_1_current_2)
      and 
      (
        examples_bstree_Node_key_2=examples_bstree_Node_key_4)
      and 
      (
        var_2_ws_1_1=var_2_ws_1_2)
      and 
      (
        examples_bstree_Node_left_2=examples_bstree_Node_left_5)
      and 
      (
        usedObjects_1=usedObjects_2)
    )
  )
  and 
  (
    (
      examples_bstree_BinTreeCondition14[exit_stmt_reached_1,
                                        var_2_ws_1_2]
      and 
      (
        (
          examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
          and 
          (
            (
              examples_bstree_BinTreeCondition6[var_1_current_2]
              and 
              (
                nullDerefBool_8=true)
            )
            or 
            (
              (
                not (
                  examples_bstree_BinTreeCondition6[var_1_current_2])
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
            (
              examples_bstree_BinTreeCondition12[examples_bstree_Node_key_4,
                                                var_1_current_2,
                                                x_0]
              and 
              (
                (
                  examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
                  and 
                  (
                    (
                      examples_bstree_BinTreeCondition6[var_1_current_2]
                      and 
                      (
                        nullDerefBool_9=true)
                    )
                    or 
                    (
                      (
                        not (
                          examples_bstree_BinTreeCondition6[var_1_current_2])
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
                      examples_bstree_BinTreeCondition8[examples_bstree_Node_left_5,
                                                       var_1_current_2]
                      and 
                      TruePred[]
                      and 
                      (
                        (
                          examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
                          and 
                          getUnusedObject[es_var__2_2,
                                         usedObjects_2,
                                         usedObjects_3]
                          and 
                          instanceOf[es_var__2_2,
                                    examples_bstree_Node]
                          and 
                          examples_bstree_Node_Constructor_0[es_var__2_2,
                                                            throw_6,
                                                            throw_7,
                                                            x_0,
                                                            examples_bstree_Node_right_5,
                                                            examples_bstree_Node_right_6,
                                                            examples_bstree_Node_right_8,
                                                            examples_bstree_Node_key_4,
                                                            examples_bstree_Node_key_5,
                                                            examples_bstree_Node_key_6,
                                                            examples_bstree_Node_left_5,
                                                            examples_bstree_Node_left_6,
                                                            examples_bstree_Node_left_7,
                                                            l3_exit_stmt_reached_1,
                                                            l3_nullDerefBool_1,
                                                            l3_nullDerefBool_2,
                                                            l3_nullDerefBool_3,
                                                            l3_nullDerefBool_4,
                                                            l3_nullDerefBool_5,
                                                            l3_nullDerefBool_6,
                                                            l3_nullDerefBool_7]
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
                            es_var__2_1=es_var__2_2)
                          and 
                          (
                            throw_5=throw_7)
                          and 
                          (
                            l3_nullDerefBool_0=l3_nullDerefBool_7)
                          and 
                          (
                            examples_bstree_Node_right_5=examples_bstree_Node_right_8)
                          and 
                          (
                            l3_exit_stmt_reached_0=l3_exit_stmt_reached_1)
                          and 
                          (
                            examples_bstree_Node_key_4=examples_bstree_Node_key_6)
                          and 
                          (
                            examples_bstree_Node_left_5=examples_bstree_Node_left_7)
                          and 
                          (
                            usedObjects_2=usedObjects_3)
                        )
                      )
                      and 
                      (
                        (
                          examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
                          and 
                          (
                            (
                              examples_bstree_BinTreeCondition6[var_1_current_2]
                              and 
                              (
                                nullDerefBool_10=true)
                            )
                            or 
                            (
                              (
                                not (
                                  examples_bstree_BinTreeCondition6[var_1_current_2])
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
                            examples_bstree_Node_left_8=(examples_bstree_Node_left_7)++((var_1_current_2)->(es_var__2_2)))
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
                            nullDerefBool_9=nullDerefBool_10)
                          and 
                          (
                            examples_bstree_Node_left_7=examples_bstree_Node_left_8)
                        )
                      )
                      and 
                      (
                        var_1_current_2=var_1_current_3)
                    )
                    or 
                    (
                      (
                        not (
                          examples_bstree_BinTreeCondition8[examples_bstree_Node_left_5,
                                                           var_1_current_2]
                        )
                      )
                      and 
                      (
                        (
                          examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
                          and 
                          (
                            (
                              examples_bstree_BinTreeCondition6[var_1_current_2]
                              and 
                              (
                                nullDerefBool_10=true)
                            )
                            or 
                            (
                              (
                                not (
                                  examples_bstree_BinTreeCondition6[var_1_current_2])
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
                            var_1_current_3=var_1_current_2.examples_bstree_Node_left_5)
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
                            var_1_current_2=var_1_current_3)
                          and 
                          (
                            nullDerefBool_9=nullDerefBool_10)
                        )
                      )
                      and 
                      (
                        l3_nullDerefBool_0=l3_nullDerefBool_7)
                      and 
                      (
                        l3_exit_stmt_reached_0=l3_exit_stmt_reached_1)
                      and 
                      (
                        es_var__2_1=es_var__2_2)
                      and 
                      (
                        throw_5=throw_7)
                      and 
                      (
                        examples_bstree_Node_right_5=examples_bstree_Node_right_8)
                      and 
                      (
                        examples_bstree_Node_key_4=examples_bstree_Node_key_6)
                      and 
                      (
                        usedObjects_2=usedObjects_3)
                      and 
                      (
                        examples_bstree_Node_left_5=examples_bstree_Node_left_8)
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
                    l3_nullDerefBool_0=l3_nullDerefBool_7)
                  and 
                  (
                    nullDerefBool_8=nullDerefBool_10)
                  and 
                  (
                    l3_exit_stmt_reached_0=l3_exit_stmt_reached_1)
                  and 
                  (
                    es_var__2_1=es_var__2_2)
                  and 
                  (
                    throw_5=throw_7)
                  and 
                  (
                    examples_bstree_Node_right_5=examples_bstree_Node_right_8)
                  and 
                  (
                    var_1_current_2=var_1_current_3)
                  and 
                  (
                    examples_bstree_Node_key_4=examples_bstree_Node_key_6)
                  and 
                  (
                    examples_bstree_Node_left_5=examples_bstree_Node_left_8)
                  and 
                  (
                    usedObjects_2=usedObjects_3)
                )
              )
              and 
              (
                l4_nullDerefBool_0=l4_nullDerefBool_7)
              and 
              (
                es_var__3_1=es_var__3_2)
              and 
              (
                l4_exit_stmt_reached_0=l4_exit_stmt_reached_1)
            )
            or 
            (
              (
                not (
                  examples_bstree_BinTreeCondition12[examples_bstree_Node_key_4,
                                                    var_1_current_2,
                                                    x_0]
                )
              )
              and 
              (
                (
                  examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
                  and 
                  (
                    (
                      examples_bstree_BinTreeCondition6[var_1_current_2]
                      and 
                      (
                        nullDerefBool_9=true)
                    )
                    or 
                    (
                      (
                        not (
                          examples_bstree_BinTreeCondition6[var_1_current_2])
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
                      examples_bstree_BinTreeCondition10[examples_bstree_Node_right_5,
                                                        var_1_current_2]
                      and 
                      TruePred[]
                      and 
                      (
                        (
                          examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
                          and 
                          getUnusedObject[es_var__3_2,
                                         usedObjects_2,
                                         usedObjects_3]
                          and 
                          instanceOf[es_var__3_2,
                                    examples_bstree_Node]
                          and 
                          examples_bstree_Node_Constructor_0[es_var__3_2,
                                                            throw_6,
                                                            throw_7,
                                                            x_0,
                                                            examples_bstree_Node_right_5,
                                                            examples_bstree_Node_right_6,
                                                            examples_bstree_Node_right_7,
                                                            examples_bstree_Node_key_4,
                                                            examples_bstree_Node_key_5,
                                                            examples_bstree_Node_key_6,
                                                            examples_bstree_Node_left_5,
                                                            examples_bstree_Node_left_6,
                                                            examples_bstree_Node_left_8,
                                                            l4_exit_stmt_reached_1,
                                                            l4_nullDerefBool_1,
                                                            l4_nullDerefBool_2,
                                                            l4_nullDerefBool_3,
                                                            l4_nullDerefBool_4,
                                                            l4_nullDerefBool_5,
                                                            l4_nullDerefBool_6,
                                                            l4_nullDerefBool_7]
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
                            throw_5=throw_7)
                          and 
                          (
                            es_var__3_1=es_var__3_2)
                          and 
                          (
                            examples_bstree_Node_right_5=examples_bstree_Node_right_7)
                          and 
                          (
                            l4_nullDerefBool_0=l4_nullDerefBool_7)
                          and 
                          (
                            examples_bstree_Node_key_4=examples_bstree_Node_key_6)
                          and 
                          (
                            examples_bstree_Node_left_5=examples_bstree_Node_left_8)
                          and 
                          (
                            usedObjects_2=usedObjects_3)
                          and 
                          (
                            l4_exit_stmt_reached_0=l4_exit_stmt_reached_1)
                        )
                      )
                      and 
                      (
                        (
                          examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
                          and 
                          (
                            (
                              examples_bstree_BinTreeCondition6[var_1_current_2]
                              and 
                              (
                                nullDerefBool_10=true)
                            )
                            or 
                            (
                              (
                                not (
                                  examples_bstree_BinTreeCondition6[var_1_current_2])
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
                            examples_bstree_Node_right_8=(examples_bstree_Node_right_7)++((var_1_current_2)->(es_var__3_2)))
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
                            examples_bstree_Node_right_7=examples_bstree_Node_right_8)
                          and 
                          (
                            nullDerefBool_9=nullDerefBool_10)
                        )
                      )
                      and 
                      (
                        var_1_current_2=var_1_current_3)
                    )
                    or 
                    (
                      (
                        not (
                          examples_bstree_BinTreeCondition10[examples_bstree_Node_right_5,
                                                            var_1_current_2]
                        )
                      )
                      and 
                      (
                        (
                          examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
                          and 
                          (
                            (
                              examples_bstree_BinTreeCondition6[var_1_current_2]
                              and 
                              (
                                nullDerefBool_10=true)
                            )
                            or 
                            (
                              (
                                not (
                                  examples_bstree_BinTreeCondition6[var_1_current_2])
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
                            var_1_current_3=var_1_current_2.examples_bstree_Node_right_5)
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
                            var_1_current_2=var_1_current_3)
                          and 
                          (
                            nullDerefBool_9=nullDerefBool_10)
                        )
                      )
                      and 
                      (
                        l4_nullDerefBool_0=l4_nullDerefBool_7)
                      and 
                      (
                        throw_5=throw_7)
                      and 
                      (
                        es_var__3_1=es_var__3_2)
                      and 
                      (
                        examples_bstree_Node_key_4=examples_bstree_Node_key_6)
                      and 
                      (
                        examples_bstree_Node_left_5=examples_bstree_Node_left_8)
                      and 
                      (
                        usedObjects_2=usedObjects_3)
                      and 
                      (
                        l4_exit_stmt_reached_0=l4_exit_stmt_reached_1)
                      and 
                      (
                        examples_bstree_Node_right_5=examples_bstree_Node_right_8)
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
                    nullDerefBool_8=nullDerefBool_10)
                  and 
                  (
                    l4_nullDerefBool_0=l4_nullDerefBool_7)
                  and 
                  (
                    throw_5=throw_7)
                  and 
                  (
                    es_var__3_1=es_var__3_2)
                  and 
                  (
                    examples_bstree_Node_right_5=examples_bstree_Node_right_8)
                  and 
                  (
                    var_1_current_2=var_1_current_3)
                  and 
                  (
                    examples_bstree_Node_key_4=examples_bstree_Node_key_6)
                  and 
                  (
                    examples_bstree_Node_left_5=examples_bstree_Node_left_8)
                  and 
                  (
                    usedObjects_2=usedObjects_3)
                  and 
                  (
                    l4_exit_stmt_reached_0=l4_exit_stmt_reached_1)
                )
              )
              and 
              (
                l3_nullDerefBool_0=l3_nullDerefBool_7)
              and 
              (
                l3_exit_stmt_reached_0=l3_exit_stmt_reached_1)
              and 
              (
                es_var__2_1=es_var__2_2)
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
            l3_nullDerefBool_0=l3_nullDerefBool_7)
          and 
          (
            nullDerefBool_7=nullDerefBool_10)
          and 
          (
            l3_exit_stmt_reached_0=l3_exit_stmt_reached_1)
          and 
          (
            l4_nullDerefBool_0=l4_nullDerefBool_7)
          and 
          (
            es_var__2_1=es_var__2_2)
          and 
          (
            es_var__3_1=es_var__3_2)
          and 
          (
            throw_5=throw_7)
          and 
          (
            examples_bstree_Node_right_5=examples_bstree_Node_right_8)
          and 
          (
            var_1_current_2=var_1_current_3)
          and 
          (
            examples_bstree_Node_key_4=examples_bstree_Node_key_6)
          and 
          (
            examples_bstree_Node_left_5=examples_bstree_Node_left_8)
          and 
          (
            usedObjects_2=usedObjects_3)
          and 
          (
            l4_exit_stmt_reached_0=l4_exit_stmt_reached_1)
        )
      )
      and 
      (
        (
          examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
          and 
          (
            var_2_ws_1_3=(neq[var_1_current_3.examples_bstree_Node_key_6,
               x_0]=>(true)else(false))
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
            var_2_ws_1_2=var_2_ws_1_3)
        )
      )
    )
    or 
    (
      TruePred[]
      and 
      (
        l3_nullDerefBool_0=l3_nullDerefBool_7)
      and 
      (
        nullDerefBool_7=nullDerefBool_10)
      and 
      (
        l3_exit_stmt_reached_0=l3_exit_stmt_reached_1)
      and 
      (
        l4_nullDerefBool_0=l4_nullDerefBool_7)
      and 
      (
        es_var__2_1=es_var__2_2)
      and 
      (
        es_var__3_1=es_var__3_2)
      and 
      (
        throw_5=throw_7)
      and 
      (
        examples_bstree_Node_right_5=examples_bstree_Node_right_8)
      and 
      (
        var_1_current_2=var_1_current_3)
      and 
      (
        examples_bstree_Node_key_4=examples_bstree_Node_key_6)
      and 
      (
        var_2_ws_1_2=var_2_ws_1_3)
      and 
      (
        examples_bstree_Node_left_5=examples_bstree_Node_left_8)
      and 
      (
        usedObjects_2=usedObjects_3)
      and 
      (
        l4_exit_stmt_reached_0=l4_exit_stmt_reached_1)
    )
  )
  and 
  (
    (
      examples_bstree_BinTreeCondition14[exit_stmt_reached_1,
                                        var_2_ws_1_3]
      and 
      (
        (
          examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
          and 
          (
            (
              examples_bstree_BinTreeCondition6[var_1_current_3]
              and 
              (
                nullDerefBool_11=true)
            )
            or 
            (
              (
                not (
                  examples_bstree_BinTreeCondition6[var_1_current_3])
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
            (
              examples_bstree_BinTreeCondition12[examples_bstree_Node_key_6,
                                                var_1_current_3,
                                                x_0]
              and 
              (
                (
                  examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
                  and 
                  (
                    (
                      examples_bstree_BinTreeCondition6[var_1_current_3]
                      and 
                      (
                        nullDerefBool_12=true)
                    )
                    or 
                    (
                      (
                        not (
                          examples_bstree_BinTreeCondition6[var_1_current_3])
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
                      examples_bstree_BinTreeCondition8[examples_bstree_Node_left_8,
                                                       var_1_current_3]
                      and 
                      TruePred[]
                      and 
                      (
                        (
                          examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
                          and 
                          getUnusedObject[es_var__2_3,
                                         usedObjects_3,
                                         usedObjects_4]
                          and 
                          instanceOf[es_var__2_3,
                                    examples_bstree_Node]
                          and 
                          examples_bstree_Node_Constructor_0[es_var__2_3,
                                                            throw_8,
                                                            throw_9,
                                                            x_0,
                                                            examples_bstree_Node_right_8,
                                                            examples_bstree_Node_right_9,
                                                            examples_bstree_Node_right_11,
                                                            examples_bstree_Node_key_6,
                                                            examples_bstree_Node_key_7,
                                                            examples_bstree_Node_key_8,
                                                            examples_bstree_Node_left_8,
                                                            examples_bstree_Node_left_9,
                                                            examples_bstree_Node_left_10,
                                                            l5_exit_stmt_reached_1,
                                                            l5_nullDerefBool_1,
                                                            l5_nullDerefBool_2,
                                                            l5_nullDerefBool_3,
                                                            l5_nullDerefBool_4,
                                                            l5_nullDerefBool_5,
                                                            l5_nullDerefBool_6,
                                                            l5_nullDerefBool_7]
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
                            es_var__2_2=es_var__2_3)
                          and 
                          (
                            throw_7=throw_9)
                          and 
                          (
                            examples_bstree_Node_right_8=examples_bstree_Node_right_11)
                          and 
                          (
                            l5_exit_stmt_reached_0=l5_exit_stmt_reached_1)
                          and 
                          (
                            l5_nullDerefBool_0=l5_nullDerefBool_7)
                          and 
                          (
                            examples_bstree_Node_key_6=examples_bstree_Node_key_8)
                          and 
                          (
                            examples_bstree_Node_left_8=examples_bstree_Node_left_10)
                          and 
                          (
                            usedObjects_3=usedObjects_4)
                        )
                      )
                      and 
                      (
                        (
                          examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
                          and 
                          (
                            (
                              examples_bstree_BinTreeCondition6[var_1_current_3]
                              and 
                              (
                                nullDerefBool_13=true)
                            )
                            or 
                            (
                              (
                                not (
                                  examples_bstree_BinTreeCondition6[var_1_current_3])
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
                            examples_bstree_Node_left_11=(examples_bstree_Node_left_10)++((var_1_current_3)->(es_var__2_3)))
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
                            nullDerefBool_12=nullDerefBool_13)
                          and 
                          (
                            examples_bstree_Node_left_10=examples_bstree_Node_left_11)
                        )
                      )
                      and 
                      (
                        var_1_current_3=var_1_current_4)
                    )
                    or 
                    (
                      (
                        not (
                          examples_bstree_BinTreeCondition8[examples_bstree_Node_left_8,
                                                           var_1_current_3]
                        )
                      )
                      and 
                      (
                        (
                          examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
                          and 
                          (
                            (
                              examples_bstree_BinTreeCondition6[var_1_current_3]
                              and 
                              (
                                nullDerefBool_13=true)
                            )
                            or 
                            (
                              (
                                not (
                                  examples_bstree_BinTreeCondition6[var_1_current_3])
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
                            var_1_current_4=var_1_current_3.examples_bstree_Node_left_8)
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
                            var_1_current_3=var_1_current_4)
                          and 
                          (
                            nullDerefBool_12=nullDerefBool_13)
                        )
                      )
                      and 
                      (
                        l5_exit_stmt_reached_0=l5_exit_stmt_reached_1)
                      and 
                      (
                        es_var__2_2=es_var__2_3)
                      and 
                      (
                        throw_7=throw_9)
                      and 
                      (
                        examples_bstree_Node_right_8=examples_bstree_Node_right_11)
                      and 
                      (
                        l5_nullDerefBool_0=l5_nullDerefBool_7)
                      and 
                      (
                        examples_bstree_Node_key_6=examples_bstree_Node_key_8)
                      and 
                      (
                        usedObjects_3=usedObjects_4)
                      and 
                      (
                        examples_bstree_Node_left_8=examples_bstree_Node_left_11)
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
                    l5_exit_stmt_reached_0=l5_exit_stmt_reached_1)
                  and 
                  (
                    nullDerefBool_11=nullDerefBool_13)
                  and 
                  (
                    es_var__2_2=es_var__2_3)
                  and 
                  (
                    throw_7=throw_9)
                  and 
                  (
                    examples_bstree_Node_right_8=examples_bstree_Node_right_11)
                  and 
                  (
                    var_1_current_3=var_1_current_4)
                  and 
                  (
                    l5_nullDerefBool_0=l5_nullDerefBool_7)
                  and 
                  (
                    examples_bstree_Node_key_6=examples_bstree_Node_key_8)
                  and 
                  (
                    examples_bstree_Node_left_8=examples_bstree_Node_left_11)
                  and 
                  (
                    usedObjects_3=usedObjects_4)
                )
              )
              and 
              (
                l6_exit_stmt_reached_0=l6_exit_stmt_reached_1)
              and 
              (
                es_var__3_2=es_var__3_3)
              and 
              (
                l6_nullDerefBool_0=l6_nullDerefBool_7)
            )
            or 
            (
              (
                not (
                  examples_bstree_BinTreeCondition12[examples_bstree_Node_key_6,
                                                    var_1_current_3,
                                                    x_0]
                )
              )
              and 
              (
                (
                  examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
                  and 
                  (
                    (
                      examples_bstree_BinTreeCondition6[var_1_current_3]
                      and 
                      (
                        nullDerefBool_12=true)
                    )
                    or 
                    (
                      (
                        not (
                          examples_bstree_BinTreeCondition6[var_1_current_3])
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
                      examples_bstree_BinTreeCondition10[examples_bstree_Node_right_8,
                                                        var_1_current_3]
                      and 
                      TruePred[]
                      and 
                      (
                        (
                          examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
                          and 
                          getUnusedObject[es_var__3_3,
                                         usedObjects_3,
                                         usedObjects_4]
                          and 
                          instanceOf[es_var__3_3,
                                    examples_bstree_Node]
                          and 
                          examples_bstree_Node_Constructor_0[es_var__3_3,
                                                            throw_8,
                                                            throw_9,
                                                            x_0,
                                                            examples_bstree_Node_right_8,
                                                            examples_bstree_Node_right_9,
                                                            examples_bstree_Node_right_10,
                                                            examples_bstree_Node_key_6,
                                                            examples_bstree_Node_key_7,
                                                            examples_bstree_Node_key_8,
                                                            examples_bstree_Node_left_8,
                                                            examples_bstree_Node_left_9,
                                                            examples_bstree_Node_left_11,
                                                            l6_exit_stmt_reached_1,
                                                            l6_nullDerefBool_1,
                                                            l6_nullDerefBool_2,
                                                            l6_nullDerefBool_3,
                                                            l6_nullDerefBool_4,
                                                            l6_nullDerefBool_5,
                                                            l6_nullDerefBool_6,
                                                            l6_nullDerefBool_7]
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
                            throw_7=throw_9)
                          and 
                          (
                            es_var__3_2=es_var__3_3)
                          and 
                          (
                            examples_bstree_Node_right_8=examples_bstree_Node_right_10)
                          and 
                          (
                            l6_exit_stmt_reached_0=l6_exit_stmt_reached_1)
                          and 
                          (
                            l6_nullDerefBool_0=l6_nullDerefBool_7)
                          and 
                          (
                            examples_bstree_Node_key_6=examples_bstree_Node_key_8)
                          and 
                          (
                            examples_bstree_Node_left_8=examples_bstree_Node_left_11)
                          and 
                          (
                            usedObjects_3=usedObjects_4)
                        )
                      )
                      and 
                      (
                        (
                          examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
                          and 
                          (
                            (
                              examples_bstree_BinTreeCondition6[var_1_current_3]
                              and 
                              (
                                nullDerefBool_13=true)
                            )
                            or 
                            (
                              (
                                not (
                                  examples_bstree_BinTreeCondition6[var_1_current_3])
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
                            examples_bstree_Node_right_11=(examples_bstree_Node_right_10)++((var_1_current_3)->(es_var__3_3)))
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
                            examples_bstree_Node_right_10=examples_bstree_Node_right_11)
                          and 
                          (
                            nullDerefBool_12=nullDerefBool_13)
                        )
                      )
                      and 
                      (
                        var_1_current_3=var_1_current_4)
                    )
                    or 
                    (
                      (
                        not (
                          examples_bstree_BinTreeCondition10[examples_bstree_Node_right_8,
                                                            var_1_current_3]
                        )
                      )
                      and 
                      (
                        (
                          examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
                          and 
                          (
                            (
                              examples_bstree_BinTreeCondition6[var_1_current_3]
                              and 
                              (
                                nullDerefBool_13=true)
                            )
                            or 
                            (
                              (
                                not (
                                  examples_bstree_BinTreeCondition6[var_1_current_3])
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
                            var_1_current_4=var_1_current_3.examples_bstree_Node_right_8)
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
                            var_1_current_3=var_1_current_4)
                          and 
                          (
                            nullDerefBool_12=nullDerefBool_13)
                        )
                      )
                      and 
                      (
                        l6_exit_stmt_reached_0=l6_exit_stmt_reached_1)
                      and 
                      (
                        throw_7=throw_9)
                      and 
                      (
                        es_var__3_2=es_var__3_3)
                      and 
                      (
                        l6_nullDerefBool_0=l6_nullDerefBool_7)
                      and 
                      (
                        examples_bstree_Node_key_6=examples_bstree_Node_key_8)
                      and 
                      (
                        examples_bstree_Node_left_8=examples_bstree_Node_left_11)
                      and 
                      (
                        usedObjects_3=usedObjects_4)
                      and 
                      (
                        examples_bstree_Node_right_8=examples_bstree_Node_right_11)
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
                    l6_exit_stmt_reached_0=l6_exit_stmt_reached_1)
                  and 
                  (
                    nullDerefBool_11=nullDerefBool_13)
                  and 
                  (
                    throw_7=throw_9)
                  and 
                  (
                    es_var__3_2=es_var__3_3)
                  and 
                  (
                    examples_bstree_Node_right_8=examples_bstree_Node_right_11)
                  and 
                  (
                    var_1_current_3=var_1_current_4)
                  and 
                  (
                    l6_nullDerefBool_0=l6_nullDerefBool_7)
                  and 
                  (
                    examples_bstree_Node_key_6=examples_bstree_Node_key_8)
                  and 
                  (
                    examples_bstree_Node_left_8=examples_bstree_Node_left_11)
                  and 
                  (
                    usedObjects_3=usedObjects_4)
                )
              )
              and 
              (
                l5_exit_stmt_reached_0=l5_exit_stmt_reached_1)
              and 
              (
                es_var__2_2=es_var__2_3)
              and 
              (
                l5_nullDerefBool_0=l5_nullDerefBool_7)
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
            l5_exit_stmt_reached_0=l5_exit_stmt_reached_1)
          and 
          (
            l6_exit_stmt_reached_0=l6_exit_stmt_reached_1)
          and 
          (
            nullDerefBool_10=nullDerefBool_13)
          and 
          (
            es_var__2_2=es_var__2_3)
          and 
          (
            es_var__3_2=es_var__3_3)
          and 
          (
            throw_7=throw_9)
          and 
          (
            examples_bstree_Node_right_8=examples_bstree_Node_right_11)
          and 
          (
            var_1_current_3=var_1_current_4)
          and 
          (
            l5_nullDerefBool_0=l5_nullDerefBool_7)
          and 
          (
            examples_bstree_Node_key_6=examples_bstree_Node_key_8)
          and 
          (
            l6_nullDerefBool_0=l6_nullDerefBool_7)
          and 
          (
            examples_bstree_Node_left_8=examples_bstree_Node_left_11)
          and 
          (
            usedObjects_3=usedObjects_4)
        )
      )
      and 
      (
        (
          examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
          and 
          (
            var_2_ws_1_4=(neq[var_1_current_4.examples_bstree_Node_key_8,
               x_0]=>(true)else(false))
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
            var_2_ws_1_3=var_2_ws_1_4)
        )
      )
    )
    or 
    (
      TruePred[]
      and 
      (
        l5_exit_stmt_reached_0=l5_exit_stmt_reached_1)
      and 
      (
        l6_exit_stmt_reached_0=l6_exit_stmt_reached_1)
      and 
      (
        nullDerefBool_10=nullDerefBool_13)
      and 
      (
        es_var__2_2=es_var__2_3)
      and 
      (
        es_var__3_2=es_var__3_3)
      and 
      (
        throw_7=throw_9)
      and 
      (
        examples_bstree_Node_right_8=examples_bstree_Node_right_11)
      and 
      (
        var_1_current_3=var_1_current_4)
      and 
      (
        l5_nullDerefBool_0=l5_nullDerefBool_7)
      and 
      (
        l6_nullDerefBool_0=l6_nullDerefBool_7)
      and 
      (
        examples_bstree_Node_key_6=examples_bstree_Node_key_8)
      and 
      (
        var_2_ws_1_3=var_2_ws_1_4)
      and 
      (
        examples_bstree_Node_left_8=examples_bstree_Node_left_11)
      and 
      (
        usedObjects_3=usedObjects_4)
    )
  )
  and 
  (
    (
      examples_bstree_BinTreeCondition14[exit_stmt_reached_1,
                                        var_2_ws_1_4]
      and 
      (
        (
          examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
          and 
          (
            (
              examples_bstree_BinTreeCondition6[var_1_current_4]
              and 
              (
                nullDerefBool_14=true)
            )
            or 
            (
              (
                not (
                  examples_bstree_BinTreeCondition6[var_1_current_4])
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
            (
              examples_bstree_BinTreeCondition12[examples_bstree_Node_key_8,
                                                var_1_current_4,
                                                x_0]
              and 
              (
                (
                  examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
                  and 
                  (
                    (
                      examples_bstree_BinTreeCondition6[var_1_current_4]
                      and 
                      (
                        nullDerefBool_15=true)
                    )
                    or 
                    (
                      (
                        not (
                          examples_bstree_BinTreeCondition6[var_1_current_4])
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
                      examples_bstree_BinTreeCondition8[examples_bstree_Node_left_11,
                                                       var_1_current_4]
                      and 
                      TruePred[]
                      and 
                      (
                        (
                          examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
                          and 
                          getUnusedObject[es_var__2_4,
                                         usedObjects_4,
                                         usedObjects_5]
                          and 
                          instanceOf[es_var__2_4,
                                    examples_bstree_Node]
                          and 
                          examples_bstree_Node_Constructor_0[es_var__2_4,
                                                            throw_10,
                                                            throw_11,
                                                            x_0,
                                                            examples_bstree_Node_right_11,
                                                            examples_bstree_Node_right_12,
                                                            examples_bstree_Node_right_14,
                                                            examples_bstree_Node_key_8,
                                                            examples_bstree_Node_key_9,
                                                            examples_bstree_Node_key_10,
                                                            examples_bstree_Node_left_11,
                                                            examples_bstree_Node_left_12,
                                                            examples_bstree_Node_left_13,
                                                            l7_exit_stmt_reached_1,
                                                            l7_nullDerefBool_1,
                                                            l7_nullDerefBool_2,
                                                            l7_nullDerefBool_3,
                                                            l7_nullDerefBool_4,
                                                            l7_nullDerefBool_5,
                                                            l7_nullDerefBool_6,
                                                            l7_nullDerefBool_7]
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
                            es_var__2_3=es_var__2_4)
                          and 
                          (
                            throw_9=throw_11)
                          and 
                          (
                            examples_bstree_Node_right_11=examples_bstree_Node_right_14)
                          and 
                          (
                            l7_nullDerefBool_0=l7_nullDerefBool_7)
                          and 
                          (
                            examples_bstree_Node_key_8=examples_bstree_Node_key_10)
                          and 
                          (
                            examples_bstree_Node_left_11=examples_bstree_Node_left_13)
                          and 
                          (
                            l7_exit_stmt_reached_0=l7_exit_stmt_reached_1)
                          and 
                          (
                            usedObjects_4=usedObjects_5)
                        )
                      )
                      and 
                      (
                        (
                          examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
                          and 
                          (
                            (
                              examples_bstree_BinTreeCondition6[var_1_current_4]
                              and 
                              (
                                nullDerefBool_16=true)
                            )
                            or 
                            (
                              (
                                not (
                                  examples_bstree_BinTreeCondition6[var_1_current_4])
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
                            examples_bstree_Node_left_14=(examples_bstree_Node_left_13)++((var_1_current_4)->(es_var__2_4)))
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
                            nullDerefBool_15=nullDerefBool_16)
                          and 
                          (
                            examples_bstree_Node_left_13=examples_bstree_Node_left_14)
                        )
                      )
                      and 
                      (
                        var_1_current_4=var_1_current_5)
                    )
                    or 
                    (
                      (
                        not (
                          examples_bstree_BinTreeCondition8[examples_bstree_Node_left_11,
                                                           var_1_current_4]
                        )
                      )
                      and 
                      (
                        (
                          examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
                          and 
                          (
                            (
                              examples_bstree_BinTreeCondition6[var_1_current_4]
                              and 
                              (
                                nullDerefBool_16=true)
                            )
                            or 
                            (
                              (
                                not (
                                  examples_bstree_BinTreeCondition6[var_1_current_4])
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
                            var_1_current_5=var_1_current_4.examples_bstree_Node_left_11)
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
                            var_1_current_4=var_1_current_5)
                          and 
                          (
                            nullDerefBool_15=nullDerefBool_16)
                        )
                      )
                      and 
                      (
                        l7_exit_stmt_reached_0=l7_exit_stmt_reached_1)
                      and 
                      (
                        es_var__2_3=es_var__2_4)
                      and 
                      (
                        throw_9=throw_11)
                      and 
                      (
                        examples_bstree_Node_right_11=examples_bstree_Node_right_14)
                      and 
                      (
                        l7_nullDerefBool_0=l7_nullDerefBool_7)
                      and 
                      (
                        examples_bstree_Node_key_8=examples_bstree_Node_key_10)
                      and 
                      (
                        usedObjects_4=usedObjects_5)
                      and 
                      (
                        examples_bstree_Node_left_11=examples_bstree_Node_left_14)
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
                    nullDerefBool_14=nullDerefBool_16)
                  and 
                  (
                    l7_exit_stmt_reached_0=l7_exit_stmt_reached_1)
                  and 
                  (
                    es_var__2_3=es_var__2_4)
                  and 
                  (
                    throw_9=throw_11)
                  and 
                  (
                    examples_bstree_Node_right_11=examples_bstree_Node_right_14)
                  and 
                  (
                    l7_nullDerefBool_0=l7_nullDerefBool_7)
                  and 
                  (
                    var_1_current_4=var_1_current_5)
                  and 
                  (
                    examples_bstree_Node_key_8=examples_bstree_Node_key_10)
                  and 
                  (
                    examples_bstree_Node_left_11=examples_bstree_Node_left_14)
                  and 
                  (
                    usedObjects_4=usedObjects_5)
                )
              )
              and 
              (
                l8_nullDerefBool_0=l8_nullDerefBool_7)
              and 
              (
                l8_exit_stmt_reached_0=l8_exit_stmt_reached_1)
              and 
              (
                es_var__3_3=es_var__3_4)
            )
            or 
            (
              (
                not (
                  examples_bstree_BinTreeCondition12[examples_bstree_Node_key_8,
                                                    var_1_current_4,
                                                    x_0]
                )
              )
              and 
              (
                (
                  examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
                  and 
                  (
                    (
                      examples_bstree_BinTreeCondition6[var_1_current_4]
                      and 
                      (
                        nullDerefBool_15=true)
                    )
                    or 
                    (
                      (
                        not (
                          examples_bstree_BinTreeCondition6[var_1_current_4])
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
                      examples_bstree_BinTreeCondition10[examples_bstree_Node_right_11,
                                                        var_1_current_4]
                      and 
                      TruePred[]
                      and 
                      (
                        (
                          examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
                          and 
                          getUnusedObject[es_var__3_4,
                                         usedObjects_4,
                                         usedObjects_5]
                          and 
                          instanceOf[es_var__3_4,
                                    examples_bstree_Node]
                          and 
                          examples_bstree_Node_Constructor_0[es_var__3_4,
                                                            throw_10,
                                                            throw_11,
                                                            x_0,
                                                            examples_bstree_Node_right_11,
                                                            examples_bstree_Node_right_12,
                                                            examples_bstree_Node_right_13,
                                                            examples_bstree_Node_key_8,
                                                            examples_bstree_Node_key_9,
                                                            examples_bstree_Node_key_10,
                                                            examples_bstree_Node_left_11,
                                                            examples_bstree_Node_left_12,
                                                            examples_bstree_Node_left_14,
                                                            l8_exit_stmt_reached_1,
                                                            l8_nullDerefBool_1,
                                                            l8_nullDerefBool_2,
                                                            l8_nullDerefBool_3,
                                                            l8_nullDerefBool_4,
                                                            l8_nullDerefBool_5,
                                                            l8_nullDerefBool_6,
                                                            l8_nullDerefBool_7]
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
                            throw_9=throw_11)
                          and 
                          (
                            l8_exit_stmt_reached_0=l8_exit_stmt_reached_1)
                          and 
                          (
                            es_var__3_3=es_var__3_4)
                          and 
                          (
                            l8_nullDerefBool_0=l8_nullDerefBool_7)
                          and 
                          (
                            examples_bstree_Node_right_11=examples_bstree_Node_right_13)
                          and 
                          (
                            examples_bstree_Node_key_8=examples_bstree_Node_key_10)
                          and 
                          (
                            examples_bstree_Node_left_11=examples_bstree_Node_left_14)
                          and 
                          (
                            usedObjects_4=usedObjects_5)
                        )
                      )
                      and 
                      (
                        (
                          examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
                          and 
                          (
                            (
                              examples_bstree_BinTreeCondition6[var_1_current_4]
                              and 
                              (
                                nullDerefBool_16=true)
                            )
                            or 
                            (
                              (
                                not (
                                  examples_bstree_BinTreeCondition6[var_1_current_4])
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
                            examples_bstree_Node_right_14=(examples_bstree_Node_right_13)++((var_1_current_4)->(es_var__3_4)))
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
                            examples_bstree_Node_right_13=examples_bstree_Node_right_14)
                          and 
                          (
                            nullDerefBool_15=nullDerefBool_16)
                        )
                      )
                      and 
                      (
                        var_1_current_4=var_1_current_5)
                    )
                    or 
                    (
                      (
                        not (
                          examples_bstree_BinTreeCondition10[examples_bstree_Node_right_11,
                                                            var_1_current_4]
                        )
                      )
                      and 
                      (
                        (
                          examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
                          and 
                          (
                            (
                              examples_bstree_BinTreeCondition6[var_1_current_4]
                              and 
                              (
                                nullDerefBool_16=true)
                            )
                            or 
                            (
                              (
                                not (
                                  examples_bstree_BinTreeCondition6[var_1_current_4])
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
                            var_1_current_5=var_1_current_4.examples_bstree_Node_right_11)
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
                            var_1_current_4=var_1_current_5)
                          and 
                          (
                            nullDerefBool_15=nullDerefBool_16)
                        )
                      )
                      and 
                      (
                        l8_nullDerefBool_0=l8_nullDerefBool_7)
                      and 
                      (
                        throw_9=throw_11)
                      and 
                      (
                        l8_exit_stmt_reached_0=l8_exit_stmt_reached_1)
                      and 
                      (
                        es_var__3_3=es_var__3_4)
                      and 
                      (
                        examples_bstree_Node_key_8=examples_bstree_Node_key_10)
                      and 
                      (
                        examples_bstree_Node_left_11=examples_bstree_Node_left_14)
                      and 
                      (
                        usedObjects_4=usedObjects_5)
                      and 
                      (
                        examples_bstree_Node_right_11=examples_bstree_Node_right_14)
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
                    l8_nullDerefBool_0=l8_nullDerefBool_7)
                  and 
                  (
                    nullDerefBool_14=nullDerefBool_16)
                  and 
                  (
                    throw_9=throw_11)
                  and 
                  (
                    l8_exit_stmt_reached_0=l8_exit_stmt_reached_1)
                  and 
                  (
                    es_var__3_3=es_var__3_4)
                  and 
                  (
                    examples_bstree_Node_right_11=examples_bstree_Node_right_14)
                  and 
                  (
                    var_1_current_4=var_1_current_5)
                  and 
                  (
                    examples_bstree_Node_key_8=examples_bstree_Node_key_10)
                  and 
                  (
                    examples_bstree_Node_left_11=examples_bstree_Node_left_14)
                  and 
                  (
                    usedObjects_4=usedObjects_5)
                )
              )
              and 
              (
                l7_exit_stmt_reached_0=l7_exit_stmt_reached_1)
              and 
              (
                es_var__2_3=es_var__2_4)
              and 
              (
                l7_nullDerefBool_0=l7_nullDerefBool_7)
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
            l8_nullDerefBool_0=l8_nullDerefBool_7)
          and 
          (
            nullDerefBool_13=nullDerefBool_16)
          and 
          (
            l7_exit_stmt_reached_0=l7_exit_stmt_reached_1)
          and 
          (
            es_var__2_3=es_var__2_4)
          and 
          (
            es_var__3_3=es_var__3_4)
          and 
          (
            l8_exit_stmt_reached_0=l8_exit_stmt_reached_1)
          and 
          (
            throw_9=throw_11)
          and 
          (
            examples_bstree_Node_right_11=examples_bstree_Node_right_14)
          and 
          (
            l7_nullDerefBool_0=l7_nullDerefBool_7)
          and 
          (
            var_1_current_4=var_1_current_5)
          and 
          (
            examples_bstree_Node_key_8=examples_bstree_Node_key_10)
          and 
          (
            examples_bstree_Node_left_11=examples_bstree_Node_left_14)
          and 
          (
            usedObjects_4=usedObjects_5)
        )
      )
      and 
      (
        (
          examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
          and 
          (
            var_2_ws_1_5=(neq[var_1_current_5.examples_bstree_Node_key_10,
               x_0]=>(true)else(false))
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
            var_2_ws_1_4=var_2_ws_1_5)
        )
      )
    )
    or 
    (
      TruePred[]
      and 
      (
        l8_nullDerefBool_0=l8_nullDerefBool_7)
      and 
      (
        nullDerefBool_13=nullDerefBool_16)
      and 
      (
        l7_exit_stmt_reached_0=l7_exit_stmt_reached_1)
      and 
      (
        es_var__2_3=es_var__2_4)
      and 
      (
        es_var__3_3=es_var__3_4)
      and 
      (
        l8_exit_stmt_reached_0=l8_exit_stmt_reached_1)
      and 
      (
        throw_9=throw_11)
      and 
      (
        examples_bstree_Node_right_11=examples_bstree_Node_right_14)
      and 
      (
        l7_nullDerefBool_0=l7_nullDerefBool_7)
      and 
      (
        var_1_current_4=var_1_current_5)
      and 
      (
        examples_bstree_Node_key_8=examples_bstree_Node_key_10)
      and 
      (
        var_2_ws_1_4=var_2_ws_1_5)
      and 
      (
        examples_bstree_Node_left_11=examples_bstree_Node_left_14)
      and 
      (
        usedObjects_4=usedObjects_5)
    )
  )
  and 
  (
    (
      examples_bstree_BinTreeCondition14[exit_stmt_reached_1,
                                        var_2_ws_1_5]
      and 
      (
        (
          examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
          and 
          (
            (
              examples_bstree_BinTreeCondition6[var_1_current_5]
              and 
              (
                nullDerefBool_17=true)
            )
            or 
            (
              (
                not (
                  examples_bstree_BinTreeCondition6[var_1_current_5])
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
            (
              examples_bstree_BinTreeCondition12[examples_bstree_Node_key_10,
                                                var_1_current_5,
                                                x_0]
              and 
              (
                (
                  examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
                  and 
                  (
                    (
                      examples_bstree_BinTreeCondition6[var_1_current_5]
                      and 
                      (
                        nullDerefBool_18=true)
                    )
                    or 
                    (
                      (
                        not (
                          examples_bstree_BinTreeCondition6[var_1_current_5])
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
                      examples_bstree_BinTreeCondition8[examples_bstree_Node_left_14,
                                                       var_1_current_5]
                      and 
                      TruePred[]
                      and 
                      (
                        (
                          examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
                          and 
                          getUnusedObject[es_var__2_5,
                                         usedObjects_5,
                                         usedObjects_6]
                          and 
                          instanceOf[es_var__2_5,
                                    examples_bstree_Node]
                          and 
                          examples_bstree_Node_Constructor_0[es_var__2_5,
                                                            throw_12,
                                                            throw_13,
                                                            x_0,
                                                            examples_bstree_Node_right_14,
                                                            examples_bstree_Node_right_15,
                                                            examples_bstree_Node_right_17,
                                                            examples_bstree_Node_key_10,
                                                            examples_bstree_Node_key_11,
                                                            examples_bstree_Node_key_12,
                                                            examples_bstree_Node_left_14,
                                                            examples_bstree_Node_left_15,
                                                            examples_bstree_Node_left_16,
                                                            l9_exit_stmt_reached_1,
                                                            l9_nullDerefBool_1,
                                                            l9_nullDerefBool_2,
                                                            l9_nullDerefBool_3,
                                                            l9_nullDerefBool_4,
                                                            l9_nullDerefBool_5,
                                                            l9_nullDerefBool_6,
                                                            l9_nullDerefBool_7]
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
                            es_var__2_4=es_var__2_5)
                          and 
                          (
                            throw_11=throw_13)
                          and 
                          (
                            l9_exit_stmt_reached_0=l9_exit_stmt_reached_1)
                          and 
                          (
                            examples_bstree_Node_right_14=examples_bstree_Node_right_17)
                          and 
                          (
                            l9_nullDerefBool_0=l9_nullDerefBool_7)
                          and 
                          (
                            examples_bstree_Node_key_10=examples_bstree_Node_key_12)
                          and 
                          (
                            examples_bstree_Node_left_14=examples_bstree_Node_left_16)
                          and 
                          (
                            usedObjects_5=usedObjects_6)
                        )
                      )
                      and 
                      (
                        (
                          examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
                          and 
                          (
                            (
                              examples_bstree_BinTreeCondition6[var_1_current_5]
                              and 
                              (
                                nullDerefBool_19=true)
                            )
                            or 
                            (
                              (
                                not (
                                  examples_bstree_BinTreeCondition6[var_1_current_5])
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
                            examples_bstree_Node_left_17=(examples_bstree_Node_left_16)++((var_1_current_5)->(es_var__2_5)))
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
                            nullDerefBool_18=nullDerefBool_19)
                          and 
                          (
                            examples_bstree_Node_left_16=examples_bstree_Node_left_17)
                        )
                      )
                      and 
                      (
                        var_1_current_5=var_1_current_6)
                    )
                    or 
                    (
                      (
                        not (
                          examples_bstree_BinTreeCondition8[examples_bstree_Node_left_14,
                                                           var_1_current_5]
                        )
                      )
                      and 
                      (
                        (
                          examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
                          and 
                          (
                            (
                              examples_bstree_BinTreeCondition6[var_1_current_5]
                              and 
                              (
                                nullDerefBool_19=true)
                            )
                            or 
                            (
                              (
                                not (
                                  examples_bstree_BinTreeCondition6[var_1_current_5])
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
                            var_1_current_6=var_1_current_5.examples_bstree_Node_left_14)
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
                            var_1_current_5=var_1_current_6)
                          and 
                          (
                            nullDerefBool_18=nullDerefBool_19)
                        )
                      )
                      and 
                      (
                        l9_exit_stmt_reached_0=l9_exit_stmt_reached_1)
                      and 
                      (
                        es_var__2_4=es_var__2_5)
                      and 
                      (
                        throw_11=throw_13)
                      and 
                      (
                        examples_bstree_Node_right_14=examples_bstree_Node_right_17)
                      and 
                      (
                        l9_nullDerefBool_0=l9_nullDerefBool_7)
                      and 
                      (
                        examples_bstree_Node_key_10=examples_bstree_Node_key_12)
                      and 
                      (
                        usedObjects_5=usedObjects_6)
                      and 
                      (
                        examples_bstree_Node_left_14=examples_bstree_Node_left_17)
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
                    l9_exit_stmt_reached_0=l9_exit_stmt_reached_1)
                  and 
                  (
                    nullDerefBool_17=nullDerefBool_19)
                  and 
                  (
                    es_var__2_4=es_var__2_5)
                  and 
                  (
                    throw_11=throw_13)
                  and 
                  (
                    examples_bstree_Node_right_14=examples_bstree_Node_right_17)
                  and 
                  (
                    var_1_current_5=var_1_current_6)
                  and 
                  (
                    l9_nullDerefBool_0=l9_nullDerefBool_7)
                  and 
                  (
                    examples_bstree_Node_key_10=examples_bstree_Node_key_12)
                  and 
                  (
                    examples_bstree_Node_left_14=examples_bstree_Node_left_17)
                  and 
                  (
                    usedObjects_5=usedObjects_6)
                )
              )
              and 
              (
                es_var__3_4=es_var__3_5)
              and 
              (
                l10_exit_stmt_reached_0=l10_exit_stmt_reached_1)
              and 
              (
                l10_nullDerefBool_0=l10_nullDerefBool_7)
            )
            or 
            (
              (
                not (
                  examples_bstree_BinTreeCondition12[examples_bstree_Node_key_10,
                                                    var_1_current_5,
                                                    x_0]
                )
              )
              and 
              (
                (
                  examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
                  and 
                  (
                    (
                      examples_bstree_BinTreeCondition6[var_1_current_5]
                      and 
                      (
                        nullDerefBool_18=true)
                    )
                    or 
                    (
                      (
                        not (
                          examples_bstree_BinTreeCondition6[var_1_current_5])
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
                      examples_bstree_BinTreeCondition10[examples_bstree_Node_right_14,
                                                        var_1_current_5]
                      and 
                      TruePred[]
                      and 
                      (
                        (
                          examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
                          and 
                          getUnusedObject[es_var__3_5,
                                         usedObjects_5,
                                         usedObjects_6]
                          and 
                          instanceOf[es_var__3_5,
                                    examples_bstree_Node]
                          and 
                          examples_bstree_Node_Constructor_0[es_var__3_5,
                                                            throw_12,
                                                            throw_13,
                                                            x_0,
                                                            examples_bstree_Node_right_14,
                                                            examples_bstree_Node_right_15,
                                                            examples_bstree_Node_right_16,
                                                            examples_bstree_Node_key_10,
                                                            examples_bstree_Node_key_11,
                                                            examples_bstree_Node_key_12,
                                                            examples_bstree_Node_left_14,
                                                            examples_bstree_Node_left_15,
                                                            examples_bstree_Node_left_17,
                                                            l10_exit_stmt_reached_1,
                                                            l10_nullDerefBool_1,
                                                            l10_nullDerefBool_2,
                                                            l10_nullDerefBool_3,
                                                            l10_nullDerefBool_4,
                                                            l10_nullDerefBool_5,
                                                            l10_nullDerefBool_6,
                                                            l10_nullDerefBool_7]
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
                            throw_11=throw_13)
                          and 
                          (
                            es_var__3_4=es_var__3_5)
                          and 
                          (
                            examples_bstree_Node_right_14=examples_bstree_Node_right_16)
                          and 
                          (
                            l10_exit_stmt_reached_0=l10_exit_stmt_reached_1)
                          and 
                          (
                            l10_nullDerefBool_0=l10_nullDerefBool_7)
                          and 
                          (
                            examples_bstree_Node_key_10=examples_bstree_Node_key_12)
                          and 
                          (
                            examples_bstree_Node_left_14=examples_bstree_Node_left_17)
                          and 
                          (
                            usedObjects_5=usedObjects_6)
                        )
                      )
                      and 
                      (
                        (
                          examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
                          and 
                          (
                            (
                              examples_bstree_BinTreeCondition6[var_1_current_5]
                              and 
                              (
                                nullDerefBool_19=true)
                            )
                            or 
                            (
                              (
                                not (
                                  examples_bstree_BinTreeCondition6[var_1_current_5])
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
                            examples_bstree_Node_right_17=(examples_bstree_Node_right_16)++((var_1_current_5)->(es_var__3_5)))
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
                            examples_bstree_Node_right_16=examples_bstree_Node_right_17)
                          and 
                          (
                            nullDerefBool_18=nullDerefBool_19)
                        )
                      )
                      and 
                      (
                        var_1_current_5=var_1_current_6)
                    )
                    or 
                    (
                      (
                        not (
                          examples_bstree_BinTreeCondition10[examples_bstree_Node_right_14,
                                                            var_1_current_5]
                        )
                      )
                      and 
                      (
                        (
                          examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
                          and 
                          (
                            (
                              examples_bstree_BinTreeCondition6[var_1_current_5]
                              and 
                              (
                                nullDerefBool_19=true)
                            )
                            or 
                            (
                              (
                                not (
                                  examples_bstree_BinTreeCondition6[var_1_current_5])
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
                            var_1_current_6=var_1_current_5.examples_bstree_Node_right_14)
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
                            var_1_current_5=var_1_current_6)
                          and 
                          (
                            nullDerefBool_18=nullDerefBool_19)
                        )
                      )
                      and 
                      (
                        throw_11=throw_13)
                      and 
                      (
                        es_var__3_4=es_var__3_5)
                      and 
                      (
                        l10_exit_stmt_reached_0=l10_exit_stmt_reached_1)
                      and 
                      (
                        l10_nullDerefBool_0=l10_nullDerefBool_7)
                      and 
                      (
                        examples_bstree_Node_key_10=examples_bstree_Node_key_12)
                      and 
                      (
                        examples_bstree_Node_left_14=examples_bstree_Node_left_17)
                      and 
                      (
                        usedObjects_5=usedObjects_6)
                      and 
                      (
                        examples_bstree_Node_right_14=examples_bstree_Node_right_17)
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
                    nullDerefBool_17=nullDerefBool_19)
                  and 
                  (
                    throw_11=throw_13)
                  and 
                  (
                    es_var__3_4=es_var__3_5)
                  and 
                  (
                    examples_bstree_Node_right_14=examples_bstree_Node_right_17)
                  and 
                  (
                    l10_exit_stmt_reached_0=l10_exit_stmt_reached_1)
                  and 
                  (
                    var_1_current_5=var_1_current_6)
                  and 
                  (
                    l10_nullDerefBool_0=l10_nullDerefBool_7)
                  and 
                  (
                    examples_bstree_Node_key_10=examples_bstree_Node_key_12)
                  and 
                  (
                    examples_bstree_Node_left_14=examples_bstree_Node_left_17)
                  and 
                  (
                    usedObjects_5=usedObjects_6)
                )
              )
              and 
              (
                l9_exit_stmt_reached_0=l9_exit_stmt_reached_1)
              and 
              (
                es_var__2_4=es_var__2_5)
              and 
              (
                l9_nullDerefBool_0=l9_nullDerefBool_7)
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
            l9_exit_stmt_reached_0=l9_exit_stmt_reached_1)
          and 
          (
            nullDerefBool_16=nullDerefBool_19)
          and 
          (
            es_var__2_4=es_var__2_5)
          and 
          (
            es_var__3_4=es_var__3_5)
          and 
          (
            throw_11=throw_13)
          and 
          (
            examples_bstree_Node_right_14=examples_bstree_Node_right_17)
          and 
          (
            l10_exit_stmt_reached_0=l10_exit_stmt_reached_1)
          and 
          (
            var_1_current_5=var_1_current_6)
          and 
          (
            l10_nullDerefBool_0=l10_nullDerefBool_7)
          and 
          (
            l9_nullDerefBool_0=l9_nullDerefBool_7)
          and 
          (
            examples_bstree_Node_key_10=examples_bstree_Node_key_12)
          and 
          (
            examples_bstree_Node_left_14=examples_bstree_Node_left_17)
          and 
          (
            usedObjects_5=usedObjects_6)
        )
      )
      and 
      (
        (
          examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
          and 
          (
            var_2_ws_1_6=(neq[var_1_current_6.examples_bstree_Node_key_12,
               x_0]=>(true)else(false))
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
            var_2_ws_1_5=var_2_ws_1_6)
        )
      )
    )
    or 
    (
      TruePred[]
      and 
      (
        l9_exit_stmt_reached_0=l9_exit_stmt_reached_1)
      and 
      (
        nullDerefBool_16=nullDerefBool_19)
      and 
      (
        es_var__2_4=es_var__2_5)
      and 
      (
        es_var__3_4=es_var__3_5)
      and 
      (
        throw_11=throw_13)
      and 
      (
        examples_bstree_Node_right_14=examples_bstree_Node_right_17)
      and 
      (
        l10_exit_stmt_reached_0=l10_exit_stmt_reached_1)
      and 
      (
        var_1_current_5=var_1_current_6)
      and 
      (
        l10_nullDerefBool_0=l10_nullDerefBool_7)
      and 
      (
        l9_nullDerefBool_0=l9_nullDerefBool_7)
      and 
      (
        examples_bstree_Node_key_10=examples_bstree_Node_key_12)
      and 
      (
        var_2_ws_1_5=var_2_ws_1_6)
      and 
      (
        examples_bstree_Node_left_14=examples_bstree_Node_left_17)
      and 
      (
        usedObjects_5=usedObjects_6)
    )
  )
  and 
  (
    (
      examples_bstree_BinTreeCondition14[exit_stmt_reached_1,
                                        var_2_ws_1_6]
      and 
      (
        (
          examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
          and 
          (
            (
              examples_bstree_BinTreeCondition6[var_1_current_6]
              and 
              (
                nullDerefBool_20=true)
            )
            or 
            (
              (
                not (
                  examples_bstree_BinTreeCondition6[var_1_current_6])
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
            (
              examples_bstree_BinTreeCondition12[examples_bstree_Node_key_12,
                                                var_1_current_6,
                                                x_0]
              and 
              (
                (
                  examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
                  and 
                  (
                    (
                      examples_bstree_BinTreeCondition6[var_1_current_6]
                      and 
                      (
                        nullDerefBool_21=true)
                    )
                    or 
                    (
                      (
                        not (
                          examples_bstree_BinTreeCondition6[var_1_current_6])
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
                      examples_bstree_BinTreeCondition8[examples_bstree_Node_left_17,
                                                       var_1_current_6]
                      and 
                      TruePred[]
                      and 
                      (
                        (
                          examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
                          and 
                          getUnusedObject[es_var__2_6,
                                         usedObjects_6,
                                         usedObjects_7]
                          and 
                          instanceOf[es_var__2_6,
                                    examples_bstree_Node]
                          and 
                          examples_bstree_Node_Constructor_0[es_var__2_6,
                                                            throw_14,
                                                            throw_15,
                                                            x_0,
                                                            examples_bstree_Node_right_17,
                                                            examples_bstree_Node_right_18,
                                                            examples_bstree_Node_right_20,
                                                            examples_bstree_Node_key_12,
                                                            examples_bstree_Node_key_13,
                                                            examples_bstree_Node_key_14,
                                                            examples_bstree_Node_left_17,
                                                            examples_bstree_Node_left_18,
                                                            examples_bstree_Node_left_19,
                                                            l11_exit_stmt_reached_1,
                                                            l11_nullDerefBool_1,
                                                            l11_nullDerefBool_2,
                                                            l11_nullDerefBool_3,
                                                            l11_nullDerefBool_4,
                                                            l11_nullDerefBool_5,
                                                            l11_nullDerefBool_6,
                                                            l11_nullDerefBool_7]
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
                            es_var__2_5=es_var__2_6)
                          and 
                          (
                            throw_13=throw_15)
                          and 
                          (
                            examples_bstree_Node_right_17=examples_bstree_Node_right_20)
                          and 
                          (
                            l11_nullDerefBool_0=l11_nullDerefBool_7)
                          and 
                          (
                            l11_exit_stmt_reached_0=l11_exit_stmt_reached_1)
                          and 
                          (
                            examples_bstree_Node_key_12=examples_bstree_Node_key_14)
                          and 
                          (
                            examples_bstree_Node_left_17=examples_bstree_Node_left_19)
                          and 
                          (
                            usedObjects_6=usedObjects_7)
                        )
                      )
                      and 
                      (
                        (
                          examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
                          and 
                          (
                            (
                              examples_bstree_BinTreeCondition6[var_1_current_6]
                              and 
                              (
                                nullDerefBool_22=true)
                            )
                            or 
                            (
                              (
                                not (
                                  examples_bstree_BinTreeCondition6[var_1_current_6])
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
                            examples_bstree_Node_left_20=(examples_bstree_Node_left_19)++((var_1_current_6)->(es_var__2_6)))
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
                            nullDerefBool_21=nullDerefBool_22)
                          and 
                          (
                            examples_bstree_Node_left_19=examples_bstree_Node_left_20)
                        )
                      )
                      and 
                      (
                        var_1_current_6=var_1_current_7)
                    )
                    or 
                    (
                      (
                        not (
                          examples_bstree_BinTreeCondition8[examples_bstree_Node_left_17,
                                                           var_1_current_6]
                        )
                      )
                      and 
                      (
                        (
                          examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
                          and 
                          (
                            (
                              examples_bstree_BinTreeCondition6[var_1_current_6]
                              and 
                              (
                                nullDerefBool_22=true)
                            )
                            or 
                            (
                              (
                                not (
                                  examples_bstree_BinTreeCondition6[var_1_current_6])
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
                            var_1_current_7=var_1_current_6.examples_bstree_Node_left_17)
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
                            var_1_current_6=var_1_current_7)
                          and 
                          (
                            nullDerefBool_21=nullDerefBool_22)
                        )
                      )
                      and 
                      (
                        l11_nullDerefBool_0=l11_nullDerefBool_7)
                      and 
                      (
                        es_var__2_5=es_var__2_6)
                      and 
                      (
                        throw_13=throw_15)
                      and 
                      (
                        examples_bstree_Node_right_17=examples_bstree_Node_right_20)
                      and 
                      (
                        l11_exit_stmt_reached_0=l11_exit_stmt_reached_1)
                      and 
                      (
                        examples_bstree_Node_key_12=examples_bstree_Node_key_14)
                      and 
                      (
                        usedObjects_6=usedObjects_7)
                      and 
                      (
                        examples_bstree_Node_left_17=examples_bstree_Node_left_20)
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
                    l11_nullDerefBool_0=l11_nullDerefBool_7)
                  and 
                  (
                    nullDerefBool_20=nullDerefBool_22)
                  and 
                  (
                    es_var__2_5=es_var__2_6)
                  and 
                  (
                    throw_13=throw_15)
                  and 
                  (
                    examples_bstree_Node_right_17=examples_bstree_Node_right_20)
                  and 
                  (
                    var_1_current_6=var_1_current_7)
                  and 
                  (
                    l11_exit_stmt_reached_0=l11_exit_stmt_reached_1)
                  and 
                  (
                    examples_bstree_Node_key_12=examples_bstree_Node_key_14)
                  and 
                  (
                    examples_bstree_Node_left_17=examples_bstree_Node_left_20)
                  and 
                  (
                    usedObjects_6=usedObjects_7)
                )
              )
              and 
              (
                l12_nullDerefBool_0=l12_nullDerefBool_7)
              and 
              (
                l12_exit_stmt_reached_0=l12_exit_stmt_reached_1)
              and 
              (
                es_var__3_5=es_var__3_6)
            )
            or 
            (
              (
                not (
                  examples_bstree_BinTreeCondition12[examples_bstree_Node_key_12,
                                                    var_1_current_6,
                                                    x_0]
                )
              )
              and 
              (
                (
                  examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
                  and 
                  (
                    (
                      examples_bstree_BinTreeCondition6[var_1_current_6]
                      and 
                      (
                        nullDerefBool_21=true)
                    )
                    or 
                    (
                      (
                        not (
                          examples_bstree_BinTreeCondition6[var_1_current_6])
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
                      examples_bstree_BinTreeCondition10[examples_bstree_Node_right_17,
                                                        var_1_current_6]
                      and 
                      TruePred[]
                      and 
                      (
                        (
                          examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
                          and 
                          getUnusedObject[es_var__3_6,
                                         usedObjects_6,
                                         usedObjects_7]
                          and 
                          instanceOf[es_var__3_6,
                                    examples_bstree_Node]
                          and 
                          examples_bstree_Node_Constructor_0[es_var__3_6,
                                                            throw_14,
                                                            throw_15,
                                                            x_0,
                                                            examples_bstree_Node_right_17,
                                                            examples_bstree_Node_right_18,
                                                            examples_bstree_Node_right_19,
                                                            examples_bstree_Node_key_12,
                                                            examples_bstree_Node_key_13,
                                                            examples_bstree_Node_key_14,
                                                            examples_bstree_Node_left_17,
                                                            examples_bstree_Node_left_18,
                                                            examples_bstree_Node_left_20,
                                                            l12_exit_stmt_reached_1,
                                                            l12_nullDerefBool_1,
                                                            l12_nullDerefBool_2,
                                                            l12_nullDerefBool_3,
                                                            l12_nullDerefBool_4,
                                                            l12_nullDerefBool_5,
                                                            l12_nullDerefBool_6,
                                                            l12_nullDerefBool_7]
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
                            throw_13=throw_15)
                          and 
                          (
                            es_var__3_5=es_var__3_6)
                          and 
                          (
                            examples_bstree_Node_right_17=examples_bstree_Node_right_19)
                          and 
                          (
                            l12_nullDerefBool_0=l12_nullDerefBool_7)
                          and 
                          (
                            examples_bstree_Node_key_12=examples_bstree_Node_key_14)
                          and 
                          (
                            examples_bstree_Node_left_17=examples_bstree_Node_left_20)
                          and 
                          (
                            usedObjects_6=usedObjects_7)
                          and 
                          (
                            l12_exit_stmt_reached_0=l12_exit_stmt_reached_1)
                        )
                      )
                      and 
                      (
                        (
                          examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
                          and 
                          (
                            (
                              examples_bstree_BinTreeCondition6[var_1_current_6]
                              and 
                              (
                                nullDerefBool_22=true)
                            )
                            or 
                            (
                              (
                                not (
                                  examples_bstree_BinTreeCondition6[var_1_current_6])
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
                            examples_bstree_Node_right_20=(examples_bstree_Node_right_19)++((var_1_current_6)->(es_var__3_6)))
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
                            examples_bstree_Node_right_19=examples_bstree_Node_right_20)
                          and 
                          (
                            nullDerefBool_21=nullDerefBool_22)
                        )
                      )
                      and 
                      (
                        var_1_current_6=var_1_current_7)
                    )
                    or 
                    (
                      (
                        not (
                          examples_bstree_BinTreeCondition10[examples_bstree_Node_right_17,
                                                            var_1_current_6]
                        )
                      )
                      and 
                      (
                        (
                          examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
                          and 
                          (
                            (
                              examples_bstree_BinTreeCondition6[var_1_current_6]
                              and 
                              (
                                nullDerefBool_22=true)
                            )
                            or 
                            (
                              (
                                not (
                                  examples_bstree_BinTreeCondition6[var_1_current_6])
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
                            var_1_current_7=var_1_current_6.examples_bstree_Node_right_17)
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
                            var_1_current_6=var_1_current_7)
                          and 
                          (
                            nullDerefBool_21=nullDerefBool_22)
                        )
                      )
                      and 
                      (
                        l12_nullDerefBool_0=l12_nullDerefBool_7)
                      and 
                      (
                        l12_exit_stmt_reached_0=l12_exit_stmt_reached_1)
                      and 
                      (
                        throw_13=throw_15)
                      and 
                      (
                        es_var__3_5=es_var__3_6)
                      and 
                      (
                        examples_bstree_Node_key_12=examples_bstree_Node_key_14)
                      and 
                      (
                        examples_bstree_Node_left_17=examples_bstree_Node_left_20)
                      and 
                      (
                        usedObjects_6=usedObjects_7)
                      and 
                      (
                        examples_bstree_Node_right_17=examples_bstree_Node_right_20)
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
                    l12_nullDerefBool_0=l12_nullDerefBool_7)
                  and 
                  (
                    nullDerefBool_20=nullDerefBool_22)
                  and 
                  (
                    l12_exit_stmt_reached_0=l12_exit_stmt_reached_1)
                  and 
                  (
                    throw_13=throw_15)
                  and 
                  (
                    es_var__3_5=es_var__3_6)
                  and 
                  (
                    examples_bstree_Node_right_17=examples_bstree_Node_right_20)
                  and 
                  (
                    var_1_current_6=var_1_current_7)
                  and 
                  (
                    examples_bstree_Node_key_12=examples_bstree_Node_key_14)
                  and 
                  (
                    examples_bstree_Node_left_17=examples_bstree_Node_left_20)
                  and 
                  (
                    usedObjects_6=usedObjects_7)
                )
              )
              and 
              (
                l11_nullDerefBool_0=l11_nullDerefBool_7)
              and 
              (
                es_var__2_5=es_var__2_6)
              and 
              (
                l11_exit_stmt_reached_0=l11_exit_stmt_reached_1)
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
            l11_nullDerefBool_0=l11_nullDerefBool_7)
          and 
          (
            l12_nullDerefBool_0=l12_nullDerefBool_7)
          and 
          (
            nullDerefBool_19=nullDerefBool_22)
          and 
          (
            l12_exit_stmt_reached_0=l12_exit_stmt_reached_1)
          and 
          (
            es_var__2_5=es_var__2_6)
          and 
          (
            es_var__3_5=es_var__3_6)
          and 
          (
            throw_13=throw_15)
          and 
          (
            examples_bstree_Node_right_17=examples_bstree_Node_right_20)
          and 
          (
            var_1_current_6=var_1_current_7)
          and 
          (
            l11_exit_stmt_reached_0=l11_exit_stmt_reached_1)
          and 
          (
            examples_bstree_Node_key_12=examples_bstree_Node_key_14)
          and 
          (
            examples_bstree_Node_left_17=examples_bstree_Node_left_20)
          and 
          (
            usedObjects_6=usedObjects_7)
        )
      )
      and 
      (
        (
          examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
          and 
          (
            var_2_ws_1_7=(neq[var_1_current_7.examples_bstree_Node_key_14,
               x_0]=>(true)else(false))
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
            var_2_ws_1_6=var_2_ws_1_7)
        )
      )
    )
    or 
    (
      TruePred[]
      and 
      (
        l11_nullDerefBool_0=l11_nullDerefBool_7)
      and 
      (
        l12_nullDerefBool_0=l12_nullDerefBool_7)
      and 
      (
        nullDerefBool_19=nullDerefBool_22)
      and 
      (
        l12_exit_stmt_reached_0=l12_exit_stmt_reached_1)
      and 
      (
        es_var__2_5=es_var__2_6)
      and 
      (
        es_var__3_5=es_var__3_6)
      and 
      (
        throw_13=throw_15)
      and 
      (
        examples_bstree_Node_right_17=examples_bstree_Node_right_20)
      and 
      (
        var_1_current_6=var_1_current_7)
      and 
      (
        l11_exit_stmt_reached_0=l11_exit_stmt_reached_1)
      and 
      (
        examples_bstree_Node_key_12=examples_bstree_Node_key_14)
      and 
      (
        var_2_ws_1_6=var_2_ws_1_7)
      and 
      (
        examples_bstree_Node_left_17=examples_bstree_Node_left_20)
      and 
      (
        usedObjects_6=usedObjects_7)
    )
  )
  and 
  (
    (
      examples_bstree_BinTreeCondition14[exit_stmt_reached_1,
                                        var_2_ws_1_7]
      and 
      (
        (
          examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
          and 
          (
            (
              examples_bstree_BinTreeCondition6[var_1_current_7]
              and 
              (
                nullDerefBool_23=true)
            )
            or 
            (
              (
                not (
                  examples_bstree_BinTreeCondition6[var_1_current_7])
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
            (
              examples_bstree_BinTreeCondition12[examples_bstree_Node_key_14,
                                                var_1_current_7,
                                                x_0]
              and 
              (
                (
                  examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
                  and 
                  (
                    (
                      examples_bstree_BinTreeCondition6[var_1_current_7]
                      and 
                      (
                        nullDerefBool_24=true)
                    )
                    or 
                    (
                      (
                        not (
                          examples_bstree_BinTreeCondition6[var_1_current_7])
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
                      examples_bstree_BinTreeCondition8[examples_bstree_Node_left_20,
                                                       var_1_current_7]
                      and 
                      TruePred[]
                      and 
                      (
                        (
                          examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
                          and 
                          getUnusedObject[es_var__2_7,
                                         usedObjects_7,
                                         usedObjects_8]
                          and 
                          instanceOf[es_var__2_7,
                                    examples_bstree_Node]
                          and 
                          examples_bstree_Node_Constructor_0[es_var__2_7,
                                                            throw_16,
                                                            throw_17,
                                                            x_0,
                                                            examples_bstree_Node_right_20,
                                                            examples_bstree_Node_right_21,
                                                            examples_bstree_Node_right_23,
                                                            examples_bstree_Node_key_14,
                                                            examples_bstree_Node_key_15,
                                                            examples_bstree_Node_key_16,
                                                            examples_bstree_Node_left_20,
                                                            examples_bstree_Node_left_21,
                                                            examples_bstree_Node_left_22,
                                                            l13_exit_stmt_reached_1,
                                                            l13_nullDerefBool_1,
                                                            l13_nullDerefBool_2,
                                                            l13_nullDerefBool_3,
                                                            l13_nullDerefBool_4,
                                                            l13_nullDerefBool_5,
                                                            l13_nullDerefBool_6,
                                                            l13_nullDerefBool_7]
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
                            es_var__2_6=es_var__2_7)
                          and 
                          (
                            throw_15=throw_17)
                          and 
                          (
                            examples_bstree_Node_right_20=examples_bstree_Node_right_23)
                          and 
                          (
                            l13_exit_stmt_reached_0=l13_exit_stmt_reached_1)
                          and 
                          (
                            l13_nullDerefBool_0=l13_nullDerefBool_7)
                          and 
                          (
                            examples_bstree_Node_key_14=examples_bstree_Node_key_16)
                          and 
                          (
                            examples_bstree_Node_left_20=examples_bstree_Node_left_22)
                          and 
                          (
                            usedObjects_7=usedObjects_8)
                        )
                      )
                      and 
                      (
                        (
                          examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
                          and 
                          (
                            (
                              examples_bstree_BinTreeCondition6[var_1_current_7]
                              and 
                              (
                                nullDerefBool_25=true)
                            )
                            or 
                            (
                              (
                                not (
                                  examples_bstree_BinTreeCondition6[var_1_current_7])
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
                            examples_bstree_Node_left_23=(examples_bstree_Node_left_22)++((var_1_current_7)->(es_var__2_7)))
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
                            nullDerefBool_24=nullDerefBool_25)
                          and 
                          (
                            examples_bstree_Node_left_22=examples_bstree_Node_left_23)
                        )
                      )
                      and 
                      (
                        var_1_current_7=var_1_current_8)
                    )
                    or 
                    (
                      (
                        not (
                          examples_bstree_BinTreeCondition8[examples_bstree_Node_left_20,
                                                           var_1_current_7]
                        )
                      )
                      and 
                      (
                        (
                          examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
                          and 
                          (
                            (
                              examples_bstree_BinTreeCondition6[var_1_current_7]
                              and 
                              (
                                nullDerefBool_25=true)
                            )
                            or 
                            (
                              (
                                not (
                                  examples_bstree_BinTreeCondition6[var_1_current_7])
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
                            var_1_current_8=var_1_current_7.examples_bstree_Node_left_20)
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
                            var_1_current_7=var_1_current_8)
                          and 
                          (
                            nullDerefBool_24=nullDerefBool_25)
                        )
                      )
                      and 
                      (
                        l13_nullDerefBool_0=l13_nullDerefBool_7)
                      and 
                      (
                        es_var__2_6=es_var__2_7)
                      and 
                      (
                        throw_15=throw_17)
                      and 
                      (
                        examples_bstree_Node_right_20=examples_bstree_Node_right_23)
                      and 
                      (
                        l13_exit_stmt_reached_0=l13_exit_stmt_reached_1)
                      and 
                      (
                        examples_bstree_Node_key_14=examples_bstree_Node_key_16)
                      and 
                      (
                        usedObjects_7=usedObjects_8)
                      and 
                      (
                        examples_bstree_Node_left_20=examples_bstree_Node_left_23)
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
                    l13_nullDerefBool_0=l13_nullDerefBool_7)
                  and 
                  (
                    nullDerefBool_23=nullDerefBool_25)
                  and 
                  (
                    es_var__2_6=es_var__2_7)
                  and 
                  (
                    throw_15=throw_17)
                  and 
                  (
                    examples_bstree_Node_right_20=examples_bstree_Node_right_23)
                  and 
                  (
                    l13_exit_stmt_reached_0=l13_exit_stmt_reached_1)
                  and 
                  (
                    var_1_current_7=var_1_current_8)
                  and 
                  (
                    examples_bstree_Node_key_14=examples_bstree_Node_key_16)
                  and 
                  (
                    examples_bstree_Node_left_20=examples_bstree_Node_left_23)
                  and 
                  (
                    usedObjects_7=usedObjects_8)
                )
              )
              and 
              (
                l14_nullDerefBool_0=l14_nullDerefBool_7)
              and 
              (
                l14_exit_stmt_reached_0=l14_exit_stmt_reached_1)
              and 
              (
                es_var__3_6=es_var__3_7)
            )
            or 
            (
              (
                not (
                  examples_bstree_BinTreeCondition12[examples_bstree_Node_key_14,
                                                    var_1_current_7,
                                                    x_0]
                )
              )
              and 
              (
                (
                  examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
                  and 
                  (
                    (
                      examples_bstree_BinTreeCondition6[var_1_current_7]
                      and 
                      (
                        nullDerefBool_24=true)
                    )
                    or 
                    (
                      (
                        not (
                          examples_bstree_BinTreeCondition6[var_1_current_7])
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
                      examples_bstree_BinTreeCondition10[examples_bstree_Node_right_20,
                                                        var_1_current_7]
                      and 
                      TruePred[]
                      and 
                      (
                        (
                          examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
                          and 
                          getUnusedObject[es_var__3_7,
                                         usedObjects_7,
                                         usedObjects_8]
                          and 
                          instanceOf[es_var__3_7,
                                    examples_bstree_Node]
                          and 
                          examples_bstree_Node_Constructor_0[es_var__3_7,
                                                            throw_16,
                                                            throw_17,
                                                            x_0,
                                                            examples_bstree_Node_right_20,
                                                            examples_bstree_Node_right_21,
                                                            examples_bstree_Node_right_22,
                                                            examples_bstree_Node_key_14,
                                                            examples_bstree_Node_key_15,
                                                            examples_bstree_Node_key_16,
                                                            examples_bstree_Node_left_20,
                                                            examples_bstree_Node_left_21,
                                                            examples_bstree_Node_left_23,
                                                            l14_exit_stmt_reached_1,
                                                            l14_nullDerefBool_1,
                                                            l14_nullDerefBool_2,
                                                            l14_nullDerefBool_3,
                                                            l14_nullDerefBool_4,
                                                            l14_nullDerefBool_5,
                                                            l14_nullDerefBool_6,
                                                            l14_nullDerefBool_7]
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
                            l14_nullDerefBool_0=l14_nullDerefBool_7)
                          and 
                          (
                            throw_15=throw_17)
                          and 
                          (
                            es_var__3_6=es_var__3_7)
                          and 
                          (
                            examples_bstree_Node_right_20=examples_bstree_Node_right_22)
                          and 
                          (
                            l14_exit_stmt_reached_0=l14_exit_stmt_reached_1)
                          and 
                          (
                            examples_bstree_Node_key_14=examples_bstree_Node_key_16)
                          and 
                          (
                            examples_bstree_Node_left_20=examples_bstree_Node_left_23)
                          and 
                          (
                            usedObjects_7=usedObjects_8)
                        )
                      )
                      and 
                      (
                        (
                          examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
                          and 
                          (
                            (
                              examples_bstree_BinTreeCondition6[var_1_current_7]
                              and 
                              (
                                nullDerefBool_25=true)
                            )
                            or 
                            (
                              (
                                not (
                                  examples_bstree_BinTreeCondition6[var_1_current_7])
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
                            examples_bstree_Node_right_23=(examples_bstree_Node_right_22)++((var_1_current_7)->(es_var__3_7)))
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
                            examples_bstree_Node_right_22=examples_bstree_Node_right_23)
                          and 
                          (
                            nullDerefBool_24=nullDerefBool_25)
                        )
                      )
                      and 
                      (
                        var_1_current_7=var_1_current_8)
                    )
                    or 
                    (
                      (
                        not (
                          examples_bstree_BinTreeCondition10[examples_bstree_Node_right_20,
                                                            var_1_current_7]
                        )
                      )
                      and 
                      (
                        (
                          examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
                          and 
                          (
                            (
                              examples_bstree_BinTreeCondition6[var_1_current_7]
                              and 
                              (
                                nullDerefBool_25=true)
                            )
                            or 
                            (
                              (
                                not (
                                  examples_bstree_BinTreeCondition6[var_1_current_7])
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
                            var_1_current_8=var_1_current_7.examples_bstree_Node_right_20)
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
                            var_1_current_7=var_1_current_8)
                          and 
                          (
                            nullDerefBool_24=nullDerefBool_25)
                        )
                      )
                      and 
                      (
                        l14_nullDerefBool_0=l14_nullDerefBool_7)
                      and 
                      (
                        l14_exit_stmt_reached_0=l14_exit_stmt_reached_1)
                      and 
                      (
                        throw_15=throw_17)
                      and 
                      (
                        es_var__3_6=es_var__3_7)
                      and 
                      (
                        examples_bstree_Node_key_14=examples_bstree_Node_key_16)
                      and 
                      (
                        examples_bstree_Node_left_20=examples_bstree_Node_left_23)
                      and 
                      (
                        usedObjects_7=usedObjects_8)
                      and 
                      (
                        examples_bstree_Node_right_20=examples_bstree_Node_right_23)
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
                    l14_nullDerefBool_0=l14_nullDerefBool_7)
                  and 
                  (
                    nullDerefBool_23=nullDerefBool_25)
                  and 
                  (
                    l14_exit_stmt_reached_0=l14_exit_stmt_reached_1)
                  and 
                  (
                    throw_15=throw_17)
                  and 
                  (
                    es_var__3_6=es_var__3_7)
                  and 
                  (
                    examples_bstree_Node_right_20=examples_bstree_Node_right_23)
                  and 
                  (
                    var_1_current_7=var_1_current_8)
                  and 
                  (
                    examples_bstree_Node_key_14=examples_bstree_Node_key_16)
                  and 
                  (
                    examples_bstree_Node_left_20=examples_bstree_Node_left_23)
                  and 
                  (
                    usedObjects_7=usedObjects_8)
                )
              )
              and 
              (
                l13_nullDerefBool_0=l13_nullDerefBool_7)
              and 
              (
                es_var__2_6=es_var__2_7)
              and 
              (
                l13_exit_stmt_reached_0=l13_exit_stmt_reached_1)
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
            l14_nullDerefBool_0=l14_nullDerefBool_7)
          and 
          (
            l13_nullDerefBool_0=l13_nullDerefBool_7)
          and 
          (
            nullDerefBool_22=nullDerefBool_25)
          and 
          (
            l14_exit_stmt_reached_0=l14_exit_stmt_reached_1)
          and 
          (
            es_var__2_6=es_var__2_7)
          and 
          (
            es_var__3_6=es_var__3_7)
          and 
          (
            throw_15=throw_17)
          and 
          (
            examples_bstree_Node_right_20=examples_bstree_Node_right_23)
          and 
          (
            l13_exit_stmt_reached_0=l13_exit_stmt_reached_1)
          and 
          (
            var_1_current_7=var_1_current_8)
          and 
          (
            examples_bstree_Node_key_14=examples_bstree_Node_key_16)
          and 
          (
            examples_bstree_Node_left_20=examples_bstree_Node_left_23)
          and 
          (
            usedObjects_7=usedObjects_8)
        )
      )
      and 
      (
        (
          examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
          and 
          (
            var_2_ws_1_8=(neq[var_1_current_8.examples_bstree_Node_key_16,
               x_0]=>(true)else(false))
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
            var_2_ws_1_7=var_2_ws_1_8)
        )
      )
    )
    or 
    (
      TruePred[]
      and 
      (
        l14_nullDerefBool_0=l14_nullDerefBool_7)
      and 
      (
        l13_nullDerefBool_0=l13_nullDerefBool_7)
      and 
      (
        nullDerefBool_22=nullDerefBool_25)
      and 
      (
        l14_exit_stmt_reached_0=l14_exit_stmt_reached_1)
      and 
      (
        es_var__2_6=es_var__2_7)
      and 
      (
        es_var__3_6=es_var__3_7)
      and 
      (
        throw_15=throw_17)
      and 
      (
        examples_bstree_Node_right_20=examples_bstree_Node_right_23)
      and 
      (
        l13_exit_stmt_reached_0=l13_exit_stmt_reached_1)
      and 
      (
        var_1_current_7=var_1_current_8)
      and 
      (
        examples_bstree_Node_key_14=examples_bstree_Node_key_16)
      and 
      (
        var_2_ws_1_7=var_2_ws_1_8)
      and 
      (
        examples_bstree_Node_left_20=examples_bstree_Node_left_23)
      and 
      (
        usedObjects_7=usedObjects_8)
    )
  )
  and 
  (
    (
      examples_bstree_BinTreeCondition14[exit_stmt_reached_1,
                                        var_2_ws_1_8]
      and 
      (
        (
          examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
          and 
          (
            (
              examples_bstree_BinTreeCondition6[var_1_current_8]
              and 
              (
                nullDerefBool_26=true)
            )
            or 
            (
              (
                not (
                  examples_bstree_BinTreeCondition6[var_1_current_8])
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
            (
              examples_bstree_BinTreeCondition12[examples_bstree_Node_key_16,
                                                var_1_current_8,
                                                x_0]
              and 
              (
                (
                  examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
                  and 
                  (
                    (
                      examples_bstree_BinTreeCondition6[var_1_current_8]
                      and 
                      (
                        nullDerefBool_27=true)
                    )
                    or 
                    (
                      (
                        not (
                          examples_bstree_BinTreeCondition6[var_1_current_8])
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
                      examples_bstree_BinTreeCondition8[examples_bstree_Node_left_23,
                                                       var_1_current_8]
                      and 
                      TruePred[]
                      and 
                      (
                        (
                          examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
                          and 
                          getUnusedObject[es_var__2_8,
                                         usedObjects_8,
                                         usedObjects_9]
                          and 
                          instanceOf[es_var__2_8,
                                    examples_bstree_Node]
                          and 
                          examples_bstree_Node_Constructor_0[es_var__2_8,
                                                            throw_18,
                                                            throw_19,
                                                            x_0,
                                                            examples_bstree_Node_right_23,
                                                            examples_bstree_Node_right_24,
                                                            examples_bstree_Node_right_26,
                                                            examples_bstree_Node_key_16,
                                                            examples_bstree_Node_key_17,
                                                            examples_bstree_Node_key_18,
                                                            examples_bstree_Node_left_23,
                                                            examples_bstree_Node_left_24,
                                                            examples_bstree_Node_left_25,
                                                            l15_exit_stmt_reached_1,
                                                            l15_nullDerefBool_1,
                                                            l15_nullDerefBool_2,
                                                            l15_nullDerefBool_3,
                                                            l15_nullDerefBool_4,
                                                            l15_nullDerefBool_5,
                                                            l15_nullDerefBool_6,
                                                            l15_nullDerefBool_7]
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
                            l15_exit_stmt_reached_0=l15_exit_stmt_reached_1)
                          and 
                          (
                            es_var__2_7=es_var__2_8)
                          and 
                          (
                            throw_17=throw_19)
                          and 
                          (
                            examples_bstree_Node_right_23=examples_bstree_Node_right_26)
                          and 
                          (
                            l15_nullDerefBool_0=l15_nullDerefBool_7)
                          and 
                          (
                            examples_bstree_Node_key_16=examples_bstree_Node_key_18)
                          and 
                          (
                            examples_bstree_Node_left_23=examples_bstree_Node_left_25)
                          and 
                          (
                            usedObjects_8=usedObjects_9)
                        )
                      )
                      and 
                      (
                        (
                          examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
                          and 
                          (
                            (
                              examples_bstree_BinTreeCondition6[var_1_current_8]
                              and 
                              (
                                nullDerefBool_28=true)
                            )
                            or 
                            (
                              (
                                not (
                                  examples_bstree_BinTreeCondition6[var_1_current_8])
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
                            examples_bstree_Node_left_26=(examples_bstree_Node_left_25)++((var_1_current_8)->(es_var__2_8)))
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
                            nullDerefBool_27=nullDerefBool_28)
                          and 
                          (
                            examples_bstree_Node_left_25=examples_bstree_Node_left_26)
                        )
                      )
                      and 
                      (
                        var_1_current_8=var_1_current_9)
                    )
                    or 
                    (
                      (
                        not (
                          examples_bstree_BinTreeCondition8[examples_bstree_Node_left_23,
                                                           var_1_current_8]
                        )
                      )
                      and 
                      (
                        (
                          examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
                          and 
                          (
                            (
                              examples_bstree_BinTreeCondition6[var_1_current_8]
                              and 
                              (
                                nullDerefBool_28=true)
                            )
                            or 
                            (
                              (
                                not (
                                  examples_bstree_BinTreeCondition6[var_1_current_8])
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
                            var_1_current_9=var_1_current_8.examples_bstree_Node_left_23)
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
                            var_1_current_8=var_1_current_9)
                          and 
                          (
                            nullDerefBool_27=nullDerefBool_28)
                        )
                      )
                      and 
                      (
                        l15_exit_stmt_reached_0=l15_exit_stmt_reached_1)
                      and 
                      (
                        l15_nullDerefBool_0=l15_nullDerefBool_7)
                      and 
                      (
                        es_var__2_7=es_var__2_8)
                      and 
                      (
                        throw_17=throw_19)
                      and 
                      (
                        examples_bstree_Node_right_23=examples_bstree_Node_right_26)
                      and 
                      (
                        examples_bstree_Node_key_16=examples_bstree_Node_key_18)
                      and 
                      (
                        usedObjects_8=usedObjects_9)
                      and 
                      (
                        examples_bstree_Node_left_23=examples_bstree_Node_left_26)
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
                    l15_exit_stmt_reached_0=l15_exit_stmt_reached_1)
                  and 
                  (
                    l15_nullDerefBool_0=l15_nullDerefBool_7)
                  and 
                  (
                    nullDerefBool_26=nullDerefBool_28)
                  and 
                  (
                    es_var__2_7=es_var__2_8)
                  and 
                  (
                    throw_17=throw_19)
                  and 
                  (
                    examples_bstree_Node_right_23=examples_bstree_Node_right_26)
                  and 
                  (
                    var_1_current_8=var_1_current_9)
                  and 
                  (
                    examples_bstree_Node_key_16=examples_bstree_Node_key_18)
                  and 
                  (
                    examples_bstree_Node_left_23=examples_bstree_Node_left_26)
                  and 
                  (
                    usedObjects_8=usedObjects_9)
                )
              )
              and 
              (
                l16_nullDerefBool_0=l16_nullDerefBool_7)
              and 
              (
                es_var__3_7=es_var__3_8)
              and 
              (
                l16_exit_stmt_reached_0=l16_exit_stmt_reached_1)
            )
            or 
            (
              (
                not (
                  examples_bstree_BinTreeCondition12[examples_bstree_Node_key_16,
                                                    var_1_current_8,
                                                    x_0]
                )
              )
              and 
              (
                (
                  examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
                  and 
                  (
                    (
                      examples_bstree_BinTreeCondition6[var_1_current_8]
                      and 
                      (
                        nullDerefBool_27=true)
                    )
                    or 
                    (
                      (
                        not (
                          examples_bstree_BinTreeCondition6[var_1_current_8])
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
                      examples_bstree_BinTreeCondition10[examples_bstree_Node_right_23,
                                                        var_1_current_8]
                      and 
                      TruePred[]
                      and 
                      (
                        (
                          examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
                          and 
                          getUnusedObject[es_var__3_8,
                                         usedObjects_8,
                                         usedObjects_9]
                          and 
                          instanceOf[es_var__3_8,
                                    examples_bstree_Node]
                          and 
                          examples_bstree_Node_Constructor_0[es_var__3_8,
                                                            throw_18,
                                                            throw_19,
                                                            x_0,
                                                            examples_bstree_Node_right_23,
                                                            examples_bstree_Node_right_24,
                                                            examples_bstree_Node_right_25,
                                                            examples_bstree_Node_key_16,
                                                            examples_bstree_Node_key_17,
                                                            examples_bstree_Node_key_18,
                                                            examples_bstree_Node_left_23,
                                                            examples_bstree_Node_left_24,
                                                            examples_bstree_Node_left_26,
                                                            l16_exit_stmt_reached_1,
                                                            l16_nullDerefBool_1,
                                                            l16_nullDerefBool_2,
                                                            l16_nullDerefBool_3,
                                                            l16_nullDerefBool_4,
                                                            l16_nullDerefBool_5,
                                                            l16_nullDerefBool_6,
                                                            l16_nullDerefBool_7]
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
                            throw_17=throw_19)
                          and 
                          (
                            es_var__3_7=es_var__3_8)
                          and 
                          (
                            examples_bstree_Node_right_23=examples_bstree_Node_right_25)
                          and 
                          (
                            l16_nullDerefBool_0=l16_nullDerefBool_7)
                          and 
                          (
                            l16_exit_stmt_reached_0=l16_exit_stmt_reached_1)
                          and 
                          (
                            examples_bstree_Node_key_16=examples_bstree_Node_key_18)
                          and 
                          (
                            examples_bstree_Node_left_23=examples_bstree_Node_left_26)
                          and 
                          (
                            usedObjects_8=usedObjects_9)
                        )
                      )
                      and 
                      (
                        (
                          examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
                          and 
                          (
                            (
                              examples_bstree_BinTreeCondition6[var_1_current_8]
                              and 
                              (
                                nullDerefBool_28=true)
                            )
                            or 
                            (
                              (
                                not (
                                  examples_bstree_BinTreeCondition6[var_1_current_8])
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
                            examples_bstree_Node_right_26=(examples_bstree_Node_right_25)++((var_1_current_8)->(es_var__3_8)))
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
                            examples_bstree_Node_right_25=examples_bstree_Node_right_26)
                          and 
                          (
                            nullDerefBool_27=nullDerefBool_28)
                        )
                      )
                      and 
                      (
                        var_1_current_8=var_1_current_9)
                    )
                    or 
                    (
                      (
                        not (
                          examples_bstree_BinTreeCondition10[examples_bstree_Node_right_23,
                                                            var_1_current_8]
                        )
                      )
                      and 
                      (
                        (
                          examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
                          and 
                          (
                            (
                              examples_bstree_BinTreeCondition6[var_1_current_8]
                              and 
                              (
                                nullDerefBool_28=true)
                            )
                            or 
                            (
                              (
                                not (
                                  examples_bstree_BinTreeCondition6[var_1_current_8])
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
                            var_1_current_9=var_1_current_8.examples_bstree_Node_right_23)
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
                            var_1_current_8=var_1_current_9)
                          and 
                          (
                            nullDerefBool_27=nullDerefBool_28)
                        )
                      )
                      and 
                      (
                        l16_nullDerefBool_0=l16_nullDerefBool_7)
                      and 
                      (
                        throw_17=throw_19)
                      and 
                      (
                        es_var__3_7=es_var__3_8)
                      and 
                      (
                        l16_exit_stmt_reached_0=l16_exit_stmt_reached_1)
                      and 
                      (
                        examples_bstree_Node_key_16=examples_bstree_Node_key_18)
                      and 
                      (
                        examples_bstree_Node_left_23=examples_bstree_Node_left_26)
                      and 
                      (
                        usedObjects_8=usedObjects_9)
                      and 
                      (
                        examples_bstree_Node_right_23=examples_bstree_Node_right_26)
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
                    nullDerefBool_26=nullDerefBool_28)
                  and 
                  (
                    l16_nullDerefBool_0=l16_nullDerefBool_7)
                  and 
                  (
                    throw_17=throw_19)
                  and 
                  (
                    es_var__3_7=es_var__3_8)
                  and 
                  (
                    examples_bstree_Node_right_23=examples_bstree_Node_right_26)
                  and 
                  (
                    var_1_current_8=var_1_current_9)
                  and 
                  (
                    l16_exit_stmt_reached_0=l16_exit_stmt_reached_1)
                  and 
                  (
                    examples_bstree_Node_key_16=examples_bstree_Node_key_18)
                  and 
                  (
                    examples_bstree_Node_left_23=examples_bstree_Node_left_26)
                  and 
                  (
                    usedObjects_8=usedObjects_9)
                )
              )
              and 
              (
                l15_exit_stmt_reached_0=l15_exit_stmt_reached_1)
              and 
              (
                l15_nullDerefBool_0=l15_nullDerefBool_7)
              and 
              (
                es_var__2_7=es_var__2_8)
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
            l15_exit_stmt_reached_0=l15_exit_stmt_reached_1)
          and 
          (
            l15_nullDerefBool_0=l15_nullDerefBool_7)
          and 
          (
            nullDerefBool_25=nullDerefBool_28)
          and 
          (
            l16_nullDerefBool_0=l16_nullDerefBool_7)
          and 
          (
            es_var__2_7=es_var__2_8)
          and 
          (
            es_var__3_7=es_var__3_8)
          and 
          (
            throw_17=throw_19)
          and 
          (
            examples_bstree_Node_right_23=examples_bstree_Node_right_26)
          and 
          (
            var_1_current_8=var_1_current_9)
          and 
          (
            l16_exit_stmt_reached_0=l16_exit_stmt_reached_1)
          and 
          (
            examples_bstree_Node_key_16=examples_bstree_Node_key_18)
          and 
          (
            examples_bstree_Node_left_23=examples_bstree_Node_left_26)
          and 
          (
            usedObjects_8=usedObjects_9)
        )
      )
      and 
      (
        (
          examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
          and 
          (
            var_2_ws_1_9=(neq[var_1_current_9.examples_bstree_Node_key_18,
               x_0]=>(true)else(false))
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
            var_2_ws_1_8=var_2_ws_1_9)
        )
      )
    )
    or 
    (
      TruePred[]
      and 
      (
        l15_exit_stmt_reached_0=l15_exit_stmt_reached_1)
      and 
      (
        l15_nullDerefBool_0=l15_nullDerefBool_7)
      and 
      (
        nullDerefBool_25=nullDerefBool_28)
      and 
      (
        l16_nullDerefBool_0=l16_nullDerefBool_7)
      and 
      (
        es_var__2_7=es_var__2_8)
      and 
      (
        es_var__3_7=es_var__3_8)
      and 
      (
        throw_17=throw_19)
      and 
      (
        examples_bstree_Node_right_23=examples_bstree_Node_right_26)
      and 
      (
        var_1_current_8=var_1_current_9)
      and 
      (
        l16_exit_stmt_reached_0=l16_exit_stmt_reached_1)
      and 
      (
        examples_bstree_Node_key_16=examples_bstree_Node_key_18)
      and 
      (
        var_2_ws_1_8=var_2_ws_1_9)
      and 
      (
        examples_bstree_Node_left_23=examples_bstree_Node_left_26)
      and 
      (
        usedObjects_8=usedObjects_9)
    )
  )
  and 
  (
    (
      examples_bstree_BinTreeCondition14[exit_stmt_reached_1,
                                        var_2_ws_1_9]
      and 
      (
        (
          examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
          and 
          (
            (
              examples_bstree_BinTreeCondition6[var_1_current_9]
              and 
              (
                nullDerefBool_29=true)
            )
            or 
            (
              (
                not (
                  examples_bstree_BinTreeCondition6[var_1_current_9])
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
            (
              examples_bstree_BinTreeCondition12[examples_bstree_Node_key_18,
                                                var_1_current_9,
                                                x_0]
              and 
              (
                (
                  examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
                  and 
                  (
                    (
                      examples_bstree_BinTreeCondition6[var_1_current_9]
                      and 
                      (
                        nullDerefBool_30=true)
                    )
                    or 
                    (
                      (
                        not (
                          examples_bstree_BinTreeCondition6[var_1_current_9])
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
                      examples_bstree_BinTreeCondition8[examples_bstree_Node_left_26,
                                                       var_1_current_9]
                      and 
                      TruePred[]
                      and 
                      (
                        (
                          examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
                          and 
                          getUnusedObject[es_var__2_9,
                                         usedObjects_9,
                                         usedObjects_10]
                          and 
                          instanceOf[es_var__2_9,
                                    examples_bstree_Node]
                          and 
                          examples_bstree_Node_Constructor_0[es_var__2_9,
                                                            throw_20,
                                                            throw_21,
                                                            x_0,
                                                            examples_bstree_Node_right_26,
                                                            examples_bstree_Node_right_27,
                                                            examples_bstree_Node_right_29,
                                                            examples_bstree_Node_key_18,
                                                            examples_bstree_Node_key_19,
                                                            examples_bstree_Node_key_20,
                                                            examples_bstree_Node_left_26,
                                                            examples_bstree_Node_left_27,
                                                            examples_bstree_Node_left_28,
                                                            l17_exit_stmt_reached_1,
                                                            l17_nullDerefBool_1,
                                                            l17_nullDerefBool_2,
                                                            l17_nullDerefBool_3,
                                                            l17_nullDerefBool_4,
                                                            l17_nullDerefBool_5,
                                                            l17_nullDerefBool_6,
                                                            l17_nullDerefBool_7]
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
                            es_var__2_8=es_var__2_9)
                          and 
                          (
                            l17_exit_stmt_reached_0=l17_exit_stmt_reached_1)
                          and 
                          (
                            throw_19=throw_21)
                          and 
                          (
                            l17_nullDerefBool_0=l17_nullDerefBool_7)
                          and 
                          (
                            examples_bstree_Node_right_26=examples_bstree_Node_right_29)
                          and 
                          (
                            examples_bstree_Node_key_18=examples_bstree_Node_key_20)
                          and 
                          (
                            examples_bstree_Node_left_26=examples_bstree_Node_left_28)
                          and 
                          (
                            usedObjects_9=usedObjects_10)
                        )
                      )
                      and 
                      (
                        (
                          examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
                          and 
                          (
                            (
                              examples_bstree_BinTreeCondition6[var_1_current_9]
                              and 
                              (
                                nullDerefBool_31=true)
                            )
                            or 
                            (
                              (
                                not (
                                  examples_bstree_BinTreeCondition6[var_1_current_9])
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
                            examples_bstree_Node_left_29=(examples_bstree_Node_left_28)++((var_1_current_9)->(es_var__2_9)))
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
                            nullDerefBool_30=nullDerefBool_31)
                          and 
                          (
                            examples_bstree_Node_left_28=examples_bstree_Node_left_29)
                        )
                      )
                      and 
                      (
                        var_1_current_9=var_1_current_10)
                    )
                    or 
                    (
                      (
                        not (
                          examples_bstree_BinTreeCondition8[examples_bstree_Node_left_26,
                                                           var_1_current_9]
                        )
                      )
                      and 
                      (
                        (
                          examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
                          and 
                          (
                            (
                              examples_bstree_BinTreeCondition6[var_1_current_9]
                              and 
                              (
                                nullDerefBool_31=true)
                            )
                            or 
                            (
                              (
                                not (
                                  examples_bstree_BinTreeCondition6[var_1_current_9])
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
                            var_1_current_10=var_1_current_9.examples_bstree_Node_left_26)
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
                            var_1_current_9=var_1_current_10)
                          and 
                          (
                            nullDerefBool_30=nullDerefBool_31)
                        )
                      )
                      and 
                      (
                        l17_exit_stmt_reached_0=l17_exit_stmt_reached_1)
                      and 
                      (
                        es_var__2_8=es_var__2_9)
                      and 
                      (
                        throw_19=throw_21)
                      and 
                      (
                        examples_bstree_Node_right_26=examples_bstree_Node_right_29)
                      and 
                      (
                        l17_nullDerefBool_0=l17_nullDerefBool_7)
                      and 
                      (
                        examples_bstree_Node_key_18=examples_bstree_Node_key_20)
                      and 
                      (
                        usedObjects_9=usedObjects_10)
                      and 
                      (
                        examples_bstree_Node_left_26=examples_bstree_Node_left_29)
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
                    l17_exit_stmt_reached_0=l17_exit_stmt_reached_1)
                  and 
                  (
                    nullDerefBool_29=nullDerefBool_31)
                  and 
                  (
                    es_var__2_8=es_var__2_9)
                  and 
                  (
                    throw_19=throw_21)
                  and 
                  (
                    examples_bstree_Node_right_26=examples_bstree_Node_right_29)
                  and 
                  (
                    l17_nullDerefBool_0=l17_nullDerefBool_7)
                  and 
                  (
                    var_1_current_9=var_1_current_10)
                  and 
                  (
                    examples_bstree_Node_key_18=examples_bstree_Node_key_20)
                  and 
                  (
                    examples_bstree_Node_left_26=examples_bstree_Node_left_29)
                  and 
                  (
                    usedObjects_9=usedObjects_10)
                )
              )
              and 
              (
                l18_nullDerefBool_0=l18_nullDerefBool_7)
              and 
              (
                es_var__3_8=es_var__3_9)
              and 
              (
                l18_exit_stmt_reached_0=l18_exit_stmt_reached_1)
            )
            or 
            (
              (
                not (
                  examples_bstree_BinTreeCondition12[examples_bstree_Node_key_18,
                                                    var_1_current_9,
                                                    x_0]
                )
              )
              and 
              (
                (
                  examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
                  and 
                  (
                    (
                      examples_bstree_BinTreeCondition6[var_1_current_9]
                      and 
                      (
                        nullDerefBool_30=true)
                    )
                    or 
                    (
                      (
                        not (
                          examples_bstree_BinTreeCondition6[var_1_current_9])
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
                      examples_bstree_BinTreeCondition10[examples_bstree_Node_right_26,
                                                        var_1_current_9]
                      and 
                      TruePred[]
                      and 
                      (
                        (
                          examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
                          and 
                          getUnusedObject[es_var__3_9,
                                         usedObjects_9,
                                         usedObjects_10]
                          and 
                          instanceOf[es_var__3_9,
                                    examples_bstree_Node]
                          and 
                          examples_bstree_Node_Constructor_0[es_var__3_9,
                                                            throw_20,
                                                            throw_21,
                                                            x_0,
                                                            examples_bstree_Node_right_26,
                                                            examples_bstree_Node_right_27,
                                                            examples_bstree_Node_right_28,
                                                            examples_bstree_Node_key_18,
                                                            examples_bstree_Node_key_19,
                                                            examples_bstree_Node_key_20,
                                                            examples_bstree_Node_left_26,
                                                            examples_bstree_Node_left_27,
                                                            examples_bstree_Node_left_29,
                                                            l18_exit_stmt_reached_1,
                                                            l18_nullDerefBool_1,
                                                            l18_nullDerefBool_2,
                                                            l18_nullDerefBool_3,
                                                            l18_nullDerefBool_4,
                                                            l18_nullDerefBool_5,
                                                            l18_nullDerefBool_6,
                                                            l18_nullDerefBool_7]
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
                            l18_nullDerefBool_0=l18_nullDerefBool_7)
                          and 
                          (
                            throw_19=throw_21)
                          and 
                          (
                            es_var__3_8=es_var__3_9)
                          and 
                          (
                            examples_bstree_Node_right_26=examples_bstree_Node_right_28)
                          and 
                          (
                            examples_bstree_Node_key_18=examples_bstree_Node_key_20)
                          and 
                          (
                            examples_bstree_Node_left_26=examples_bstree_Node_left_29)
                          and 
                          (
                            usedObjects_9=usedObjects_10)
                          and 
                          (
                            l18_exit_stmt_reached_0=l18_exit_stmt_reached_1)
                        )
                      )
                      and 
                      (
                        (
                          examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
                          and 
                          (
                            (
                              examples_bstree_BinTreeCondition6[var_1_current_9]
                              and 
                              (
                                nullDerefBool_31=true)
                            )
                            or 
                            (
                              (
                                not (
                                  examples_bstree_BinTreeCondition6[var_1_current_9])
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
                            examples_bstree_Node_right_29=(examples_bstree_Node_right_28)++((var_1_current_9)->(es_var__3_9)))
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
                            examples_bstree_Node_right_28=examples_bstree_Node_right_29)
                          and 
                          (
                            nullDerefBool_30=nullDerefBool_31)
                        )
                      )
                      and 
                      (
                        var_1_current_9=var_1_current_10)
                    )
                    or 
                    (
                      (
                        not (
                          examples_bstree_BinTreeCondition10[examples_bstree_Node_right_26,
                                                            var_1_current_9]
                        )
                      )
                      and 
                      (
                        (
                          examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
                          and 
                          (
                            (
                              examples_bstree_BinTreeCondition6[var_1_current_9]
                              and 
                              (
                                nullDerefBool_31=true)
                            )
                            or 
                            (
                              (
                                not (
                                  examples_bstree_BinTreeCondition6[var_1_current_9])
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
                            var_1_current_10=var_1_current_9.examples_bstree_Node_right_26)
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
                            var_1_current_9=var_1_current_10)
                          and 
                          (
                            nullDerefBool_30=nullDerefBool_31)
                        )
                      )
                      and 
                      (
                        l18_nullDerefBool_0=l18_nullDerefBool_7)
                      and 
                      (
                        throw_19=throw_21)
                      and 
                      (
                        es_var__3_8=es_var__3_9)
                      and 
                      (
                        examples_bstree_Node_key_18=examples_bstree_Node_key_20)
                      and 
                      (
                        examples_bstree_Node_left_26=examples_bstree_Node_left_29)
                      and 
                      (
                        usedObjects_9=usedObjects_10)
                      and 
                      (
                        l18_exit_stmt_reached_0=l18_exit_stmt_reached_1)
                      and 
                      (
                        examples_bstree_Node_right_26=examples_bstree_Node_right_29)
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
                    l18_nullDerefBool_0=l18_nullDerefBool_7)
                  and 
                  (
                    nullDerefBool_29=nullDerefBool_31)
                  and 
                  (
                    throw_19=throw_21)
                  and 
                  (
                    es_var__3_8=es_var__3_9)
                  and 
                  (
                    examples_bstree_Node_right_26=examples_bstree_Node_right_29)
                  and 
                  (
                    var_1_current_9=var_1_current_10)
                  and 
                  (
                    examples_bstree_Node_key_18=examples_bstree_Node_key_20)
                  and 
                  (
                    examples_bstree_Node_left_26=examples_bstree_Node_left_29)
                  and 
                  (
                    usedObjects_9=usedObjects_10)
                  and 
                  (
                    l18_exit_stmt_reached_0=l18_exit_stmt_reached_1)
                )
              )
              and 
              (
                l17_exit_stmt_reached_0=l17_exit_stmt_reached_1)
              and 
              (
                es_var__2_8=es_var__2_9)
              and 
              (
                l17_nullDerefBool_0=l17_nullDerefBool_7)
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
            l17_exit_stmt_reached_0=l17_exit_stmt_reached_1)
          and 
          (
            l18_nullDerefBool_0=l18_nullDerefBool_7)
          and 
          (
            nullDerefBool_28=nullDerefBool_31)
          and 
          (
            es_var__2_8=es_var__2_9)
          and 
          (
            es_var__3_8=es_var__3_9)
          and 
          (
            throw_19=throw_21)
          and 
          (
            l17_nullDerefBool_0=l17_nullDerefBool_7)
          and 
          (
            examples_bstree_Node_right_26=examples_bstree_Node_right_29)
          and 
          (
            var_1_current_9=var_1_current_10)
          and 
          (
            examples_bstree_Node_key_18=examples_bstree_Node_key_20)
          and 
          (
            examples_bstree_Node_left_26=examples_bstree_Node_left_29)
          and 
          (
            usedObjects_9=usedObjects_10)
          and 
          (
            l18_exit_stmt_reached_0=l18_exit_stmt_reached_1)
        )
      )
      and 
      (
        (
          examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
          and 
          (
            var_2_ws_1_10=(neq[var_1_current_10.examples_bstree_Node_key_20,
               x_0]=>(true)else(false))
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
            var_2_ws_1_9=var_2_ws_1_10)
        )
      )
    )
    or 
    (
      TruePred[]
      and 
      (
        l18_nullDerefBool_0=l18_nullDerefBool_7)
      and 
      (
        l17_exit_stmt_reached_0=l17_exit_stmt_reached_1)
      and 
      (
        nullDerefBool_28=nullDerefBool_31)
      and 
      (
        es_var__2_8=es_var__2_9)
      and 
      (
        es_var__3_8=es_var__3_9)
      and 
      (
        throw_19=throw_21)
      and 
      (
        l17_nullDerefBool_0=l17_nullDerefBool_7)
      and 
      (
        examples_bstree_Node_right_26=examples_bstree_Node_right_29)
      and 
      (
        var_1_current_9=var_1_current_10)
      and 
      (
        examples_bstree_Node_key_18=examples_bstree_Node_key_20)
      and 
      (
        var_2_ws_1_9=var_2_ws_1_10)
      and 
      (
        examples_bstree_Node_left_26=examples_bstree_Node_left_29)
      and 
      (
        usedObjects_9=usedObjects_10)
      and 
      (
        l18_exit_stmt_reached_0=l18_exit_stmt_reached_1)
    )
  )
  and 
  (
    (
      examples_bstree_BinTreeCondition14[exit_stmt_reached_1,
                                        var_2_ws_1_10]
      and 
      (
        (
          examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
          and 
          (
            (
              examples_bstree_BinTreeCondition6[var_1_current_10]
              and 
              (
                nullDerefBool_32=true)
            )
            or 
            (
              (
                not (
                  examples_bstree_BinTreeCondition6[var_1_current_10])
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
            (
              examples_bstree_BinTreeCondition12[examples_bstree_Node_key_20,
                                                var_1_current_10,
                                                x_0]
              and 
              (
                (
                  examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
                  and 
                  (
                    (
                      examples_bstree_BinTreeCondition6[var_1_current_10]
                      and 
                      (
                        nullDerefBool_33=true)
                    )
                    or 
                    (
                      (
                        not (
                          examples_bstree_BinTreeCondition6[var_1_current_10])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_32=nullDerefBool_33)
                    )
                  )
                  and 
                  (
                    (
                      examples_bstree_BinTreeCondition8[examples_bstree_Node_left_29,
                                                       var_1_current_10]
                      and 
                      TruePred[]
                      and 
                      (
                        (
                          examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
                          and 
                          getUnusedObject[es_var__2_10,
                                         usedObjects_10,
                                         usedObjects_11]
                          and 
                          instanceOf[es_var__2_10,
                                    examples_bstree_Node]
                          and 
                          examples_bstree_Node_Constructor_0[es_var__2_10,
                                                            throw_22,
                                                            throw_23,
                                                            x_0,
                                                            examples_bstree_Node_right_29,
                                                            examples_bstree_Node_right_30,
                                                            examples_bstree_Node_right_32,
                                                            examples_bstree_Node_key_20,
                                                            examples_bstree_Node_key_21,
                                                            examples_bstree_Node_key_22,
                                                            examples_bstree_Node_left_29,
                                                            examples_bstree_Node_left_30,
                                                            examples_bstree_Node_left_31,
                                                            l19_exit_stmt_reached_1,
                                                            l19_nullDerefBool_1,
                                                            l19_nullDerefBool_2,
                                                            l19_nullDerefBool_3,
                                                            l19_nullDerefBool_4,
                                                            l19_nullDerefBool_5,
                                                            l19_nullDerefBool_6,
                                                            l19_nullDerefBool_7]
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
                            es_var__2_9=es_var__2_10)
                          and 
                          (
                            l19_nullDerefBool_0=l19_nullDerefBool_7)
                          and 
                          (
                            throw_21=throw_23)
                          and 
                          (
                            l19_exit_stmt_reached_0=l19_exit_stmt_reached_1)
                          and 
                          (
                            examples_bstree_Node_right_29=examples_bstree_Node_right_32)
                          and 
                          (
                            examples_bstree_Node_key_20=examples_bstree_Node_key_22)
                          and 
                          (
                            examples_bstree_Node_left_29=examples_bstree_Node_left_31)
                          and 
                          (
                            usedObjects_10=usedObjects_11)
                        )
                      )
                      and 
                      (
                        (
                          examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
                          and 
                          (
                            (
                              examples_bstree_BinTreeCondition6[var_1_current_10]
                              and 
                              (
                                nullDerefBool_34=true)
                            )
                            or 
                            (
                              (
                                not (
                                  examples_bstree_BinTreeCondition6[var_1_current_10])
                              )
                              and 
                              TruePred[]
                              and 
                              (
                                nullDerefBool_33=nullDerefBool_34)
                            )
                          )
                          and 
                          (
                            examples_bstree_Node_left_32=(examples_bstree_Node_left_31)++((var_1_current_10)->(es_var__2_10)))
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
                            nullDerefBool_33=nullDerefBool_34)
                          and 
                          (
                            examples_bstree_Node_left_31=examples_bstree_Node_left_32)
                        )
                      )
                      and 
                      (
                        var_1_current_10=var_1_current_11)
                    )
                    or 
                    (
                      (
                        not (
                          examples_bstree_BinTreeCondition8[examples_bstree_Node_left_29,
                                                           var_1_current_10]
                        )
                      )
                      and 
                      (
                        (
                          examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
                          and 
                          (
                            (
                              examples_bstree_BinTreeCondition6[var_1_current_10]
                              and 
                              (
                                nullDerefBool_34=true)
                            )
                            or 
                            (
                              (
                                not (
                                  examples_bstree_BinTreeCondition6[var_1_current_10])
                              )
                              and 
                              TruePred[]
                              and 
                              (
                                nullDerefBool_33=nullDerefBool_34)
                            )
                          )
                          and 
                          (
                            var_1_current_11=var_1_current_10.examples_bstree_Node_left_29)
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
                            var_1_current_10=var_1_current_11)
                          and 
                          (
                            nullDerefBool_33=nullDerefBool_34)
                        )
                      )
                      and 
                      (
                        l19_nullDerefBool_0=l19_nullDerefBool_7)
                      and 
                      (
                        es_var__2_9=es_var__2_10)
                      and 
                      (
                        throw_21=throw_23)
                      and 
                      (
                        l19_exit_stmt_reached_0=l19_exit_stmt_reached_1)
                      and 
                      (
                        examples_bstree_Node_right_29=examples_bstree_Node_right_32)
                      and 
                      (
                        examples_bstree_Node_key_20=examples_bstree_Node_key_22)
                      and 
                      (
                        usedObjects_10=usedObjects_11)
                      and 
                      (
                        examples_bstree_Node_left_29=examples_bstree_Node_left_32)
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
                    l19_nullDerefBool_0=l19_nullDerefBool_7)
                  and 
                  (
                    nullDerefBool_32=nullDerefBool_34)
                  and 
                  (
                    es_var__2_9=es_var__2_10)
                  and 
                  (
                    throw_21=throw_23)
                  and 
                  (
                    l19_exit_stmt_reached_0=l19_exit_stmt_reached_1)
                  and 
                  (
                    examples_bstree_Node_right_29=examples_bstree_Node_right_32)
                  and 
                  (
                    var_1_current_10=var_1_current_11)
                  and 
                  (
                    examples_bstree_Node_key_20=examples_bstree_Node_key_22)
                  and 
                  (
                    examples_bstree_Node_left_29=examples_bstree_Node_left_32)
                  and 
                  (
                    usedObjects_10=usedObjects_11)
                )
              )
              and 
              (
                l20_nullDerefBool_0=l20_nullDerefBool_7)
              and 
              (
                es_var__3_9=es_var__3_10)
              and 
              (
                l20_exit_stmt_reached_0=l20_exit_stmt_reached_1)
            )
            or 
            (
              (
                not (
                  examples_bstree_BinTreeCondition12[examples_bstree_Node_key_20,
                                                    var_1_current_10,
                                                    x_0]
                )
              )
              and 
              (
                (
                  examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
                  and 
                  (
                    (
                      examples_bstree_BinTreeCondition6[var_1_current_10]
                      and 
                      (
                        nullDerefBool_33=true)
                    )
                    or 
                    (
                      (
                        not (
                          examples_bstree_BinTreeCondition6[var_1_current_10])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_32=nullDerefBool_33)
                    )
                  )
                  and 
                  (
                    (
                      examples_bstree_BinTreeCondition10[examples_bstree_Node_right_29,
                                                        var_1_current_10]
                      and 
                      TruePred[]
                      and 
                      (
                        (
                          examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
                          and 
                          getUnusedObject[es_var__3_10,
                                         usedObjects_10,
                                         usedObjects_11]
                          and 
                          instanceOf[es_var__3_10,
                                    examples_bstree_Node]
                          and 
                          examples_bstree_Node_Constructor_0[es_var__3_10,
                                                            throw_22,
                                                            throw_23,
                                                            x_0,
                                                            examples_bstree_Node_right_29,
                                                            examples_bstree_Node_right_30,
                                                            examples_bstree_Node_right_31,
                                                            examples_bstree_Node_key_20,
                                                            examples_bstree_Node_key_21,
                                                            examples_bstree_Node_key_22,
                                                            examples_bstree_Node_left_29,
                                                            examples_bstree_Node_left_30,
                                                            examples_bstree_Node_left_32,
                                                            l20_exit_stmt_reached_1,
                                                            l20_nullDerefBool_1,
                                                            l20_nullDerefBool_2,
                                                            l20_nullDerefBool_3,
                                                            l20_nullDerefBool_4,
                                                            l20_nullDerefBool_5,
                                                            l20_nullDerefBool_6,
                                                            l20_nullDerefBool_7]
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
                            throw_21=throw_23)
                          and 
                          (
                            es_var__3_9=es_var__3_10)
                          and 
                          (
                            examples_bstree_Node_right_29=examples_bstree_Node_right_31)
                          and 
                          (
                            l20_nullDerefBool_0=l20_nullDerefBool_7)
                          and 
                          (
                            examples_bstree_Node_key_20=examples_bstree_Node_key_22)
                          and 
                          (
                            l20_exit_stmt_reached_0=l20_exit_stmt_reached_1)
                          and 
                          (
                            examples_bstree_Node_left_29=examples_bstree_Node_left_32)
                          and 
                          (
                            usedObjects_10=usedObjects_11)
                        )
                      )
                      and 
                      (
                        (
                          examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
                          and 
                          (
                            (
                              examples_bstree_BinTreeCondition6[var_1_current_10]
                              and 
                              (
                                nullDerefBool_34=true)
                            )
                            or 
                            (
                              (
                                not (
                                  examples_bstree_BinTreeCondition6[var_1_current_10])
                              )
                              and 
                              TruePred[]
                              and 
                              (
                                nullDerefBool_33=nullDerefBool_34)
                            )
                          )
                          and 
                          (
                            examples_bstree_Node_right_32=(examples_bstree_Node_right_31)++((var_1_current_10)->(es_var__3_10)))
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
                            examples_bstree_Node_right_31=examples_bstree_Node_right_32)
                          and 
                          (
                            nullDerefBool_33=nullDerefBool_34)
                        )
                      )
                      and 
                      (
                        var_1_current_10=var_1_current_11)
                    )
                    or 
                    (
                      (
                        not (
                          examples_bstree_BinTreeCondition10[examples_bstree_Node_right_29,
                                                            var_1_current_10]
                        )
                      )
                      and 
                      (
                        (
                          examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
                          and 
                          (
                            (
                              examples_bstree_BinTreeCondition6[var_1_current_10]
                              and 
                              (
                                nullDerefBool_34=true)
                            )
                            or 
                            (
                              (
                                not (
                                  examples_bstree_BinTreeCondition6[var_1_current_10])
                              )
                              and 
                              TruePred[]
                              and 
                              (
                                nullDerefBool_33=nullDerefBool_34)
                            )
                          )
                          and 
                          (
                            var_1_current_11=var_1_current_10.examples_bstree_Node_right_29)
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
                            var_1_current_10=var_1_current_11)
                          and 
                          (
                            nullDerefBool_33=nullDerefBool_34)
                        )
                      )
                      and 
                      (
                        l20_nullDerefBool_0=l20_nullDerefBool_7)
                      and 
                      (
                        throw_21=throw_23)
                      and 
                      (
                        es_var__3_9=es_var__3_10)
                      and 
                      (
                        examples_bstree_Node_key_20=examples_bstree_Node_key_22)
                      and 
                      (
                        l20_exit_stmt_reached_0=l20_exit_stmt_reached_1)
                      and 
                      (
                        examples_bstree_Node_left_29=examples_bstree_Node_left_32)
                      and 
                      (
                        usedObjects_10=usedObjects_11)
                      and 
                      (
                        examples_bstree_Node_right_29=examples_bstree_Node_right_32)
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
                    l20_nullDerefBool_0=l20_nullDerefBool_7)
                  and 
                  (
                    nullDerefBool_32=nullDerefBool_34)
                  and 
                  (
                    throw_21=throw_23)
                  and 
                  (
                    es_var__3_9=es_var__3_10)
                  and 
                  (
                    examples_bstree_Node_right_29=examples_bstree_Node_right_32)
                  and 
                  (
                    var_1_current_10=var_1_current_11)
                  and 
                  (
                    examples_bstree_Node_key_20=examples_bstree_Node_key_22)
                  and 
                  (
                    l20_exit_stmt_reached_0=l20_exit_stmt_reached_1)
                  and 
                  (
                    examples_bstree_Node_left_29=examples_bstree_Node_left_32)
                  and 
                  (
                    usedObjects_10=usedObjects_11)
                )
              )
              and 
              (
                l19_nullDerefBool_0=l19_nullDerefBool_7)
              and 
              (
                es_var__2_9=es_var__2_10)
              and 
              (
                l19_exit_stmt_reached_0=l19_exit_stmt_reached_1)
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
            l19_nullDerefBool_0=l19_nullDerefBool_7)
          and 
          (
            l20_nullDerefBool_0=l20_nullDerefBool_7)
          and 
          (
            nullDerefBool_31=nullDerefBool_34)
          and 
          (
            es_var__2_9=es_var__2_10)
          and 
          (
            es_var__3_9=es_var__3_10)
          and 
          (
            l19_exit_stmt_reached_0=l19_exit_stmt_reached_1)
          and 
          (
            throw_21=throw_23)
          and 
          (
            examples_bstree_Node_right_29=examples_bstree_Node_right_32)
          and 
          (
            var_1_current_10=var_1_current_11)
          and 
          (
            examples_bstree_Node_key_20=examples_bstree_Node_key_22)
          and 
          (
            l20_exit_stmt_reached_0=l20_exit_stmt_reached_1)
          and 
          (
            examples_bstree_Node_left_29=examples_bstree_Node_left_32)
          and 
          (
            usedObjects_10=usedObjects_11)
        )
      )
      and 
      (
        (
          examples_bstree_BinTreeCondition2[exit_stmt_reached_1]
          and 
          (
            var_2_ws_1_11=(neq[var_1_current_11.examples_bstree_Node_key_22,
               x_0]=>(true)else(false))
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
            var_2_ws_1_10=var_2_ws_1_11)
        )
      )
    )
    or 
    (
      TruePred[]
      and 
      (
        l19_nullDerefBool_0=l19_nullDerefBool_7)
      and 
      (
        l20_nullDerefBool_0=l20_nullDerefBool_7)
      and 
      (
        nullDerefBool_31=nullDerefBool_34)
      and 
      (
        es_var__2_9=es_var__2_10)
      and 
      (
        es_var__3_9=es_var__3_10)
      and 
      (
        l19_exit_stmt_reached_0=l19_exit_stmt_reached_1)
      and 
      (
        throw_21=throw_23)
      and 
      (
        examples_bstree_Node_right_29=examples_bstree_Node_right_32)
      and 
      (
        var_1_current_10=var_1_current_11)
      and 
      (
        examples_bstree_Node_key_20=examples_bstree_Node_key_22)
      and 
      (
        var_2_ws_1_10=var_2_ws_1_11)
      and 
      (
        l20_exit_stmt_reached_0=l20_exit_stmt_reached_1)
      and 
      (
        examples_bstree_Node_left_29=examples_bstree_Node_left_32)
      and 
      (
        usedObjects_10=usedObjects_11)
    )
  )
  and 
  examples_bstree_BinTreeCondition15[exit_stmt_reached_1,
                                    var_2_ws_1_11]
  and 
  (
    (
      examples_bstree_BinTreeCondition16[nullDerefBool_34,
                                        throw_23]
      and 
      (
        throw_24=java_lang_NullPointerExceptionLit)
    )
    or 
    (
      (
        not (
          examples_bstree_BinTreeCondition16[nullDerefBool_34,
                                            throw_23]
        )
      )
      and 
      TruePred[]
      and 
      (
        throw_23=throw_24)
    )
  )

}



pred examples_bstree_Node_Constructor_0[
  thiz_0: examples_bstree_Node,
  throw_1: java_lang_Throwable + null,
  throw_2: java_lang_Throwable + null,
  x_0: Int,
  examples_bstree_Node_right_0: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_1: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_2: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_key_0: ( examples_bstree_Node ) -> one ( Int ),
  examples_bstree_Node_key_1: ( examples_bstree_Node ) -> one ( Int ),
  examples_bstree_Node_key_2: ( examples_bstree_Node ) -> one ( Int ),
  examples_bstree_Node_left_0: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_1: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_2: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  exit_stmt_reached_1: boolean,
  nullDerefBool_1: boolean,
  nullDerefBool_2: boolean,
  nullDerefBool_3: boolean,
  nullDerefBool_4: boolean,
  nullDerefBool_5: boolean,
  nullDerefBool_6: boolean,
  nullDerefBool_7: boolean
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
  (
    (
      examples_bstree_NodeCondition2[exit_stmt_reached_1]
      and 
      (
        (
          examples_bstree_NodeCondition0[thiz_0]
          and 
          (
            nullDerefBool_2=true)
        )
        or 
        (
          (
            not (
              examples_bstree_NodeCondition0[thiz_0])
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
        examples_bstree_Node_key_1=(examples_bstree_Node_key_0)++((thiz_0)->(0)))
    )
    or 
    (
      (
        not (
          examples_bstree_NodeCondition2[exit_stmt_reached_1])
      )
      and 
      TruePred[]
      and 
      (
        nullDerefBool_1=nullDerefBool_2)
      and 
      (
        examples_bstree_Node_key_0=examples_bstree_Node_key_1)
    )
  )
  and 
  (
    (
      examples_bstree_NodeCondition2[exit_stmt_reached_1]
      and 
      (
        (
          examples_bstree_NodeCondition0[thiz_0]
          and 
          (
            nullDerefBool_3=true)
        )
        or 
        (
          (
            not (
              examples_bstree_NodeCondition0[thiz_0])
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
        examples_bstree_Node_left_1=(examples_bstree_Node_left_0)++((thiz_0)->(null)))
    )
    or 
    (
      (
        not (
          examples_bstree_NodeCondition2[exit_stmt_reached_1])
      )
      and 
      TruePred[]
      and 
      (
        nullDerefBool_2=nullDerefBool_3)
      and 
      (
        examples_bstree_Node_left_0=examples_bstree_Node_left_1)
    )
  )
  and 
  (
    (
      examples_bstree_NodeCondition2[exit_stmt_reached_1]
      and 
      (
        (
          examples_bstree_NodeCondition0[thiz_0]
          and 
          (
            nullDerefBool_4=true)
        )
        or 
        (
          (
            not (
              examples_bstree_NodeCondition0[thiz_0])
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
        examples_bstree_Node_right_1=(examples_bstree_Node_right_0)++((thiz_0)->(null)))
    )
    or 
    (
      (
        not (
          examples_bstree_NodeCondition2[exit_stmt_reached_1])
      )
      and 
      TruePred[]
      and 
      (
        examples_bstree_Node_right_0=examples_bstree_Node_right_1)
      and 
      (
        nullDerefBool_3=nullDerefBool_4)
    )
  )
  and 
  (
    (
      examples_bstree_NodeCondition2[exit_stmt_reached_1]
      and 
      (
        (
          examples_bstree_NodeCondition0[thiz_0]
          and 
          (
            nullDerefBool_5=true)
        )
        or 
        (
          (
            not (
              examples_bstree_NodeCondition0[thiz_0])
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
        examples_bstree_Node_key_2=(examples_bstree_Node_key_1)++((thiz_0)->(x_0)))
    )
    or 
    (
      (
        not (
          examples_bstree_NodeCondition2[exit_stmt_reached_1])
      )
      and 
      TruePred[]
      and 
      (
        nullDerefBool_4=nullDerefBool_5)
      and 
      (
        examples_bstree_Node_key_1=examples_bstree_Node_key_2)
    )
  )
  and 
  (
    (
      examples_bstree_NodeCondition2[exit_stmt_reached_1]
      and 
      (
        (
          examples_bstree_NodeCondition0[thiz_0]
          and 
          (
            nullDerefBool_6=true)
        )
        or 
        (
          (
            not (
              examples_bstree_NodeCondition0[thiz_0])
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
        examples_bstree_Node_left_2=(examples_bstree_Node_left_1)++((thiz_0)->(null)))
    )
    or 
    (
      (
        not (
          examples_bstree_NodeCondition2[exit_stmt_reached_1])
      )
      and 
      TruePred[]
      and 
      (
        nullDerefBool_5=nullDerefBool_6)
      and 
      (
        examples_bstree_Node_left_1=examples_bstree_Node_left_2)
    )
  )
  and 
  (
    (
      examples_bstree_NodeCondition2[exit_stmt_reached_1]
      and 
      (
        (
          examples_bstree_NodeCondition0[thiz_0]
          and 
          (
            nullDerefBool_7=true)
        )
        or 
        (
          (
            not (
              examples_bstree_NodeCondition0[thiz_0])
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
        examples_bstree_Node_right_2=(examples_bstree_Node_right_1)++((thiz_0)->(null)))
    )
    or 
    (
      (
        not (
          examples_bstree_NodeCondition2[exit_stmt_reached_1])
      )
      and 
      TruePred[]
      and 
      (
        examples_bstree_Node_right_1=examples_bstree_Node_right_2)
      and 
      (
        nullDerefBool_6=nullDerefBool_7)
    )
  )
  and 
  (
    (
      examples_bstree_NodeCondition4[nullDerefBool_7,
                                    throw_1]
      and 
      (
        throw_2=java_lang_NullPointerExceptionLit)
    )
    or 
    (
      (
        not (
          examples_bstree_NodeCondition4[nullDerefBool_7,
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



pred simulate_examples_bstree_BinTree_add_0[
  thiz_0: examples_bstree_BinTree,
  examples_bstree_BinTree_root_0: ( examples_bstree_BinTree ) -> one ( examples_bstree_Node + null ),
  examples_bstree_BinTree_root_1: ( examples_bstree_BinTree ) -> one ( examples_bstree_Node + null ),
  x_0: Int,
  throw_0: java_lang_Throwable + null,
  throw_1: java_lang_Throwable + null,
  throw_2: java_lang_Throwable + null,
  throw_3: java_lang_Throwable + null,
  throw_4: java_lang_Throwable + null,
  throw_5: java_lang_Throwable + null,
  throw_6: java_lang_Throwable + null,
  throw_7: java_lang_Throwable + null,
  throw_8: java_lang_Throwable + null,
  throw_9: java_lang_Throwable + null,
  throw_10: java_lang_Throwable + null,
  throw_11: java_lang_Throwable + null,
  throw_12: java_lang_Throwable + null,
  throw_13: java_lang_Throwable + null,
  throw_14: java_lang_Throwable + null,
  throw_15: java_lang_Throwable + null,
  throw_16: java_lang_Throwable + null,
  throw_17: java_lang_Throwable + null,
  throw_18: java_lang_Throwable + null,
  throw_19: java_lang_Throwable + null,
  throw_20: java_lang_Throwable + null,
  throw_21: java_lang_Throwable + null,
  throw_22: java_lang_Throwable + null,
  throw_23: java_lang_Throwable + null,
  throw_24: java_lang_Throwable + null,
  examples_bstree_Node_right_0: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_1: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_2: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_3: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_4: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_5: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_6: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_7: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_8: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_9: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_10: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_11: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_12: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_13: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_14: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_15: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_16: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_17: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_18: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_19: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_20: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_21: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_22: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_23: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_24: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_25: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_26: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_27: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_28: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_29: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_30: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_31: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_32: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  nodes_0: ( examples_bstree_BinTree ) -> ( examples_bstree_Node ),
  nodes_1: ( examples_bstree_BinTree ) -> ( examples_bstree_Node ),
  examples_bstree_Node_key_0: ( examples_bstree_Node ) -> one ( Int ),
  examples_bstree_Node_key_1: ( examples_bstree_Node ) -> one ( Int ),
  examples_bstree_Node_key_2: ( examples_bstree_Node ) -> one ( Int ),
  examples_bstree_Node_key_3: ( examples_bstree_Node ) -> one ( Int ),
  examples_bstree_Node_key_4: ( examples_bstree_Node ) -> one ( Int ),
  examples_bstree_Node_key_5: ( examples_bstree_Node ) -> one ( Int ),
  examples_bstree_Node_key_6: ( examples_bstree_Node ) -> one ( Int ),
  examples_bstree_Node_key_7: ( examples_bstree_Node ) -> one ( Int ),
  examples_bstree_Node_key_8: ( examples_bstree_Node ) -> one ( Int ),
  examples_bstree_Node_key_9: ( examples_bstree_Node ) -> one ( Int ),
  examples_bstree_Node_key_10: ( examples_bstree_Node ) -> one ( Int ),
  examples_bstree_Node_key_11: ( examples_bstree_Node ) -> one ( Int ),
  examples_bstree_Node_key_12: ( examples_bstree_Node ) -> one ( Int ),
  examples_bstree_Node_key_13: ( examples_bstree_Node ) -> one ( Int ),
  examples_bstree_Node_key_14: ( examples_bstree_Node ) -> one ( Int ),
  examples_bstree_Node_key_15: ( examples_bstree_Node ) -> one ( Int ),
  examples_bstree_Node_key_16: ( examples_bstree_Node ) -> one ( Int ),
  examples_bstree_Node_key_17: ( examples_bstree_Node ) -> one ( Int ),
  examples_bstree_Node_key_18: ( examples_bstree_Node ) -> one ( Int ),
  examples_bstree_Node_key_19: ( examples_bstree_Node ) -> one ( Int ),
  examples_bstree_Node_key_20: ( examples_bstree_Node ) -> one ( Int ),
  examples_bstree_Node_key_21: ( examples_bstree_Node ) -> one ( Int ),
  examples_bstree_Node_key_22: ( examples_bstree_Node ) -> one ( Int ),
  examples_bstree_Node_left_0: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_1: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_2: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_3: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_4: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_5: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_6: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_7: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_8: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_9: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_10: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_11: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_12: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_13: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_14: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_15: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_16: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_17: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_18: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_19: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_20: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_21: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_22: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_23: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_24: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_25: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_26: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_27: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_28: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_29: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_30: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_31: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_32: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  usedObjects_0: set ( java_lang_Object ),
  usedObjects_1: set ( java_lang_Object ),
  usedObjects_2: set ( java_lang_Object ),
  usedObjects_3: set ( java_lang_Object ),
  usedObjects_4: set ( java_lang_Object ),
  usedObjects_5: set ( java_lang_Object ),
  usedObjects_6: set ( java_lang_Object ),
  usedObjects_7: set ( java_lang_Object ),
  usedObjects_8: set ( java_lang_Object ),
  usedObjects_9: set ( java_lang_Object ),
  usedObjects_10: set ( java_lang_Object ),
  usedObjects_11: set ( java_lang_Object ),
  l21_l0_nullDerefBool_0: boolean,
  l21_l0_nullDerefBool_1: boolean,
  l21_l0_nullDerefBool_2: boolean,
  l21_l0_nullDerefBool_3: boolean,
  l21_l0_nullDerefBool_4: boolean,
  l21_l0_nullDerefBool_5: boolean,
  l21_l0_nullDerefBool_6: boolean,
  l21_l0_nullDerefBool_7: boolean,
  l21_l11_exit_stmt_reached_0: boolean,
  l21_l11_exit_stmt_reached_1: boolean,
  l21_l14_exit_stmt_reached_0: boolean,
  l21_l14_exit_stmt_reached_1: boolean,
  l21_l2_nullDerefBool_0: boolean,
  l21_l2_nullDerefBool_1: boolean,
  l21_l2_nullDerefBool_2: boolean,
  l21_l2_nullDerefBool_3: boolean,
  l21_l2_nullDerefBool_4: boolean,
  l21_l2_nullDerefBool_5: boolean,
  l21_l2_nullDerefBool_6: boolean,
  l21_l2_nullDerefBool_7: boolean,
  l21_l16_exit_stmt_reached_0: boolean,
  l21_l16_exit_stmt_reached_1: boolean,
  l21_l5_exit_stmt_reached_0: boolean,
  l21_l5_exit_stmt_reached_1: boolean,
  l21_exit_stmt_reached_1: boolean,
  l21_nullDerefBool_1: boolean,
  l21_nullDerefBool_2: boolean,
  l21_nullDerefBool_3: boolean,
  l21_nullDerefBool_4: boolean,
  l21_nullDerefBool_5: boolean,
  l21_nullDerefBool_6: boolean,
  l21_nullDerefBool_7: boolean,
  l21_nullDerefBool_8: boolean,
  l21_nullDerefBool_9: boolean,
  l21_nullDerefBool_10: boolean,
  l21_nullDerefBool_11: boolean,
  l21_nullDerefBool_12: boolean,
  l21_nullDerefBool_13: boolean,
  l21_nullDerefBool_14: boolean,
  l21_nullDerefBool_15: boolean,
  l21_nullDerefBool_16: boolean,
  l21_nullDerefBool_17: boolean,
  l21_nullDerefBool_18: boolean,
  l21_nullDerefBool_19: boolean,
  l21_nullDerefBool_20: boolean,
  l21_nullDerefBool_21: boolean,
  l21_nullDerefBool_22: boolean,
  l21_nullDerefBool_23: boolean,
  l21_nullDerefBool_24: boolean,
  l21_nullDerefBool_25: boolean,
  l21_nullDerefBool_26: boolean,
  l21_nullDerefBool_27: boolean,
  l21_nullDerefBool_28: boolean,
  l21_nullDerefBool_29: boolean,
  l21_nullDerefBool_30: boolean,
  l21_nullDerefBool_31: boolean,
  l21_nullDerefBool_32: boolean,
  l21_nullDerefBool_33: boolean,
  l21_nullDerefBool_34: boolean,
  l21_l1_exit_stmt_reached_0: boolean,
  l21_l1_exit_stmt_reached_1: boolean,
  l21_l20_exit_stmt_reached_0: boolean,
  l21_l20_exit_stmt_reached_1: boolean,
  l21_l17_exit_stmt_reached_0: boolean,
  l21_l17_exit_stmt_reached_1: boolean,
  l21_l7_exit_stmt_reached_0: boolean,
  l21_l7_exit_stmt_reached_1: boolean,
  l21_l19_exit_stmt_reached_0: boolean,
  l21_l19_exit_stmt_reached_1: boolean,
  l21_l6_nullDerefBool_0: boolean,
  l21_l6_nullDerefBool_1: boolean,
  l21_l6_nullDerefBool_2: boolean,
  l21_l6_nullDerefBool_3: boolean,
  l21_l6_nullDerefBool_4: boolean,
  l21_l6_nullDerefBool_5: boolean,
  l21_l6_nullDerefBool_6: boolean,
  l21_l6_nullDerefBool_7: boolean,
  l21_l9_exit_stmt_reached_0: boolean,
  l21_l9_exit_stmt_reached_1: boolean,
  l21_l12_exit_stmt_reached_0: boolean,
  l21_l12_exit_stmt_reached_1: boolean,
  l21_l10_exit_stmt_reached_0: boolean,
  l21_l10_exit_stmt_reached_1: boolean,
  l21_l13_nullDerefBool_0: boolean,
  l21_l13_nullDerefBool_1: boolean,
  l21_l13_nullDerefBool_2: boolean,
  l21_l13_nullDerefBool_3: boolean,
  l21_l13_nullDerefBool_4: boolean,
  l21_l13_nullDerefBool_5: boolean,
  l21_l13_nullDerefBool_6: boolean,
  l21_l13_nullDerefBool_7: boolean,
  l21_l4_nullDerefBool_0: boolean,
  l21_l4_nullDerefBool_1: boolean,
  l21_l4_nullDerefBool_2: boolean,
  l21_l4_nullDerefBool_3: boolean,
  l21_l4_nullDerefBool_4: boolean,
  l21_l4_nullDerefBool_5: boolean,
  l21_l4_nullDerefBool_6: boolean,
  l21_l4_nullDerefBool_7: boolean,
  l21_l0_exit_stmt_reached_0: boolean,
  l21_l0_exit_stmt_reached_1: boolean,
  l21_l16_nullDerefBool_0: boolean,
  l21_l16_nullDerefBool_1: boolean,
  l21_l16_nullDerefBool_2: boolean,
  l21_l16_nullDerefBool_3: boolean,
  l21_l16_nullDerefBool_4: boolean,
  l21_l16_nullDerefBool_5: boolean,
  l21_l16_nullDerefBool_6: boolean,
  l21_l16_nullDerefBool_7: boolean,
  l21_l18_exit_stmt_reached_0: boolean,
  l21_l18_exit_stmt_reached_1: boolean,
  l21_l20_nullDerefBool_0: boolean,
  l21_l20_nullDerefBool_1: boolean,
  l21_l20_nullDerefBool_2: boolean,
  l21_l20_nullDerefBool_3: boolean,
  l21_l20_nullDerefBool_4: boolean,
  l21_l20_nullDerefBool_5: boolean,
  l21_l20_nullDerefBool_6: boolean,
  l21_l20_nullDerefBool_7: boolean,
  l21_l1_nullDerefBool_0: boolean,
  l21_l1_nullDerefBool_1: boolean,
  l21_l1_nullDerefBool_2: boolean,
  l21_l1_nullDerefBool_3: boolean,
  l21_l1_nullDerefBool_4: boolean,
  l21_l1_nullDerefBool_5: boolean,
  l21_l1_nullDerefBool_6: boolean,
  l21_l1_nullDerefBool_7: boolean,
  l21_l17_nullDerefBool_0: boolean,
  l21_l17_nullDerefBool_1: boolean,
  l21_l17_nullDerefBool_2: boolean,
  l21_l17_nullDerefBool_3: boolean,
  l21_l17_nullDerefBool_4: boolean,
  l21_l17_nullDerefBool_5: boolean,
  l21_l17_nullDerefBool_6: boolean,
  l21_l17_nullDerefBool_7: boolean,
  l21_l13_exit_stmt_reached_0: boolean,
  l21_l13_exit_stmt_reached_1: boolean,
  l21_l18_nullDerefBool_0: boolean,
  l21_l18_nullDerefBool_1: boolean,
  l21_l18_nullDerefBool_2: boolean,
  l21_l18_nullDerefBool_3: boolean,
  l21_l18_nullDerefBool_4: boolean,
  l21_l18_nullDerefBool_5: boolean,
  l21_l18_nullDerefBool_6: boolean,
  l21_l18_nullDerefBool_7: boolean,
  l21_l12_nullDerefBool_0: boolean,
  l21_l12_nullDerefBool_1: boolean,
  l21_l12_nullDerefBool_2: boolean,
  l21_l12_nullDerefBool_3: boolean,
  l21_l12_nullDerefBool_4: boolean,
  l21_l12_nullDerefBool_5: boolean,
  l21_l12_nullDerefBool_6: boolean,
  l21_l12_nullDerefBool_7: boolean,
  l21_l6_exit_stmt_reached_0: boolean,
  l21_l6_exit_stmt_reached_1: boolean,
  l21_l11_nullDerefBool_0: boolean,
  l21_l11_nullDerefBool_1: boolean,
  l21_l11_nullDerefBool_2: boolean,
  l21_l11_nullDerefBool_3: boolean,
  l21_l11_nullDerefBool_4: boolean,
  l21_l11_nullDerefBool_5: boolean,
  l21_l11_nullDerefBool_6: boolean,
  l21_l11_nullDerefBool_7: boolean,
  l21_l15_nullDerefBool_0: boolean,
  l21_l15_nullDerefBool_1: boolean,
  l21_l15_nullDerefBool_2: boolean,
  l21_l15_nullDerefBool_3: boolean,
  l21_l15_nullDerefBool_4: boolean,
  l21_l15_nullDerefBool_5: boolean,
  l21_l15_nullDerefBool_6: boolean,
  l21_l15_nullDerefBool_7: boolean,
  l21_l4_exit_stmt_reached_0: boolean,
  l21_l4_exit_stmt_reached_1: boolean,
  l21_var_2_ws_1_0: boolean,
  l21_var_2_ws_1_1: boolean,
  l21_var_2_ws_1_2: boolean,
  l21_var_2_ws_1_3: boolean,
  l21_var_2_ws_1_4: boolean,
  l21_var_2_ws_1_5: boolean,
  l21_var_2_ws_1_6: boolean,
  l21_var_2_ws_1_7: boolean,
  l21_var_2_ws_1_8: boolean,
  l21_var_2_ws_1_9: boolean,
  l21_var_2_ws_1_10: boolean,
  l21_var_2_ws_1_11: boolean,
  l21_var_1_current_0: examples_bstree_Node + null,
  l21_var_1_current_1: examples_bstree_Node + null,
  l21_var_1_current_2: examples_bstree_Node + null,
  l21_var_1_current_3: examples_bstree_Node + null,
  l21_var_1_current_4: examples_bstree_Node + null,
  l21_var_1_current_5: examples_bstree_Node + null,
  l21_var_1_current_6: examples_bstree_Node + null,
  l21_var_1_current_7: examples_bstree_Node + null,
  l21_var_1_current_8: examples_bstree_Node + null,
  l21_var_1_current_9: examples_bstree_Node + null,
  l21_var_1_current_10: examples_bstree_Node + null,
  l21_var_1_current_11: examples_bstree_Node + null,
  l21_l7_nullDerefBool_0: boolean,
  l21_l7_nullDerefBool_1: boolean,
  l21_l7_nullDerefBool_2: boolean,
  l21_l7_nullDerefBool_3: boolean,
  l21_l7_nullDerefBool_4: boolean,
  l21_l7_nullDerefBool_5: boolean,
  l21_l7_nullDerefBool_6: boolean,
  l21_l7_nullDerefBool_7: boolean,
  l21_l8_exit_stmt_reached_0: boolean,
  l21_l8_exit_stmt_reached_1: boolean,
  l21_l5_nullDerefBool_0: boolean,
  l21_l5_nullDerefBool_1: boolean,
  l21_l5_nullDerefBool_2: boolean,
  l21_l5_nullDerefBool_3: boolean,
  l21_l5_nullDerefBool_4: boolean,
  l21_l5_nullDerefBool_5: boolean,
  l21_l5_nullDerefBool_6: boolean,
  l21_l5_nullDerefBool_7: boolean,
  l21_l14_nullDerefBool_0: boolean,
  l21_l14_nullDerefBool_1: boolean,
  l21_l14_nullDerefBool_2: boolean,
  l21_l14_nullDerefBool_3: boolean,
  l21_l14_nullDerefBool_4: boolean,
  l21_l14_nullDerefBool_5: boolean,
  l21_l14_nullDerefBool_6: boolean,
  l21_l14_nullDerefBool_7: boolean,
  l21_l9_nullDerefBool_0: boolean,
  l21_l9_nullDerefBool_1: boolean,
  l21_l9_nullDerefBool_2: boolean,
  l21_l9_nullDerefBool_3: boolean,
  l21_l9_nullDerefBool_4: boolean,
  l21_l9_nullDerefBool_5: boolean,
  l21_l9_nullDerefBool_6: boolean,
  l21_l9_nullDerefBool_7: boolean,
  l21_es_var__1_0: examples_bstree_Node + null,
  l21_es_var__1_1: examples_bstree_Node + null,
  l21_l2_exit_stmt_reached_0: boolean,
  l21_l2_exit_stmt_reached_1: boolean,
  l21_l15_exit_stmt_reached_0: boolean,
  l21_l15_exit_stmt_reached_1: boolean,
  l21_l19_nullDerefBool_0: boolean,
  l21_l19_nullDerefBool_1: boolean,
  l21_l19_nullDerefBool_2: boolean,
  l21_l19_nullDerefBool_3: boolean,
  l21_l19_nullDerefBool_4: boolean,
  l21_l19_nullDerefBool_5: boolean,
  l21_l19_nullDerefBool_6: boolean,
  l21_l19_nullDerefBool_7: boolean,
  l21_l10_nullDerefBool_0: boolean,
  l21_l10_nullDerefBool_1: boolean,
  l21_l10_nullDerefBool_2: boolean,
  l21_l10_nullDerefBool_3: boolean,
  l21_l10_nullDerefBool_4: boolean,
  l21_l10_nullDerefBool_5: boolean,
  l21_l10_nullDerefBool_6: boolean,
  l21_l10_nullDerefBool_7: boolean,
  l21_l3_exit_stmt_reached_0: boolean,
  l21_l3_exit_stmt_reached_1: boolean,
  l21_l8_nullDerefBool_0: boolean,
  l21_l8_nullDerefBool_1: boolean,
  l21_l8_nullDerefBool_2: boolean,
  l21_l8_nullDerefBool_3: boolean,
  l21_l8_nullDerefBool_4: boolean,
  l21_l8_nullDerefBool_5: boolean,
  l21_l8_nullDerefBool_6: boolean,
  l21_l8_nullDerefBool_7: boolean,
  l21_l3_nullDerefBool_0: boolean,
  l21_l3_nullDerefBool_1: boolean,
  l21_l3_nullDerefBool_2: boolean,
  l21_l3_nullDerefBool_3: boolean,
  l21_l3_nullDerefBool_4: boolean,
  l21_l3_nullDerefBool_5: boolean,
  l21_l3_nullDerefBool_6: boolean,
  l21_l3_nullDerefBool_7: boolean,
  l21_es_var__3_0: examples_bstree_Node + null,
  l21_es_var__3_1: examples_bstree_Node + null,
  l21_es_var__3_2: examples_bstree_Node + null,
  l21_es_var__3_3: examples_bstree_Node + null,
  l21_es_var__3_4: examples_bstree_Node + null,
  l21_es_var__3_5: examples_bstree_Node + null,
  l21_es_var__3_6: examples_bstree_Node + null,
  l21_es_var__3_7: examples_bstree_Node + null,
  l21_es_var__3_8: examples_bstree_Node + null,
  l21_es_var__3_9: examples_bstree_Node + null,
  l21_es_var__3_10: examples_bstree_Node + null,
  l21_es_var__2_0: examples_bstree_Node + null,
  l21_es_var__2_1: examples_bstree_Node + null,
  l21_es_var__2_2: examples_bstree_Node + null,
  l21_es_var__2_3: examples_bstree_Node + null,
  l21_es_var__2_4: examples_bstree_Node + null,
  l21_es_var__2_5: examples_bstree_Node + null,
  l21_es_var__2_6: examples_bstree_Node + null,
  l21_es_var__2_7: examples_bstree_Node + null,
  l21_es_var__2_8: examples_bstree_Node + null,
  l21_es_var__2_9: examples_bstree_Node + null,
  l21_es_var__2_10: examples_bstree_Node + null
]{
  precondition_examples_bstree_BinTree_add_0[examples_bstree_BinTree_root_0,
                                            examples_bstree_Node_key_0,
                                            examples_bstree_Node_left_0,
                                            examples_bstree_Node_right_0,
                                            nodes_0,
                                            thiz_0,
                                            throw_0,
                                            usedObjects_0]
  and 
  examples_bstree_BinTree_add_0[thiz_0,
                               throw_1,
                               throw_2,
                               throw_3,
                               throw_4,
                               throw_5,
                               throw_6,
                               throw_7,
                               throw_8,
                               throw_9,
                               throw_10,
                               throw_11,
                               throw_12,
                               throw_13,
                               throw_14,
                               throw_15,
                               throw_16,
                               throw_17,
                               throw_18,
                               throw_19,
                               throw_20,
                               throw_21,
                               throw_22,
                               throw_23,
                               throw_24,
                               x_0,
                               examples_bstree_Node_right_0,
                               examples_bstree_Node_right_1,
                               examples_bstree_Node_right_2,
                               examples_bstree_Node_right_3,
                               examples_bstree_Node_right_4,
                               examples_bstree_Node_right_5,
                               examples_bstree_Node_right_6,
                               examples_bstree_Node_right_7,
                               examples_bstree_Node_right_8,
                               examples_bstree_Node_right_9,
                               examples_bstree_Node_right_10,
                               examples_bstree_Node_right_11,
                               examples_bstree_Node_right_12,
                               examples_bstree_Node_right_13,
                               examples_bstree_Node_right_14,
                               examples_bstree_Node_right_15,
                               examples_bstree_Node_right_16,
                               examples_bstree_Node_right_17,
                               examples_bstree_Node_right_18,
                               examples_bstree_Node_right_19,
                               examples_bstree_Node_right_20,
                               examples_bstree_Node_right_21,
                               examples_bstree_Node_right_22,
                               examples_bstree_Node_right_23,
                               examples_bstree_Node_right_24,
                               examples_bstree_Node_right_25,
                               examples_bstree_Node_right_26,
                               examples_bstree_Node_right_27,
                               examples_bstree_Node_right_28,
                               examples_bstree_Node_right_29,
                               examples_bstree_Node_right_30,
                               examples_bstree_Node_right_31,
                               examples_bstree_Node_right_32,
                               examples_bstree_Node_key_0,
                               examples_bstree_Node_key_1,
                               examples_bstree_Node_key_2,
                               examples_bstree_Node_key_3,
                               examples_bstree_Node_key_4,
                               examples_bstree_Node_key_5,
                               examples_bstree_Node_key_6,
                               examples_bstree_Node_key_7,
                               examples_bstree_Node_key_8,
                               examples_bstree_Node_key_9,
                               examples_bstree_Node_key_10,
                               examples_bstree_Node_key_11,
                               examples_bstree_Node_key_12,
                               examples_bstree_Node_key_13,
                               examples_bstree_Node_key_14,
                               examples_bstree_Node_key_15,
                               examples_bstree_Node_key_16,
                               examples_bstree_Node_key_17,
                               examples_bstree_Node_key_18,
                               examples_bstree_Node_key_19,
                               examples_bstree_Node_key_20,
                               examples_bstree_Node_key_21,
                               examples_bstree_Node_key_22,
                               examples_bstree_BinTree_root_0,
                               examples_bstree_BinTree_root_1,
                               examples_bstree_Node_left_0,
                               examples_bstree_Node_left_1,
                               examples_bstree_Node_left_2,
                               examples_bstree_Node_left_3,
                               examples_bstree_Node_left_4,
                               examples_bstree_Node_left_5,
                               examples_bstree_Node_left_6,
                               examples_bstree_Node_left_7,
                               examples_bstree_Node_left_8,
                               examples_bstree_Node_left_9,
                               examples_bstree_Node_left_10,
                               examples_bstree_Node_left_11,
                               examples_bstree_Node_left_12,
                               examples_bstree_Node_left_13,
                               examples_bstree_Node_left_14,
                               examples_bstree_Node_left_15,
                               examples_bstree_Node_left_16,
                               examples_bstree_Node_left_17,
                               examples_bstree_Node_left_18,
                               examples_bstree_Node_left_19,
                               examples_bstree_Node_left_20,
                               examples_bstree_Node_left_21,
                               examples_bstree_Node_left_22,
                               examples_bstree_Node_left_23,
                               examples_bstree_Node_left_24,
                               examples_bstree_Node_left_25,
                               examples_bstree_Node_left_26,
                               examples_bstree_Node_left_27,
                               examples_bstree_Node_left_28,
                               examples_bstree_Node_left_29,
                               examples_bstree_Node_left_30,
                               examples_bstree_Node_left_31,
                               examples_bstree_Node_left_32,
                               usedObjects_0,
                               usedObjects_1,
                               usedObjects_2,
                               usedObjects_3,
                               usedObjects_4,
                               usedObjects_5,
                               usedObjects_6,
                               usedObjects_7,
                               usedObjects_8,
                               usedObjects_9,
                               usedObjects_10,
                               usedObjects_11,
                               l21_es_var__3_0,
                               l21_es_var__3_1,
                               l21_es_var__3_2,
                               l21_es_var__3_3,
                               l21_es_var__3_4,
                               l21_es_var__3_5,
                               l21_es_var__3_6,
                               l21_es_var__3_7,
                               l21_es_var__3_8,
                               l21_es_var__3_9,
                               l21_es_var__3_10,
                               l21_exit_stmt_reached_1,
                               l21_es_var__1_0,
                               l21_es_var__1_1,
                               l21_var_1_current_0,
                               l21_var_1_current_1,
                               l21_var_1_current_2,
                               l21_var_1_current_3,
                               l21_var_1_current_4,
                               l21_var_1_current_5,
                               l21_var_1_current_6,
                               l21_var_1_current_7,
                               l21_var_1_current_8,
                               l21_var_1_current_9,
                               l21_var_1_current_10,
                               l21_var_1_current_11,
                               l21_es_var__2_0,
                               l21_es_var__2_1,
                               l21_es_var__2_2,
                               l21_es_var__2_3,
                               l21_es_var__2_4,
                               l21_es_var__2_5,
                               l21_es_var__2_6,
                               l21_es_var__2_7,
                               l21_es_var__2_8,
                               l21_es_var__2_9,
                               l21_es_var__2_10,
                               l21_nullDerefBool_1,
                               l21_nullDerefBool_2,
                               l21_nullDerefBool_3,
                               l21_nullDerefBool_4,
                               l21_nullDerefBool_5,
                               l21_nullDerefBool_6,
                               l21_nullDerefBool_7,
                               l21_nullDerefBool_8,
                               l21_nullDerefBool_9,
                               l21_nullDerefBool_10,
                               l21_nullDerefBool_11,
                               l21_nullDerefBool_12,
                               l21_nullDerefBool_13,
                               l21_nullDerefBool_14,
                               l21_nullDerefBool_15,
                               l21_nullDerefBool_16,
                               l21_nullDerefBool_17,
                               l21_nullDerefBool_18,
                               l21_nullDerefBool_19,
                               l21_nullDerefBool_20,
                               l21_nullDerefBool_21,
                               l21_nullDerefBool_22,
                               l21_nullDerefBool_23,
                               l21_nullDerefBool_24,
                               l21_nullDerefBool_25,
                               l21_nullDerefBool_26,
                               l21_nullDerefBool_27,
                               l21_nullDerefBool_28,
                               l21_nullDerefBool_29,
                               l21_nullDerefBool_30,
                               l21_nullDerefBool_31,
                               l21_nullDerefBool_32,
                               l21_nullDerefBool_33,
                               l21_nullDerefBool_34,
                               l21_var_2_ws_1_0,
                               l21_var_2_ws_1_1,
                               l21_var_2_ws_1_2,
                               l21_var_2_ws_1_3,
                               l21_var_2_ws_1_4,
                               l21_var_2_ws_1_5,
                               l21_var_2_ws_1_6,
                               l21_var_2_ws_1_7,
                               l21_var_2_ws_1_8,
                               l21_var_2_ws_1_9,
                               l21_var_2_ws_1_10,
                               l21_var_2_ws_1_11,
                               l21_l9_exit_stmt_reached_0,
                               l21_l9_exit_stmt_reached_1,
                               l21_l8_nullDerefBool_0,
                               l21_l8_nullDerefBool_1,
                               l21_l8_nullDerefBool_2,
                               l21_l8_nullDerefBool_3,
                               l21_l8_nullDerefBool_4,
                               l21_l8_nullDerefBool_5,
                               l21_l8_nullDerefBool_6,
                               l21_l8_nullDerefBool_7,
                               l21_l13_nullDerefBool_0,
                               l21_l13_nullDerefBool_1,
                               l21_l13_nullDerefBool_2,
                               l21_l13_nullDerefBool_3,
                               l21_l13_nullDerefBool_4,
                               l21_l13_nullDerefBool_5,
                               l21_l13_nullDerefBool_6,
                               l21_l13_nullDerefBool_7,
                               l21_l0_exit_stmt_reached_0,
                               l21_l0_exit_stmt_reached_1,
                               l21_l6_exit_stmt_reached_0,
                               l21_l6_exit_stmt_reached_1,
                               l21_l16_nullDerefBool_0,
                               l21_l16_nullDerefBool_1,
                               l21_l16_nullDerefBool_2,
                               l21_l16_nullDerefBool_3,
                               l21_l16_nullDerefBool_4,
                               l21_l16_nullDerefBool_5,
                               l21_l16_nullDerefBool_6,
                               l21_l16_nullDerefBool_7,
                               l21_l3_exit_stmt_reached_0,
                               l21_l3_exit_stmt_reached_1,
                               l21_l18_exit_stmt_reached_0,
                               l21_l18_exit_stmt_reached_1,
                               l21_l5_exit_stmt_reached_0,
                               l21_l5_exit_stmt_reached_1,
                               l21_l11_nullDerefBool_0,
                               l21_l11_nullDerefBool_1,
                               l21_l11_nullDerefBool_2,
                               l21_l11_nullDerefBool_3,
                               l21_l11_nullDerefBool_4,
                               l21_l11_nullDerefBool_5,
                               l21_l11_nullDerefBool_6,
                               l21_l11_nullDerefBool_7,
                               l21_l0_nullDerefBool_0,
                               l21_l0_nullDerefBool_1,
                               l21_l0_nullDerefBool_2,
                               l21_l0_nullDerefBool_3,
                               l21_l0_nullDerefBool_4,
                               l21_l0_nullDerefBool_5,
                               l21_l0_nullDerefBool_6,
                               l21_l0_nullDerefBool_7,
                               l21_l12_exit_stmt_reached_0,
                               l21_l12_exit_stmt_reached_1,
                               l21_l2_nullDerefBool_0,
                               l21_l2_nullDerefBool_1,
                               l21_l2_nullDerefBool_2,
                               l21_l2_nullDerefBool_3,
                               l21_l2_nullDerefBool_4,
                               l21_l2_nullDerefBool_5,
                               l21_l2_nullDerefBool_6,
                               l21_l2_nullDerefBool_7,
                               l21_l7_nullDerefBool_0,
                               l21_l7_nullDerefBool_1,
                               l21_l7_nullDerefBool_2,
                               l21_l7_nullDerefBool_3,
                               l21_l7_nullDerefBool_4,
                               l21_l7_nullDerefBool_5,
                               l21_l7_nullDerefBool_6,
                               l21_l7_nullDerefBool_7,
                               l21_l16_exit_stmt_reached_0,
                               l21_l16_exit_stmt_reached_1,
                               l21_l20_exit_stmt_reached_0,
                               l21_l20_exit_stmt_reached_1,
                               l21_l4_exit_stmt_reached_0,
                               l21_l4_exit_stmt_reached_1,
                               l21_l15_exit_stmt_reached_0,
                               l21_l15_exit_stmt_reached_1,
                               l21_l14_nullDerefBool_0,
                               l21_l14_nullDerefBool_1,
                               l21_l14_nullDerefBool_2,
                               l21_l14_nullDerefBool_3,
                               l21_l14_nullDerefBool_4,
                               l21_l14_nullDerefBool_5,
                               l21_l14_nullDerefBool_6,
                               l21_l14_nullDerefBool_7,
                               l21_l19_nullDerefBool_0,
                               l21_l19_nullDerefBool_1,
                               l21_l19_nullDerefBool_2,
                               l21_l19_nullDerefBool_3,
                               l21_l19_nullDerefBool_4,
                               l21_l19_nullDerefBool_5,
                               l21_l19_nullDerefBool_6,
                               l21_l19_nullDerefBool_7,
                               l21_l1_exit_stmt_reached_0,
                               l21_l1_exit_stmt_reached_1,
                               l21_l2_exit_stmt_reached_0,
                               l21_l2_exit_stmt_reached_1,
                               l21_l14_exit_stmt_reached_0,
                               l21_l14_exit_stmt_reached_1,
                               l21_l4_nullDerefBool_0,
                               l21_l4_nullDerefBool_1,
                               l21_l4_nullDerefBool_2,
                               l21_l4_nullDerefBool_3,
                               l21_l4_nullDerefBool_4,
                               l21_l4_nullDerefBool_5,
                               l21_l4_nullDerefBool_6,
                               l21_l4_nullDerefBool_7,
                               l21_l19_exit_stmt_reached_0,
                               l21_l19_exit_stmt_reached_1,
                               l21_l8_exit_stmt_reached_0,
                               l21_l8_exit_stmt_reached_1,
                               l21_l13_exit_stmt_reached_0,
                               l21_l13_exit_stmt_reached_1,
                               l21_l9_nullDerefBool_0,
                               l21_l9_nullDerefBool_1,
                               l21_l9_nullDerefBool_2,
                               l21_l9_nullDerefBool_3,
                               l21_l9_nullDerefBool_4,
                               l21_l9_nullDerefBool_5,
                               l21_l9_nullDerefBool_6,
                               l21_l9_nullDerefBool_7,
                               l21_l5_nullDerefBool_0,
                               l21_l5_nullDerefBool_1,
                               l21_l5_nullDerefBool_2,
                               l21_l5_nullDerefBool_3,
                               l21_l5_nullDerefBool_4,
                               l21_l5_nullDerefBool_5,
                               l21_l5_nullDerefBool_6,
                               l21_l5_nullDerefBool_7,
                               l21_l11_exit_stmt_reached_0,
                               l21_l11_exit_stmt_reached_1,
                               l21_l6_nullDerefBool_0,
                               l21_l6_nullDerefBool_1,
                               l21_l6_nullDerefBool_2,
                               l21_l6_nullDerefBool_3,
                               l21_l6_nullDerefBool_4,
                               l21_l6_nullDerefBool_5,
                               l21_l6_nullDerefBool_6,
                               l21_l6_nullDerefBool_7,
                               l21_l17_exit_stmt_reached_0,
                               l21_l17_exit_stmt_reached_1,
                               l21_l18_nullDerefBool_0,
                               l21_l18_nullDerefBool_1,
                               l21_l18_nullDerefBool_2,
                               l21_l18_nullDerefBool_3,
                               l21_l18_nullDerefBool_4,
                               l21_l18_nullDerefBool_5,
                               l21_l18_nullDerefBool_6,
                               l21_l18_nullDerefBool_7,
                               l21_l3_nullDerefBool_0,
                               l21_l3_nullDerefBool_1,
                               l21_l3_nullDerefBool_2,
                               l21_l3_nullDerefBool_3,
                               l21_l3_nullDerefBool_4,
                               l21_l3_nullDerefBool_5,
                               l21_l3_nullDerefBool_6,
                               l21_l3_nullDerefBool_7,
                               l21_l20_nullDerefBool_0,
                               l21_l20_nullDerefBool_1,
                               l21_l20_nullDerefBool_2,
                               l21_l20_nullDerefBool_3,
                               l21_l20_nullDerefBool_4,
                               l21_l20_nullDerefBool_5,
                               l21_l20_nullDerefBool_6,
                               l21_l20_nullDerefBool_7,
                               l21_l15_nullDerefBool_0,
                               l21_l15_nullDerefBool_1,
                               l21_l15_nullDerefBool_2,
                               l21_l15_nullDerefBool_3,
                               l21_l15_nullDerefBool_4,
                               l21_l15_nullDerefBool_5,
                               l21_l15_nullDerefBool_6,
                               l21_l15_nullDerefBool_7,
                               l21_l1_nullDerefBool_0,
                               l21_l1_nullDerefBool_1,
                               l21_l1_nullDerefBool_2,
                               l21_l1_nullDerefBool_3,
                               l21_l1_nullDerefBool_4,
                               l21_l1_nullDerefBool_5,
                               l21_l1_nullDerefBool_6,
                               l21_l1_nullDerefBool_7,
                               l21_l12_nullDerefBool_0,
                               l21_l12_nullDerefBool_1,
                               l21_l12_nullDerefBool_2,
                               l21_l12_nullDerefBool_3,
                               l21_l12_nullDerefBool_4,
                               l21_l12_nullDerefBool_5,
                               l21_l12_nullDerefBool_6,
                               l21_l12_nullDerefBool_7,
                               l21_l7_exit_stmt_reached_0,
                               l21_l7_exit_stmt_reached_1,
                               l21_l17_nullDerefBool_0,
                               l21_l17_nullDerefBool_1,
                               l21_l17_nullDerefBool_2,
                               l21_l17_nullDerefBool_3,
                               l21_l17_nullDerefBool_4,
                               l21_l17_nullDerefBool_5,
                               l21_l17_nullDerefBool_6,
                               l21_l17_nullDerefBool_7,
                               l21_l10_exit_stmt_reached_0,
                               l21_l10_exit_stmt_reached_1,
                               l21_l10_nullDerefBool_0,
                               l21_l10_nullDerefBool_1,
                               l21_l10_nullDerefBool_2,
                               l21_l10_nullDerefBool_3,
                               l21_l10_nullDerefBool_4,
                               l21_l10_nullDerefBool_5,
                               l21_l10_nullDerefBool_6,
                               l21_l10_nullDerefBool_7]
  and 
  havocVariable2[nodes_1]
  and 
  examples_bstree_BinTreeCondition18[examples_bstree_BinTree_root_1,
                                    examples_bstree_Node_left_32,
                                    examples_bstree_Node_right_32,
                                    nodes_1,
                                    thiz_0]
  and 
  postcondition_examples_bstree_BinTree_add_0[examples_bstree_BinTree_root_1,
                                             examples_bstree_Node_key_22,
                                             examples_bstree_Node_left_32,
                                             examples_bstree_Node_right_32,
                                             nodes_0,
                                             nodes_1,
                                             thiz_0,
                                             thiz_0,
                                             throw_24,
                                             x_0]

}

one sig QF {
  examples_bstree_BinTree_root_0: ( examples_bstree_BinTree ) -> one ( examples_bstree_Node + null ),
  examples_bstree_BinTree_root_1: ( examples_bstree_BinTree ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_key_0: ( examples_bstree_Node ) -> one ( Int ),
  examples_bstree_Node_key_1: ( examples_bstree_Node ) -> one ( Int ),
  examples_bstree_Node_key_10: ( examples_bstree_Node ) -> one ( Int ),
  examples_bstree_Node_key_11: ( examples_bstree_Node ) -> one ( Int ),
  examples_bstree_Node_key_12: ( examples_bstree_Node ) -> one ( Int ),
  examples_bstree_Node_key_13: ( examples_bstree_Node ) -> one ( Int ),
  examples_bstree_Node_key_14: ( examples_bstree_Node ) -> one ( Int ),
  examples_bstree_Node_key_15: ( examples_bstree_Node ) -> one ( Int ),
  examples_bstree_Node_key_16: ( examples_bstree_Node ) -> one ( Int ),
  examples_bstree_Node_key_17: ( examples_bstree_Node ) -> one ( Int ),
  examples_bstree_Node_key_18: ( examples_bstree_Node ) -> one ( Int ),
  examples_bstree_Node_key_19: ( examples_bstree_Node ) -> one ( Int ),
  examples_bstree_Node_key_2: ( examples_bstree_Node ) -> one ( Int ),
  examples_bstree_Node_key_20: ( examples_bstree_Node ) -> one ( Int ),
  examples_bstree_Node_key_21: ( examples_bstree_Node ) -> one ( Int ),
  examples_bstree_Node_key_22: ( examples_bstree_Node ) -> one ( Int ),
  examples_bstree_Node_key_3: ( examples_bstree_Node ) -> one ( Int ),
  examples_bstree_Node_key_4: ( examples_bstree_Node ) -> one ( Int ),
  examples_bstree_Node_key_5: ( examples_bstree_Node ) -> one ( Int ),
  examples_bstree_Node_key_6: ( examples_bstree_Node ) -> one ( Int ),
  examples_bstree_Node_key_7: ( examples_bstree_Node ) -> one ( Int ),
  examples_bstree_Node_key_8: ( examples_bstree_Node ) -> one ( Int ),
  examples_bstree_Node_key_9: ( examples_bstree_Node ) -> one ( Int ),
  bexamples_bstree_Node_left_0,fexamples_bstree_Node_left_0: ( examples_bstree_Node ) -> lone ( examples_bstree_Node + null ),
  examples_bstree_Node_left_1: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_10: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_11: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_12: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_13: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_14: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_15: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_16: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_17: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_18: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_19: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_2: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_20: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_21: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_22: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_23: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_24: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_25: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_26: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_27: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_28: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_29: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_3: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_30: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_31: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_32: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_4: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_5: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_6: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_7: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_8: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_left_9: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  bexamples_bstree_Node_right_0,fexamples_bstree_Node_right_0: ( examples_bstree_Node ) -> lone ( examples_bstree_Node + null ),
  examples_bstree_Node_right_1: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_10: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_11: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_12: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_13: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_14: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_15: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_16: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_17: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_18: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_19: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_2: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_20: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_21: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_22: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_23: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_24: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_25: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_26: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_27: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_28: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_29: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_3: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_30: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_31: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_32: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_4: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_5: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_6: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_7: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_8: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  examples_bstree_Node_right_9: ( examples_bstree_Node ) -> one ( examples_bstree_Node + null ),
  l22_es_var__1_0: examples_bstree_Node + null,
  l22_es_var__1_1: examples_bstree_Node + null,
  l22_es_var__2_0: examples_bstree_Node + null,
  l22_es_var__2_1: examples_bstree_Node + null,
  l22_es_var__2_10: examples_bstree_Node + null,
  l22_es_var__2_2: examples_bstree_Node + null,
  l22_es_var__2_3: examples_bstree_Node + null,
  l22_es_var__2_4: examples_bstree_Node + null,
  l22_es_var__2_5: examples_bstree_Node + null,
  l22_es_var__2_6: examples_bstree_Node + null,
  l22_es_var__2_7: examples_bstree_Node + null,
  l22_es_var__2_8: examples_bstree_Node + null,
  l22_es_var__2_9: examples_bstree_Node + null,
  l22_es_var__3_0: examples_bstree_Node + null,
  l22_es_var__3_1: examples_bstree_Node + null,
  l22_es_var__3_10: examples_bstree_Node + null,
  l22_es_var__3_2: examples_bstree_Node + null,
  l22_es_var__3_3: examples_bstree_Node + null,
  l22_es_var__3_4: examples_bstree_Node + null,
  l22_es_var__3_5: examples_bstree_Node + null,
  l22_es_var__3_6: examples_bstree_Node + null,
  l22_es_var__3_7: examples_bstree_Node + null,
  l22_es_var__3_8: examples_bstree_Node + null,
  l22_es_var__3_9: examples_bstree_Node + null,
  l22_exit_stmt_reached_1: boolean,
  l22_l0_exit_stmt_reached_0: boolean,
  l22_l0_exit_stmt_reached_1: boolean,
  l22_l0_nullDerefBool_0: boolean,
  l22_l0_nullDerefBool_1: boolean,
  l22_l0_nullDerefBool_2: boolean,
  l22_l0_nullDerefBool_3: boolean,
  l22_l0_nullDerefBool_4: boolean,
  l22_l0_nullDerefBool_5: boolean,
  l22_l0_nullDerefBool_6: boolean,
  l22_l0_nullDerefBool_7: boolean,
  l22_l10_exit_stmt_reached_0: boolean,
  l22_l10_exit_stmt_reached_1: boolean,
  l22_l10_nullDerefBool_0: boolean,
  l22_l10_nullDerefBool_1: boolean,
  l22_l10_nullDerefBool_2: boolean,
  l22_l10_nullDerefBool_3: boolean,
  l22_l10_nullDerefBool_4: boolean,
  l22_l10_nullDerefBool_5: boolean,
  l22_l10_nullDerefBool_6: boolean,
  l22_l10_nullDerefBool_7: boolean,
  l22_l11_exit_stmt_reached_0: boolean,
  l22_l11_exit_stmt_reached_1: boolean,
  l22_l11_nullDerefBool_0: boolean,
  l22_l11_nullDerefBool_1: boolean,
  l22_l11_nullDerefBool_2: boolean,
  l22_l11_nullDerefBool_3: boolean,
  l22_l11_nullDerefBool_4: boolean,
  l22_l11_nullDerefBool_5: boolean,
  l22_l11_nullDerefBool_6: boolean,
  l22_l11_nullDerefBool_7: boolean,
  l22_l12_exit_stmt_reached_0: boolean,
  l22_l12_exit_stmt_reached_1: boolean,
  l22_l12_nullDerefBool_0: boolean,
  l22_l12_nullDerefBool_1: boolean,
  l22_l12_nullDerefBool_2: boolean,
  l22_l12_nullDerefBool_3: boolean,
  l22_l12_nullDerefBool_4: boolean,
  l22_l12_nullDerefBool_5: boolean,
  l22_l12_nullDerefBool_6: boolean,
  l22_l12_nullDerefBool_7: boolean,
  l22_l13_exit_stmt_reached_0: boolean,
  l22_l13_exit_stmt_reached_1: boolean,
  l22_l13_nullDerefBool_0: boolean,
  l22_l13_nullDerefBool_1: boolean,
  l22_l13_nullDerefBool_2: boolean,
  l22_l13_nullDerefBool_3: boolean,
  l22_l13_nullDerefBool_4: boolean,
  l22_l13_nullDerefBool_5: boolean,
  l22_l13_nullDerefBool_6: boolean,
  l22_l13_nullDerefBool_7: boolean,
  l22_l14_exit_stmt_reached_0: boolean,
  l22_l14_exit_stmt_reached_1: boolean,
  l22_l14_nullDerefBool_0: boolean,
  l22_l14_nullDerefBool_1: boolean,
  l22_l14_nullDerefBool_2: boolean,
  l22_l14_nullDerefBool_3: boolean,
  l22_l14_nullDerefBool_4: boolean,
  l22_l14_nullDerefBool_5: boolean,
  l22_l14_nullDerefBool_6: boolean,
  l22_l14_nullDerefBool_7: boolean,
  l22_l15_exit_stmt_reached_0: boolean,
  l22_l15_exit_stmt_reached_1: boolean,
  l22_l15_nullDerefBool_0: boolean,
  l22_l15_nullDerefBool_1: boolean,
  l22_l15_nullDerefBool_2: boolean,
  l22_l15_nullDerefBool_3: boolean,
  l22_l15_nullDerefBool_4: boolean,
  l22_l15_nullDerefBool_5: boolean,
  l22_l15_nullDerefBool_6: boolean,
  l22_l15_nullDerefBool_7: boolean,
  l22_l16_exit_stmt_reached_0: boolean,
  l22_l16_exit_stmt_reached_1: boolean,
  l22_l16_nullDerefBool_0: boolean,
  l22_l16_nullDerefBool_1: boolean,
  l22_l16_nullDerefBool_2: boolean,
  l22_l16_nullDerefBool_3: boolean,
  l22_l16_nullDerefBool_4: boolean,
  l22_l16_nullDerefBool_5: boolean,
  l22_l16_nullDerefBool_6: boolean,
  l22_l16_nullDerefBool_7: boolean,
  l22_l17_exit_stmt_reached_0: boolean,
  l22_l17_exit_stmt_reached_1: boolean,
  l22_l17_nullDerefBool_0: boolean,
  l22_l17_nullDerefBool_1: boolean,
  l22_l17_nullDerefBool_2: boolean,
  l22_l17_nullDerefBool_3: boolean,
  l22_l17_nullDerefBool_4: boolean,
  l22_l17_nullDerefBool_5: boolean,
  l22_l17_nullDerefBool_6: boolean,
  l22_l17_nullDerefBool_7: boolean,
  l22_l18_exit_stmt_reached_0: boolean,
  l22_l18_exit_stmt_reached_1: boolean,
  l22_l18_nullDerefBool_0: boolean,
  l22_l18_nullDerefBool_1: boolean,
  l22_l18_nullDerefBool_2: boolean,
  l22_l18_nullDerefBool_3: boolean,
  l22_l18_nullDerefBool_4: boolean,
  l22_l18_nullDerefBool_5: boolean,
  l22_l18_nullDerefBool_6: boolean,
  l22_l18_nullDerefBool_7: boolean,
  l22_l19_exit_stmt_reached_0: boolean,
  l22_l19_exit_stmt_reached_1: boolean,
  l22_l19_nullDerefBool_0: boolean,
  l22_l19_nullDerefBool_1: boolean,
  l22_l19_nullDerefBool_2: boolean,
  l22_l19_nullDerefBool_3: boolean,
  l22_l19_nullDerefBool_4: boolean,
  l22_l19_nullDerefBool_5: boolean,
  l22_l19_nullDerefBool_6: boolean,
  l22_l19_nullDerefBool_7: boolean,
  l22_l1_exit_stmt_reached_0: boolean,
  l22_l1_exit_stmt_reached_1: boolean,
  l22_l1_nullDerefBool_0: boolean,
  l22_l1_nullDerefBool_1: boolean,
  l22_l1_nullDerefBool_2: boolean,
  l22_l1_nullDerefBool_3: boolean,
  l22_l1_nullDerefBool_4: boolean,
  l22_l1_nullDerefBool_5: boolean,
  l22_l1_nullDerefBool_6: boolean,
  l22_l1_nullDerefBool_7: boolean,
  l22_l20_exit_stmt_reached_0: boolean,
  l22_l20_exit_stmt_reached_1: boolean,
  l22_l20_nullDerefBool_0: boolean,
  l22_l20_nullDerefBool_1: boolean,
  l22_l20_nullDerefBool_2: boolean,
  l22_l20_nullDerefBool_3: boolean,
  l22_l20_nullDerefBool_4: boolean,
  l22_l20_nullDerefBool_5: boolean,
  l22_l20_nullDerefBool_6: boolean,
  l22_l20_nullDerefBool_7: boolean,
  l22_l2_exit_stmt_reached_0: boolean,
  l22_l2_exit_stmt_reached_1: boolean,
  l22_l2_nullDerefBool_0: boolean,
  l22_l2_nullDerefBool_1: boolean,
  l22_l2_nullDerefBool_2: boolean,
  l22_l2_nullDerefBool_3: boolean,
  l22_l2_nullDerefBool_4: boolean,
  l22_l2_nullDerefBool_5: boolean,
  l22_l2_nullDerefBool_6: boolean,
  l22_l2_nullDerefBool_7: boolean,
  l22_l3_exit_stmt_reached_0: boolean,
  l22_l3_exit_stmt_reached_1: boolean,
  l22_l3_nullDerefBool_0: boolean,
  l22_l3_nullDerefBool_1: boolean,
  l22_l3_nullDerefBool_2: boolean,
  l22_l3_nullDerefBool_3: boolean,
  l22_l3_nullDerefBool_4: boolean,
  l22_l3_nullDerefBool_5: boolean,
  l22_l3_nullDerefBool_6: boolean,
  l22_l3_nullDerefBool_7: boolean,
  l22_l4_exit_stmt_reached_0: boolean,
  l22_l4_exit_stmt_reached_1: boolean,
  l22_l4_nullDerefBool_0: boolean,
  l22_l4_nullDerefBool_1: boolean,
  l22_l4_nullDerefBool_2: boolean,
  l22_l4_nullDerefBool_3: boolean,
  l22_l4_nullDerefBool_4: boolean,
  l22_l4_nullDerefBool_5: boolean,
  l22_l4_nullDerefBool_6: boolean,
  l22_l4_nullDerefBool_7: boolean,
  l22_l5_exit_stmt_reached_0: boolean,
  l22_l5_exit_stmt_reached_1: boolean,
  l22_l5_nullDerefBool_0: boolean,
  l22_l5_nullDerefBool_1: boolean,
  l22_l5_nullDerefBool_2: boolean,
  l22_l5_nullDerefBool_3: boolean,
  l22_l5_nullDerefBool_4: boolean,
  l22_l5_nullDerefBool_5: boolean,
  l22_l5_nullDerefBool_6: boolean,
  l22_l5_nullDerefBool_7: boolean,
  l22_l6_exit_stmt_reached_0: boolean,
  l22_l6_exit_stmt_reached_1: boolean,
  l22_l6_nullDerefBool_0: boolean,
  l22_l6_nullDerefBool_1: boolean,
  l22_l6_nullDerefBool_2: boolean,
  l22_l6_nullDerefBool_3: boolean,
  l22_l6_nullDerefBool_4: boolean,
  l22_l6_nullDerefBool_5: boolean,
  l22_l6_nullDerefBool_6: boolean,
  l22_l6_nullDerefBool_7: boolean,
  l22_l7_exit_stmt_reached_0: boolean,
  l22_l7_exit_stmt_reached_1: boolean,
  l22_l7_nullDerefBool_0: boolean,
  l22_l7_nullDerefBool_1: boolean,
  l22_l7_nullDerefBool_2: boolean,
  l22_l7_nullDerefBool_3: boolean,
  l22_l7_nullDerefBool_4: boolean,
  l22_l7_nullDerefBool_5: boolean,
  l22_l7_nullDerefBool_6: boolean,
  l22_l7_nullDerefBool_7: boolean,
  l22_l8_exit_stmt_reached_0: boolean,
  l22_l8_exit_stmt_reached_1: boolean,
  l22_l8_nullDerefBool_0: boolean,
  l22_l8_nullDerefBool_1: boolean,
  l22_l8_nullDerefBool_2: boolean,
  l22_l8_nullDerefBool_3: boolean,
  l22_l8_nullDerefBool_4: boolean,
  l22_l8_nullDerefBool_5: boolean,
  l22_l8_nullDerefBool_6: boolean,
  l22_l8_nullDerefBool_7: boolean,
  l22_l9_exit_stmt_reached_0: boolean,
  l22_l9_exit_stmt_reached_1: boolean,
  l22_l9_nullDerefBool_0: boolean,
  l22_l9_nullDerefBool_1: boolean,
  l22_l9_nullDerefBool_2: boolean,
  l22_l9_nullDerefBool_3: boolean,
  l22_l9_nullDerefBool_4: boolean,
  l22_l9_nullDerefBool_5: boolean,
  l22_l9_nullDerefBool_6: boolean,
  l22_l9_nullDerefBool_7: boolean,
  l22_nullDerefBool_1: boolean,
  l22_nullDerefBool_10: boolean,
  l22_nullDerefBool_11: boolean,
  l22_nullDerefBool_12: boolean,
  l22_nullDerefBool_13: boolean,
  l22_nullDerefBool_14: boolean,
  l22_nullDerefBool_15: boolean,
  l22_nullDerefBool_16: boolean,
  l22_nullDerefBool_17: boolean,
  l22_nullDerefBool_18: boolean,
  l22_nullDerefBool_19: boolean,
  l22_nullDerefBool_2: boolean,
  l22_nullDerefBool_20: boolean,
  l22_nullDerefBool_21: boolean,
  l22_nullDerefBool_22: boolean,
  l22_nullDerefBool_23: boolean,
  l22_nullDerefBool_24: boolean,
  l22_nullDerefBool_25: boolean,
  l22_nullDerefBool_26: boolean,
  l22_nullDerefBool_27: boolean,
  l22_nullDerefBool_28: boolean,
  l22_nullDerefBool_29: boolean,
  l22_nullDerefBool_3: boolean,
  l22_nullDerefBool_30: boolean,
  l22_nullDerefBool_31: boolean,
  l22_nullDerefBool_32: boolean,
  l22_nullDerefBool_33: boolean,
  l22_nullDerefBool_34: boolean,
  l22_nullDerefBool_4: boolean,
  l22_nullDerefBool_5: boolean,
  l22_nullDerefBool_6: boolean,
  l22_nullDerefBool_7: boolean,
  l22_nullDerefBool_8: boolean,
  l22_nullDerefBool_9: boolean,
  l22_var_1_current_0: examples_bstree_Node + null,
  l22_var_1_current_1: examples_bstree_Node + null,
  l22_var_1_current_10: examples_bstree_Node + null,
  l22_var_1_current_11: examples_bstree_Node + null,
  l22_var_1_current_2: examples_bstree_Node + null,
  l22_var_1_current_3: examples_bstree_Node + null,
  l22_var_1_current_4: examples_bstree_Node + null,
  l22_var_1_current_5: examples_bstree_Node + null,
  l22_var_1_current_6: examples_bstree_Node + null,
  l22_var_1_current_7: examples_bstree_Node + null,
  l22_var_1_current_8: examples_bstree_Node + null,
  l22_var_1_current_9: examples_bstree_Node + null,
  l22_var_2_ws_1_0: boolean,
  l22_var_2_ws_1_1: boolean,
  l22_var_2_ws_1_10: boolean,
  l22_var_2_ws_1_11: boolean,
  l22_var_2_ws_1_2: boolean,
  l22_var_2_ws_1_3: boolean,
  l22_var_2_ws_1_4: boolean,
  l22_var_2_ws_1_5: boolean,
  l22_var_2_ws_1_6: boolean,
  l22_var_2_ws_1_7: boolean,
  l22_var_2_ws_1_8: boolean,
  l22_var_2_ws_1_9: boolean,
  nodes_0: ( examples_bstree_BinTree ) -> ( examples_bstree_Node ),
  nodes_1: ( examples_bstree_BinTree ) -> ( examples_bstree_Node ),
  thiz_0: examples_bstree_BinTree,
  throw_0: java_lang_Throwable + null,
  throw_1: java_lang_Throwable + null,
  throw_10: java_lang_Throwable + null,
  throw_11: java_lang_Throwable + null,
  throw_12: java_lang_Throwable + null,
  throw_13: java_lang_Throwable + null,
  throw_14: java_lang_Throwable + null,
  throw_15: java_lang_Throwable + null,
  throw_16: java_lang_Throwable + null,
  throw_17: java_lang_Throwable + null,
  throw_18: java_lang_Throwable + null,
  throw_19: java_lang_Throwable + null,
  throw_2: java_lang_Throwable + null,
  throw_20: java_lang_Throwable + null,
  throw_21: java_lang_Throwable + null,
  throw_22: java_lang_Throwable + null,
  throw_23: java_lang_Throwable + null,
  throw_24: java_lang_Throwable + null,
  throw_3: java_lang_Throwable + null,
  throw_4: java_lang_Throwable + null,
  throw_5: java_lang_Throwable + null,
  throw_6: java_lang_Throwable + null,
  throw_7: java_lang_Throwable + null,
  throw_8: java_lang_Throwable + null,
  throw_9: java_lang_Throwable + null,
  usedObjects_0: set ( java_lang_Object ),
  usedObjects_1: set ( java_lang_Object ),
  usedObjects_10: set ( java_lang_Object ),
  usedObjects_11: set ( java_lang_Object ),
  usedObjects_2: set ( java_lang_Object ),
  usedObjects_3: set ( java_lang_Object ),
  usedObjects_4: set ( java_lang_Object ),
  usedObjects_5: set ( java_lang_Object ),
  usedObjects_6: set ( java_lang_Object ),
  usedObjects_7: set ( java_lang_Object ),
  usedObjects_8: set ( java_lang_Object ),
  usedObjects_9: set ( java_lang_Object ),
  x_0: Int
}


fact {
  precondition_examples_bstree_BinTree_add_0[QF.examples_bstree_BinTree_root_0,
                                            QF.examples_bstree_Node_key_0,
                                            (QF.fexamples_bstree_Node_left_0+QF.bexamples_bstree_Node_left_0),
                                            (QF.fexamples_bstree_Node_right_0+QF.bexamples_bstree_Node_right_0),
                                            QF.nodes_0,
                                            QF.thiz_0,
                                            QF.throw_0,
                                            QF.usedObjects_0]

}

fact {
  examples_bstree_BinTree_add_0[QF.thiz_0,
                               QF.throw_1,
                               QF.throw_2,
                               QF.throw_3,
                               QF.throw_4,
                               QF.throw_5,
                               QF.throw_6,
                               QF.throw_7,
                               QF.throw_8,
                               QF.throw_9,
                               QF.throw_10,
                               QF.throw_11,
                               QF.throw_12,
                               QF.throw_13,
                               QF.throw_14,
                               QF.throw_15,
                               QF.throw_16,
                               QF.throw_17,
                               QF.throw_18,
                               QF.throw_19,
                               QF.throw_20,
                               QF.throw_21,
                               QF.throw_22,
                               QF.throw_23,
                               QF.throw_24,
                               QF.x_0,
                               (QF.fexamples_bstree_Node_right_0+QF.bexamples_bstree_Node_right_0),
                               QF.examples_bstree_Node_right_1,
                               QF.examples_bstree_Node_right_2,
                               QF.examples_bstree_Node_right_3,
                               QF.examples_bstree_Node_right_4,
                               QF.examples_bstree_Node_right_5,
                               QF.examples_bstree_Node_right_6,
                               QF.examples_bstree_Node_right_7,
                               QF.examples_bstree_Node_right_8,
                               QF.examples_bstree_Node_right_9,
                               QF.examples_bstree_Node_right_10,
                               QF.examples_bstree_Node_right_11,
                               QF.examples_bstree_Node_right_12,
                               QF.examples_bstree_Node_right_13,
                               QF.examples_bstree_Node_right_14,
                               QF.examples_bstree_Node_right_15,
                               QF.examples_bstree_Node_right_16,
                               QF.examples_bstree_Node_right_17,
                               QF.examples_bstree_Node_right_18,
                               QF.examples_bstree_Node_right_19,
                               QF.examples_bstree_Node_right_20,
                               QF.examples_bstree_Node_right_21,
                               QF.examples_bstree_Node_right_22,
                               QF.examples_bstree_Node_right_23,
                               QF.examples_bstree_Node_right_24,
                               QF.examples_bstree_Node_right_25,
                               QF.examples_bstree_Node_right_26,
                               QF.examples_bstree_Node_right_27,
                               QF.examples_bstree_Node_right_28,
                               QF.examples_bstree_Node_right_29,
                               QF.examples_bstree_Node_right_30,
                               QF.examples_bstree_Node_right_31,
                               QF.examples_bstree_Node_right_32,
                               QF.examples_bstree_Node_key_0,
                               QF.examples_bstree_Node_key_1,
                               QF.examples_bstree_Node_key_2,
                               QF.examples_bstree_Node_key_3,
                               QF.examples_bstree_Node_key_4,
                               QF.examples_bstree_Node_key_5,
                               QF.examples_bstree_Node_key_6,
                               QF.examples_bstree_Node_key_7,
                               QF.examples_bstree_Node_key_8,
                               QF.examples_bstree_Node_key_9,
                               QF.examples_bstree_Node_key_10,
                               QF.examples_bstree_Node_key_11,
                               QF.examples_bstree_Node_key_12,
                               QF.examples_bstree_Node_key_13,
                               QF.examples_bstree_Node_key_14,
                               QF.examples_bstree_Node_key_15,
                               QF.examples_bstree_Node_key_16,
                               QF.examples_bstree_Node_key_17,
                               QF.examples_bstree_Node_key_18,
                               QF.examples_bstree_Node_key_19,
                               QF.examples_bstree_Node_key_20,
                               QF.examples_bstree_Node_key_21,
                               QF.examples_bstree_Node_key_22,
                               QF.examples_bstree_BinTree_root_0,
                               QF.examples_bstree_BinTree_root_1,
                               (QF.fexamples_bstree_Node_left_0+QF.bexamples_bstree_Node_left_0),
                               QF.examples_bstree_Node_left_1,
                               QF.examples_bstree_Node_left_2,
                               QF.examples_bstree_Node_left_3,
                               QF.examples_bstree_Node_left_4,
                               QF.examples_bstree_Node_left_5,
                               QF.examples_bstree_Node_left_6,
                               QF.examples_bstree_Node_left_7,
                               QF.examples_bstree_Node_left_8,
                               QF.examples_bstree_Node_left_9,
                               QF.examples_bstree_Node_left_10,
                               QF.examples_bstree_Node_left_11,
                               QF.examples_bstree_Node_left_12,
                               QF.examples_bstree_Node_left_13,
                               QF.examples_bstree_Node_left_14,
                               QF.examples_bstree_Node_left_15,
                               QF.examples_bstree_Node_left_16,
                               QF.examples_bstree_Node_left_17,
                               QF.examples_bstree_Node_left_18,
                               QF.examples_bstree_Node_left_19,
                               QF.examples_bstree_Node_left_20,
                               QF.examples_bstree_Node_left_21,
                               QF.examples_bstree_Node_left_22,
                               QF.examples_bstree_Node_left_23,
                               QF.examples_bstree_Node_left_24,
                               QF.examples_bstree_Node_left_25,
                               QF.examples_bstree_Node_left_26,
                               QF.examples_bstree_Node_left_27,
                               QF.examples_bstree_Node_left_28,
                               QF.examples_bstree_Node_left_29,
                               QF.examples_bstree_Node_left_30,
                               QF.examples_bstree_Node_left_31,
                               QF.examples_bstree_Node_left_32,
                               QF.usedObjects_0,
                               QF.usedObjects_1,
                               QF.usedObjects_2,
                               QF.usedObjects_3,
                               QF.usedObjects_4,
                               QF.usedObjects_5,
                               QF.usedObjects_6,
                               QF.usedObjects_7,
                               QF.usedObjects_8,
                               QF.usedObjects_9,
                               QF.usedObjects_10,
                               QF.usedObjects_11,
                               QF.l22_es_var__3_0,
                               QF.l22_es_var__3_1,
                               QF.l22_es_var__3_2,
                               QF.l22_es_var__3_3,
                               QF.l22_es_var__3_4,
                               QF.l22_es_var__3_5,
                               QF.l22_es_var__3_6,
                               QF.l22_es_var__3_7,
                               QF.l22_es_var__3_8,
                               QF.l22_es_var__3_9,
                               QF.l22_es_var__3_10,
                               QF.l22_exit_stmt_reached_1,
                               QF.l22_es_var__1_0,
                               QF.l22_es_var__1_1,
                               QF.l22_var_1_current_0,
                               QF.l22_var_1_current_1,
                               QF.l22_var_1_current_2,
                               QF.l22_var_1_current_3,
                               QF.l22_var_1_current_4,
                               QF.l22_var_1_current_5,
                               QF.l22_var_1_current_6,
                               QF.l22_var_1_current_7,
                               QF.l22_var_1_current_8,
                               QF.l22_var_1_current_9,
                               QF.l22_var_1_current_10,
                               QF.l22_var_1_current_11,
                               QF.l22_es_var__2_0,
                               QF.l22_es_var__2_1,
                               QF.l22_es_var__2_2,
                               QF.l22_es_var__2_3,
                               QF.l22_es_var__2_4,
                               QF.l22_es_var__2_5,
                               QF.l22_es_var__2_6,
                               QF.l22_es_var__2_7,
                               QF.l22_es_var__2_8,
                               QF.l22_es_var__2_9,
                               QF.l22_es_var__2_10,
                               QF.l22_nullDerefBool_1,
                               QF.l22_nullDerefBool_2,
                               QF.l22_nullDerefBool_3,
                               QF.l22_nullDerefBool_4,
                               QF.l22_nullDerefBool_5,
                               QF.l22_nullDerefBool_6,
                               QF.l22_nullDerefBool_7,
                               QF.l22_nullDerefBool_8,
                               QF.l22_nullDerefBool_9,
                               QF.l22_nullDerefBool_10,
                               QF.l22_nullDerefBool_11,
                               QF.l22_nullDerefBool_12,
                               QF.l22_nullDerefBool_13,
                               QF.l22_nullDerefBool_14,
                               QF.l22_nullDerefBool_15,
                               QF.l22_nullDerefBool_16,
                               QF.l22_nullDerefBool_17,
                               QF.l22_nullDerefBool_18,
                               QF.l22_nullDerefBool_19,
                               QF.l22_nullDerefBool_20,
                               QF.l22_nullDerefBool_21,
                               QF.l22_nullDerefBool_22,
                               QF.l22_nullDerefBool_23,
                               QF.l22_nullDerefBool_24,
                               QF.l22_nullDerefBool_25,
                               QF.l22_nullDerefBool_26,
                               QF.l22_nullDerefBool_27,
                               QF.l22_nullDerefBool_28,
                               QF.l22_nullDerefBool_29,
                               QF.l22_nullDerefBool_30,
                               QF.l22_nullDerefBool_31,
                               QF.l22_nullDerefBool_32,
                               QF.l22_nullDerefBool_33,
                               QF.l22_nullDerefBool_34,
                               QF.l22_var_2_ws_1_0,
                               QF.l22_var_2_ws_1_1,
                               QF.l22_var_2_ws_1_2,
                               QF.l22_var_2_ws_1_3,
                               QF.l22_var_2_ws_1_4,
                               QF.l22_var_2_ws_1_5,
                               QF.l22_var_2_ws_1_6,
                               QF.l22_var_2_ws_1_7,
                               QF.l22_var_2_ws_1_8,
                               QF.l22_var_2_ws_1_9,
                               QF.l22_var_2_ws_1_10,
                               QF.l22_var_2_ws_1_11,
                               QF.l22_l9_exit_stmt_reached_0,
                               QF.l22_l9_exit_stmt_reached_1,
                               QF.l22_l8_nullDerefBool_0,
                               QF.l22_l8_nullDerefBool_1,
                               QF.l22_l8_nullDerefBool_2,
                               QF.l22_l8_nullDerefBool_3,
                               QF.l22_l8_nullDerefBool_4,
                               QF.l22_l8_nullDerefBool_5,
                               QF.l22_l8_nullDerefBool_6,
                               QF.l22_l8_nullDerefBool_7,
                               QF.l22_l13_nullDerefBool_0,
                               QF.l22_l13_nullDerefBool_1,
                               QF.l22_l13_nullDerefBool_2,
                               QF.l22_l13_nullDerefBool_3,
                               QF.l22_l13_nullDerefBool_4,
                               QF.l22_l13_nullDerefBool_5,
                               QF.l22_l13_nullDerefBool_6,
                               QF.l22_l13_nullDerefBool_7,
                               QF.l22_l0_exit_stmt_reached_0,
                               QF.l22_l0_exit_stmt_reached_1,
                               QF.l22_l6_exit_stmt_reached_0,
                               QF.l22_l6_exit_stmt_reached_1,
                               QF.l22_l16_nullDerefBool_0,
                               QF.l22_l16_nullDerefBool_1,
                               QF.l22_l16_nullDerefBool_2,
                               QF.l22_l16_nullDerefBool_3,
                               QF.l22_l16_nullDerefBool_4,
                               QF.l22_l16_nullDerefBool_5,
                               QF.l22_l16_nullDerefBool_6,
                               QF.l22_l16_nullDerefBool_7,
                               QF.l22_l3_exit_stmt_reached_0,
                               QF.l22_l3_exit_stmt_reached_1,
                               QF.l22_l18_exit_stmt_reached_0,
                               QF.l22_l18_exit_stmt_reached_1,
                               QF.l22_l5_exit_stmt_reached_0,
                               QF.l22_l5_exit_stmt_reached_1,
                               QF.l22_l11_nullDerefBool_0,
                               QF.l22_l11_nullDerefBool_1,
                               QF.l22_l11_nullDerefBool_2,
                               QF.l22_l11_nullDerefBool_3,
                               QF.l22_l11_nullDerefBool_4,
                               QF.l22_l11_nullDerefBool_5,
                               QF.l22_l11_nullDerefBool_6,
                               QF.l22_l11_nullDerefBool_7,
                               QF.l22_l0_nullDerefBool_0,
                               QF.l22_l0_nullDerefBool_1,
                               QF.l22_l0_nullDerefBool_2,
                               QF.l22_l0_nullDerefBool_3,
                               QF.l22_l0_nullDerefBool_4,
                               QF.l22_l0_nullDerefBool_5,
                               QF.l22_l0_nullDerefBool_6,
                               QF.l22_l0_nullDerefBool_7,
                               QF.l22_l12_exit_stmt_reached_0,
                               QF.l22_l12_exit_stmt_reached_1,
                               QF.l22_l2_nullDerefBool_0,
                               QF.l22_l2_nullDerefBool_1,
                               QF.l22_l2_nullDerefBool_2,
                               QF.l22_l2_nullDerefBool_3,
                               QF.l22_l2_nullDerefBool_4,
                               QF.l22_l2_nullDerefBool_5,
                               QF.l22_l2_nullDerefBool_6,
                               QF.l22_l2_nullDerefBool_7,
                               QF.l22_l7_nullDerefBool_0,
                               QF.l22_l7_nullDerefBool_1,
                               QF.l22_l7_nullDerefBool_2,
                               QF.l22_l7_nullDerefBool_3,
                               QF.l22_l7_nullDerefBool_4,
                               QF.l22_l7_nullDerefBool_5,
                               QF.l22_l7_nullDerefBool_6,
                               QF.l22_l7_nullDerefBool_7,
                               QF.l22_l16_exit_stmt_reached_0,
                               QF.l22_l16_exit_stmt_reached_1,
                               QF.l22_l20_exit_stmt_reached_0,
                               QF.l22_l20_exit_stmt_reached_1,
                               QF.l22_l4_exit_stmt_reached_0,
                               QF.l22_l4_exit_stmt_reached_1,
                               QF.l22_l15_exit_stmt_reached_0,
                               QF.l22_l15_exit_stmt_reached_1,
                               QF.l22_l14_nullDerefBool_0,
                               QF.l22_l14_nullDerefBool_1,
                               QF.l22_l14_nullDerefBool_2,
                               QF.l22_l14_nullDerefBool_3,
                               QF.l22_l14_nullDerefBool_4,
                               QF.l22_l14_nullDerefBool_5,
                               QF.l22_l14_nullDerefBool_6,
                               QF.l22_l14_nullDerefBool_7,
                               QF.l22_l19_nullDerefBool_0,
                               QF.l22_l19_nullDerefBool_1,
                               QF.l22_l19_nullDerefBool_2,
                               QF.l22_l19_nullDerefBool_3,
                               QF.l22_l19_nullDerefBool_4,
                               QF.l22_l19_nullDerefBool_5,
                               QF.l22_l19_nullDerefBool_6,
                               QF.l22_l19_nullDerefBool_7,
                               QF.l22_l1_exit_stmt_reached_0,
                               QF.l22_l1_exit_stmt_reached_1,
                               QF.l22_l2_exit_stmt_reached_0,
                               QF.l22_l2_exit_stmt_reached_1,
                               QF.l22_l14_exit_stmt_reached_0,
                               QF.l22_l14_exit_stmt_reached_1,
                               QF.l22_l4_nullDerefBool_0,
                               QF.l22_l4_nullDerefBool_1,
                               QF.l22_l4_nullDerefBool_2,
                               QF.l22_l4_nullDerefBool_3,
                               QF.l22_l4_nullDerefBool_4,
                               QF.l22_l4_nullDerefBool_5,
                               QF.l22_l4_nullDerefBool_6,
                               QF.l22_l4_nullDerefBool_7,
                               QF.l22_l19_exit_stmt_reached_0,
                               QF.l22_l19_exit_stmt_reached_1,
                               QF.l22_l8_exit_stmt_reached_0,
                               QF.l22_l8_exit_stmt_reached_1,
                               QF.l22_l13_exit_stmt_reached_0,
                               QF.l22_l13_exit_stmt_reached_1,
                               QF.l22_l9_nullDerefBool_0,
                               QF.l22_l9_nullDerefBool_1,
                               QF.l22_l9_nullDerefBool_2,
                               QF.l22_l9_nullDerefBool_3,
                               QF.l22_l9_nullDerefBool_4,
                               QF.l22_l9_nullDerefBool_5,
                               QF.l22_l9_nullDerefBool_6,
                               QF.l22_l9_nullDerefBool_7,
                               QF.l22_l5_nullDerefBool_0,
                               QF.l22_l5_nullDerefBool_1,
                               QF.l22_l5_nullDerefBool_2,
                               QF.l22_l5_nullDerefBool_3,
                               QF.l22_l5_nullDerefBool_4,
                               QF.l22_l5_nullDerefBool_5,
                               QF.l22_l5_nullDerefBool_6,
                               QF.l22_l5_nullDerefBool_7,
                               QF.l22_l11_exit_stmt_reached_0,
                               QF.l22_l11_exit_stmt_reached_1,
                               QF.l22_l6_nullDerefBool_0,
                               QF.l22_l6_nullDerefBool_1,
                               QF.l22_l6_nullDerefBool_2,
                               QF.l22_l6_nullDerefBool_3,
                               QF.l22_l6_nullDerefBool_4,
                               QF.l22_l6_nullDerefBool_5,
                               QF.l22_l6_nullDerefBool_6,
                               QF.l22_l6_nullDerefBool_7,
                               QF.l22_l17_exit_stmt_reached_0,
                               QF.l22_l17_exit_stmt_reached_1,
                               QF.l22_l18_nullDerefBool_0,
                               QF.l22_l18_nullDerefBool_1,
                               QF.l22_l18_nullDerefBool_2,
                               QF.l22_l18_nullDerefBool_3,
                               QF.l22_l18_nullDerefBool_4,
                               QF.l22_l18_nullDerefBool_5,
                               QF.l22_l18_nullDerefBool_6,
                               QF.l22_l18_nullDerefBool_7,
                               QF.l22_l3_nullDerefBool_0,
                               QF.l22_l3_nullDerefBool_1,
                               QF.l22_l3_nullDerefBool_2,
                               QF.l22_l3_nullDerefBool_3,
                               QF.l22_l3_nullDerefBool_4,
                               QF.l22_l3_nullDerefBool_5,
                               QF.l22_l3_nullDerefBool_6,
                               QF.l22_l3_nullDerefBool_7,
                               QF.l22_l20_nullDerefBool_0,
                               QF.l22_l20_nullDerefBool_1,
                               QF.l22_l20_nullDerefBool_2,
                               QF.l22_l20_nullDerefBool_3,
                               QF.l22_l20_nullDerefBool_4,
                               QF.l22_l20_nullDerefBool_5,
                               QF.l22_l20_nullDerefBool_6,
                               QF.l22_l20_nullDerefBool_7,
                               QF.l22_l15_nullDerefBool_0,
                               QF.l22_l15_nullDerefBool_1,
                               QF.l22_l15_nullDerefBool_2,
                               QF.l22_l15_nullDerefBool_3,
                               QF.l22_l15_nullDerefBool_4,
                               QF.l22_l15_nullDerefBool_5,
                               QF.l22_l15_nullDerefBool_6,
                               QF.l22_l15_nullDerefBool_7,
                               QF.l22_l1_nullDerefBool_0,
                               QF.l22_l1_nullDerefBool_1,
                               QF.l22_l1_nullDerefBool_2,
                               QF.l22_l1_nullDerefBool_3,
                               QF.l22_l1_nullDerefBool_4,
                               QF.l22_l1_nullDerefBool_5,
                               QF.l22_l1_nullDerefBool_6,
                               QF.l22_l1_nullDerefBool_7,
                               QF.l22_l12_nullDerefBool_0,
                               QF.l22_l12_nullDerefBool_1,
                               QF.l22_l12_nullDerefBool_2,
                               QF.l22_l12_nullDerefBool_3,
                               QF.l22_l12_nullDerefBool_4,
                               QF.l22_l12_nullDerefBool_5,
                               QF.l22_l12_nullDerefBool_6,
                               QF.l22_l12_nullDerefBool_7,
                               QF.l22_l7_exit_stmt_reached_0,
                               QF.l22_l7_exit_stmt_reached_1,
                               QF.l22_l17_nullDerefBool_0,
                               QF.l22_l17_nullDerefBool_1,
                               QF.l22_l17_nullDerefBool_2,
                               QF.l22_l17_nullDerefBool_3,
                               QF.l22_l17_nullDerefBool_4,
                               QF.l22_l17_nullDerefBool_5,
                               QF.l22_l17_nullDerefBool_6,
                               QF.l22_l17_nullDerefBool_7,
                               QF.l22_l10_exit_stmt_reached_0,
                               QF.l22_l10_exit_stmt_reached_1,
                               QF.l22_l10_nullDerefBool_0,
                               QF.l22_l10_nullDerefBool_1,
                               QF.l22_l10_nullDerefBool_2,
                               QF.l22_l10_nullDerefBool_3,
                               QF.l22_l10_nullDerefBool_4,
                               QF.l22_l10_nullDerefBool_5,
                               QF.l22_l10_nullDerefBool_6,
                               QF.l22_l10_nullDerefBool_7]

}

fact {
  havocVariable2[QF.nodes_1]
}

fact {
  examples_bstree_BinTreeCondition18[QF.examples_bstree_BinTree_root_1,
                                    QF.examples_bstree_Node_left_32,
                                    QF.examples_bstree_Node_right_32,
                                    QF.nodes_1,
                                    QF.thiz_0]

}

assert BSTree_m3{
  postcondition_examples_bstree_BinTree_add_0[QF.examples_bstree_BinTree_root_1,
                                             QF.examples_bstree_Node_key_22,
                                             QF.examples_bstree_Node_left_32,
                                             QF.examples_bstree_Node_right_32,
                                             QF.nodes_0,
                                             QF.nodes_1,
                                             QF.thiz_0,
                                             QF.thiz_0,
                                             QF.throw_24,
                                             QF.x_0]
}
check BSTree_m3 for 0 but 
                 exactly 1 examples_bstree_BinTree, 
                 exactly 20 examples_bstree_Node,
                 6 int  



one sig N0,N1,N2,N3,N4,N5,N6,N7,N8,N9,N10,N11,N12,N13,N14,N15,N16,N17,N18,N19 extends examples_bstree_Node {}
fun node_next[]: (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19) -> lone (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19)  
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
  + 
  N16->N17 
  + 
  N17->N18 
  + 
  N18->N19 
} 
fun node_prevs[e: N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19] :set (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19) 
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
   + 
   N17 -> ( N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16 ) 
   + 
   N18 -> ( N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17 ) 
   + 
   N19 -> ( N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18 ) 
 ) 
} 















































































































fun node_relprevs[] :( N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19 ) -> set ( N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19 ) 
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
   + 
   N17 -> ( N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17 ) 
   + 
   N18 -> ( N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18 ) 
   + 
   N19 -> ( N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19 ) 
} 
fun node_min [es: set ( N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19 )] : lone ( N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19 ) 
{ 
  es - es.( 
   N0 -> ( N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19 ) 
   + 
   N1 -> ( N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19 ) 
   + 
   N2 -> ( N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19 ) 
   + 
   N3 -> ( N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19 ) 
   + 
   N4 -> ( N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19 ) 
   + 
   N5 -> ( N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19 ) 
   + 
   N6 -> ( N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19 ) 
   + 
   N7 -> ( N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19 ) 
   + 
   N8 -> ( N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19 ) 
   + 
   N9 -> ( N10+N11+N12+N13+N14+N15+N16+N17+N18+N19 ) 
   + 
   N10 -> ( N11+N12+N13+N14+N15+N16+N17+N18+N19 ) 
   + 
   N11 -> ( N12+N13+N14+N15+N16+N17+N18+N19 ) 
   + 
   N12 -> ( N13+N14+N15+N16+N17+N18+N19 ) 
   + 
   N13 -> ( N14+N15+N16+N17+N18+N19 ) 
   + 
   N14 -> ( N15+N16+N17+N18+N19 ) 
   + 
   N15 -> ( N16+N17+N18+N19 ) 
   + 
   N16 -> ( N17+N18+N19 ) 
   + 
   N17 -> ( N18+N19 ) 
   + 
   N18 -> ( N19 ) 
  ) 
} 
fact { 
let entry=(QF.thiz_0).(QF.examples_bstree_BinTree_root_0),ff1=QF.fexamples_bstree_Node_left_0,ff2=QF.fexamples_bstree_Node_right_0,bf1=QF.bexamples_bstree_Node_left_0,bf2=QF.bexamples_bstree_Node_right_0 | { 
   -- forwardPlusBackwardAreFunctions 
   no ((ff1.univ) & (bf1.univ)) 
   no ((ff2.univ) & (bf2.univ)) 
   N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19 = ff1.univ + bf1.univ   
   N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19 = ff2.univ + bf2.univ   

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
+N8->N17 
+N8->N18 
+N8->null 
+N9->N10 
+N9->N11 
+N9->N12 
+N9->N13 
+N9->N14 
+N9->N15 
+N9->N16 
+N9->N17 
+N9->N18 
+N9->N19 
+N9->null 
+N10->N11 
+N10->N12 
+N10->N13 
+N10->N14 
+N10->N15 
+N10->N16 
+N10->N17 
+N10->N18 
+N10->N19 
+N10->null 
+N11->N12 
+N11->N13 
+N11->N14 
+N11->N15 
+N11->N16 
+N11->N17 
+N11->N18 
+N11->N19 
+N11->null 
+N12->N13 
+N12->N14 
+N12->N15 
+N12->N16 
+N12->N17 
+N12->N18 
+N12->N19 
+N12->null 
+N13->N14 
+N13->N15 
+N13->N16 
+N13->N17 
+N13->N18 
+N13->N19 
+N13->null 
+N14->N15 
+N14->N16 
+N14->N17 
+N14->N18 
+N14->N19 
+N14->null 
+N15->N16 
+N15->N17 
+N15->N18 
+N15->N19 
+N15->null 
+N16->N17 
+N16->N18 
+N16->N19 
+N16->null 
+N17->N18 
+N17->N19 
+N17->null 
+N18->N19 
+N18->null 
+N19->null 
 
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
+N8->N17 
+N8->null 
+N9->N10 
+N9->N11 
+N9->N12 
+N9->N13 
+N9->N14 
+N9->N15 
+N9->N16 
+N9->N17 
+N9->N18 
+N9->N19 
+N9->null 
+N10->N11 
+N10->N12 
+N10->N13 
+N10->N14 
+N10->N15 
+N10->N16 
+N10->N17 
+N10->N18 
+N10->N19 
+N10->null 
+N11->N12 
+N11->N13 
+N11->N14 
+N11->N15 
+N11->N16 
+N11->N17 
+N11->N18 
+N11->N19 
+N11->null 
+N12->N13 
+N12->N14 
+N12->N15 
+N12->N16 
+N12->N17 
+N12->N18 
+N12->N19 
+N12->null 
+N13->N14 
+N13->N15 
+N13->N16 
+N13->N17 
+N13->N18 
+N13->N19 
+N13->null 
+N14->N15 
+N14->N16 
+N14->N17 
+N14->N18 
+N14->N19 
+N14->null 
+N15->N16 
+N15->N17 
+N15->N18 
+N15->N19 
+N15->null 
+N16->N17 
+N16->N18 
+N16->N19 
+N16->null 
+N17->N18 
+N17->N19 
+N17->null 
+N18->N19 
+N18->null 
+N19->null 
 
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
+N0->17 
+N0->18 
+N0->19 
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
+N1->17 
+N1->18 
+N1->19 
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
+N2->17 
+N2->18 
+N2->19 
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
+N3->17 
+N3->18 
+N3->19 
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
+N4->17 
+N4->18 
+N4->19 
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
+N5->17 
+N5->18 
+N5->19 
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
+N6->17 
+N6->18 
+N6->19 
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
+N7->17 
+N7->18 
+N7->19 
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
+N8->17 
+N8->18 
+N8->19 
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
+N9->17 
+N9->18 
+N9->19 
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
+N10->17 
+N10->18 
+N10->19 
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
+N11->17 
+N11->18 
+N11->19 
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
+N12->17 
+N12->18 
+N12->19 
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
+N13->17 
+N13->18 
+N13->19 
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
+N14->17 
+N14->18 
+N14->19 
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
+N15->17 
+N15->18 
+N15->19 
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
+N16->17 
+N16->18 
+N16->19 
+N17->0 
+N17->1 
+N17->2 
+N17->3 
+N17->4 
+N17->5 
+N17->6 
+N17->7 
+N17->8 
+N17->9 
+N17->10 
+N17->11 
+N17->12 
+N17->13 
+N17->14 
+N17->15 
+N17->16 
+N17->17 
+N17->18 
+N17->19 
+N18->0 
+N18->1 
+N18->2 
+N18->3 
+N18->4 
+N18->5 
+N18->6 
+N18->7 
+N18->8 
+N18->9 
+N18->10 
+N18->11 
+N18->12 
+N18->13 
+N18->14 
+N18->15 
+N18->16 
+N18->17 
+N18->18 
+N18->19 
+N19->0 
+N19->1 
+N19->2 
+N19->3 
+N19->4 
+N19->5 
+N19->6 
+N19->7 
+N19->8 
+N19->9 
+N19->10 
+N19->11 
+N19->12 
+N19->13 
+N19->14 
+N19->15 
+N19->16 
+N19->17 
+N19->18 
+N19->19 

} 
//fact root_int_fields 
fact { 
} 
//fact root_node_fields 
fact { 
} 



