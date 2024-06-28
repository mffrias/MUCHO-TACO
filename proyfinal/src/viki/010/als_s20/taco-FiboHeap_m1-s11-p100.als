/* 
 * DynAlloy translator options 
 * --------------------------- 
 * applySimplifications= true
 * assertionId= FiboHeap_m1
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
//-------------- examples_fiboheap_FibHeap--------------//
sig examples_fiboheap_FibHeap extends java_lang_Object {}
{}




pred examples_fiboheap_FibHeapCondition0[
  thiz:univ
]{
   isEmptyOrNull[thiz]

}

pred examples_fiboheap_FibHeap_ensures[
  examples_fiboheap_Node_cost':univ->univ,
  nodes':univ->univ,
  return':univ,
  thiz:univ,
  throw':univ
]{
(
   some thiz.nodes' => 
(
   isSubset[return',
           thiz.nodes']
   and 
   (
     no node:examples_fiboheap_Node | {
       isSubset[node,
               thiz.nodes']
       and 
       lt[node.examples_fiboheap_Node_cost',
         return'.examples_fiboheap_Node_cost']
     
     }
   )
)
)
   and
(
   no thiz.nodes' =>
(
   return'=null
)
)
   and 
   equ[throw',
      null]

}

pred examples_fiboheap_FibHeapCondition1[
  thiz:univ
]{
   not (
     isEmptyOrNull[thiz])

}

pred examples_fiboheap_FibHeap_object_invariant[
  examples_fiboheap_FibHeap_min:univ->univ,
  examples_fiboheap_FibHeap_n:univ->univ,
  examples_fiboheap_Node_child:univ->univ,
  examples_fiboheap_Node_cost:univ->univ,
  examples_fiboheap_Node_degree:univ->univ,
  examples_fiboheap_Node_left:univ->univ,
  examples_fiboheap_Node_parent:univ->univ,
  examples_fiboheap_Node_right:univ->univ,
  thiz:univ
]{
   (
     all node:examples_fiboheap_Node | {
       isSubset[node,
               (thiz.examples_fiboheap_FibHeap_min).(fun_reflexive_closure[examples_fiboheap_Node_child+examples_fiboheap_Node_right])]
       implies 
               (
                 isNotSubset[node,
                            ((fun_set_difference[node.(fun_reflexive_closure[examples_fiboheap_Node_right]),node]).examples_fiboheap_Node_child).(fun_reflexive_closure[examples_fiboheap_Node_child+examples_fiboheap_Node_right])]
                 and 
                 (
                   isSubset[node,
                           (thiz.examples_fiboheap_FibHeap_min).(fun_reflexive_closure[examples_fiboheap_Node_right])]
                   implies 
                           (
                             equ[node.examples_fiboheap_Node_parent,
                                null]
                             and 
                             lte[(thiz.examples_fiboheap_FibHeap_min).examples_fiboheap_Node_cost,
                                node.examples_fiboheap_Node_cost]
                           )
                 )
                 and 
                 neq[node.examples_fiboheap_Node_right,
                    null]
                 and 
                 equ[(node.examples_fiboheap_Node_right).examples_fiboheap_Node_left,
                    node]
                 and 
                 equ[node.examples_fiboheap_Node_degree,
                    #(fun_set_difference[(node.examples_fiboheap_Node_child).(fun_reflexive_closure[examples_fiboheap_Node_right]),null])]
                 and 
                 (
                   all m:examples_fiboheap_Node | {
                     isSubset[m,
                             (node.examples_fiboheap_Node_child).(fun_reflexive_closure[examples_fiboheap_Node_child+examples_fiboheap_Node_right])]
                     implies 
                             lte[node.examples_fiboheap_Node_cost,
                                m.examples_fiboheap_Node_cost]
                   
                   }
                 )
                 and 
                 (
                   neq[node.examples_fiboheap_Node_child,
                      null]
                   implies 
                           equ[(node.(examples_fiboheap_Node_child.(fun_reflexive_closure[examples_fiboheap_Node_right]))).examples_fiboheap_Node_parent,
                              node]
                 )
               )
     
     }
   )
   and 
   equ[thiz.examples_fiboheap_FibHeap_n,
      #(fun_set_difference[(thiz.examples_fiboheap_FibHeap_min).(fun_reflexive_closure[examples_fiboheap_Node_child+examples_fiboheap_Node_right]),null])]

}

pred postcondition_examples_fiboheap_FibHeap_minimum_0[
  examples_fiboheap_Node_cost':univ->univ,
  nodes':univ->univ,
  return':univ,
  thiz:univ,
  throw':univ
]{
   examples_fiboheap_FibHeap_ensures[examples_fiboheap_Node_cost',
                                    nodes',
                                    return',
                                    thiz,
                                    throw']

}

pred examples_fiboheap_FibHeapCondition5[
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

pred examples_fiboheap_FibHeapCondition4[
  nullDerefBool:univ,
  throw:univ
]{
   equ[nullDerefBool,
      true]
   and 
   equ[throw,
      null]

}

pred precondition_examples_fiboheap_FibHeap_minimum_0[
  examples_fiboheap_FibHeap_min:univ->univ,
  examples_fiboheap_FibHeap_n:univ->univ,
  examples_fiboheap_Node_child:univ->univ,
  examples_fiboheap_Node_cost:univ->univ,
  examples_fiboheap_Node_degree:univ->univ,
  examples_fiboheap_Node_left:univ->univ,
  examples_fiboheap_Node_parent:univ->univ,
  examples_fiboheap_Node_right:univ->univ,
  nodes:univ->univ,
  thiz:univ,
  throw:univ
]{
   equ[throw,
      null]
   and 
   examples_fiboheap_FibHeap_object_invariant[examples_fiboheap_FibHeap_min,
                                             examples_fiboheap_FibHeap_n,
                                             examples_fiboheap_Node_child,
                                             examples_fiboheap_Node_cost,
                                             examples_fiboheap_Node_degree,
                                             examples_fiboheap_Node_left,
                                             examples_fiboheap_Node_parent,
                                             examples_fiboheap_Node_right,
                                             thiz]
   and 
   examples_fiboheap_FibHeap_nodes_abstraction[examples_fiboheap_FibHeap_min,
                                              examples_fiboheap_Node_child,
                                              examples_fiboheap_Node_left,
                                              examples_fiboheap_Node_parent,
                                              examples_fiboheap_Node_right,
                                              nodes,
                                              thiz]

}

pred examples_fiboheap_FibHeapCondition3[
  exit_stmt_reached:univ
]{
   not (
     exit_stmt_reached=false)

}

pred examples_fiboheap_FibHeap_nodes_abstraction[
  examples_fiboheap_FibHeap_min:univ->univ,
  examples_fiboheap_Node_child:univ->univ,
  examples_fiboheap_Node_left:univ->univ,
  examples_fiboheap_Node_parent:univ->univ,
  examples_fiboheap_Node_right:univ->univ,
  nodes:univ->univ,
  thiz:univ
]{
   equ[thiz.nodes,
      fun_set_difference[(thiz.examples_fiboheap_FibHeap_min).(fun_reflexive_closure[examples_fiboheap_Node_left+examples_fiboheap_Node_right+examples_fiboheap_Node_parent+examples_fiboheap_Node_child]),null]]

}

pred examples_fiboheap_FibHeapCondition2[
  exit_stmt_reached:univ
]{
   exit_stmt_reached=false

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




//-------------- java_lang_Object--------------//
abstract sig java_lang_Object {}
{}




//-------------- java_lang_NullPointerException--------------//
abstract one sig java_lang_NullPointerException extends java_lang_RuntimeException {}
{}



one
sig java_lang_NullPointerExceptionLit extends java_lang_NullPointerException {}
{}

//-------------- examples_fiboheap_Node--------------//
sig examples_fiboheap_Node extends java_lang_Object {}
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


pred examples_fiboheap_FibHeap_minimum_0[
  thiz_0: examples_fiboheap_FibHeap,
  throw_1: java_lang_Throwable + null,
  throw_2: java_lang_Throwable + null,
  return_0: examples_fiboheap_Node + null,
  return_1: examples_fiboheap_Node + null,
  examples_fiboheap_FibHeap_min_0: ( examples_fiboheap_FibHeap ) -> one ( examples_fiboheap_Node + null ),
  exit_stmt_reached_1: boolean,
  exit_stmt_reached_2: boolean,
  nullDerefBool_1: boolean,
  nullDerefBool_2: boolean
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
      examples_fiboheap_FibHeapCondition2[exit_stmt_reached_1]
      and 
      (
        (
          examples_fiboheap_FibHeapCondition0[thiz_0]
          and 
          (
            nullDerefBool_2=true)
        )
        or 
        (
          (
            not (
              examples_fiboheap_FibHeapCondition0[thiz_0])
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
        return_1=thiz_0.examples_fiboheap_FibHeap_min_0)
      and 
      (
        exit_stmt_reached_2=true)
    )
    or 
    (
      (
        not (
          examples_fiboheap_FibHeapCondition2[exit_stmt_reached_1])
      )
      and 
      TruePred[]
      and 
      (
        return_0=return_1)
      and 
      (
        nullDerefBool_1=nullDerefBool_2)
      and 
      (
        exit_stmt_reached_1=exit_stmt_reached_2)
    )
  )
  and 
  (
    (
      examples_fiboheap_FibHeapCondition4[nullDerefBool_2,
                                         throw_1]
      and 
      (
        throw_2=java_lang_NullPointerExceptionLit)
    )
    or 
    (
      (
        not (
          examples_fiboheap_FibHeapCondition4[nullDerefBool_2,
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



pred simulate_examples_fiboheap_FibHeap_minimum_0[
  thiz_0: examples_fiboheap_FibHeap,
  examples_fiboheap_Node_left_0: ( examples_fiboheap_Node ) -> one ( examples_fiboheap_Node + null ),
  examples_fiboheap_Node_cost_0: ( examples_fiboheap_Node ) -> one ( Int ),
  examples_fiboheap_FibHeap_n_0: ( examples_fiboheap_FibHeap ) -> one ( Int ),
  throw_0: java_lang_Throwable + null,
  throw_1: java_lang_Throwable + null,
  throw_2: java_lang_Throwable + null,
  examples_fiboheap_Node_degree_0: ( examples_fiboheap_Node ) -> one ( Int ),
  examples_fiboheap_Node_right_0: ( examples_fiboheap_Node ) -> one ( examples_fiboheap_Node + null ),
  return_0: examples_fiboheap_Node + null,
  return_1: examples_fiboheap_Node + null,
  examples_fiboheap_Node_parent_0: ( examples_fiboheap_Node ) -> one ( examples_fiboheap_Node + null ),
  nodes_0: ( examples_fiboheap_FibHeap ) -> ( examples_fiboheap_Node ),
  examples_fiboheap_FibHeap_min_0: ( examples_fiboheap_FibHeap ) -> one ( examples_fiboheap_Node + null ),
  examples_fiboheap_Node_child_0: ( examples_fiboheap_Node ) -> one ( examples_fiboheap_Node + null ),
  l0_exit_stmt_reached_1: boolean,
  l0_exit_stmt_reached_2: boolean,
  l0_nullDerefBool_1: boolean,
  l0_nullDerefBool_2: boolean
]{
  precondition_examples_fiboheap_FibHeap_minimum_0[examples_fiboheap_FibHeap_min_0,
                                                  examples_fiboheap_FibHeap_n_0,
                                                  examples_fiboheap_Node_child_0,
                                                  examples_fiboheap_Node_cost_0,
                                                  examples_fiboheap_Node_degree_0,
                                                  examples_fiboheap_Node_left_0,
                                                  examples_fiboheap_Node_parent_0,
                                                  examples_fiboheap_Node_right_0,
                                                  nodes_0,
                                                  thiz_0,
                                                  throw_0]
  and 
  examples_fiboheap_FibHeap_minimum_0[thiz_0,
                                     throw_1,
                                     throw_2,
                                     return_0,
                                     return_1,
                                     examples_fiboheap_FibHeap_min_0,
                                     l0_exit_stmt_reached_1,
                                     l0_exit_stmt_reached_2,
                                     l0_nullDerefBool_1,
                                     l0_nullDerefBool_2]
  and 
  postcondition_examples_fiboheap_FibHeap_minimum_0[examples_fiboheap_Node_cost_0,
                                                   nodes_0,
                                                   return_1,
                                                   thiz_0,
                                                   throw_2]

}

one sig QF {
  examples_fiboheap_FibHeap_min_0: ( examples_fiboheap_FibHeap ) -> one ( examples_fiboheap_Node + null ),
  examples_fiboheap_FibHeap_n_0: ( examples_fiboheap_FibHeap ) -> one ( Int ),
  bexamples_fiboheap_Node_child_0,fexamples_fiboheap_Node_child_0: ( examples_fiboheap_Node ) -> lone ( examples_fiboheap_Node + null ),
  examples_fiboheap_Node_cost_0: ( examples_fiboheap_Node ) -> one ( Int ),
  examples_fiboheap_Node_degree_0: ( examples_fiboheap_Node ) -> one ( Int ),
  bexamples_fiboheap_Node_left_0,fexamples_fiboheap_Node_left_0: ( examples_fiboheap_Node ) -> lone ( examples_fiboheap_Node + null ),
  bexamples_fiboheap_Node_parent_0,fexamples_fiboheap_Node_parent_0: ( examples_fiboheap_Node ) -> lone ( examples_fiboheap_Node + null ),
  bexamples_fiboheap_Node_right_0,fexamples_fiboheap_Node_right_0: ( examples_fiboheap_Node ) -> lone ( examples_fiboheap_Node + null ),
  l1_exit_stmt_reached_1: boolean,
  l1_exit_stmt_reached_2: boolean,
  l1_nullDerefBool_1: boolean,
  l1_nullDerefBool_2: boolean,
  nodes_0: ( examples_fiboheap_FibHeap ) -> ( examples_fiboheap_Node ),
  return_0: examples_fiboheap_Node + null,
  return_1: examples_fiboheap_Node + null,
  thiz_0: examples_fiboheap_FibHeap,
  throw_0: java_lang_Throwable + null,
  throw_1: java_lang_Throwable + null,
  throw_2: java_lang_Throwable + null
}


fact {
  precondition_examples_fiboheap_FibHeap_minimum_0[QF.examples_fiboheap_FibHeap_min_0,
                                                  QF.examples_fiboheap_FibHeap_n_0,
                                                  (QF.fexamples_fiboheap_Node_child_0+QF.bexamples_fiboheap_Node_child_0),
                                                  QF.examples_fiboheap_Node_cost_0,
                                                  QF.examples_fiboheap_Node_degree_0,
                                                  (QF.fexamples_fiboheap_Node_left_0+QF.bexamples_fiboheap_Node_left_0),
                                                  (QF.fexamples_fiboheap_Node_parent_0+QF.bexamples_fiboheap_Node_parent_0),
                                                  (QF.fexamples_fiboheap_Node_right_0+QF.bexamples_fiboheap_Node_right_0),
                                                  QF.nodes_0,
                                                  QF.thiz_0,
                                                  QF.throw_0]

}

fact {
  examples_fiboheap_FibHeap_minimum_0[QF.thiz_0,
                                     QF.throw_1,
                                     QF.throw_2,
                                     QF.return_0,
                                     QF.return_1,
                                     QF.examples_fiboheap_FibHeap_min_0,
                                     QF.l1_exit_stmt_reached_1,
                                     QF.l1_exit_stmt_reached_2,
                                     QF.l1_nullDerefBool_1,
                                     QF.l1_nullDerefBool_2]

}

assert FiboHeap_m1{
  postcondition_examples_fiboheap_FibHeap_minimum_0[QF.examples_fiboheap_Node_cost_0,
                                                   QF.nodes_0,
                                                   QF.return_1,
                                                   QF.thiz_0,
                                                   QF.throw_2]
}
check FiboHeap_m1 for 0 but 
                 exactly 1 examples_fiboheap_FibHeap, 
                 exactly 11 examples_fiboheap_Node,
                 5 int  



one sig N0,N1,N2,N3,N4,N5,N6,N7,N8,N9,N10 extends examples_fiboheap_Node {}

fun globalMin[s : set (examples_fiboheap_Node + examples_fiboheap_FibHeap)] : lone (examples_fiboheap_Node + examples_fiboheap_FibHeap) {
	s - s.^(examples_fiboheap_FibHeap->N0 + node_next[])
}

fun minP[n : examples_fiboheap_Node] : examples_fiboheap_Node {
	globalMin[(QF.fexamples_fiboheap_Node_left_0 + QF.fexamples_fiboheap_Node_right_0 + QF.fexamples_fiboheap_Node_child_0 + QF.fexamples_fiboheap_Node_parent_0 + QF.examples_fiboheap_FibHeap_min_0).n ]
}

fun FReach[] : set univ {
  (QF.thiz_0).(QF.examples_fiboheap_FibHeap_min_0).*(QF.fexamples_fiboheap_Node_child_0 + QF.fexamples_fiboheap_Node_right_0 + QF.fexamples_fiboheap_Node_left_0) - null
}

fact { 
  let 	
    thiz    = QF.thiz_0,
    size    = QF.examples_fiboheap_FibHeap_n_0, 
    minNode = QF.examples_fiboheap_FibHeap_min_0,
    degree  = QF.examples_fiboheap_Node_degree_0, 
    fleft   = QF.fexamples_fiboheap_Node_left_0,
    bleft   = QF.bexamples_fiboheap_Node_left_0,
    fright  = QF.fexamples_fiboheap_Node_right_0,
    bright  = QF.bexamples_fiboheap_Node_right_0,
    fchild  = QF.fexamples_fiboheap_Node_child_0,
    bchild  = QF.bexamples_fiboheap_Node_child_0,
    fparent = QF.fexamples_fiboheap_Node_parent_0,
    bparent = QF.bexamples_fiboheap_Node_parent_0,
    key	    = QF.examples_fiboheap_Node_cost_0 | 

 no ((fleft.univ) & (bleft.univ)) and     
 examples_fiboheap_Node = fleft.univ + bleft.univ and  

 no ((fright.univ) & (bright.univ)) and   
 examples_fiboheap_Node = fright.univ + bright.univ and

 no ((fchild.univ) & (bchild.univ)) and   
 examples_fiboheap_Node = fchild.univ + bchild.univ and

 no ((fparent.univ) & (bparent.univ)) and   
 examples_fiboheap_Node = fparent.univ + bparent.univ
			
}

fact orderFibHeapNodeCondition_c{
( all disj o1, o2, o3 : examples_fiboheap_Node |
  let a = minP[o1] | let b = minP[o2] | let c = minP[o3] |
  ( o1+o2+o3 in FReach[] and
    some a and some b and some c and a = b and b=c and a in examples_fiboheap_Node and
    o1 = a.(QF.fexamples_fiboheap_Node_left_0) and
    o2 = a.(QF.fexamples_fiboheap_Node_child_0) and
    o3 = a.(QF.fexamples_fiboheap_Node_right_0)
  ) implies  (o2 = o1.node_next[] and o3 = o2.node_next[])
)
&&
( all disj o1, o2 : examples_fiboheap_Node |
  let a = minP[o1] | let b = minP[o2] |
	( 	o1+o2 in FReach[] 
		and	some a and some b and a = b and a in examples_fiboheap_Node
		and (no o3 : examples_fiboheap_Node | o3 != o1 and o3 != o2 and minP[o3] = a) 
		and	o1 = a.(QF.fexamples_fiboheap_Node_left_0)
	) implies o2 = o1.node_next[]
)
&&
( all disj o1, o2 : examples_fiboheap_Node |
  let a = minP[o1] | let b = minP[o2] |
	( 	o1+o2 in FReach[] 
		and	some a and some b and a = b and a in examples_fiboheap_Node
		and (no o3 : examples_fiboheap_Node | o3 != o1 and o3 != o2 and minP[o3] = a) 
		and o1 != a.(QF.fexamples_fiboheap_Node_left_0) and o2 != a.(QF.fexamples_fiboheap_Node_left_0) and o1 = a.(QF.fexamples_fiboheap_Node_child_0)
	) implies o2 = o1.node_next[]
)
}

fact orderFibHeapNodeCondition_d { 
  all disj o1, o2 : examples_fiboheap_Node | 
    let a = minP[o1] | let b = minP[o2] | 
      (o1+o2 in FReach[] and some a and some b and 
        a!=b and a+b in examples_fiboheap_Node and a in node_prevs[b]) 
           implies o1 in node_prevs[o2]
} 

fact orderFibHeapNodeCondition_e {
  all disj o1, o2 : examples_fiboheap_Node | 
    let a = minP[o1] | let b = minP[o2] | 
      (o1+o2 in FReach[] and some a and some b and 
        a in examples_fiboheap_FibHeap and b in examples_fiboheap_Node) 
           implies o1 in node_prevs[o2]
}

fact compactFibHeapNode { 
  all o : examples_fiboheap_Node | o in FReach[] 
    implies node_prevs[o] in FReach[]
} 




fun node_next[]: (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10) -> lone (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10)  
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
} 
fun node_prevs[e: N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10] :set (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10) 
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
 ) 
} 


































































fun node_relprevs[] :( N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10 ) -> set ( N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10 ) 
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
} 
fun node_min [es: set ( N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10 )] : lone ( N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10 ) 
{ 
  es - es.( 
   N0 -> ( N1+N2+N3+N4+N5+N6+N7+N8+N9+N10 ) 
   + 
   N1 -> ( N2+N3+N4+N5+N6+N7+N8+N9+N10 ) 
   + 
   N2 -> ( N3+N4+N5+N6+N7+N8+N9+N10 ) 
   + 
   N3 -> ( N4+N5+N6+N7+N8+N9+N10 ) 
   + 
   N4 -> ( N5+N6+N7+N8+N9+N10 ) 
   + 
   N5 -> ( N6+N7+N8+N9+N10 ) 
   + 
   N6 -> ( N7+N8+N9+N10 ) 
   + 
   N7 -> ( N8+N9+N10 ) 
   + 
   N8 -> ( N9+N10 ) 
   + 
   N9 -> ( N10 ) 
  ) 
} 
-- no ordering axiom//fact ffields_bfields 
fact { 
QF.bexamples_fiboheap_Node_child_0 in none->none 
QF.bexamples_fiboheap_Node_parent_0 in N1->N0 
+N2->N0 
+N2->N1 
+N3->N0 
+N3->N1 
+N3->N2 
+N4->N0 
+N4->N1 
+N4->N2 
+N4->N3 
+N5->N0 
+N5->N1 
+N5->N2 
+N5->N3 
+N5->N4 
+N6->N0 
+N6->N1 
+N6->N2 
+N6->N3 
+N6->N4 
+N6->N5 
+N7->N0 
+N7->N1 
+N7->N2 
+N7->N3 
+N7->N4 
+N7->N5 
+N7->N6 
+N8->N0 
+N8->N1 
+N8->N2 
+N8->N3 
+N8->N4 
+N8->N5 
+N8->N6 
+N8->N7 
+N9->N0 
+N9->N1 
+N9->N2 
+N9->N3 
+N9->N4 
+N9->N5 
+N9->N6 
+N9->N7 
+N9->N8 
+N10->N0 
+N10->N1 
+N10->N2 
+N10->N3 
+N10->N4 
+N10->N5 
+N10->N6 
+N10->N7 
+N10->N8 
+N10->N9 
 
QF.bexamples_fiboheap_Node_right_0 in N0->N0 
+N1->N0 
+N1->N1 
+N2->N1 
+N2->N2 
+N3->N1 
+N3->N2 
+N3->N3 
+N4->N1 
+N4->N2 
+N4->N3 
+N4->N4 
+N5->N2 
+N5->N3 
+N5->N4 
+N5->N5 
+N6->N2 
+N6->N3 
+N6->N4 
+N6->N5 
+N6->N6 
+N7->N3 
+N7->N4 
+N7->N5 
+N7->N6 
+N7->N7 
+N8->N4 
+N8->N5 
+N8->N6 
+N8->N7 
+N8->N8 
+N9->N4 
+N9->N5 
+N9->N6 
+N9->N7 
+N9->N8 
+N9->N9 
+N10->N4 
+N10->N5 
+N10->N6 
+N10->N7 
+N10->N8 
+N10->N9 
+N10->N10 
 
QF.fexamples_fiboheap_Node_right_0 in N0->N1 
+N0->N2 
+N0->N3 
+N0->null 
+N1->N2 
+N1->N3 
+N1->N4 
+N1->null 
+N2->N3 
+N2->N4 
+N2->N5 
+N2->N6 
+N2->N7 
+N2->N8 
+N2->null 
+N3->N4 
+N3->N5 
+N3->N6 
+N3->N7 
+N3->N8 
+N3->N9 
+N3->N10 
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
+N5->null 
+N6->N7 
+N6->N8 
+N6->N9 
+N6->N10 
+N6->null 
+N7->N8 
+N7->N9 
+N7->N10 
+N7->null 
+N8->N9 
+N8->N10 
+N8->null 
+N9->N10 
+N9->null 
+N10->null 
 
QF.fexamples_fiboheap_Node_parent_0 in N0->null 
+N1->null 
+N2->null 
+N3->null 
+N4->null 
+N5->null 
+N6->null 
+N7->null 
+N8->null 
+N9->null 
+N10->null 
 
QF.fexamples_fiboheap_Node_child_0 in N0->N1 
+N0->N2 
+N0->null 
+N1->N2 
+N1->N3 
+N1->N4 
+N1->N5 
+N1->null 
+N2->N3 
+N2->N4 
+N2->N5 
+N2->N6 
+N2->N7 
+N2->null 
+N3->N4 
+N3->N5 
+N3->N6 
+N3->N7 
+N3->N8 
+N3->N9 
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
+N5->null 
+N6->N7 
+N6->N8 
+N6->N9 
+N6->N10 
+N6->null 
+N7->N8 
+N7->N9 
+N7->N10 
+N7->null 
+N8->N9 
+N8->N10 
+N8->null 
+N9->N10 
+N9->null 
+N10->null 
 
QF.bexamples_fiboheap_Node_left_0 in N0->N0 
+N1->N0 
+N1->N1 
+N2->N0 
+N2->N1 
+N2->N2 
+N3->N0 
+N3->N1 
+N3->N2 
+N3->N3 
+N4->N1 
+N4->N2 
+N4->N3 
+N4->N4 
+N5->N2 
+N5->N3 
+N5->N4 
+N5->N5 
+N6->N2 
+N6->N3 
+N6->N4 
+N6->N5 
+N6->N6 
+N7->N2 
+N7->N3 
+N7->N4 
+N7->N5 
+N7->N6 
+N7->N7 
+N8->N2 
+N8->N3 
+N8->N4 
+N8->N5 
+N8->N6 
+N8->N7 
+N8->N8 
+N9->N3 
+N9->N4 
+N9->N5 
+N9->N6 
+N9->N7 
+N9->N8 
+N9->N9 
+N10->N3 
+N10->N4 
+N10->N5 
+N10->N6 
+N10->N7 
+N10->N8 
+N10->N9 
+N10->N10 
 
QF.fexamples_fiboheap_Node_left_0 in N0->N1 
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
+N5->null 
+N6->N7 
+N6->N8 
+N6->N9 
+N6->N10 
+N6->null 
+N7->N8 
+N7->N9 
+N7->N10 
+N7->null 
+N8->N9 
+N8->N10 
+N8->null 
+N9->N10 
+N9->null 
+N10->null 
 
} 
// fact int_fields 
fact { 
QF.examples_fiboheap_Node_degree_0 in N0->0 
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
+N2->0 
+N2->1 
+N2->2 
+N2->3 
+N2->4 
+N2->5 
+N2->6 
+N2->7 
+N2->8 
+N3->0 
+N3->1 
+N3->2 
+N3->3 
+N3->4 
+N3->5 
+N3->6 
+N3->7 
+N4->0 
+N4->1 
+N4->2 
+N4->3 
+N4->4 
+N4->5 
+N4->6 
+N5->0 
+N5->1 
+N5->2 
+N5->3 
+N5->4 
+N5->5 
+N6->0 
+N6->1 
+N6->2 
+N6->3 
+N6->4 
+N7->0 
+N7->1 
+N7->2 
+N7->3 
+N8->0 
+N8->1 
+N8->2 
+N9->0 
+N9->1 
+N10->0 

} 
//fact data_fields 
fact { 
QF.examples_fiboheap_Node_cost_0 in N0->0 
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

} 
//fact root_int_fields 
fact { 
(QF.examples_fiboheap_FibHeap_n_0) in QF.thiz_0->0 
+QF.thiz_0->1 
+QF.thiz_0->2 
+QF.thiz_0->3 
+QF.thiz_0->4 
+QF.thiz_0->5 
+QF.thiz_0->6 
+QF.thiz_0->7 
+QF.thiz_0->8 
+QF.thiz_0->9 
+QF.thiz_0->10 
+QF.thiz_0->11 

} 
//fact root_node_fields 
fact { 
(QF.examples_fiboheap_FibHeap_min_0) in QF.thiz_0->N0 
+QF.thiz_0->null 

} 




