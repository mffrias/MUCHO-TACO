/* 
 * DynAlloy translator options 
 * --------------------------- 
 * applySimplifications= true
 * assertionId= AList_m1
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

pred pred_empty_set[l: set univ] { (no l) } 

pred pred_set_some[l: set univ] { some l } 

pred pred_set_one[l: set univ] { one l } 

pred pred_set_lone[l: set univ] { lone l } 

pred pred_Object_subset[
  s: set univ
] {
  s in Object+null
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

pred instanceOf[n: Object, t: set Object] { n in t } 

pred getUnusedObjectPost[
  usedObjects1:set Object, 
  usedObjects0:set Object,
  n1: Object+null
]{ 
  n1 !in usedObjects0 
  usedObjects1 = usedObjects0 + (n1)
}
//-------------- amelia_dlist_ApacheListNode--------------//
sig ApacheListNode extends Object {}
{}





//-------------- java_lang_RuntimeException--------------//
abstract sig RuntimeException extends Exception {}
{}



one
sig RuntimeExceptionLit extends RuntimeException {}
{}


//-------------- java_lang_Exception--------------//
sig Exception extends Throwable {}
{}



one
sig ExceptionLit extends Exception {}
{}


//-------------- java_lang_Throwable--------------//
abstract sig Throwable extends Object {}
{}





//-------------- java_lang_Object--------------//
abstract sig Object {}
{}





//-------------- java_lang_NullPointerException--------------//
abstract sig NullPointerException extends RuntimeException {}
{}



one
sig NullPointerExceptionLit extends NullPointerException {}
{}


//-------------- amelia_dlist_ApacheList--------------//
sig ApacheList extends Object {}
{}




pred ApacheListCondition10[
  equalValue:univ
]{
   equ[equalValue,
      true]

}

pred ApacheListCondition2[
  thiz:univ
]{
   isEmptyOrNull[thiz]

}

pred ApacheListCondition9[
  myValue:univ
]{
   not (
     neq[myValue,
        null]
   )

}

pred ApacheList_myseq_abstraction[
  header:univ->univ,
  i:univ,
  myseq:univ->(seq univ),
  next:univ->univ,
  previous:univ->univ,
  thiz:univ
]{
   (
     all i:Int | {
       (
         gte[i,
            0]
         and 
         lt[i,
           sub[fun_list_size[thiz.myseq],1]]
       )
       implies 
               instanceOf[fun_list_get[thiz.myseq,i],
                         ApacheListNode]
     
     }
   )
   and 
   equ[sub[fun_set_size[fun_reach[thiz.header,ApacheListNode,next]],1],
      fun_list_size[thiz.myseq]]
   and 
   (
     equ[(thiz.header).next,
        thiz.header]
     implies 
             pred_empty_list[thiz.myseq]
   )
   and 
   (
     neq[(thiz.header).next,
        thiz.header]
     implies 
             (
               equ[(thiz.header).next,
                  fun_list_get[thiz.myseq,0]]
               and 
               equ[(thiz.header).previous,
                  fun_list_get[thiz.myseq,sub[fun_list_size[thiz.myseq],1]]]
             )
   )
   and 
   (
     all i:Int | {
       (
         gte[i,
            0]
         and 
         lt[i,
           sub[fun_list_size[thiz.myseq],1]]
       )
       implies 
               equ[(fun_list_get[thiz.myseq,i]).next,
                  fun_list_get[thiz.myseq,add[i,1]]]
     
     }
   )

}

pred ApacheListCondition8[
  myValue:univ
]{
   neq[myValue,
      null]

}

pred ApacheListCondition3[
  thiz:univ
]{
   not (
     isEmptyOrNull[thiz])

}

pred ApacheListCondition5[
  node:univ
]{
   not (
     isEmptyOrNull[node])

}

pred ApacheListCondition4[
  node:univ
]{
   isEmptyOrNull[node]

}

pred ApacheListCondition11[
  equalValue:univ
]{
   not (
     equ[equalValue,
        true]
   )

}

pred ApacheList_invariant[
  header:univ->univ,
  next:univ->univ,
  previous:univ->univ,
  size:univ->univ,
  thiz:univ
]{
   neq[thiz.header,
      null]
   and 
   neq[(thiz.header).next,
      null]
   and 
   neq[(thiz.header).previous,
      null]
   and 
   (
     all n:ApacheListNode+null | {
       equ[fun_set_contains[fun_reach[thiz.header,ApacheListNode,next],n],
          true]
       implies 
               (
                 neq[n,
                    null]
                 and 
                 neq[n.previous,
                    null]
                 and 
                 equ[(n.previous).next,
                    n]
                 and 
                 neq[n.next,
                    null]
                 and 
                 equ[(n.next).previous,
                    n]
               )
     
     }
   )
   and 
   equ[thiz.size,
      sub[fun_set_size[fun_reach[thiz.header,ApacheListNode,next]],1]]
   and 
   gte[thiz.size,
      0]

}

pred ApacheListCondition13[
  header:univ->univ,
  indexFound:univ,
  node:univ,
  thiz:univ
]{
   not (
     equ[indexFound,
        negate[1]]
     and 
     neq[node,
        thiz.header]
   )

}

pred ApacheList_ensures[
  i:univ,
  myseq':univ->(seq univ),
  nodeValue':univ->univ,
  return':univ,
  thiz':univ,
  value_param:univ
]{
   (
     (
       some i:Int | {
         gte[i,
            0]
         and 
         lt[i,
           fun_list_size[thiz'.myseq']]
         and 
         equ[(fun_list_get[thiz'.myseq',i]).nodeValue',
            value_param]
       
       }
     )
     implies 
             equ[return',
                true]
   )
   and 
   (
     equ[return',
        true]
     implies 
             (
               some i:Int | {
                 gte[i,
                    0]
                 and 
                 lt[i,
                   fun_list_size[thiz'.myseq']]
                 and 
                 equ[(fun_list_get[thiz'.myseq',i]).nodeValue',
                    value_param]
               
               }
             )
   )

}

pred ApacheListCondition12[
  header:univ->univ,
  indexFound:univ,
  node:univ,
  thiz:univ
]{
   equ[indexFound,
      negate[1]]
   and 
   neq[node,
      thiz.header]

}

pred ApacheListCondition16[
  nullDerefBool:univ,
  throw:univ
]{
   equ[nullDerefBool,
      true]
   and 
   equ[throw,
      null]

}

pred ApacheListCondition17[
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

pred ApacheListCondition15[
  index:univ
]{
   not (
     neq[index,
        negate[1]]
   )

}

pred ApacheListCondition14[
  index:univ
]{
   neq[index,
      negate[1]]

}

pred ApacheListCondition1[
  header:univ->univ,
  thiz:univ
]{
   not (
     isEmptyOrNull[thiz.header]
     and 
     isEmptyOrNull[thiz]
   )

}

pred ApacheListCondition0[
  header:univ->univ,
  thiz:univ
]{
   isEmptyOrNull[thiz.header]
   and 
   isEmptyOrNull[thiz]

}

pred ApacheListCondition6[
  myValue:univ,
  value_param:univ
]{
   equ[myValue,
      value_param]

}

pred ApacheListCondition7[
  myValue:univ,
  value_param:univ
]{
   not (
     equ[myValue,
        value_param]
   )

}

pred postcondition_ApacheList_contains_0[
  i:univ,
  myseq':univ->(seq univ),
  nodeValue':univ->univ,
  return':univ,
  thiz':univ,
  throw':univ,
  value_param:univ
]{
   ApacheList_ensures[i,
                     myseq',
                     nodeValue',
                     return',
                     thiz',
                     value_param]
   and 
   equ[throw',
      null]

}

pred precondition_ApacheList_contains_0[
  header:univ->univ,
  i:univ,
  myseq:univ->(seq univ),
  next:univ->univ,
  previous:univ->univ,
  size:univ->univ,
  thiz:univ
]{
   ApacheList_invariant[header,
                       next,
                       previous,
                       size,
                       thiz]
   and 
   ApacheList_myseq_abstraction[header,
                               i,
                               myseq,
                               next,
                               previous,
                               thiz]

}
//-------------- amelia_dlist_Data--------------//
sig Data extends Object {}
{}



pred getUnusedObject[
  n_1: Object + null,
  usedObjects_0: set Object,
  usedObjects_1: set Object
]{
  TruePred[]
  and 
  getUnusedObjectPost[usedObjects_1,
                     usedObjects_0,
                     n_1]
}


pred updateVariable[
  l_1: univ,
  r_0: univ
]{
  TruePred[]
  and 
  equ[l_1,
     r_0]
}


pred havocVariable[
  v_1: univ
]{
  TruePred[]
  and 
  havocVarPost[v_1]
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


pred ApacheList_contains_0[
  thiz_0: ApacheList,
  throw_1: Throwable + null,
  throw_2: Throwable + null,
  return_1: boolean,
  value_param_0: Data + null,
  next_0: ( ApacheListNode ) -> one ( ApacheListNode + null ),
  nodeValue_0: ( ApacheListNode ) -> one ( Data + null ),
  header_0: ( ApacheList ) -> one ( ApacheListNode + null ),
  result_1: boolean,
  node_1: ApacheListNode + null,
  node_2: ApacheListNode + null,
  node_3: ApacheListNode + null,
  node_4: ApacheListNode + null,
  node_5: ApacheListNode + null,
  node_6: ApacheListNode + null,
  node_7: ApacheListNode + null,
  node_8: ApacheListNode + null,
  node_9: ApacheListNode + null,
  node_10: ApacheListNode + null,
  node_11: ApacheListNode + null,
  index_1: Int,
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
  myValue_0: Data + null,
  myValue_1: Data + null,
  myValue_2: Data + null,
  myValue_3: Data + null,
  myValue_4: Data + null,
  myValue_5: Data + null,
  myValue_6: Data + null,
  myValue_7: Data + null,
  myValue_8: Data + null,
  myValue_9: Data + null,
  myValue_10: Data + null,
  indexFound_1: Int,
  indexFound_2: Int,
  indexFound_3: Int,
  indexFound_4: Int,
  indexFound_5: Int,
  indexFound_6: Int,
  indexFound_7: Int,
  indexFound_8: Int,
  indexFound_9: Int,
  indexFound_10: Int,
  indexFound_11: Int,
  equalValue_0: boolean,
  equalValue_1: boolean,
  equalValue_2: boolean,
  equalValue_3: boolean,
  equalValue_4: boolean,
  equalValue_5: boolean,
  equalValue_6: boolean,
  equalValue_7: boolean,
  equalValue_8: boolean,
  equalValue_9: boolean,
  equalValue_10: boolean,
  i_1: Int,
  i_2: Int,
  i_3: Int,
  i_4: Int,
  i_5: Int,
  i_6: Int,
  i_7: Int,
  i_8: Int,
  i_9: Int,
  i_10: Int,
  i_11: Int
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
  TruePred[]
  and 
  TruePred[]
  and 
  TruePred[]
  and 
  (
    i_1=0)
  and 
  (
    (
      ApacheListCondition0[header_0,
                          thiz_0]
      and 
      (
        nullDerefBool_2=true)
    )
    or 
    (
      (
        not (
          ApacheListCondition0[header_0,
                              thiz_0]
        )
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
    node_1=(thiz_0.header_0).next_0)
  and 
  TruePred[]
  and 
  (
    indexFound_1=negate[1])
  and 
  (
    (
      ApacheListCondition2[thiz_0]
      and 
      (
        nullDerefBool_3=true)
    )
    or 
    (
      (
        not (
          ApacheListCondition2[thiz_0])
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
      ApacheListCondition12[header_0,
                           indexFound_1,
                           node_1,
                           thiz_0]
      and 
      TruePred[]
      and 
      (
        (
          ApacheListCondition4[node_1]
          and 
          (
            nullDerefBool_4=true)
        )
        or 
        (
          (
            not (
              ApacheListCondition4[node_1])
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
        myValue_1=node_1.nodeValue_0)
      and 
      TruePred[]
      and 
      (
        (
          ApacheListCondition6[myValue_1,
                              value_param_0]
          and 
          (
            equalValue_1=true)
        )
        or 
        (
          (
            not (
              ApacheListCondition6[myValue_1,
                                  value_param_0]
            )
          )
          and 
          (
            (
              ApacheListCondition8[myValue_1]
              and 
              (
                (
                  ApacheListCondition6[myValue_1,
                                      value_param_0]
                  and 
                  (
                    equalValue_1=true)
                )
                or 
                (
                  (
                    not (
                      ApacheListCondition6[myValue_1,
                                          value_param_0]
                    )
                  )
                  and 
                  (
                    equalValue_1=false)
                )
              )
            )
            or 
            (
              (
                not (
                  ApacheListCondition8[myValue_1])
              )
              and 
              (
                equalValue_1=false)
            )
          )
        )
      )
      and 
      (
        (
          ApacheListCondition10[equalValue_1]
          and 
          (
            indexFound_2=i_1)
        )
        or 
        (
          (
            not (
              ApacheListCondition10[equalValue_1])
          )
          and 
          TruePred[]
          and 
          (
            indexFound_1=indexFound_2)
        )
      )
      and 
      (
        i_2=add[i_1,1])
      and 
      (
        (
          ApacheListCondition4[node_1]
          and 
          (
            nullDerefBool_5=true)
        )
        or 
        (
          (
            not (
              ApacheListCondition4[node_1])
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
        node_2=node_1.next_0)
    )
    or 
    (
      TruePred[]
      and 
      (
        node_1=node_2)
      and 
      (
        indexFound_1=indexFound_2)
      and 
      (
        myValue_0=myValue_1)
      and 
      (
        nullDerefBool_3=nullDerefBool_5)
      and 
      (
        equalValue_0=equalValue_1)
      and 
      (
        i_1=i_2)
    )
  )
  and 
  (
    (
      ApacheListCondition12[header_0,
                           indexFound_2,
                           node_2,
                           thiz_0]
      and 
      TruePred[]
      and 
      (
        (
          ApacheListCondition4[node_2]
          and 
          (
            nullDerefBool_6=true)
        )
        or 
        (
          (
            not (
              ApacheListCondition4[node_2])
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
        myValue_2=node_2.nodeValue_0)
      and 
      TruePred[]
      and 
      (
        (
          ApacheListCondition6[myValue_2,
                              value_param_0]
          and 
          (
            equalValue_2=true)
        )
        or 
        (
          (
            not (
              ApacheListCondition6[myValue_2,
                                  value_param_0]
            )
          )
          and 
          (
            (
              ApacheListCondition8[myValue_2]
              and 
              (
                (
                  ApacheListCondition6[myValue_2,
                                      value_param_0]
                  and 
                  (
                    equalValue_2=true)
                )
                or 
                (
                  (
                    not (
                      ApacheListCondition6[myValue_2,
                                          value_param_0]
                    )
                  )
                  and 
                  (
                    equalValue_2=false)
                )
              )
            )
            or 
            (
              (
                not (
                  ApacheListCondition8[myValue_2])
              )
              and 
              (
                equalValue_2=false)
            )
          )
        )
      )
      and 
      (
        (
          ApacheListCondition10[equalValue_2]
          and 
          (
            indexFound_3=i_2)
        )
        or 
        (
          (
            not (
              ApacheListCondition10[equalValue_2])
          )
          and 
          TruePred[]
          and 
          (
            indexFound_2=indexFound_3)
        )
      )
      and 
      (
        i_3=add[i_2,1])
      and 
      (
        (
          ApacheListCondition4[node_2]
          and 
          (
            nullDerefBool_7=true)
        )
        or 
        (
          (
            not (
              ApacheListCondition4[node_2])
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
        node_3=node_2.next_0)
    )
    or 
    (
      TruePred[]
      and 
      (
        node_2=node_3)
      and 
      (
        indexFound_2=indexFound_3)
      and 
      (
        myValue_1=myValue_2)
      and 
      (
        nullDerefBool_5=nullDerefBool_7)
      and 
      (
        equalValue_1=equalValue_2)
      and 
      (
        i_2=i_3)
    )
  )
  and 
  (
    (
      ApacheListCondition12[header_0,
                           indexFound_3,
                           node_3,
                           thiz_0]
      and 
      TruePred[]
      and 
      (
        (
          ApacheListCondition4[node_3]
          and 
          (
            nullDerefBool_8=true)
        )
        or 
        (
          (
            not (
              ApacheListCondition4[node_3])
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
        myValue_3=node_3.nodeValue_0)
      and 
      TruePred[]
      and 
      (
        (
          ApacheListCondition6[myValue_3,
                              value_param_0]
          and 
          (
            equalValue_3=true)
        )
        or 
        (
          (
            not (
              ApacheListCondition6[myValue_3,
                                  value_param_0]
            )
          )
          and 
          (
            (
              ApacheListCondition8[myValue_3]
              and 
              (
                (
                  ApacheListCondition6[myValue_3,
                                      value_param_0]
                  and 
                  (
                    equalValue_3=true)
                )
                or 
                (
                  (
                    not (
                      ApacheListCondition6[myValue_3,
                                          value_param_0]
                    )
                  )
                  and 
                  (
                    equalValue_3=false)
                )
              )
            )
            or 
            (
              (
                not (
                  ApacheListCondition8[myValue_3])
              )
              and 
              (
                equalValue_3=false)
            )
          )
        )
      )
      and 
      (
        (
          ApacheListCondition10[equalValue_3]
          and 
          (
            indexFound_4=i_3)
        )
        or 
        (
          (
            not (
              ApacheListCondition10[equalValue_3])
          )
          and 
          TruePred[]
          and 
          (
            indexFound_3=indexFound_4)
        )
      )
      and 
      (
        i_4=add[i_3,1])
      and 
      (
        (
          ApacheListCondition4[node_3]
          and 
          (
            nullDerefBool_9=true)
        )
        or 
        (
          (
            not (
              ApacheListCondition4[node_3])
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
        node_4=node_3.next_0)
    )
    or 
    (
      TruePred[]
      and 
      (
        node_3=node_4)
      and 
      (
        indexFound_3=indexFound_4)
      and 
      (
        myValue_2=myValue_3)
      and 
      (
        nullDerefBool_7=nullDerefBool_9)
      and 
      (
        equalValue_2=equalValue_3)
      and 
      (
        i_3=i_4)
    )
  )
  and 
  (
    (
      ApacheListCondition12[header_0,
                           indexFound_4,
                           node_4,
                           thiz_0]
      and 
      TruePred[]
      and 
      (
        (
          ApacheListCondition4[node_4]
          and 
          (
            nullDerefBool_10=true)
        )
        or 
        (
          (
            not (
              ApacheListCondition4[node_4])
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
        myValue_4=node_4.nodeValue_0)
      and 
      TruePred[]
      and 
      (
        (
          ApacheListCondition6[myValue_4,
                              value_param_0]
          and 
          (
            equalValue_4=true)
        )
        or 
        (
          (
            not (
              ApacheListCondition6[myValue_4,
                                  value_param_0]
            )
          )
          and 
          (
            (
              ApacheListCondition8[myValue_4]
              and 
              (
                (
                  ApacheListCondition6[myValue_4,
                                      value_param_0]
                  and 
                  (
                    equalValue_4=true)
                )
                or 
                (
                  (
                    not (
                      ApacheListCondition6[myValue_4,
                                          value_param_0]
                    )
                  )
                  and 
                  (
                    equalValue_4=false)
                )
              )
            )
            or 
            (
              (
                not (
                  ApacheListCondition8[myValue_4])
              )
              and 
              (
                equalValue_4=false)
            )
          )
        )
      )
      and 
      (
        (
          ApacheListCondition10[equalValue_4]
          and 
          (
            indexFound_5=i_4)
        )
        or 
        (
          (
            not (
              ApacheListCondition10[equalValue_4])
          )
          and 
          TruePred[]
          and 
          (
            indexFound_4=indexFound_5)
        )
      )
      and 
      (
        i_5=add[i_4,1])
      and 
      (
        (
          ApacheListCondition4[node_4]
          and 
          (
            nullDerefBool_11=true)
        )
        or 
        (
          (
            not (
              ApacheListCondition4[node_4])
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
        node_5=node_4.next_0)
    )
    or 
    (
      TruePred[]
      and 
      (
        node_4=node_5)
      and 
      (
        indexFound_4=indexFound_5)
      and 
      (
        myValue_3=myValue_4)
      and 
      (
        nullDerefBool_9=nullDerefBool_11)
      and 
      (
        equalValue_3=equalValue_4)
      and 
      (
        i_4=i_5)
    )
  )
  and 
  (
    (
      ApacheListCondition12[header_0,
                           indexFound_5,
                           node_5,
                           thiz_0]
      and 
      TruePred[]
      and 
      (
        (
          ApacheListCondition4[node_5]
          and 
          (
            nullDerefBool_12=true)
        )
        or 
        (
          (
            not (
              ApacheListCondition4[node_5])
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
        myValue_5=node_5.nodeValue_0)
      and 
      TruePred[]
      and 
      (
        (
          ApacheListCondition6[myValue_5,
                              value_param_0]
          and 
          (
            equalValue_5=true)
        )
        or 
        (
          (
            not (
              ApacheListCondition6[myValue_5,
                                  value_param_0]
            )
          )
          and 
          (
            (
              ApacheListCondition8[myValue_5]
              and 
              (
                (
                  ApacheListCondition6[myValue_5,
                                      value_param_0]
                  and 
                  (
                    equalValue_5=true)
                )
                or 
                (
                  (
                    not (
                      ApacheListCondition6[myValue_5,
                                          value_param_0]
                    )
                  )
                  and 
                  (
                    equalValue_5=false)
                )
              )
            )
            or 
            (
              (
                not (
                  ApacheListCondition8[myValue_5])
              )
              and 
              (
                equalValue_5=false)
            )
          )
        )
      )
      and 
      (
        (
          ApacheListCondition10[equalValue_5]
          and 
          (
            indexFound_6=i_5)
        )
        or 
        (
          (
            not (
              ApacheListCondition10[equalValue_5])
          )
          and 
          TruePred[]
          and 
          (
            indexFound_5=indexFound_6)
        )
      )
      and 
      (
        i_6=add[i_5,1])
      and 
      (
        (
          ApacheListCondition4[node_5]
          and 
          (
            nullDerefBool_13=true)
        )
        or 
        (
          (
            not (
              ApacheListCondition4[node_5])
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
        node_6=node_5.next_0)
    )
    or 
    (
      TruePred[]
      and 
      (
        node_5=node_6)
      and 
      (
        indexFound_5=indexFound_6)
      and 
      (
        myValue_4=myValue_5)
      and 
      (
        nullDerefBool_11=nullDerefBool_13)
      and 
      (
        equalValue_4=equalValue_5)
      and 
      (
        i_5=i_6)
    )
  )
  and 
  (
    (
      ApacheListCondition12[header_0,
                           indexFound_6,
                           node_6,
                           thiz_0]
      and 
      TruePred[]
      and 
      (
        (
          ApacheListCondition4[node_6]
          and 
          (
            nullDerefBool_14=true)
        )
        or 
        (
          (
            not (
              ApacheListCondition4[node_6])
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
        myValue_6=node_6.nodeValue_0)
      and 
      TruePred[]
      and 
      (
        (
          ApacheListCondition6[myValue_6,
                              value_param_0]
          and 
          (
            equalValue_6=true)
        )
        or 
        (
          (
            not (
              ApacheListCondition6[myValue_6,
                                  value_param_0]
            )
          )
          and 
          (
            (
              ApacheListCondition8[myValue_6]
              and 
              (
                (
                  ApacheListCondition6[myValue_6,
                                      value_param_0]
                  and 
                  (
                    equalValue_6=true)
                )
                or 
                (
                  (
                    not (
                      ApacheListCondition6[myValue_6,
                                          value_param_0]
                    )
                  )
                  and 
                  (
                    equalValue_6=false)
                )
              )
            )
            or 
            (
              (
                not (
                  ApacheListCondition8[myValue_6])
              )
              and 
              (
                equalValue_6=false)
            )
          )
        )
      )
      and 
      (
        (
          ApacheListCondition10[equalValue_6]
          and 
          (
            indexFound_7=i_6)
        )
        or 
        (
          (
            not (
              ApacheListCondition10[equalValue_6])
          )
          and 
          TruePred[]
          and 
          (
            indexFound_6=indexFound_7)
        )
      )
      and 
      (
        i_7=add[i_6,1])
      and 
      (
        (
          ApacheListCondition4[node_6]
          and 
          (
            nullDerefBool_15=true)
        )
        or 
        (
          (
            not (
              ApacheListCondition4[node_6])
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
        node_7=node_6.next_0)
    )
    or 
    (
      TruePred[]
      and 
      (
        node_6=node_7)
      and 
      (
        indexFound_6=indexFound_7)
      and 
      (
        myValue_5=myValue_6)
      and 
      (
        nullDerefBool_13=nullDerefBool_15)
      and 
      (
        equalValue_5=equalValue_6)
      and 
      (
        i_6=i_7)
    )
  )
  and 
  (
    (
      ApacheListCondition12[header_0,
                           indexFound_7,
                           node_7,
                           thiz_0]
      and 
      TruePred[]
      and 
      (
        (
          ApacheListCondition4[node_7]
          and 
          (
            nullDerefBool_16=true)
        )
        or 
        (
          (
            not (
              ApacheListCondition4[node_7])
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
        myValue_7=node_7.nodeValue_0)
      and 
      TruePred[]
      and 
      (
        (
          ApacheListCondition6[myValue_7,
                              value_param_0]
          and 
          (
            equalValue_7=true)
        )
        or 
        (
          (
            not (
              ApacheListCondition6[myValue_7,
                                  value_param_0]
            )
          )
          and 
          (
            (
              ApacheListCondition8[myValue_7]
              and 
              (
                (
                  ApacheListCondition6[myValue_7,
                                      value_param_0]
                  and 
                  (
                    equalValue_7=true)
                )
                or 
                (
                  (
                    not (
                      ApacheListCondition6[myValue_7,
                                          value_param_0]
                    )
                  )
                  and 
                  (
                    equalValue_7=false)
                )
              )
            )
            or 
            (
              (
                not (
                  ApacheListCondition8[myValue_7])
              )
              and 
              (
                equalValue_7=false)
            )
          )
        )
      )
      and 
      (
        (
          ApacheListCondition10[equalValue_7]
          and 
          (
            indexFound_8=i_7)
        )
        or 
        (
          (
            not (
              ApacheListCondition10[equalValue_7])
          )
          and 
          TruePred[]
          and 
          (
            indexFound_7=indexFound_8)
        )
      )
      and 
      (
        i_8=add[i_7,1])
      and 
      (
        (
          ApacheListCondition4[node_7]
          and 
          (
            nullDerefBool_17=true)
        )
        or 
        (
          (
            not (
              ApacheListCondition4[node_7])
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
        node_8=node_7.next_0)
    )
    or 
    (
      TruePred[]
      and 
      (
        node_7=node_8)
      and 
      (
        indexFound_7=indexFound_8)
      and 
      (
        myValue_6=myValue_7)
      and 
      (
        nullDerefBool_15=nullDerefBool_17)
      and 
      (
        equalValue_6=equalValue_7)
      and 
      (
        i_7=i_8)
    )
  )
  and 
  (
    (
      ApacheListCondition12[header_0,
                           indexFound_8,
                           node_8,
                           thiz_0]
      and 
      TruePred[]
      and 
      (
        (
          ApacheListCondition4[node_8]
          and 
          (
            nullDerefBool_18=true)
        )
        or 
        (
          (
            not (
              ApacheListCondition4[node_8])
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
        myValue_8=node_8.nodeValue_0)
      and 
      TruePred[]
      and 
      (
        (
          ApacheListCondition6[myValue_8,
                              value_param_0]
          and 
          (
            equalValue_8=true)
        )
        or 
        (
          (
            not (
              ApacheListCondition6[myValue_8,
                                  value_param_0]
            )
          )
          and 
          (
            (
              ApacheListCondition8[myValue_8]
              and 
              (
                (
                  ApacheListCondition6[myValue_8,
                                      value_param_0]
                  and 
                  (
                    equalValue_8=true)
                )
                or 
                (
                  (
                    not (
                      ApacheListCondition6[myValue_8,
                                          value_param_0]
                    )
                  )
                  and 
                  (
                    equalValue_8=false)
                )
              )
            )
            or 
            (
              (
                not (
                  ApacheListCondition8[myValue_8])
              )
              and 
              (
                equalValue_8=false)
            )
          )
        )
      )
      and 
      (
        (
          ApacheListCondition10[equalValue_8]
          and 
          (
            indexFound_9=i_8)
        )
        or 
        (
          (
            not (
              ApacheListCondition10[equalValue_8])
          )
          and 
          TruePred[]
          and 
          (
            indexFound_8=indexFound_9)
        )
      )
      and 
      (
        i_9=add[i_8,1])
      and 
      (
        (
          ApacheListCondition4[node_8]
          and 
          (
            nullDerefBool_19=true)
        )
        or 
        (
          (
            not (
              ApacheListCondition4[node_8])
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
        node_9=node_8.next_0)
    )
    or 
    (
      TruePred[]
      and 
      (
        node_8=node_9)
      and 
      (
        indexFound_8=indexFound_9)
      and 
      (
        myValue_7=myValue_8)
      and 
      (
        nullDerefBool_17=nullDerefBool_19)
      and 
      (
        equalValue_7=equalValue_8)
      and 
      (
        i_8=i_9)
    )
  )
  and 
  (
    (
      ApacheListCondition12[header_0,
                           indexFound_9,
                           node_9,
                           thiz_0]
      and 
      TruePred[]
      and 
      (
        (
          ApacheListCondition4[node_9]
          and 
          (
            nullDerefBool_20=true)
        )
        or 
        (
          (
            not (
              ApacheListCondition4[node_9])
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
        myValue_9=node_9.nodeValue_0)
      and 
      TruePred[]
      and 
      (
        (
          ApacheListCondition6[myValue_9,
                              value_param_0]
          and 
          (
            equalValue_9=true)
        )
        or 
        (
          (
            not (
              ApacheListCondition6[myValue_9,
                                  value_param_0]
            )
          )
          and 
          (
            (
              ApacheListCondition8[myValue_9]
              and 
              (
                (
                  ApacheListCondition6[myValue_9,
                                      value_param_0]
                  and 
                  (
                    equalValue_9=true)
                )
                or 
                (
                  (
                    not (
                      ApacheListCondition6[myValue_9,
                                          value_param_0]
                    )
                  )
                  and 
                  (
                    equalValue_9=false)
                )
              )
            )
            or 
            (
              (
                not (
                  ApacheListCondition8[myValue_9])
              )
              and 
              (
                equalValue_9=false)
            )
          )
        )
      )
      and 
      (
        (
          ApacheListCondition10[equalValue_9]
          and 
          (
            indexFound_10=i_9)
        )
        or 
        (
          (
            not (
              ApacheListCondition10[equalValue_9])
          )
          and 
          TruePred[]
          and 
          (
            indexFound_9=indexFound_10)
        )
      )
      and 
      (
        i_10=add[i_9,1])
      and 
      (
        (
          ApacheListCondition4[node_9]
          and 
          (
            nullDerefBool_21=true)
        )
        or 
        (
          (
            not (
              ApacheListCondition4[node_9])
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
        node_10=node_9.next_0)
    )
    or 
    (
      TruePred[]
      and 
      (
        node_9=node_10)
      and 
      (
        indexFound_9=indexFound_10)
      and 
      (
        myValue_8=myValue_9)
      and 
      (
        nullDerefBool_19=nullDerefBool_21)
      and 
      (
        equalValue_8=equalValue_9)
      and 
      (
        i_9=i_10)
    )
  )
  and 
  (
    (
      ApacheListCondition12[header_0,
                           indexFound_10,
                           node_10,
                           thiz_0]
      and 
      TruePred[]
      and 
      (
        (
          ApacheListCondition4[node_10]
          and 
          (
            nullDerefBool_22=true)
        )
        or 
        (
          (
            not (
              ApacheListCondition4[node_10])
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
        myValue_10=node_10.nodeValue_0)
      and 
      TruePred[]
      and 
      (
        (
          ApacheListCondition6[myValue_10,
                              value_param_0]
          and 
          (
            equalValue_10=true)
        )
        or 
        (
          (
            not (
              ApacheListCondition6[myValue_10,
                                  value_param_0]
            )
          )
          and 
          (
            (
              ApacheListCondition8[myValue_10]
              and 
              (
                (
                  ApacheListCondition6[myValue_10,
                                      value_param_0]
                  and 
                  (
                    equalValue_10=true)
                )
                or 
                (
                  (
                    not (
                      ApacheListCondition6[myValue_10,
                                          value_param_0]
                    )
                  )
                  and 
                  (
                    equalValue_10=false)
                )
              )
            )
            or 
            (
              (
                not (
                  ApacheListCondition8[myValue_10])
              )
              and 
              (
                equalValue_10=false)
            )
          )
        )
      )
      and 
      (
        (
          ApacheListCondition10[equalValue_10]
          and 
          (
            indexFound_11=i_10)
        )
        or 
        (
          (
            not (
              ApacheListCondition10[equalValue_10])
          )
          and 
          TruePred[]
          and 
          (
            indexFound_10=indexFound_11)
        )
      )
      and 
      (
        i_11=add[i_10,1])
      and 
      (
        (
          ApacheListCondition4[node_10]
          and 
          (
            nullDerefBool_23=true)
        )
        or 
        (
          (
            not (
              ApacheListCondition4[node_10])
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
        node_11=node_10.next_0)
    )
    or 
    (
      TruePred[]
      and 
      (
        node_10=node_11)
      and 
      (
        indexFound_10=indexFound_11)
      and 
      (
        myValue_9=myValue_10)
      and 
      (
        nullDerefBool_21=nullDerefBool_23)
      and 
      (
        equalValue_9=equalValue_10)
      and 
      (
        i_10=i_11)
    )
  )
  and 
  ApacheListCondition13[header_0,
                       indexFound_11,
                       node_11,
                       thiz_0]
  and 
  (
    index_1=indexFound_11)
  and 
  (
    (
      ApacheListCondition14[index_1]
      and 
      (
        result_1=true)
    )
    or 
    (
      (
        not (
          ApacheListCondition14[index_1])
      )
      and 
      (
        result_1=false)
    )
  )
  and 
  (
    return_1=result_1)
  and 
  (
    (
      ApacheListCondition16[nullDerefBool_23,
                           throw_1]
      and 
      (
        throw_2=NullPointerExceptionLit)
    )
    or 
    (
      (
        not (
          ApacheListCondition16[nullDerefBool_23,
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
  header_0: ( ApacheList ) -> one ( ApacheListNode + null ),
  i_0: Int,
  l0_equalValue_0: boolean,
  l0_equalValue_1: boolean,
  l0_equalValue_10: boolean,
  l0_equalValue_2: boolean,
  l0_equalValue_3: boolean,
  l0_equalValue_4: boolean,
  l0_equalValue_5: boolean,
  l0_equalValue_6: boolean,
  l0_equalValue_7: boolean,
  l0_equalValue_8: boolean,
  l0_equalValue_9: boolean,
  l0_i_1: Int,
  l0_i_10: Int,
  l0_i_11: Int,
  l0_i_2: Int,
  l0_i_3: Int,
  l0_i_4: Int,
  l0_i_5: Int,
  l0_i_6: Int,
  l0_i_7: Int,
  l0_i_8: Int,
  l0_i_9: Int,
  l0_indexFound_1: Int,
  l0_indexFound_10: Int,
  l0_indexFound_11: Int,
  l0_indexFound_2: Int,
  l0_indexFound_3: Int,
  l0_indexFound_4: Int,
  l0_indexFound_5: Int,
  l0_indexFound_6: Int,
  l0_indexFound_7: Int,
  l0_indexFound_8: Int,
  l0_indexFound_9: Int,
  l0_index_1: Int,
  l0_myValue_0: Data + null,
  l0_myValue_1: Data + null,
  l0_myValue_10: Data + null,
  l0_myValue_2: Data + null,
  l0_myValue_3: Data + null,
  l0_myValue_4: Data + null,
  l0_myValue_5: Data + null,
  l0_myValue_6: Data + null,
  l0_myValue_7: Data + null,
  l0_myValue_8: Data + null,
  l0_myValue_9: Data + null,
  l0_node_1: ApacheListNode + null,
  l0_node_10: ApacheListNode + null,
  l0_node_11: ApacheListNode + null,
  l0_node_2: ApacheListNode + null,
  l0_node_3: ApacheListNode + null,
  l0_node_4: ApacheListNode + null,
  l0_node_5: ApacheListNode + null,
  l0_node_6: ApacheListNode + null,
  l0_node_7: ApacheListNode + null,
  l0_node_8: ApacheListNode + null,
  l0_node_9: ApacheListNode + null,
  l0_nullDerefBool_1: boolean,
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
  l0_nullDerefBool_2: boolean,
  l0_nullDerefBool_20: boolean,
  l0_nullDerefBool_21: boolean,
  l0_nullDerefBool_22: boolean,
  l0_nullDerefBool_23: boolean,
  l0_nullDerefBool_3: boolean,
  l0_nullDerefBool_4: boolean,
  l0_nullDerefBool_5: boolean,
  l0_nullDerefBool_6: boolean,
  l0_nullDerefBool_7: boolean,
  l0_nullDerefBool_8: boolean,
  l0_nullDerefBool_9: boolean,
  l0_result_1: boolean,
  myseq_0: ( ApacheList ) -> ( seq ( null + Object ) ),
  bnext_0,fnext_0: ( ApacheListNode ) -> lone ( ApacheListNode + null ),
  nodeValue_0: ( ApacheListNode ) -> one ( Data + null ),
  bprevious_0,fprevious_0: ( ApacheListNode ) -> lone ( ApacheListNode + null ),
  return_1: boolean,
  size_0: ( ApacheList ) -> one ( Int ),
  thiz_0: ApacheList,
  throw_1: Throwable + null,
  throw_2: Throwable + null,
  value_param_0: Data + null
}


fact {
  precondition_ApacheList_contains_0[QF.header_0,
                                    QF.i_0,
                                    QF.myseq_0,
                                    (QF.fnext_0+QF.bnext_0),
                                    (QF.fprevious_0+QF.bprevious_0),
                                    QF.size_0,
                                    QF.thiz_0]

}

fact {
  ApacheList_contains_0[QF.thiz_0,
                       QF.throw_1,
                       QF.throw_2,
                       QF.return_1,
                       QF.value_param_0,
                       (QF.fnext_0+QF.bnext_0),
                       QF.nodeValue_0,
                       QF.header_0,
                       QF.l0_result_1,
                       QF.l0_node_1,
                       QF.l0_node_2,
                       QF.l0_node_3,
                       QF.l0_node_4,
                       QF.l0_node_5,
                       QF.l0_node_6,
                       QF.l0_node_7,
                       QF.l0_node_8,
                       QF.l0_node_9,
                       QF.l0_node_10,
                       QF.l0_node_11,
                       QF.l0_index_1,
                       QF.l0_nullDerefBool_1,
                       QF.l0_nullDerefBool_2,
                       QF.l0_nullDerefBool_3,
                       QF.l0_nullDerefBool_4,
                       QF.l0_nullDerefBool_5,
                       QF.l0_nullDerefBool_6,
                       QF.l0_nullDerefBool_7,
                       QF.l0_nullDerefBool_8,
                       QF.l0_nullDerefBool_9,
                       QF.l0_nullDerefBool_10,
                       QF.l0_nullDerefBool_11,
                       QF.l0_nullDerefBool_12,
                       QF.l0_nullDerefBool_13,
                       QF.l0_nullDerefBool_14,
                       QF.l0_nullDerefBool_15,
                       QF.l0_nullDerefBool_16,
                       QF.l0_nullDerefBool_17,
                       QF.l0_nullDerefBool_18,
                       QF.l0_nullDerefBool_19,
                       QF.l0_nullDerefBool_20,
                       QF.l0_nullDerefBool_21,
                       QF.l0_nullDerefBool_22,
                       QF.l0_nullDerefBool_23,
                       QF.l0_myValue_0,
                       QF.l0_myValue_1,
                       QF.l0_myValue_2,
                       QF.l0_myValue_3,
                       QF.l0_myValue_4,
                       QF.l0_myValue_5,
                       QF.l0_myValue_6,
                       QF.l0_myValue_7,
                       QF.l0_myValue_8,
                       QF.l0_myValue_9,
                       QF.l0_myValue_10,
                       QF.l0_indexFound_1,
                       QF.l0_indexFound_2,
                       QF.l0_indexFound_3,
                       QF.l0_indexFound_4,
                       QF.l0_indexFound_5,
                       QF.l0_indexFound_6,
                       QF.l0_indexFound_7,
                       QF.l0_indexFound_8,
                       QF.l0_indexFound_9,
                       QF.l0_indexFound_10,
                       QF.l0_indexFound_11,
                       QF.l0_equalValue_0,
                       QF.l0_equalValue_1,
                       QF.l0_equalValue_2,
                       QF.l0_equalValue_3,
                       QF.l0_equalValue_4,
                       QF.l0_equalValue_5,
                       QF.l0_equalValue_6,
                       QF.l0_equalValue_7,
                       QF.l0_equalValue_8,
                       QF.l0_equalValue_9,
                       QF.l0_equalValue_10,
                       QF.l0_i_1,
                       QF.l0_i_2,
                       QF.l0_i_3,
                       QF.l0_i_4,
                       QF.l0_i_5,
                       QF.l0_i_6,
                       QF.l0_i_7,
                       QF.l0_i_8,
                       QF.l0_i_9,
                       QF.l0_i_10,
                       QF.l0_i_11]

}

assert AList_m1{
  postcondition_ApacheList_contains_0[QF.i_0,
                                     QF.myseq_0,
                                     QF.nodeValue_0,
                                     QF.return_1,
                                     QF.thiz_0,
                                     QF.throw_2,
                                     QF.value_param_0]
}
check AList_m1 for 0 but 
                 exactly 1 ApacheList, 
                 exactly 17 Data,
                 exactly 17 ApacheListNode,
                 17 seq, 
                 6 int  



one sig N0,N1,N2,N3,N4,N5,N6,N7,N8,N9,N10,N11,N12,N13,N14,N15,N16 extends ApacheListNode {}
one sig D0,D1,D2,D3,D4,D5,D6,D7,D8,D9,D10,D11,D12,D13,D14,D15,D16 extends Data {}

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
fun data_prevs[e: D0+D1+D2+D3+D4+D5+D6+D7+D8+D9+D10+D11+D12+D13+D14+D15+D16] : set (D0+D1+D2+D3+D4+D5+D6+D7+D8+D9+D10+D11+D12+D13+D14+D15+D16) 
{ 
 e.( 
   D1 -> ( D0 ) 
     +
   D2 -> ( D0+D1 ) 
     +
   D3 -> ( D0+D1+D2 ) 
     +
   D4 -> ( D0+D1+D2+D3 ) 
     +
   D5 -> ( D0+D1+D2+D3+D4 ) 
     +
   D6 -> ( D0+D1+D2+D3+D4+D5 ) 
     +
   D7 -> ( D0+D1+D2+D3+D4+D5+D6 ) 
     +
   D8 -> ( D0+D1+D2+D3+D4+D5+D6+D7 ) 
     +
   D9 -> ( D0+D1+D2+D3+D4+D5+D6+D7+D8 ) 
     +
   D10 -> ( D0+D1+D2+D3+D4+D5+D6+D7+D8+D9 ) 
     +
   D11 -> ( D0+D1+D2+D3+D4+D5+D6+D7+D8+D9+D10 ) 
     +
   D12 -> ( D0+D1+D2+D3+D4+D5+D6+D7+D8+D9+D10+D11 ) 
     +
   D13 -> ( D0+D1+D2+D3+D4+D5+D6+D7+D8+D9+D10+D11+D12 ) 
     +
   D14 -> ( D0+D1+D2+D3+D4+D5+D6+D7+D8+D9+D10+D11+D12+D13 ) 
     +
   D15 -> ( D0+D1+D2+D3+D4+D5+D6+D7+D8+D9+D10+D11+D12+D13+D14 ) 
     +
   D16 -> ( D0+D1+D2+D3+D4+D5+D6+D7+D8+D9+D10+D11+D12+D13+D14+D15 ) 
  ) 
} 
fun data_next[]: (D0+D1+D2+D3+D4+D5+D6+D7+D8+D9+D10+D11+D12+D13+D14+D15+D16) -> (D0+D1+D2+D3+D4+D5+D6+D7+D8+D9+D10+D11+D12+D13+D14+D15+D16) 
{ 
 D0 -> D1 
 +  D1 -> D2 
 +  D2 -> D3 
 +  D3 -> D4 
 +  D4 -> D5 
 +  D5 -> D6 
 +  D6 -> D7 
 +  D7 -> D8 
 +  D8 -> D9 
 +  D9 -> D10 
 +  D10 -> D11 
 +  D11 -> D12 
 +  D12 -> D13 
 +  D13 -> D14 
 +  D14 -> D15 
 +  D15 -> D16 
} 
pred data_lt[e1,e2: D0+D1+D2+D3+D4+D5+D6+D7+D8+D9+D10+D11+D12+D13+D14+D15+D16] { 
   e1 in data_prevs[e2] 
 } 
fun node_rprevs[e: N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16] :set (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16) 
{ 
 e.( 
   N0 -> ( N0 ) 
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
let entry=(QF.thiz_0).(QF.header_0),ff1=QF.fnext_0,ff2=QF.fprevious_0,bf1=QF.bnext_0,bf2=QF.bprevious_0 | { 
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
QF.bprevious_0 in N0->N0 
+N1->N0 
+N2->N1 
+N3->N1 
+N4->N3 
+N5->N3 
+N6->N5 
+N7->N5 
+N8->N7 
+N9->N7 
+N10->N9 
+N11->N9 
+N12->N11 
+N13->N11 
+N14->N13 
+N15->N13 
+N16->N15 
 
QF.bnext_0 in N0->N0 
+N1->N0 
+N2->N0 
+N3->N2 
+N4->N2 
+N5->N4 
+N6->N4 
+N7->N6 
+N8->N6 
+N9->N8 
+N10->N8 
+N11->N10 
+N12->N10 
+N13->N12 
+N14->N12 
+N15->N14 
+N16->N14 
 
QF.fprevious_0 in N0->N1 
+N0->N2 
+N0->null 
+N1->null 
+N2->N3 
+N2->N4 
+N2->null 
+N3->null 
+N4->N5 
+N4->N6 
+N4->null 
+N5->null 
+N6->N7 
+N6->N8 
+N6->null 
+N7->null 
+N8->N9 
+N8->N10 
+N8->null 
+N9->null 
+N10->N11 
+N10->N12 
+N10->null 
+N11->null 
+N12->N13 
+N12->N14 
+N12->null 
+N13->null 
+N14->N15 
+N14->N16 
+N14->null 
+N15->null 
+N16->null 
 
QF.fnext_0 in N0->N1 
+N0->null 
+N1->N2 
+N1->N3 
+N1->null 
+N2->null 
+N3->N4 
+N3->N5 
+N3->null 
+N4->null 
+N5->N6 
+N5->N7 
+N5->null 
+N6->null 
+N7->N8 
+N7->N9 
+N7->null 
+N8->null 
+N9->N10 
+N9->N11 
+N9->null 
+N10->null 
+N11->N12 
+N11->N13 
+N11->null 
+N12->null 
+N13->N14 
+N13->N15 
+N13->null 
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
} 
//fact root_int_fields 
fact { 
(QF.size_0) in (QF.thiz_0)->0 
+(QF.thiz_0)->1 
+(QF.thiz_0)->2 
+(QF.thiz_0)->3 
+(QF.thiz_0)->4 
+(QF.thiz_0)->5 
+(QF.thiz_0)->6 
+(QF.thiz_0)->7 
+(QF.thiz_0)->8 
+(QF.thiz_0)->9 
+(QF.thiz_0)->10 
+(QF.thiz_0)->11 
+(QF.thiz_0)->12 
+(QF.thiz_0)->13 
+(QF.thiz_0)->14 
+(QF.thiz_0)->15 
+(QF.thiz_0)->16 

} 
//fact root_node_fields 
fact { 
} 
