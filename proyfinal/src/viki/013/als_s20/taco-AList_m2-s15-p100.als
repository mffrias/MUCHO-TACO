/* 
 * DynAlloy translator options 
 * --------------------------- 
 * applySimplifications= true
 * assertionId= AList_m2
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




pred ApacheListCondition4[
  freshNode:univ,
  header:univ->univ,
  thiz:univ
]{
   isEmptyOrNull[freshNode]
   and 
   isEmptyOrNull[thiz.header]
   and 
   isEmptyOrNull[thiz]

}

pred ApacheList_myseq_abstraction[
  header:univ->univ,
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

pred precondition_ApacheList_insertBack_0[
  freshNode:univ,
  header:univ->univ,
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
                               myseq,
                               next,
                               previous,
                               thiz]
   and 
   ApacheList_requires[freshNode,
                      header,
                      myseq,
                      thiz]

}

pred ApacheList_ensures[
  freshNode:univ,
  myseq:univ->(seq univ),
  myseq':univ->(seq univ),
  thiz:univ,
  thiz':univ
]{
   equ[fun_list_size[thiz'.myseq'],
      add[fun_list_size[thiz.myseq],1]]
   and 
   equ[fun_list_get[thiz'.myseq',sub[fun_list_size[thiz'.myseq'],1]],
      freshNode]
   and 
   (
     all i:Int | {
       (
         gte[i,
            0]
         and 
         lt[i,
           fun_list_size[thiz.myseq]]
       )
       implies 
               equ[fun_list_get[thiz'.myseq',i],
                  fun_list_get[thiz.myseq,i]]
     
     }
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

pred ApacheListCondition5[
  freshNode:univ,
  header:univ->univ,
  thiz:univ
]{
   not (
     isEmptyOrNull[freshNode]
     and 
     isEmptyOrNull[thiz.header]
     and 
     isEmptyOrNull[thiz]
   )

}

pred ApacheListCondition0[
  freshNode:univ
]{
   isEmptyOrNull[freshNode]

}

pred ApacheListCondition1[
  freshNode:univ
]{
   not (
     isEmptyOrNull[freshNode])

}

pred ApacheListCondition7[
  header:univ->univ,
  previous:univ->univ,
  thiz:univ
]{
   not (
     isEmptyOrNull[(thiz.header).previous]
     and 
     isEmptyOrNull[thiz.header]
     and 
     isEmptyOrNull[thiz]
   )

}

pred ApacheListCondition13[
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

pred ApacheListCondition9[
  header:univ->univ,
  thiz:univ
]{
   not (
     isEmptyOrNull[thiz.header]
     and 
     isEmptyOrNull[thiz]
   )

}

pred ApacheListCondition8[
  header:univ->univ,
  thiz:univ
]{
   isEmptyOrNull[thiz.header]
   and 
   isEmptyOrNull[thiz]

}

pred ApacheListCondition6[
  header:univ->univ,
  previous:univ->univ,
  thiz:univ
]{
   isEmptyOrNull[(thiz.header).previous]
   and 
   isEmptyOrNull[thiz.header]
   and 
   isEmptyOrNull[thiz]

}

pred ApacheListCondition14[
  header:univ->univ,
  myseq:univ->(seq univ),
  next:univ->univ,
  previous:univ->univ,
  thiz:univ
]{
   ApacheList_myseq_abstraction[header,
                               myseq,
                               next,
                               previous,
                               thiz]

}

pred postcondition_ApacheList_insertBack_0[
  freshNode:univ,
  header':univ->univ,
  myseq:univ->(seq univ),
  myseq':univ->(seq univ),
  next':univ->univ,
  previous':univ->univ,
  size':univ->univ,
  thiz:univ,
  thiz':univ,
  throw':univ
]{
   ApacheList_ensures[freshNode,
                     myseq,
                     myseq',
                     thiz,
                     thiz']
   and 
   ApacheList_invariant[header',
                       next',
                       previous',
                       size',
                       thiz']
   and 
   equ[throw',
      null]

}

pred ApacheListCondition2[
  freshNode:univ,
  thiz:univ
]{
   isEmptyOrNull[freshNode]
   and 
   isEmptyOrNull[thiz]

}

pred ApacheListCondition3[
  freshNode:univ,
  thiz:univ
]{
   not (
     isEmptyOrNull[freshNode]
     and 
     isEmptyOrNull[thiz]
   )

}

pred ApacheListCondition11[
  thiz:univ
]{
   not (
     isEmptyOrNull[thiz]
     and 
     isEmptyOrNull[thiz]
   )

}

pred ApacheListCondition10[
  thiz:univ
]{
   isEmptyOrNull[thiz]
   and 
   isEmptyOrNull[thiz]

}

pred ApacheList_requires[
  freshNode:univ,
  header:univ->univ,
  myseq:univ->(seq univ),
  thiz:univ
]{
   neq[freshNode,
      null]
   and 
   neq[thiz.header,
      freshNode]
   and 
   (
     all i:Int | {
       (
         gte[i,
            0]
         and 
         lt[i,
           fun_list_size[thiz.myseq]]
       )
       implies 
               neq[fun_list_get[thiz.myseq,i],
                  freshNode]
     
     }
   )

}

pred ApacheListCondition12[
  nullDerefBool:univ,
  throw:univ
]{
   equ[nullDerefBool,
      true]
   and 
   equ[throw,
      null]

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


pred ApacheList_insertBack_0[
  thiz_0: ApacheList,
  throw_1: Throwable + null,
  throw_2: Throwable + null,
  return_1: boolean,
  o_0: Data + null,
  freshNode_0: ApacheListNode + null,
  previous_0: ( ApacheListNode ) -> one ( ApacheListNode + null ),
  previous_1: ( ApacheListNode ) -> one ( ApacheListNode + null ),
  previous_2: ( ApacheListNode ) -> one ( ApacheListNode + null ),
  next_0: ( ApacheListNode ) -> one ( ApacheListNode + null ),
  next_1: ( ApacheListNode ) -> one ( ApacheListNode + null ),
  next_2: ( ApacheListNode ) -> one ( ApacheListNode + null ),
  nodeValue_0: ( ApacheListNode ) -> one ( Data + null ),
  nodeValue_1: ( ApacheListNode ) -> one ( Data + null ),
  modCount_0: ( ApacheList ) -> one ( Int ),
  modCount_1: ( ApacheList ) -> one ( Int ),
  size_0: ( ApacheList ) -> one ( Int ),
  size_1: ( ApacheList ) -> one ( Int ),
  header_0: ( ApacheList ) -> one ( ApacheListNode + null ),
  nullDerefBool_1: boolean,
  nullDerefBool_2: boolean,
  nullDerefBool_3: boolean,
  nullDerefBool_4: boolean,
  nullDerefBool_5: boolean,
  nullDerefBool_6: boolean,
  nullDerefBool_7: boolean,
  nullDerefBool_8: boolean
]{
  TruePred[]
  and 
  (
    nullDerefBool_1=false)
  and 
  (
    throw_1=null)
  and 
  (
    (
      ApacheListCondition0[freshNode_0]
      and 
      (
        nullDerefBool_2=true)
    )
    or 
    (
      (
        not (
          ApacheListCondition0[freshNode_0])
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
    nodeValue_1=(nodeValue_0)++((freshNode_0)->(o_0)))
  and 
  (
    (
      ApacheListCondition2[freshNode_0,
                          thiz_0]
      and 
      (
        nullDerefBool_3=true)
    )
    or 
    (
      (
        not (
          ApacheListCondition2[freshNode_0,
                              thiz_0]
        )
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
    next_1=(next_0)++((freshNode_0)->(thiz_0.header_0)))
  and 
  (
    (
      ApacheListCondition4[freshNode_0,
                          header_0,
                          thiz_0]
      and 
      (
        nullDerefBool_4=true)
    )
    or 
    (
      (
        not (
          ApacheListCondition4[freshNode_0,
                              header_0,
                              thiz_0]
        )
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
    previous_1=(previous_0)++((freshNode_0)->((thiz_0.header_0).previous_0)))
  and 
  (
    (
      ApacheListCondition6[header_0,
                          previous_1,
                          thiz_0]
      and 
      (
        nullDerefBool_5=true)
    )
    or 
    (
      (
        not (
          ApacheListCondition6[header_0,
                              previous_1,
                              thiz_0]
        )
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
    next_2=(next_1)++(((thiz_0.header_0).previous_1)->(freshNode_0)))
  and 
  (
    (
      ApacheListCondition8[header_0,
                          thiz_0]
      and 
      (
        nullDerefBool_6=true)
    )
    or 
    (
      (
        not (
          ApacheListCondition8[header_0,
                              thiz_0]
        )
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
    previous_2=(previous_1)++((thiz_0.header_0)->(freshNode_0)))
  and 
  (
    (
      ApacheListCondition10[thiz_0]
      and 
      (
        nullDerefBool_7=true)
    )
    or 
    (
      (
        not (
          ApacheListCondition10[thiz_0])
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
    size_1=(size_0)++((thiz_0)->(add[thiz_0.size_0,1])))
  and 
  (
    (
      ApacheListCondition10[thiz_0]
      and 
      (
        nullDerefBool_8=true)
    )
    or 
    (
      (
        not (
          ApacheListCondition10[thiz_0])
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
    modCount_1=(modCount_0)++((thiz_0)->(add[thiz_0.modCount_0,1])))
  and 
  (
    return_1=true)
  and 
  (
    (
      ApacheListCondition12[nullDerefBool_8,
                           throw_1]
      and 
      (
        throw_2=NullPointerExceptionLit)
    )
    or 
    (
      (
        not (
          ApacheListCondition12[nullDerefBool_8,
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
  freshNode_0: ApacheListNode + null,
  header_0: ( ApacheList ) -> one ( ApacheListNode + null ),
  l0_nullDerefBool_1: boolean,
  l0_nullDerefBool_2: boolean,
  l0_nullDerefBool_3: boolean,
  l0_nullDerefBool_4: boolean,
  l0_nullDerefBool_5: boolean,
  l0_nullDerefBool_6: boolean,
  l0_nullDerefBool_7: boolean,
  l0_nullDerefBool_8: boolean,
  modCount_0: ( ApacheList ) -> one ( Int ),
  modCount_1: ( ApacheList ) -> one ( Int ),
  myseq_0: ( ApacheList ) -> ( seq ( null + Object ) ),
  myseq_1: ( ApacheList ) -> ( seq ( null + Object ) ),
  bnext_0,fnext_0: ( ApacheListNode ) -> lone ( ApacheListNode + null ),
  next_1: ( ApacheListNode ) -> one ( ApacheListNode + null ),
  next_2: ( ApacheListNode ) -> one ( ApacheListNode + null ),
  nodeValue_0: ( ApacheListNode ) -> one ( Data + null ),
  nodeValue_1: ( ApacheListNode ) -> one ( Data + null ),
  o_0: Data + null,
  bprevious_0,fprevious_0: ( ApacheListNode ) -> lone ( ApacheListNode + null ),
  previous_1: ( ApacheListNode ) -> one ( ApacheListNode + null ),
  previous_2: ( ApacheListNode ) -> one ( ApacheListNode + null ),
  return_1: boolean,
  size_0: ( ApacheList ) -> one ( Int ),
  size_1: ( ApacheList ) -> one ( Int ),
  thiz_0: ApacheList,
  throw_1: Throwable + null,
  throw_2: Throwable + null
}


fact {
  precondition_ApacheList_insertBack_0[QF.freshNode_0,
                                      QF.header_0,
                                      QF.myseq_0,
                                      (QF.fnext_0+QF.bnext_0),
                                      (QF.fprevious_0+QF.bprevious_0),
                                      QF.size_0,
                                      QF.thiz_0]

}

fact {
  ApacheList_insertBack_0[QF.thiz_0,
                         QF.throw_1,
                         QF.throw_2,
                         QF.return_1,
                         QF.o_0,
                         QF.freshNode_0,
                         (QF.fprevious_0+QF.bprevious_0),
                         QF.previous_1,
                         QF.previous_2,
                         (QF.fnext_0+QF.bnext_0),
                         QF.next_1,
                         QF.next_2,
                         QF.nodeValue_0,
                         QF.nodeValue_1,
                         QF.modCount_0,
                         QF.modCount_1,
                         QF.size_0,
                         QF.size_1,
                         QF.header_0,
                         QF.l0_nullDerefBool_1,
                         QF.l0_nullDerefBool_2,
                         QF.l0_nullDerefBool_3,
                         QF.l0_nullDerefBool_4,
                         QF.l0_nullDerefBool_5,
                         QF.l0_nullDerefBool_6,
                         QF.l0_nullDerefBool_7,
                         QF.l0_nullDerefBool_8]

}

fact {
  havocVariable3[QF.myseq_1]
}

fact {
  ApacheListCondition14[QF.header_0,
                       QF.myseq_1,
                       QF.next_2,
                       QF.previous_2,
                       QF.thiz_0]

}

assert AList_m2{
  postcondition_ApacheList_insertBack_0[QF.freshNode_0,
                                       QF.header_0,
                                       QF.myseq_0,
                                       QF.myseq_1,
                                       QF.next_2,
                                       QF.previous_2,
                                       QF.size_1,
                                       QF.thiz_0,
                                       QF.thiz_0,
                                       QF.throw_2]
}
check AList_m2 for 0 but 
                 exactly 1 ApacheList, 
                 exactly 15 Data,
                 exactly 15 ApacheListNode,
                 15 seq, 
                 5 int  



one sig N0,N1,N2,N3,N4,N5,N6,N7,N8,N9,N10,N11,N12,N13,N14 extends ApacheListNode {}
one sig D0,D1,D2,D3,D4,D5,D6,D7,D8,D9,D10,D11,D12,D13,D14 extends Data {}

fun node_next[]: (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14) -> lone (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14)  
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
} 
fun node_prevs[e: N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14] :set (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14) 
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
 ) 
} 
fun data_prevs[e: D0+D1+D2+D3+D4+D5+D6+D7+D8+D9+D10+D11+D12+D13+D14] : set (D0+D1+D2+D3+D4+D5+D6+D7+D8+D9+D10+D11+D12+D13+D14) 
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
  ) 
} 
fun data_next[]: (D0+D1+D2+D3+D4+D5+D6+D7+D8+D9+D10+D11+D12+D13+D14) -> (D0+D1+D2+D3+D4+D5+D6+D7+D8+D9+D10+D11+D12+D13+D14) 
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
} 
pred data_lt[e1,e2: D0+D1+D2+D3+D4+D5+D6+D7+D8+D9+D10+D11+D12+D13+D14] { 
   e1 in data_prevs[e2] 
 } 
fun node_rprevs[e: N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14] :set (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14) 
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
 ) 
} 
fun node_relprevs[] :( N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14 ) -> set ( N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14 ) 
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
} 
fun node_min [es: set ( N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14 )] : lone ( N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14 ) 
{ 
  es - es.( 
   N0 -> ( N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14 ) 
   + 
   N1 -> ( N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14 ) 
   + 
   N2 -> ( N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14 ) 
   + 
   N3 -> ( N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14 ) 
   + 
   N4 -> ( N5+N6+N7+N8+N9+N10+N11+N12+N13+N14 ) 
   + 
   N5 -> ( N6+N7+N8+N9+N10+N11+N12+N13+N14 ) 
   + 
   N6 -> ( N7+N8+N9+N10+N11+N12+N13+N14 ) 
   + 
   N7 -> ( N8+N9+N10+N11+N12+N13+N14 ) 
   + 
   N8 -> ( N9+N10+N11+N12+N13+N14 ) 
   + 
   N9 -> ( N10+N11+N12+N13+N14 ) 
   + 
   N10 -> ( N11+N12+N13+N14 ) 
   + 
   N11 -> ( N12+N13+N14 ) 
   + 
   N12 -> ( N13+N14 ) 
   + 
   N13 -> ( N14 ) 
  ) 
} 
fact { 
let entry=(QF.thiz_0).(QF.header_0),ff1=QF.fnext_0,ff2=QF.fprevious_0,bf1=QF.bnext_0,bf2=QF.bprevious_0 | { 
   -- forwardPlusBackwardAreFunctions 
   no ((ff1.univ) & (bf1.univ)) 
   no ((ff2.univ) & (bf2.univ)) 
   N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14 = ff1.univ + bf1.univ   
   N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14 = ff2.univ + bf2.univ   

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
+N14->null 
 
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
+N13->null 
+N14->null 
 
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

} 
//fact root_node_fields 
fact { 
} 
