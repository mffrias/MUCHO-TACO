/* 
 * DynAlloy translator options 
 * --------------------------- 
 * applySimplifications= true
 * assertionId= CList_m1
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
  usedObjects1:set Object, 
  usedObjects0:set Object,
  n1: Object+null
]{ 
  n1 !in usedObjects0 
  usedObjects1 = usedObjects0 + (n1)
}
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





//-------------- java_lang_IndexOutOfBoundException--------------//
abstract sig IndexOutOfBoundsException extends RuntimeException {}
{}



one
sig IndexOutOfBoundsExceptionLit extends IndexOutOfBoundsException {}
{}


//-------------- amelia_jfsl_clist_CacheList--------------//
sig CacheList extends Object {}
{}




pred CacheListCondition0[
  throw:univ
]{
   equ[throw,
      null]

}

pred CacheListCondition1[
  throw:univ
]{
   not (
     equ[throw,
        null]
   )

}

pred CacheListCondition16[
  nullDerefBool:univ,
  throw:univ
]{
   equ[nullDerefBool,
      true]
   and 
   equ[throw,
      null]

}

pred CacheList_myseq_abstraction[
  listHeader:univ->univ,
  listNext:univ->univ,
  myseq:univ->(seq univ),
  thiz:univ
]{
   equ[#(thiz.myseq),
      #(fun_set_difference[fun_set_difference[(thiz.listHeader).(fun_reflexive_closure[listNext]),thiz.listHeader],null])]
   and 
   (
     neq[(thiz.listHeader).listNext,
        null]
     implies 
             (
               equ[(0).(thiz.myseq),
                  (thiz.listHeader).listNext]
               and 
               (
                 all j:Int | {
                   (
                     lte[0,
                        j]
                     and 
                     lt[j,
                       sub[#(thiz.myseq),1]]
                   )
                   implies 
                           equ[(add[j,1]).(thiz.myseq),
                              (j.(thiz.myseq)).listNext]
                 
                 }
               )
             )
   )

}

pred CacheList_ensures[
  data_value':univ,
  i:univ,
  myseq':univ->(seq univ),
  nodeValue':univ->univ,
  return':univ,
  thiz:univ,
  throw':univ
]{
   (
     some i:Int | {
       lte[0,
          i]
       and 
       lt[i,
         #(thiz.myseq')]
       and 
       equ[(i.(thiz.myseq')).nodeValue',
          data_value']
     
     }
     iff
     equ[return',
        true]
   )
   and 
   equ[throw',
      null]

}

pred CacheListCondition12[
  found:univ
]{
   equ[found,
      false]

}

pred CacheListCondition8[
  data_value:univ,
  node:univ,
  nodeValue:univ->univ
]{
   equ[node.nodeValue,
      data_value]

}

pred CacheListCondition9[
  data_value:univ,
  node:univ,
  nodeValue:univ->univ
]{
   not (
     equ[node.nodeValue,
        data_value]
   )

}

pred CacheListCondition13[
  found:univ
]{
   not (
     equ[found,
        false]
   )

}

pred CacheListCondition2[
  listHeader:univ->univ,
  thiz:univ
]{
   isEmptyOrNull[thiz.listHeader]
   and 
   isEmptyOrNull[thiz]

}

pred CacheList_object_invariant[
  DEFAULT_CACHE_SIZE:univ->univ,
  cacheHeader:univ->univ,
  cacheSize:univ->univ,
  listHeader:univ->univ,
  listNext:univ->univ,
  listPrevious:univ->univ,
  listSize:univ->univ,
  maximumCacheSize:univ->univ,
  nodeValue:univ->univ,
  thiz:univ
]{
   lte[thiz.cacheSize,
      thiz.maximumCacheSize]
   and 
   neq[thiz.listHeader,
      null]
   and 
   (
     all n:CacheListNode | {
       isSubset[n,
               fun_set_difference[(thiz.listHeader).(fun_reflexive_closure[listNext]),null]]
       implies 
               (
                 neq[n,
                    null]
                 and 
                 neq[n.listPrevious,
                    null]
                 and 
                 equ[(n.listPrevious).listNext,
                    n]
                 and 
                 neq[n.listNext,
                    null]
                 and 
                 equ[(n.listNext).listPrevious,
                    n]
               )
     
     }
   )
   and 
   (
     all m:CacheListNode | {
       isSubset[m,
               fun_set_difference[(thiz.cacheHeader).(fun_reflexive_closure[listNext]),null]]
       implies 
               (
                 isNotSubset[m,
                            fun_set_difference[(m.listNext).(fun_reflexive_closure[listNext]),null]]
                 and 
                 equ[m.listPrevious,
                    null]
                 and 
                 equ[m.nodeValue,
                    null]
               )
     
     }
   )
   and 
   equ[thiz.cacheSize,
      #(fun_set_difference[(thiz.cacheHeader).(fun_reflexive_closure[listNext]),null])]
   and 
   neq[(thiz.listHeader).listPrevious,
      null]
   and 
   equ[thiz.listSize,
      sub[#(fun_set_difference[(thiz.listHeader).(fun_reflexive_closure[listNext]),null]),1]]
   and 
   equ[thiz.DEFAULT_CACHE_SIZE,
      20]
   and 
   gte[thiz.listSize,
      0]
   and 
   neq[(thiz.listHeader).listNext,
      null]

}

pred CacheListCondition3[
  listHeader:univ->univ,
  thiz:univ
]{
   not (
     isEmptyOrNull[thiz.listHeader]
     and 
     isEmptyOrNull[thiz]
   )

}

pred CacheListCondition17[
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

pred precondition_CacheList_contains_0[
  DEFAULT_CACHE_SIZE:univ->univ,
  cacheHeader:univ->univ,
  cacheSize:univ->univ,
  listHeader:univ->univ,
  listNext:univ->univ,
  listPrevious:univ->univ,
  listSize:univ->univ,
  maximumCacheSize:univ->univ,
  myseq:univ->(seq univ),
  nodeValue:univ->univ,
  thiz:univ,
  throw:univ
]{
   CacheList_object_invariant[DEFAULT_CACHE_SIZE,
                             cacheHeader,
                             cacheSize,
                             listHeader,
                             listNext,
                             listPrevious,
                             listSize,
                             maximumCacheSize,
                             nodeValue,
                             thiz]
   and 
   equ[throw,
      null]
   and 
   CacheList_myseq_abstraction[listHeader,
                              listNext,
                              myseq,
                              thiz]

}

pred CacheListCondition15[
  index_ret:univ
]{
   not (
     neq[index_ret,
        negate[1]]
   )

}

pred CacheListCondition5[
  thiz:univ
]{
   not (
     isEmptyOrNull[thiz])

}

pred postcondition_CacheList_contains_0[
  data_value':univ,
  i:univ,
  myseq':univ->(seq univ),
  nodeValue':univ->univ,
  return':univ,
  thiz:univ,
  throw':univ
]{
   CacheList_ensures[data_value',
                    i,
                    myseq',
                    nodeValue',
                    return',
                    thiz,
                    throw']

}

pred CacheListCondition14[
  index_ret:univ
]{
   neq[index_ret,
      negate[1]]

}

pred CacheListCondition6[
  node:univ
]{
   isEmptyOrNull[node]

}

pred CacheListCondition7[
  node:univ
]{
   not (
     isEmptyOrNull[node])

}

pred CacheListCondition4[
  thiz:univ
]{
   isEmptyOrNull[thiz]

}

pred CacheListCondition11[
  found:univ,
  listHeader:univ->univ,
  node:univ,
  thiz:univ
]{
   not (
     neq[node,
        thiz.listHeader]
     and 
     equ[found,
        false]
   )

}

pred CacheListCondition10[
  found:univ,
  listHeader:univ->univ,
  node:univ,
  thiz:univ
]{
   neq[node,
      thiz.listHeader]
   and 
   equ[found,
      false]

}
//-------------- java_lang_NullPointerException--------------//
abstract sig NullPointerException extends RuntimeException {}
{}



one
sig NullPointerExceptionLit extends NullPointerException {}
{}


//-------------- amelia_jfsl_clist_CacheListNode--------------//
sig CacheListNode extends Object {}
{}





//-------------- amelia_jfsl_clist_Data--------------//
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


pred CacheList_contains_0[
  thiz_0: CacheList,
  throw_0: Throwable + null,
  throw_1: Throwable + null,
  throw_2: Throwable + null,
  return_0: boolean,
  return_1: boolean,
  data_value_0: Data + null,
  listHeader_0: ( CacheList ) -> one ( CacheListNode + null ),
  listNext_0: ( CacheListNode ) -> one ( CacheListNode + null ),
  nodeValue_0: ( CacheListNode ) -> one ( Data + null ),
  node_0: CacheListNode + null,
  node_1: CacheListNode + null,
  node_2: CacheListNode + null,
  node_3: CacheListNode + null,
  node_4: CacheListNode + null,
  node_5: CacheListNode + null,
  node_6: CacheListNode + null,
  node_7: CacheListNode + null,
  node_8: CacheListNode + null,
  node_9: CacheListNode + null,
  node_10: CacheListNode + null,
  node_11: CacheListNode + null,
  index_ret_0: Int,
  index_ret_1: Int,
  nullDerefBool_0: boolean,
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
  found_0: boolean,
  found_1: boolean,
  found_2: boolean,
  found_3: boolean,
  found_4: boolean,
  found_5: boolean,
  found_6: boolean,
  found_7: boolean,
  found_8: boolean,
  found_9: boolean,
  found_10: boolean,
  found_11: boolean,
  i_0: Int,
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
  i_11: Int,
  i_12: Int,
  ret_value_0: boolean,
  ret_value_1: boolean
]{
  TruePred[]
  and 
  (
    (
      CacheListCondition0[throw_0]
      and 
      (
        nullDerefBool_1=false)
    )
    or 
    (
      (
        not (
          CacheListCondition0[throw_0])
      )
      and 
      TruePred[]
      and 
      (
        nullDerefBool_0=nullDerefBool_1)
    )
  )
  and 
  (
    (
      CacheListCondition0[throw_0]
      and 
      (
        throw_1=null)
    )
    or 
    (
      (
        not (
          CacheListCondition0[throw_0])
      )
      and 
      TruePred[]
      and 
      (
        throw_0=throw_1)
    )
  )
  and 
  TruePred[]
  and 
  (
    (
      CacheListCondition0[throw_1]
      and 
      (
        i_1=0)
    )
    or 
    (
      (
        not (
          CacheListCondition0[throw_1])
      )
      and 
      TruePred[]
      and 
      (
        i_0=i_1)
    )
  )
  and 
  TruePred[]
  and 
  (
    (
      CacheListCondition2[listHeader_0,
                         thiz_0]
      and 
      (
        (
          CacheListCondition0[throw_1]
          and 
          (
            nullDerefBool_2=true)
        )
        or 
        (
          (
            not (
              CacheListCondition0[throw_1])
          )
          and 
          TruePred[]
          and 
          (
            nullDerefBool_1=nullDerefBool_2)
        )
      )
    )
    or 
    (
      (
        not (
          CacheListCondition2[listHeader_0,
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
    (
      CacheListCondition0[throw_1]
      and 
      (
        node_1=(thiz_0.listHeader_0).listNext_0)
    )
    or 
    (
      (
        not (
          CacheListCondition0[throw_1])
      )
      and 
      TruePred[]
      and 
      (
        node_0=node_1)
    )
  )
  and 
  TruePred[]
  and 
  (
    (
      CacheListCondition0[throw_1]
      and 
      (
        found_1=false)
    )
    or 
    (
      (
        not (
          CacheListCondition0[throw_1])
      )
      and 
      TruePred[]
      and 
      (
        found_0=found_1)
    )
  )
  and 
  (
    (
      CacheListCondition4[thiz_0]
      and 
      (
        (
          CacheListCondition0[throw_1]
          and 
          (
            nullDerefBool_3=true)
        )
        or 
        (
          (
            not (
              CacheListCondition0[throw_1])
          )
          and 
          TruePred[]
          and 
          (
            nullDerefBool_2=nullDerefBool_3)
        )
      )
    )
    or 
    (
      (
        not (
          CacheListCondition4[thiz_0])
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
      CacheListCondition0[throw_1]
      and 
      (
        (
          CacheListCondition10[found_1,
                              listHeader_0,
                              node_1,
                              thiz_0]
          and 
          (
            (
              CacheListCondition6[node_1]
              and 
              (
                (
                  CacheListCondition0[throw_1]
                  and 
                  (
                    nullDerefBool_4=true)
                )
                or 
                (
                  (
                    not (
                      CacheListCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_3=nullDerefBool_4)
                )
              )
            )
            or 
            (
              (
                not (
                  CacheListCondition6[node_1])
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
              CacheListCondition8[data_value_0,
                                 node_1,
                                 nodeValue_0]
              and 
              (
                (
                  CacheListCondition0[throw_1]
                  and 
                  (
                    found_2=true)
                )
                or 
                (
                  (
                    not (
                      CacheListCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    found_1=found_2)
                )
              )
              and 
              (
                nullDerefBool_4=nullDerefBool_5)
              and 
              (
                i_1=i_2)
              and 
              (
                node_1=node_2)
            )
            or 
            (
              (
                not (
                  CacheListCondition8[data_value_0,
                                     node_1,
                                     nodeValue_0]
                )
              )
              and 
              (
                (
                  CacheListCondition0[throw_1]
                  and 
                  (
                    i_2=add[i_1,1])
                )
                or 
                (
                  (
                    not (
                      CacheListCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    i_1=i_2)
                )
              )
              and 
              (
                (
                  CacheListCondition6[node_1]
                  and 
                  (
                    (
                      CacheListCondition0[throw_1]
                      and 
                      (
                        nullDerefBool_5=true)
                    )
                    or 
                    (
                      (
                        not (
                          CacheListCondition0[throw_1])
                      )
                      and 
                      TruePred[]
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
                      CacheListCondition6[node_1])
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
                  CacheListCondition0[throw_1]
                  and 
                  (
                    node_2=node_1.listNext_0)
                )
                or 
                (
                  (
                    not (
                      CacheListCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    node_1=node_2)
                )
              )
              and 
              (
                found_1=found_2)
            )
          )
        )
        or 
        (
          TruePred[]
          and 
          (
            node_1=node_2)
          and 
          (
            nullDerefBool_3=nullDerefBool_5)
          and 
          (
            i_1=i_2)
          and 
          (
            found_1=found_2)
        )
      )
      and 
      (
        (
          CacheListCondition10[found_2,
                              listHeader_0,
                              node_2,
                              thiz_0]
          and 
          (
            (
              CacheListCondition6[node_2]
              and 
              (
                (
                  CacheListCondition0[throw_1]
                  and 
                  (
                    nullDerefBool_6=true)
                )
                or 
                (
                  (
                    not (
                      CacheListCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_5=nullDerefBool_6)
                )
              )
            )
            or 
            (
              (
                not (
                  CacheListCondition6[node_2])
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
              CacheListCondition8[data_value_0,
                                 node_2,
                                 nodeValue_0]
              and 
              (
                (
                  CacheListCondition0[throw_1]
                  and 
                  (
                    found_3=true)
                )
                or 
                (
                  (
                    not (
                      CacheListCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    found_2=found_3)
                )
              )
              and 
              (
                nullDerefBool_6=nullDerefBool_7)
              and 
              (
                i_2=i_3)
              and 
              (
                node_2=node_3)
            )
            or 
            (
              (
                not (
                  CacheListCondition8[data_value_0,
                                     node_2,
                                     nodeValue_0]
                )
              )
              and 
              (
                (
                  CacheListCondition0[throw_1]
                  and 
                  (
                    i_3=add[i_2,1])
                )
                or 
                (
                  (
                    not (
                      CacheListCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    i_2=i_3)
                )
              )
              and 
              (
                (
                  CacheListCondition6[node_2]
                  and 
                  (
                    (
                      CacheListCondition0[throw_1]
                      and 
                      (
                        nullDerefBool_7=true)
                    )
                    or 
                    (
                      (
                        not (
                          CacheListCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_6=nullDerefBool_7)
                    )
                  )
                )
                or 
                (
                  (
                    not (
                      CacheListCondition6[node_2])
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
                  CacheListCondition0[throw_1]
                  and 
                  (
                    node_3=node_2.listNext_0)
                )
                or 
                (
                  (
                    not (
                      CacheListCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    node_2=node_3)
                )
              )
              and 
              (
                found_2=found_3)
            )
          )
        )
        or 
        (
          TruePred[]
          and 
          (
            node_2=node_3)
          and 
          (
            nullDerefBool_5=nullDerefBool_7)
          and 
          (
            i_2=i_3)
          and 
          (
            found_2=found_3)
        )
      )
      and 
      (
        (
          CacheListCondition10[found_3,
                              listHeader_0,
                              node_3,
                              thiz_0]
          and 
          (
            (
              CacheListCondition6[node_3]
              and 
              (
                (
                  CacheListCondition0[throw_1]
                  and 
                  (
                    nullDerefBool_8=true)
                )
                or 
                (
                  (
                    not (
                      CacheListCondition0[throw_1])
                  )
                  and 
                  TruePred[]
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
                  CacheListCondition6[node_3])
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
              CacheListCondition8[data_value_0,
                                 node_3,
                                 nodeValue_0]
              and 
              (
                (
                  CacheListCondition0[throw_1]
                  and 
                  (
                    found_4=true)
                )
                or 
                (
                  (
                    not (
                      CacheListCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    found_3=found_4)
                )
              )
              and 
              (
                nullDerefBool_8=nullDerefBool_9)
              and 
              (
                i_3=i_4)
              and 
              (
                node_3=node_4)
            )
            or 
            (
              (
                not (
                  CacheListCondition8[data_value_0,
                                     node_3,
                                     nodeValue_0]
                )
              )
              and 
              (
                (
                  CacheListCondition0[throw_1]
                  and 
                  (
                    i_4=add[i_3,1])
                )
                or 
                (
                  (
                    not (
                      CacheListCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    i_3=i_4)
                )
              )
              and 
              (
                (
                  CacheListCondition6[node_3]
                  and 
                  (
                    (
                      CacheListCondition0[throw_1]
                      and 
                      (
                        nullDerefBool_9=true)
                    )
                    or 
                    (
                      (
                        not (
                          CacheListCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_8=nullDerefBool_9)
                    )
                  )
                )
                or 
                (
                  (
                    not (
                      CacheListCondition6[node_3])
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
                  CacheListCondition0[throw_1]
                  and 
                  (
                    node_4=node_3.listNext_0)
                )
                or 
                (
                  (
                    not (
                      CacheListCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    node_3=node_4)
                )
              )
              and 
              (
                found_3=found_4)
            )
          )
        )
        or 
        (
          TruePred[]
          and 
          (
            node_3=node_4)
          and 
          (
            nullDerefBool_7=nullDerefBool_9)
          and 
          (
            i_3=i_4)
          and 
          (
            found_3=found_4)
        )
      )
      and 
      (
        (
          CacheListCondition10[found_4,
                              listHeader_0,
                              node_4,
                              thiz_0]
          and 
          (
            (
              CacheListCondition6[node_4]
              and 
              (
                (
                  CacheListCondition0[throw_1]
                  and 
                  (
                    nullDerefBool_10=true)
                )
                or 
                (
                  (
                    not (
                      CacheListCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_9=nullDerefBool_10)
                )
              )
            )
            or 
            (
              (
                not (
                  CacheListCondition6[node_4])
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
              CacheListCondition8[data_value_0,
                                 node_4,
                                 nodeValue_0]
              and 
              (
                (
                  CacheListCondition0[throw_1]
                  and 
                  (
                    found_5=true)
                )
                or 
                (
                  (
                    not (
                      CacheListCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    found_4=found_5)
                )
              )
              and 
              (
                nullDerefBool_10=nullDerefBool_11)
              and 
              (
                i_4=i_5)
              and 
              (
                node_4=node_5)
            )
            or 
            (
              (
                not (
                  CacheListCondition8[data_value_0,
                                     node_4,
                                     nodeValue_0]
                )
              )
              and 
              (
                (
                  CacheListCondition0[throw_1]
                  and 
                  (
                    i_5=add[i_4,1])
                )
                or 
                (
                  (
                    not (
                      CacheListCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    i_4=i_5)
                )
              )
              and 
              (
                (
                  CacheListCondition6[node_4]
                  and 
                  (
                    (
                      CacheListCondition0[throw_1]
                      and 
                      (
                        nullDerefBool_11=true)
                    )
                    or 
                    (
                      (
                        not (
                          CacheListCondition0[throw_1])
                      )
                      and 
                      TruePred[]
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
                      CacheListCondition6[node_4])
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
                  CacheListCondition0[throw_1]
                  and 
                  (
                    node_5=node_4.listNext_0)
                )
                or 
                (
                  (
                    not (
                      CacheListCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    node_4=node_5)
                )
              )
              and 
              (
                found_4=found_5)
            )
          )
        )
        or 
        (
          TruePred[]
          and 
          (
            node_4=node_5)
          and 
          (
            nullDerefBool_9=nullDerefBool_11)
          and 
          (
            i_4=i_5)
          and 
          (
            found_4=found_5)
        )
      )
      and 
      (
        (
          CacheListCondition10[found_5,
                              listHeader_0,
                              node_5,
                              thiz_0]
          and 
          (
            (
              CacheListCondition6[node_5]
              and 
              (
                (
                  CacheListCondition0[throw_1]
                  and 
                  (
                    nullDerefBool_12=true)
                )
                or 
                (
                  (
                    not (
                      CacheListCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_11=nullDerefBool_12)
                )
              )
            )
            or 
            (
              (
                not (
                  CacheListCondition6[node_5])
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
              CacheListCondition8[data_value_0,
                                 node_5,
                                 nodeValue_0]
              and 
              (
                (
                  CacheListCondition0[throw_1]
                  and 
                  (
                    found_6=true)
                )
                or 
                (
                  (
                    not (
                      CacheListCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    found_5=found_6)
                )
              )
              and 
              (
                nullDerefBool_12=nullDerefBool_13)
              and 
              (
                i_5=i_6)
              and 
              (
                node_5=node_6)
            )
            or 
            (
              (
                not (
                  CacheListCondition8[data_value_0,
                                     node_5,
                                     nodeValue_0]
                )
              )
              and 
              (
                (
                  CacheListCondition0[throw_1]
                  and 
                  (
                    i_6=add[i_5,1])
                )
                or 
                (
                  (
                    not (
                      CacheListCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    i_5=i_6)
                )
              )
              and 
              (
                (
                  CacheListCondition6[node_5]
                  and 
                  (
                    (
                      CacheListCondition0[throw_1]
                      and 
                      (
                        nullDerefBool_13=true)
                    )
                    or 
                    (
                      (
                        not (
                          CacheListCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_12=nullDerefBool_13)
                    )
                  )
                )
                or 
                (
                  (
                    not (
                      CacheListCondition6[node_5])
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
                  CacheListCondition0[throw_1]
                  and 
                  (
                    node_6=node_5.listNext_0)
                )
                or 
                (
                  (
                    not (
                      CacheListCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    node_5=node_6)
                )
              )
              and 
              (
                found_5=found_6)
            )
          )
        )
        or 
        (
          TruePred[]
          and 
          (
            node_5=node_6)
          and 
          (
            nullDerefBool_11=nullDerefBool_13)
          and 
          (
            i_5=i_6)
          and 
          (
            found_5=found_6)
        )
      )
      and 
      (
        (
          CacheListCondition10[found_6,
                              listHeader_0,
                              node_6,
                              thiz_0]
          and 
          (
            (
              CacheListCondition6[node_6]
              and 
              (
                (
                  CacheListCondition0[throw_1]
                  and 
                  (
                    nullDerefBool_14=true)
                )
                or 
                (
                  (
                    not (
                      CacheListCondition0[throw_1])
                  )
                  and 
                  TruePred[]
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
                  CacheListCondition6[node_6])
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
              CacheListCondition8[data_value_0,
                                 node_6,
                                 nodeValue_0]
              and 
              (
                (
                  CacheListCondition0[throw_1]
                  and 
                  (
                    found_7=true)
                )
                or 
                (
                  (
                    not (
                      CacheListCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    found_6=found_7)
                )
              )
              and 
              (
                nullDerefBool_14=nullDerefBool_15)
              and 
              (
                i_6=i_7)
              and 
              (
                node_6=node_7)
            )
            or 
            (
              (
                not (
                  CacheListCondition8[data_value_0,
                                     node_6,
                                     nodeValue_0]
                )
              )
              and 
              (
                (
                  CacheListCondition0[throw_1]
                  and 
                  (
                    i_7=add[i_6,1])
                )
                or 
                (
                  (
                    not (
                      CacheListCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    i_6=i_7)
                )
              )
              and 
              (
                (
                  CacheListCondition6[node_6]
                  and 
                  (
                    (
                      CacheListCondition0[throw_1]
                      and 
                      (
                        nullDerefBool_15=true)
                    )
                    or 
                    (
                      (
                        not (
                          CacheListCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_14=nullDerefBool_15)
                    )
                  )
                )
                or 
                (
                  (
                    not (
                      CacheListCondition6[node_6])
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
                  CacheListCondition0[throw_1]
                  and 
                  (
                    node_7=node_6.listNext_0)
                )
                or 
                (
                  (
                    not (
                      CacheListCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    node_6=node_7)
                )
              )
              and 
              (
                found_6=found_7)
            )
          )
        )
        or 
        (
          TruePred[]
          and 
          (
            node_6=node_7)
          and 
          (
            nullDerefBool_13=nullDerefBool_15)
          and 
          (
            i_6=i_7)
          and 
          (
            found_6=found_7)
        )
      )
      and 
      (
        (
          CacheListCondition10[found_7,
                              listHeader_0,
                              node_7,
                              thiz_0]
          and 
          (
            (
              CacheListCondition6[node_7]
              and 
              (
                (
                  CacheListCondition0[throw_1]
                  and 
                  (
                    nullDerefBool_16=true)
                )
                or 
                (
                  (
                    not (
                      CacheListCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_15=nullDerefBool_16)
                )
              )
            )
            or 
            (
              (
                not (
                  CacheListCondition6[node_7])
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
              CacheListCondition8[data_value_0,
                                 node_7,
                                 nodeValue_0]
              and 
              (
                (
                  CacheListCondition0[throw_1]
                  and 
                  (
                    found_8=true)
                )
                or 
                (
                  (
                    not (
                      CacheListCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    found_7=found_8)
                )
              )
              and 
              (
                nullDerefBool_16=nullDerefBool_17)
              and 
              (
                i_7=i_8)
              and 
              (
                node_7=node_8)
            )
            or 
            (
              (
                not (
                  CacheListCondition8[data_value_0,
                                     node_7,
                                     nodeValue_0]
                )
              )
              and 
              (
                (
                  CacheListCondition0[throw_1]
                  and 
                  (
                    i_8=add[i_7,1])
                )
                or 
                (
                  (
                    not (
                      CacheListCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    i_7=i_8)
                )
              )
              and 
              (
                (
                  CacheListCondition6[node_7]
                  and 
                  (
                    (
                      CacheListCondition0[throw_1]
                      and 
                      (
                        nullDerefBool_17=true)
                    )
                    or 
                    (
                      (
                        not (
                          CacheListCondition0[throw_1])
                      )
                      and 
                      TruePred[]
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
                      CacheListCondition6[node_7])
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
                  CacheListCondition0[throw_1]
                  and 
                  (
                    node_8=node_7.listNext_0)
                )
                or 
                (
                  (
                    not (
                      CacheListCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    node_7=node_8)
                )
              )
              and 
              (
                found_7=found_8)
            )
          )
        )
        or 
        (
          TruePred[]
          and 
          (
            node_7=node_8)
          and 
          (
            nullDerefBool_15=nullDerefBool_17)
          and 
          (
            i_7=i_8)
          and 
          (
            found_7=found_8)
        )
      )
      and 
      (
        (
          CacheListCondition10[found_8,
                              listHeader_0,
                              node_8,
                              thiz_0]
          and 
          (
            (
              CacheListCondition6[node_8]
              and 
              (
                (
                  CacheListCondition0[throw_1]
                  and 
                  (
                    nullDerefBool_18=true)
                )
                or 
                (
                  (
                    not (
                      CacheListCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_17=nullDerefBool_18)
                )
              )
            )
            or 
            (
              (
                not (
                  CacheListCondition6[node_8])
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
              CacheListCondition8[data_value_0,
                                 node_8,
                                 nodeValue_0]
              and 
              (
                (
                  CacheListCondition0[throw_1]
                  and 
                  (
                    found_9=true)
                )
                or 
                (
                  (
                    not (
                      CacheListCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    found_8=found_9)
                )
              )
              and 
              (
                nullDerefBool_18=nullDerefBool_19)
              and 
              (
                i_8=i_9)
              and 
              (
                node_8=node_9)
            )
            or 
            (
              (
                not (
                  CacheListCondition8[data_value_0,
                                     node_8,
                                     nodeValue_0]
                )
              )
              and 
              (
                (
                  CacheListCondition0[throw_1]
                  and 
                  (
                    i_9=add[i_8,1])
                )
                or 
                (
                  (
                    not (
                      CacheListCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    i_8=i_9)
                )
              )
              and 
              (
                (
                  CacheListCondition6[node_8]
                  and 
                  (
                    (
                      CacheListCondition0[throw_1]
                      and 
                      (
                        nullDerefBool_19=true)
                    )
                    or 
                    (
                      (
                        not (
                          CacheListCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_18=nullDerefBool_19)
                    )
                  )
                )
                or 
                (
                  (
                    not (
                      CacheListCondition6[node_8])
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
                  CacheListCondition0[throw_1]
                  and 
                  (
                    node_9=node_8.listNext_0)
                )
                or 
                (
                  (
                    not (
                      CacheListCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    node_8=node_9)
                )
              )
              and 
              (
                found_8=found_9)
            )
          )
        )
        or 
        (
          TruePred[]
          and 
          (
            node_8=node_9)
          and 
          (
            nullDerefBool_17=nullDerefBool_19)
          and 
          (
            i_8=i_9)
          and 
          (
            found_8=found_9)
        )
      )
      and 
      (
        (
          CacheListCondition10[found_9,
                              listHeader_0,
                              node_9,
                              thiz_0]
          and 
          (
            (
              CacheListCondition6[node_9]
              and 
              (
                (
                  CacheListCondition0[throw_1]
                  and 
                  (
                    nullDerefBool_20=true)
                )
                or 
                (
                  (
                    not (
                      CacheListCondition0[throw_1])
                  )
                  and 
                  TruePred[]
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
                  CacheListCondition6[node_9])
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
              CacheListCondition8[data_value_0,
                                 node_9,
                                 nodeValue_0]
              and 
              (
                (
                  CacheListCondition0[throw_1]
                  and 
                  (
                    found_10=true)
                )
                or 
                (
                  (
                    not (
                      CacheListCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    found_9=found_10)
                )
              )
              and 
              (
                nullDerefBool_20=nullDerefBool_21)
              and 
              (
                i_9=i_10)
              and 
              (
                node_9=node_10)
            )
            or 
            (
              (
                not (
                  CacheListCondition8[data_value_0,
                                     node_9,
                                     nodeValue_0]
                )
              )
              and 
              (
                (
                  CacheListCondition0[throw_1]
                  and 
                  (
                    i_10=add[i_9,1])
                )
                or 
                (
                  (
                    not (
                      CacheListCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    i_9=i_10)
                )
              )
              and 
              (
                (
                  CacheListCondition6[node_9]
                  and 
                  (
                    (
                      CacheListCondition0[throw_1]
                      and 
                      (
                        nullDerefBool_21=true)
                    )
                    or 
                    (
                      (
                        not (
                          CacheListCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_20=nullDerefBool_21)
                    )
                  )
                )
                or 
                (
                  (
                    not (
                      CacheListCondition6[node_9])
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
                  CacheListCondition0[throw_1]
                  and 
                  (
                    node_10=node_9.listNext_0)
                )
                or 
                (
                  (
                    not (
                      CacheListCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    node_9=node_10)
                )
              )
              and 
              (
                found_9=found_10)
            )
          )
        )
        or 
        (
          TruePred[]
          and 
          (
            node_9=node_10)
          and 
          (
            nullDerefBool_19=nullDerefBool_21)
          and 
          (
            i_9=i_10)
          and 
          (
            found_9=found_10)
        )
      )
      and 
      (
        (
          CacheListCondition10[found_10,
                              listHeader_0,
                              node_10,
                              thiz_0]
          and 
          (
            (
              CacheListCondition6[node_10]
              and 
              (
                (
                  CacheListCondition0[throw_1]
                  and 
                  (
                    nullDerefBool_22=true)
                )
                or 
                (
                  (
                    not (
                      CacheListCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_21=nullDerefBool_22)
                )
              )
            )
            or 
            (
              (
                not (
                  CacheListCondition6[node_10])
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
              CacheListCondition8[data_value_0,
                                 node_10,
                                 nodeValue_0]
              and 
              (
                (
                  CacheListCondition0[throw_1]
                  and 
                  (
                    found_11=true)
                )
                or 
                (
                  (
                    not (
                      CacheListCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    found_10=found_11)
                )
              )
              and 
              (
                nullDerefBool_22=nullDerefBool_23)
              and 
              (
                i_10=i_11)
              and 
              (
                node_10=node_11)
            )
            or 
            (
              (
                not (
                  CacheListCondition8[data_value_0,
                                     node_10,
                                     nodeValue_0]
                )
              )
              and 
              (
                (
                  CacheListCondition0[throw_1]
                  and 
                  (
                    i_11=add[i_10,1])
                )
                or 
                (
                  (
                    not (
                      CacheListCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    i_10=i_11)
                )
              )
              and 
              (
                (
                  CacheListCondition6[node_10]
                  and 
                  (
                    (
                      CacheListCondition0[throw_1]
                      and 
                      (
                        nullDerefBool_23=true)
                    )
                    or 
                    (
                      (
                        not (
                          CacheListCondition0[throw_1])
                      )
                      and 
                      TruePred[]
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
                      CacheListCondition6[node_10])
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
                  CacheListCondition0[throw_1]
                  and 
                  (
                    node_11=node_10.listNext_0)
                )
                or 
                (
                  (
                    not (
                      CacheListCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    node_10=node_11)
                )
              )
              and 
              (
                found_10=found_11)
            )
          )
        )
        or 
        (
          TruePred[]
          and 
          (
            node_10=node_11)
          and 
          (
            nullDerefBool_21=nullDerefBool_23)
          and 
          (
            i_10=i_11)
          and 
          (
            found_10=found_11)
        )
      )
      and 
      CacheListCondition11[found_11,
                          listHeader_0,
                          node_11,
                          thiz_0]
    )
    or 
    (
      (
        not (
          CacheListCondition0[throw_1])
      )
      and 
      TruePred[]
      and 
      (
        node_1=node_11)
      and 
      (
        nullDerefBool_3=nullDerefBool_23)
      and 
      (
        i_1=i_11)
      and 
      (
        found_1=found_11)
    )
  )
  and 
  (
    (
      CacheListCondition12[found_11]
      and 
      (
        (
          CacheListCondition0[throw_1]
          and 
          (
            i_12=negate[1])
        )
        or 
        (
          (
            not (
              CacheListCondition0[throw_1])
          )
          and 
          TruePred[]
          and 
          (
            i_11=i_12)
        )
      )
    )
    or 
    (
      (
        not (
          CacheListCondition12[found_11])
      )
      and 
      TruePred[]
      and 
      (
        i_11=i_12)
    )
  )
  and 
  TruePred[]
  and 
  (
    (
      CacheListCondition0[throw_1]
      and 
      (
        index_ret_1=i_12)
    )
    or 
    (
      (
        not (
          CacheListCondition0[throw_1])
      )
      and 
      TruePred[]
      and 
      (
        index_ret_0=index_ret_1)
    )
  )
  and 
  TruePred[]
  and 
  (
    (
      CacheListCondition14[index_ret_1]
      and 
      (
        (
          CacheListCondition0[throw_1]
          and 
          (
            ret_value_1=true)
        )
        or 
        (
          (
            not (
              CacheListCondition0[throw_1])
          )
          and 
          TruePred[]
          and 
          (
            ret_value_0=ret_value_1)
        )
      )
    )
    or 
    (
      (
        not (
          CacheListCondition14[index_ret_1])
      )
      and 
      (
        (
          CacheListCondition0[throw_1]
          and 
          (
            ret_value_1=false)
        )
        or 
        (
          (
            not (
              CacheListCondition0[throw_1])
          )
          and 
          TruePred[]
          and 
          (
            ret_value_0=ret_value_1)
        )
      )
    )
  )
  and 
  (
    (
      CacheListCondition0[throw_1]
      and 
      (
        return_1=ret_value_1)
    )
    or 
    (
      (
        not (
          CacheListCondition0[throw_1])
      )
      and 
      TruePred[]
      and 
      (
        return_0=return_1)
    )
  )
  and 
  (
    (
      CacheListCondition16[nullDerefBool_23,
                          throw_1]
      and 
      (
        (
          CacheListCondition0[throw_1]
          and 
          (
            throw_2=NullPointerExceptionLit)
        )
        or 
        (
          (
            not (
              CacheListCondition0[throw_1])
          )
          and 
          TruePred[]
          and 
          (
            throw_1=throw_2)
        )
      )
    )
    or 
    (
      (
        not (
          CacheListCondition16[nullDerefBool_23,
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
  DEFAULT_CACHE_SIZE_0: ( CacheList ) -> one ( Int ),
  cacheHeader_0: ( CacheList ) -> one ( CacheListNode + null ),
  cacheSize_0: ( CacheList ) -> one ( Int ),
  data_value_0: Data + null,
  i_0: Int,
  l0_found_0: boolean,
  l0_found_1: boolean,
  l0_found_10: boolean,
  l0_found_11: boolean,
  l0_found_2: boolean,
  l0_found_3: boolean,
  l0_found_4: boolean,
  l0_found_5: boolean,
  l0_found_6: boolean,
  l0_found_7: boolean,
  l0_found_8: boolean,
  l0_found_9: boolean,
  l0_i_0: Int,
  l0_i_1: Int,
  l0_i_10: Int,
  l0_i_11: Int,
  l0_i_12: Int,
  l0_i_2: Int,
  l0_i_3: Int,
  l0_i_4: Int,
  l0_i_5: Int,
  l0_i_6: Int,
  l0_i_7: Int,
  l0_i_8: Int,
  l0_i_9: Int,
  l0_index_ret_0: Int,
  l0_index_ret_1: Int,
  l0_node_0: CacheListNode + null,
  l0_node_1: CacheListNode + null,
  l0_node_10: CacheListNode + null,
  l0_node_11: CacheListNode + null,
  l0_node_2: CacheListNode + null,
  l0_node_3: CacheListNode + null,
  l0_node_4: CacheListNode + null,
  l0_node_5: CacheListNode + null,
  l0_node_6: CacheListNode + null,
  l0_node_7: CacheListNode + null,
  l0_node_8: CacheListNode + null,
  l0_node_9: CacheListNode + null,
  l0_nullDerefBool_0: boolean,
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
  l0_ret_value_0: boolean,
  l0_ret_value_1: boolean,
  listHeader_0: ( CacheList ) -> one ( CacheListNode + null ),
  blistNext_0,flistNext_0: ( CacheListNode ) -> lone ( CacheListNode + null ),
  blistPrevious_0,flistPrevious_0: ( CacheListNode ) -> lone ( CacheListNode + null ),
  listSize_0: ( CacheList ) -> one ( Int ),
  maximumCacheSize_0: ( CacheList ) -> one ( Int ),
  myseq_0: ( CacheList ) -> ( seq ( CacheListNode ) ),
  nodeValue_0: ( CacheListNode ) -> one ( Data + null ),
  return_0: boolean,
  return_1: boolean,
  thiz_0: CacheList,
  throw_0: Throwable + null,
  throw_1: Throwable + null,
  throw_2: Throwable + null
}


fact {
  precondition_CacheList_contains_0[QF.DEFAULT_CACHE_SIZE_0,
                                   QF.cacheHeader_0,
                                   QF.cacheSize_0,
                                   QF.listHeader_0,
                                   (QF.flistNext_0+QF.blistNext_0),
                                   (QF.flistPrevious_0+QF.blistPrevious_0),
                                   QF.listSize_0,
                                   QF.maximumCacheSize_0,
                                   QF.myseq_0,
                                   QF.nodeValue_0,
                                   QF.thiz_0,
                                   QF.throw_0]

}

fact {
  CacheList_contains_0[QF.thiz_0,
                      QF.throw_0,
                      QF.throw_1,
                      QF.throw_2,
                      QF.return_0,
                      QF.return_1,
                      QF.data_value_0,
                      QF.listHeader_0,
                      (QF.flistNext_0+QF.blistNext_0),
                      QF.nodeValue_0,
                      QF.l0_node_0,
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
                      QF.l0_index_ret_0,
                      QF.l0_index_ret_1,
                      QF.l0_nullDerefBool_0,
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
                      QF.l0_found_0,
                      QF.l0_found_1,
                      QF.l0_found_2,
                      QF.l0_found_3,
                      QF.l0_found_4,
                      QF.l0_found_5,
                      QF.l0_found_6,
                      QF.l0_found_7,
                      QF.l0_found_8,
                      QF.l0_found_9,
                      QF.l0_found_10,
                      QF.l0_found_11,
                      QF.l0_i_0,
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
                      QF.l0_i_11,
                      QF.l0_i_12,
                      QF.l0_ret_value_0,
                      QF.l0_ret_value_1]

}

assert CList_m1{
  postcondition_CacheList_contains_0[QF.data_value_0,
                                    QF.i_0,
                                    QF.myseq_0,
                                    QF.nodeValue_0,
                                    QF.return_1,
                                    QF.thiz_0,
                                    QF.throw_2]
}
check CList_m1 for 0 but 
                 exactly 1 CacheList, 
                 exactly 15 Data,
                 exactly 15 CacheListNode,
                 15 seq, 
                 6 int  


one sig CL0 extends CacheList {}
one sig N0,N1,N2,N3,N4,N5,N6,N7,N8,N9,N10,N11,N12,N13,N14 extends CacheListNode {}
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
let entry=(CL0.(QF.listHeader_0+QF.cacheHeader_0)),ff1=QF.flistNext_0,ff2=QF.flistPrevious_0,bf1=QF.blistNext_0,bf2=QF.blistPrevious_0 | { 
   -- forwardPlusBackwardAreFunctions 
   no ((ff1.univ) & (bf1.univ)) 
   no ((ff2.univ) & (bf2.univ)) 
   N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14 = ff1.univ + bf1.univ   
   N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14 = ff2.univ + bf2.univ   

  --forwardIsIndeedForward 
  entry in N0+N1+null and 
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
QF.blistNext_0 in N0->N0 
+N1->N0 
+N1->N1 
+N2->N0 
+N2->N1 
+N3->N0 
+N3->N1 
+N3->N2 
+N4->N1 
+N4->N2 
+N4->N3 
+N5->N3 
+N5->N4 
+N6->N3 
+N6->N4 
+N6->N5 
+N7->N4 
+N7->N5 
+N7->N6 
+N8->N6 
+N8->N7 
+N9->N6 
+N9->N7 
+N9->N8 
+N10->N7 
+N10->N8 
+N10->N9 
+N11->N9 
+N11->N10 
+N12->N9 
+N12->N10 
+N12->N11 
+N13->N10 
+N13->N11 
+N13->N12 
+N14->N12 
+N14->N13 
 
QF.blistPrevious_0 in N0->N0 
+N1->N0 
+N1->N1 
+N2->N0 
+N2->N1 
+N3->N1 
+N3->N2 
+N4->N2 
+N4->N3 
+N5->N2 
+N5->N3 
+N5->N4 
+N6->N3 
+N6->N4 
+N6->N5 
+N7->N5 
+N7->N6 
+N8->N5 
+N8->N6 
+N8->N7 
+N9->N6 
+N9->N7 
+N9->N8 
+N10->N8 
+N10->N9 
+N11->N8 
+N11->N9 
+N11->N10 
+N12->N9 
+N12->N10 
+N12->N11 
+N13->N11 
+N13->N12 
+N14->N11 
+N14->N12 
+N14->N13 
 
QF.flistPrevious_0 in N0->N1 
+N0->N2 
+N0->N3 
+N0->null 
+N1->N2 
+N1->N3 
+N1->N4 
+N1->null 
+N2->N3 
+N2->N4 
+N2->null 
+N3->N4 
+N3->N5 
+N3->N6 
+N3->null 
+N4->N5 
+N4->N6 
+N4->N7 
+N4->null 
+N5->N6 
+N5->N7 
+N5->null 
+N6->N7 
+N6->N8 
+N6->N9 
+N6->null 
+N7->N8 
+N7->N9 
+N7->N10 
+N7->null 
+N8->N9 
+N8->N10 
+N8->null 
+N9->N10 
+N9->N11 
+N9->N12 
+N9->null 
+N10->N11 
+N10->N12 
+N10->N13 
+N10->null 
+N11->N12 
+N11->N13 
+N11->null 
+N12->N13 
+N12->N14 
+N12->null 
+N13->N14 
+N13->null 
+N14->null 
 
QF.flistNext_0 in N0->N1 
+N0->N2 
+N0->null 
+N1->N2 
+N1->N3 
+N1->N4 
+N1->null 
+N2->N3 
+N2->N4 
+N2->N5 
+N2->null 
+N3->N4 
+N3->N5 
+N3->N6 
+N3->null 
+N4->N5 
+N4->N6 
+N4->N7 
+N4->null 
+N5->N6 
+N5->N7 
+N5->N8 
+N5->null 
+N6->N7 
+N6->N8 
+N6->N9 
+N6->null 
+N7->N8 
+N7->N9 
+N7->N10 
+N7->null 
+N8->N9 
+N8->N10 
+N8->N11 
+N8->null 
+N9->N10 
+N9->N11 
+N9->N12 
+N9->null 
+N10->N11 
+N10->N12 
+N10->N13 
+N10->null 
+N11->N12 
+N11->N13 
+N11->N14 
+N11->null 
+N12->N13 
+N12->N14 
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
(QF.listSize_0) in CL0->0 
+CL0->1 
+CL0->2 
+CL0->3 
+CL0->4 
+CL0->5 
+CL0->6 
+CL0->7 
+CL0->8 
+CL0->9 
+CL0->10 
+CL0->11 
+CL0->12 
+CL0->13 
+CL0->14 

(QF.cacheSize_0) in CL0->0 
+CL0->1 
+CL0->2 
+CL0->3 
+CL0->4 
+CL0->5 
+CL0->6 
+CL0->7 
+CL0->8 
+CL0->9 
+CL0->10 
+CL0->11 
+CL0->12 
+CL0->13 
+CL0->14 

(QF.maximumCacheSize_0) in CL0->0 
+CL0->1 
+CL0->2 
+CL0->3 
+CL0->4 
+CL0->5 
+CL0->6 
+CL0->7 
+CL0->8 
+CL0->9 
+CL0->10 
+CL0->11 
+CL0->12 
+CL0->13 
+CL0->14 
+CL0->15 
+CL0->16 
+CL0->17 
+CL0->18 
+CL0->19 
+CL0->20 
+CL0->21 
+CL0->22 
+CL0->23 
+CL0->24 
+CL0->25 
+CL0->26 
+CL0->27 
+CL0->28 
+CL0->29 
+CL0->30 
+CL0->31 

(QF.DEFAULT_CACHE_SIZE_0) in CL0->0 
+CL0->20 

} 
//fact root_node_fields 
fact { 
(QF.listHeader_0) in CL0->N0 
+CL0->N1 
+CL0->null 

(QF.cacheHeader_0) in CL0->N0 
+CL0->N1 
+CL0->null 

} 
