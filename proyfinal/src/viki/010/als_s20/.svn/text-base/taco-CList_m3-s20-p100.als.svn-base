/* 
 * DynAlloy translator options 
 * --------------------------- 
 * applySimplifications= true
 * assertionId= CList_m3
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




pred CacheListCondition12[
  node1:univ
]{
   isEmptyOrNull[node1]

}

pred CacheListCondition13[
  node1:univ
]{
   not (
     isEmptyOrNull[node1])

}

pred CacheListCondition30[
  nullDerefBool:univ,
  throw:univ
]{
   equ[nullDerefBool,
      true]
   and 
   equ[throw,
      null]

}

pred CacheListCondition10[
  listHeader:univ->univ,
  thiz:univ
]{
   isEmptyOrNull[thiz.listHeader]
   and 
   isEmptyOrNull[thiz]

}

pred CacheListCondition18[
  index:univ,
  listSize:univ->univ,
  thiz:univ
]{
   lt[index,
     div[thiz.listSize,2]]

}

pred CacheListCondition11[
  listHeader:univ->univ,
  thiz:univ
]{
   not (
     isEmptyOrNull[thiz.listHeader]
     and 
     isEmptyOrNull[thiz]
   )

}

pred precondition_CacheList_remove_0[
  DEFAULT_CACHE_SIZE:univ->univ,
  cacheHeader:univ->univ,
  cacheSize:univ->univ,
  index:univ,
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
   CacheList_requires[index,
                     listSize,
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

pred CacheListCondition19[
  index:univ,
  listSize:univ->univ,
  thiz:univ
]{
   not (
     lt[index,
       div[thiz.listSize,2]]
   )

}

pred CacheListCondition31[
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

pred CacheListCondition17[
  currentIndex:univ,
  index:univ
]{
   not (
     gt[currentIndex,
       index]
   )

}

pred CacheListCondition15[
  currentIndex:univ,
  index:univ
]{
   not (
     lt[currentIndex,
       index]
   )

}

pred CacheListCondition16[
  currentIndex:univ,
  index:univ
]{
   gt[currentIndex,
     index]

}

pred CacheListCondition14[
  currentIndex:univ,
  index:univ
]{
   lt[currentIndex,
     index]

}

pred CacheListCondition6[
  index:univ,
  listSize:univ->univ,
  thiz:univ
]{
   equ[false,
      false]
   and 
   equ[index,
      thiz.listSize]

}

pred CacheListCondition7[
  index:univ,
  listSize:univ->univ,
  thiz:univ
]{
   not (
     equ[false,
        false]
     and 
     equ[index,
        thiz.listSize]
   )

}

pred CacheListCondition3[
  index:univ
]{
   not (
     lt[index,
       0]
   )

}

pred CacheListCondition20[
  node:univ
]{
   isEmptyOrNull[node]

}

pred CacheListCondition2[
  index:univ
]{
   lt[index,
     0]

}

pred CacheListCondition21[
  node:univ
]{
   not (
     isEmptyOrNull[node])

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
   equ[thiz.cacheSize,
      #(fun_set_difference[(thiz.cacheHeader).(fun_reflexive_closure[listNext]),null])]
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
   neq[(thiz.listHeader).listPrevious,
      null]
   and 
   equ[thiz.DEFAULT_CACHE_SIZE,
      20]
   and 
   gte[thiz.listSize,
      0]
   and 
   equ[thiz.listSize,
      sub[#(fun_set_difference[(thiz.listHeader).(fun_reflexive_closure[listNext]),null]),1]]
   and 
   neq[(thiz.listHeader).listNext,
      null]

}

pred CacheListCondition0[
  throw:univ
]{
   equ[throw,
      null]

}

pred CacheListCondition9[
  index:univ,
  listSize:univ->univ,
  thiz:univ
]{
   not (
     gt[index,
       thiz.listSize]
   )

}

pred CacheListCondition1[
  throw:univ
]{
   not (
     equ[throw,
        null]
   )

}

pred CacheListCondition8[
  index:univ,
  listSize:univ->univ,
  thiz:univ
]{
   gt[index,
     thiz.listSize]

}

pred CacheListCondition24[
  listNext:univ->univ,
  node:univ
]{
   isEmptyOrNull[node.listNext]
   and 
   isEmptyOrNull[node]
   and 
   isEmptyOrNull[node]

}

pred CacheListCondition22[
  listPrevious:univ->univ,
  node:univ
]{
   isEmptyOrNull[node.listPrevious]
   and 
   isEmptyOrNull[node]
   and 
   isEmptyOrNull[node]

}

pred CacheListCondition27[
  thiz:univ
]{
   not (
     isEmptyOrNull[thiz]
     and 
     isEmptyOrNull[thiz]
   )

}

pred CacheListCondition23[
  listPrevious:univ->univ,
  node:univ
]{
   not (
     isEmptyOrNull[node.listPrevious]
     and 
     isEmptyOrNull[node]
     and 
     isEmptyOrNull[node]
   )

}

pred CacheListCondition26[
  thiz:univ
]{
   isEmptyOrNull[thiz]
   and 
   isEmptyOrNull[thiz]

}

pred CacheList_ensures[
  index:univ,
  index':univ,
  listSize:univ->univ,
  myseq:univ->(seq univ),
  myseq':univ->(seq univ),
  thiz:univ,
  throw':univ
]{
   (
     (
       gte[index,
          0]
       and 
       lt[index,
         thiz.listSize]
     )
     implies 
             (
               equ[#(thiz.myseq'),
                  sub[#(thiz.myseq),1]]
               and 
               (
                 all i:Int | {
                   (
                     lte[0,
                        i]
                     and 
                     lt[i,
                       #(thiz.myseq')]
                   )
                   implies 
                           (
                             (
                               lt[i,
                                 index']
                               implies 
                                       equ[i.(thiz.myseq'),
                                          i.(thiz.myseq)]
                             )
                             and 
                             (
                               gte[i,
                                  index']
                               implies 
                                       equ[i.(thiz.myseq'),
                                          (add[i,1]).(thiz.myseq)]
                             )
                           )
                 
                 }
               )
               and 
               equ[throw',
                  null]
             )
   )
   and 
   (
     (
       lt[index,
         0]
       or 
       gte[index,
          thiz.listSize]
     )
     implies 
             isSubset[throw',
                     IndexOutOfBoundsException ]
   )

}

pred CacheListCondition25[
  listNext:univ->univ,
  node:univ
]{
   not (
     isEmptyOrNull[node.listNext]
     and 
     isEmptyOrNull[node]
     and 
     isEmptyOrNull[node]
   )

}

pred CacheListCondition5[
  thiz:univ
]{
   not (
     isEmptyOrNull[thiz])

}

pred CacheList_requires[
  index:univ,
  listSize:univ->univ,
  thiz:univ
]{
   (
     gte[index,
        0]
     and 
     lt[index,
       thiz.listSize]
   )
   or 
   lt[index,
     0]
   or 
   gte[index,
      thiz.listSize]

}

pred postcondition_CacheList_remove_0[
  DEFAULT_CACHE_SIZE':univ->univ,
  cacheHeader':univ->univ,
  cacheSize':univ->univ,
  index:univ,
  index':univ,
  listHeader':univ->univ,
  listNext':univ->univ,
  listPrevious':univ->univ,
  listSize:univ->univ,
  listSize':univ->univ,
  maximumCacheSize':univ->univ,
  myseq:univ->(seq univ),
  myseq':univ->(seq univ),
  nodeValue':univ->univ,
  thiz:univ,
  thiz':univ,
  throw':univ
]{
   CacheList_ensures[index,
                    index',
                    listSize,
                    myseq,
                    myseq',
                    thiz,
                    throw']
   and 
   CacheList_object_invariant[DEFAULT_CACHE_SIZE',
                             cacheHeader',
                             cacheSize',
                             listHeader',
                             listNext',
                             listPrevious',
                             listSize',
                             maximumCacheSize',
                             nodeValue',
                             thiz']

}

pred CacheListCondition32[
  listHeader:univ->univ,
  listNext:univ->univ,
  myseq:univ->(seq univ),
  thiz:univ
]{
   CacheList_myseq_abstraction[listHeader,
                              listNext,
                              myseq,
                              thiz]

}

pred CacheListCondition4[
  thiz:univ
]{
   isEmptyOrNull[thiz]

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

pred CacheListCondition28[
  cacheSize:univ->univ,
  maximumCacheSize:univ->univ,
  thiz:univ
]{
   lt[thiz.cacheSize,
     thiz.maximumCacheSize]

}

pred CacheListCondition29[
  cacheSize:univ->univ,
  maximumCacheSize:univ->univ,
  thiz:univ
]{
   not (
     lt[thiz.cacheSize,
       thiz.maximumCacheSize]
   )

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


pred CacheList_remove_0[
  thiz_0: CacheList,
  throw_0: Throwable + null,
  throw_1: Throwable + null,
  throw_2: Throwable + null,
  throw_3: Throwable + null,
  throw_4: Throwable + null,
  throw_5: Throwable + null,
  return_0: Object + null,
  return_1: Object + null,
  index_0: Int,
  listPrevious_0: ( CacheListNode ) -> one ( CacheListNode + null ),
  listPrevious_1: ( CacheListNode ) -> one ( CacheListNode + null ),
  listPrevious_2: ( CacheListNode ) -> one ( CacheListNode + null ),
  listHeader_0: ( CacheList ) -> one ( CacheListNode + null ),
  listNext_0: ( CacheListNode ) -> one ( CacheListNode + null ),
  listNext_1: ( CacheListNode ) -> one ( CacheListNode + null ),
  listNext_2: ( CacheListNode ) -> one ( CacheListNode + null ),
  maximumCacheSize_0: ( CacheList ) -> one ( Int ),
  nodeValue_0: ( CacheListNode ) -> one ( Data + null ),
  nodeValue_1: ( CacheListNode ) -> one ( Data + null ),
  listSize_0: ( CacheList ) -> one ( Int ),
  listSize_1: ( CacheList ) -> one ( Int ),
  modCount_0: ( CacheList ) -> one ( Int ),
  modCount_1: ( CacheList ) -> one ( Int ),
  cacheSize_0: ( CacheList ) -> one ( Int ),
  cacheSize_1: ( CacheList ) -> one ( Int ),
  cacheHeader_0: ( CacheList ) -> one ( CacheListNode + null ),
  cacheHeader_1: ( CacheList ) -> one ( CacheListNode + null ),
  nextCachedNode_0: CacheListNode + null,
  nextCachedNode_1: CacheListNode + null,
  currentIndex_0: Int,
  currentIndex_1: Int,
  currentIndex_2: Int,
  currentIndex_3: Int,
  currentIndex_4: Int,
  currentIndex_5: Int,
  currentIndex_6: Int,
  currentIndex_7: Int,
  currentIndex_8: Int,
  currentIndex_9: Int,
  currentIndex_10: Int,
  currentIndex_11: Int,
  node_0: CacheListNode + null,
  node_1: CacheListNode + null,
  node1_0: CacheListNode + null,
  node1_1: CacheListNode + null,
  node1_2: CacheListNode + null,
  node1_3: CacheListNode + null,
  node1_4: CacheListNode + null,
  node1_5: CacheListNode + null,
  node1_6: CacheListNode + null,
  node1_7: CacheListNode + null,
  node1_8: CacheListNode + null,
  node1_9: CacheListNode + null,
  node1_10: CacheListNode + null,
  node1_11: CacheListNode + null,
  exception_0: IndexOutOfBoundsException + null,
  exception_1: IndexOutOfBoundsException + null,
  exception_2: IndexOutOfBoundsException + null,
  exception_3: IndexOutOfBoundsException + null,
  exception_4: IndexOutOfBoundsException + null,
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
  nullDerefBool_24: boolean,
  nullDerefBool_25: boolean,
  nullDerefBool_26: boolean,
  nullDerefBool_27: boolean,
  nullDerefBool_28: boolean,
  oldValue_0: Object + null,
  oldValue_1: Object + null
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
  TruePred[]
  and 
  (
    (
      CacheListCondition0[throw_1]
      and 
      (
        exception_1=null)
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
        exception_0=exception_1)
    )
  )
  and 
  (
    (
      CacheListCondition2[index_0]
      and 
      (
        (
          CacheListCondition0[throw_1]
          and 
          (
            exception_2=IndexOutOfBoundsExceptionLit)
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
            exception_1=exception_2)
        )
      )
      and 
      (
        (
          CacheListCondition0[throw_1]
          and 
          (
            throw_2=exception_2)
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
          CacheListCondition2[index_0])
      )
      and 
      TruePred[]
      and 
      (
        throw_1=throw_2)
      and 
      (
        exception_1=exception_2)
    )
  )
  and 
  (
    (
      CacheListCondition4[thiz_0]
      and 
      (
        (
          CacheListCondition0[throw_2]
          and 
          (
            nullDerefBool_2=true)
        )
        or 
        (
          (
            not (
              CacheListCondition0[throw_2])
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
          CacheListCondition4[thiz_0])
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
      CacheListCondition6[index_0,
                         listSize_0,
                         thiz_0]
      and 
      (
        (
          CacheListCondition0[throw_2]
          and 
          (
            exception_3=IndexOutOfBoundsExceptionLit)
        )
        or 
        (
          (
            not (
              CacheListCondition0[throw_2])
          )
          and 
          TruePred[]
          and 
          (
            exception_2=exception_3)
        )
      )
      and 
      (
        (
          CacheListCondition0[throw_2]
          and 
          (
            throw_3=exception_3)
        )
        or 
        (
          (
            not (
              CacheListCondition0[throw_2])
          )
          and 
          TruePred[]
          and 
          (
            throw_2=throw_3)
        )
      )
    )
    or 
    (
      (
        not (
          CacheListCondition6[index_0,
                             listSize_0,
                             thiz_0]
        )
      )
      and 
      TruePred[]
      and 
      (
        throw_2=throw_3)
      and 
      (
        exception_2=exception_3)
    )
  )
  and 
  (
    (
      CacheListCondition4[thiz_0]
      and 
      (
        (
          CacheListCondition0[throw_3]
          and 
          (
            nullDerefBool_3=true)
        )
        or 
        (
          (
            not (
              CacheListCondition0[throw_3])
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
      CacheListCondition8[index_0,
                         listSize_0,
                         thiz_0]
      and 
      (
        (
          CacheListCondition0[throw_3]
          and 
          (
            exception_4=IndexOutOfBoundsExceptionLit)
        )
        or 
        (
          (
            not (
              CacheListCondition0[throw_3])
          )
          and 
          TruePred[]
          and 
          (
            exception_3=exception_4)
        )
      )
      and 
      (
        (
          CacheListCondition0[throw_3]
          and 
          (
            throw_4=exception_4)
        )
        or 
        (
          (
            not (
              CacheListCondition0[throw_3])
          )
          and 
          TruePred[]
          and 
          (
            throw_3=throw_4)
        )
      )
    )
    or 
    (
      (
        not (
          CacheListCondition8[index_0,
                             listSize_0,
                             thiz_0]
        )
      )
      and 
      TruePred[]
      and 
      (
        throw_3=throw_4)
      and 
      (
        exception_3=exception_4)
    )
  )
  and 
  TruePred[]
  and 
  (
    (
      CacheListCondition4[thiz_0]
      and 
      (
        (
          CacheListCondition0[throw_4]
          and 
          (
            nullDerefBool_4=true)
        )
        or 
        (
          (
            not (
              CacheListCondition0[throw_4])
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
          CacheListCondition4[thiz_0])
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
      CacheListCondition18[index_0,
                          listSize_0,
                          thiz_0]
      and 
      (
        (
          CacheListCondition10[listHeader_0,
                              thiz_0]
          and 
          (
            (
              CacheListCondition0[throw_4]
              and 
              (
                nullDerefBool_5=true)
            )
            or 
            (
              (
                not (
                  CacheListCondition0[throw_4])
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
              CacheListCondition10[listHeader_0,
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
        (
          CacheListCondition0[throw_4]
          and 
          (
            node1_1=(thiz_0.listHeader_0).listNext_0)
        )
        or 
        (
          (
            not (
              CacheListCondition0[throw_4])
          )
          and 
          TruePred[]
          and 
          (
            node1_0=node1_1)
        )
      )
      and 
      TruePred[]
      and 
      (
        (
          CacheListCondition0[throw_4]
          and 
          (
            currentIndex_1=0)
        )
        or 
        (
          (
            not (
              CacheListCondition0[throw_4])
          )
          and 
          TruePred[]
          and 
          (
            currentIndex_0=currentIndex_1)
        )
      )
      and 
      (
        (
          CacheListCondition0[throw_4]
          and 
          (
            (
              CacheListCondition14[currentIndex_1,
                                  index_0]
              and 
              (
                (
                  CacheListCondition12[node1_1]
                  and 
                  (
                    (
                      CacheListCondition0[throw_4]
                      and 
                      (
                        nullDerefBool_6=true)
                    )
                    or 
                    (
                      (
                        not (
                          CacheListCondition0[throw_4])
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
                      CacheListCondition12[node1_1])
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
                  CacheListCondition0[throw_4]
                  and 
                  (
                    node1_2=node1_1.listNext_0)
                )
                or 
                (
                  (
                    not (
                      CacheListCondition0[throw_4])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    node1_1=node1_2)
                )
              )
              and 
              (
                (
                  CacheListCondition0[throw_4]
                  and 
                  (
                    currentIndex_2=add[currentIndex_1,1])
                )
                or 
                (
                  (
                    not (
                      CacheListCondition0[throw_4])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    currentIndex_1=currentIndex_2)
                )
              )
            )
            or 
            (
              TruePred[]
              and 
              (
                currentIndex_1=currentIndex_2)
              and 
              (
                node1_1=node1_2)
              and 
              (
                nullDerefBool_5=nullDerefBool_6)
            )
          )
          and 
          (
            (
              CacheListCondition14[currentIndex_2,
                                  index_0]
              and 
              (
                (
                  CacheListCondition12[node1_2]
                  and 
                  (
                    (
                      CacheListCondition0[throw_4]
                      and 
                      (
                        nullDerefBool_7=true)
                    )
                    or 
                    (
                      (
                        not (
                          CacheListCondition0[throw_4])
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
                      CacheListCondition12[node1_2])
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
                  CacheListCondition0[throw_4]
                  and 
                  (
                    node1_3=node1_2.listNext_0)
                )
                or 
                (
                  (
                    not (
                      CacheListCondition0[throw_4])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    node1_2=node1_3)
                )
              )
              and 
              (
                (
                  CacheListCondition0[throw_4]
                  and 
                  (
                    currentIndex_3=add[currentIndex_2,1])
                )
                or 
                (
                  (
                    not (
                      CacheListCondition0[throw_4])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    currentIndex_2=currentIndex_3)
                )
              )
            )
            or 
            (
              TruePred[]
              and 
              (
                currentIndex_2=currentIndex_3)
              and 
              (
                node1_2=node1_3)
              and 
              (
                nullDerefBool_6=nullDerefBool_7)
            )
          )
          and 
          (
            (
              CacheListCondition14[currentIndex_3,
                                  index_0]
              and 
              (
                (
                  CacheListCondition12[node1_3]
                  and 
                  (
                    (
                      CacheListCondition0[throw_4]
                      and 
                      (
                        nullDerefBool_8=true)
                    )
                    or 
                    (
                      (
                        not (
                          CacheListCondition0[throw_4])
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
                      CacheListCondition12[node1_3])
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
                  CacheListCondition0[throw_4]
                  and 
                  (
                    node1_4=node1_3.listNext_0)
                )
                or 
                (
                  (
                    not (
                      CacheListCondition0[throw_4])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    node1_3=node1_4)
                )
              )
              and 
              (
                (
                  CacheListCondition0[throw_4]
                  and 
                  (
                    currentIndex_4=add[currentIndex_3,1])
                )
                or 
                (
                  (
                    not (
                      CacheListCondition0[throw_4])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    currentIndex_3=currentIndex_4)
                )
              )
            )
            or 
            (
              TruePred[]
              and 
              (
                currentIndex_3=currentIndex_4)
              and 
              (
                node1_3=node1_4)
              and 
              (
                nullDerefBool_7=nullDerefBool_8)
            )
          )
          and 
          (
            (
              CacheListCondition14[currentIndex_4,
                                  index_0]
              and 
              (
                (
                  CacheListCondition12[node1_4]
                  and 
                  (
                    (
                      CacheListCondition0[throw_4]
                      and 
                      (
                        nullDerefBool_9=true)
                    )
                    or 
                    (
                      (
                        not (
                          CacheListCondition0[throw_4])
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
                      CacheListCondition12[node1_4])
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
                  CacheListCondition0[throw_4]
                  and 
                  (
                    node1_5=node1_4.listNext_0)
                )
                or 
                (
                  (
                    not (
                      CacheListCondition0[throw_4])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    node1_4=node1_5)
                )
              )
              and 
              (
                (
                  CacheListCondition0[throw_4]
                  and 
                  (
                    currentIndex_5=add[currentIndex_4,1])
                )
                or 
                (
                  (
                    not (
                      CacheListCondition0[throw_4])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    currentIndex_4=currentIndex_5)
                )
              )
            )
            or 
            (
              TruePred[]
              and 
              (
                currentIndex_4=currentIndex_5)
              and 
              (
                node1_4=node1_5)
              and 
              (
                nullDerefBool_8=nullDerefBool_9)
            )
          )
          and 
          (
            (
              CacheListCondition14[currentIndex_5,
                                  index_0]
              and 
              (
                (
                  CacheListCondition12[node1_5]
                  and 
                  (
                    (
                      CacheListCondition0[throw_4]
                      and 
                      (
                        nullDerefBool_10=true)
                    )
                    or 
                    (
                      (
                        not (
                          CacheListCondition0[throw_4])
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
                      CacheListCondition12[node1_5])
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
                  CacheListCondition0[throw_4]
                  and 
                  (
                    node1_6=node1_5.listNext_0)
                )
                or 
                (
                  (
                    not (
                      CacheListCondition0[throw_4])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    node1_5=node1_6)
                )
              )
              and 
              (
                (
                  CacheListCondition0[throw_4]
                  and 
                  (
                    currentIndex_6=add[currentIndex_5,1])
                )
                or 
                (
                  (
                    not (
                      CacheListCondition0[throw_4])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    currentIndex_5=currentIndex_6)
                )
              )
            )
            or 
            (
              TruePred[]
              and 
              (
                currentIndex_5=currentIndex_6)
              and 
              (
                node1_5=node1_6)
              and 
              (
                nullDerefBool_9=nullDerefBool_10)
            )
          )
          and 
          (
            (
              CacheListCondition14[currentIndex_6,
                                  index_0]
              and 
              (
                (
                  CacheListCondition12[node1_6]
                  and 
                  (
                    (
                      CacheListCondition0[throw_4]
                      and 
                      (
                        nullDerefBool_11=true)
                    )
                    or 
                    (
                      (
                        not (
                          CacheListCondition0[throw_4])
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
                      CacheListCondition12[node1_6])
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
                  CacheListCondition0[throw_4]
                  and 
                  (
                    node1_7=node1_6.listNext_0)
                )
                or 
                (
                  (
                    not (
                      CacheListCondition0[throw_4])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    node1_6=node1_7)
                )
              )
              and 
              (
                (
                  CacheListCondition0[throw_4]
                  and 
                  (
                    currentIndex_7=add[currentIndex_6,1])
                )
                or 
                (
                  (
                    not (
                      CacheListCondition0[throw_4])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    currentIndex_6=currentIndex_7)
                )
              )
            )
            or 
            (
              TruePred[]
              and 
              (
                currentIndex_6=currentIndex_7)
              and 
              (
                node1_6=node1_7)
              and 
              (
                nullDerefBool_10=nullDerefBool_11)
            )
          )
          and 
          (
            (
              CacheListCondition14[currentIndex_7,
                                  index_0]
              and 
              (
                (
                  CacheListCondition12[node1_7]
                  and 
                  (
                    (
                      CacheListCondition0[throw_4]
                      and 
                      (
                        nullDerefBool_12=true)
                    )
                    or 
                    (
                      (
                        not (
                          CacheListCondition0[throw_4])
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
                      CacheListCondition12[node1_7])
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
                  CacheListCondition0[throw_4]
                  and 
                  (
                    node1_8=node1_7.listNext_0)
                )
                or 
                (
                  (
                    not (
                      CacheListCondition0[throw_4])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    node1_7=node1_8)
                )
              )
              and 
              (
                (
                  CacheListCondition0[throw_4]
                  and 
                  (
                    currentIndex_8=add[currentIndex_7,1])
                )
                or 
                (
                  (
                    not (
                      CacheListCondition0[throw_4])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    currentIndex_7=currentIndex_8)
                )
              )
            )
            or 
            (
              TruePred[]
              and 
              (
                currentIndex_7=currentIndex_8)
              and 
              (
                node1_7=node1_8)
              and 
              (
                nullDerefBool_11=nullDerefBool_12)
            )
          )
          and 
          (
            (
              CacheListCondition14[currentIndex_8,
                                  index_0]
              and 
              (
                (
                  CacheListCondition12[node1_8]
                  and 
                  (
                    (
                      CacheListCondition0[throw_4]
                      and 
                      (
                        nullDerefBool_13=true)
                    )
                    or 
                    (
                      (
                        not (
                          CacheListCondition0[throw_4])
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
                      CacheListCondition12[node1_8])
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
                  CacheListCondition0[throw_4]
                  and 
                  (
                    node1_9=node1_8.listNext_0)
                )
                or 
                (
                  (
                    not (
                      CacheListCondition0[throw_4])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    node1_8=node1_9)
                )
              )
              and 
              (
                (
                  CacheListCondition0[throw_4]
                  and 
                  (
                    currentIndex_9=add[currentIndex_8,1])
                )
                or 
                (
                  (
                    not (
                      CacheListCondition0[throw_4])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    currentIndex_8=currentIndex_9)
                )
              )
            )
            or 
            (
              TruePred[]
              and 
              (
                currentIndex_8=currentIndex_9)
              and 
              (
                node1_8=node1_9)
              and 
              (
                nullDerefBool_12=nullDerefBool_13)
            )
          )
          and 
          (
            (
              CacheListCondition14[currentIndex_9,
                                  index_0]
              and 
              (
                (
                  CacheListCondition12[node1_9]
                  and 
                  (
                    (
                      CacheListCondition0[throw_4]
                      and 
                      (
                        nullDerefBool_14=true)
                    )
                    or 
                    (
                      (
                        not (
                          CacheListCondition0[throw_4])
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
                      CacheListCondition12[node1_9])
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
                  CacheListCondition0[throw_4]
                  and 
                  (
                    node1_10=node1_9.listNext_0)
                )
                or 
                (
                  (
                    not (
                      CacheListCondition0[throw_4])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    node1_9=node1_10)
                )
              )
              and 
              (
                (
                  CacheListCondition0[throw_4]
                  and 
                  (
                    currentIndex_10=add[currentIndex_9,1])
                )
                or 
                (
                  (
                    not (
                      CacheListCondition0[throw_4])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    currentIndex_9=currentIndex_10)
                )
              )
            )
            or 
            (
              TruePred[]
              and 
              (
                currentIndex_9=currentIndex_10)
              and 
              (
                node1_9=node1_10)
              and 
              (
                nullDerefBool_13=nullDerefBool_14)
            )
          )
          and 
          (
            (
              CacheListCondition14[currentIndex_10,
                                  index_0]
              and 
              (
                (
                  CacheListCondition12[node1_10]
                  and 
                  (
                    (
                      CacheListCondition0[throw_4]
                      and 
                      (
                        nullDerefBool_16=true)
                    )
                    or 
                    (
                      (
                        not (
                          CacheListCondition0[throw_4])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_14=nullDerefBool_16)
                    )
                  )
                )
                or 
                (
                  (
                    not (
                      CacheListCondition12[node1_10])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_14=nullDerefBool_16)
                )
              )
              and 
              (
                (
                  CacheListCondition0[throw_4]
                  and 
                  (
                    node1_11=node1_10.listNext_0)
                )
                or 
                (
                  (
                    not (
                      CacheListCondition0[throw_4])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    node1_10=node1_11)
                )
              )
              and 
              (
                (
                  CacheListCondition0[throw_4]
                  and 
                  (
                    currentIndex_11=add[currentIndex_10,1])
                )
                or 
                (
                  (
                    not (
                      CacheListCondition0[throw_4])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    currentIndex_10=currentIndex_11)
                )
              )
            )
            or 
            (
              TruePred[]
              and 
              (
                currentIndex_10=currentIndex_11)
              and 
              (
                node1_10=node1_11)
              and 
              (
                nullDerefBool_14=nullDerefBool_16)
            )
          )
          and 
          CacheListCondition15[currentIndex_11,
                              index_0]
        )
        or 
        (
          (
            not (
              CacheListCondition0[throw_4])
          )
          and 
          TruePred[]
          and 
          (
            currentIndex_1=currentIndex_11)
          and 
          (
            node1_1=node1_11)
          and 
          (
            nullDerefBool_5=nullDerefBool_16)
        )
      )
    )
    or 
    (
      (
        not (
          CacheListCondition18[index_0,
                              listSize_0,
                              thiz_0]
        )
      )
      and 
      (
        (
          CacheListCondition4[thiz_0]
          and 
          (
            (
              CacheListCondition0[throw_4]
              and 
              (
                nullDerefBool_5=true)
            )
            or 
            (
              (
                not (
                  CacheListCondition0[throw_4])
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
              CacheListCondition4[thiz_0])
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
          CacheListCondition0[throw_4]
          and 
          (
            node1_1=thiz_0.listHeader_0)
        )
        or 
        (
          (
            not (
              CacheListCondition0[throw_4])
          )
          and 
          TruePred[]
          and 
          (
            node1_0=node1_1)
        )
      )
      and 
      TruePred[]
      and 
      (
        (
          CacheListCondition4[thiz_0]
          and 
          (
            (
              CacheListCondition0[throw_4]
              and 
              (
                nullDerefBool_6=true)
            )
            or 
            (
              (
                not (
                  CacheListCondition0[throw_4])
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
              CacheListCondition4[thiz_0])
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
          CacheListCondition0[throw_4]
          and 
          (
            currentIndex_1=thiz_0.listSize_0)
        )
        or 
        (
          (
            not (
              CacheListCondition0[throw_4])
          )
          and 
          TruePred[]
          and 
          (
            currentIndex_0=currentIndex_1)
        )
      )
      and 
      (
        (
          CacheListCondition0[throw_4]
          and 
          (
            (
              CacheListCondition16[currentIndex_1,
                                  index_0]
              and 
              (
                (
                  CacheListCondition12[node1_1]
                  and 
                  (
                    (
                      CacheListCondition0[throw_4]
                      and 
                      (
                        nullDerefBool_7=true)
                    )
                    or 
                    (
                      (
                        not (
                          CacheListCondition0[throw_4])
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
                      CacheListCondition12[node1_1])
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
                  CacheListCondition0[throw_4]
                  and 
                  (
                    node1_2=node1_1.listPrevious_0)
                )
                or 
                (
                  (
                    not (
                      CacheListCondition0[throw_4])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    node1_1=node1_2)
                )
              )
              and 
              (
                (
                  CacheListCondition0[throw_4]
                  and 
                  (
                    currentIndex_2=sub[currentIndex_1,1])
                )
                or 
                (
                  (
                    not (
                      CacheListCondition0[throw_4])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    currentIndex_1=currentIndex_2)
                )
              )
            )
            or 
            (
              TruePred[]
              and 
              (
                currentIndex_1=currentIndex_2)
              and 
              (
                node1_1=node1_2)
              and 
              (
                nullDerefBool_6=nullDerefBool_7)
            )
          )
          and 
          (
            (
              CacheListCondition16[currentIndex_2,
                                  index_0]
              and 
              (
                (
                  CacheListCondition12[node1_2]
                  and 
                  (
                    (
                      CacheListCondition0[throw_4]
                      and 
                      (
                        nullDerefBool_8=true)
                    )
                    or 
                    (
                      (
                        not (
                          CacheListCondition0[throw_4])
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
                      CacheListCondition12[node1_2])
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
                  CacheListCondition0[throw_4]
                  and 
                  (
                    node1_3=node1_2.listPrevious_0)
                )
                or 
                (
                  (
                    not (
                      CacheListCondition0[throw_4])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    node1_2=node1_3)
                )
              )
              and 
              (
                (
                  CacheListCondition0[throw_4]
                  and 
                  (
                    currentIndex_3=sub[currentIndex_2,1])
                )
                or 
                (
                  (
                    not (
                      CacheListCondition0[throw_4])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    currentIndex_2=currentIndex_3)
                )
              )
            )
            or 
            (
              TruePred[]
              and 
              (
                currentIndex_2=currentIndex_3)
              and 
              (
                node1_2=node1_3)
              and 
              (
                nullDerefBool_7=nullDerefBool_8)
            )
          )
          and 
          (
            (
              CacheListCondition16[currentIndex_3,
                                  index_0]
              and 
              (
                (
                  CacheListCondition12[node1_3]
                  and 
                  (
                    (
                      CacheListCondition0[throw_4]
                      and 
                      (
                        nullDerefBool_9=true)
                    )
                    or 
                    (
                      (
                        not (
                          CacheListCondition0[throw_4])
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
                      CacheListCondition12[node1_3])
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
                  CacheListCondition0[throw_4]
                  and 
                  (
                    node1_4=node1_3.listPrevious_0)
                )
                or 
                (
                  (
                    not (
                      CacheListCondition0[throw_4])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    node1_3=node1_4)
                )
              )
              and 
              (
                (
                  CacheListCondition0[throw_4]
                  and 
                  (
                    currentIndex_4=sub[currentIndex_3,1])
                )
                or 
                (
                  (
                    not (
                      CacheListCondition0[throw_4])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    currentIndex_3=currentIndex_4)
                )
              )
            )
            or 
            (
              TruePred[]
              and 
              (
                currentIndex_3=currentIndex_4)
              and 
              (
                node1_3=node1_4)
              and 
              (
                nullDerefBool_8=nullDerefBool_9)
            )
          )
          and 
          (
            (
              CacheListCondition16[currentIndex_4,
                                  index_0]
              and 
              (
                (
                  CacheListCondition12[node1_4]
                  and 
                  (
                    (
                      CacheListCondition0[throw_4]
                      and 
                      (
                        nullDerefBool_10=true)
                    )
                    or 
                    (
                      (
                        not (
                          CacheListCondition0[throw_4])
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
                      CacheListCondition12[node1_4])
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
                  CacheListCondition0[throw_4]
                  and 
                  (
                    node1_5=node1_4.listPrevious_0)
                )
                or 
                (
                  (
                    not (
                      CacheListCondition0[throw_4])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    node1_4=node1_5)
                )
              )
              and 
              (
                (
                  CacheListCondition0[throw_4]
                  and 
                  (
                    currentIndex_5=sub[currentIndex_4,1])
                )
                or 
                (
                  (
                    not (
                      CacheListCondition0[throw_4])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    currentIndex_4=currentIndex_5)
                )
              )
            )
            or 
            (
              TruePred[]
              and 
              (
                currentIndex_4=currentIndex_5)
              and 
              (
                node1_4=node1_5)
              and 
              (
                nullDerefBool_9=nullDerefBool_10)
            )
          )
          and 
          (
            (
              CacheListCondition16[currentIndex_5,
                                  index_0]
              and 
              (
                (
                  CacheListCondition12[node1_5]
                  and 
                  (
                    (
                      CacheListCondition0[throw_4]
                      and 
                      (
                        nullDerefBool_11=true)
                    )
                    or 
                    (
                      (
                        not (
                          CacheListCondition0[throw_4])
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
                      CacheListCondition12[node1_5])
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
                  CacheListCondition0[throw_4]
                  and 
                  (
                    node1_6=node1_5.listPrevious_0)
                )
                or 
                (
                  (
                    not (
                      CacheListCondition0[throw_4])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    node1_5=node1_6)
                )
              )
              and 
              (
                (
                  CacheListCondition0[throw_4]
                  and 
                  (
                    currentIndex_6=sub[currentIndex_5,1])
                )
                or 
                (
                  (
                    not (
                      CacheListCondition0[throw_4])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    currentIndex_5=currentIndex_6)
                )
              )
            )
            or 
            (
              TruePred[]
              and 
              (
                currentIndex_5=currentIndex_6)
              and 
              (
                node1_5=node1_6)
              and 
              (
                nullDerefBool_10=nullDerefBool_11)
            )
          )
          and 
          (
            (
              CacheListCondition16[currentIndex_6,
                                  index_0]
              and 
              (
                (
                  CacheListCondition12[node1_6]
                  and 
                  (
                    (
                      CacheListCondition0[throw_4]
                      and 
                      (
                        nullDerefBool_12=true)
                    )
                    or 
                    (
                      (
                        not (
                          CacheListCondition0[throw_4])
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
                      CacheListCondition12[node1_6])
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
                  CacheListCondition0[throw_4]
                  and 
                  (
                    node1_7=node1_6.listPrevious_0)
                )
                or 
                (
                  (
                    not (
                      CacheListCondition0[throw_4])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    node1_6=node1_7)
                )
              )
              and 
              (
                (
                  CacheListCondition0[throw_4]
                  and 
                  (
                    currentIndex_7=sub[currentIndex_6,1])
                )
                or 
                (
                  (
                    not (
                      CacheListCondition0[throw_4])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    currentIndex_6=currentIndex_7)
                )
              )
            )
            or 
            (
              TruePred[]
              and 
              (
                currentIndex_6=currentIndex_7)
              and 
              (
                node1_6=node1_7)
              and 
              (
                nullDerefBool_11=nullDerefBool_12)
            )
          )
          and 
          (
            (
              CacheListCondition16[currentIndex_7,
                                  index_0]
              and 
              (
                (
                  CacheListCondition12[node1_7]
                  and 
                  (
                    (
                      CacheListCondition0[throw_4]
                      and 
                      (
                        nullDerefBool_13=true)
                    )
                    or 
                    (
                      (
                        not (
                          CacheListCondition0[throw_4])
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
                      CacheListCondition12[node1_7])
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
                  CacheListCondition0[throw_4]
                  and 
                  (
                    node1_8=node1_7.listPrevious_0)
                )
                or 
                (
                  (
                    not (
                      CacheListCondition0[throw_4])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    node1_7=node1_8)
                )
              )
              and 
              (
                (
                  CacheListCondition0[throw_4]
                  and 
                  (
                    currentIndex_8=sub[currentIndex_7,1])
                )
                or 
                (
                  (
                    not (
                      CacheListCondition0[throw_4])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    currentIndex_7=currentIndex_8)
                )
              )
            )
            or 
            (
              TruePred[]
              and 
              (
                currentIndex_7=currentIndex_8)
              and 
              (
                node1_7=node1_8)
              and 
              (
                nullDerefBool_12=nullDerefBool_13)
            )
          )
          and 
          (
            (
              CacheListCondition16[currentIndex_8,
                                  index_0]
              and 
              (
                (
                  CacheListCondition12[node1_8]
                  and 
                  (
                    (
                      CacheListCondition0[throw_4]
                      and 
                      (
                        nullDerefBool_14=true)
                    )
                    or 
                    (
                      (
                        not (
                          CacheListCondition0[throw_4])
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
                      CacheListCondition12[node1_8])
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
                  CacheListCondition0[throw_4]
                  and 
                  (
                    node1_9=node1_8.listPrevious_0)
                )
                or 
                (
                  (
                    not (
                      CacheListCondition0[throw_4])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    node1_8=node1_9)
                )
              )
              and 
              (
                (
                  CacheListCondition0[throw_4]
                  and 
                  (
                    currentIndex_9=sub[currentIndex_8,1])
                )
                or 
                (
                  (
                    not (
                      CacheListCondition0[throw_4])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    currentIndex_8=currentIndex_9)
                )
              )
            )
            or 
            (
              TruePred[]
              and 
              (
                currentIndex_8=currentIndex_9)
              and 
              (
                node1_8=node1_9)
              and 
              (
                nullDerefBool_13=nullDerefBool_14)
            )
          )
          and 
          (
            (
              CacheListCondition16[currentIndex_9,
                                  index_0]
              and 
              (
                (
                  CacheListCondition12[node1_9]
                  and 
                  (
                    (
                      CacheListCondition0[throw_4]
                      and 
                      (
                        nullDerefBool_15=true)
                    )
                    or 
                    (
                      (
                        not (
                          CacheListCondition0[throw_4])
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
                      CacheListCondition12[node1_9])
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
                  CacheListCondition0[throw_4]
                  and 
                  (
                    node1_10=node1_9.listPrevious_0)
                )
                or 
                (
                  (
                    not (
                      CacheListCondition0[throw_4])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    node1_9=node1_10)
                )
              )
              and 
              (
                (
                  CacheListCondition0[throw_4]
                  and 
                  (
                    currentIndex_10=sub[currentIndex_9,1])
                )
                or 
                (
                  (
                    not (
                      CacheListCondition0[throw_4])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    currentIndex_9=currentIndex_10)
                )
              )
            )
            or 
            (
              TruePred[]
              and 
              (
                currentIndex_9=currentIndex_10)
              and 
              (
                node1_9=node1_10)
              and 
              (
                nullDerefBool_14=nullDerefBool_15)
            )
          )
          and 
          (
            (
              CacheListCondition16[currentIndex_10,
                                  index_0]
              and 
              (
                (
                  CacheListCondition12[node1_10]
                  and 
                  (
                    (
                      CacheListCondition0[throw_4]
                      and 
                      (
                        nullDerefBool_16=true)
                    )
                    or 
                    (
                      (
                        not (
                          CacheListCondition0[throw_4])
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
                      CacheListCondition12[node1_10])
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
                  CacheListCondition0[throw_4]
                  and 
                  (
                    node1_11=node1_10.listPrevious_0)
                )
                or 
                (
                  (
                    not (
                      CacheListCondition0[throw_4])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    node1_10=node1_11)
                )
              )
              and 
              (
                (
                  CacheListCondition0[throw_4]
                  and 
                  (
                    currentIndex_11=sub[currentIndex_10,1])
                )
                or 
                (
                  (
                    not (
                      CacheListCondition0[throw_4])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    currentIndex_10=currentIndex_11)
                )
              )
            )
            or 
            (
              TruePred[]
              and 
              (
                currentIndex_10=currentIndex_11)
              and 
              (
                node1_10=node1_11)
              and 
              (
                nullDerefBool_15=nullDerefBool_16)
            )
          )
          and 
          CacheListCondition17[currentIndex_11,
                              index_0]
        )
        or 
        (
          (
            not (
              CacheListCondition0[throw_4])
          )
          and 
          TruePred[]
          and 
          (
            currentIndex_1=currentIndex_11)
          and 
          (
            node1_1=node1_11)
          and 
          (
            nullDerefBool_6=nullDerefBool_16)
        )
      )
    )
  )
  and 
  (
    (
      CacheListCondition0[throw_4]
      and 
      (
        node_1=node1_11)
    )
    or 
    (
      (
        not (
          CacheListCondition0[throw_4])
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
      CacheListCondition20[node_1]
      and 
      (
        (
          CacheListCondition0[throw_4]
          and 
          (
            nullDerefBool_17=true)
        )
        or 
        (
          (
            not (
              CacheListCondition0[throw_4])
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
          CacheListCondition20[node_1])
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
      CacheListCondition0[throw_4]
      and 
      (
        oldValue_1=node_1.nodeValue_0)
    )
    or 
    (
      (
        not (
          CacheListCondition0[throw_4])
      )
      and 
      TruePred[]
      and 
      (
        oldValue_0=oldValue_1)
    )
  )
  and 
  (
    (
      CacheListCondition22[listPrevious_0,
                          node_1]
      and 
      (
        (
          CacheListCondition0[throw_4]
          and 
          (
            nullDerefBool_18=true)
        )
        or 
        (
          (
            not (
              CacheListCondition0[throw_4])
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
          CacheListCondition22[listPrevious_0,
                              node_1]
        )
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
      CacheListCondition0[throw_4]
      and 
      (
        listNext_1=(listNext_0)++((node_1.listPrevious_0)->(node_1.listNext_0)))
    )
    or 
    (
      (
        not (
          CacheListCondition0[throw_4])
      )
      and 
      TruePred[]
      and 
      (
        listNext_0=listNext_1)
    )
  )
  and 
  (
    (
      CacheListCondition24[listNext_1,
                          node_1]
      and 
      (
        (
          CacheListCondition0[throw_4]
          and 
          (
            nullDerefBool_19=true)
        )
        or 
        (
          (
            not (
              CacheListCondition0[throw_4])
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
          CacheListCondition24[listNext_1,
                              node_1]
        )
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
      CacheListCondition0[throw_4]
      and 
      (
        listPrevious_1=(listPrevious_0)++((node_1.listNext_1)->(node_1.listPrevious_0)))
    )
    or 
    (
      (
        not (
          CacheListCondition0[throw_4])
      )
      and 
      TruePred[]
      and 
      (
        listPrevious_0=listPrevious_1)
    )
  )
  and 
  (
    (
      CacheListCondition26[thiz_0]
      and 
      (
        (
          CacheListCondition0[throw_4]
          and 
          (
            nullDerefBool_20=true)
        )
        or 
        (
          (
            not (
              CacheListCondition0[throw_4])
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
          CacheListCondition26[thiz_0])
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
      CacheListCondition0[throw_4]
      and 
      (
        listSize_1=(listSize_0)++((thiz_0)->(sub[thiz_0.listSize_0,1])))
    )
    or 
    (
      (
        not (
          CacheListCondition0[throw_4])
      )
      and 
      TruePred[]
      and 
      (
        listSize_0=listSize_1)
    )
  )
  and 
  (
    (
      CacheListCondition26[thiz_0]
      and 
      (
        (
          CacheListCondition0[throw_4]
          and 
          (
            nullDerefBool_21=true)
        )
        or 
        (
          (
            not (
              CacheListCondition0[throw_4])
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
          CacheListCondition26[thiz_0])
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
      CacheListCondition0[throw_4]
      and 
      (
        modCount_1=(modCount_0)++((thiz_0)->(add[thiz_0.modCount_0,1])))
    )
    or 
    (
      (
        not (
          CacheListCondition0[throw_4])
      )
      and 
      TruePred[]
      and 
      (
        modCount_0=modCount_1)
    )
  )
  and 
  (
    (
      CacheListCondition26[thiz_0]
      and 
      (
        (
          CacheListCondition0[throw_4]
          and 
          (
            nullDerefBool_22=true)
        )
        or 
        (
          (
            not (
              CacheListCondition0[throw_4])
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
          CacheListCondition26[thiz_0])
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
      CacheListCondition28[cacheSize_0,
                          maximumCacheSize_0,
                          thiz_0]
      and 
      TruePred[]
      and 
      (
        (
          CacheListCondition4[thiz_0]
          and 
          (
            (
              CacheListCondition0[throw_4]
              and 
              (
                nullDerefBool_23=true)
            )
            or 
            (
              (
                not (
                  CacheListCondition0[throw_4])
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
              CacheListCondition4[thiz_0])
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
          CacheListCondition0[throw_4]
          and 
          (
            nextCachedNode_1=thiz_0.cacheHeader_0)
        )
        or 
        (
          (
            not (
              CacheListCondition0[throw_4])
          )
          and 
          TruePred[]
          and 
          (
            nextCachedNode_0=nextCachedNode_1)
        )
      )
      and 
      (
        (
          CacheListCondition20[node_1]
          and 
          (
            (
              CacheListCondition0[throw_4]
              and 
              (
                nullDerefBool_24=true)
            )
            or 
            (
              (
                not (
                  CacheListCondition0[throw_4])
              )
              and 
              TruePred[]
              and 
              (
                nullDerefBool_23=nullDerefBool_24)
            )
          )
        )
        or 
        (
          (
            not (
              CacheListCondition20[node_1])
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
          CacheListCondition0[throw_4]
          and 
          (
            listPrevious_2=(listPrevious_1)++((node_1)->(null)))
        )
        or 
        (
          (
            not (
              CacheListCondition0[throw_4])
          )
          and 
          TruePred[]
          and 
          (
            listPrevious_1=listPrevious_2)
        )
      )
      and 
      (
        (
          CacheListCondition20[node_1]
          and 
          (
            (
              CacheListCondition0[throw_4]
              and 
              (
                nullDerefBool_25=true)
            )
            or 
            (
              (
                not (
                  CacheListCondition0[throw_4])
              )
              and 
              TruePred[]
              and 
              (
                nullDerefBool_24=nullDerefBool_25)
            )
          )
        )
        or 
        (
          (
            not (
              CacheListCondition20[node_1])
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
          CacheListCondition0[throw_4]
          and 
          (
            listNext_2=(listNext_1)++((node_1)->(nextCachedNode_1)))
        )
        or 
        (
          (
            not (
              CacheListCondition0[throw_4])
          )
          and 
          TruePred[]
          and 
          (
            listNext_1=listNext_2)
        )
      )
      and 
      (
        (
          CacheListCondition20[node_1]
          and 
          (
            (
              CacheListCondition0[throw_4]
              and 
              (
                nullDerefBool_26=true)
            )
            or 
            (
              (
                not (
                  CacheListCondition0[throw_4])
              )
              and 
              TruePred[]
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
              CacheListCondition20[node_1])
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
          CacheListCondition0[throw_4]
          and 
          (
            nodeValue_1=(nodeValue_0)++((node_1)->(null)))
        )
        or 
        (
          (
            not (
              CacheListCondition0[throw_4])
          )
          and 
          TruePred[]
          and 
          (
            nodeValue_0=nodeValue_1)
        )
      )
      and 
      (
        (
          CacheListCondition4[thiz_0]
          and 
          (
            (
              CacheListCondition0[throw_4]
              and 
              (
                nullDerefBool_27=true)
            )
            or 
            (
              (
                not (
                  CacheListCondition0[throw_4])
              )
              and 
              TruePred[]
              and 
              (
                nullDerefBool_26=nullDerefBool_27)
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
            nullDerefBool_26=nullDerefBool_27)
        )
      )
      and 
      (
        (
          CacheListCondition0[throw_4]
          and 
          (
            cacheHeader_1=(cacheHeader_0)++((thiz_0)->(node_1)))
        )
        or 
        (
          (
            not (
              CacheListCondition0[throw_4])
          )
          and 
          TruePred[]
          and 
          (
            cacheHeader_0=cacheHeader_1)
        )
      )
      and 
      (
        (
          CacheListCondition26[thiz_0]
          and 
          (
            (
              CacheListCondition0[throw_4]
              and 
              (
                nullDerefBool_28=true)
            )
            or 
            (
              (
                not (
                  CacheListCondition0[throw_4])
              )
              and 
              TruePred[]
              and 
              (
                nullDerefBool_27=nullDerefBool_28)
            )
          )
        )
        or 
        (
          (
            not (
              CacheListCondition26[thiz_0])
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
          CacheListCondition0[throw_4]
          and 
          (
            cacheSize_1=(cacheSize_0)++((thiz_0)->(add[thiz_0.cacheSize_0,1])))
        )
        or 
        (
          (
            not (
              CacheListCondition0[throw_4])
          )
          and 
          TruePred[]
          and 
          (
            cacheSize_0=cacheSize_1)
        )
      )
    )
    or 
    (
      (
        not (
          CacheListCondition28[cacheSize_0,
                              maximumCacheSize_0,
                              thiz_0]
        )
      )
      and 
      TruePred[]
      and 
      (
        listPrevious_1=listPrevious_2)
      and 
      (
        nextCachedNode_0=nextCachedNode_1)
      and 
      (
        listNext_1=listNext_2)
      and 
      (
        nodeValue_0=nodeValue_1)
      and 
      (
        nullDerefBool_22=nullDerefBool_28)
      and 
      (
        cacheHeader_0=cacheHeader_1)
      and 
      (
        cacheSize_0=cacheSize_1)
    )
  )
  and 
  (
    (
      CacheListCondition0[throw_4]
      and 
      (
        return_1=oldValue_1)
    )
    or 
    (
      (
        not (
          CacheListCondition0[throw_4])
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
      CacheListCondition30[nullDerefBool_28,
                          throw_4]
      and 
      (
        (
          CacheListCondition0[throw_4]
          and 
          (
            throw_5=NullPointerExceptionLit)
        )
        or 
        (
          (
            not (
              CacheListCondition0[throw_4])
          )
          and 
          TruePred[]
          and 
          (
            throw_4=throw_5)
        )
      )
    )
    or 
    (
      (
        not (
          CacheListCondition30[nullDerefBool_28,
                              throw_4]
        )
      )
      and 
      TruePred[]
      and 
      (
        throw_4=throw_5)
    )
  )

}

one sig QF {
  DEFAULT_CACHE_SIZE_0: ( CacheList ) -> one ( Int ),
  cacheHeader_0: ( CacheList ) -> one ( CacheListNode + null ),
  cacheHeader_1: ( CacheList ) -> one ( CacheListNode + null ),
  cacheSize_0: ( CacheList ) -> one ( Int ),
  cacheSize_1: ( CacheList ) -> one ( Int ),
  index_0: Int,
  l0_currentIndex_0: Int,
  l0_currentIndex_1: Int,
  l0_currentIndex_10: Int,
  l0_currentIndex_11: Int,
  l0_currentIndex_2: Int,
  l0_currentIndex_3: Int,
  l0_currentIndex_4: Int,
  l0_currentIndex_5: Int,
  l0_currentIndex_6: Int,
  l0_currentIndex_7: Int,
  l0_currentIndex_8: Int,
  l0_currentIndex_9: Int,
  l0_exception_0: IndexOutOfBoundsException + null,
  l0_exception_1: IndexOutOfBoundsException + null,
  l0_exception_2: IndexOutOfBoundsException + null,
  l0_exception_3: IndexOutOfBoundsException + null,
  l0_exception_4: IndexOutOfBoundsException + null,
  l0_nextCachedNode_0: CacheListNode + null,
  l0_nextCachedNode_1: CacheListNode + null,
  l0_node1_0: CacheListNode + null,
  l0_node1_1: CacheListNode + null,
  l0_node1_10: CacheListNode + null,
  l0_node1_11: CacheListNode + null,
  l0_node1_2: CacheListNode + null,
  l0_node1_3: CacheListNode + null,
  l0_node1_4: CacheListNode + null,
  l0_node1_5: CacheListNode + null,
  l0_node1_6: CacheListNode + null,
  l0_node1_7: CacheListNode + null,
  l0_node1_8: CacheListNode + null,
  l0_node1_9: CacheListNode + null,
  l0_node_0: CacheListNode + null,
  l0_node_1: CacheListNode + null,
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
  l0_nullDerefBool_24: boolean,
  l0_nullDerefBool_25: boolean,
  l0_nullDerefBool_26: boolean,
  l0_nullDerefBool_27: boolean,
  l0_nullDerefBool_28: boolean,
  l0_nullDerefBool_3: boolean,
  l0_nullDerefBool_4: boolean,
  l0_nullDerefBool_5: boolean,
  l0_nullDerefBool_6: boolean,
  l0_nullDerefBool_7: boolean,
  l0_nullDerefBool_8: boolean,
  l0_nullDerefBool_9: boolean,
  l0_oldValue_0: Object + null,
  l0_oldValue_1: Object + null,
  listHeader_0: ( CacheList ) -> one ( CacheListNode + null ),
  blistNext_0,flistNext_0: ( CacheListNode ) -> lone ( CacheListNode + null ),
  listNext_1: ( CacheListNode ) -> one ( CacheListNode + null ),
  listNext_2: ( CacheListNode ) -> one ( CacheListNode + null ),
  blistPrevious_0,flistPrevious_0: ( CacheListNode ) -> lone ( CacheListNode + null ),
  listPrevious_1: ( CacheListNode ) -> one ( CacheListNode + null ),
  listPrevious_2: ( CacheListNode ) -> one ( CacheListNode + null ),
  listSize_0: ( CacheList ) -> one ( Int ),
  listSize_1: ( CacheList ) -> one ( Int ),
  maximumCacheSize_0: ( CacheList ) -> one ( Int ),
  modCount_0: ( CacheList ) -> one ( Int ),
  modCount_1: ( CacheList ) -> one ( Int ),
  myseq_0: ( CacheList ) -> ( seq ( CacheListNode ) ),
  myseq_1: ( CacheList ) -> ( seq ( CacheListNode ) ),
  nodeValue_0: ( CacheListNode ) -> one ( Data + null ),
  nodeValue_1: ( CacheListNode ) -> one ( Data + null ),
  return_0: Object + null,
  return_1: Object + null,
  thiz_0: CacheList,
  throw_0: Throwable + null,
  throw_1: Throwable + null,
  throw_2: Throwable + null,
  throw_3: Throwable + null,
  throw_4: Throwable + null,
  throw_5: Throwable + null
}


fact {
  precondition_CacheList_remove_0[QF.DEFAULT_CACHE_SIZE_0,
                                 QF.cacheHeader_0,
                                 QF.cacheSize_0,
                                 QF.index_0,
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
  CacheList_remove_0[QF.thiz_0,
                    QF.throw_0,
                    QF.throw_1,
                    QF.throw_2,
                    QF.throw_3,
                    QF.throw_4,
                    QF.throw_5,
                    QF.return_0,
                    QF.return_1,
                    QF.index_0,
                    (QF.flistPrevious_0+QF.blistPrevious_0),
                    QF.listPrevious_1,
                    QF.listPrevious_2,
                    QF.listHeader_0,
                    (QF.flistNext_0+QF.blistNext_0),
                    QF.listNext_1,
                    QF.listNext_2,
                    QF.maximumCacheSize_0,
                    QF.nodeValue_0,
                    QF.nodeValue_1,
                    QF.listSize_0,
                    QF.listSize_1,
                    QF.modCount_0,
                    QF.modCount_1,
                    QF.cacheSize_0,
                    QF.cacheSize_1,
                    QF.cacheHeader_0,
                    QF.cacheHeader_1,
                    QF.l0_nextCachedNode_0,
                    QF.l0_nextCachedNode_1,
                    QF.l0_currentIndex_0,
                    QF.l0_currentIndex_1,
                    QF.l0_currentIndex_2,
                    QF.l0_currentIndex_3,
                    QF.l0_currentIndex_4,
                    QF.l0_currentIndex_5,
                    QF.l0_currentIndex_6,
                    QF.l0_currentIndex_7,
                    QF.l0_currentIndex_8,
                    QF.l0_currentIndex_9,
                    QF.l0_currentIndex_10,
                    QF.l0_currentIndex_11,
                    QF.l0_node_0,
                    QF.l0_node_1,
                    QF.l0_node1_0,
                    QF.l0_node1_1,
                    QF.l0_node1_2,
                    QF.l0_node1_3,
                    QF.l0_node1_4,
                    QF.l0_node1_5,
                    QF.l0_node1_6,
                    QF.l0_node1_7,
                    QF.l0_node1_8,
                    QF.l0_node1_9,
                    QF.l0_node1_10,
                    QF.l0_node1_11,
                    QF.l0_exception_0,
                    QF.l0_exception_1,
                    QF.l0_exception_2,
                    QF.l0_exception_3,
                    QF.l0_exception_4,
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
                    QF.l0_nullDerefBool_24,
                    QF.l0_nullDerefBool_25,
                    QF.l0_nullDerefBool_26,
                    QF.l0_nullDerefBool_27,
                    QF.l0_nullDerefBool_28,
                    QF.l0_oldValue_0,
                    QF.l0_oldValue_1]

}

fact {
  havocVariable3[QF.myseq_1]
}

fact {
  CacheListCondition32[QF.listHeader_0,
                      QF.listNext_2,
                      QF.myseq_1,
                      QF.thiz_0]

}

assert CList_m3{
  postcondition_CacheList_remove_0[QF.DEFAULT_CACHE_SIZE_0,
                                  QF.cacheHeader_1,
                                  QF.cacheSize_1,
                                  QF.index_0,
                                  QF.index_0,
                                  QF.listHeader_0,
                                  QF.listNext_2,
                                  QF.listPrevious_2,
                                  QF.listSize_0,
                                  QF.listSize_1,
                                  QF.maximumCacheSize_0,
                                  QF.myseq_0,
                                  QF.myseq_1,
                                  QF.nodeValue_1,
                                  QF.thiz_0,
                                  QF.thiz_0,
                                  QF.throw_5]
}
check CList_m3 for 0 but 
                 exactly 1 CacheList, 
                 exactly 20 Data,
                 exactly 20 CacheListNode,
                 20 seq, 
                 6 int  


one sig CL0 extends CacheList {}
one sig N0,N1,N2,N3,N4,N5,N6,N7,N8,N9,N10,N11,N12,N13,N14,N15,N16,N17,N18,N19 extends CacheListNode {}
one sig D0,D1,D2,D3,D4,D5,D6,D7,D8,D9,D10,D11,D12,D13,D14,D15,D16,D17,D18,D19 extends Data {}
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
fun data_prevs[e: D0+D1+D2+D3+D4+D5+D6+D7+D8+D9+D10+D11+D12+D13+D14+D15+D16+D17+D18+D19] : set (D0+D1+D2+D3+D4+D5+D6+D7+D8+D9+D10+D11+D12+D13+D14+D15+D16+D17+D18+D19) 
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
     +
   D17 -> ( D0+D1+D2+D3+D4+D5+D6+D7+D8+D9+D10+D11+D12+D13+D14+D15+D16 ) 
     +
   D18 -> ( D0+D1+D2+D3+D4+D5+D6+D7+D8+D9+D10+D11+D12+D13+D14+D15+D16+D17 ) 
     +
   D19 -> ( D0+D1+D2+D3+D4+D5+D6+D7+D8+D9+D10+D11+D12+D13+D14+D15+D16+D17+D18 ) 
  ) 
} 
fun data_next[]: (D0+D1+D2+D3+D4+D5+D6+D7+D8+D9+D10+D11+D12+D13+D14+D15+D16+D17+D18+D19) -> (D0+D1+D2+D3+D4+D5+D6+D7+D8+D9+D10+D11+D12+D13+D14+D15+D16+D17+D18+D19) 
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
 +  D16 -> D17 
 +  D17 -> D18 
 +  D18 -> D19 
} 
pred data_lt[e1,e2: D0+D1+D2+D3+D4+D5+D6+D7+D8+D9+D10+D11+D12+D13+D14+D15+D16+D17+D18+D19] { 
   e1 in data_prevs[e2] 
 } 
fun node_rprevs[e: N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19] :set (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19) 
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
   + 
   N17 -> ( N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17 ) 
   + 
   N18 -> ( N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18 ) 
   + 
   N19 -> ( N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19 ) 
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
let entry=(CL0.(QF.listHeader_0+QF.cacheHeader_0)),ff1=QF.flistNext_0,ff2=QF.flistPrevious_0,bf1=QF.blistNext_0,bf2=QF.blistPrevious_0 | { 
   -- forwardPlusBackwardAreFunctions 
   no ((ff1.univ) & (bf1.univ)) 
   no ((ff2.univ) & (bf2.univ)) 
   N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19 = ff1.univ + bf1.univ   
   N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19 = ff2.univ + bf2.univ   

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
+N15->N12 
+N15->N13 
+N15->N14 
+N16->N13 
+N16->N14 
+N16->N15 
+N17->N15 
+N17->N16 
+N18->N15 
+N18->N16 
+N18->N17 
+N19->N16 
+N19->N17 
+N19->N18 
 
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
+N15->N12 
+N15->N13 
+N15->N14 
+N16->N14 
+N16->N15 
+N17->N14 
+N17->N15 
+N17->N16 
+N18->N15 
+N18->N16 
+N18->N17 
+N19->N17 
+N19->N18 
 
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
+N12->N15 
+N12->null 
+N13->N14 
+N13->N15 
+N13->N16 
+N13->null 
+N14->N15 
+N14->N16 
+N14->null 
+N15->N16 
+N15->N17 
+N15->N18 
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
+N12->N15 
+N12->null 
+N13->N14 
+N13->N15 
+N13->N16 
+N13->null 
+N14->N15 
+N14->N16 
+N14->N17 
+N14->null 
+N15->N16 
+N15->N17 
+N15->N18 
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
+CL0->15 
+CL0->16 
+CL0->17 
+CL0->18 
+CL0->19 

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
+CL0->15 
+CL0->16 
+CL0->17 
+CL0->18 
+CL0->19 

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
