/* 
 * DynAlloy translator options 
 * --------------------------- 
 * applySimplifications= true
 * assertionId= BinHeap_m3
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
//-------------- amelia_data_D0--------------//
sig D0 extends Data {}
{}





//-------------- amelia_data_D1--------------//
sig D1 extends Data {}
{}





//-------------- amelia_data_D2--------------//
sig D2 extends Data {}
{}





//-------------- java_lang_Throwable--------------//
abstract sig Throwable extends Object {}
{}





//-------------- java_lang_Object--------------//
abstract sig Object {}
{}





//-------------- amelia_data_D15--------------//
sig D15 extends Data {}
{}





//-------------- amelia_data_D14--------------//
sig D14 extends Data {}
{}





//-------------- amelia_data_D13--------------//
sig D13 extends Data {}
{}





//-------------- amelia_data_D12--------------//
sig D12 extends Data {}
{}





//-------------- amelia_data_D11--------------//
sig D11 extends Data {}
{}





//-------------- amelia_binheap_BinHeap--------------//
sig BinHeap extends Object {}
{}




pred postcondition_BinHeap_insert_0[
  child':univ->univ,
  data_value':univ,
  degree':univ->univ,
  element':univ->univ,
  fresh_node':univ,
  head':univ->univ,
  nextData':univ->univ,
  nodes:univ->univ,
  nodes':univ->univ,
  parent':univ->univ,
  sibling':univ->univ,
  size':univ->univ,
  thiz:univ,
  thiz':univ,
  throw':univ
]{
   BinHeap_ensures[data_value',
                  element',
                  fresh_node',
                  nodes,
                  nodes',
                  thiz,
                  throw']
   and 
   BinHeap_object_invariant[child',
                           degree',
                           element',
                           head',
                           nextData',
                           parent',
                           sibling',
                           size',
                           thiz']

}

pred BinHeap_ensures[
  data_value':univ,
  element':univ->univ,
  fresh_node':univ,
  nodes:univ->univ,
  nodes':univ->univ,
  thiz:univ,
  throw':univ
]{
   equ[thiz.nodes',
      (thiz.nodes)+fresh_node']
   and 
   equ[fresh_node'.element',
      data_value']
   and 
   equ[throw',
      null]

}

pred BinHeapCondition41[
  tmp:univ
]{
   not (
     isEmptyOrNull[tmp])

}

pred BinHeapCondition40[
  tmp:univ
]{
   isEmptyOrNull[tmp]

}

pred BinHeapCondition36[
  temp1:univ,
  tmp:univ
]{
   isEmptyOrNull[tmp]
   and 
   isEmptyOrNull[temp1]

}

pred BinHeapCondition3[
  thiz:univ
]{
   not (
     isEmptyOrNull[thiz])

}

pred BinHeapCondition37[
  temp1:univ,
  tmp:univ
]{
   not (
     isEmptyOrNull[tmp]
     and 
     isEmptyOrNull[temp1]
   )

}

pred BinHeapCondition2[
  thiz:univ
]{
   isEmptyOrNull[thiz]

}

pred BinHeapCondition59[
  temp_0:univ
]{
   not (
     isEmptyOrNull[temp_0])

}

pred BinHeapCondition58[
  temp_0:univ
]{
   isEmptyOrNull[temp_0]

}

pred BinHeapCondition1[
  throw:univ
]{
   not (
     equ[throw,
        null]
   )

}

pred BinHeapCondition0[
  throw:univ
]{
   equ[throw,
      null]

}

pred BinHeapCondition61[
  thiz:univ
]{
   not (
     isEmptyOrNull[thiz]
     and 
     isEmptyOrNull[thiz]
   )

}

pred BinHeapCondition48[
  degree:univ->univ,
  temp1:univ,
  temp2:univ
]{
   lt[temp1.degree,
     temp2.degree]

}

pred BinHeapCondition60[
  thiz:univ
]{
   isEmptyOrNull[thiz]
   and 
   isEmptyOrNull[thiz]

}

pred BinHeap_nodes_abstraction[
  child:univ->univ,
  head:univ->univ,
  nodes:univ->univ,
  sibling:univ->univ,
  thiz:univ
]{
   equ[thiz.nodes,
      fun_set_difference[(thiz.head).(fun_reflexive_closure[child+sibling]),null]]

}

pred BinHeapCondition49[
  degree:univ->univ,
  temp1:univ,
  temp2:univ
]{
   not (
     lt[temp1.degree,
       temp2.degree]
   )

}

pred BinHeapCondition20[
  prevTemp:univ
]{
   equ[prevTemp,
      null]

}

pred BinHeapCondition21[
  prevTemp:univ
]{
   not (
     equ[prevTemp,
        null]
   )

}

pred BinHeapCondition5[
  head:univ->univ,
  thiz:univ
]{
   not (
     isEmptyOrNull[thiz.head]
     and 
     isEmptyOrNull[thiz]
   )

}

pred BinHeapCondition4[
  head:univ->univ,
  thiz:univ
]{
   isEmptyOrNull[thiz.head]
   and 
   isEmptyOrNull[thiz]

}

pred BinHeapCondition54[
  sibling:univ->univ,
  temp1:univ
]{
   neq[temp1.sibling,
      null]

}

pred BinHeapCondition55[
  sibling:univ->univ,
  temp1:univ
]{
   not (
     neq[temp1.sibling,
        null]
   )

}

pred BinHeapCondition56[
  temp1:univ
]{
   equ[temp1,
      null]

}

pred BinHeapCondition57[
  temp1:univ
]{
   not (
     equ[temp1,
        null]
   )

}

pred BinHeapCondition32[
  temp1:univ,
  temp2:univ
]{
   isEmptyOrNull[temp1]
   and 
   isEmptyOrNull[temp2]

}

pred Data_object_invariant[
  nextData:univ->univ
]{
   (
     pred_set_some[D19]
     implies 
             equ[D19.nextData,
                null]
   )
   and 
   (
     pred_empty_set[D19]
     implies 
             isSubset[D18.nextData,
                     null]
   )
   and 
   (
     pred_set_some[D19]
     implies 
             equ[D18.nextData,
                D19]
   )
   and 
   (
     pred_empty_set[D18]
     implies 
             isSubset[D17.nextData,
                     null]
   )
   and 
   (
     pred_set_some[D18]
     implies 
             equ[D17.nextData,
                D18]
   )
   and 
   (
     pred_empty_set[D17]
     implies 
             isSubset[D16.nextData,
                     null]
   )
   and 
   (
     pred_set_some[D17]
     implies 
             equ[D16.nextData,
                D17]
   )
   and 
   (
     pred_empty_set[D16]
     implies 
             isSubset[D15.nextData,
                     null]
   )
   and 
   (
     pred_set_some[D16]
     implies 
             equ[D15.nextData,
                D16]
   )
   and 
   (
     pred_empty_set[D15]
     implies 
             isSubset[D14.nextData,
                     null]
   )
   and 
   (
     pred_set_some[D15]
     implies 
             equ[D14.nextData,
                D15]
   )
   and 
   (
     pred_empty_set[D14]
     implies 
             isSubset[D13.nextData,
                     null]
   )
   and 
   (
     pred_set_some[D14]
     implies 
             equ[D13.nextData,
                D14]
   )
   and 
   (
     pred_empty_set[D13]
     implies 
             isSubset[D12.nextData,
                     null]
   )
   and 
   (
     pred_set_some[D13]
     implies 
             equ[D12.nextData,
                D13]
   )
   and 
   (
     pred_empty_set[D12]
     implies 
             isSubset[D11.nextData,
                     null]
   )
   and 
   (
     pred_set_some[D12]
     implies 
             equ[D11.nextData,
                D12]
   )
   and 
   (
     pred_empty_set[D11]
     implies 
             isSubset[D10.nextData,
                     null]
   )
   and 
   (
     pred_set_some[D11]
     implies 
             equ[D10.nextData,
                D11]
   )
   and 
   (
     pred_empty_set[D10]
     implies 
             isSubset[D9.nextData,
                     null]
   )
   and 
   (
     pred_set_some[D10]
     implies 
             equ[D9.nextData,
                D10]
   )
   and 
   (
     pred_empty_set[D9]
     implies 
             isSubset[D8.nextData,
                     null]
   )
   and 
   (
     pred_set_some[D9]
     implies 
             equ[D8.nextData,
                D9]
   )
   and 
   (
     pred_empty_set[D8]
     implies 
             isSubset[D7.nextData,
                     null]
   )
   and 
   (
     pred_set_some[D8]
     implies 
             equ[D7.nextData,
                D8]
   )
   and 
   (
     pred_empty_set[D7]
     implies 
             isSubset[D6.nextData,
                     null]
   )
   and 
   (
     pred_set_some[D7]
     implies 
             equ[D6.nextData,
                D7]
   )
   and 
   (
     pred_empty_set[D6]
     implies 
             isSubset[D5.nextData,
                     null]
   )
   and 
   (
     pred_set_some[D6]
     implies 
             equ[D5.nextData,
                D6]
   )
   and 
   (
     pred_empty_set[D5]
     implies 
             isSubset[D4.nextData,
                     null]
   )
   and 
   (
     pred_set_some[D5]
     implies 
             equ[D4.nextData,
                D5]
   )
   and 
   (
     pred_empty_set[D4]
     implies 
             isSubset[D3.nextData,
                     null]
   )
   and 
   (
     pred_set_some[D4]
     implies 
             equ[D3.nextData,
                D4]
   )
   and 
   (
     pred_empty_set[D3]
     implies 
             isSubset[D2.nextData,
                     null]
   )
   and 
   (
     pred_set_some[D3]
     implies 
             equ[D2.nextData,
                D3]
   )
   and 
   (
     pred_empty_set[D2]
     implies 
             isSubset[D1.nextData,
                     null]
   )
   and 
   (
     pred_set_some[D2]
     implies 
             equ[D1.nextData,
                D2]
   )
   and 
   (
     pred_empty_set[D1]
     implies 
             isSubset[D0.nextData,
                     null]
   )
   and 
   (
     pred_set_some[D1]
     implies 
             equ[D0.nextData,
                D1]
   )

}

pred BinHeapCondition6[
  nextTemp:univ,
  sibling:univ->univ,
  temp:univ
]{
   isEmptyOrNull[temp]
   and 
   isEmptyOrNull[nextTemp]
   and 
   isEmptyOrNull[nextTemp]
   and 
   isEmptyOrNull[nextTemp.sibling]
   and 
   isEmptyOrNull[nextTemp]
   and 
   isEmptyOrNull[temp]

}

pred BinHeapCondition30[
  nullDerefBool:univ,
  throw:univ
]{
   equ[nullDerefBool,
      true]
   and 
   equ[throw,
      null]

}

pred BinHeapCondition7[
  nextTemp:univ,
  sibling:univ->univ,
  temp:univ
]{
   not (
     isEmptyOrNull[temp]
     and 
     isEmptyOrNull[nextTemp]
     and 
     isEmptyOrNull[nextTemp]
     and 
     isEmptyOrNull[nextTemp.sibling]
     and 
     isEmptyOrNull[nextTemp]
     and 
     isEmptyOrNull[temp]
   )

}

pred BinHeapCondition31[
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

pred BinHeapCondition18[
  prevTemp:univ
]{
   isEmptyOrNull[prevTemp]

}

pred BinHeapCondition62[
  head:univ->univ,
  thiz:univ
]{
   equ[thiz.head,
      null]

}

pred BinHeapCondition63[
  head:univ->univ,
  thiz:univ
]{
   not (
     equ[thiz.head,
        null]
   )

}

pred BinHeapCondition19[
  prevTemp:univ
]{
   not (
     isEmptyOrNull[prevTemp])

}

pred BinHeapCondition14[
  temp:univ
]{
   isEmptyOrNull[temp]

}

pred BinHeapCondition15[
  temp:univ
]{
   not (
     isEmptyOrNull[temp])

}

pred BinHeapCondition38[
  temp1:univ
]{
   isEmptyOrNull[temp1]

}

pred BinHeapCondition39[
  temp1:univ
]{
   not (
     isEmptyOrNull[temp1])

}

pred BinHeap_object_invariant[
  child:univ->univ,
  degree:univ->univ,
  element:univ->univ,
  head:univ->univ,
  nextData:univ->univ,
  parent:univ->univ,
  sibling:univ->univ,
  size:univ->univ,
  thiz:univ
]{
   (
     all n:BinHeapNode | {
       isSubset[n,
               fun_set_difference[(thiz.head).(fun_reflexive_closure[sibling+child]),null]]
       implies 
               (
                 neq[n.element,
                    null]
                 and 
                 (
                   neq[n.parent,
                      null]
                   implies 
                           isSubset[n.element,
                                   fun_set_difference[((n.parent).element).(fun_reflexive_closure[nextData]),null]]
                 )
                 and 
                 (
                   neq[n.child,
                      null]
                   implies 
                           isNotSubset[n,
                                      fun_set_difference[(n.child).(fun_reflexive_closure[sibling+child]),null]]
                 )
                 and 
                 (
                   neq[n.sibling,
                      null]
                   implies 
                           isNotSubset[n,
                                      fun_set_difference[(n.sibling).(fun_reflexive_closure[sibling+child]),null]]
                 )
                 and 
                 (
                   (
                     neq[n.child,
                        null]
                     and 
                     neq[n.sibling,
                        null]
                   )
                   implies 
                           (
                             no m:BinHeapNode | {
                               isSubset[m,
                                       fun_set_difference[(n.child).(fun_reflexive_closure[child+sibling]),null]]
                               and 
                               isSubset[m,
                                       fun_set_difference[(n.sibling).(fun_reflexive_closure[child+sibling]),null]]
                             
                             }
                           )
                 )
                 and 
                 gte[n.degree,
                    0]
                 and 
                 (
                   equ[n.child,
                      null]
                   implies 
                           equ[n.degree,
                              0]
                 )
                 and 
                 (
                   neq[n.child,
                      null]
                   implies 
                           equ[n.degree,
                              #(fun_set_difference[(n.child).(fun_reflexive_closure[sibling]),null])]
                 )
                 and 
                 equ[#(fun_set_difference[(n.child)+(((n.child).child).(fun_reflexive_closure[child+sibling])),null]),
                    #(fun_set_difference[(n.child)+(((n.child).sibling).(fun_reflexive_closure[child+sibling])),null])]
                 and 
                 (
                   neq[n.child,
                      null]
                   implies 
                           (
                             all m:BinHeapNode | {
                               isSubset[m,
                                       fun_set_difference[(n.child).(fun_reflexive_closure[sibling]),null]]
                               implies 
                                       equ[m.parent,
                                          n]
                             
                             }
                           )
                 )
                 and 
                 (
                   (
                     neq[n.sibling,
                        null]
                     and 
                     neq[n.parent,
                        null]
                   )
                   implies 
                           gt[n.degree,
                             (n.sibling).degree]
                 )
               )
     
     }
   )
   and 
   equ[thiz.size,
      #(fun_set_difference[(thiz.head).(fun_reflexive_closure[sibling+child]),null])]
   and 
   (
     all n:BinHeapNode | {
       isSubset[n,
               fun_set_difference[(thiz.head).(fun_reflexive_closure[sibling]),null]]
       implies 
               (
                 (
                   neq[n.sibling,
                      null]
                   implies 
                           lt[n.degree,
                             (n.sibling).degree]
                 )
                 and 
                 equ[n.parent,
                    null]
               )
     
     }
   )

}

pred BinHeapCondition51[
  degree:univ->univ,
  temp1:univ,
  temp2:univ
]{
   not (
     equ[temp1.degree,
        temp2.degree]
   )

}

pred BinHeapCondition44[
  degree:univ->univ,
  sibling:univ->univ,
  temp1:univ,
  temp2:univ
]{
   equ[temp1.sibling,
      null]
   or 
   gt[(temp1.sibling).degree,
     temp2.degree]

}

pred BinHeapCondition12[
  nextTemp:univ,
  temp:univ
]{
   isEmptyOrNull[nextTemp]
   and 
   isEmptyOrNull[temp]

}

pred BinHeapCondition45[
  degree:univ->univ,
  sibling:univ->univ,
  temp1:univ,
  temp2:univ
]{
   not (
     equ[temp1.sibling,
        null]
     or 
     gt[(temp1.sibling).degree,
       temp2.degree]
   )

}

pred BinHeapCondition64[
  child:univ->univ,
  head:univ->univ,
  nodes:univ->univ,
  sibling:univ->univ,
  thiz:univ
]{
   BinHeap_nodes_abstraction[child,
                            head,
                            nodes,
                            sibling,
                            thiz]

}

pred BinHeapCondition33[
  temp1:univ,
  temp2:univ
]{
   not (
     isEmptyOrNull[temp1]
     and 
     isEmptyOrNull[temp2]
   )

}

pred BinHeapCondition13[
  nextTemp:univ,
  temp:univ
]{
   not (
     isEmptyOrNull[nextTemp]
     and 
     isEmptyOrNull[temp]
   )

}

pred BinHeapCondition29[
  nextTemp:univ
]{
   not (
     neq[nextTemp,
        null]
   )

}

pred BinHeapCondition35[
  temp2:univ
]{
   not (
     isEmptyOrNull[temp2])

}

pred BinHeapCondition28[
  nextTemp:univ
]{
   neq[nextTemp,
      null]

}

pred BinHeapCondition34[
  temp2:univ
]{
   isEmptyOrNull[temp2]

}

pred BinHeapCondition17[
  temp:univ
]{
   not (
     isEmptyOrNull[temp]
     and 
     isEmptyOrNull[temp]
   )

}

pred BinHeapCondition16[
  temp:univ
]{
   isEmptyOrNull[temp]
   and 
   isEmptyOrNull[temp]

}

pred BinHeapCondition8[
  nextTemp:univ,
  temp:univ
]{
   isEmptyOrNull[temp]
   and 
   isEmptyOrNull[nextTemp]

}

pred BinHeapCondition24[
  lte:univ
]{
   equ[lte,
      true]

}

pred BinHeapCondition9[
  nextTemp:univ,
  temp:univ
]{
   not (
     isEmptyOrNull[temp]
     and 
     isEmptyOrNull[nextTemp]
   )

}

pred BinHeapCondition53[
  temp1:univ,
  temp2:univ
]{
   not (
     neq[temp1,
        null]
     and 
     neq[temp2,
        null]
   )

}

pred BinHeapCondition42[
  sibling:univ->univ,
  temp1:univ,
  temp2:univ
]{
   isEmptyOrNull[temp1]
   and 
   isEmptyOrNull[temp1.sibling]
   and 
   isEmptyOrNull[temp1]
   and 
   isEmptyOrNull[temp2]

}

pred BinHeap_requires[
  child:univ->univ,
  data_value:univ,
  degree:univ->univ,
  fresh_node:univ,
  nodes:univ->univ,
  parent:univ->univ,
  sibling:univ->univ,
  thiz:univ
]{
   isNotSubset[fresh_node,
              thiz.nodes]
   and 
   equ[fresh_node.degree,
      0]
   and 
   equ[fresh_node.parent,
      null]
   and 
   equ[fresh_node.child,
      null]
   and 
   equ[fresh_node.sibling,
      null]
   and 
   neq[data_value,
      null]

}

pred BinHeapCondition25[
  lte:univ
]{
   not (
     equ[lte,
        true]
   )

}

pred BinHeapCondition43[
  sibling:univ->univ,
  temp1:univ,
  temp2:univ
]{
   not (
     isEmptyOrNull[temp1]
     and 
     isEmptyOrNull[temp1.sibling]
     and 
     isEmptyOrNull[temp1]
     and 
     isEmptyOrNull[temp2]
   )

}

pred BinHeapCondition50[
  degree:univ->univ,
  temp1:univ,
  temp2:univ
]{
   equ[temp1.degree,
      temp2.degree]

}

pred BinHeapCondition52[
  temp1:univ,
  temp2:univ
]{
   neq[temp1,
      null]
   and 
   neq[temp2,
      null]

}

pred BinHeapCondition26[
  degree:univ->univ,
  nextTemp:univ,
  sibling:univ->univ,
  temp:univ
]{
   neq[temp.degree,
      nextTemp.degree]
   or 
   (
     neq[nextTemp.sibling,
        null]
     and 
     equ[(nextTemp.sibling).degree,
        temp.degree]
   )

}

pred BinHeapCondition27[
  degree:univ->univ,
  nextTemp:univ,
  sibling:univ->univ,
  temp:univ
]{
   not (
     neq[temp.degree,
        nextTemp.degree]
     or 
     (
       neq[nextTemp.sibling,
          null]
       and 
       equ[(nextTemp.sibling).degree,
          temp.degree]
     )
   )

}

pred precondition_BinHeap_insert_0[
  child:univ->univ,
  data_value:univ,
  degree:univ->univ,
  element:univ->univ,
  fresh_node:univ,
  head:univ->univ,
  nextData:univ->univ,
  nodes:univ->univ,
  parent:univ->univ,
  sibling:univ->univ,
  size:univ->univ,
  thiz:univ,
  throw:univ
]{
   equ[throw,
      null]
   and 
   BinHeap_requires[child,
                   data_value,
                   degree,
                   fresh_node,
                   nodes,
                   parent,
                   sibling,
                   thiz]
   and 
   BinHeap_nodes_abstraction[child,
                            head,
                            nodes,
                            sibling,
                            thiz]
   and 
   BinHeap_object_invariant[child,
                           degree,
                           element,
                           head,
                           nextData,
                           parent,
                           sibling,
                           size,
                           thiz]
   and 
   Data_object_invariant[nextData]

}

pred BinHeapCondition23[
  nextTemp:univ
]{
   not (
     isEmptyOrNull[nextTemp]
     and 
     isEmptyOrNull[nextTemp]
   )

}

pred BinHeapCondition10[
  nextTemp:univ
]{
   isEmptyOrNull[nextTemp]

}

pred BinHeapCondition11[
  nextTemp:univ
]{
   not (
     isEmptyOrNull[nextTemp])

}

pred BinHeapCondition47[
  head:univ->univ,
  thiz:univ,
  tmp:univ
]{
   not (
     equ[tmp,
        thiz.head]
   )

}

pred BinHeapCondition46[
  head:univ->univ,
  thiz:univ,
  tmp:univ
]{
   equ[tmp,
      thiz.head]

}

pred BinHeapCondition22[
  nextTemp:univ
]{
   isEmptyOrNull[nextTemp]
   and 
   isEmptyOrNull[nextTemp]

}
//-------------- amelia_data_D10--------------//
sig D10 extends Data {}
{}





//-------------- amelia_data_D8--------------//
sig D8 extends Data {}
{}





//-------------- amelia_binheap_BinHeapNode--------------//
sig BinHeapNode extends Object {}
{}





//-------------- amelia_data_D7--------------//
sig D7 extends Data {}
{}





//-------------- amelia_data_D9--------------//
sig D9 extends Data {}
{}





//-------------- amelia_data_D19--------------//
sig D19 extends Data {}
{}





//-------------- amelia_data_D4--------------//
sig D4 extends Data {}
{}





//-------------- amelia_data_D18--------------//
sig D18 extends Data {}
{}





//-------------- amelia_data_D3--------------//
sig D3 extends Data {}
{}





//-------------- amelia_data_D17--------------//
sig D17 extends Data {}
{}





//-------------- amelia_data_D6--------------//
sig D6 extends Data {}
{}





//-------------- amelia_data_D16--------------//
sig D16 extends Data {}
{}





//-------------- amelia_data_D5--------------//
sig D5 extends Data {}
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


//-------------- java_lang_NullPointerException--------------//
abstract sig NullPointerException extends RuntimeException {}
{}



one
sig NullPointerExceptionLit extends NullPointerException {}
{}


//-------------- amelia_data_Data--------------//
abstract sig Data extends Object {}
{}




pred DataCondition73[
  thiz:univ
]{
   not (
     instanceOf[thiz,
               D3]
   )

}

pred DataCondition37[
  data:univ
]{
   not (
     instanceOf[data,
               D18]
     or 
     instanceOf[data,
               D19]
   )

}

pred DataCondition36[
  data:univ
]{
   instanceOf[data,
             D18]
   or 
   instanceOf[data,
             D19]

}

pred DataCondition10[
  data:univ
]{
   instanceOf[data,
             D5]
   or 
   instanceOf[data,
             D6]
   
   or 
   instanceOf[data,
             D7]
   
   or 
   instanceOf[data,
             D8]
   
   or 
   instanceOf[data,
             D9]
   
   or 
   instanceOf[data,
             D10]
   
   or 
   instanceOf[data,
             D11]
   
   or 
   instanceOf[data,
             D12]
   
   or 
   instanceOf[data,
             D13]
   
   or 
   instanceOf[data,
             D14]
   
   or 
   instanceOf[data,
             D15]
   
   or 
   instanceOf[data,
             D16]
   
   or 
   instanceOf[data,
             D17]
   
   or 
   instanceOf[data,
             D18]
   
   or 
   instanceOf[data,
             D19]

}

pred DataCondition27[
  data:univ
]{
   not (
     instanceOf[data,
               D13]
     or 
     instanceOf[data,
               D14]
     
     or 
     instanceOf[data,
               D15]
     
     or 
     instanceOf[data,
               D16]
     
     or 
     instanceOf[data,
               D17]
     
     or 
     instanceOf[data,
               D18]
     
     or 
     instanceOf[data,
               D19]
   )

}

pred DataCondition33[
  data:univ
]{
   not (
     instanceOf[data,
               D16]
     or 
     instanceOf[data,
               D17]
     
     or 
     instanceOf[data,
               D18]
     
     or 
     instanceOf[data,
               D19]
   )

}

pred DataCondition32[
  data:univ
]{
   instanceOf[data,
             D16]
   or 
   instanceOf[data,
             D17]
   
   or 
   instanceOf[data,
             D18]
   
   or 
   instanceOf[data,
             D19]

}

pred DataCondition47[
  thiz:univ
]{
   not (
     instanceOf[thiz,
               D16]
   )

}

pred DataCondition46[
  thiz:univ
]{
   instanceOf[thiz,
             D16]

}

pred DataCondition26[
  data:univ
]{
   instanceOf[data,
             D13]
   or 
   instanceOf[data,
             D14]
   
   or 
   instanceOf[data,
             D15]
   
   or 
   instanceOf[data,
             D16]
   
   or 
   instanceOf[data,
             D17]
   
   or 
   instanceOf[data,
             D18]
   
   or 
   instanceOf[data,
             D19]

}

pred DataCondition11[
  data:univ
]{
   not (
     instanceOf[data,
               D5]
     or 
     instanceOf[data,
               D6]
     
     or 
     instanceOf[data,
               D7]
     
     or 
     instanceOf[data,
               D8]
     
     or 
     instanceOf[data,
               D9]
     
     or 
     instanceOf[data,
               D10]
     
     or 
     instanceOf[data,
               D11]
     
     or 
     instanceOf[data,
               D12]
     
     or 
     instanceOf[data,
               D13]
     
     or 
     instanceOf[data,
               D14]
     
     or 
     instanceOf[data,
               D15]
     
     or 
     instanceOf[data,
               D16]
     
     or 
     instanceOf[data,
               D17]
     
     or 
     instanceOf[data,
               D18]
     
     or 
     instanceOf[data,
               D19]
   )

}

pred DataCondition38[
  data:univ
]{
   instanceOf[data,
             D19]

}

pred DataCondition49[
  thiz:univ
]{
   not (
     instanceOf[thiz,
               D15]
   )

}

pred DataCondition7[
  data:univ
]{
   not (
     instanceOf[data,
               D3]
     or 
     instanceOf[data,
               D4]
     
     or 
     instanceOf[data,
               D5]
     
     or 
     instanceOf[data,
               D6]
     
     or 
     instanceOf[data,
               D7]
     
     or 
     instanceOf[data,
               D8]
     
     or 
     instanceOf[data,
               D9]
     
     or 
     instanceOf[data,
               D10]
     
     or 
     instanceOf[data,
               D11]
     
     or 
     instanceOf[data,
               D12]
     
     or 
     instanceOf[data,
               D13]
     
     or 
     instanceOf[data,
               D14]
     
     or 
     instanceOf[data,
               D15]
     
     or 
     instanceOf[data,
               D16]
     
     or 
     instanceOf[data,
               D17]
     
     or 
     instanceOf[data,
               D18]
     
     or 
     instanceOf[data,
               D19]
   )

}

pred DataCondition6[
  data:univ
]{
   instanceOf[data,
             D3]
   or 
   instanceOf[data,
             D4]
   
   or 
   instanceOf[data,
             D5]
   
   or 
   instanceOf[data,
             D6]
   
   or 
   instanceOf[data,
             D7]
   
   or 
   instanceOf[data,
             D8]
   
   or 
   instanceOf[data,
             D9]
   
   or 
   instanceOf[data,
             D10]
   
   or 
   instanceOf[data,
             D11]
   
   or 
   instanceOf[data,
             D12]
   
   or 
   instanceOf[data,
             D13]
   
   or 
   instanceOf[data,
             D14]
   
   or 
   instanceOf[data,
             D15]
   
   or 
   instanceOf[data,
             D16]
   
   or 
   instanceOf[data,
             D17]
   
   or 
   instanceOf[data,
             D18]
   
   or 
   instanceOf[data,
             D19]

}

pred DataCondition62[
  thiz:univ
]{
   instanceOf[thiz,
             D8]

}

pred DataCondition63[
  thiz:univ
]{
   not (
     instanceOf[thiz,
               D8]
   )

}

pred DataCondition39[
  data:univ
]{
   not (
     instanceOf[data,
               D19]
   )

}

pred DataCondition72[
  thiz:univ
]{
   instanceOf[thiz,
             D3]

}

pred DataCondition74[
  thiz:univ
]{
   instanceOf[thiz,
             D2]

}

pred DataCondition75[
  thiz:univ
]{
   not (
     instanceOf[thiz,
               D2]
   )

}

pred DataCondition25[
  data:univ
]{
   not (
     instanceOf[data,
               D12]
     or 
     instanceOf[data,
               D13]
     
     or 
     instanceOf[data,
               D14]
     
     or 
     instanceOf[data,
               D15]
     
     or 
     instanceOf[data,
               D16]
     
     or 
     instanceOf[data,
               D17]
     
     or 
     instanceOf[data,
               D18]
     
     or 
     instanceOf[data,
               D19]
   )

}

pred DataCondition24[
  data:univ
]{
   instanceOf[data,
             D12]
   or 
   instanceOf[data,
             D13]
   
   or 
   instanceOf[data,
             D14]
   
   or 
   instanceOf[data,
             D15]
   
   or 
   instanceOf[data,
             D16]
   
   or 
   instanceOf[data,
             D17]
   
   or 
   instanceOf[data,
             D18]
   
   or 
   instanceOf[data,
             D19]

}

pred DataCondition34[
  data:univ
]{
   instanceOf[data,
             D17]
   or 
   instanceOf[data,
             D18]
   
   or 
   instanceOf[data,
             D19]

}

pred DataCondition35[
  data:univ
]{
   not (
     instanceOf[data,
               D17]
     or 
     instanceOf[data,
               D18]
     
     or 
     instanceOf[data,
               D19]
   )

}

pred DataCondition14[
  data:univ
]{
   instanceOf[data,
             D7]
   or 
   instanceOf[data,
             D8]
   
   or 
   instanceOf[data,
             D9]
   
   or 
   instanceOf[data,
             D10]
   
   or 
   instanceOf[data,
             D11]
   
   or 
   instanceOf[data,
             D12]
   
   or 
   instanceOf[data,
             D13]
   
   or 
   instanceOf[data,
             D14]
   
   or 
   instanceOf[data,
             D15]
   
   or 
   instanceOf[data,
             D16]
   
   or 
   instanceOf[data,
             D17]
   
   or 
   instanceOf[data,
             D18]
   
   or 
   instanceOf[data,
             D19]

}

pred DataCondition15[
  data:univ
]{
   not (
     instanceOf[data,
               D7]
     or 
     instanceOf[data,
               D8]
     
     or 
     instanceOf[data,
               D9]
     
     or 
     instanceOf[data,
               D10]
     
     or 
     instanceOf[data,
               D11]
     
     or 
     instanceOf[data,
               D12]
     
     or 
     instanceOf[data,
               D13]
     
     or 
     instanceOf[data,
               D14]
     
     or 
     instanceOf[data,
               D15]
     
     or 
     instanceOf[data,
               D16]
     
     or 
     instanceOf[data,
               D17]
     
     or 
     instanceOf[data,
               D18]
     
     or 
     instanceOf[data,
               D19]
   )

}

pred DataCondition45[
  thiz:univ
]{
   not (
     instanceOf[thiz,
               D17]
   )

}

pred DataCondition44[
  thiz:univ
]{
   instanceOf[thiz,
             D17]

}

pred DataCondition64[
  thiz:univ
]{
   instanceOf[thiz,
             D7]

}

pred DataCondition65[
  thiz:univ
]{
   not (
     instanceOf[thiz,
               D7]
   )

}

pred DataCondition0[
  throw:univ
]{
   equ[throw,
      null]

}

pred DataCondition1[
  throw:univ
]{
   not (
     equ[throw,
        null]
   )

}

pred DataCondition76[
  thiz:univ
]{
   instanceOf[thiz,
             D1]

}

pred DataCondition77[
  thiz:univ
]{
   not (
     instanceOf[thiz,
               D1]
   )

}

pred DataCondition54[
  thiz:univ
]{
   instanceOf[thiz,
             D12]

}

pred DataCondition55[
  thiz:univ
]{
   not (
     instanceOf[thiz,
               D12]
   )

}

pred DataCondition42[
  thiz:univ
]{
   instanceOf[thiz,
             D18]

}

pred DataCondition43[
  thiz:univ
]{
   not (
     instanceOf[thiz,
               D18]
   )

}

pred DataCondition66[
  thiz:univ
]{
   instanceOf[thiz,
             D6]

}

pred DataCondition31[
  data:univ
]{
   not (
     instanceOf[data,
               D15]
     or 
     instanceOf[data,
               D16]
     
     or 
     instanceOf[data,
               D17]
     
     or 
     instanceOf[data,
               D18]
     
     or 
     instanceOf[data,
               D19]
   )

}

pred DataCondition53[
  thiz:univ
]{
   not (
     instanceOf[thiz,
               D13]
   )

}

pred DataCondition30[
  data:univ
]{
   instanceOf[data,
             D15]
   or 
   instanceOf[data,
             D16]
   
   or 
   instanceOf[data,
             D17]
   
   or 
   instanceOf[data,
             D18]
   
   or 
   instanceOf[data,
             D19]

}

pred DataCondition52[
  thiz:univ
]{
   instanceOf[thiz,
             D13]

}

pred DataCondition67[
  thiz:univ
]{
   not (
     instanceOf[thiz,
               D6]
   )

}

pred DataCondition57[
  thiz:univ
]{
   not (
     instanceOf[thiz,
               D11]
   )

}

pred DataCondition83[
  lt:univ
]{
   not (
     equ[lt,
        true]
   )

}

pred DataCondition56[
  thiz:univ
]{
   instanceOf[thiz,
             D11]

}

pred DataCondition82[
  lt:univ
]{
   equ[lt,
      true]

}

pred DataCondition29[
  data:univ
]{
   not (
     instanceOf[data,
               D14]
     or 
     instanceOf[data,
               D15]
     
     or 
     instanceOf[data,
               D16]
     
     or 
     instanceOf[data,
               D17]
     
     or 
     instanceOf[data,
               D18]
     
     or 
     instanceOf[data,
               D19]
   )

}

pred DataCondition28[
  data:univ
]{
   instanceOf[data,
             D14]
   or 
   instanceOf[data,
             D15]
   
   or 
   instanceOf[data,
             D16]
   
   or 
   instanceOf[data,
             D17]
   
   or 
   instanceOf[data,
             D18]
   
   or 
   instanceOf[data,
             D19]

}

pred DataCondition19[
  data:univ
]{
   not (
     instanceOf[data,
               D9]
     or 
     instanceOf[data,
               D10]
     
     or 
     instanceOf[data,
               D11]
     
     or 
     instanceOf[data,
               D12]
     
     or 
     instanceOf[data,
               D13]
     
     or 
     instanceOf[data,
               D14]
     
     or 
     instanceOf[data,
               D15]
     
     or 
     instanceOf[data,
               D16]
     
     or 
     instanceOf[data,
               D17]
     
     or 
     instanceOf[data,
               D18]
     
     or 
     instanceOf[data,
               D19]
   )

}

pred DataCondition18[
  data:univ
]{
   instanceOf[data,
             D9]
   or 
   instanceOf[data,
             D10]
   
   or 
   instanceOf[data,
             D11]
   
   or 
   instanceOf[data,
             D12]
   
   or 
   instanceOf[data,
             D13]
   
   or 
   instanceOf[data,
             D14]
   
   or 
   instanceOf[data,
             D15]
   
   or 
   instanceOf[data,
             D16]
   
   or 
   instanceOf[data,
             D17]
   
   or 
   instanceOf[data,
             D18]
   
   or 
   instanceOf[data,
             D19]

}

pred DataCondition50[
  thiz:univ
]{
   instanceOf[thiz,
             D14]

}

pred DataCondition5[
  data:univ
]{
   not (
     instanceOf[data,
               D2]
     or 
     instanceOf[data,
               D3]
     
     or 
     instanceOf[data,
               D4]
     
     or 
     instanceOf[data,
               D5]
     
     or 
     instanceOf[data,
               D6]
     
     or 
     instanceOf[data,
               D7]
     
     or 
     instanceOf[data,
               D8]
     
     or 
     instanceOf[data,
               D9]
     
     or 
     instanceOf[data,
               D10]
     
     or 
     instanceOf[data,
               D11]
     
     or 
     instanceOf[data,
               D12]
     
     or 
     instanceOf[data,
               D13]
     
     or 
     instanceOf[data,
               D14]
     
     or 
     instanceOf[data,
               D15]
     
     or 
     instanceOf[data,
               D16]
     
     or 
     instanceOf[data,
               D17]
     
     or 
     instanceOf[data,
               D18]
     
     or 
     instanceOf[data,
               D19]
   )

}

pred DataCondition81[
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

pred DataCondition80[
  nullDerefBool:univ,
  throw:univ
]{
   equ[nullDerefBool,
      true]
   and 
   equ[throw,
      null]

}

pred DataCondition48[
  thiz:univ
]{
   instanceOf[thiz,
             D15]

}

pred DataCondition69[
  thiz:univ
]{
   not (
     instanceOf[thiz,
               D5]
   )

}

pred DataCondition41[
  thiz:univ
]{
   not (
     instanceOf[thiz,
               D19]
   )

}

pred DataCondition68[
  thiz:univ
]{
   instanceOf[thiz,
             D5]

}

pred DataCondition61[
  thiz:univ
]{
   not (
     instanceOf[thiz,
               D9]
   )

}

pred DataCondition60[
  thiz:univ
]{
   instanceOf[thiz,
             D9]

}

pred DataCondition40[
  thiz:univ
]{
   instanceOf[thiz,
             D19]

}

pred DataCondition21[
  data:univ
]{
   not (
     instanceOf[data,
               D10]
     or 
     instanceOf[data,
               D11]
     
     or 
     instanceOf[data,
               D12]
     
     or 
     instanceOf[data,
               D13]
     
     or 
     instanceOf[data,
               D14]
     
     or 
     instanceOf[data,
               D15]
     
     or 
     instanceOf[data,
               D16]
     
     or 
     instanceOf[data,
               D17]
     
     or 
     instanceOf[data,
               D18]
     
     or 
     instanceOf[data,
               D19]
   )

}

pred DataCondition4[
  data:univ
]{
   instanceOf[data,
             D2]
   or 
   instanceOf[data,
             D3]
   
   or 
   instanceOf[data,
             D4]
   
   or 
   instanceOf[data,
             D5]
   
   or 
   instanceOf[data,
             D6]
   
   or 
   instanceOf[data,
             D7]
   
   or 
   instanceOf[data,
             D8]
   
   or 
   instanceOf[data,
             D9]
   
   or 
   instanceOf[data,
             D10]
   
   or 
   instanceOf[data,
             D11]
   
   or 
   instanceOf[data,
             D12]
   
   or 
   instanceOf[data,
             D13]
   
   or 
   instanceOf[data,
             D14]
   
   or 
   instanceOf[data,
             D15]
   
   or 
   instanceOf[data,
             D16]
   
   or 
   instanceOf[data,
             D17]
   
   or 
   instanceOf[data,
             D18]
   
   or 
   instanceOf[data,
             D19]

}

pred DataCondition78[
  thiz:univ
]{
   instanceOf[thiz,
             D0]

}

pred DataCondition8[
  data:univ
]{
   instanceOf[data,
             D4]
   or 
   instanceOf[data,
             D5]
   
   or 
   instanceOf[data,
             D6]
   
   or 
   instanceOf[data,
             D7]
   
   or 
   instanceOf[data,
             D8]
   
   or 
   instanceOf[data,
             D9]
   
   or 
   instanceOf[data,
             D10]
   
   or 
   instanceOf[data,
             D11]
   
   or 
   instanceOf[data,
             D12]
   
   or 
   instanceOf[data,
             D13]
   
   or 
   instanceOf[data,
             D14]
   
   or 
   instanceOf[data,
             D15]
   
   or 
   instanceOf[data,
             D16]
   
   or 
   instanceOf[data,
             D17]
   
   or 
   instanceOf[data,
             D18]
   
   or 
   instanceOf[data,
             D19]

}

pred DataCondition51[
  thiz:univ
]{
   not (
     instanceOf[thiz,
               D14]
   )

}

pred DataCondition79[
  thiz:univ
]{
   not (
     instanceOf[thiz,
               D0]
   )

}

pred DataCondition9[
  data:univ
]{
   not (
     instanceOf[data,
               D4]
     or 
     instanceOf[data,
               D5]
     
     or 
     instanceOf[data,
               D6]
     
     or 
     instanceOf[data,
               D7]
     
     or 
     instanceOf[data,
               D8]
     
     or 
     instanceOf[data,
               D9]
     
     or 
     instanceOf[data,
               D10]
     
     or 
     instanceOf[data,
               D11]
     
     or 
     instanceOf[data,
               D12]
     
     or 
     instanceOf[data,
               D13]
     
     or 
     instanceOf[data,
               D14]
     
     or 
     instanceOf[data,
               D15]
     
     or 
     instanceOf[data,
               D16]
     
     or 
     instanceOf[data,
               D17]
     
     or 
     instanceOf[data,
               D18]
     
     or 
     instanceOf[data,
               D19]
   )

}

pred DataCondition23[
  data:univ
]{
   not (
     instanceOf[data,
               D11]
     or 
     instanceOf[data,
               D12]
     
     or 
     instanceOf[data,
               D13]
     
     or 
     instanceOf[data,
               D14]
     
     or 
     instanceOf[data,
               D15]
     
     or 
     instanceOf[data,
               D16]
     
     or 
     instanceOf[data,
               D17]
     
     or 
     instanceOf[data,
               D18]
     
     or 
     instanceOf[data,
               D19]
   )

}

pred DataCondition20[
  data:univ
]{
   instanceOf[data,
             D10]
   or 
   instanceOf[data,
             D11]
   
   or 
   instanceOf[data,
             D12]
   
   or 
   instanceOf[data,
             D13]
   
   or 
   instanceOf[data,
             D14]
   
   or 
   instanceOf[data,
             D15]
   
   or 
   instanceOf[data,
             D16]
   
   or 
   instanceOf[data,
             D17]
   
   or 
   instanceOf[data,
             D18]
   
   or 
   instanceOf[data,
             D19]

}

pred DataCondition2[
  data:univ
]{
   instanceOf[data,
             D1]
   or 
   instanceOf[data,
             D2]
   
   or 
   instanceOf[data,
             D3]
   
   or 
   instanceOf[data,
             D4]
   
   or 
   instanceOf[data,
             D5]
   
   or 
   instanceOf[data,
             D6]
   
   or 
   instanceOf[data,
             D7]
   
   or 
   instanceOf[data,
             D8]
   
   or 
   instanceOf[data,
             D9]
   
   or 
   instanceOf[data,
             D10]
   
   or 
   instanceOf[data,
             D11]
   
   or 
   instanceOf[data,
             D12]
   
   or 
   instanceOf[data,
             D13]
   
   or 
   instanceOf[data,
             D14]
   
   or 
   instanceOf[data,
             D15]
   
   or 
   instanceOf[data,
             D16]
   
   or 
   instanceOf[data,
             D17]
   
   or 
   instanceOf[data,
             D18]
   
   or 
   instanceOf[data,
             D19]

}

pred DataCondition85[
  data:univ,
  thiz:univ
]{
   not (
     equ[thiz,
        data]
   )

}

pred DataCondition22[
  data:univ
]{
   instanceOf[data,
             D11]
   or 
   instanceOf[data,
             D12]
   
   or 
   instanceOf[data,
             D13]
   
   or 
   instanceOf[data,
             D14]
   
   or 
   instanceOf[data,
             D15]
   
   or 
   instanceOf[data,
             D16]
   
   or 
   instanceOf[data,
             D17]
   
   or 
   instanceOf[data,
             D18]
   
   or 
   instanceOf[data,
             D19]

}

pred DataCondition3[
  data:univ
]{
   not (
     instanceOf[data,
               D1]
     or 
     instanceOf[data,
               D2]
     
     or 
     instanceOf[data,
               D3]
     
     or 
     instanceOf[data,
               D4]
     
     or 
     instanceOf[data,
               D5]
     
     or 
     instanceOf[data,
               D6]
     
     or 
     instanceOf[data,
               D7]
     
     or 
     instanceOf[data,
               D8]
     
     or 
     instanceOf[data,
               D9]
     
     or 
     instanceOf[data,
               D10]
     
     or 
     instanceOf[data,
               D11]
     
     or 
     instanceOf[data,
               D12]
     
     or 
     instanceOf[data,
               D13]
     
     or 
     instanceOf[data,
               D14]
     
     or 
     instanceOf[data,
               D15]
     
     or 
     instanceOf[data,
               D16]
     
     or 
     instanceOf[data,
               D17]
     
     or 
     instanceOf[data,
               D18]
     
     or 
     instanceOf[data,
               D19]
   )

}

pred DataCondition84[
  data:univ,
  thiz:univ
]{
   equ[thiz,
      data]

}

pred DataCondition70[
  thiz:univ
]{
   instanceOf[thiz,
             D4]

}

pred DataCondition59[
  thiz:univ
]{
   not (
     instanceOf[thiz,
               D10]
   )

}

pred DataCondition71[
  thiz:univ
]{
   not (
     instanceOf[thiz,
               D4]
   )

}

pred DataCondition58[
  thiz:univ
]{
   instanceOf[thiz,
             D10]

}

pred DataCondition17[
  data:univ
]{
   not (
     instanceOf[data,
               D8]
     or 
     instanceOf[data,
               D9]
     
     or 
     instanceOf[data,
               D10]
     
     or 
     instanceOf[data,
               D11]
     
     or 
     instanceOf[data,
               D12]
     
     or 
     instanceOf[data,
               D13]
     
     or 
     instanceOf[data,
               D14]
     
     or 
     instanceOf[data,
               D15]
     
     or 
     instanceOf[data,
               D16]
     
     or 
     instanceOf[data,
               D17]
     
     or 
     instanceOf[data,
               D18]
     
     or 
     instanceOf[data,
               D19]
   )

}

pred DataCondition16[
  data:univ
]{
   instanceOf[data,
             D8]
   or 
   instanceOf[data,
             D9]
   
   or 
   instanceOf[data,
             D10]
   
   or 
   instanceOf[data,
             D11]
   
   or 
   instanceOf[data,
             D12]
   
   or 
   instanceOf[data,
             D13]
   
   or 
   instanceOf[data,
             D14]
   
   or 
   instanceOf[data,
             D15]
   
   or 
   instanceOf[data,
             D16]
   
   or 
   instanceOf[data,
             D17]
   
   or 
   instanceOf[data,
             D18]
   
   or 
   instanceOf[data,
             D19]

}

pred DataCondition12[
  data:univ
]{
   instanceOf[data,
             D6]
   or 
   instanceOf[data,
             D7]
   
   or 
   instanceOf[data,
             D8]
   
   or 
   instanceOf[data,
             D9]
   
   or 
   instanceOf[data,
             D10]
   
   or 
   instanceOf[data,
             D11]
   
   or 
   instanceOf[data,
             D12]
   
   or 
   instanceOf[data,
             D13]
   
   or 
   instanceOf[data,
             D14]
   
   or 
   instanceOf[data,
             D15]
   
   or 
   instanceOf[data,
             D16]
   
   or 
   instanceOf[data,
             D17]
   
   or 
   instanceOf[data,
             D18]
   
   or 
   instanceOf[data,
             D19]

}

pred DataCondition13[
  data:univ
]{
   not (
     instanceOf[data,
               D6]
     or 
     instanceOf[data,
               D7]
     
     or 
     instanceOf[data,
               D8]
     
     or 
     instanceOf[data,
               D9]
     
     or 
     instanceOf[data,
               D10]
     
     or 
     instanceOf[data,
               D11]
     
     or 
     instanceOf[data,
               D12]
     
     or 
     instanceOf[data,
               D13]
     
     or 
     instanceOf[data,
               D14]
     
     or 
     instanceOf[data,
               D15]
     
     or 
     instanceOf[data,
               D16]
     
     or 
     instanceOf[data,
               D17]
     
     or 
     instanceOf[data,
               D18]
     
     or 
     instanceOf[data,
               D19]
   )

}



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


pred Data_data_lte_0[
  thiz_0: Data,
  throw_0: Throwable + null,
  throw_1: Throwable + null,
  throw_2: Throwable + null,
  throw_3: Throwable + null,
  throw_4: Throwable + null,
  return_0: boolean,
  return_1: boolean,
  data_0: Data + null,
  lt_0: boolean,
  lt_1: boolean,
  nullDerefBool_0: boolean,
  nullDerefBool_1: boolean,
  lte_0: boolean,
  lte_1: boolean,
  lte_2: boolean,
  l0_result_0: boolean,
  l0_result_1: boolean,
  l0_result_2: boolean,
  l0_nullDerefBool_0: boolean,
  l0_nullDerefBool_1: boolean
]{
  TruePred[]
  and 
  (
    (
      DataCondition0[throw_0]
      and 
      (
        nullDerefBool_1=false)
    )
    or 
    (
      (
        not (
          DataCondition0[throw_0])
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
      DataCondition0[throw_0]
      and 
      (
        throw_1=null)
    )
    or 
    (
      (
        not (
          DataCondition0[throw_0])
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
      DataCondition0[throw_1]
      and 
      (
        lte_1=false)
    )
    or 
    (
      (
        not (
          DataCondition0[throw_1])
      )
      and 
      TruePred[]
      and 
      (
        lte_0=lte_1)
    )
  )
  and 
  (
    (
      DataCondition84[data_0,
                     thiz_0]
      and 
      (
        (
          DataCondition0[throw_1]
          and 
          (
            lte_2=true)
        )
        or 
        (
          (
            not (
              DataCondition0[throw_1])
          )
          and 
          TruePred[]
          and 
          (
            lte_1=lte_2)
        )
      )
      and 
      (
        l0_result_0=l0_result_2)
      and 
      (
        l0_nullDerefBool_0=l0_nullDerefBool_1)
      and 
      (
        lt_0=lt_1)
      and 
      (
        throw_1=throw_3)
    )
    or 
    (
      (
        not (
          DataCondition84[data_0,
                         thiz_0]
        )
      )
      and 
      TruePred[]
      and 
      (
        (
          DataCondition0[throw_1]
          and 
          Data_data_lt_0[thiz_0,
                        throw_1,
                        throw_2,
                        throw_3,
                        lt_0,
                        lt_1,
                        data_0,
                        l0_result_0,
                        l0_result_1,
                        l0_result_2,
                        l0_nullDerefBool_0,
                        l0_nullDerefBool_1]
        )
        or 
        (
          (
            not (
              DataCondition0[throw_1])
          )
          and 
          TruePred[]
          and 
          (
            l0_result_0=l0_result_2)
          and 
          (
            l0_nullDerefBool_0=l0_nullDerefBool_1)
          and 
          (
            lt_0=lt_1)
          and 
          (
            throw_1=throw_3)
        )
      )
      and 
      (
        (
          DataCondition82[lt_1]
          and 
          (
            (
              DataCondition0[throw_3]
              and 
              (
                lte_2=true)
            )
            or 
            (
              (
                not (
                  DataCondition0[throw_3])
              )
              and 
              TruePred[]
              and 
              (
                lte_1=lte_2)
            )
          )
        )
        or 
        (
          (
            not (
              DataCondition82[lt_1])
          )
          and 
          TruePred[]
          and 
          (
            lte_1=lte_2)
        )
      )
    )
  )
  and 
  (
    (
      DataCondition0[throw_3]
      and 
      (
        return_1=lte_2)
    )
    or 
    (
      (
        not (
          DataCondition0[throw_3])
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
      DataCondition80[nullDerefBool_1,
                     throw_3]
      and 
      (
        (
          DataCondition0[throw_3]
          and 
          (
            throw_4=NullPointerExceptionLit)
        )
        or 
        (
          (
            not (
              DataCondition0[throw_3])
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
          DataCondition80[nullDerefBool_1,
                         throw_3]
        )
      )
      and 
      TruePred[]
      and 
      (
        throw_3=throw_4)
    )
  )

}



pred BinHeap_insert_0[
  thiz_0: BinHeap,
  throw_0: Throwable + null,
  throw_1: Throwable + null,
  throw_2: Throwable + null,
  throw_3: Throwable + null,
  throw_4: Throwable + null,
  throw_5: Throwable + null,
  throw_6: Throwable + null,
  throw_7: Throwable + null,
  throw_8: Throwable + null,
  throw_9: Throwable + null,
  throw_10: Throwable + null,
  throw_11: Throwable + null,
  throw_12: Throwable + null,
  throw_13: Throwable + null,
  throw_14: Throwable + null,
  throw_15: Throwable + null,
  throw_16: Throwable + null,
  throw_17: Throwable + null,
  throw_18: Throwable + null,
  throw_19: Throwable + null,
  throw_20: Throwable + null,
  throw_21: Throwable + null,
  throw_22: Throwable + null,
  throw_23: Throwable + null,
  throw_24: Throwable + null,
  throw_25: Throwable + null,
  throw_26: Throwable + null,
  throw_27: Throwable + null,
  throw_28: Throwable + null,
  throw_29: Throwable + null,
  throw_30: Throwable + null,
  throw_31: Throwable + null,
  throw_32: Throwable + null,
  throw_33: Throwable + null,
  throw_34: Throwable + null,
  throw_35: Throwable + null,
  throw_36: Throwable + null,
  throw_37: Throwable + null,
  throw_38: Throwable + null,
  throw_39: Throwable + null,
  throw_40: Throwable + null,
  throw_41: Throwable + null,
  throw_42: Throwable + null,
  throw_43: Throwable + null,
  throw_44: Throwable + null,
  throw_45: Throwable + null,
  throw_46: Throwable + null,
  fresh_node_0: BinHeapNode + null,
  data_value_0: Data + null,
  head_0: ( BinHeap ) -> one ( BinHeapNode + null ),
  head_1: ( BinHeap ) -> one ( BinHeapNode + null ),
  head_2: ( BinHeap ) -> one ( BinHeapNode + null ),
  head_3: ( BinHeap ) -> one ( BinHeapNode + null ),
  head_4: ( BinHeap ) -> one ( BinHeapNode + null ),
  head_5: ( BinHeap ) -> one ( BinHeapNode + null ),
  head_6: ( BinHeap ) -> one ( BinHeapNode + null ),
  head_7: ( BinHeap ) -> one ( BinHeapNode + null ),
  head_8: ( BinHeap ) -> one ( BinHeapNode + null ),
  head_9: ( BinHeap ) -> one ( BinHeapNode + null ),
  head_10: ( BinHeap ) -> one ( BinHeapNode + null ),
  head_11: ( BinHeap ) -> one ( BinHeapNode + null ),
  head_12: ( BinHeap ) -> one ( BinHeapNode + null ),
  head_13: ( BinHeap ) -> one ( BinHeapNode + null ),
  head_14: ( BinHeap ) -> one ( BinHeapNode + null ),
  head_15: ( BinHeap ) -> one ( BinHeapNode + null ),
  head_16: ( BinHeap ) -> one ( BinHeapNode + null ),
  head_17: ( BinHeap ) -> one ( BinHeapNode + null ),
  head_18: ( BinHeap ) -> one ( BinHeapNode + null ),
  head_19: ( BinHeap ) -> one ( BinHeapNode + null ),
  head_20: ( BinHeap ) -> one ( BinHeapNode + null ),
  degree_0: ( BinHeapNode ) -> one ( Int ),
  degree_1: ( BinHeapNode ) -> one ( Int ),
  degree_2: ( BinHeapNode ) -> one ( Int ),
  degree_3: ( BinHeapNode ) -> one ( Int ),
  degree_4: ( BinHeapNode ) -> one ( Int ),
  degree_5: ( BinHeapNode ) -> one ( Int ),
  degree_6: ( BinHeapNode ) -> one ( Int ),
  degree_7: ( BinHeapNode ) -> one ( Int ),
  degree_8: ( BinHeapNode ) -> one ( Int ),
  degree_9: ( BinHeapNode ) -> one ( Int ),
  degree_10: ( BinHeapNode ) -> one ( Int ),
  sibling_0: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_1: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_2: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_3: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_4: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_5: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_6: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_7: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_8: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_9: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_10: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_11: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_12: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_13: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_14: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_15: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_16: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_17: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_18: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_19: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_20: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_21: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_22: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_23: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_24: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_25: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_26: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_27: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_28: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_29: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_30: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_31: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_32: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_33: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_34: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_35: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_36: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_37: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_38: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_39: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_40: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_41: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  element_0: ( BinHeapNode ) -> one ( Data + null ),
  element_1: ( BinHeapNode ) -> one ( Data + null ),
  child_0: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  child_1: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  child_2: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  child_3: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  child_4: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  child_5: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  child_6: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  child_7: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  child_8: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  child_9: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  child_10: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  parent_0: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  parent_1: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  parent_2: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  parent_3: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  parent_4: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  parent_5: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  parent_6: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  parent_7: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  parent_8: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  parent_9: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  parent_10: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  size_0: ( BinHeap ) -> one ( Int ),
  size_1: ( BinHeap ) -> one ( Int ),
  temp_0_0: BinHeapNode + null,
  temp_0_1: BinHeapNode + null,
  nullDerefBool_0: boolean,
  nullDerefBool_1: boolean,
  nullDerefBool_2: boolean,
  nullDerefBool_3: boolean,
  nullDerefBool_4: boolean,
  nullDerefBool_5: boolean,
  l12_nextTemp_0: BinHeapNode + null,
  l12_nextTemp_1: BinHeapNode + null,
  l12_nextTemp_2: BinHeapNode + null,
  l12_nextTemp_3: BinHeapNode + null,
  l12_nextTemp_4: BinHeapNode + null,
  l12_nextTemp_5: BinHeapNode + null,
  l12_nextTemp_6: BinHeapNode + null,
  l12_nextTemp_7: BinHeapNode + null,
  l12_nextTemp_8: BinHeapNode + null,
  l12_nextTemp_9: BinHeapNode + null,
  l12_nextTemp_10: BinHeapNode + null,
  l12_nextTemp_11: BinHeapNode + null,
  l12_l2_l0_result_0: boolean,
  l12_l2_l0_result_1: boolean,
  l12_l2_l0_result_2: boolean,
  l12_l2_nullDerefBool_0: boolean,
  l12_l2_nullDerefBool_1: boolean,
  l12_l3_lt_0: boolean,
  l12_l3_lt_1: boolean,
  l12_l11_lt_0: boolean,
  l12_l11_lt_1: boolean,
  l12_l9_lte_0: boolean,
  l12_l9_lte_1: boolean,
  l12_l9_lte_2: boolean,
  l12_l4_l0_nullDerefBool_0: boolean,
  l12_l4_l0_nullDerefBool_1: boolean,
  l12_l6_lte_0: boolean,
  l12_l6_lte_1: boolean,
  l12_l6_lte_2: boolean,
  l12_l9_lt_0: boolean,
  l12_l9_lt_1: boolean,
  l12_l5_l0_result_0: boolean,
  l12_l5_l0_result_1: boolean,
  l12_l5_l0_result_2: boolean,
  l12_l8_lte_0: boolean,
  l12_l8_lte_1: boolean,
  l12_l8_lte_2: boolean,
  l12_l8_l0_nullDerefBool_0: boolean,
  l12_l8_l0_nullDerefBool_1: boolean,
  l12_l8_nullDerefBool_0: boolean,
  l12_l8_nullDerefBool_1: boolean,
  l12_l10_lt_0: boolean,
  l12_l10_lt_1: boolean,
  l12_l10_lte_0: boolean,
  l12_l10_lte_1: boolean,
  l12_l10_lte_2: boolean,
  l12_l7_lte_0: boolean,
  l12_l7_lte_1: boolean,
  l12_l7_lte_2: boolean,
  l12_l6_l0_nullDerefBool_0: boolean,
  l12_l6_l0_nullDerefBool_1: boolean,
  l12_l4_lt_0: boolean,
  l12_l4_lt_1: boolean,
  l12_l2_lte_0: boolean,
  l12_l2_lte_1: boolean,
  l12_l2_lte_2: boolean,
  l12_l7_l0_result_0: boolean,
  l12_l7_l0_result_1: boolean,
  l12_l7_l0_result_2: boolean,
  l12_l2_lt_0: boolean,
  l12_l2_lt_1: boolean,
  l12_l4_nullDerefBool_0: boolean,
  l12_l4_nullDerefBool_1: boolean,
  l12_l5_nullDerefBool_0: boolean,
  l12_l5_nullDerefBool_1: boolean,
  l12_l3_l0_nullDerefBool_0: boolean,
  l12_l3_l0_nullDerefBool_1: boolean,
  l12_temp_0: BinHeapNode + null,
  l12_temp_1: BinHeapNode + null,
  l12_temp_2: BinHeapNode + null,
  l12_temp_3: BinHeapNode + null,
  l12_temp_4: BinHeapNode + null,
  l12_temp_5: BinHeapNode + null,
  l12_temp_6: BinHeapNode + null,
  l12_temp_7: BinHeapNode + null,
  l12_temp_8: BinHeapNode + null,
  l12_temp_9: BinHeapNode + null,
  l12_temp_10: BinHeapNode + null,
  l12_temp_11: BinHeapNode + null,
  l12_l1_nullDerefBool_0: boolean,
  l12_l1_nullDerefBool_1: boolean,
  l12_l1_nullDerefBool_2: boolean,
  l12_l1_nullDerefBool_3: boolean,
  l12_l1_nullDerefBool_4: boolean,
  l12_l1_nullDerefBool_5: boolean,
  l12_l1_nullDerefBool_6: boolean,
  l12_l1_nullDerefBool_7: boolean,
  l12_l1_nullDerefBool_8: boolean,
  l12_l1_nullDerefBool_9: boolean,
  l12_l1_nullDerefBool_10: boolean,
  l12_l1_nullDerefBool_11: boolean,
  l12_l1_nullDerefBool_12: boolean,
  l12_l1_nullDerefBool_13: boolean,
  l12_l1_nullDerefBool_14: boolean,
  l12_l1_nullDerefBool_15: boolean,
  l12_l1_nullDerefBool_16: boolean,
  l12_l1_nullDerefBool_17: boolean,
  l12_l1_nullDerefBool_18: boolean,
  l12_l1_nullDerefBool_19: boolean,
  l12_l1_nullDerefBool_20: boolean,
  l12_l1_nullDerefBool_21: boolean,
  l12_l1_nullDerefBool_22: boolean,
  l12_l1_nullDerefBool_23: boolean,
  l12_l1_nullDerefBool_24: boolean,
  l12_l1_nullDerefBool_25: boolean,
  l12_l1_nullDerefBool_26: boolean,
  l12_l1_nullDerefBool_27: boolean,
  l12_l1_nullDerefBool_28: boolean,
  l12_l1_nullDerefBool_29: boolean,
  l12_l1_nullDerefBool_30: boolean,
  l12_l1_nullDerefBool_31: boolean,
  l12_l1_nullDerefBool_32: boolean,
  l12_l1_nullDerefBool_33: boolean,
  l12_l1_nullDerefBool_34: boolean,
  l12_l1_nullDerefBool_35: boolean,
  l12_l1_nullDerefBool_36: boolean,
  l12_l1_nullDerefBool_37: boolean,
  l12_l1_nullDerefBool_38: boolean,
  l12_l1_nullDerefBool_39: boolean,
  l12_l1_nullDerefBool_40: boolean,
  l12_l1_nullDerefBool_41: boolean,
  l12_l1_nullDerefBool_42: boolean,
  l12_l1_nullDerefBool_43: boolean,
  l12_l1_nullDerefBool_44: boolean,
  l12_l1_nullDerefBool_45: boolean,
  l12_l1_nullDerefBool_46: boolean,
  l12_l1_nullDerefBool_47: boolean,
  l12_l1_nullDerefBool_48: boolean,
  l12_l1_nullDerefBool_49: boolean,
  l12_l1_nullDerefBool_50: boolean,
  l12_l1_nullDerefBool_51: boolean,
  l12_l1_nullDerefBool_52: boolean,
  l12_l1_nullDerefBool_53: boolean,
  l12_l1_nullDerefBool_54: boolean,
  l12_l1_nullDerefBool_55: boolean,
  l12_l1_nullDerefBool_56: boolean,
  l12_l1_nullDerefBool_57: boolean,
  l12_l1_nullDerefBool_58: boolean,
  l12_l1_nullDerefBool_59: boolean,
  l12_l1_nullDerefBool_60: boolean,
  l12_l1_nullDerefBool_61: boolean,
  l12_l1_nullDerefBool_62: boolean,
  l12_l1_nullDerefBool_63: boolean,
  l12_l1_nullDerefBool_64: boolean,
  l12_l1_nullDerefBool_65: boolean,
  l12_l1_nullDerefBool_66: boolean,
  l12_l1_nullDerefBool_67: boolean,
  l12_l1_nullDerefBool_68: boolean,
  l12_l1_nullDerefBool_69: boolean,
  l12_l1_nullDerefBool_70: boolean,
  l12_l1_nullDerefBool_71: boolean,
  l12_l1_nullDerefBool_72: boolean,
  l12_l1_nullDerefBool_73: boolean,
  l12_l1_nullDerefBool_74: boolean,
  l12_l1_nullDerefBool_75: boolean,
  l12_l1_nullDerefBool_76: boolean,
  l12_l1_nullDerefBool_77: boolean,
  l12_l1_nullDerefBool_78: boolean,
  l12_l1_nullDerefBool_79: boolean,
  l12_l1_nullDerefBool_80: boolean,
  l12_l1_nullDerefBool_81: boolean,
  l12_l1_nullDerefBool_82: boolean,
  l12_l1_nullDerefBool_83: boolean,
  l12_l1_nullDerefBool_84: boolean,
  l12_l1_nullDerefBool_85: boolean,
  l12_l3_lte_0: boolean,
  l12_l3_lte_1: boolean,
  l12_l3_lte_2: boolean,
  l12_l5_lt_0: boolean,
  l12_l5_lt_1: boolean,
  l12_l5_l0_nullDerefBool_0: boolean,
  l12_l5_l0_nullDerefBool_1: boolean,
  l12_lte_0: boolean,
  l12_lte_1: boolean,
  l12_lte_2: boolean,
  l12_lte_3: boolean,
  l12_lte_4: boolean,
  l12_lte_5: boolean,
  l12_lte_6: boolean,
  l12_lte_7: boolean,
  l12_lte_8: boolean,
  l12_lte_9: boolean,
  l12_lte_10: boolean,
  l12_l11_nullDerefBool_0: boolean,
  l12_l11_nullDerefBool_1: boolean,
  l12_l9_l0_nullDerefBool_0: boolean,
  l12_l9_l0_nullDerefBool_1: boolean,
  l12_l9_nullDerefBool_0: boolean,
  l12_l9_nullDerefBool_1: boolean,
  l12_l10_nullDerefBool_0: boolean,
  l12_l10_nullDerefBool_1: boolean,
  l12_l10_l0_nullDerefBool_0: boolean,
  l12_l10_l0_nullDerefBool_1: boolean,
  l12_l6_nullDerefBool_0: boolean,
  l12_l6_nullDerefBool_1: boolean,
  l12_l8_lt_0: boolean,
  l12_l8_lt_1: boolean,
  l12_l3_l0_result_0: boolean,
  l12_l3_l0_result_1: boolean,
  l12_l3_l0_result_2: boolean,
  l12_l6_lt_0: boolean,
  l12_l6_lt_1: boolean,
  l12_l11_l0_result_0: boolean,
  l12_l11_l0_result_1: boolean,
  l12_l11_l0_result_2: boolean,
  l12_l11_lte_0: boolean,
  l12_l11_lte_1: boolean,
  l12_l11_lte_2: boolean,
  l12_l2_l0_nullDerefBool_0: boolean,
  l12_l2_l0_nullDerefBool_1: boolean,
  l12_prevTemp_0: BinHeapNode + null,
  l12_prevTemp_1: BinHeapNode + null,
  l12_prevTemp_2: BinHeapNode + null,
  l12_prevTemp_3: BinHeapNode + null,
  l12_prevTemp_4: BinHeapNode + null,
  l12_prevTemp_5: BinHeapNode + null,
  l12_prevTemp_6: BinHeapNode + null,
  l12_prevTemp_7: BinHeapNode + null,
  l12_prevTemp_8: BinHeapNode + null,
  l12_prevTemp_9: BinHeapNode + null,
  l12_prevTemp_10: BinHeapNode + null,
  l12_prevTemp_11: BinHeapNode + null,
  l12_l4_lte_0: boolean,
  l12_l4_lte_1: boolean,
  l12_l4_lte_2: boolean,
  l12_l7_lt_0: boolean,
  l12_l7_lt_1: boolean,
  l12_l6_l0_result_0: boolean,
  l12_l6_l0_result_1: boolean,
  l12_l6_l0_result_2: boolean,
  l12_l3_nullDerefBool_0: boolean,
  l12_l3_nullDerefBool_1: boolean,
  l12_l10_l0_result_0: boolean,
  l12_l10_l0_result_1: boolean,
  l12_l10_l0_result_2: boolean,
  l12_l11_l0_nullDerefBool_0: boolean,
  l12_l11_l0_nullDerefBool_1: boolean,
  l12_l5_lte_0: boolean,
  l12_l5_lte_1: boolean,
  l12_l5_lte_2: boolean,
  l12_nullDerefBool_0: boolean,
  l12_nullDerefBool_1: boolean,
  l12_nullDerefBool_2: boolean,
  l12_nullDerefBool_3: boolean,
  l12_nullDerefBool_4: boolean,
  l12_nullDerefBool_5: boolean,
  l12_nullDerefBool_6: boolean,
  l12_nullDerefBool_7: boolean,
  l12_nullDerefBool_8: boolean,
  l12_nullDerefBool_9: boolean,
  l12_nullDerefBool_10: boolean,
  l12_nullDerefBool_11: boolean,
  l12_nullDerefBool_12: boolean,
  l12_nullDerefBool_13: boolean,
  l12_nullDerefBool_14: boolean,
  l12_nullDerefBool_15: boolean,
  l12_nullDerefBool_16: boolean,
  l12_nullDerefBool_17: boolean,
  l12_nullDerefBool_18: boolean,
  l12_nullDerefBool_19: boolean,
  l12_nullDerefBool_20: boolean,
  l12_nullDerefBool_21: boolean,
  l12_nullDerefBool_22: boolean,
  l12_nullDerefBool_23: boolean,
  l12_nullDerefBool_24: boolean,
  l12_nullDerefBool_25: boolean,
  l12_nullDerefBool_26: boolean,
  l12_nullDerefBool_27: boolean,
  l12_nullDerefBool_28: boolean,
  l12_nullDerefBool_29: boolean,
  l12_nullDerefBool_30: boolean,
  l12_nullDerefBool_31: boolean,
  l12_nullDerefBool_32: boolean,
  l12_nullDerefBool_33: boolean,
  l12_nullDerefBool_34: boolean,
  l12_nullDerefBool_35: boolean,
  l12_nullDerefBool_36: boolean,
  l12_nullDerefBool_37: boolean,
  l12_nullDerefBool_38: boolean,
  l12_nullDerefBool_39: boolean,
  l12_nullDerefBool_40: boolean,
  l12_nullDerefBool_41: boolean,
  l12_nullDerefBool_42: boolean,
  l12_nullDerefBool_43: boolean,
  l12_nullDerefBool_44: boolean,
  l12_nullDerefBool_45: boolean,
  l12_nullDerefBool_46: boolean,
  l12_nullDerefBool_47: boolean,
  l12_nullDerefBool_48: boolean,
  l12_nullDerefBool_49: boolean,
  l12_nullDerefBool_50: boolean,
  l12_nullDerefBool_51: boolean,
  l12_nullDerefBool_52: boolean,
  l12_nullDerefBool_53: boolean,
  l12_nullDerefBool_54: boolean,
  l12_nullDerefBool_55: boolean,
  l12_nullDerefBool_56: boolean,
  l12_nullDerefBool_57: boolean,
  l12_nullDerefBool_58: boolean,
  l12_nullDerefBool_59: boolean,
  l12_nullDerefBool_60: boolean,
  l12_nullDerefBool_61: boolean,
  l12_nullDerefBool_62: boolean,
  l12_nullDerefBool_63: boolean,
  l12_nullDerefBool_64: boolean,
  l12_nullDerefBool_65: boolean,
  l12_nullDerefBool_66: boolean,
  l12_nullDerefBool_67: boolean,
  l12_nullDerefBool_68: boolean,
  l12_nullDerefBool_69: boolean,
  l12_nullDerefBool_70: boolean,
  l12_nullDerefBool_71: boolean,
  l12_nullDerefBool_72: boolean,
  l12_nullDerefBool_73: boolean,
  l12_nullDerefBool_74: boolean,
  l12_nullDerefBool_75: boolean,
  l12_nullDerefBool_76: boolean,
  l12_nullDerefBool_77: boolean,
  l12_nullDerefBool_78: boolean,
  l12_nullDerefBool_79: boolean,
  l12_nullDerefBool_80: boolean,
  l12_nullDerefBool_81: boolean,
  l12_nullDerefBool_82: boolean,
  l12_nullDerefBool_83: boolean,
  l12_l1_temp1_0: BinHeapNode + null,
  l12_l1_temp1_1: BinHeapNode + null,
  l12_l1_temp1_2: BinHeapNode + null,
  l12_l1_temp1_3: BinHeapNode + null,
  l12_l1_temp1_4: BinHeapNode + null,
  l12_l1_temp1_5: BinHeapNode + null,
  l12_l1_temp1_6: BinHeapNode + null,
  l12_l1_temp1_7: BinHeapNode + null,
  l12_l1_temp1_8: BinHeapNode + null,
  l12_l1_temp1_9: BinHeapNode + null,
  l12_l1_temp1_10: BinHeapNode + null,
  l12_l1_temp1_11: BinHeapNode + null,
  l12_l1_temp1_12: BinHeapNode + null,
  l12_l1_temp1_13: BinHeapNode + null,
  l12_l1_temp1_14: BinHeapNode + null,
  l12_l1_temp1_15: BinHeapNode + null,
  l12_l1_temp1_16: BinHeapNode + null,
  l12_l1_temp1_17: BinHeapNode + null,
  l12_l1_temp1_18: BinHeapNode + null,
  l12_l1_temp1_19: BinHeapNode + null,
  l12_l1_temp1_20: BinHeapNode + null,
  l12_l1_temp1_21: BinHeapNode + null,
  l12_l1_temp1_22: BinHeapNode + null,
  l12_l4_l0_result_0: boolean,
  l12_l4_l0_result_1: boolean,
  l12_l4_l0_result_2: boolean,
  l12_l1_temp2_0: BinHeapNode + null,
  l12_l1_temp2_1: BinHeapNode + null,
  l12_l1_temp2_2: BinHeapNode + null,
  l12_l1_temp2_3: BinHeapNode + null,
  l12_l1_temp2_4: BinHeapNode + null,
  l12_l1_temp2_5: BinHeapNode + null,
  l12_l1_temp2_6: BinHeapNode + null,
  l12_l1_temp2_7: BinHeapNode + null,
  l12_l1_temp2_8: BinHeapNode + null,
  l12_l1_temp2_9: BinHeapNode + null,
  l12_l1_temp2_10: BinHeapNode + null,
  l12_l1_temp2_11: BinHeapNode + null,
  l12_l9_l0_result_0: boolean,
  l12_l9_l0_result_1: boolean,
  l12_l9_l0_result_2: boolean,
  l12_l8_l0_result_0: boolean,
  l12_l8_l0_result_1: boolean,
  l12_l8_l0_result_2: boolean,
  l12_l7_nullDerefBool_0: boolean,
  l12_l7_nullDerefBool_1: boolean,
  l12_l7_l0_nullDerefBool_0: boolean,
  l12_l7_l0_nullDerefBool_1: boolean,
  l12_l1_tmp_0: BinHeapNode + null,
  l12_l1_tmp_1: BinHeapNode + null,
  l12_l1_tmp_2: BinHeapNode + null,
  l12_l1_tmp_3: BinHeapNode + null,
  l12_l1_tmp_4: BinHeapNode + null,
  l12_l1_tmp_5: BinHeapNode + null,
  l12_l1_tmp_6: BinHeapNode + null,
  l12_l1_tmp_7: BinHeapNode + null,
  l12_l1_tmp_8: BinHeapNode + null,
  l12_l1_tmp_9: BinHeapNode + null,
  l12_l1_tmp_10: BinHeapNode + null
]{
  TruePred[]
  and 
  (
    (
      BinHeapCondition0[throw_0]
      and 
      (
        nullDerefBool_1=false)
    )
    or 
    (
      (
        not (
          BinHeapCondition0[throw_0])
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
      BinHeapCondition0[throw_0]
      and 
      (
        throw_1=null)
    )
    or 
    (
      (
        not (
          BinHeapCondition0[throw_0])
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
      BinHeapCondition0[throw_1]
      and 
      (
        temp_0_1=fresh_node_0)
    )
    or 
    (
      (
        not (
          BinHeapCondition0[throw_1])
      )
      and 
      TruePred[]
      and 
      (
        temp_0_0=temp_0_1)
    )
  )
  and 
  (
    (
      BinHeapCondition58[temp_0_1]
      and 
      (
        (
          BinHeapCondition0[throw_1]
          and 
          (
            nullDerefBool_2=true)
        )
        or 
        (
          (
            not (
              BinHeapCondition0[throw_1])
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
          BinHeapCondition58[temp_0_1])
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
      BinHeapCondition0[throw_1]
      and 
      (
        element_1=(element_0)++((temp_0_1)->(data_value_0)))
    )
    or 
    (
      (
        not (
          BinHeapCondition0[throw_1])
      )
      and 
      TruePred[]
      and 
      (
        element_0=element_1)
    )
  )
  and 
  (
    (
      BinHeapCondition2[thiz_0]
      and 
      (
        (
          BinHeapCondition0[throw_1]
          and 
          (
            nullDerefBool_3=true)
        )
        or 
        (
          (
            not (
              BinHeapCondition0[throw_1])
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
          BinHeapCondition2[thiz_0])
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
      BinHeapCondition62[head_0,
                        thiz_0]
      and 
      (
        (
          BinHeapCondition2[thiz_0]
          and 
          (
            (
              BinHeapCondition0[throw_1]
              and 
              (
                nullDerefBool_4=true)
            )
            or 
            (
              (
                not (
                  BinHeapCondition0[throw_1])
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
              BinHeapCondition2[thiz_0])
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
          BinHeapCondition0[throw_1]
          and 
          (
            head_20=(head_0)++((thiz_0)->(temp_0_1)))
        )
        or 
        (
          (
            not (
              BinHeapCondition0[throw_1])
          )
          and 
          TruePred[]
          and 
          (
            head_0=head_20)
        )
      )
      and 
      (
        (
          BinHeapCondition2[thiz_0]
          and 
          (
            (
              BinHeapCondition0[throw_1]
              and 
              (
                nullDerefBool_5=true)
            )
            or 
            (
              (
                not (
                  BinHeapCondition0[throw_1])
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
              BinHeapCondition2[thiz_0])
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
          BinHeapCondition0[throw_1]
          and 
          (
            size_1=(size_0)++((thiz_0)->(1)))
        )
        or 
        (
          (
            not (
              BinHeapCondition0[throw_1])
          )
          and 
          TruePred[]
          and 
          (
            size_0=size_1)
        )
      )
      and 
      (
        l12_nextTemp_0=l12_nextTemp_11)
      and 
      (
        l12_l2_l0_result_0=l12_l2_l0_result_2)
      and 
      (
        l12_l2_nullDerefBool_0=l12_l2_nullDerefBool_1)
      and 
      (
        l12_l3_lt_0=l12_l3_lt_1)
      and 
      (
        l12_l11_lt_0=l12_l11_lt_1)
      and 
      (
        l12_l9_lte_0=l12_l9_lte_2)
      and 
      (
        l12_l6_lte_0=l12_l6_lte_2)
      and 
      (
        l12_l4_l0_nullDerefBool_0=l12_l4_l0_nullDerefBool_1)
      and 
      (
        l12_l9_lt_0=l12_l9_lt_1)
      and 
      (
        l12_l5_l0_result_0=l12_l5_l0_result_2)
      and 
      (
        l12_l8_lte_0=l12_l8_lte_2)
      and 
      (
        l12_l8_l0_nullDerefBool_0=l12_l8_l0_nullDerefBool_1)
      and 
      (
        l12_l8_nullDerefBool_0=l12_l8_nullDerefBool_1)
      and 
      (
        l12_l10_lt_0=l12_l10_lt_1)
      and 
      (
        l12_l10_lte_0=l12_l10_lte_2)
      and 
      (
        l12_l6_l0_nullDerefBool_0=l12_l6_l0_nullDerefBool_1)
      and 
      (
        l12_l7_lte_0=l12_l7_lte_2)
      and 
      (
        l12_l4_lt_0=l12_l4_lt_1)
      and 
      (
        l12_l2_lte_0=l12_l2_lte_2)
      and 
      (
        l12_l7_l0_result_0=l12_l7_l0_result_2)
      and 
      (
        parent_0=parent_10)
      and 
      (
        l12_l2_lt_0=l12_l2_lt_1)
      and 
      (
        l12_l4_nullDerefBool_0=l12_l4_nullDerefBool_1)
      and 
      (
        l12_l5_nullDerefBool_0=l12_l5_nullDerefBool_1)
      and 
      (
        l12_l3_l0_nullDerefBool_0=l12_l3_l0_nullDerefBool_1)
      and 
      (
        l12_temp_0=l12_temp_11)
      and 
      (
        l12_l1_nullDerefBool_0=l12_l1_nullDerefBool_85)
      and 
      (
        l12_l5_lt_0=l12_l5_lt_1)
      and 
      (
        l12_l3_lte_0=l12_l3_lte_2)
      and 
      (
        l12_lte_0=l12_lte_10)
      and 
      (
        l12_l5_l0_nullDerefBool_0=l12_l5_l0_nullDerefBool_1)
      and 
      (
        l12_l11_nullDerefBool_0=l12_l11_nullDerefBool_1)
      and 
      (
        l12_l9_l0_nullDerefBool_0=l12_l9_l0_nullDerefBool_1)
      and 
      (
        l12_l10_nullDerefBool_0=l12_l10_nullDerefBool_1)
      and 
      (
        l12_l9_nullDerefBool_0=l12_l9_nullDerefBool_1)
      and 
      (
        l12_l6_nullDerefBool_0=l12_l6_nullDerefBool_1)
      and 
      (
        l12_l10_l0_nullDerefBool_0=l12_l10_l0_nullDerefBool_1)
      and 
      (
        l12_l8_lt_0=l12_l8_lt_1)
      and 
      (
        l12_l3_l0_result_0=l12_l3_l0_result_2)
      and 
      (
        child_0=child_10)
      and 
      (
        l12_l6_lt_0=l12_l6_lt_1)
      and 
      (
        l12_l11_l0_result_0=l12_l11_l0_result_2)
      and 
      (
        l12_l11_lte_0=l12_l11_lte_2)
      and 
      (
        l12_l2_l0_nullDerefBool_0=l12_l2_l0_nullDerefBool_1)
      and 
      (
        l12_prevTemp_0=l12_prevTemp_11)
      and 
      (
        l12_l4_lte_0=l12_l4_lte_2)
      and 
      (
        l12_l7_lt_0=l12_l7_lt_1)
      and 
      (
        l12_l6_l0_result_0=l12_l6_l0_result_2)
      and 
      (
        l12_l10_l0_result_0=l12_l10_l0_result_2)
      and 
      (
        l12_l3_nullDerefBool_0=l12_l3_nullDerefBool_1)
      and 
      (
        l12_l11_l0_nullDerefBool_0=l12_l11_l0_nullDerefBool_1)
      and 
      (
        l12_l5_lte_0=l12_l5_lte_2)
      and 
      (
        l12_nullDerefBool_0=l12_nullDerefBool_83)
      and 
      (
        l12_l1_temp1_0=l12_l1_temp1_22)
      and 
      (
        l12_l4_l0_result_0=l12_l4_l0_result_2)
      and 
      (
        l12_l1_temp2_0=l12_l1_temp2_11)
      and 
      (
        l12_l9_l0_result_0=l12_l9_l0_result_2)
      and 
      (
        l12_l8_l0_result_0=l12_l8_l0_result_2)
      and 
      (
        l12_l7_nullDerefBool_0=l12_l7_nullDerefBool_1)
      and 
      (
        degree_0=degree_10)
      and 
      (
        sibling_0=sibling_41)
      and 
      (
        l12_l7_l0_nullDerefBool_0=l12_l7_l0_nullDerefBool_1)
      and 
      (
        l12_l1_tmp_0=l12_l1_tmp_10)
      and 
      (
        throw_1=throw_45)
    )
    or 
    (
      (
        not (
          BinHeapCondition62[head_0,
                            thiz_0]
        )
      )
      and 
      (
        (
          BinHeapCondition0[throw_1]
          and 
          BinHeap_unionNodes_0[thiz_0,
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
                              throw_25,
                              throw_26,
                              throw_27,
                              throw_28,
                              throw_29,
                              throw_30,
                              throw_31,
                              throw_32,
                              throw_33,
                              throw_34,
                              throw_35,
                              throw_36,
                              throw_37,
                              throw_38,
                              throw_39,
                              throw_40,
                              throw_41,
                              throw_42,
                              throw_43,
                              throw_44,
                              throw_45,
                              temp_0_1,
                              head_0,
                              head_1,
                              head_2,
                              head_3,
                              head_4,
                              head_5,
                              head_6,
                              head_7,
                              head_8,
                              head_9,
                              head_10,
                              head_11,
                              head_12,
                              head_13,
                              head_14,
                              head_15,
                              head_16,
                              head_17,
                              head_18,
                              head_19,
                              head_20,
                              degree_0,
                              degree_1,
                              degree_2,
                              degree_3,
                              degree_4,
                              degree_5,
                              degree_6,
                              degree_7,
                              degree_8,
                              degree_9,
                              degree_10,
                              sibling_0,
                              sibling_1,
                              sibling_2,
                              sibling_3,
                              sibling_4,
                              sibling_5,
                              sibling_6,
                              sibling_7,
                              sibling_8,
                              sibling_9,
                              sibling_10,
                              sibling_11,
                              sibling_12,
                              sibling_13,
                              sibling_14,
                              sibling_15,
                              sibling_16,
                              sibling_17,
                              sibling_18,
                              sibling_19,
                              sibling_20,
                              sibling_21,
                              sibling_22,
                              sibling_23,
                              sibling_24,
                              sibling_25,
                              sibling_26,
                              sibling_27,
                              sibling_28,
                              sibling_29,
                              sibling_30,
                              sibling_31,
                              sibling_32,
                              sibling_33,
                              sibling_34,
                              sibling_35,
                              sibling_36,
                              sibling_37,
                              sibling_38,
                              sibling_39,
                              sibling_40,
                              sibling_41,
                              element_1,
                              child_0,
                              child_1,
                              child_2,
                              child_3,
                              child_4,
                              child_5,
                              child_6,
                              child_7,
                              child_8,
                              child_9,
                              child_10,
                              parent_0,
                              parent_1,
                              parent_2,
                              parent_3,
                              parent_4,
                              parent_5,
                              parent_6,
                              parent_7,
                              parent_8,
                              parent_9,
                              parent_10,
                              l12_nextTemp_0,
                              l12_nextTemp_1,
                              l12_nextTemp_2,
                              l12_nextTemp_3,
                              l12_nextTemp_4,
                              l12_nextTemp_5,
                              l12_nextTemp_6,
                              l12_nextTemp_7,
                              l12_nextTemp_8,
                              l12_nextTemp_9,
                              l12_nextTemp_10,
                              l12_nextTemp_11,
                              l12_prevTemp_0,
                              l12_prevTemp_1,
                              l12_prevTemp_2,
                              l12_prevTemp_3,
                              l12_prevTemp_4,
                              l12_prevTemp_5,
                              l12_prevTemp_6,
                              l12_prevTemp_7,
                              l12_prevTemp_8,
                              l12_prevTemp_9,
                              l12_prevTemp_10,
                              l12_prevTemp_11,
                              l12_nullDerefBool_0,
                              l12_nullDerefBool_1,
                              l12_nullDerefBool_2,
                              l12_nullDerefBool_3,
                              l12_nullDerefBool_4,
                              l12_nullDerefBool_5,
                              l12_nullDerefBool_6,
                              l12_nullDerefBool_7,
                              l12_nullDerefBool_8,
                              l12_nullDerefBool_9,
                              l12_nullDerefBool_10,
                              l12_nullDerefBool_11,
                              l12_nullDerefBool_12,
                              l12_nullDerefBool_13,
                              l12_nullDerefBool_14,
                              l12_nullDerefBool_15,
                              l12_nullDerefBool_16,
                              l12_nullDerefBool_17,
                              l12_nullDerefBool_18,
                              l12_nullDerefBool_19,
                              l12_nullDerefBool_20,
                              l12_nullDerefBool_21,
                              l12_nullDerefBool_22,
                              l12_nullDerefBool_23,
                              l12_nullDerefBool_24,
                              l12_nullDerefBool_25,
                              l12_nullDerefBool_26,
                              l12_nullDerefBool_27,
                              l12_nullDerefBool_28,
                              l12_nullDerefBool_29,
                              l12_nullDerefBool_30,
                              l12_nullDerefBool_31,
                              l12_nullDerefBool_32,
                              l12_nullDerefBool_33,
                              l12_nullDerefBool_34,
                              l12_nullDerefBool_35,
                              l12_nullDerefBool_36,
                              l12_nullDerefBool_37,
                              l12_nullDerefBool_38,
                              l12_nullDerefBool_39,
                              l12_nullDerefBool_40,
                              l12_nullDerefBool_41,
                              l12_nullDerefBool_42,
                              l12_nullDerefBool_43,
                              l12_nullDerefBool_44,
                              l12_nullDerefBool_45,
                              l12_nullDerefBool_46,
                              l12_nullDerefBool_47,
                              l12_nullDerefBool_48,
                              l12_nullDerefBool_49,
                              l12_nullDerefBool_50,
                              l12_nullDerefBool_51,
                              l12_nullDerefBool_52,
                              l12_nullDerefBool_53,
                              l12_nullDerefBool_54,
                              l12_nullDerefBool_55,
                              l12_nullDerefBool_56,
                              l12_nullDerefBool_57,
                              l12_nullDerefBool_58,
                              l12_nullDerefBool_59,
                              l12_nullDerefBool_60,
                              l12_nullDerefBool_61,
                              l12_nullDerefBool_62,
                              l12_nullDerefBool_63,
                              l12_nullDerefBool_64,
                              l12_nullDerefBool_65,
                              l12_nullDerefBool_66,
                              l12_nullDerefBool_67,
                              l12_nullDerefBool_68,
                              l12_nullDerefBool_69,
                              l12_nullDerefBool_70,
                              l12_nullDerefBool_71,
                              l12_nullDerefBool_72,
                              l12_nullDerefBool_73,
                              l12_nullDerefBool_74,
                              l12_nullDerefBool_75,
                              l12_nullDerefBool_76,
                              l12_nullDerefBool_77,
                              l12_nullDerefBool_78,
                              l12_nullDerefBool_79,
                              l12_nullDerefBool_80,
                              l12_nullDerefBool_81,
                              l12_nullDerefBool_82,
                              l12_nullDerefBool_83,
                              l12_lte_0,
                              l12_lte_1,
                              l12_lte_2,
                              l12_lte_3,
                              l12_lte_4,
                              l12_lte_5,
                              l12_lte_6,
                              l12_lte_7,
                              l12_lte_8,
                              l12_lte_9,
                              l12_lte_10,
                              l12_temp_0,
                              l12_temp_1,
                              l12_temp_2,
                              l12_temp_3,
                              l12_temp_4,
                              l12_temp_5,
                              l12_temp_6,
                              l12_temp_7,
                              l12_temp_8,
                              l12_temp_9,
                              l12_temp_10,
                              l12_temp_11,
                              l12_l8_nullDerefBool_0,
                              l12_l8_nullDerefBool_1,
                              l12_l8_lt_0,
                              l12_l8_lt_1,
                              l12_l10_l0_nullDerefBool_0,
                              l12_l10_l0_nullDerefBool_1,
                              l12_l9_l0_nullDerefBool_0,
                              l12_l9_l0_nullDerefBool_1,
                              l12_l5_lt_0,
                              l12_l5_lt_1,
                              l12_l9_lt_0,
                              l12_l9_lt_1,
                              l12_l5_l0_nullDerefBool_0,
                              l12_l5_l0_nullDerefBool_1,
                              l12_l10_lte_0,
                              l12_l10_lte_1,
                              l12_l10_lte_2,
                              l12_l6_l0_nullDerefBool_0,
                              l12_l6_l0_nullDerefBool_1,
                              l12_l6_lte_0,
                              l12_l6_lte_1,
                              l12_l6_lte_2,
                              l12_l8_l0_result_0,
                              l12_l8_l0_result_1,
                              l12_l8_l0_result_2,
                              l12_l11_l0_result_0,
                              l12_l11_l0_result_1,
                              l12_l11_l0_result_2,
                              l12_l10_lt_0,
                              l12_l10_lt_1,
                              l12_l3_l0_nullDerefBool_0,
                              l12_l3_l0_nullDerefBool_1,
                              l12_l11_nullDerefBool_0,
                              l12_l11_nullDerefBool_1,
                              l12_l3_lt_0,
                              l12_l3_lt_1,
                              l12_l3_l0_result_0,
                              l12_l3_l0_result_1,
                              l12_l3_l0_result_2,
                              l12_l2_l0_nullDerefBool_0,
                              l12_l2_l0_nullDerefBool_1,
                              l12_l11_lt_0,
                              l12_l11_lt_1,
                              l12_l2_nullDerefBool_0,
                              l12_l2_nullDerefBool_1,
                              l12_l4_lte_0,
                              l12_l4_lte_1,
                              l12_l4_lte_2,
                              l12_l9_l0_result_0,
                              l12_l9_l0_result_1,
                              l12_l9_l0_result_2,
                              l12_l8_l0_nullDerefBool_0,
                              l12_l8_l0_nullDerefBool_1,
                              l12_l4_l0_result_0,
                              l12_l4_l0_result_1,
                              l12_l4_l0_result_2,
                              l12_l7_nullDerefBool_0,
                              l12_l7_nullDerefBool_1,
                              l12_l3_lte_0,
                              l12_l3_lte_1,
                              l12_l3_lte_2,
                              l12_l1_temp2_0,
                              l12_l1_temp2_1,
                              l12_l1_temp2_2,
                              l12_l1_temp2_3,
                              l12_l1_temp2_4,
                              l12_l1_temp2_5,
                              l12_l1_temp2_6,
                              l12_l1_temp2_7,
                              l12_l1_temp2_8,
                              l12_l1_temp2_9,
                              l12_l1_temp2_10,
                              l12_l1_temp2_11,
                              l12_l1_temp1_0,
                              l12_l1_temp1_1,
                              l12_l1_temp1_2,
                              l12_l1_temp1_3,
                              l12_l1_temp1_4,
                              l12_l1_temp1_5,
                              l12_l1_temp1_6,
                              l12_l1_temp1_7,
                              l12_l1_temp1_8,
                              l12_l1_temp1_9,
                              l12_l1_temp1_10,
                              l12_l1_temp1_11,
                              l12_l1_temp1_12,
                              l12_l1_temp1_13,
                              l12_l1_temp1_14,
                              l12_l1_temp1_15,
                              l12_l1_temp1_16,
                              l12_l1_temp1_17,
                              l12_l1_temp1_18,
                              l12_l1_temp1_19,
                              l12_l1_temp1_20,
                              l12_l1_temp1_21,
                              l12_l1_temp1_22,
                              l12_l7_lte_0,
                              l12_l7_lte_1,
                              l12_l7_lte_2,
                              l12_l8_lte_0,
                              l12_l8_lte_1,
                              l12_l8_lte_2,
                              l12_l11_lte_0,
                              l12_l11_lte_1,
                              l12_l11_lte_2,
                              l12_l4_nullDerefBool_0,
                              l12_l4_nullDerefBool_1,
                              l12_l7_l0_nullDerefBool_0,
                              l12_l7_l0_nullDerefBool_1,
                              l12_l6_lt_0,
                              l12_l6_lt_1,
                              l12_l9_nullDerefBool_0,
                              l12_l9_nullDerefBool_1,
                              l12_l5_nullDerefBool_0,
                              l12_l5_nullDerefBool_1,
                              l12_l5_lte_0,
                              l12_l5_lte_1,
                              l12_l5_lte_2,
                              l12_l6_nullDerefBool_0,
                              l12_l6_nullDerefBool_1,
                              l12_l9_lte_0,
                              l12_l9_lte_1,
                              l12_l9_lte_2,
                              l12_l11_l0_nullDerefBool_0,
                              l12_l11_l0_nullDerefBool_1,
                              l12_l7_l0_result_0,
                              l12_l7_l0_result_1,
                              l12_l7_l0_result_2,
                              l12_l4_lt_0,
                              l12_l4_lt_1,
                              l12_l2_l0_result_0,
                              l12_l2_l0_result_1,
                              l12_l2_l0_result_2,
                              l12_l3_nullDerefBool_0,
                              l12_l3_nullDerefBool_1,
                              l12_l5_l0_result_0,
                              l12_l5_l0_result_1,
                              l12_l5_l0_result_2,
                              l12_l7_lt_0,
                              l12_l7_lt_1,
                              l12_l2_lte_0,
                              l12_l2_lte_1,
                              l12_l2_lte_2,
                              l12_l6_l0_result_0,
                              l12_l6_l0_result_1,
                              l12_l6_l0_result_2,
                              l12_l1_nullDerefBool_0,
                              l12_l1_nullDerefBool_1,
                              l12_l1_nullDerefBool_2,
                              l12_l1_nullDerefBool_3,
                              l12_l1_nullDerefBool_4,
                              l12_l1_nullDerefBool_5,
                              l12_l1_nullDerefBool_6,
                              l12_l1_nullDerefBool_7,
                              l12_l1_nullDerefBool_8,
                              l12_l1_nullDerefBool_9,
                              l12_l1_nullDerefBool_10,
                              l12_l1_nullDerefBool_11,
                              l12_l1_nullDerefBool_12,
                              l12_l1_nullDerefBool_13,
                              l12_l1_nullDerefBool_14,
                              l12_l1_nullDerefBool_15,
                              l12_l1_nullDerefBool_16,
                              l12_l1_nullDerefBool_17,
                              l12_l1_nullDerefBool_18,
                              l12_l1_nullDerefBool_19,
                              l12_l1_nullDerefBool_20,
                              l12_l1_nullDerefBool_21,
                              l12_l1_nullDerefBool_22,
                              l12_l1_nullDerefBool_23,
                              l12_l1_nullDerefBool_24,
                              l12_l1_nullDerefBool_25,
                              l12_l1_nullDerefBool_26,
                              l12_l1_nullDerefBool_27,
                              l12_l1_nullDerefBool_28,
                              l12_l1_nullDerefBool_29,
                              l12_l1_nullDerefBool_30,
                              l12_l1_nullDerefBool_31,
                              l12_l1_nullDerefBool_32,
                              l12_l1_nullDerefBool_33,
                              l12_l1_nullDerefBool_34,
                              l12_l1_nullDerefBool_35,
                              l12_l1_nullDerefBool_36,
                              l12_l1_nullDerefBool_37,
                              l12_l1_nullDerefBool_38,
                              l12_l1_nullDerefBool_39,
                              l12_l1_nullDerefBool_40,
                              l12_l1_nullDerefBool_41,
                              l12_l1_nullDerefBool_42,
                              l12_l1_nullDerefBool_43,
                              l12_l1_nullDerefBool_44,
                              l12_l1_nullDerefBool_45,
                              l12_l1_nullDerefBool_46,
                              l12_l1_nullDerefBool_47,
                              l12_l1_nullDerefBool_48,
                              l12_l1_nullDerefBool_49,
                              l12_l1_nullDerefBool_50,
                              l12_l1_nullDerefBool_51,
                              l12_l1_nullDerefBool_52,
                              l12_l1_nullDerefBool_53,
                              l12_l1_nullDerefBool_54,
                              l12_l1_nullDerefBool_55,
                              l12_l1_nullDerefBool_56,
                              l12_l1_nullDerefBool_57,
                              l12_l1_nullDerefBool_58,
                              l12_l1_nullDerefBool_59,
                              l12_l1_nullDerefBool_60,
                              l12_l1_nullDerefBool_61,
                              l12_l1_nullDerefBool_62,
                              l12_l1_nullDerefBool_63,
                              l12_l1_nullDerefBool_64,
                              l12_l1_nullDerefBool_65,
                              l12_l1_nullDerefBool_66,
                              l12_l1_nullDerefBool_67,
                              l12_l1_nullDerefBool_68,
                              l12_l1_nullDerefBool_69,
                              l12_l1_nullDerefBool_70,
                              l12_l1_nullDerefBool_71,
                              l12_l1_nullDerefBool_72,
                              l12_l1_nullDerefBool_73,
                              l12_l1_nullDerefBool_74,
                              l12_l1_nullDerefBool_75,
                              l12_l1_nullDerefBool_76,
                              l12_l1_nullDerefBool_77,
                              l12_l1_nullDerefBool_78,
                              l12_l1_nullDerefBool_79,
                              l12_l1_nullDerefBool_80,
                              l12_l1_nullDerefBool_81,
                              l12_l1_nullDerefBool_82,
                              l12_l1_nullDerefBool_83,
                              l12_l1_nullDerefBool_84,
                              l12_l1_nullDerefBool_85,
                              l12_l4_l0_nullDerefBool_0,
                              l12_l4_l0_nullDerefBool_1,
                              l12_l10_l0_result_0,
                              l12_l10_l0_result_1,
                              l12_l10_l0_result_2,
                              l12_l2_lt_0,
                              l12_l2_lt_1,
                              l12_l1_tmp_0,
                              l12_l1_tmp_1,
                              l12_l1_tmp_2,
                              l12_l1_tmp_3,
                              l12_l1_tmp_4,
                              l12_l1_tmp_5,
                              l12_l1_tmp_6,
                              l12_l1_tmp_7,
                              l12_l1_tmp_8,
                              l12_l1_tmp_9,
                              l12_l1_tmp_10,
                              l12_l10_nullDerefBool_0,
                              l12_l10_nullDerefBool_1]
        )
        or 
        (
          (
            not (
              BinHeapCondition0[throw_1])
          )
          and 
          TruePred[]
          and 
          (
            l12_nextTemp_0=l12_nextTemp_11)
          and 
          (
            l12_l2_l0_result_0=l12_l2_l0_result_2)
          and 
          (
            l12_l2_nullDerefBool_0=l12_l2_nullDerefBool_1)
          and 
          (
            l12_l3_lt_0=l12_l3_lt_1)
          and 
          (
            l12_l11_lt_0=l12_l11_lt_1)
          and 
          (
            l12_l9_lte_0=l12_l9_lte_2)
          and 
          (
            l12_l4_l0_nullDerefBool_0=l12_l4_l0_nullDerefBool_1)
          and 
          (
            l12_l6_lte_0=l12_l6_lte_2)
          and 
          (
            l12_l9_lt_0=l12_l9_lt_1)
          and 
          (
            l12_l5_l0_result_0=l12_l5_l0_result_2)
          and 
          (
            l12_l8_lte_0=l12_l8_lte_2)
          and 
          (
            l12_l8_l0_nullDerefBool_0=l12_l8_l0_nullDerefBool_1)
          and 
          (
            l12_l8_nullDerefBool_0=l12_l8_nullDerefBool_1)
          and 
          (
            head_0=head_20)
          and 
          (
            l12_l10_lt_0=l12_l10_lt_1)
          and 
          (
            l12_l10_lte_0=l12_l10_lte_2)
          and 
          (
            l12_l6_l0_nullDerefBool_0=l12_l6_l0_nullDerefBool_1)
          and 
          (
            l12_l7_lte_0=l12_l7_lte_2)
          and 
          (
            l12_l4_lt_0=l12_l4_lt_1)
          and 
          (
            l12_l2_lte_0=l12_l2_lte_2)
          and 
          (
            l12_l7_l0_result_0=l12_l7_l0_result_2)
          and 
          (
            parent_0=parent_10)
          and 
          (
            l12_l2_lt_0=l12_l2_lt_1)
          and 
          (
            l12_l4_nullDerefBool_0=l12_l4_nullDerefBool_1)
          and 
          (
            l12_l5_nullDerefBool_0=l12_l5_nullDerefBool_1)
          and 
          (
            l12_l3_l0_nullDerefBool_0=l12_l3_l0_nullDerefBool_1)
          and 
          (
            l12_temp_0=l12_temp_11)
          and 
          (
            l12_l1_nullDerefBool_0=l12_l1_nullDerefBool_85)
          and 
          (
            l12_l5_lt_0=l12_l5_lt_1)
          and 
          (
            l12_l3_lte_0=l12_l3_lte_2)
          and 
          (
            l12_lte_0=l12_lte_10)
          and 
          (
            l12_l5_l0_nullDerefBool_0=l12_l5_l0_nullDerefBool_1)
          and 
          (
            l12_l11_nullDerefBool_0=l12_l11_nullDerefBool_1)
          and 
          (
            l12_l9_l0_nullDerefBool_0=l12_l9_l0_nullDerefBool_1)
          and 
          (
            l12_l10_nullDerefBool_0=l12_l10_nullDerefBool_1)
          and 
          (
            l12_l9_nullDerefBool_0=l12_l9_nullDerefBool_1)
          and 
          (
            l12_l6_nullDerefBool_0=l12_l6_nullDerefBool_1)
          and 
          (
            l12_l10_l0_nullDerefBool_0=l12_l10_l0_nullDerefBool_1)
          and 
          (
            l12_l8_lt_0=l12_l8_lt_1)
          and 
          (
            l12_l3_l0_result_0=l12_l3_l0_result_2)
          and 
          (
            child_0=child_10)
          and 
          (
            l12_l6_lt_0=l12_l6_lt_1)
          and 
          (
            l12_l11_l0_result_0=l12_l11_l0_result_2)
          and 
          (
            l12_l11_lte_0=l12_l11_lte_2)
          and 
          (
            l12_l2_l0_nullDerefBool_0=l12_l2_l0_nullDerefBool_1)
          and 
          (
            l12_prevTemp_0=l12_prevTemp_11)
          and 
          (
            l12_l4_lte_0=l12_l4_lte_2)
          and 
          (
            l12_l7_lt_0=l12_l7_lt_1)
          and 
          (
            l12_l6_l0_result_0=l12_l6_l0_result_2)
          and 
          (
            l12_l10_l0_result_0=l12_l10_l0_result_2)
          and 
          (
            l12_l3_nullDerefBool_0=l12_l3_nullDerefBool_1)
          and 
          (
            l12_l11_l0_nullDerefBool_0=l12_l11_l0_nullDerefBool_1)
          and 
          (
            l12_l5_lte_0=l12_l5_lte_2)
          and 
          (
            l12_nullDerefBool_0=l12_nullDerefBool_83)
          and 
          (
            l12_l1_temp1_0=l12_l1_temp1_22)
          and 
          (
            l12_l4_l0_result_0=l12_l4_l0_result_2)
          and 
          (
            l12_l1_temp2_0=l12_l1_temp2_11)
          and 
          (
            l12_l9_l0_result_0=l12_l9_l0_result_2)
          and 
          (
            l12_l8_l0_result_0=l12_l8_l0_result_2)
          and 
          (
            l12_l7_nullDerefBool_0=l12_l7_nullDerefBool_1)
          and 
          (
            degree_0=degree_10)
          and 
          (
            sibling_0=sibling_41)
          and 
          (
            l12_l7_l0_nullDerefBool_0=l12_l7_l0_nullDerefBool_1)
          and 
          (
            l12_l1_tmp_0=l12_l1_tmp_10)
          and 
          (
            throw_1=throw_45)
        )
      )
      and 
      (
        (
          BinHeapCondition60[thiz_0]
          and 
          (
            (
              BinHeapCondition0[throw_45]
              and 
              (
                nullDerefBool_5=true)
            )
            or 
            (
              (
                not (
                  BinHeapCondition0[throw_45])
              )
              and 
              TruePred[]
              and 
              (
                nullDerefBool_3=nullDerefBool_5)
            )
          )
        )
        or 
        (
          (
            not (
              BinHeapCondition60[thiz_0])
          )
          and 
          TruePred[]
          and 
          (
            nullDerefBool_3=nullDerefBool_5)
        )
      )
      and 
      (
        (
          BinHeapCondition0[throw_45]
          and 
          (
            size_1=(size_0)++((thiz_0)->(add[thiz_0.size_0,1])))
        )
        or 
        (
          (
            not (
              BinHeapCondition0[throw_45])
          )
          and 
          TruePred[]
          and 
          (
            size_0=size_1)
        )
      )
    )
  )
  and 
  (
    (
      BinHeapCondition30[nullDerefBool_5,
                        throw_45]
      and 
      (
        (
          BinHeapCondition0[throw_45]
          and 
          (
            throw_46=NullPointerExceptionLit)
        )
        or 
        (
          (
            not (
              BinHeapCondition0[throw_45])
          )
          and 
          TruePred[]
          and 
          (
            throw_45=throw_46)
        )
      )
    )
    or 
    (
      (
        not (
          BinHeapCondition30[nullDerefBool_5,
                            throw_45]
        )
      )
      and 
      TruePred[]
      and 
      (
        throw_45=throw_46)
    )
  )

}



pred Data_data_lt_0[
  thiz_0: Data,
  throw_0: Throwable + null,
  throw_1: Throwable + null,
  throw_2: Throwable + null,
  return_0: boolean,
  return_1: boolean,
  data_0: Data + null,
  result_0: boolean,
  result_1: boolean,
  result_2: boolean,
  nullDerefBool_0: boolean,
  nullDerefBool_1: boolean
]{
  TruePred[]
  and 
  (
    (
      DataCondition0[throw_0]
      and 
      (
        nullDerefBool_1=false)
    )
    or 
    (
      (
        not (
          DataCondition0[throw_0])
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
      DataCondition0[throw_0]
      and 
      (
        throw_1=null)
    )
    or 
    (
      (
        not (
          DataCondition0[throw_0])
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
      DataCondition0[throw_1]
      and 
      (
        result_1=false)
    )
    or 
    (
      (
        not (
          DataCondition0[throw_1])
      )
      and 
      TruePred[]
      and 
      (
        result_0=result_1)
    )
  )
  and 
  (
    (
      DataCondition78[thiz_0]
      and 
      (
        (
          DataCondition2[data_0]
          and 
          (
            (
              DataCondition0[throw_1]
              and 
              (
                result_2=true)
            )
            or 
            (
              (
                not (
                  DataCondition0[throw_1])
              )
              and 
              TruePred[]
              and 
              (
                result_1=result_2)
            )
          )
        )
        or 
        (
          (
            not (
              DataCondition2[data_0])
          )
          and 
          TruePred[]
          and 
          (
            result_1=result_2)
        )
      )
    )
    or 
    (
      (
        not (
          DataCondition78[thiz_0])
      )
      and 
      (
        (
          DataCondition76[thiz_0]
          and 
          (
            (
              DataCondition4[data_0]
              and 
              (
                (
                  DataCondition0[throw_1]
                  and 
                  (
                    result_2=true)
                )
                or 
                (
                  (
                    not (
                      DataCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    result_1=result_2)
                )
              )
            )
            or 
            (
              (
                not (
                  DataCondition4[data_0])
              )
              and 
              TruePred[]
              and 
              (
                result_1=result_2)
            )
          )
        )
        or 
        (
          (
            not (
              DataCondition76[thiz_0])
          )
          and 
          (
            (
              DataCondition74[thiz_0]
              and 
              (
                (
                  DataCondition6[data_0]
                  and 
                  (
                    (
                      DataCondition0[throw_1]
                      and 
                      (
                        result_2=true)
                    )
                    or 
                    (
                      (
                        not (
                          DataCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        result_1=result_2)
                    )
                  )
                )
                or 
                (
                  (
                    not (
                      DataCondition6[data_0])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    result_1=result_2)
                )
              )
            )
            or 
            (
              (
                not (
                  DataCondition74[thiz_0])
              )
              and 
              (
                (
                  DataCondition72[thiz_0]
                  and 
                  (
                    (
                      DataCondition8[data_0]
                      and 
                      (
                        (
                          DataCondition0[throw_1]
                          and 
                          (
                            result_2=true)
                        )
                        or 
                        (
                          (
                            not (
                              DataCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            result_1=result_2)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          DataCondition8[data_0])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        result_1=result_2)
                    )
                  )
                )
                or 
                (
                  (
                    not (
                      DataCondition72[thiz_0])
                  )
                  and 
                  (
                    (
                      DataCondition70[thiz_0]
                      and 
                      (
                        (
                          DataCondition10[data_0]
                          and 
                          (
                            (
                              DataCondition0[throw_1]
                              and 
                              (
                                result_2=true)
                            )
                            or 
                            (
                              (
                                not (
                                  DataCondition0[throw_1])
                              )
                              and 
                              TruePred[]
                              and 
                              (
                                result_1=result_2)
                            )
                          )
                        )
                        or 
                        (
                          (
                            not (
                              DataCondition10[data_0])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            result_1=result_2)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          DataCondition70[thiz_0])
                      )
                      and 
                      (
                        (
                          DataCondition68[thiz_0]
                          and 
                          (
                            (
                              DataCondition12[data_0]
                              and 
                              (
                                (
                                  DataCondition0[throw_1]
                                  and 
                                  (
                                    result_2=true)
                                )
                                or 
                                (
                                  (
                                    not (
                                      DataCondition0[throw_1])
                                  )
                                  and 
                                  TruePred[]
                                  and 
                                  (
                                    result_1=result_2)
                                )
                              )
                            )
                            or 
                            (
                              (
                                not (
                                  DataCondition12[data_0])
                              )
                              and 
                              TruePred[]
                              and 
                              (
                                result_1=result_2)
                            )
                          )
                        )
                        or 
                        (
                          (
                            not (
                              DataCondition68[thiz_0])
                          )
                          and 
                          (
                            (
                              DataCondition66[thiz_0]
                              and 
                              (
                                (
                                  DataCondition14[data_0]
                                  and 
                                  (
                                    (
                                      DataCondition0[throw_1]
                                      and 
                                      (
                                        result_2=true)
                                    )
                                    or 
                                    (
                                      (
                                        not (
                                          DataCondition0[throw_1])
                                      )
                                      and 
                                      TruePred[]
                                      and 
                                      (
                                        result_1=result_2)
                                    )
                                  )
                                )
                                or 
                                (
                                  (
                                    not (
                                      DataCondition14[data_0])
                                  )
                                  and 
                                  TruePred[]
                                  and 
                                  (
                                    result_1=result_2)
                                )
                              )
                            )
                            or 
                            (
                              (
                                not (
                                  DataCondition66[thiz_0])
                              )
                              and 
                              (
                                (
                                  DataCondition64[thiz_0]
                                  and 
                                  (
                                    (
                                      DataCondition16[data_0]
                                      and 
                                      (
                                        (
                                          DataCondition0[throw_1]
                                          and 
                                          (
                                            result_2=true)
                                        )
                                        or 
                                        (
                                          (
                                            not (
                                              DataCondition0[throw_1])
                                          )
                                          and 
                                          TruePred[]
                                          and 
                                          (
                                            result_1=result_2)
                                        )
                                      )
                                    )
                                    or 
                                    (
                                      (
                                        not (
                                          DataCondition16[data_0])
                                      )
                                      and 
                                      TruePred[]
                                      and 
                                      (
                                        result_1=result_2)
                                    )
                                  )
                                )
                                or 
                                (
                                  (
                                    not (
                                      DataCondition64[thiz_0])
                                  )
                                  and 
                                  (
                                    (
                                      DataCondition62[thiz_0]
                                      and 
                                      (
                                        (
                                          DataCondition18[data_0]
                                          and 
                                          (
                                            (
                                              DataCondition0[throw_1]
                                              and 
                                              (
                                                result_2=true)
                                            )
                                            or 
                                            (
                                              (
                                                not (
                                                  DataCondition0[throw_1])
                                              )
                                              and 
                                              TruePred[]
                                              and 
                                              (
                                                result_1=result_2)
                                            )
                                          )
                                        )
                                        or 
                                        (
                                          (
                                            not (
                                              DataCondition18[data_0])
                                          )
                                          and 
                                          TruePred[]
                                          and 
                                          (
                                            result_1=result_2)
                                        )
                                      )
                                    )
                                    or 
                                    (
                                      (
                                        not (
                                          DataCondition62[thiz_0])
                                      )
                                      and 
                                      (
                                        (
                                          DataCondition60[thiz_0]
                                          and 
                                          (
                                            (
                                              DataCondition20[data_0]
                                              and 
                                              (
                                                (
                                                  DataCondition0[throw_1]
                                                  and 
                                                  (
                                                    result_2=true)
                                                )
                                                or 
                                                (
                                                  (
                                                    not (
                                                      DataCondition0[throw_1])
                                                  )
                                                  and 
                                                  TruePred[]
                                                  and 
                                                  (
                                                    result_1=result_2)
                                                )
                                              )
                                            )
                                            or 
                                            (
                                              (
                                                not (
                                                  DataCondition20[data_0])
                                              )
                                              and 
                                              TruePred[]
                                              and 
                                              (
                                                result_1=result_2)
                                            )
                                          )
                                        )
                                        or 
                                        (
                                          (
                                            not (
                                              DataCondition60[thiz_0])
                                          )
                                          and 
                                          (
                                            (
                                              DataCondition58[thiz_0]
                                              and 
                                              (
                                                (
                                                  DataCondition22[data_0]
                                                  and 
                                                  (
                                                    (
                                                      DataCondition0[throw_1]
                                                      and 
                                                      (
                                                        result_2=true)
                                                    )
                                                    or 
                                                    (
                                                      (
                                                        not (
                                                          DataCondition0[throw_1])
                                                      )
                                                      and 
                                                      TruePred[]
                                                      and 
                                                      (
                                                        result_1=result_2)
                                                    )
                                                  )
                                                )
                                                or 
                                                (
                                                  (
                                                    not (
                                                      DataCondition22[data_0])
                                                  )
                                                  and 
                                                  TruePred[]
                                                  and 
                                                  (
                                                    result_1=result_2)
                                                )
                                              )
                                            )
                                            or 
                                            (
                                              (
                                                not (
                                                  DataCondition58[thiz_0])
                                              )
                                              and 
                                              (
                                                (
                                                  DataCondition56[thiz_0]
                                                  and 
                                                  (
                                                    (
                                                      DataCondition24[data_0]
                                                      and 
                                                      (
                                                        (
                                                          DataCondition0[throw_1]
                                                          and 
                                                          (
                                                            result_2=true)
                                                        )
                                                        or 
                                                        (
                                                          (
                                                            not (
                                                              DataCondition0[throw_1])
                                                          )
                                                          and 
                                                          TruePred[]
                                                          and 
                                                          (
                                                            result_1=result_2)
                                                        )
                                                      )
                                                    )
                                                    or 
                                                    (
                                                      (
                                                        not (
                                                          DataCondition24[data_0])
                                                      )
                                                      and 
                                                      TruePred[]
                                                      and 
                                                      (
                                                        result_1=result_2)
                                                    )
                                                  )
                                                )
                                                or 
                                                (
                                                  (
                                                    not (
                                                      DataCondition56[thiz_0])
                                                  )
                                                  and 
                                                  (
                                                    (
                                                      DataCondition54[thiz_0]
                                                      and 
                                                      (
                                                        (
                                                          DataCondition26[data_0]
                                                          and 
                                                          (
                                                            (
                                                              DataCondition0[throw_1]
                                                              and 
                                                              (
                                                                result_2=true)
                                                            )
                                                            or 
                                                            (
                                                              (
                                                                not (
                                                                  DataCondition0[throw_1])
                                                              )
                                                              and 
                                                              TruePred[]
                                                              and 
                                                              (
                                                                result_1=result_2)
                                                            )
                                                          )
                                                        )
                                                        or 
                                                        (
                                                          (
                                                            not (
                                                              DataCondition26[data_0])
                                                          )
                                                          and 
                                                          TruePred[]
                                                          and 
                                                          (
                                                            result_1=result_2)
                                                        )
                                                      )
                                                    )
                                                    or 
                                                    (
                                                      (
                                                        not (
                                                          DataCondition54[thiz_0])
                                                      )
                                                      and 
                                                      (
                                                        (
                                                          DataCondition52[thiz_0]
                                                          and 
                                                          (
                                                            (
                                                              DataCondition28[data_0]
                                                              and 
                                                              (
                                                                (
                                                                  DataCondition0[throw_1]
                                                                  and 
                                                                  (
                                                                    result_2=true)
                                                                )
                                                                or 
                                                                (
                                                                  (
                                                                    not (
                                                                      DataCondition0[throw_1])
                                                                  )
                                                                  and 
                                                                  TruePred[]
                                                                  and 
                                                                  (
                                                                    result_1=result_2)
                                                                )
                                                              )
                                                            )
                                                            or 
                                                            (
                                                              (
                                                                not (
                                                                  DataCondition28[data_0])
                                                              )
                                                              and 
                                                              TruePred[]
                                                              and 
                                                              (
                                                                result_1=result_2)
                                                            )
                                                          )
                                                        )
                                                        or 
                                                        (
                                                          (
                                                            not (
                                                              DataCondition52[thiz_0])
                                                          )
                                                          and 
                                                          (
                                                            (
                                                              DataCondition50[thiz_0]
                                                              and 
                                                              (
                                                                (
                                                                  DataCondition30[data_0]
                                                                  and 
                                                                  (
                                                                    (
                                                                      DataCondition0[throw_1]
                                                                      and 
                                                                      (
                                                                        result_2=true)
                                                                    )
                                                                    or 
                                                                    (
                                                                      (
                                                                        not (
                                                                          DataCondition0[throw_1])
                                                                      )
                                                                      and 
                                                                      TruePred[]
                                                                      and 
                                                                      (
                                                                        result_1=result_2)
                                                                    )
                                                                  )
                                                                )
                                                                or 
                                                                (
                                                                  (
                                                                    not (
                                                                      DataCondition30[data_0])
                                                                  )
                                                                  and 
                                                                  TruePred[]
                                                                  and 
                                                                  (
                                                                    result_1=result_2)
                                                                )
                                                              )
                                                            )
                                                            or 
                                                            (
                                                              (
                                                                not (
                                                                  DataCondition50[thiz_0])
                                                              )
                                                              and 
                                                              (
                                                                (
                                                                  DataCondition48[thiz_0]
                                                                  and 
                                                                  (
                                                                    (
                                                                      DataCondition32[data_0]
                                                                      and 
                                                                      (
                                                                        (
                                                                          DataCondition0[throw_1]
                                                                          and 
                                                                          (
                                                                            result_2=true)
                                                                        )
                                                                        or 
                                                                        (
                                                                          (
                                                                            not (
                                                                              DataCondition0[throw_1])
                                                                          )
                                                                          and 
                                                                          TruePred[]
                                                                          and 
                                                                          (
                                                                            result_1=result_2)
                                                                        )
                                                                      )
                                                                    )
                                                                    or 
                                                                    (
                                                                      (
                                                                        not (
                                                                          DataCondition32[data_0])
                                                                      )
                                                                      and 
                                                                      TruePred[]
                                                                      and 
                                                                      (
                                                                        result_1=result_2)
                                                                    )
                                                                  )
                                                                )
                                                                or 
                                                                (
                                                                  (
                                                                    not (
                                                                      DataCondition48[thiz_0])
                                                                  )
                                                                  and 
                                                                  (
                                                                    (
                                                                      DataCondition46[thiz_0]
                                                                      and 
                                                                      (
                                                                        (
                                                                          DataCondition34[data_0]
                                                                          and 
                                                                          (
                                                                            (
                                                                              DataCondition0[throw_1]
                                                                              and 
                                                                              (
                                                                                result_2=true)
                                                                            )
                                                                            or 
                                                                            (
                                                                              (
                                                                                not (
                                                                                  DataCondition0[throw_1])
                                                                              )
                                                                              and 
                                                                              TruePred[]
                                                                              and 
                                                                              (
                                                                                result_1=result_2)
                                                                            )
                                                                          )
                                                                        )
                                                                        or 
                                                                        (
                                                                          (
                                                                            not (
                                                                              DataCondition34[data_0])
                                                                          )
                                                                          and 
                                                                          TruePred[]
                                                                          and 
                                                                          (
                                                                            result_1=result_2)
                                                                        )
                                                                      )
                                                                    )
                                                                    or 
                                                                    (
                                                                      (
                                                                        not (
                                                                          DataCondition46[thiz_0])
                                                                      )
                                                                      and 
                                                                      (
                                                                        (
                                                                          DataCondition44[thiz_0]
                                                                          and 
                                                                          (
                                                                            (
                                                                              DataCondition36[data_0]
                                                                              and 
                                                                              (
                                                                                (
                                                                                  DataCondition0[throw_1]
                                                                                  and 
                                                                                  (
                                                                                    result_2=true)
                                                                                )
                                                                                or 
                                                                                (
                                                                                  (
                                                                                    not (
                                                                                      DataCondition0[throw_1])
                                                                                  )
                                                                                  and 
                                                                                  TruePred[]
                                                                                  and 
                                                                                  (
                                                                                    result_1=result_2)
                                                                                )
                                                                              )
                                                                            )
                                                                            or 
                                                                            (
                                                                              (
                                                                                not (
                                                                                  DataCondition36[data_0])
                                                                              )
                                                                              and 
                                                                              TruePred[]
                                                                              and 
                                                                              (
                                                                                result_1=result_2)
                                                                            )
                                                                          )
                                                                        )
                                                                        or 
                                                                        (
                                                                          (
                                                                            not (
                                                                              DataCondition44[thiz_0])
                                                                          )
                                                                          and 
                                                                          (
                                                                            (
                                                                              DataCondition42[thiz_0]
                                                                              and 
                                                                              (
                                                                                (
                                                                                  DataCondition38[data_0]
                                                                                  and 
                                                                                  (
                                                                                    (
                                                                                      DataCondition0[throw_1]
                                                                                      and 
                                                                                      (
                                                                                        result_2=true)
                                                                                    )
                                                                                    or 
                                                                                    (
                                                                                      (
                                                                                        not (
                                                                                          DataCondition0[throw_1])
                                                                                      )
                                                                                      and 
                                                                                      TruePred[]
                                                                                      and 
                                                                                      (
                                                                                        result_1=result_2)
                                                                                    )
                                                                                  )
                                                                                )
                                                                                or 
                                                                                (
                                                                                  (
                                                                                    not (
                                                                                      DataCondition38[data_0])
                                                                                  )
                                                                                  and 
                                                                                  TruePred[]
                                                                                  and 
                                                                                  (
                                                                                    result_1=result_2)
                                                                                )
                                                                              )
                                                                            )
                                                                            or 
                                                                            (
                                                                              (
                                                                                not (
                                                                                  DataCondition42[thiz_0])
                                                                              )
                                                                              and 
                                                                              (
                                                                                (
                                                                                  DataCondition40[thiz_0]
                                                                                  and 
                                                                                  (
                                                                                    (
                                                                                      DataCondition0[throw_1]
                                                                                      and 
                                                                                      (
                                                                                        result_2=false)
                                                                                    )
                                                                                    or 
                                                                                    (
                                                                                      (
                                                                                        not (
                                                                                          DataCondition0[throw_1])
                                                                                      )
                                                                                      and 
                                                                                      TruePred[]
                                                                                      and 
                                                                                      (
                                                                                        result_1=result_2)
                                                                                    )
                                                                                  )
                                                                                )
                                                                                or 
                                                                                (
                                                                                  (
                                                                                    not (
                                                                                      DataCondition40[thiz_0])
                                                                                  )
                                                                                  and 
                                                                                  TruePred[]
                                                                                  and 
                                                                                  (
                                                                                    result_1=result_2)
                                                                                )
                                                                              )
                                                                            )
                                                                          )
                                                                        )
                                                                      )
                                                                    )
                                                                  )
                                                                )
                                                              )
                                                            )
                                                          )
                                                        )
                                                      )
                                                    )
                                                  )
                                                )
                                              )
                                            )
                                          )
                                        )
                                      )
                                    )
                                  )
                                )
                              )
                            )
                          )
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
  )
  and 
  (
    (
      DataCondition0[throw_1]
      and 
      (
        return_1=result_2)
    )
    or 
    (
      (
        not (
          DataCondition0[throw_1])
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
      DataCondition80[nullDerefBool_1,
                     throw_1]
      and 
      (
        (
          DataCondition0[throw_1]
          and 
          (
            throw_2=NullPointerExceptionLit)
        )
        or 
        (
          (
            not (
              DataCondition0[throw_1])
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
          DataCondition80[nullDerefBool_1,
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



pred BinHeap_merge_0[
  thiz_0: BinHeap,
  throw_0: Throwable + null,
  throw_1: Throwable + null,
  throw_2: Throwable + null,
  binHeap_0: BinHeapNode + null,
  head_0: ( BinHeap ) -> one ( BinHeapNode + null ),
  head_1: ( BinHeap ) -> one ( BinHeapNode + null ),
  head_2: ( BinHeap ) -> one ( BinHeapNode + null ),
  head_3: ( BinHeap ) -> one ( BinHeapNode + null ),
  head_4: ( BinHeap ) -> one ( BinHeapNode + null ),
  head_5: ( BinHeap ) -> one ( BinHeapNode + null ),
  head_6: ( BinHeap ) -> one ( BinHeapNode + null ),
  head_7: ( BinHeap ) -> one ( BinHeapNode + null ),
  head_8: ( BinHeap ) -> one ( BinHeapNode + null ),
  head_9: ( BinHeap ) -> one ( BinHeapNode + null ),
  head_10: ( BinHeap ) -> one ( BinHeapNode + null ),
  degree_0: ( BinHeapNode ) -> one ( Int ),
  sibling_0: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_1: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_2: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_3: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_4: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_5: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_6: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_7: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_8: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_9: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_10: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_11: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_12: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_13: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_14: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_15: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_16: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_17: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_18: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_19: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_20: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_21: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  temp1_0: BinHeapNode + null,
  temp1_1: BinHeapNode + null,
  temp1_2: BinHeapNode + null,
  temp1_3: BinHeapNode + null,
  temp1_4: BinHeapNode + null,
  temp1_5: BinHeapNode + null,
  temp1_6: BinHeapNode + null,
  temp1_7: BinHeapNode + null,
  temp1_8: BinHeapNode + null,
  temp1_9: BinHeapNode + null,
  temp1_10: BinHeapNode + null,
  temp1_11: BinHeapNode + null,
  temp1_12: BinHeapNode + null,
  temp1_13: BinHeapNode + null,
  temp1_14: BinHeapNode + null,
  temp1_15: BinHeapNode + null,
  temp1_16: BinHeapNode + null,
  temp1_17: BinHeapNode + null,
  temp1_18: BinHeapNode + null,
  temp1_19: BinHeapNode + null,
  temp1_20: BinHeapNode + null,
  temp1_21: BinHeapNode + null,
  temp1_22: BinHeapNode + null,
  temp2_0: BinHeapNode + null,
  temp2_1: BinHeapNode + null,
  temp2_2: BinHeapNode + null,
  temp2_3: BinHeapNode + null,
  temp2_4: BinHeapNode + null,
  temp2_5: BinHeapNode + null,
  temp2_6: BinHeapNode + null,
  temp2_7: BinHeapNode + null,
  temp2_8: BinHeapNode + null,
  temp2_9: BinHeapNode + null,
  temp2_10: BinHeapNode + null,
  temp2_11: BinHeapNode + null,
  tmp_0: BinHeapNode + null,
  tmp_1: BinHeapNode + null,
  tmp_2: BinHeapNode + null,
  tmp_3: BinHeapNode + null,
  tmp_4: BinHeapNode + null,
  tmp_5: BinHeapNode + null,
  tmp_6: BinHeapNode + null,
  tmp_7: BinHeapNode + null,
  tmp_8: BinHeapNode + null,
  tmp_9: BinHeapNode + null,
  tmp_10: BinHeapNode + null,
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
  nullDerefBool_29: boolean,
  nullDerefBool_30: boolean,
  nullDerefBool_31: boolean,
  nullDerefBool_32: boolean,
  nullDerefBool_33: boolean,
  nullDerefBool_34: boolean,
  nullDerefBool_35: boolean,
  nullDerefBool_36: boolean,
  nullDerefBool_37: boolean,
  nullDerefBool_38: boolean,
  nullDerefBool_39: boolean,
  nullDerefBool_40: boolean,
  nullDerefBool_41: boolean,
  nullDerefBool_42: boolean,
  nullDerefBool_43: boolean,
  nullDerefBool_44: boolean,
  nullDerefBool_45: boolean,
  nullDerefBool_46: boolean,
  nullDerefBool_47: boolean,
  nullDerefBool_48: boolean,
  nullDerefBool_49: boolean,
  nullDerefBool_50: boolean,
  nullDerefBool_51: boolean,
  nullDerefBool_52: boolean,
  nullDerefBool_53: boolean,
  nullDerefBool_54: boolean,
  nullDerefBool_55: boolean,
  nullDerefBool_56: boolean,
  nullDerefBool_57: boolean,
  nullDerefBool_58: boolean,
  nullDerefBool_59: boolean,
  nullDerefBool_60: boolean,
  nullDerefBool_61: boolean,
  nullDerefBool_62: boolean,
  nullDerefBool_63: boolean,
  nullDerefBool_64: boolean,
  nullDerefBool_65: boolean,
  nullDerefBool_66: boolean,
  nullDerefBool_67: boolean,
  nullDerefBool_68: boolean,
  nullDerefBool_69: boolean,
  nullDerefBool_70: boolean,
  nullDerefBool_71: boolean,
  nullDerefBool_72: boolean,
  nullDerefBool_73: boolean,
  nullDerefBool_74: boolean,
  nullDerefBool_75: boolean,
  nullDerefBool_76: boolean,
  nullDerefBool_77: boolean,
  nullDerefBool_78: boolean,
  nullDerefBool_79: boolean,
  nullDerefBool_80: boolean,
  nullDerefBool_81: boolean,
  nullDerefBool_82: boolean,
  nullDerefBool_83: boolean,
  nullDerefBool_84: boolean,
  nullDerefBool_85: boolean
]{
  TruePred[]
  and 
  (
    (
      BinHeapCondition0[throw_0]
      and 
      (
        nullDerefBool_1=false)
    )
    or 
    (
      (
        not (
          BinHeapCondition0[throw_0])
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
      BinHeapCondition0[throw_0]
      and 
      (
        throw_1=null)
    )
    or 
    (
      (
        not (
          BinHeapCondition0[throw_0])
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
      BinHeapCondition2[thiz_0]
      and 
      (
        (
          BinHeapCondition0[throw_1]
          and 
          (
            nullDerefBool_2=true)
        )
        or 
        (
          (
            not (
              BinHeapCondition0[throw_1])
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
          BinHeapCondition2[thiz_0])
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
      BinHeapCondition0[throw_1]
      and 
      (
        temp1_1=thiz_0.head_0)
    )
    or 
    (
      (
        not (
          BinHeapCondition0[throw_1])
      )
      and 
      TruePred[]
      and 
      (
        temp1_0=temp1_1)
    )
  )
  and 
  TruePred[]
  and 
  (
    (
      BinHeapCondition0[throw_1]
      and 
      (
        temp2_1=binHeap_0)
    )
    or 
    (
      (
        not (
          BinHeapCondition0[throw_1])
      )
      and 
      TruePred[]
      and 
      (
        temp2_0=temp2_1)
    )
  )
  and 
  (
    (
      BinHeapCondition0[throw_1]
      and 
      (
        (
          BinHeapCondition52[temp1_1,
                            temp2_1]
          and 
          (
            (
              BinHeapCondition32[temp1_1,
                                temp2_1]
              and 
              (
                (
                  BinHeapCondition0[throw_1]
                  and 
                  (
                    nullDerefBool_3=true)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_1])
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
                  BinHeapCondition32[temp1_1,
                                    temp2_1]
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
            (
              BinHeapCondition50[degree_0,
                                temp1_1,
                                temp2_1]
              and 
              TruePred[]
              and 
              (
                (
                  BinHeapCondition0[throw_1]
                  and 
                  (
                    tmp_1=temp2_1)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    tmp_0=tmp_1)
                )
              )
              and 
              (
                (
                  BinHeapCondition34[temp2_1]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        nullDerefBool_4=true)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
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
                      BinHeapCondition34[temp2_1])
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
                  BinHeapCondition0[throw_1]
                  and 
                  (
                    temp2_2=temp2_1.sibling_0)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    temp2_1=temp2_2)
                )
              )
              and 
              (
                (
                  BinHeapCondition36[temp1_1,
                                    tmp_1]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        nullDerefBool_5=true)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
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
                      BinHeapCondition36[temp1_1,
                                        tmp_1]
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
                  BinHeapCondition0[throw_1]
                  and 
                  (
                    sibling_1=(sibling_0)++((tmp_1)->(temp1_1.sibling_0)))
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    sibling_0=sibling_1)
                )
              )
              and 
              (
                (
                  BinHeapCondition38[temp1_1]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        nullDerefBool_6=true)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
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
                      BinHeapCondition38[temp1_1])
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
                  BinHeapCondition0[throw_1]
                  and 
                  (
                    sibling_2=(sibling_1)++((temp1_1)->(tmp_1)))
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    sibling_1=sibling_2)
                )
              )
              and 
              (
                (
                  BinHeapCondition40[tmp_1]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        nullDerefBool_9=true)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_6=nullDerefBool_9)
                    )
                  )
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition40[tmp_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_6=nullDerefBool_9)
                )
              )
              and 
              (
                (
                  BinHeapCondition0[throw_1]
                  and 
                  (
                    temp1_2=tmp_1.sibling_2)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    temp1_1=temp1_2)
                )
              )
              and 
              (
                head_0=head_1)
            )
            or 
            (
              (
                not (
                  BinHeapCondition50[degree_0,
                                    temp1_1,
                                    temp2_1]
                )
              )
              and 
              (
                (
                  BinHeapCondition32[temp1_1,
                                    temp2_1]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        nullDerefBool_4=true)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
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
                      BinHeapCondition32[temp1_1,
                                        temp2_1]
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
                (
                  BinHeapCondition48[degree_0,
                                    temp1_1,
                                    temp2_1]
                  and 
                  (
                    (
                      BinHeapCondition42[sibling_0,
                                        temp1_1,
                                        temp2_1]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            nullDerefBool_5=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
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
                          BinHeapCondition42[sibling_0,
                                            temp1_1,
                                            temp2_1]
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
                      BinHeapCondition44[degree_0,
                                        sibling_0,
                                        temp1_1,
                                        temp2_1]
                      and 
                      TruePred[]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            tmp_1=temp2_1)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            tmp_0=tmp_1)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition34[temp2_1]
                          and 
                          (
                            (
                              BinHeapCondition0[throw_1]
                              and 
                              (
                                nullDerefBool_6=true)
                            )
                            or 
                            (
                              (
                                not (
                                  BinHeapCondition0[throw_1])
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
                              BinHeapCondition34[temp2_1])
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
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            temp2_2=temp2_1.sibling_0)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            temp2_1=temp2_2)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition36[temp1_1,
                                            tmp_1]
                          and 
                          (
                            (
                              BinHeapCondition0[throw_1]
                              and 
                              (
                                nullDerefBool_7=true)
                            )
                            or 
                            (
                              (
                                not (
                                  BinHeapCondition0[throw_1])
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
                              BinHeapCondition36[temp1_1,
                                                tmp_1]
                            )
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
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            sibling_1=(sibling_0)++((tmp_1)->(temp1_1.sibling_0)))
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            sibling_0=sibling_1)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition38[temp1_1]
                          and 
                          (
                            (
                              BinHeapCondition0[throw_1]
                              and 
                              (
                                nullDerefBool_8=true)
                            )
                            or 
                            (
                              (
                                not (
                                  BinHeapCondition0[throw_1])
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
                              BinHeapCondition38[temp1_1])
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
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            sibling_2=(sibling_1)++((temp1_1)->(tmp_1)))
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            sibling_1=sibling_2)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition40[tmp_1]
                          and 
                          (
                            (
                              BinHeapCondition0[throw_1]
                              and 
                              (
                                nullDerefBool_9=true)
                            )
                            or 
                            (
                              (
                                not (
                                  BinHeapCondition0[throw_1])
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
                              BinHeapCondition40[tmp_1])
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
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            temp1_2=tmp_1.sibling_2)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            temp1_1=temp1_2)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition44[degree_0,
                                            sibling_0,
                                            temp1_1,
                                            temp2_1]
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition38[temp1_1]
                          and 
                          (
                            (
                              BinHeapCondition0[throw_1]
                              and 
                              (
                                nullDerefBool_9=true)
                            )
                            or 
                            (
                              (
                                not (
                                  BinHeapCondition0[throw_1])
                              )
                              and 
                              TruePred[]
                              and 
                              (
                                nullDerefBool_5=nullDerefBool_9)
                            )
                          )
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition38[temp1_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_5=nullDerefBool_9)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            temp1_2=temp1_1.sibling_0)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            temp1_1=temp1_2)
                        )
                      )
                      and 
                      (
                        tmp_0=tmp_1)
                      and 
                      (
                        temp2_1=temp2_2)
                      and 
                      (
                        sibling_0=sibling_2)
                    )
                  )
                  and 
                  (
                    head_0=head_1)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition48[degree_0,
                                        temp1_1,
                                        temp2_1]
                    )
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        tmp_1=temp1_1)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        tmp_0=tmp_1)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        temp1_2=temp2_1)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        temp1_1=temp1_2)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition34[temp2_1]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            nullDerefBool_5=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
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
                          BinHeapCondition34[temp2_1])
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
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        temp2_2=temp2_1.sibling_0)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        temp2_1=temp2_2)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition38[temp1_2]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            nullDerefBool_6=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
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
                          BinHeapCondition38[temp1_2])
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
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        sibling_2=(sibling_0)++((temp1_2)->(tmp_1)))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        sibling_0=sibling_2)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition2[thiz_0]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            nullDerefBool_7=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
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
                          BinHeapCondition2[thiz_0])
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
                      BinHeapCondition46[head_0,
                                        thiz_0,
                                        tmp_1]
                      and 
                      (
                        (
                          BinHeapCondition2[thiz_0]
                          and 
                          (
                            (
                              BinHeapCondition0[throw_1]
                              and 
                              (
                                nullDerefBool_9=true)
                            )
                            or 
                            (
                              (
                                not (
                                  BinHeapCondition0[throw_1])
                              )
                              and 
                              TruePred[]
                              and 
                              (
                                nullDerefBool_7=nullDerefBool_9)
                            )
                          )
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition2[thiz_0])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_7=nullDerefBool_9)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            head_1=(head_0)++((thiz_0)->(temp1_2)))
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            head_0=head_1)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition46[head_0,
                                            thiz_0,
                                            tmp_1]
                        )
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_7=nullDerefBool_9)
                      and 
                      (
                        head_0=head_1)
                    )
                  )
                )
              )
            )
          )
        )
        or 
        (
          TruePred[]
          and 
          (
            temp1_1=temp1_2)
          and 
          (
            temp2_1=temp2_2)
          and 
          (
            sibling_0=sibling_2)
          and 
          (
            nullDerefBool_2=nullDerefBool_9)
          and 
          (
            tmp_0=tmp_1)
          and 
          (
            head_0=head_1)
        )
      )
      and 
      (
        (
          BinHeapCondition52[temp1_2,
                            temp2_2]
          and 
          (
            (
              BinHeapCondition32[temp1_2,
                                temp2_2]
              and 
              (
                (
                  BinHeapCondition0[throw_1]
                  and 
                  (
                    nullDerefBool_10=true)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_1])
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
                  BinHeapCondition32[temp1_2,
                                    temp2_2]
                )
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
              BinHeapCondition50[degree_0,
                                temp1_2,
                                temp2_2]
              and 
              TruePred[]
              and 
              (
                (
                  BinHeapCondition0[throw_1]
                  and 
                  (
                    tmp_2=temp2_2)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    tmp_1=tmp_2)
                )
              )
              and 
              (
                (
                  BinHeapCondition34[temp2_2]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        nullDerefBool_11=true)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
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
                      BinHeapCondition34[temp2_2])
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
                  BinHeapCondition0[throw_1]
                  and 
                  (
                    temp2_3=temp2_2.sibling_2)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    temp2_2=temp2_3)
                )
              )
              and 
              (
                (
                  BinHeapCondition36[temp1_2,
                                    tmp_2]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        nullDerefBool_12=true)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
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
                      BinHeapCondition36[temp1_2,
                                        tmp_2]
                    )
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
                  BinHeapCondition0[throw_1]
                  and 
                  (
                    sibling_3=(sibling_2)++((tmp_2)->(temp1_2.sibling_2)))
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    sibling_2=sibling_3)
                )
              )
              and 
              (
                (
                  BinHeapCondition38[temp1_2]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        nullDerefBool_13=true)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
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
                      BinHeapCondition38[temp1_2])
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
                  BinHeapCondition0[throw_1]
                  and 
                  (
                    sibling_4=(sibling_3)++((temp1_2)->(tmp_2)))
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    sibling_3=sibling_4)
                )
              )
              and 
              (
                (
                  BinHeapCondition40[tmp_2]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        nullDerefBool_16=true)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_13=nullDerefBool_16)
                    )
                  )
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition40[tmp_2])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_13=nullDerefBool_16)
                )
              )
              and 
              (
                (
                  BinHeapCondition0[throw_1]
                  and 
                  (
                    temp1_3=tmp_2.sibling_4)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    temp1_2=temp1_3)
                )
              )
              and 
              (
                head_1=head_2)
            )
            or 
            (
              (
                not (
                  BinHeapCondition50[degree_0,
                                    temp1_2,
                                    temp2_2]
                )
              )
              and 
              (
                (
                  BinHeapCondition32[temp1_2,
                                    temp2_2]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        nullDerefBool_11=true)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
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
                      BinHeapCondition32[temp1_2,
                                        temp2_2]
                    )
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
                  BinHeapCondition48[degree_0,
                                    temp1_2,
                                    temp2_2]
                  and 
                  (
                    (
                      BinHeapCondition42[sibling_2,
                                        temp1_2,
                                        temp2_2]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            nullDerefBool_12=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
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
                          BinHeapCondition42[sibling_2,
                                            temp1_2,
                                            temp2_2]
                        )
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
                      BinHeapCondition44[degree_0,
                                        sibling_2,
                                        temp1_2,
                                        temp2_2]
                      and 
                      TruePred[]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            tmp_2=temp2_2)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            tmp_1=tmp_2)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition34[temp2_2]
                          and 
                          (
                            (
                              BinHeapCondition0[throw_1]
                              and 
                              (
                                nullDerefBool_13=true)
                            )
                            or 
                            (
                              (
                                not (
                                  BinHeapCondition0[throw_1])
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
                              BinHeapCondition34[temp2_2])
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
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            temp2_3=temp2_2.sibling_2)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            temp2_2=temp2_3)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition36[temp1_2,
                                            tmp_2]
                          and 
                          (
                            (
                              BinHeapCondition0[throw_1]
                              and 
                              (
                                nullDerefBool_14=true)
                            )
                            or 
                            (
                              (
                                not (
                                  BinHeapCondition0[throw_1])
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
                              BinHeapCondition36[temp1_2,
                                                tmp_2]
                            )
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
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            sibling_3=(sibling_2)++((tmp_2)->(temp1_2.sibling_2)))
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            sibling_2=sibling_3)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition38[temp1_2]
                          and 
                          (
                            (
                              BinHeapCondition0[throw_1]
                              and 
                              (
                                nullDerefBool_15=true)
                            )
                            or 
                            (
                              (
                                not (
                                  BinHeapCondition0[throw_1])
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
                              BinHeapCondition38[temp1_2])
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
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            sibling_4=(sibling_3)++((temp1_2)->(tmp_2)))
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            sibling_3=sibling_4)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition40[tmp_2]
                          and 
                          (
                            (
                              BinHeapCondition0[throw_1]
                              and 
                              (
                                nullDerefBool_16=true)
                            )
                            or 
                            (
                              (
                                not (
                                  BinHeapCondition0[throw_1])
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
                              BinHeapCondition40[tmp_2])
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
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            temp1_3=tmp_2.sibling_4)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            temp1_2=temp1_3)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition44[degree_0,
                                            sibling_2,
                                            temp1_2,
                                            temp2_2]
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition38[temp1_2]
                          and 
                          (
                            (
                              BinHeapCondition0[throw_1]
                              and 
                              (
                                nullDerefBool_16=true)
                            )
                            or 
                            (
                              (
                                not (
                                  BinHeapCondition0[throw_1])
                              )
                              and 
                              TruePred[]
                              and 
                              (
                                nullDerefBool_12=nullDerefBool_16)
                            )
                          )
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition38[temp1_2])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_12=nullDerefBool_16)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            temp1_3=temp1_2.sibling_2)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            temp1_2=temp1_3)
                        )
                      )
                      and 
                      (
                        tmp_1=tmp_2)
                      and 
                      (
                        temp2_2=temp2_3)
                      and 
                      (
                        sibling_2=sibling_4)
                    )
                  )
                  and 
                  (
                    head_1=head_2)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition48[degree_0,
                                        temp1_2,
                                        temp2_2]
                    )
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        tmp_2=temp1_2)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        tmp_1=tmp_2)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        temp1_3=temp2_2)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        temp1_2=temp1_3)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition34[temp2_2]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            nullDerefBool_12=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
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
                          BinHeapCondition34[temp2_2])
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
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        temp2_3=temp2_2.sibling_2)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        temp2_2=temp2_3)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition38[temp1_3]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            nullDerefBool_13=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
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
                          BinHeapCondition38[temp1_3])
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
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        sibling_4=(sibling_2)++((temp1_3)->(tmp_2)))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        sibling_2=sibling_4)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition2[thiz_0]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            nullDerefBool_14=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
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
                          BinHeapCondition2[thiz_0])
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
                      BinHeapCondition46[head_1,
                                        thiz_0,
                                        tmp_2]
                      and 
                      (
                        (
                          BinHeapCondition2[thiz_0]
                          and 
                          (
                            (
                              BinHeapCondition0[throw_1]
                              and 
                              (
                                nullDerefBool_16=true)
                            )
                            or 
                            (
                              (
                                not (
                                  BinHeapCondition0[throw_1])
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
                              BinHeapCondition2[thiz_0])
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
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            head_2=(head_1)++((thiz_0)->(temp1_3)))
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            head_1=head_2)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition46[head_1,
                                            thiz_0,
                                            tmp_2]
                        )
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_14=nullDerefBool_16)
                      and 
                      (
                        head_1=head_2)
                    )
                  )
                )
              )
            )
          )
        )
        or 
        (
          TruePred[]
          and 
          (
            temp1_2=temp1_3)
          and 
          (
            temp2_2=temp2_3)
          and 
          (
            sibling_2=sibling_4)
          and 
          (
            nullDerefBool_9=nullDerefBool_16)
          and 
          (
            tmp_1=tmp_2)
          and 
          (
            head_1=head_2)
        )
      )
      and 
      (
        (
          BinHeapCondition52[temp1_3,
                            temp2_3]
          and 
          (
            (
              BinHeapCondition32[temp1_3,
                                temp2_3]
              and 
              (
                (
                  BinHeapCondition0[throw_1]
                  and 
                  (
                    nullDerefBool_17=true)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_1])
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
                  BinHeapCondition32[temp1_3,
                                    temp2_3]
                )
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
              BinHeapCondition50[degree_0,
                                temp1_3,
                                temp2_3]
              and 
              TruePred[]
              and 
              (
                (
                  BinHeapCondition0[throw_1]
                  and 
                  (
                    tmp_3=temp2_3)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    tmp_2=tmp_3)
                )
              )
              and 
              (
                (
                  BinHeapCondition34[temp2_3]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        nullDerefBool_18=true)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
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
                      BinHeapCondition34[temp2_3])
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
                  BinHeapCondition0[throw_1]
                  and 
                  (
                    temp2_4=temp2_3.sibling_4)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    temp2_3=temp2_4)
                )
              )
              and 
              (
                (
                  BinHeapCondition36[temp1_3,
                                    tmp_3]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        nullDerefBool_19=true)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
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
                      BinHeapCondition36[temp1_3,
                                        tmp_3]
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
                  BinHeapCondition0[throw_1]
                  and 
                  (
                    sibling_5=(sibling_4)++((tmp_3)->(temp1_3.sibling_4)))
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    sibling_4=sibling_5)
                )
              )
              and 
              (
                (
                  BinHeapCondition38[temp1_3]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        nullDerefBool_20=true)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
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
                      BinHeapCondition38[temp1_3])
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
                  BinHeapCondition0[throw_1]
                  and 
                  (
                    sibling_6=(sibling_5)++((temp1_3)->(tmp_3)))
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    sibling_5=sibling_6)
                )
              )
              and 
              (
                (
                  BinHeapCondition40[tmp_3]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        nullDerefBool_23=true)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_20=nullDerefBool_23)
                    )
                  )
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition40[tmp_3])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_20=nullDerefBool_23)
                )
              )
              and 
              (
                (
                  BinHeapCondition0[throw_1]
                  and 
                  (
                    temp1_4=tmp_3.sibling_6)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    temp1_3=temp1_4)
                )
              )
              and 
              (
                head_2=head_3)
            )
            or 
            (
              (
                not (
                  BinHeapCondition50[degree_0,
                                    temp1_3,
                                    temp2_3]
                )
              )
              and 
              (
                (
                  BinHeapCondition32[temp1_3,
                                    temp2_3]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        nullDerefBool_18=true)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
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
                      BinHeapCondition32[temp1_3,
                                        temp2_3]
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
                  BinHeapCondition48[degree_0,
                                    temp1_3,
                                    temp2_3]
                  and 
                  (
                    (
                      BinHeapCondition42[sibling_4,
                                        temp1_3,
                                        temp2_3]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            nullDerefBool_19=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
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
                          BinHeapCondition42[sibling_4,
                                            temp1_3,
                                            temp2_3]
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
                      BinHeapCondition44[degree_0,
                                        sibling_4,
                                        temp1_3,
                                        temp2_3]
                      and 
                      TruePred[]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            tmp_3=temp2_3)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            tmp_2=tmp_3)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition34[temp2_3]
                          and 
                          (
                            (
                              BinHeapCondition0[throw_1]
                              and 
                              (
                                nullDerefBool_20=true)
                            )
                            or 
                            (
                              (
                                not (
                                  BinHeapCondition0[throw_1])
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
                              BinHeapCondition34[temp2_3])
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
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            temp2_4=temp2_3.sibling_4)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            temp2_3=temp2_4)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition36[temp1_3,
                                            tmp_3]
                          and 
                          (
                            (
                              BinHeapCondition0[throw_1]
                              and 
                              (
                                nullDerefBool_21=true)
                            )
                            or 
                            (
                              (
                                not (
                                  BinHeapCondition0[throw_1])
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
                              BinHeapCondition36[temp1_3,
                                                tmp_3]
                            )
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
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            sibling_5=(sibling_4)++((tmp_3)->(temp1_3.sibling_4)))
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            sibling_4=sibling_5)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition38[temp1_3]
                          and 
                          (
                            (
                              BinHeapCondition0[throw_1]
                              and 
                              (
                                nullDerefBool_22=true)
                            )
                            or 
                            (
                              (
                                not (
                                  BinHeapCondition0[throw_1])
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
                              BinHeapCondition38[temp1_3])
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
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            sibling_6=(sibling_5)++((temp1_3)->(tmp_3)))
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            sibling_5=sibling_6)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition40[tmp_3]
                          and 
                          (
                            (
                              BinHeapCondition0[throw_1]
                              and 
                              (
                                nullDerefBool_23=true)
                            )
                            or 
                            (
                              (
                                not (
                                  BinHeapCondition0[throw_1])
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
                              BinHeapCondition40[tmp_3])
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
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            temp1_4=tmp_3.sibling_6)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            temp1_3=temp1_4)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition44[degree_0,
                                            sibling_4,
                                            temp1_3,
                                            temp2_3]
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition38[temp1_3]
                          and 
                          (
                            (
                              BinHeapCondition0[throw_1]
                              and 
                              (
                                nullDerefBool_23=true)
                            )
                            or 
                            (
                              (
                                not (
                                  BinHeapCondition0[throw_1])
                              )
                              and 
                              TruePred[]
                              and 
                              (
                                nullDerefBool_19=nullDerefBool_23)
                            )
                          )
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition38[temp1_3])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_19=nullDerefBool_23)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            temp1_4=temp1_3.sibling_4)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            temp1_3=temp1_4)
                        )
                      )
                      and 
                      (
                        tmp_2=tmp_3)
                      and 
                      (
                        temp2_3=temp2_4)
                      and 
                      (
                        sibling_4=sibling_6)
                    )
                  )
                  and 
                  (
                    head_2=head_3)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition48[degree_0,
                                        temp1_3,
                                        temp2_3]
                    )
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        tmp_3=temp1_3)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        tmp_2=tmp_3)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        temp1_4=temp2_3)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        temp1_3=temp1_4)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition34[temp2_3]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            nullDerefBool_19=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
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
                          BinHeapCondition34[temp2_3])
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
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        temp2_4=temp2_3.sibling_4)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        temp2_3=temp2_4)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition38[temp1_4]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            nullDerefBool_20=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
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
                          BinHeapCondition38[temp1_4])
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
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        sibling_6=(sibling_4)++((temp1_4)->(tmp_3)))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        sibling_4=sibling_6)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition2[thiz_0]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            nullDerefBool_21=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
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
                          BinHeapCondition2[thiz_0])
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
                      BinHeapCondition46[head_2,
                                        thiz_0,
                                        tmp_3]
                      and 
                      (
                        (
                          BinHeapCondition2[thiz_0]
                          and 
                          (
                            (
                              BinHeapCondition0[throw_1]
                              and 
                              (
                                nullDerefBool_23=true)
                            )
                            or 
                            (
                              (
                                not (
                                  BinHeapCondition0[throw_1])
                              )
                              and 
                              TruePred[]
                              and 
                              (
                                nullDerefBool_21=nullDerefBool_23)
                            )
                          )
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition2[thiz_0])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_21=nullDerefBool_23)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            head_3=(head_2)++((thiz_0)->(temp1_4)))
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            head_2=head_3)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition46[head_2,
                                            thiz_0,
                                            tmp_3]
                        )
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_21=nullDerefBool_23)
                      and 
                      (
                        head_2=head_3)
                    )
                  )
                )
              )
            )
          )
        )
        or 
        (
          TruePred[]
          and 
          (
            temp1_3=temp1_4)
          and 
          (
            temp2_3=temp2_4)
          and 
          (
            sibling_4=sibling_6)
          and 
          (
            nullDerefBool_16=nullDerefBool_23)
          and 
          (
            tmp_2=tmp_3)
          and 
          (
            head_2=head_3)
        )
      )
      and 
      (
        (
          BinHeapCondition52[temp1_4,
                            temp2_4]
          and 
          (
            (
              BinHeapCondition32[temp1_4,
                                temp2_4]
              and 
              (
                (
                  BinHeapCondition0[throw_1]
                  and 
                  (
                    nullDerefBool_24=true)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_1])
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
                  BinHeapCondition32[temp1_4,
                                    temp2_4]
                )
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
              BinHeapCondition50[degree_0,
                                temp1_4,
                                temp2_4]
              and 
              TruePred[]
              and 
              (
                (
                  BinHeapCondition0[throw_1]
                  and 
                  (
                    tmp_4=temp2_4)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    tmp_3=tmp_4)
                )
              )
              and 
              (
                (
                  BinHeapCondition34[temp2_4]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        nullDerefBool_25=true)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
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
                      BinHeapCondition34[temp2_4])
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
                  BinHeapCondition0[throw_1]
                  and 
                  (
                    temp2_5=temp2_4.sibling_6)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    temp2_4=temp2_5)
                )
              )
              and 
              (
                (
                  BinHeapCondition36[temp1_4,
                                    tmp_4]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        nullDerefBool_26=true)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
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
                      BinHeapCondition36[temp1_4,
                                        tmp_4]
                    )
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
                  BinHeapCondition0[throw_1]
                  and 
                  (
                    sibling_7=(sibling_6)++((tmp_4)->(temp1_4.sibling_6)))
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    sibling_6=sibling_7)
                )
              )
              and 
              (
                (
                  BinHeapCondition38[temp1_4]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        nullDerefBool_27=true)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
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
                      BinHeapCondition38[temp1_4])
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
                  BinHeapCondition0[throw_1]
                  and 
                  (
                    sibling_8=(sibling_7)++((temp1_4)->(tmp_4)))
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    sibling_7=sibling_8)
                )
              )
              and 
              (
                (
                  BinHeapCondition40[tmp_4]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        nullDerefBool_30=true)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_27=nullDerefBool_30)
                    )
                  )
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition40[tmp_4])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_27=nullDerefBool_30)
                )
              )
              and 
              (
                (
                  BinHeapCondition0[throw_1]
                  and 
                  (
                    temp1_5=tmp_4.sibling_8)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    temp1_4=temp1_5)
                )
              )
              and 
              (
                head_3=head_4)
            )
            or 
            (
              (
                not (
                  BinHeapCondition50[degree_0,
                                    temp1_4,
                                    temp2_4]
                )
              )
              and 
              (
                (
                  BinHeapCondition32[temp1_4,
                                    temp2_4]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        nullDerefBool_25=true)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
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
                      BinHeapCondition32[temp1_4,
                                        temp2_4]
                    )
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
                  BinHeapCondition48[degree_0,
                                    temp1_4,
                                    temp2_4]
                  and 
                  (
                    (
                      BinHeapCondition42[sibling_6,
                                        temp1_4,
                                        temp2_4]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            nullDerefBool_26=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
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
                          BinHeapCondition42[sibling_6,
                                            temp1_4,
                                            temp2_4]
                        )
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
                      BinHeapCondition44[degree_0,
                                        sibling_6,
                                        temp1_4,
                                        temp2_4]
                      and 
                      TruePred[]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            tmp_4=temp2_4)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            tmp_3=tmp_4)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition34[temp2_4]
                          and 
                          (
                            (
                              BinHeapCondition0[throw_1]
                              and 
                              (
                                nullDerefBool_27=true)
                            )
                            or 
                            (
                              (
                                not (
                                  BinHeapCondition0[throw_1])
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
                              BinHeapCondition34[temp2_4])
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
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            temp2_5=temp2_4.sibling_6)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            temp2_4=temp2_5)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition36[temp1_4,
                                            tmp_4]
                          and 
                          (
                            (
                              BinHeapCondition0[throw_1]
                              and 
                              (
                                nullDerefBool_28=true)
                            )
                            or 
                            (
                              (
                                not (
                                  BinHeapCondition0[throw_1])
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
                              BinHeapCondition36[temp1_4,
                                                tmp_4]
                            )
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
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            sibling_7=(sibling_6)++((tmp_4)->(temp1_4.sibling_6)))
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            sibling_6=sibling_7)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition38[temp1_4]
                          and 
                          (
                            (
                              BinHeapCondition0[throw_1]
                              and 
                              (
                                nullDerefBool_29=true)
                            )
                            or 
                            (
                              (
                                not (
                                  BinHeapCondition0[throw_1])
                              )
                              and 
                              TruePred[]
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
                              BinHeapCondition38[temp1_4])
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
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            sibling_8=(sibling_7)++((temp1_4)->(tmp_4)))
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            sibling_7=sibling_8)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition40[tmp_4]
                          and 
                          (
                            (
                              BinHeapCondition0[throw_1]
                              and 
                              (
                                nullDerefBool_30=true)
                            )
                            or 
                            (
                              (
                                not (
                                  BinHeapCondition0[throw_1])
                              )
                              and 
                              TruePred[]
                              and 
                              (
                                nullDerefBool_29=nullDerefBool_30)
                            )
                          )
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition40[tmp_4])
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
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            temp1_5=tmp_4.sibling_8)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            temp1_4=temp1_5)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition44[degree_0,
                                            sibling_6,
                                            temp1_4,
                                            temp2_4]
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition38[temp1_4]
                          and 
                          (
                            (
                              BinHeapCondition0[throw_1]
                              and 
                              (
                                nullDerefBool_30=true)
                            )
                            or 
                            (
                              (
                                not (
                                  BinHeapCondition0[throw_1])
                              )
                              and 
                              TruePred[]
                              and 
                              (
                                nullDerefBool_26=nullDerefBool_30)
                            )
                          )
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition38[temp1_4])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_26=nullDerefBool_30)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            temp1_5=temp1_4.sibling_6)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            temp1_4=temp1_5)
                        )
                      )
                      and 
                      (
                        tmp_3=tmp_4)
                      and 
                      (
                        temp2_4=temp2_5)
                      and 
                      (
                        sibling_6=sibling_8)
                    )
                  )
                  and 
                  (
                    head_3=head_4)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition48[degree_0,
                                        temp1_4,
                                        temp2_4]
                    )
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        tmp_4=temp1_4)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        tmp_3=tmp_4)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        temp1_5=temp2_4)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        temp1_4=temp1_5)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition34[temp2_4]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            nullDerefBool_26=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
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
                          BinHeapCondition34[temp2_4])
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
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        temp2_5=temp2_4.sibling_6)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        temp2_4=temp2_5)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition38[temp1_5]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            nullDerefBool_27=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
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
                          BinHeapCondition38[temp1_5])
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
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        sibling_8=(sibling_6)++((temp1_5)->(tmp_4)))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        sibling_6=sibling_8)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition2[thiz_0]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            nullDerefBool_28=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
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
                          BinHeapCondition2[thiz_0])
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
                      BinHeapCondition46[head_3,
                                        thiz_0,
                                        tmp_4]
                      and 
                      (
                        (
                          BinHeapCondition2[thiz_0]
                          and 
                          (
                            (
                              BinHeapCondition0[throw_1]
                              and 
                              (
                                nullDerefBool_30=true)
                            )
                            or 
                            (
                              (
                                not (
                                  BinHeapCondition0[throw_1])
                              )
                              and 
                              TruePred[]
                              and 
                              (
                                nullDerefBool_28=nullDerefBool_30)
                            )
                          )
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition2[thiz_0])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_28=nullDerefBool_30)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            head_4=(head_3)++((thiz_0)->(temp1_5)))
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            head_3=head_4)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition46[head_3,
                                            thiz_0,
                                            tmp_4]
                        )
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_28=nullDerefBool_30)
                      and 
                      (
                        head_3=head_4)
                    )
                  )
                )
              )
            )
          )
        )
        or 
        (
          TruePred[]
          and 
          (
            temp1_4=temp1_5)
          and 
          (
            temp2_4=temp2_5)
          and 
          (
            sibling_6=sibling_8)
          and 
          (
            nullDerefBool_23=nullDerefBool_30)
          and 
          (
            tmp_3=tmp_4)
          and 
          (
            head_3=head_4)
        )
      )
      and 
      (
        (
          BinHeapCondition52[temp1_5,
                            temp2_5]
          and 
          (
            (
              BinHeapCondition32[temp1_5,
                                temp2_5]
              and 
              (
                (
                  BinHeapCondition0[throw_1]
                  and 
                  (
                    nullDerefBool_31=true)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_30=nullDerefBool_31)
                )
              )
            )
            or 
            (
              (
                not (
                  BinHeapCondition32[temp1_5,
                                    temp2_5]
                )
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
              BinHeapCondition50[degree_0,
                                temp1_5,
                                temp2_5]
              and 
              TruePred[]
              and 
              (
                (
                  BinHeapCondition0[throw_1]
                  and 
                  (
                    tmp_5=temp2_5)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    tmp_4=tmp_5)
                )
              )
              and 
              (
                (
                  BinHeapCondition34[temp2_5]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        nullDerefBool_32=true)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
                      )
                      and 
                      TruePred[]
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
                      BinHeapCondition34[temp2_5])
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
                  BinHeapCondition0[throw_1]
                  and 
                  (
                    temp2_6=temp2_5.sibling_8)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    temp2_5=temp2_6)
                )
              )
              and 
              (
                (
                  BinHeapCondition36[temp1_5,
                                    tmp_5]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        nullDerefBool_33=true)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_32=nullDerefBool_33)
                    )
                  )
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition36[temp1_5,
                                        tmp_5]
                    )
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
                  BinHeapCondition0[throw_1]
                  and 
                  (
                    sibling_9=(sibling_8)++((tmp_5)->(temp1_5.sibling_8)))
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    sibling_8=sibling_9)
                )
              )
              and 
              (
                (
                  BinHeapCondition38[temp1_5]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        nullDerefBool_34=true)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_33=nullDerefBool_34)
                    )
                  )
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition38[temp1_5])
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
                (
                  BinHeapCondition0[throw_1]
                  and 
                  (
                    sibling_10=(sibling_9)++((temp1_5)->(tmp_5)))
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    sibling_9=sibling_10)
                )
              )
              and 
              (
                (
                  BinHeapCondition40[tmp_5]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        nullDerefBool_37=true)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_34=nullDerefBool_37)
                    )
                  )
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition40[tmp_5])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_34=nullDerefBool_37)
                )
              )
              and 
              (
                (
                  BinHeapCondition0[throw_1]
                  and 
                  (
                    temp1_6=tmp_5.sibling_10)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    temp1_5=temp1_6)
                )
              )
              and 
              (
                head_4=head_5)
            )
            or 
            (
              (
                not (
                  BinHeapCondition50[degree_0,
                                    temp1_5,
                                    temp2_5]
                )
              )
              and 
              (
                (
                  BinHeapCondition32[temp1_5,
                                    temp2_5]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        nullDerefBool_32=true)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
                      )
                      and 
                      TruePred[]
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
                      BinHeapCondition32[temp1_5,
                                        temp2_5]
                    )
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
                  BinHeapCondition48[degree_0,
                                    temp1_5,
                                    temp2_5]
                  and 
                  (
                    (
                      BinHeapCondition42[sibling_8,
                                        temp1_5,
                                        temp2_5]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            nullDerefBool_33=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_32=nullDerefBool_33)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition42[sibling_8,
                                            temp1_5,
                                            temp2_5]
                        )
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
                      BinHeapCondition44[degree_0,
                                        sibling_8,
                                        temp1_5,
                                        temp2_5]
                      and 
                      TruePred[]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            tmp_5=temp2_5)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            tmp_4=tmp_5)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition34[temp2_5]
                          and 
                          (
                            (
                              BinHeapCondition0[throw_1]
                              and 
                              (
                                nullDerefBool_34=true)
                            )
                            or 
                            (
                              (
                                not (
                                  BinHeapCondition0[throw_1])
                              )
                              and 
                              TruePred[]
                              and 
                              (
                                nullDerefBool_33=nullDerefBool_34)
                            )
                          )
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition34[temp2_5])
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
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            temp2_6=temp2_5.sibling_8)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            temp2_5=temp2_6)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition36[temp1_5,
                                            tmp_5]
                          and 
                          (
                            (
                              BinHeapCondition0[throw_1]
                              and 
                              (
                                nullDerefBool_35=true)
                            )
                            or 
                            (
                              (
                                not (
                                  BinHeapCondition0[throw_1])
                              )
                              and 
                              TruePred[]
                              and 
                              (
                                nullDerefBool_34=nullDerefBool_35)
                            )
                          )
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition36[temp1_5,
                                                tmp_5]
                            )
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_34=nullDerefBool_35)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            sibling_9=(sibling_8)++((tmp_5)->(temp1_5.sibling_8)))
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            sibling_8=sibling_9)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition38[temp1_5]
                          and 
                          (
                            (
                              BinHeapCondition0[throw_1]
                              and 
                              (
                                nullDerefBool_36=true)
                            )
                            or 
                            (
                              (
                                not (
                                  BinHeapCondition0[throw_1])
                              )
                              and 
                              TruePred[]
                              and 
                              (
                                nullDerefBool_35=nullDerefBool_36)
                            )
                          )
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition38[temp1_5])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_35=nullDerefBool_36)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            sibling_10=(sibling_9)++((temp1_5)->(tmp_5)))
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            sibling_9=sibling_10)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition40[tmp_5]
                          and 
                          (
                            (
                              BinHeapCondition0[throw_1]
                              and 
                              (
                                nullDerefBool_37=true)
                            )
                            or 
                            (
                              (
                                not (
                                  BinHeapCondition0[throw_1])
                              )
                              and 
                              TruePred[]
                              and 
                              (
                                nullDerefBool_36=nullDerefBool_37)
                            )
                          )
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition40[tmp_5])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_36=nullDerefBool_37)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            temp1_6=tmp_5.sibling_10)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            temp1_5=temp1_6)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition44[degree_0,
                                            sibling_8,
                                            temp1_5,
                                            temp2_5]
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition38[temp1_5]
                          and 
                          (
                            (
                              BinHeapCondition0[throw_1]
                              and 
                              (
                                nullDerefBool_37=true)
                            )
                            or 
                            (
                              (
                                not (
                                  BinHeapCondition0[throw_1])
                              )
                              and 
                              TruePred[]
                              and 
                              (
                                nullDerefBool_33=nullDerefBool_37)
                            )
                          )
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition38[temp1_5])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_33=nullDerefBool_37)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            temp1_6=temp1_5.sibling_8)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            temp1_5=temp1_6)
                        )
                      )
                      and 
                      (
                        tmp_4=tmp_5)
                      and 
                      (
                        temp2_5=temp2_6)
                      and 
                      (
                        sibling_8=sibling_10)
                    )
                  )
                  and 
                  (
                    head_4=head_5)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition48[degree_0,
                                        temp1_5,
                                        temp2_5]
                    )
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        tmp_5=temp1_5)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        tmp_4=tmp_5)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        temp1_6=temp2_5)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        temp1_5=temp1_6)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition34[temp2_5]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            nullDerefBool_33=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_32=nullDerefBool_33)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition34[temp2_5])
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
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        temp2_6=temp2_5.sibling_8)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        temp2_5=temp2_6)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition38[temp1_6]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            nullDerefBool_34=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_33=nullDerefBool_34)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition38[temp1_6])
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
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        sibling_10=(sibling_8)++((temp1_6)->(tmp_5)))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        sibling_8=sibling_10)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition2[thiz_0]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            nullDerefBool_35=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_34=nullDerefBool_35)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition2[thiz_0])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_34=nullDerefBool_35)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition46[head_4,
                                        thiz_0,
                                        tmp_5]
                      and 
                      (
                        (
                          BinHeapCondition2[thiz_0]
                          and 
                          (
                            (
                              BinHeapCondition0[throw_1]
                              and 
                              (
                                nullDerefBool_37=true)
                            )
                            or 
                            (
                              (
                                not (
                                  BinHeapCondition0[throw_1])
                              )
                              and 
                              TruePred[]
                              and 
                              (
                                nullDerefBool_35=nullDerefBool_37)
                            )
                          )
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition2[thiz_0])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_35=nullDerefBool_37)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            head_5=(head_4)++((thiz_0)->(temp1_6)))
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            head_4=head_5)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition46[head_4,
                                            thiz_0,
                                            tmp_5]
                        )
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_35=nullDerefBool_37)
                      and 
                      (
                        head_4=head_5)
                    )
                  )
                )
              )
            )
          )
        )
        or 
        (
          TruePred[]
          and 
          (
            temp1_5=temp1_6)
          and 
          (
            temp2_5=temp2_6)
          and 
          (
            sibling_8=sibling_10)
          and 
          (
            nullDerefBool_30=nullDerefBool_37)
          and 
          (
            tmp_4=tmp_5)
          and 
          (
            head_4=head_5)
        )
      )
      and 
      (
        (
          BinHeapCondition52[temp1_6,
                            temp2_6]
          and 
          (
            (
              BinHeapCondition32[temp1_6,
                                temp2_6]
              and 
              (
                (
                  BinHeapCondition0[throw_1]
                  and 
                  (
                    nullDerefBool_38=true)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_37=nullDerefBool_38)
                )
              )
            )
            or 
            (
              (
                not (
                  BinHeapCondition32[temp1_6,
                                    temp2_6]
                )
              )
              and 
              TruePred[]
              and 
              (
                nullDerefBool_37=nullDerefBool_38)
            )
          )
          and 
          (
            (
              BinHeapCondition50[degree_0,
                                temp1_6,
                                temp2_6]
              and 
              TruePred[]
              and 
              (
                (
                  BinHeapCondition0[throw_1]
                  and 
                  (
                    tmp_6=temp2_6)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    tmp_5=tmp_6)
                )
              )
              and 
              (
                (
                  BinHeapCondition34[temp2_6]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        nullDerefBool_39=true)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_38=nullDerefBool_39)
                    )
                  )
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition34[temp2_6])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_38=nullDerefBool_39)
                )
              )
              and 
              (
                (
                  BinHeapCondition0[throw_1]
                  and 
                  (
                    temp2_7=temp2_6.sibling_10)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    temp2_6=temp2_7)
                )
              )
              and 
              (
                (
                  BinHeapCondition36[temp1_6,
                                    tmp_6]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        nullDerefBool_40=true)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_39=nullDerefBool_40)
                    )
                  )
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition36[temp1_6,
                                        tmp_6]
                    )
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_39=nullDerefBool_40)
                )
              )
              and 
              (
                (
                  BinHeapCondition0[throw_1]
                  and 
                  (
                    sibling_11=(sibling_10)++((tmp_6)->(temp1_6.sibling_10)))
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    sibling_10=sibling_11)
                )
              )
              and 
              (
                (
                  BinHeapCondition38[temp1_6]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        nullDerefBool_41=true)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_40=nullDerefBool_41)
                    )
                  )
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition38[temp1_6])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_40=nullDerefBool_41)
                )
              )
              and 
              (
                (
                  BinHeapCondition0[throw_1]
                  and 
                  (
                    sibling_12=(sibling_11)++((temp1_6)->(tmp_6)))
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    sibling_11=sibling_12)
                )
              )
              and 
              (
                (
                  BinHeapCondition40[tmp_6]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        nullDerefBool_44=true)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_41=nullDerefBool_44)
                    )
                  )
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition40[tmp_6])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_41=nullDerefBool_44)
                )
              )
              and 
              (
                (
                  BinHeapCondition0[throw_1]
                  and 
                  (
                    temp1_7=tmp_6.sibling_12)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    temp1_6=temp1_7)
                )
              )
              and 
              (
                head_5=head_6)
            )
            or 
            (
              (
                not (
                  BinHeapCondition50[degree_0,
                                    temp1_6,
                                    temp2_6]
                )
              )
              and 
              (
                (
                  BinHeapCondition32[temp1_6,
                                    temp2_6]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        nullDerefBool_39=true)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_38=nullDerefBool_39)
                    )
                  )
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition32[temp1_6,
                                        temp2_6]
                    )
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_38=nullDerefBool_39)
                )
              )
              and 
              (
                (
                  BinHeapCondition48[degree_0,
                                    temp1_6,
                                    temp2_6]
                  and 
                  (
                    (
                      BinHeapCondition42[sibling_10,
                                        temp1_6,
                                        temp2_6]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            nullDerefBool_40=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_39=nullDerefBool_40)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition42[sibling_10,
                                            temp1_6,
                                            temp2_6]
                        )
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_39=nullDerefBool_40)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition44[degree_0,
                                        sibling_10,
                                        temp1_6,
                                        temp2_6]
                      and 
                      TruePred[]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            tmp_6=temp2_6)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            tmp_5=tmp_6)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition34[temp2_6]
                          and 
                          (
                            (
                              BinHeapCondition0[throw_1]
                              and 
                              (
                                nullDerefBool_41=true)
                            )
                            or 
                            (
                              (
                                not (
                                  BinHeapCondition0[throw_1])
                              )
                              and 
                              TruePred[]
                              and 
                              (
                                nullDerefBool_40=nullDerefBool_41)
                            )
                          )
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition34[temp2_6])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_40=nullDerefBool_41)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            temp2_7=temp2_6.sibling_10)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            temp2_6=temp2_7)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition36[temp1_6,
                                            tmp_6]
                          and 
                          (
                            (
                              BinHeapCondition0[throw_1]
                              and 
                              (
                                nullDerefBool_42=true)
                            )
                            or 
                            (
                              (
                                not (
                                  BinHeapCondition0[throw_1])
                              )
                              and 
                              TruePred[]
                              and 
                              (
                                nullDerefBool_41=nullDerefBool_42)
                            )
                          )
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition36[temp1_6,
                                                tmp_6]
                            )
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_41=nullDerefBool_42)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            sibling_11=(sibling_10)++((tmp_6)->(temp1_6.sibling_10)))
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            sibling_10=sibling_11)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition38[temp1_6]
                          and 
                          (
                            (
                              BinHeapCondition0[throw_1]
                              and 
                              (
                                nullDerefBool_43=true)
                            )
                            or 
                            (
                              (
                                not (
                                  BinHeapCondition0[throw_1])
                              )
                              and 
                              TruePred[]
                              and 
                              (
                                nullDerefBool_42=nullDerefBool_43)
                            )
                          )
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition38[temp1_6])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_42=nullDerefBool_43)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            sibling_12=(sibling_11)++((temp1_6)->(tmp_6)))
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            sibling_11=sibling_12)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition40[tmp_6]
                          and 
                          (
                            (
                              BinHeapCondition0[throw_1]
                              and 
                              (
                                nullDerefBool_44=true)
                            )
                            or 
                            (
                              (
                                not (
                                  BinHeapCondition0[throw_1])
                              )
                              and 
                              TruePred[]
                              and 
                              (
                                nullDerefBool_43=nullDerefBool_44)
                            )
                          )
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition40[tmp_6])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_43=nullDerefBool_44)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            temp1_7=tmp_6.sibling_12)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            temp1_6=temp1_7)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition44[degree_0,
                                            sibling_10,
                                            temp1_6,
                                            temp2_6]
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition38[temp1_6]
                          and 
                          (
                            (
                              BinHeapCondition0[throw_1]
                              and 
                              (
                                nullDerefBool_44=true)
                            )
                            or 
                            (
                              (
                                not (
                                  BinHeapCondition0[throw_1])
                              )
                              and 
                              TruePred[]
                              and 
                              (
                                nullDerefBool_40=nullDerefBool_44)
                            )
                          )
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition38[temp1_6])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_40=nullDerefBool_44)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            temp1_7=temp1_6.sibling_10)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            temp1_6=temp1_7)
                        )
                      )
                      and 
                      (
                        tmp_5=tmp_6)
                      and 
                      (
                        temp2_6=temp2_7)
                      and 
                      (
                        sibling_10=sibling_12)
                    )
                  )
                  and 
                  (
                    head_5=head_6)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition48[degree_0,
                                        temp1_6,
                                        temp2_6]
                    )
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        tmp_6=temp1_6)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        tmp_5=tmp_6)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        temp1_7=temp2_6)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        temp1_6=temp1_7)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition34[temp2_6]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            nullDerefBool_40=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_39=nullDerefBool_40)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition34[temp2_6])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_39=nullDerefBool_40)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        temp2_7=temp2_6.sibling_10)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        temp2_6=temp2_7)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition38[temp1_7]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            nullDerefBool_41=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_40=nullDerefBool_41)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition38[temp1_7])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_40=nullDerefBool_41)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        sibling_12=(sibling_10)++((temp1_7)->(tmp_6)))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        sibling_10=sibling_12)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition2[thiz_0]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            nullDerefBool_42=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_41=nullDerefBool_42)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition2[thiz_0])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_41=nullDerefBool_42)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition46[head_5,
                                        thiz_0,
                                        tmp_6]
                      and 
                      (
                        (
                          BinHeapCondition2[thiz_0]
                          and 
                          (
                            (
                              BinHeapCondition0[throw_1]
                              and 
                              (
                                nullDerefBool_44=true)
                            )
                            or 
                            (
                              (
                                not (
                                  BinHeapCondition0[throw_1])
                              )
                              and 
                              TruePred[]
                              and 
                              (
                                nullDerefBool_42=nullDerefBool_44)
                            )
                          )
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition2[thiz_0])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_42=nullDerefBool_44)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            head_6=(head_5)++((thiz_0)->(temp1_7)))
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            head_5=head_6)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition46[head_5,
                                            thiz_0,
                                            tmp_6]
                        )
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_42=nullDerefBool_44)
                      and 
                      (
                        head_5=head_6)
                    )
                  )
                )
              )
            )
          )
        )
        or 
        (
          TruePred[]
          and 
          (
            temp1_6=temp1_7)
          and 
          (
            temp2_6=temp2_7)
          and 
          (
            sibling_10=sibling_12)
          and 
          (
            nullDerefBool_37=nullDerefBool_44)
          and 
          (
            tmp_5=tmp_6)
          and 
          (
            head_5=head_6)
        )
      )
      and 
      (
        (
          BinHeapCondition52[temp1_7,
                            temp2_7]
          and 
          (
            (
              BinHeapCondition32[temp1_7,
                                temp2_7]
              and 
              (
                (
                  BinHeapCondition0[throw_1]
                  and 
                  (
                    nullDerefBool_45=true)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_44=nullDerefBool_45)
                )
              )
            )
            or 
            (
              (
                not (
                  BinHeapCondition32[temp1_7,
                                    temp2_7]
                )
              )
              and 
              TruePred[]
              and 
              (
                nullDerefBool_44=nullDerefBool_45)
            )
          )
          and 
          (
            (
              BinHeapCondition50[degree_0,
                                temp1_7,
                                temp2_7]
              and 
              TruePred[]
              and 
              (
                (
                  BinHeapCondition0[throw_1]
                  and 
                  (
                    tmp_7=temp2_7)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    tmp_6=tmp_7)
                )
              )
              and 
              (
                (
                  BinHeapCondition34[temp2_7]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        nullDerefBool_46=true)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_45=nullDerefBool_46)
                    )
                  )
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition34[temp2_7])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_45=nullDerefBool_46)
                )
              )
              and 
              (
                (
                  BinHeapCondition0[throw_1]
                  and 
                  (
                    temp2_8=temp2_7.sibling_12)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    temp2_7=temp2_8)
                )
              )
              and 
              (
                (
                  BinHeapCondition36[temp1_7,
                                    tmp_7]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        nullDerefBool_47=true)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_46=nullDerefBool_47)
                    )
                  )
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition36[temp1_7,
                                        tmp_7]
                    )
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_46=nullDerefBool_47)
                )
              )
              and 
              (
                (
                  BinHeapCondition0[throw_1]
                  and 
                  (
                    sibling_13=(sibling_12)++((tmp_7)->(temp1_7.sibling_12)))
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    sibling_12=sibling_13)
                )
              )
              and 
              (
                (
                  BinHeapCondition38[temp1_7]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        nullDerefBool_48=true)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_47=nullDerefBool_48)
                    )
                  )
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition38[temp1_7])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_47=nullDerefBool_48)
                )
              )
              and 
              (
                (
                  BinHeapCondition0[throw_1]
                  and 
                  (
                    sibling_14=(sibling_13)++((temp1_7)->(tmp_7)))
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    sibling_13=sibling_14)
                )
              )
              and 
              (
                (
                  BinHeapCondition40[tmp_7]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        nullDerefBool_51=true)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_48=nullDerefBool_51)
                    )
                  )
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition40[tmp_7])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_48=nullDerefBool_51)
                )
              )
              and 
              (
                (
                  BinHeapCondition0[throw_1]
                  and 
                  (
                    temp1_8=tmp_7.sibling_14)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    temp1_7=temp1_8)
                )
              )
              and 
              (
                head_6=head_7)
            )
            or 
            (
              (
                not (
                  BinHeapCondition50[degree_0,
                                    temp1_7,
                                    temp2_7]
                )
              )
              and 
              (
                (
                  BinHeapCondition32[temp1_7,
                                    temp2_7]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        nullDerefBool_46=true)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_45=nullDerefBool_46)
                    )
                  )
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition32[temp1_7,
                                        temp2_7]
                    )
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_45=nullDerefBool_46)
                )
              )
              and 
              (
                (
                  BinHeapCondition48[degree_0,
                                    temp1_7,
                                    temp2_7]
                  and 
                  (
                    (
                      BinHeapCondition42[sibling_12,
                                        temp1_7,
                                        temp2_7]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            nullDerefBool_47=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_46=nullDerefBool_47)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition42[sibling_12,
                                            temp1_7,
                                            temp2_7]
                        )
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_46=nullDerefBool_47)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition44[degree_0,
                                        sibling_12,
                                        temp1_7,
                                        temp2_7]
                      and 
                      TruePred[]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            tmp_7=temp2_7)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            tmp_6=tmp_7)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition34[temp2_7]
                          and 
                          (
                            (
                              BinHeapCondition0[throw_1]
                              and 
                              (
                                nullDerefBool_48=true)
                            )
                            or 
                            (
                              (
                                not (
                                  BinHeapCondition0[throw_1])
                              )
                              and 
                              TruePred[]
                              and 
                              (
                                nullDerefBool_47=nullDerefBool_48)
                            )
                          )
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition34[temp2_7])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_47=nullDerefBool_48)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            temp2_8=temp2_7.sibling_12)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            temp2_7=temp2_8)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition36[temp1_7,
                                            tmp_7]
                          and 
                          (
                            (
                              BinHeapCondition0[throw_1]
                              and 
                              (
                                nullDerefBool_49=true)
                            )
                            or 
                            (
                              (
                                not (
                                  BinHeapCondition0[throw_1])
                              )
                              and 
                              TruePred[]
                              and 
                              (
                                nullDerefBool_48=nullDerefBool_49)
                            )
                          )
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition36[temp1_7,
                                                tmp_7]
                            )
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_48=nullDerefBool_49)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            sibling_13=(sibling_12)++((tmp_7)->(temp1_7.sibling_12)))
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            sibling_12=sibling_13)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition38[temp1_7]
                          and 
                          (
                            (
                              BinHeapCondition0[throw_1]
                              and 
                              (
                                nullDerefBool_50=true)
                            )
                            or 
                            (
                              (
                                not (
                                  BinHeapCondition0[throw_1])
                              )
                              and 
                              TruePred[]
                              and 
                              (
                                nullDerefBool_49=nullDerefBool_50)
                            )
                          )
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition38[temp1_7])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_49=nullDerefBool_50)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            sibling_14=(sibling_13)++((temp1_7)->(tmp_7)))
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            sibling_13=sibling_14)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition40[tmp_7]
                          and 
                          (
                            (
                              BinHeapCondition0[throw_1]
                              and 
                              (
                                nullDerefBool_51=true)
                            )
                            or 
                            (
                              (
                                not (
                                  BinHeapCondition0[throw_1])
                              )
                              and 
                              TruePred[]
                              and 
                              (
                                nullDerefBool_50=nullDerefBool_51)
                            )
                          )
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition40[tmp_7])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_50=nullDerefBool_51)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            temp1_8=tmp_7.sibling_14)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            temp1_7=temp1_8)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition44[degree_0,
                                            sibling_12,
                                            temp1_7,
                                            temp2_7]
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition38[temp1_7]
                          and 
                          (
                            (
                              BinHeapCondition0[throw_1]
                              and 
                              (
                                nullDerefBool_51=true)
                            )
                            or 
                            (
                              (
                                not (
                                  BinHeapCondition0[throw_1])
                              )
                              and 
                              TruePred[]
                              and 
                              (
                                nullDerefBool_47=nullDerefBool_51)
                            )
                          )
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition38[temp1_7])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_47=nullDerefBool_51)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            temp1_8=temp1_7.sibling_12)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            temp1_7=temp1_8)
                        )
                      )
                      and 
                      (
                        tmp_6=tmp_7)
                      and 
                      (
                        temp2_7=temp2_8)
                      and 
                      (
                        sibling_12=sibling_14)
                    )
                  )
                  and 
                  (
                    head_6=head_7)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition48[degree_0,
                                        temp1_7,
                                        temp2_7]
                    )
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        tmp_7=temp1_7)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        tmp_6=tmp_7)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        temp1_8=temp2_7)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        temp1_7=temp1_8)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition34[temp2_7]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            nullDerefBool_47=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_46=nullDerefBool_47)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition34[temp2_7])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_46=nullDerefBool_47)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        temp2_8=temp2_7.sibling_12)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        temp2_7=temp2_8)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition38[temp1_8]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            nullDerefBool_48=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_47=nullDerefBool_48)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition38[temp1_8])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_47=nullDerefBool_48)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        sibling_14=(sibling_12)++((temp1_8)->(tmp_7)))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        sibling_12=sibling_14)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition2[thiz_0]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            nullDerefBool_49=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_48=nullDerefBool_49)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition2[thiz_0])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_48=nullDerefBool_49)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition46[head_6,
                                        thiz_0,
                                        tmp_7]
                      and 
                      (
                        (
                          BinHeapCondition2[thiz_0]
                          and 
                          (
                            (
                              BinHeapCondition0[throw_1]
                              and 
                              (
                                nullDerefBool_51=true)
                            )
                            or 
                            (
                              (
                                not (
                                  BinHeapCondition0[throw_1])
                              )
                              and 
                              TruePred[]
                              and 
                              (
                                nullDerefBool_49=nullDerefBool_51)
                            )
                          )
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition2[thiz_0])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_49=nullDerefBool_51)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            head_7=(head_6)++((thiz_0)->(temp1_8)))
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            head_6=head_7)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition46[head_6,
                                            thiz_0,
                                            tmp_7]
                        )
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_49=nullDerefBool_51)
                      and 
                      (
                        head_6=head_7)
                    )
                  )
                )
              )
            )
          )
        )
        or 
        (
          TruePred[]
          and 
          (
            temp1_7=temp1_8)
          and 
          (
            temp2_7=temp2_8)
          and 
          (
            sibling_12=sibling_14)
          and 
          (
            nullDerefBool_44=nullDerefBool_51)
          and 
          (
            tmp_6=tmp_7)
          and 
          (
            head_6=head_7)
        )
      )
      and 
      (
        (
          BinHeapCondition52[temp1_8,
                            temp2_8]
          and 
          (
            (
              BinHeapCondition32[temp1_8,
                                temp2_8]
              and 
              (
                (
                  BinHeapCondition0[throw_1]
                  and 
                  (
                    nullDerefBool_52=true)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_51=nullDerefBool_52)
                )
              )
            )
            or 
            (
              (
                not (
                  BinHeapCondition32[temp1_8,
                                    temp2_8]
                )
              )
              and 
              TruePred[]
              and 
              (
                nullDerefBool_51=nullDerefBool_52)
            )
          )
          and 
          (
            (
              BinHeapCondition50[degree_0,
                                temp1_8,
                                temp2_8]
              and 
              TruePred[]
              and 
              (
                (
                  BinHeapCondition0[throw_1]
                  and 
                  (
                    tmp_8=temp2_8)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    tmp_7=tmp_8)
                )
              )
              and 
              (
                (
                  BinHeapCondition34[temp2_8]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        nullDerefBool_53=true)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_52=nullDerefBool_53)
                    )
                  )
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition34[temp2_8])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_52=nullDerefBool_53)
                )
              )
              and 
              (
                (
                  BinHeapCondition0[throw_1]
                  and 
                  (
                    temp2_9=temp2_8.sibling_14)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    temp2_8=temp2_9)
                )
              )
              and 
              (
                (
                  BinHeapCondition36[temp1_8,
                                    tmp_8]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        nullDerefBool_54=true)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_53=nullDerefBool_54)
                    )
                  )
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition36[temp1_8,
                                        tmp_8]
                    )
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_53=nullDerefBool_54)
                )
              )
              and 
              (
                (
                  BinHeapCondition0[throw_1]
                  and 
                  (
                    sibling_15=(sibling_14)++((tmp_8)->(temp1_8.sibling_14)))
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    sibling_14=sibling_15)
                )
              )
              and 
              (
                (
                  BinHeapCondition38[temp1_8]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        nullDerefBool_55=true)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_54=nullDerefBool_55)
                    )
                  )
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition38[temp1_8])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_54=nullDerefBool_55)
                )
              )
              and 
              (
                (
                  BinHeapCondition0[throw_1]
                  and 
                  (
                    sibling_16=(sibling_15)++((temp1_8)->(tmp_8)))
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    sibling_15=sibling_16)
                )
              )
              and 
              (
                (
                  BinHeapCondition40[tmp_8]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        nullDerefBool_58=true)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_55=nullDerefBool_58)
                    )
                  )
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition40[tmp_8])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_55=nullDerefBool_58)
                )
              )
              and 
              (
                (
                  BinHeapCondition0[throw_1]
                  and 
                  (
                    temp1_9=tmp_8.sibling_16)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    temp1_8=temp1_9)
                )
              )
              and 
              (
                head_7=head_8)
            )
            or 
            (
              (
                not (
                  BinHeapCondition50[degree_0,
                                    temp1_8,
                                    temp2_8]
                )
              )
              and 
              (
                (
                  BinHeapCondition32[temp1_8,
                                    temp2_8]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        nullDerefBool_53=true)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_52=nullDerefBool_53)
                    )
                  )
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition32[temp1_8,
                                        temp2_8]
                    )
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_52=nullDerefBool_53)
                )
              )
              and 
              (
                (
                  BinHeapCondition48[degree_0,
                                    temp1_8,
                                    temp2_8]
                  and 
                  (
                    (
                      BinHeapCondition42[sibling_14,
                                        temp1_8,
                                        temp2_8]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            nullDerefBool_54=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_53=nullDerefBool_54)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition42[sibling_14,
                                            temp1_8,
                                            temp2_8]
                        )
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_53=nullDerefBool_54)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition44[degree_0,
                                        sibling_14,
                                        temp1_8,
                                        temp2_8]
                      and 
                      TruePred[]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            tmp_8=temp2_8)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            tmp_7=tmp_8)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition34[temp2_8]
                          and 
                          (
                            (
                              BinHeapCondition0[throw_1]
                              and 
                              (
                                nullDerefBool_55=true)
                            )
                            or 
                            (
                              (
                                not (
                                  BinHeapCondition0[throw_1])
                              )
                              and 
                              TruePred[]
                              and 
                              (
                                nullDerefBool_54=nullDerefBool_55)
                            )
                          )
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition34[temp2_8])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_54=nullDerefBool_55)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            temp2_9=temp2_8.sibling_14)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            temp2_8=temp2_9)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition36[temp1_8,
                                            tmp_8]
                          and 
                          (
                            (
                              BinHeapCondition0[throw_1]
                              and 
                              (
                                nullDerefBool_56=true)
                            )
                            or 
                            (
                              (
                                not (
                                  BinHeapCondition0[throw_1])
                              )
                              and 
                              TruePred[]
                              and 
                              (
                                nullDerefBool_55=nullDerefBool_56)
                            )
                          )
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition36[temp1_8,
                                                tmp_8]
                            )
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_55=nullDerefBool_56)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            sibling_15=(sibling_14)++((tmp_8)->(temp1_8.sibling_14)))
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            sibling_14=sibling_15)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition38[temp1_8]
                          and 
                          (
                            (
                              BinHeapCondition0[throw_1]
                              and 
                              (
                                nullDerefBool_57=true)
                            )
                            or 
                            (
                              (
                                not (
                                  BinHeapCondition0[throw_1])
                              )
                              and 
                              TruePred[]
                              and 
                              (
                                nullDerefBool_56=nullDerefBool_57)
                            )
                          )
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition38[temp1_8])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_56=nullDerefBool_57)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            sibling_16=(sibling_15)++((temp1_8)->(tmp_8)))
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            sibling_15=sibling_16)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition40[tmp_8]
                          and 
                          (
                            (
                              BinHeapCondition0[throw_1]
                              and 
                              (
                                nullDerefBool_58=true)
                            )
                            or 
                            (
                              (
                                not (
                                  BinHeapCondition0[throw_1])
                              )
                              and 
                              TruePred[]
                              and 
                              (
                                nullDerefBool_57=nullDerefBool_58)
                            )
                          )
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition40[tmp_8])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_57=nullDerefBool_58)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            temp1_9=tmp_8.sibling_16)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            temp1_8=temp1_9)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition44[degree_0,
                                            sibling_14,
                                            temp1_8,
                                            temp2_8]
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition38[temp1_8]
                          and 
                          (
                            (
                              BinHeapCondition0[throw_1]
                              and 
                              (
                                nullDerefBool_58=true)
                            )
                            or 
                            (
                              (
                                not (
                                  BinHeapCondition0[throw_1])
                              )
                              and 
                              TruePred[]
                              and 
                              (
                                nullDerefBool_54=nullDerefBool_58)
                            )
                          )
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition38[temp1_8])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_54=nullDerefBool_58)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            temp1_9=temp1_8.sibling_14)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            temp1_8=temp1_9)
                        )
                      )
                      and 
                      (
                        tmp_7=tmp_8)
                      and 
                      (
                        temp2_8=temp2_9)
                      and 
                      (
                        sibling_14=sibling_16)
                    )
                  )
                  and 
                  (
                    head_7=head_8)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition48[degree_0,
                                        temp1_8,
                                        temp2_8]
                    )
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        tmp_8=temp1_8)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        tmp_7=tmp_8)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        temp1_9=temp2_8)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        temp1_8=temp1_9)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition34[temp2_8]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            nullDerefBool_54=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_53=nullDerefBool_54)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition34[temp2_8])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_53=nullDerefBool_54)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        temp2_9=temp2_8.sibling_14)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        temp2_8=temp2_9)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition38[temp1_9]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            nullDerefBool_55=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_54=nullDerefBool_55)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition38[temp1_9])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_54=nullDerefBool_55)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        sibling_16=(sibling_14)++((temp1_9)->(tmp_8)))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        sibling_14=sibling_16)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition2[thiz_0]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            nullDerefBool_56=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_55=nullDerefBool_56)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition2[thiz_0])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_55=nullDerefBool_56)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition46[head_7,
                                        thiz_0,
                                        tmp_8]
                      and 
                      (
                        (
                          BinHeapCondition2[thiz_0]
                          and 
                          (
                            (
                              BinHeapCondition0[throw_1]
                              and 
                              (
                                nullDerefBool_58=true)
                            )
                            or 
                            (
                              (
                                not (
                                  BinHeapCondition0[throw_1])
                              )
                              and 
                              TruePred[]
                              and 
                              (
                                nullDerefBool_56=nullDerefBool_58)
                            )
                          )
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition2[thiz_0])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_56=nullDerefBool_58)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            head_8=(head_7)++((thiz_0)->(temp1_9)))
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            head_7=head_8)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition46[head_7,
                                            thiz_0,
                                            tmp_8]
                        )
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_56=nullDerefBool_58)
                      and 
                      (
                        head_7=head_8)
                    )
                  )
                )
              )
            )
          )
        )
        or 
        (
          TruePred[]
          and 
          (
            temp1_8=temp1_9)
          and 
          (
            temp2_8=temp2_9)
          and 
          (
            sibling_14=sibling_16)
          and 
          (
            nullDerefBool_51=nullDerefBool_58)
          and 
          (
            tmp_7=tmp_8)
          and 
          (
            head_7=head_8)
        )
      )
      and 
      (
        (
          BinHeapCondition52[temp1_9,
                            temp2_9]
          and 
          (
            (
              BinHeapCondition32[temp1_9,
                                temp2_9]
              and 
              (
                (
                  BinHeapCondition0[throw_1]
                  and 
                  (
                    nullDerefBool_59=true)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_58=nullDerefBool_59)
                )
              )
            )
            or 
            (
              (
                not (
                  BinHeapCondition32[temp1_9,
                                    temp2_9]
                )
              )
              and 
              TruePred[]
              and 
              (
                nullDerefBool_58=nullDerefBool_59)
            )
          )
          and 
          (
            (
              BinHeapCondition50[degree_0,
                                temp1_9,
                                temp2_9]
              and 
              TruePred[]
              and 
              (
                (
                  BinHeapCondition0[throw_1]
                  and 
                  (
                    tmp_9=temp2_9)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    tmp_8=tmp_9)
                )
              )
              and 
              (
                (
                  BinHeapCondition34[temp2_9]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        nullDerefBool_60=true)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_59=nullDerefBool_60)
                    )
                  )
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition34[temp2_9])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_59=nullDerefBool_60)
                )
              )
              and 
              (
                (
                  BinHeapCondition0[throw_1]
                  and 
                  (
                    temp2_10=temp2_9.sibling_16)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    temp2_9=temp2_10)
                )
              )
              and 
              (
                (
                  BinHeapCondition36[temp1_9,
                                    tmp_9]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        nullDerefBool_61=true)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_60=nullDerefBool_61)
                    )
                  )
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition36[temp1_9,
                                        tmp_9]
                    )
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_60=nullDerefBool_61)
                )
              )
              and 
              (
                (
                  BinHeapCondition0[throw_1]
                  and 
                  (
                    sibling_17=(sibling_16)++((tmp_9)->(temp1_9.sibling_16)))
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    sibling_16=sibling_17)
                )
              )
              and 
              (
                (
                  BinHeapCondition38[temp1_9]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        nullDerefBool_62=true)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_61=nullDerefBool_62)
                    )
                  )
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition38[temp1_9])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_61=nullDerefBool_62)
                )
              )
              and 
              (
                (
                  BinHeapCondition0[throw_1]
                  and 
                  (
                    sibling_18=(sibling_17)++((temp1_9)->(tmp_9)))
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    sibling_17=sibling_18)
                )
              )
              and 
              (
                (
                  BinHeapCondition40[tmp_9]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        nullDerefBool_65=true)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_62=nullDerefBool_65)
                    )
                  )
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition40[tmp_9])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_62=nullDerefBool_65)
                )
              )
              and 
              (
                (
                  BinHeapCondition0[throw_1]
                  and 
                  (
                    temp1_10=tmp_9.sibling_18)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    temp1_9=temp1_10)
                )
              )
              and 
              (
                head_8=head_9)
            )
            or 
            (
              (
                not (
                  BinHeapCondition50[degree_0,
                                    temp1_9,
                                    temp2_9]
                )
              )
              and 
              (
                (
                  BinHeapCondition32[temp1_9,
                                    temp2_9]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        nullDerefBool_60=true)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_59=nullDerefBool_60)
                    )
                  )
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition32[temp1_9,
                                        temp2_9]
                    )
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_59=nullDerefBool_60)
                )
              )
              and 
              (
                (
                  BinHeapCondition48[degree_0,
                                    temp1_9,
                                    temp2_9]
                  and 
                  (
                    (
                      BinHeapCondition42[sibling_16,
                                        temp1_9,
                                        temp2_9]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            nullDerefBool_61=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_60=nullDerefBool_61)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition42[sibling_16,
                                            temp1_9,
                                            temp2_9]
                        )
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_60=nullDerefBool_61)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition44[degree_0,
                                        sibling_16,
                                        temp1_9,
                                        temp2_9]
                      and 
                      TruePred[]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            tmp_9=temp2_9)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            tmp_8=tmp_9)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition34[temp2_9]
                          and 
                          (
                            (
                              BinHeapCondition0[throw_1]
                              and 
                              (
                                nullDerefBool_62=true)
                            )
                            or 
                            (
                              (
                                not (
                                  BinHeapCondition0[throw_1])
                              )
                              and 
                              TruePred[]
                              and 
                              (
                                nullDerefBool_61=nullDerefBool_62)
                            )
                          )
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition34[temp2_9])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_61=nullDerefBool_62)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            temp2_10=temp2_9.sibling_16)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            temp2_9=temp2_10)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition36[temp1_9,
                                            tmp_9]
                          and 
                          (
                            (
                              BinHeapCondition0[throw_1]
                              and 
                              (
                                nullDerefBool_63=true)
                            )
                            or 
                            (
                              (
                                not (
                                  BinHeapCondition0[throw_1])
                              )
                              and 
                              TruePred[]
                              and 
                              (
                                nullDerefBool_62=nullDerefBool_63)
                            )
                          )
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition36[temp1_9,
                                                tmp_9]
                            )
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_62=nullDerefBool_63)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            sibling_17=(sibling_16)++((tmp_9)->(temp1_9.sibling_16)))
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            sibling_16=sibling_17)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition38[temp1_9]
                          and 
                          (
                            (
                              BinHeapCondition0[throw_1]
                              and 
                              (
                                nullDerefBool_64=true)
                            )
                            or 
                            (
                              (
                                not (
                                  BinHeapCondition0[throw_1])
                              )
                              and 
                              TruePred[]
                              and 
                              (
                                nullDerefBool_63=nullDerefBool_64)
                            )
                          )
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition38[temp1_9])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_63=nullDerefBool_64)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            sibling_18=(sibling_17)++((temp1_9)->(tmp_9)))
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            sibling_17=sibling_18)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition40[tmp_9]
                          and 
                          (
                            (
                              BinHeapCondition0[throw_1]
                              and 
                              (
                                nullDerefBool_65=true)
                            )
                            or 
                            (
                              (
                                not (
                                  BinHeapCondition0[throw_1])
                              )
                              and 
                              TruePred[]
                              and 
                              (
                                nullDerefBool_64=nullDerefBool_65)
                            )
                          )
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition40[tmp_9])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_64=nullDerefBool_65)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            temp1_10=tmp_9.sibling_18)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            temp1_9=temp1_10)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition44[degree_0,
                                            sibling_16,
                                            temp1_9,
                                            temp2_9]
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition38[temp1_9]
                          and 
                          (
                            (
                              BinHeapCondition0[throw_1]
                              and 
                              (
                                nullDerefBool_65=true)
                            )
                            or 
                            (
                              (
                                not (
                                  BinHeapCondition0[throw_1])
                              )
                              and 
                              TruePred[]
                              and 
                              (
                                nullDerefBool_61=nullDerefBool_65)
                            )
                          )
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition38[temp1_9])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_61=nullDerefBool_65)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            temp1_10=temp1_9.sibling_16)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            temp1_9=temp1_10)
                        )
                      )
                      and 
                      (
                        tmp_8=tmp_9)
                      and 
                      (
                        temp2_9=temp2_10)
                      and 
                      (
                        sibling_16=sibling_18)
                    )
                  )
                  and 
                  (
                    head_8=head_9)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition48[degree_0,
                                        temp1_9,
                                        temp2_9]
                    )
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        tmp_9=temp1_9)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        tmp_8=tmp_9)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        temp1_10=temp2_9)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        temp1_9=temp1_10)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition34[temp2_9]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            nullDerefBool_61=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_60=nullDerefBool_61)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition34[temp2_9])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_60=nullDerefBool_61)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        temp2_10=temp2_9.sibling_16)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        temp2_9=temp2_10)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition38[temp1_10]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            nullDerefBool_62=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_61=nullDerefBool_62)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition38[temp1_10])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_61=nullDerefBool_62)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        sibling_18=(sibling_16)++((temp1_10)->(tmp_9)))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        sibling_16=sibling_18)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition2[thiz_0]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            nullDerefBool_63=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_62=nullDerefBool_63)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition2[thiz_0])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_62=nullDerefBool_63)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition46[head_8,
                                        thiz_0,
                                        tmp_9]
                      and 
                      (
                        (
                          BinHeapCondition2[thiz_0]
                          and 
                          (
                            (
                              BinHeapCondition0[throw_1]
                              and 
                              (
                                nullDerefBool_65=true)
                            )
                            or 
                            (
                              (
                                not (
                                  BinHeapCondition0[throw_1])
                              )
                              and 
                              TruePred[]
                              and 
                              (
                                nullDerefBool_63=nullDerefBool_65)
                            )
                          )
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition2[thiz_0])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_63=nullDerefBool_65)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            head_9=(head_8)++((thiz_0)->(temp1_10)))
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            head_8=head_9)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition46[head_8,
                                            thiz_0,
                                            tmp_9]
                        )
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_63=nullDerefBool_65)
                      and 
                      (
                        head_8=head_9)
                    )
                  )
                )
              )
            )
          )
        )
        or 
        (
          TruePred[]
          and 
          (
            temp1_9=temp1_10)
          and 
          (
            temp2_9=temp2_10)
          and 
          (
            sibling_16=sibling_18)
          and 
          (
            nullDerefBool_58=nullDerefBool_65)
          and 
          (
            tmp_8=tmp_9)
          and 
          (
            head_8=head_9)
        )
      )
      and 
      (
        (
          BinHeapCondition52[temp1_10,
                            temp2_10]
          and 
          (
            (
              BinHeapCondition32[temp1_10,
                                temp2_10]
              and 
              (
                (
                  BinHeapCondition0[throw_1]
                  and 
                  (
                    nullDerefBool_66=true)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_65=nullDerefBool_66)
                )
              )
            )
            or 
            (
              (
                not (
                  BinHeapCondition32[temp1_10,
                                    temp2_10]
                )
              )
              and 
              TruePred[]
              and 
              (
                nullDerefBool_65=nullDerefBool_66)
            )
          )
          and 
          (
            (
              BinHeapCondition50[degree_0,
                                temp1_10,
                                temp2_10]
              and 
              TruePred[]
              and 
              (
                (
                  BinHeapCondition0[throw_1]
                  and 
                  (
                    tmp_10=temp2_10)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    tmp_9=tmp_10)
                )
              )
              and 
              (
                (
                  BinHeapCondition34[temp2_10]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        nullDerefBool_67=true)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_66=nullDerefBool_67)
                    )
                  )
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition34[temp2_10])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_66=nullDerefBool_67)
                )
              )
              and 
              (
                (
                  BinHeapCondition0[throw_1]
                  and 
                  (
                    temp2_11=temp2_10.sibling_18)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    temp2_10=temp2_11)
                )
              )
              and 
              (
                (
                  BinHeapCondition36[temp1_10,
                                    tmp_10]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        nullDerefBool_68=true)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_67=nullDerefBool_68)
                    )
                  )
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition36[temp1_10,
                                        tmp_10]
                    )
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_67=nullDerefBool_68)
                )
              )
              and 
              (
                (
                  BinHeapCondition0[throw_1]
                  and 
                  (
                    sibling_19=(sibling_18)++((tmp_10)->(temp1_10.sibling_18)))
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    sibling_18=sibling_19)
                )
              )
              and 
              (
                (
                  BinHeapCondition38[temp1_10]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        nullDerefBool_69=true)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_68=nullDerefBool_69)
                    )
                  )
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition38[temp1_10])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_68=nullDerefBool_69)
                )
              )
              and 
              (
                (
                  BinHeapCondition0[throw_1]
                  and 
                  (
                    sibling_20=(sibling_19)++((temp1_10)->(tmp_10)))
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    sibling_19=sibling_20)
                )
              )
              and 
              (
                (
                  BinHeapCondition40[tmp_10]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        nullDerefBool_72=true)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_69=nullDerefBool_72)
                    )
                  )
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition40[tmp_10])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_69=nullDerefBool_72)
                )
              )
              and 
              (
                (
                  BinHeapCondition0[throw_1]
                  and 
                  (
                    temp1_11=tmp_10.sibling_20)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    temp1_10=temp1_11)
                )
              )
              and 
              (
                head_9=head_10)
            )
            or 
            (
              (
                not (
                  BinHeapCondition50[degree_0,
                                    temp1_10,
                                    temp2_10]
                )
              )
              and 
              (
                (
                  BinHeapCondition32[temp1_10,
                                    temp2_10]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        nullDerefBool_67=true)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_66=nullDerefBool_67)
                    )
                  )
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition32[temp1_10,
                                        temp2_10]
                    )
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_66=nullDerefBool_67)
                )
              )
              and 
              (
                (
                  BinHeapCondition48[degree_0,
                                    temp1_10,
                                    temp2_10]
                  and 
                  (
                    (
                      BinHeapCondition42[sibling_18,
                                        temp1_10,
                                        temp2_10]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            nullDerefBool_68=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_67=nullDerefBool_68)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition42[sibling_18,
                                            temp1_10,
                                            temp2_10]
                        )
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_67=nullDerefBool_68)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition44[degree_0,
                                        sibling_18,
                                        temp1_10,
                                        temp2_10]
                      and 
                      TruePred[]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            tmp_10=temp2_10)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            tmp_9=tmp_10)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition34[temp2_10]
                          and 
                          (
                            (
                              BinHeapCondition0[throw_1]
                              and 
                              (
                                nullDerefBool_69=true)
                            )
                            or 
                            (
                              (
                                not (
                                  BinHeapCondition0[throw_1])
                              )
                              and 
                              TruePred[]
                              and 
                              (
                                nullDerefBool_68=nullDerefBool_69)
                            )
                          )
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition34[temp2_10])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_68=nullDerefBool_69)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            temp2_11=temp2_10.sibling_18)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            temp2_10=temp2_11)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition36[temp1_10,
                                            tmp_10]
                          and 
                          (
                            (
                              BinHeapCondition0[throw_1]
                              and 
                              (
                                nullDerefBool_70=true)
                            )
                            or 
                            (
                              (
                                not (
                                  BinHeapCondition0[throw_1])
                              )
                              and 
                              TruePred[]
                              and 
                              (
                                nullDerefBool_69=nullDerefBool_70)
                            )
                          )
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition36[temp1_10,
                                                tmp_10]
                            )
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_69=nullDerefBool_70)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            sibling_19=(sibling_18)++((tmp_10)->(temp1_10.sibling_18)))
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            sibling_18=sibling_19)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition38[temp1_10]
                          and 
                          (
                            (
                              BinHeapCondition0[throw_1]
                              and 
                              (
                                nullDerefBool_71=true)
                            )
                            or 
                            (
                              (
                                not (
                                  BinHeapCondition0[throw_1])
                              )
                              and 
                              TruePred[]
                              and 
                              (
                                nullDerefBool_70=nullDerefBool_71)
                            )
                          )
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition38[temp1_10])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_70=nullDerefBool_71)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            sibling_20=(sibling_19)++((temp1_10)->(tmp_10)))
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            sibling_19=sibling_20)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition40[tmp_10]
                          and 
                          (
                            (
                              BinHeapCondition0[throw_1]
                              and 
                              (
                                nullDerefBool_72=true)
                            )
                            or 
                            (
                              (
                                not (
                                  BinHeapCondition0[throw_1])
                              )
                              and 
                              TruePred[]
                              and 
                              (
                                nullDerefBool_71=nullDerefBool_72)
                            )
                          )
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition40[tmp_10])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_71=nullDerefBool_72)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            temp1_11=tmp_10.sibling_20)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            temp1_10=temp1_11)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition44[degree_0,
                                            sibling_18,
                                            temp1_10,
                                            temp2_10]
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition38[temp1_10]
                          and 
                          (
                            (
                              BinHeapCondition0[throw_1]
                              and 
                              (
                                nullDerefBool_72=true)
                            )
                            or 
                            (
                              (
                                not (
                                  BinHeapCondition0[throw_1])
                              )
                              and 
                              TruePred[]
                              and 
                              (
                                nullDerefBool_68=nullDerefBool_72)
                            )
                          )
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition38[temp1_10])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_68=nullDerefBool_72)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            temp1_11=temp1_10.sibling_18)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            temp1_10=temp1_11)
                        )
                      )
                      and 
                      (
                        tmp_9=tmp_10)
                      and 
                      (
                        temp2_10=temp2_11)
                      and 
                      (
                        sibling_18=sibling_20)
                    )
                  )
                  and 
                  (
                    head_9=head_10)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition48[degree_0,
                                        temp1_10,
                                        temp2_10]
                    )
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        tmp_10=temp1_10)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        tmp_9=tmp_10)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        temp1_11=temp2_10)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        temp1_10=temp1_11)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition34[temp2_10]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            nullDerefBool_68=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_67=nullDerefBool_68)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition34[temp2_10])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_67=nullDerefBool_68)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        temp2_11=temp2_10.sibling_18)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        temp2_10=temp2_11)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition38[temp1_11]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            nullDerefBool_69=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_68=nullDerefBool_69)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition38[temp1_11])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_68=nullDerefBool_69)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        sibling_20=(sibling_18)++((temp1_11)->(tmp_10)))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        sibling_18=sibling_20)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition2[thiz_0]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            nullDerefBool_70=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_69=nullDerefBool_70)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition2[thiz_0])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_69=nullDerefBool_70)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition46[head_9,
                                        thiz_0,
                                        tmp_10]
                      and 
                      (
                        (
                          BinHeapCondition2[thiz_0]
                          and 
                          (
                            (
                              BinHeapCondition0[throw_1]
                              and 
                              (
                                nullDerefBool_72=true)
                            )
                            or 
                            (
                              (
                                not (
                                  BinHeapCondition0[throw_1])
                              )
                              and 
                              TruePred[]
                              and 
                              (
                                nullDerefBool_70=nullDerefBool_72)
                            )
                          )
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition2[thiz_0])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_70=nullDerefBool_72)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition0[throw_1]
                          and 
                          (
                            head_10=(head_9)++((thiz_0)->(temp1_11)))
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_1])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            head_9=head_10)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition46[head_9,
                                            thiz_0,
                                            tmp_10]
                        )
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_70=nullDerefBool_72)
                      and 
                      (
                        head_9=head_10)
                    )
                  )
                )
              )
            )
          )
        )
        or 
        (
          TruePred[]
          and 
          (
            temp1_10=temp1_11)
          and 
          (
            temp2_10=temp2_11)
          and 
          (
            sibling_18=sibling_20)
          and 
          (
            nullDerefBool_65=nullDerefBool_72)
          and 
          (
            tmp_9=tmp_10)
          and 
          (
            head_9=head_10)
        )
      )
      and 
      BinHeapCondition53[temp1_11,
                        temp2_11]
    )
    or 
    (
      (
        not (
          BinHeapCondition0[throw_1])
      )
      and 
      TruePred[]
      and 
      (
        temp1_1=temp1_11)
      and 
      (
        temp2_1=temp2_11)
      and 
      (
        sibling_0=sibling_20)
      and 
      (
        nullDerefBool_2=nullDerefBool_72)
      and 
      (
        tmp_0=tmp_10)
      and 
      (
        head_0=head_10)
    )
  )
  and 
  (
    (
      BinHeapCondition56[temp1_11]
      and 
      (
        (
          BinHeapCondition2[thiz_0]
          and 
          (
            (
              BinHeapCondition0[throw_1]
              and 
              (
                nullDerefBool_73=true)
            )
            or 
            (
              (
                not (
                  BinHeapCondition0[throw_1])
              )
              and 
              TruePred[]
              and 
              (
                nullDerefBool_72=nullDerefBool_73)
            )
          )
        )
        or 
        (
          (
            not (
              BinHeapCondition2[thiz_0])
          )
          and 
          TruePred[]
          and 
          (
            nullDerefBool_72=nullDerefBool_73)
        )
      )
      and 
      (
        (
          BinHeapCondition0[throw_1]
          and 
          (
            temp1_12=thiz_0.head_10)
        )
        or 
        (
          (
            not (
              BinHeapCondition0[throw_1])
          )
          and 
          TruePred[]
          and 
          (
            temp1_11=temp1_12)
        )
      )
      and 
      (
        (
          BinHeapCondition38[temp1_12]
          and 
          (
            (
              BinHeapCondition0[throw_1]
              and 
              (
                nullDerefBool_74=true)
            )
            or 
            (
              (
                not (
                  BinHeapCondition0[throw_1])
              )
              and 
              TruePred[]
              and 
              (
                nullDerefBool_73=nullDerefBool_74)
            )
          )
        )
        or 
        (
          (
            not (
              BinHeapCondition38[temp1_12])
          )
          and 
          TruePred[]
          and 
          (
            nullDerefBool_73=nullDerefBool_74)
        )
      )
      and 
      (
        (
          BinHeapCondition0[throw_1]
          and 
          (
            (
              BinHeapCondition54[sibling_20,
                                temp1_12]
              and 
              (
                (
                  BinHeapCondition38[temp1_12]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        nullDerefBool_75=true)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_74=nullDerefBool_75)
                    )
                  )
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition38[temp1_12])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_74=nullDerefBool_75)
                )
              )
              and 
              (
                (
                  BinHeapCondition0[throw_1]
                  and 
                  (
                    temp1_13=temp1_12.sibling_20)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    temp1_12=temp1_13)
                )
              )
            )
            or 
            (
              TruePred[]
              and 
              (
                temp1_12=temp1_13)
              and 
              (
                nullDerefBool_74=nullDerefBool_75)
            )
          )
          and 
          (
            (
              BinHeapCondition54[sibling_20,
                                temp1_13]
              and 
              (
                (
                  BinHeapCondition38[temp1_13]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        nullDerefBool_76=true)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_75=nullDerefBool_76)
                    )
                  )
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition38[temp1_13])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_75=nullDerefBool_76)
                )
              )
              and 
              (
                (
                  BinHeapCondition0[throw_1]
                  and 
                  (
                    temp1_14=temp1_13.sibling_20)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    temp1_13=temp1_14)
                )
              )
            )
            or 
            (
              TruePred[]
              and 
              (
                temp1_13=temp1_14)
              and 
              (
                nullDerefBool_75=nullDerefBool_76)
            )
          )
          and 
          (
            (
              BinHeapCondition54[sibling_20,
                                temp1_14]
              and 
              (
                (
                  BinHeapCondition38[temp1_14]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        nullDerefBool_77=true)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_76=nullDerefBool_77)
                    )
                  )
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition38[temp1_14])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_76=nullDerefBool_77)
                )
              )
              and 
              (
                (
                  BinHeapCondition0[throw_1]
                  and 
                  (
                    temp1_15=temp1_14.sibling_20)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    temp1_14=temp1_15)
                )
              )
            )
            or 
            (
              TruePred[]
              and 
              (
                temp1_14=temp1_15)
              and 
              (
                nullDerefBool_76=nullDerefBool_77)
            )
          )
          and 
          (
            (
              BinHeapCondition54[sibling_20,
                                temp1_15]
              and 
              (
                (
                  BinHeapCondition38[temp1_15]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        nullDerefBool_78=true)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_77=nullDerefBool_78)
                    )
                  )
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition38[temp1_15])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_77=nullDerefBool_78)
                )
              )
              and 
              (
                (
                  BinHeapCondition0[throw_1]
                  and 
                  (
                    temp1_16=temp1_15.sibling_20)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    temp1_15=temp1_16)
                )
              )
            )
            or 
            (
              TruePred[]
              and 
              (
                temp1_15=temp1_16)
              and 
              (
                nullDerefBool_77=nullDerefBool_78)
            )
          )
          and 
          (
            (
              BinHeapCondition54[sibling_20,
                                temp1_16]
              and 
              (
                (
                  BinHeapCondition38[temp1_16]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        nullDerefBool_79=true)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_78=nullDerefBool_79)
                    )
                  )
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition38[temp1_16])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_78=nullDerefBool_79)
                )
              )
              and 
              (
                (
                  BinHeapCondition0[throw_1]
                  and 
                  (
                    temp1_17=temp1_16.sibling_20)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    temp1_16=temp1_17)
                )
              )
            )
            or 
            (
              TruePred[]
              and 
              (
                temp1_16=temp1_17)
              and 
              (
                nullDerefBool_78=nullDerefBool_79)
            )
          )
          and 
          (
            (
              BinHeapCondition54[sibling_20,
                                temp1_17]
              and 
              (
                (
                  BinHeapCondition38[temp1_17]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        nullDerefBool_80=true)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_79=nullDerefBool_80)
                    )
                  )
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition38[temp1_17])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_79=nullDerefBool_80)
                )
              )
              and 
              (
                (
                  BinHeapCondition0[throw_1]
                  and 
                  (
                    temp1_18=temp1_17.sibling_20)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    temp1_17=temp1_18)
                )
              )
            )
            or 
            (
              TruePred[]
              and 
              (
                temp1_17=temp1_18)
              and 
              (
                nullDerefBool_79=nullDerefBool_80)
            )
          )
          and 
          (
            (
              BinHeapCondition54[sibling_20,
                                temp1_18]
              and 
              (
                (
                  BinHeapCondition38[temp1_18]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        nullDerefBool_81=true)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_80=nullDerefBool_81)
                    )
                  )
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition38[temp1_18])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_80=nullDerefBool_81)
                )
              )
              and 
              (
                (
                  BinHeapCondition0[throw_1]
                  and 
                  (
                    temp1_19=temp1_18.sibling_20)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    temp1_18=temp1_19)
                )
              )
            )
            or 
            (
              TruePred[]
              and 
              (
                temp1_18=temp1_19)
              and 
              (
                nullDerefBool_80=nullDerefBool_81)
            )
          )
          and 
          (
            (
              BinHeapCondition54[sibling_20,
                                temp1_19]
              and 
              (
                (
                  BinHeapCondition38[temp1_19]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        nullDerefBool_82=true)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_81=nullDerefBool_82)
                    )
                  )
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition38[temp1_19])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_81=nullDerefBool_82)
                )
              )
              and 
              (
                (
                  BinHeapCondition0[throw_1]
                  and 
                  (
                    temp1_20=temp1_19.sibling_20)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    temp1_19=temp1_20)
                )
              )
            )
            or 
            (
              TruePred[]
              and 
              (
                temp1_19=temp1_20)
              and 
              (
                nullDerefBool_81=nullDerefBool_82)
            )
          )
          and 
          (
            (
              BinHeapCondition54[sibling_20,
                                temp1_20]
              and 
              (
                (
                  BinHeapCondition38[temp1_20]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        nullDerefBool_83=true)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_82=nullDerefBool_83)
                    )
                  )
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition38[temp1_20])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_82=nullDerefBool_83)
                )
              )
              and 
              (
                (
                  BinHeapCondition0[throw_1]
                  and 
                  (
                    temp1_21=temp1_20.sibling_20)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    temp1_20=temp1_21)
                )
              )
            )
            or 
            (
              TruePred[]
              and 
              (
                temp1_20=temp1_21)
              and 
              (
                nullDerefBool_82=nullDerefBool_83)
            )
          )
          and 
          (
            (
              BinHeapCondition54[sibling_20,
                                temp1_21]
              and 
              (
                (
                  BinHeapCondition38[temp1_21]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_1]
                      and 
                      (
                        nullDerefBool_84=true)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_1])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_83=nullDerefBool_84)
                    )
                  )
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition38[temp1_21])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_83=nullDerefBool_84)
                )
              )
              and 
              (
                (
                  BinHeapCondition0[throw_1]
                  and 
                  (
                    temp1_22=temp1_21.sibling_20)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    temp1_21=temp1_22)
                )
              )
            )
            or 
            (
              TruePred[]
              and 
              (
                temp1_21=temp1_22)
              and 
              (
                nullDerefBool_83=nullDerefBool_84)
            )
          )
          and 
          BinHeapCondition55[sibling_20,
                            temp1_22]
        )
        or 
        (
          (
            not (
              BinHeapCondition0[throw_1])
          )
          and 
          TruePred[]
          and 
          (
            temp1_12=temp1_22)
          and 
          (
            nullDerefBool_74=nullDerefBool_84)
        )
      )
      and 
      (
        (
          BinHeapCondition38[temp1_22]
          and 
          (
            (
              BinHeapCondition0[throw_1]
              and 
              (
                nullDerefBool_85=true)
            )
            or 
            (
              (
                not (
                  BinHeapCondition0[throw_1])
              )
              and 
              TruePred[]
              and 
              (
                nullDerefBool_84=nullDerefBool_85)
            )
          )
        )
        or 
        (
          (
            not (
              BinHeapCondition38[temp1_22])
          )
          and 
          TruePred[]
          and 
          (
            nullDerefBool_84=nullDerefBool_85)
        )
      )
      and 
      (
        (
          BinHeapCondition0[throw_1]
          and 
          (
            sibling_21=(sibling_20)++((temp1_22)->(temp2_11)))
        )
        or 
        (
          (
            not (
              BinHeapCondition0[throw_1])
          )
          and 
          TruePred[]
          and 
          (
            sibling_20=sibling_21)
        )
      )
    )
    or 
    (
      (
        not (
          BinHeapCondition56[temp1_11])
      )
      and 
      TruePred[]
      and 
      (
        sibling_20=sibling_21)
      and 
      (
        nullDerefBool_72=nullDerefBool_85)
      and 
      (
        temp1_11=temp1_22)
    )
  )
  and 
  (
    (
      BinHeapCondition30[nullDerefBool_85,
                        throw_1]
      and 
      (
        (
          BinHeapCondition0[throw_1]
          and 
          (
            throw_2=NullPointerExceptionLit)
        )
        or 
        (
          (
            not (
              BinHeapCondition0[throw_1])
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
          BinHeapCondition30[nullDerefBool_85,
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



pred BinHeap_unionNodes_0[
  thiz_0: BinHeap,
  throw_0: Throwable + null,
  throw_1: Throwable + null,
  throw_2: Throwable + null,
  throw_3: Throwable + null,
  throw_4: Throwable + null,
  throw_5: Throwable + null,
  throw_6: Throwable + null,
  throw_7: Throwable + null,
  throw_8: Throwable + null,
  throw_9: Throwable + null,
  throw_10: Throwable + null,
  throw_11: Throwable + null,
  throw_12: Throwable + null,
  throw_13: Throwable + null,
  throw_14: Throwable + null,
  throw_15: Throwable + null,
  throw_16: Throwable + null,
  throw_17: Throwable + null,
  throw_18: Throwable + null,
  throw_19: Throwable + null,
  throw_20: Throwable + null,
  throw_21: Throwable + null,
  throw_22: Throwable + null,
  throw_23: Throwable + null,
  throw_24: Throwable + null,
  throw_25: Throwable + null,
  throw_26: Throwable + null,
  throw_27: Throwable + null,
  throw_28: Throwable + null,
  throw_29: Throwable + null,
  throw_30: Throwable + null,
  throw_31: Throwable + null,
  throw_32: Throwable + null,
  throw_33: Throwable + null,
  throw_34: Throwable + null,
  throw_35: Throwable + null,
  throw_36: Throwable + null,
  throw_37: Throwable + null,
  throw_38: Throwable + null,
  throw_39: Throwable + null,
  throw_40: Throwable + null,
  throw_41: Throwable + null,
  throw_42: Throwable + null,
  throw_43: Throwable + null,
  throw_44: Throwable + null,
  binHeap_0: BinHeapNode + null,
  head_0: ( BinHeap ) -> one ( BinHeapNode + null ),
  head_1: ( BinHeap ) -> one ( BinHeapNode + null ),
  head_2: ( BinHeap ) -> one ( BinHeapNode + null ),
  head_3: ( BinHeap ) -> one ( BinHeapNode + null ),
  head_4: ( BinHeap ) -> one ( BinHeapNode + null ),
  head_5: ( BinHeap ) -> one ( BinHeapNode + null ),
  head_6: ( BinHeap ) -> one ( BinHeapNode + null ),
  head_7: ( BinHeap ) -> one ( BinHeapNode + null ),
  head_8: ( BinHeap ) -> one ( BinHeapNode + null ),
  head_9: ( BinHeap ) -> one ( BinHeapNode + null ),
  head_10: ( BinHeap ) -> one ( BinHeapNode + null ),
  head_11: ( BinHeap ) -> one ( BinHeapNode + null ),
  head_12: ( BinHeap ) -> one ( BinHeapNode + null ),
  head_13: ( BinHeap ) -> one ( BinHeapNode + null ),
  head_14: ( BinHeap ) -> one ( BinHeapNode + null ),
  head_15: ( BinHeap ) -> one ( BinHeapNode + null ),
  head_16: ( BinHeap ) -> one ( BinHeapNode + null ),
  head_17: ( BinHeap ) -> one ( BinHeapNode + null ),
  head_18: ( BinHeap ) -> one ( BinHeapNode + null ),
  head_19: ( BinHeap ) -> one ( BinHeapNode + null ),
  head_20: ( BinHeap ) -> one ( BinHeapNode + null ),
  degree_0: ( BinHeapNode ) -> one ( Int ),
  degree_1: ( BinHeapNode ) -> one ( Int ),
  degree_2: ( BinHeapNode ) -> one ( Int ),
  degree_3: ( BinHeapNode ) -> one ( Int ),
  degree_4: ( BinHeapNode ) -> one ( Int ),
  degree_5: ( BinHeapNode ) -> one ( Int ),
  degree_6: ( BinHeapNode ) -> one ( Int ),
  degree_7: ( BinHeapNode ) -> one ( Int ),
  degree_8: ( BinHeapNode ) -> one ( Int ),
  degree_9: ( BinHeapNode ) -> one ( Int ),
  degree_10: ( BinHeapNode ) -> one ( Int ),
  sibling_0: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_1: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_2: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_3: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_4: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_5: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_6: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_7: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_8: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_9: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_10: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_11: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_12: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_13: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_14: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_15: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_16: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_17: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_18: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_19: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_20: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_21: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_22: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_23: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_24: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_25: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_26: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_27: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_28: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_29: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_30: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_31: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_32: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_33: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_34: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_35: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_36: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_37: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_38: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_39: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_40: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_41: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  element_0: ( BinHeapNode ) -> one ( Data + null ),
  child_0: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  child_1: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  child_2: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  child_3: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  child_4: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  child_5: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  child_6: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  child_7: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  child_8: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  child_9: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  child_10: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  parent_0: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  parent_1: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  parent_2: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  parent_3: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  parent_4: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  parent_5: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  parent_6: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  parent_7: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  parent_8: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  parent_9: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  parent_10: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  nextTemp_0: BinHeapNode + null,
  nextTemp_1: BinHeapNode + null,
  nextTemp_2: BinHeapNode + null,
  nextTemp_3: BinHeapNode + null,
  nextTemp_4: BinHeapNode + null,
  nextTemp_5: BinHeapNode + null,
  nextTemp_6: BinHeapNode + null,
  nextTemp_7: BinHeapNode + null,
  nextTemp_8: BinHeapNode + null,
  nextTemp_9: BinHeapNode + null,
  nextTemp_10: BinHeapNode + null,
  nextTemp_11: BinHeapNode + null,
  prevTemp_0: BinHeapNode + null,
  prevTemp_1: BinHeapNode + null,
  prevTemp_2: BinHeapNode + null,
  prevTemp_3: BinHeapNode + null,
  prevTemp_4: BinHeapNode + null,
  prevTemp_5: BinHeapNode + null,
  prevTemp_6: BinHeapNode + null,
  prevTemp_7: BinHeapNode + null,
  prevTemp_8: BinHeapNode + null,
  prevTemp_9: BinHeapNode + null,
  prevTemp_10: BinHeapNode + null,
  prevTemp_11: BinHeapNode + null,
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
  nullDerefBool_29: boolean,
  nullDerefBool_30: boolean,
  nullDerefBool_31: boolean,
  nullDerefBool_32: boolean,
  nullDerefBool_33: boolean,
  nullDerefBool_34: boolean,
  nullDerefBool_35: boolean,
  nullDerefBool_36: boolean,
  nullDerefBool_37: boolean,
  nullDerefBool_38: boolean,
  nullDerefBool_39: boolean,
  nullDerefBool_40: boolean,
  nullDerefBool_41: boolean,
  nullDerefBool_42: boolean,
  nullDerefBool_43: boolean,
  nullDerefBool_44: boolean,
  nullDerefBool_45: boolean,
  nullDerefBool_46: boolean,
  nullDerefBool_47: boolean,
  nullDerefBool_48: boolean,
  nullDerefBool_49: boolean,
  nullDerefBool_50: boolean,
  nullDerefBool_51: boolean,
  nullDerefBool_52: boolean,
  nullDerefBool_53: boolean,
  nullDerefBool_54: boolean,
  nullDerefBool_55: boolean,
  nullDerefBool_56: boolean,
  nullDerefBool_57: boolean,
  nullDerefBool_58: boolean,
  nullDerefBool_59: boolean,
  nullDerefBool_60: boolean,
  nullDerefBool_61: boolean,
  nullDerefBool_62: boolean,
  nullDerefBool_63: boolean,
  nullDerefBool_64: boolean,
  nullDerefBool_65: boolean,
  nullDerefBool_66: boolean,
  nullDerefBool_67: boolean,
  nullDerefBool_68: boolean,
  nullDerefBool_69: boolean,
  nullDerefBool_70: boolean,
  nullDerefBool_71: boolean,
  nullDerefBool_72: boolean,
  nullDerefBool_73: boolean,
  nullDerefBool_74: boolean,
  nullDerefBool_75: boolean,
  nullDerefBool_76: boolean,
  nullDerefBool_77: boolean,
  nullDerefBool_78: boolean,
  nullDerefBool_79: boolean,
  nullDerefBool_80: boolean,
  nullDerefBool_81: boolean,
  nullDerefBool_82: boolean,
  nullDerefBool_83: boolean,
  lte_0: boolean,
  lte_1: boolean,
  lte_2: boolean,
  lte_3: boolean,
  lte_4: boolean,
  lte_5: boolean,
  lte_6: boolean,
  lte_7: boolean,
  lte_8: boolean,
  lte_9: boolean,
  lte_10: boolean,
  temp_0: BinHeapNode + null,
  temp_1: BinHeapNode + null,
  temp_2: BinHeapNode + null,
  temp_3: BinHeapNode + null,
  temp_4: BinHeapNode + null,
  temp_5: BinHeapNode + null,
  temp_6: BinHeapNode + null,
  temp_7: BinHeapNode + null,
  temp_8: BinHeapNode + null,
  temp_9: BinHeapNode + null,
  temp_10: BinHeapNode + null,
  temp_11: BinHeapNode + null,
  l8_nullDerefBool_0: boolean,
  l8_nullDerefBool_1: boolean,
  l8_lt_0: boolean,
  l8_lt_1: boolean,
  l10_l0_nullDerefBool_0: boolean,
  l10_l0_nullDerefBool_1: boolean,
  l9_l0_nullDerefBool_0: boolean,
  l9_l0_nullDerefBool_1: boolean,
  l5_lt_0: boolean,
  l5_lt_1: boolean,
  l9_lt_0: boolean,
  l9_lt_1: boolean,
  l5_l0_nullDerefBool_0: boolean,
  l5_l0_nullDerefBool_1: boolean,
  l10_lte_0: boolean,
  l10_lte_1: boolean,
  l10_lte_2: boolean,
  l6_l0_nullDerefBool_0: boolean,
  l6_l0_nullDerefBool_1: boolean,
  l6_lte_0: boolean,
  l6_lte_1: boolean,
  l6_lte_2: boolean,
  l8_l0_result_0: boolean,
  l8_l0_result_1: boolean,
  l8_l0_result_2: boolean,
  l11_l0_result_0: boolean,
  l11_l0_result_1: boolean,
  l11_l0_result_2: boolean,
  l10_lt_0: boolean,
  l10_lt_1: boolean,
  l3_l0_nullDerefBool_0: boolean,
  l3_l0_nullDerefBool_1: boolean,
  l11_nullDerefBool_0: boolean,
  l11_nullDerefBool_1: boolean,
  l3_lt_0: boolean,
  l3_lt_1: boolean,
  l3_l0_result_0: boolean,
  l3_l0_result_1: boolean,
  l3_l0_result_2: boolean,
  l2_l0_nullDerefBool_0: boolean,
  l2_l0_nullDerefBool_1: boolean,
  l11_lt_0: boolean,
  l11_lt_1: boolean,
  l2_nullDerefBool_0: boolean,
  l2_nullDerefBool_1: boolean,
  l4_lte_0: boolean,
  l4_lte_1: boolean,
  l4_lte_2: boolean,
  l9_l0_result_0: boolean,
  l9_l0_result_1: boolean,
  l9_l0_result_2: boolean,
  l8_l0_nullDerefBool_0: boolean,
  l8_l0_nullDerefBool_1: boolean,
  l4_l0_result_0: boolean,
  l4_l0_result_1: boolean,
  l4_l0_result_2: boolean,
  l7_nullDerefBool_0: boolean,
  l7_nullDerefBool_1: boolean,
  l3_lte_0: boolean,
  l3_lte_1: boolean,
  l3_lte_2: boolean,
  l1_temp2_0: BinHeapNode + null,
  l1_temp2_1: BinHeapNode + null,
  l1_temp2_2: BinHeapNode + null,
  l1_temp2_3: BinHeapNode + null,
  l1_temp2_4: BinHeapNode + null,
  l1_temp2_5: BinHeapNode + null,
  l1_temp2_6: BinHeapNode + null,
  l1_temp2_7: BinHeapNode + null,
  l1_temp2_8: BinHeapNode + null,
  l1_temp2_9: BinHeapNode + null,
  l1_temp2_10: BinHeapNode + null,
  l1_temp2_11: BinHeapNode + null,
  l1_temp1_0: BinHeapNode + null,
  l1_temp1_1: BinHeapNode + null,
  l1_temp1_2: BinHeapNode + null,
  l1_temp1_3: BinHeapNode + null,
  l1_temp1_4: BinHeapNode + null,
  l1_temp1_5: BinHeapNode + null,
  l1_temp1_6: BinHeapNode + null,
  l1_temp1_7: BinHeapNode + null,
  l1_temp1_8: BinHeapNode + null,
  l1_temp1_9: BinHeapNode + null,
  l1_temp1_10: BinHeapNode + null,
  l1_temp1_11: BinHeapNode + null,
  l1_temp1_12: BinHeapNode + null,
  l1_temp1_13: BinHeapNode + null,
  l1_temp1_14: BinHeapNode + null,
  l1_temp1_15: BinHeapNode + null,
  l1_temp1_16: BinHeapNode + null,
  l1_temp1_17: BinHeapNode + null,
  l1_temp1_18: BinHeapNode + null,
  l1_temp1_19: BinHeapNode + null,
  l1_temp1_20: BinHeapNode + null,
  l1_temp1_21: BinHeapNode + null,
  l1_temp1_22: BinHeapNode + null,
  l7_lte_0: boolean,
  l7_lte_1: boolean,
  l7_lte_2: boolean,
  l8_lte_0: boolean,
  l8_lte_1: boolean,
  l8_lte_2: boolean,
  l11_lte_0: boolean,
  l11_lte_1: boolean,
  l11_lte_2: boolean,
  l4_nullDerefBool_0: boolean,
  l4_nullDerefBool_1: boolean,
  l7_l0_nullDerefBool_0: boolean,
  l7_l0_nullDerefBool_1: boolean,
  l6_lt_0: boolean,
  l6_lt_1: boolean,
  l9_nullDerefBool_0: boolean,
  l9_nullDerefBool_1: boolean,
  l5_nullDerefBool_0: boolean,
  l5_nullDerefBool_1: boolean,
  l5_lte_0: boolean,
  l5_lte_1: boolean,
  l5_lte_2: boolean,
  l6_nullDerefBool_0: boolean,
  l6_nullDerefBool_1: boolean,
  l9_lte_0: boolean,
  l9_lte_1: boolean,
  l9_lte_2: boolean,
  l11_l0_nullDerefBool_0: boolean,
  l11_l0_nullDerefBool_1: boolean,
  l7_l0_result_0: boolean,
  l7_l0_result_1: boolean,
  l7_l0_result_2: boolean,
  l4_lt_0: boolean,
  l4_lt_1: boolean,
  l2_l0_result_0: boolean,
  l2_l0_result_1: boolean,
  l2_l0_result_2: boolean,
  l3_nullDerefBool_0: boolean,
  l3_nullDerefBool_1: boolean,
  l5_l0_result_0: boolean,
  l5_l0_result_1: boolean,
  l5_l0_result_2: boolean,
  l7_lt_0: boolean,
  l7_lt_1: boolean,
  l2_lte_0: boolean,
  l2_lte_1: boolean,
  l2_lte_2: boolean,
  l6_l0_result_0: boolean,
  l6_l0_result_1: boolean,
  l6_l0_result_2: boolean,
  l1_nullDerefBool_0: boolean,
  l1_nullDerefBool_1: boolean,
  l1_nullDerefBool_2: boolean,
  l1_nullDerefBool_3: boolean,
  l1_nullDerefBool_4: boolean,
  l1_nullDerefBool_5: boolean,
  l1_nullDerefBool_6: boolean,
  l1_nullDerefBool_7: boolean,
  l1_nullDerefBool_8: boolean,
  l1_nullDerefBool_9: boolean,
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
  l1_nullDerefBool_30: boolean,
  l1_nullDerefBool_31: boolean,
  l1_nullDerefBool_32: boolean,
  l1_nullDerefBool_33: boolean,
  l1_nullDerefBool_34: boolean,
  l1_nullDerefBool_35: boolean,
  l1_nullDerefBool_36: boolean,
  l1_nullDerefBool_37: boolean,
  l1_nullDerefBool_38: boolean,
  l1_nullDerefBool_39: boolean,
  l1_nullDerefBool_40: boolean,
  l1_nullDerefBool_41: boolean,
  l1_nullDerefBool_42: boolean,
  l1_nullDerefBool_43: boolean,
  l1_nullDerefBool_44: boolean,
  l1_nullDerefBool_45: boolean,
  l1_nullDerefBool_46: boolean,
  l1_nullDerefBool_47: boolean,
  l1_nullDerefBool_48: boolean,
  l1_nullDerefBool_49: boolean,
  l1_nullDerefBool_50: boolean,
  l1_nullDerefBool_51: boolean,
  l1_nullDerefBool_52: boolean,
  l1_nullDerefBool_53: boolean,
  l1_nullDerefBool_54: boolean,
  l1_nullDerefBool_55: boolean,
  l1_nullDerefBool_56: boolean,
  l1_nullDerefBool_57: boolean,
  l1_nullDerefBool_58: boolean,
  l1_nullDerefBool_59: boolean,
  l1_nullDerefBool_60: boolean,
  l1_nullDerefBool_61: boolean,
  l1_nullDerefBool_62: boolean,
  l1_nullDerefBool_63: boolean,
  l1_nullDerefBool_64: boolean,
  l1_nullDerefBool_65: boolean,
  l1_nullDerefBool_66: boolean,
  l1_nullDerefBool_67: boolean,
  l1_nullDerefBool_68: boolean,
  l1_nullDerefBool_69: boolean,
  l1_nullDerefBool_70: boolean,
  l1_nullDerefBool_71: boolean,
  l1_nullDerefBool_72: boolean,
  l1_nullDerefBool_73: boolean,
  l1_nullDerefBool_74: boolean,
  l1_nullDerefBool_75: boolean,
  l1_nullDerefBool_76: boolean,
  l1_nullDerefBool_77: boolean,
  l1_nullDerefBool_78: boolean,
  l1_nullDerefBool_79: boolean,
  l1_nullDerefBool_80: boolean,
  l1_nullDerefBool_81: boolean,
  l1_nullDerefBool_82: boolean,
  l1_nullDerefBool_83: boolean,
  l1_nullDerefBool_84: boolean,
  l1_nullDerefBool_85: boolean,
  l4_l0_nullDerefBool_0: boolean,
  l4_l0_nullDerefBool_1: boolean,
  l10_l0_result_0: boolean,
  l10_l0_result_1: boolean,
  l10_l0_result_2: boolean,
  l2_lt_0: boolean,
  l2_lt_1: boolean,
  l1_tmp_0: BinHeapNode + null,
  l1_tmp_1: BinHeapNode + null,
  l1_tmp_2: BinHeapNode + null,
  l1_tmp_3: BinHeapNode + null,
  l1_tmp_4: BinHeapNode + null,
  l1_tmp_5: BinHeapNode + null,
  l1_tmp_6: BinHeapNode + null,
  l1_tmp_7: BinHeapNode + null,
  l1_tmp_8: BinHeapNode + null,
  l1_tmp_9: BinHeapNode + null,
  l1_tmp_10: BinHeapNode + null,
  l10_nullDerefBool_0: boolean,
  l10_nullDerefBool_1: boolean
]{
  TruePred[]
  and 
  (
    (
      BinHeapCondition0[throw_0]
      and 
      (
        nullDerefBool_1=false)
    )
    or 
    (
      (
        not (
          BinHeapCondition0[throw_0])
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
      BinHeapCondition0[throw_0]
      and 
      (
        throw_1=null)
    )
    or 
    (
      (
        not (
          BinHeapCondition0[throw_0])
      )
      and 
      TruePred[]
      and 
      (
        throw_0=throw_1)
    )
  )
  and 
  (
    (
      BinHeapCondition0[throw_1]
      and 
      BinHeap_merge_0[thiz_0,
                     throw_1,
                     throw_2,
                     throw_3,
                     binHeap_0,
                     head_0,
                     head_1,
                     head_2,
                     head_3,
                     head_4,
                     head_5,
                     head_6,
                     head_7,
                     head_8,
                     head_9,
                     head_10,
                     degree_0,
                     sibling_0,
                     sibling_1,
                     sibling_2,
                     sibling_3,
                     sibling_4,
                     sibling_5,
                     sibling_6,
                     sibling_7,
                     sibling_8,
                     sibling_9,
                     sibling_10,
                     sibling_11,
                     sibling_12,
                     sibling_13,
                     sibling_14,
                     sibling_15,
                     sibling_16,
                     sibling_17,
                     sibling_18,
                     sibling_19,
                     sibling_20,
                     sibling_21,
                     l1_temp1_0,
                     l1_temp1_1,
                     l1_temp1_2,
                     l1_temp1_3,
                     l1_temp1_4,
                     l1_temp1_5,
                     l1_temp1_6,
                     l1_temp1_7,
                     l1_temp1_8,
                     l1_temp1_9,
                     l1_temp1_10,
                     l1_temp1_11,
                     l1_temp1_12,
                     l1_temp1_13,
                     l1_temp1_14,
                     l1_temp1_15,
                     l1_temp1_16,
                     l1_temp1_17,
                     l1_temp1_18,
                     l1_temp1_19,
                     l1_temp1_20,
                     l1_temp1_21,
                     l1_temp1_22,
                     l1_temp2_0,
                     l1_temp2_1,
                     l1_temp2_2,
                     l1_temp2_3,
                     l1_temp2_4,
                     l1_temp2_5,
                     l1_temp2_6,
                     l1_temp2_7,
                     l1_temp2_8,
                     l1_temp2_9,
                     l1_temp2_10,
                     l1_temp2_11,
                     l1_tmp_0,
                     l1_tmp_1,
                     l1_tmp_2,
                     l1_tmp_3,
                     l1_tmp_4,
                     l1_tmp_5,
                     l1_tmp_6,
                     l1_tmp_7,
                     l1_tmp_8,
                     l1_tmp_9,
                     l1_tmp_10,
                     l1_nullDerefBool_0,
                     l1_nullDerefBool_1,
                     l1_nullDerefBool_2,
                     l1_nullDerefBool_3,
                     l1_nullDerefBool_4,
                     l1_nullDerefBool_5,
                     l1_nullDerefBool_6,
                     l1_nullDerefBool_7,
                     l1_nullDerefBool_8,
                     l1_nullDerefBool_9,
                     l1_nullDerefBool_10,
                     l1_nullDerefBool_11,
                     l1_nullDerefBool_12,
                     l1_nullDerefBool_13,
                     l1_nullDerefBool_14,
                     l1_nullDerefBool_15,
                     l1_nullDerefBool_16,
                     l1_nullDerefBool_17,
                     l1_nullDerefBool_18,
                     l1_nullDerefBool_19,
                     l1_nullDerefBool_20,
                     l1_nullDerefBool_21,
                     l1_nullDerefBool_22,
                     l1_nullDerefBool_23,
                     l1_nullDerefBool_24,
                     l1_nullDerefBool_25,
                     l1_nullDerefBool_26,
                     l1_nullDerefBool_27,
                     l1_nullDerefBool_28,
                     l1_nullDerefBool_29,
                     l1_nullDerefBool_30,
                     l1_nullDerefBool_31,
                     l1_nullDerefBool_32,
                     l1_nullDerefBool_33,
                     l1_nullDerefBool_34,
                     l1_nullDerefBool_35,
                     l1_nullDerefBool_36,
                     l1_nullDerefBool_37,
                     l1_nullDerefBool_38,
                     l1_nullDerefBool_39,
                     l1_nullDerefBool_40,
                     l1_nullDerefBool_41,
                     l1_nullDerefBool_42,
                     l1_nullDerefBool_43,
                     l1_nullDerefBool_44,
                     l1_nullDerefBool_45,
                     l1_nullDerefBool_46,
                     l1_nullDerefBool_47,
                     l1_nullDerefBool_48,
                     l1_nullDerefBool_49,
                     l1_nullDerefBool_50,
                     l1_nullDerefBool_51,
                     l1_nullDerefBool_52,
                     l1_nullDerefBool_53,
                     l1_nullDerefBool_54,
                     l1_nullDerefBool_55,
                     l1_nullDerefBool_56,
                     l1_nullDerefBool_57,
                     l1_nullDerefBool_58,
                     l1_nullDerefBool_59,
                     l1_nullDerefBool_60,
                     l1_nullDerefBool_61,
                     l1_nullDerefBool_62,
                     l1_nullDerefBool_63,
                     l1_nullDerefBool_64,
                     l1_nullDerefBool_65,
                     l1_nullDerefBool_66,
                     l1_nullDerefBool_67,
                     l1_nullDerefBool_68,
                     l1_nullDerefBool_69,
                     l1_nullDerefBool_70,
                     l1_nullDerefBool_71,
                     l1_nullDerefBool_72,
                     l1_nullDerefBool_73,
                     l1_nullDerefBool_74,
                     l1_nullDerefBool_75,
                     l1_nullDerefBool_76,
                     l1_nullDerefBool_77,
                     l1_nullDerefBool_78,
                     l1_nullDerefBool_79,
                     l1_nullDerefBool_80,
                     l1_nullDerefBool_81,
                     l1_nullDerefBool_82,
                     l1_nullDerefBool_83,
                     l1_nullDerefBool_84,
                     l1_nullDerefBool_85]
    )
    or 
    (
      (
        not (
          BinHeapCondition0[throw_1])
      )
      and 
      TruePred[]
      and 
      (
        l1_nullDerefBool_0=l1_nullDerefBool_85)
      and 
      (
        l1_tmp_0=l1_tmp_10)
      and 
      (
        sibling_0=sibling_21)
      and 
      (
        l1_temp2_0=l1_temp2_11)
      and 
      (
        l1_temp1_0=l1_temp1_22)
      and 
      (
        head_0=head_10)
      and 
      (
        throw_1=throw_3)
    )
  )
  and 
  TruePred[]
  and 
  (
    (
      BinHeapCondition0[throw_3]
      and 
      (
        prevTemp_1=null)
    )
    or 
    (
      (
        not (
          BinHeapCondition0[throw_3])
      )
      and 
      TruePred[]
      and 
      (
        prevTemp_0=prevTemp_1)
    )
  )
  and 
  TruePred[]
  and 
  (
    (
      BinHeapCondition2[thiz_0]
      and 
      (
        (
          BinHeapCondition0[throw_3]
          and 
          (
            nullDerefBool_2=true)
        )
        or 
        (
          (
            not (
              BinHeapCondition0[throw_3])
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
          BinHeapCondition2[thiz_0])
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
      BinHeapCondition0[throw_3]
      and 
      (
        temp_1=thiz_0.head_10)
    )
    or 
    (
      (
        not (
          BinHeapCondition0[throw_3])
      )
      and 
      TruePred[]
      and 
      (
        temp_0=temp_1)
    )
  )
  and 
  TruePred[]
  and 
  (
    (
      BinHeapCondition4[head_10,
                       thiz_0]
      and 
      (
        (
          BinHeapCondition0[throw_3]
          and 
          (
            nullDerefBool_3=true)
        )
        or 
        (
          (
            not (
              BinHeapCondition0[throw_3])
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
          BinHeapCondition4[head_10,
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
    (
      BinHeapCondition0[throw_3]
      and 
      (
        nextTemp_1=(thiz_0.head_10).sibling_21)
    )
    or 
    (
      (
        not (
          BinHeapCondition0[throw_3])
      )
      and 
      TruePred[]
      and 
      (
        nextTemp_0=nextTemp_1)
    )
  )
  and 
  (
    (
      BinHeapCondition0[throw_3]
      and 
      (
        (
          BinHeapCondition28[nextTemp_1]
          and 
          (
            (
              BinHeapCondition6[nextTemp_1,
                               sibling_21,
                               temp_1]
              and 
              (
                (
                  BinHeapCondition0[throw_3]
                  and 
                  (
                    nullDerefBool_4=true)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_3])
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
                  BinHeapCondition6[nextTemp_1,
                                   sibling_21,
                                   temp_1]
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
            (
              BinHeapCondition26[degree_0,
                                nextTemp_1,
                                sibling_21,
                                temp_1]
              and 
              (
                (
                  BinHeapCondition0[throw_3]
                  and 
                  (
                    prevTemp_2=temp_1)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_3])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    prevTemp_1=prevTemp_2)
                )
              )
              and 
              (
                (
                  BinHeapCondition0[throw_3]
                  and 
                  (
                    temp_2=nextTemp_1)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_3])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    temp_1=temp_2)
                )
              )
              and 
              (
                l2_l0_result_0=l2_l0_result_2)
              and 
              (
                l2_lte_0=l2_lte_2)
              and 
              (
                parent_0=parent_1)
              and 
              (
                nullDerefBool_4=nullDerefBool_10)
              and 
              (
                l2_l0_nullDerefBool_0=l2_l0_nullDerefBool_1)
              and 
              (
                l2_nullDerefBool_0=l2_nullDerefBool_1)
              and 
              (
                child_0=child_1)
              and 
              (
                l2_lt_0=l2_lt_1)
              and 
              (
                head_10=head_11)
              and 
              (
                lte_0=lte_1)
              and 
              (
                throw_3=throw_7)
              and 
              (
                degree_0=degree_1)
              and 
              (
                sibling_21=sibling_23)
            )
            or 
            (
              (
                not (
                  BinHeapCondition26[degree_0,
                                    nextTemp_1,
                                    sibling_21,
                                    temp_1]
                )
              )
              and 
              TruePred[]
              and 
              (
                (
                  BinHeapCondition8[nextTemp_1,
                                   temp_1]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_3]
                      and 
                      (
                        nullDerefBool_5=true)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_3])
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
                      BinHeapCondition8[nextTemp_1,
                                       temp_1]
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
                  BinHeapCondition0[throw_3]
                  and 
                  Data_data_lte_0[temp_1.element_0,
                                 throw_3,
                                 throw_4,
                                 throw_5,
                                 throw_6,
                                 throw_7,
                                 lte_0,
                                 lte_1,
                                 nextTemp_1.element_0,
                                 l2_lt_0,
                                 l2_lt_1,
                                 l2_nullDerefBool_0,
                                 l2_nullDerefBool_1,
                                 l2_lte_0,
                                 l2_lte_1,
                                 l2_lte_2,
                                 l2_l0_result_0,
                                 l2_l0_result_1,
                                 l2_l0_result_2,
                                 l2_l0_nullDerefBool_0,
                                 l2_l0_nullDerefBool_1]
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_3])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    l2_l0_result_0=l2_l0_result_2)
                  and 
                  (
                    l2_nullDerefBool_0=l2_nullDerefBool_1)
                  and 
                  (
                    l2_lt_0=l2_lt_1)
                  and 
                  (
                    l2_lte_0=l2_lte_2)
                  and 
                  (
                    lte_0=lte_1)
                  and 
                  (
                    l2_l0_nullDerefBool_0=l2_l0_nullDerefBool_1)
                  and 
                  (
                    throw_3=throw_7)
                )
              )
              and 
              (
                (
                  BinHeapCondition24[lte_1]
                  and 
                  (
                    (
                      BinHeapCondition8[nextTemp_1,
                                       temp_1]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_7]
                          and 
                          (
                            nullDerefBool_6=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_7])
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
                          BinHeapCondition8[nextTemp_1,
                                           temp_1]
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
                    (
                      BinHeapCondition0[throw_7]
                      and 
                      (
                        sibling_22=(sibling_21)++((temp_1)->(nextTemp_1.sibling_21)))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_7])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        sibling_21=sibling_22)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition10[nextTemp_1]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_7]
                          and 
                          (
                            nullDerefBool_7=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_7])
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
                          BinHeapCondition10[nextTemp_1])
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
                      BinHeapCondition0[throw_7]
                      and 
                      (
                        parent_1=(parent_0)++((nextTemp_1)->(temp_1)))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_7])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        parent_0=parent_1)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition12[nextTemp_1,
                                        temp_1]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_7]
                          and 
                          (
                            nullDerefBool_8=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_7])
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
                          BinHeapCondition12[nextTemp_1,
                                            temp_1]
                        )
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
                      BinHeapCondition0[throw_7]
                      and 
                      (
                        sibling_23=(sibling_22)++((nextTemp_1)->(temp_1.child_0)))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_7])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        sibling_22=sibling_23)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition14[temp_1]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_7]
                          and 
                          (
                            nullDerefBool_9=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_7])
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
                          BinHeapCondition14[temp_1])
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
                      BinHeapCondition0[throw_7]
                      and 
                      (
                        child_1=(child_0)++((temp_1)->(nextTemp_1)))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_7])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        child_0=child_1)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition16[temp_1]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_7]
                          and 
                          (
                            nullDerefBool_10=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_7])
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
                          BinHeapCondition16[temp_1])
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
                      BinHeapCondition0[throw_7]
                      and 
                      (
                        degree_1=(degree_0)++((temp_1)->(add[temp_1.degree_0,1])))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_7])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        degree_0=degree_1)
                    )
                  )
                  and 
                  (
                    head_10=head_11)
                  and 
                  (
                    temp_1=temp_2)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition24[lte_1])
                  )
                  and 
                  (
                    (
                      BinHeapCondition20[prevTemp_1]
                      and 
                      (
                        (
                          BinHeapCondition2[thiz_0]
                          and 
                          (
                            (
                              BinHeapCondition0[throw_7]
                              and 
                              (
                                nullDerefBool_6=true)
                            )
                            or 
                            (
                              (
                                not (
                                  BinHeapCondition0[throw_7])
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
                              BinHeapCondition2[thiz_0])
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
                          BinHeapCondition0[throw_7]
                          and 
                          (
                            head_11=(head_10)++((thiz_0)->(nextTemp_1)))
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_7])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            head_10=head_11)
                        )
                      )
                      and 
                      (
                        sibling_21=sibling_22)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition20[prevTemp_1])
                      )
                      and 
                      (
                        (
                          BinHeapCondition18[prevTemp_1]
                          and 
                          (
                            (
                              BinHeapCondition0[throw_7]
                              and 
                              (
                                nullDerefBool_6=true)
                            )
                            or 
                            (
                              (
                                not (
                                  BinHeapCondition0[throw_7])
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
                              BinHeapCondition18[prevTemp_1])
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
                          BinHeapCondition0[throw_7]
                          and 
                          (
                            sibling_22=(sibling_21)++((prevTemp_1)->(nextTemp_1)))
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_7])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            sibling_21=sibling_22)
                        )
                      )
                      and 
                      (
                        head_10=head_11)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition14[temp_1]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_7]
                          and 
                          (
                            nullDerefBool_7=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_7])
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
                          BinHeapCondition14[temp_1])
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
                      BinHeapCondition0[throw_7]
                      and 
                      (
                        parent_1=(parent_0)++((temp_1)->(nextTemp_1)))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_7])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        parent_0=parent_1)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition8[nextTemp_1,
                                       temp_1]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_7]
                          and 
                          (
                            nullDerefBool_8=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_7])
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
                          BinHeapCondition8[nextTemp_1,
                                           temp_1]
                        )
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
                      BinHeapCondition0[throw_7]
                      and 
                      (
                        sibling_23=(sibling_22)++((temp_1)->(nextTemp_1.child_0)))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_7])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        sibling_22=sibling_23)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition10[nextTemp_1]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_7]
                          and 
                          (
                            nullDerefBool_9=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_7])
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
                          BinHeapCondition10[nextTemp_1])
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
                      BinHeapCondition0[throw_7]
                      and 
                      (
                        child_1=(child_0)++((nextTemp_1)->(temp_1)))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_7])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        child_0=child_1)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition22[nextTemp_1]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_7]
                          and 
                          (
                            nullDerefBool_10=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_7])
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
                          BinHeapCondition22[nextTemp_1])
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
                      BinHeapCondition0[throw_7]
                      and 
                      (
                        degree_1=(degree_0)++((nextTemp_1)->(add[nextTemp_1.degree_0,1])))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_7])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        degree_0=degree_1)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_7]
                      and 
                      (
                        temp_2=nextTemp_1)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_7])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        temp_1=temp_2)
                    )
                  )
                )
              )
              and 
              (
                prevTemp_1=prevTemp_2)
            )
          )
          and 
          (
            (
              BinHeapCondition14[temp_2]
              and 
              (
                (
                  BinHeapCondition0[throw_7]
                  and 
                  (
                    nullDerefBool_11=true)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_7])
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
                  BinHeapCondition14[temp_2])
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
              BinHeapCondition0[throw_7]
              and 
              (
                nextTemp_2=temp_2.sibling_23)
            )
            or 
            (
              (
                not (
                  BinHeapCondition0[throw_7])
              )
              and 
              TruePred[]
              and 
              (
                nextTemp_1=nextTemp_2)
            )
          )
        )
        or 
        (
          TruePred[]
          and 
          (
            l2_l0_result_0=l2_l0_result_2)
          and 
          (
            l2_lte_0=l2_lte_2)
          and 
          (
            parent_0=parent_1)
          and 
          (
            nullDerefBool_3=nullDerefBool_11)
          and 
          (
            l2_l0_nullDerefBool_0=l2_l0_nullDerefBool_1)
          and 
          (
            l2_nullDerefBool_0=l2_nullDerefBool_1)
          and 
          (
            child_0=child_1)
          and 
          (
            nextTemp_1=nextTemp_2)
          and 
          (
            throw_3=throw_7)
          and 
          (
            l2_lt_0=l2_lt_1)
          and 
          (
            degree_0=degree_1)
          and 
          (
            prevTemp_1=prevTemp_2)
          and 
          (
            sibling_21=sibling_23)
          and 
          (
            temp_1=temp_2)
          and 
          (
            head_10=head_11)
          and 
          (
            lte_0=lte_1)
        )
      )
      and 
      (
        (
          BinHeapCondition28[nextTemp_2]
          and 
          (
            (
              BinHeapCondition6[nextTemp_2,
                               sibling_23,
                               temp_2]
              and 
              (
                (
                  BinHeapCondition0[throw_7]
                  and 
                  (
                    nullDerefBool_12=true)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_7])
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
                  BinHeapCondition6[nextTemp_2,
                                   sibling_23,
                                   temp_2]
                )
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
              BinHeapCondition26[degree_1,
                                nextTemp_2,
                                sibling_23,
                                temp_2]
              and 
              (
                (
                  BinHeapCondition0[throw_7]
                  and 
                  (
                    prevTemp_3=temp_2)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_7])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    prevTemp_2=prevTemp_3)
                )
              )
              and 
              (
                (
                  BinHeapCondition0[throw_7]
                  and 
                  (
                    temp_3=nextTemp_2)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_7])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    temp_2=temp_3)
                )
              )
              and 
              (
                l3_nullDerefBool_0=l3_nullDerefBool_1)
              and 
              (
                l3_l0_nullDerefBool_0=l3_l0_nullDerefBool_1)
              and 
              (
                parent_1=parent_2)
              and 
              (
                nullDerefBool_12=nullDerefBool_18)
              and 
              (
                l3_lt_0=l3_lt_1)
              and 
              (
                l3_l0_result_0=l3_l0_result_2)
              and 
              (
                child_1=child_2)
              and 
              (
                l3_lte_0=l3_lte_2)
              and 
              (
                head_11=head_12)
              and 
              (
                lte_1=lte_2)
              and 
              (
                throw_7=throw_11)
              and 
              (
                degree_1=degree_2)
              and 
              (
                sibling_23=sibling_25)
            )
            or 
            (
              (
                not (
                  BinHeapCondition26[degree_1,
                                    nextTemp_2,
                                    sibling_23,
                                    temp_2]
                )
              )
              and 
              TruePred[]
              and 
              (
                (
                  BinHeapCondition8[nextTemp_2,
                                   temp_2]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_7]
                      and 
                      (
                        nullDerefBool_13=true)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_7])
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
                      BinHeapCondition8[nextTemp_2,
                                       temp_2]
                    )
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
                  BinHeapCondition0[throw_7]
                  and 
                  Data_data_lte_0[temp_2.element_0,
                                 throw_7,
                                 throw_8,
                                 throw_9,
                                 throw_10,
                                 throw_11,
                                 lte_1,
                                 lte_2,
                                 nextTemp_2.element_0,
                                 l3_lt_0,
                                 l3_lt_1,
                                 l3_nullDerefBool_0,
                                 l3_nullDerefBool_1,
                                 l3_lte_0,
                                 l3_lte_1,
                                 l3_lte_2,
                                 l3_l0_result_0,
                                 l3_l0_result_1,
                                 l3_l0_result_2,
                                 l3_l0_nullDerefBool_0,
                                 l3_l0_nullDerefBool_1]
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_7])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    l3_nullDerefBool_0=l3_nullDerefBool_1)
                  and 
                  (
                    l3_l0_nullDerefBool_0=l3_l0_nullDerefBool_1)
                  and 
                  (
                    l3_lt_0=l3_lt_1)
                  and 
                  (
                    l3_lte_0=l3_lte_2)
                  and 
                  (
                    l3_l0_result_0=l3_l0_result_2)
                  and 
                  (
                    lte_1=lte_2)
                  and 
                  (
                    throw_7=throw_11)
                )
              )
              and 
              (
                (
                  BinHeapCondition24[lte_2]
                  and 
                  (
                    (
                      BinHeapCondition8[nextTemp_2,
                                       temp_2]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_11]
                          and 
                          (
                            nullDerefBool_14=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_11])
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
                          BinHeapCondition8[nextTemp_2,
                                           temp_2]
                        )
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
                      BinHeapCondition0[throw_11]
                      and 
                      (
                        sibling_24=(sibling_23)++((temp_2)->(nextTemp_2.sibling_23)))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_11])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        sibling_23=sibling_24)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition10[nextTemp_2]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_11]
                          and 
                          (
                            nullDerefBool_15=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_11])
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
                          BinHeapCondition10[nextTemp_2])
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
                      BinHeapCondition0[throw_11]
                      and 
                      (
                        parent_2=(parent_1)++((nextTemp_2)->(temp_2)))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_11])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        parent_1=parent_2)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition12[nextTemp_2,
                                        temp_2]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_11]
                          and 
                          (
                            nullDerefBool_16=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_11])
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
                          BinHeapCondition12[nextTemp_2,
                                            temp_2]
                        )
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
                      BinHeapCondition0[throw_11]
                      and 
                      (
                        sibling_25=(sibling_24)++((nextTemp_2)->(temp_2.child_1)))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_11])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        sibling_24=sibling_25)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition14[temp_2]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_11]
                          and 
                          (
                            nullDerefBool_17=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_11])
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
                          BinHeapCondition14[temp_2])
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
                      BinHeapCondition0[throw_11]
                      and 
                      (
                        child_2=(child_1)++((temp_2)->(nextTemp_2)))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_11])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        child_1=child_2)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition16[temp_2]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_11]
                          and 
                          (
                            nullDerefBool_18=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_11])
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
                          BinHeapCondition16[temp_2])
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
                      BinHeapCondition0[throw_11]
                      and 
                      (
                        degree_2=(degree_1)++((temp_2)->(add[temp_2.degree_1,1])))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_11])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        degree_1=degree_2)
                    )
                  )
                  and 
                  (
                    head_11=head_12)
                  and 
                  (
                    temp_2=temp_3)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition24[lte_2])
                  )
                  and 
                  (
                    (
                      BinHeapCondition20[prevTemp_2]
                      and 
                      (
                        (
                          BinHeapCondition2[thiz_0]
                          and 
                          (
                            (
                              BinHeapCondition0[throw_11]
                              and 
                              (
                                nullDerefBool_14=true)
                            )
                            or 
                            (
                              (
                                not (
                                  BinHeapCondition0[throw_11])
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
                              BinHeapCondition2[thiz_0])
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
                          BinHeapCondition0[throw_11]
                          and 
                          (
                            head_12=(head_11)++((thiz_0)->(nextTemp_2)))
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_11])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            head_11=head_12)
                        )
                      )
                      and 
                      (
                        sibling_23=sibling_24)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition20[prevTemp_2])
                      )
                      and 
                      (
                        (
                          BinHeapCondition18[prevTemp_2]
                          and 
                          (
                            (
                              BinHeapCondition0[throw_11]
                              and 
                              (
                                nullDerefBool_14=true)
                            )
                            or 
                            (
                              (
                                not (
                                  BinHeapCondition0[throw_11])
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
                              BinHeapCondition18[prevTemp_2])
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
                          BinHeapCondition0[throw_11]
                          and 
                          (
                            sibling_24=(sibling_23)++((prevTemp_2)->(nextTemp_2)))
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_11])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            sibling_23=sibling_24)
                        )
                      )
                      and 
                      (
                        head_11=head_12)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition14[temp_2]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_11]
                          and 
                          (
                            nullDerefBool_15=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_11])
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
                          BinHeapCondition14[temp_2])
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
                      BinHeapCondition0[throw_11]
                      and 
                      (
                        parent_2=(parent_1)++((temp_2)->(nextTemp_2)))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_11])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        parent_1=parent_2)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition8[nextTemp_2,
                                       temp_2]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_11]
                          and 
                          (
                            nullDerefBool_16=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_11])
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
                          BinHeapCondition8[nextTemp_2,
                                           temp_2]
                        )
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
                      BinHeapCondition0[throw_11]
                      and 
                      (
                        sibling_25=(sibling_24)++((temp_2)->(nextTemp_2.child_1)))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_11])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        sibling_24=sibling_25)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition10[nextTemp_2]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_11]
                          and 
                          (
                            nullDerefBool_17=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_11])
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
                          BinHeapCondition10[nextTemp_2])
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
                      BinHeapCondition0[throw_11]
                      and 
                      (
                        child_2=(child_1)++((nextTemp_2)->(temp_2)))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_11])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        child_1=child_2)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition22[nextTemp_2]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_11]
                          and 
                          (
                            nullDerefBool_18=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_11])
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
                          BinHeapCondition22[nextTemp_2])
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
                      BinHeapCondition0[throw_11]
                      and 
                      (
                        degree_2=(degree_1)++((nextTemp_2)->(add[nextTemp_2.degree_1,1])))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_11])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        degree_1=degree_2)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_11]
                      and 
                      (
                        temp_3=nextTemp_2)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_11])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        temp_2=temp_3)
                    )
                  )
                )
              )
              and 
              (
                prevTemp_2=prevTemp_3)
            )
          )
          and 
          (
            (
              BinHeapCondition14[temp_3]
              and 
              (
                (
                  BinHeapCondition0[throw_11]
                  and 
                  (
                    nullDerefBool_19=true)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_11])
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
                  BinHeapCondition14[temp_3])
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
              BinHeapCondition0[throw_11]
              and 
              (
                nextTemp_3=temp_3.sibling_25)
            )
            or 
            (
              (
                not (
                  BinHeapCondition0[throw_11])
              )
              and 
              TruePred[]
              and 
              (
                nextTemp_2=nextTemp_3)
            )
          )
        )
        or 
        (
          TruePred[]
          and 
          (
            l3_nullDerefBool_0=l3_nullDerefBool_1)
          and 
          (
            l3_l0_nullDerefBool_0=l3_l0_nullDerefBool_1)
          and 
          (
            parent_1=parent_2)
          and 
          (
            nullDerefBool_11=nullDerefBool_19)
          and 
          (
            l3_lt_0=l3_lt_1)
          and 
          (
            l3_l0_result_0=l3_l0_result_2)
          and 
          (
            child_1=child_2)
          and 
          (
            nextTemp_2=nextTemp_3)
          and 
          (
            throw_7=throw_11)
          and 
          (
            degree_1=degree_2)
          and 
          (
            prevTemp_2=prevTemp_3)
          and 
          (
            sibling_23=sibling_25)
          and 
          (
            temp_2=temp_3)
          and 
          (
            l3_lte_0=l3_lte_2)
          and 
          (
            head_11=head_12)
          and 
          (
            lte_1=lte_2)
        )
      )
      and 
      (
        (
          BinHeapCondition28[nextTemp_3]
          and 
          (
            (
              BinHeapCondition6[nextTemp_3,
                               sibling_25,
                               temp_3]
              and 
              (
                (
                  BinHeapCondition0[throw_11]
                  and 
                  (
                    nullDerefBool_20=true)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_11])
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
                  BinHeapCondition6[nextTemp_3,
                                   sibling_25,
                                   temp_3]
                )
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
              BinHeapCondition26[degree_2,
                                nextTemp_3,
                                sibling_25,
                                temp_3]
              and 
              (
                (
                  BinHeapCondition0[throw_11]
                  and 
                  (
                    prevTemp_4=temp_3)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_11])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    prevTemp_3=prevTemp_4)
                )
              )
              and 
              (
                (
                  BinHeapCondition0[throw_11]
                  and 
                  (
                    temp_4=nextTemp_3)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_11])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    temp_3=temp_4)
                )
              )
              and 
              (
                parent_2=parent_3)
              and 
              (
                nullDerefBool_20=nullDerefBool_26)
              and 
              (
                l4_l0_nullDerefBool_0=l4_l0_nullDerefBool_1)
              and 
              (
                l4_nullDerefBool_0=l4_nullDerefBool_1)
              and 
              (
                l4_lte_0=l4_lte_2)
              and 
              (
                child_2=child_3)
              and 
              (
                l4_l0_result_0=l4_l0_result_2)
              and 
              (
                head_12=head_13)
              and 
              (
                lte_2=lte_3)
              and 
              (
                l4_lt_0=l4_lt_1)
              and 
              (
                throw_11=throw_15)
              and 
              (
                degree_2=degree_3)
              and 
              (
                sibling_25=sibling_27)
            )
            or 
            (
              (
                not (
                  BinHeapCondition26[degree_2,
                                    nextTemp_3,
                                    sibling_25,
                                    temp_3]
                )
              )
              and 
              TruePred[]
              and 
              (
                (
                  BinHeapCondition8[nextTemp_3,
                                   temp_3]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_11]
                      and 
                      (
                        nullDerefBool_21=true)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_11])
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
                      BinHeapCondition8[nextTemp_3,
                                       temp_3]
                    )
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
                  BinHeapCondition0[throw_11]
                  and 
                  Data_data_lte_0[temp_3.element_0,
                                 throw_11,
                                 throw_12,
                                 throw_13,
                                 throw_14,
                                 throw_15,
                                 lte_2,
                                 lte_3,
                                 nextTemp_3.element_0,
                                 l4_lt_0,
                                 l4_lt_1,
                                 l4_nullDerefBool_0,
                                 l4_nullDerefBool_1,
                                 l4_lte_0,
                                 l4_lte_1,
                                 l4_lte_2,
                                 l4_l0_result_0,
                                 l4_l0_result_1,
                                 l4_l0_result_2,
                                 l4_l0_nullDerefBool_0,
                                 l4_l0_nullDerefBool_1]
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_11])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    l4_lte_0=l4_lte_2)
                  and 
                  (
                    l4_l0_result_0=l4_l0_result_2)
                  and 
                  (
                    l4_l0_nullDerefBool_0=l4_l0_nullDerefBool_1)
                  and 
                  (
                    l4_nullDerefBool_0=l4_nullDerefBool_1)
                  and 
                  (
                    lte_2=lte_3)
                  and 
                  (
                    l4_lt_0=l4_lt_1)
                  and 
                  (
                    throw_11=throw_15)
                )
              )
              and 
              (
                (
                  BinHeapCondition24[lte_3]
                  and 
                  (
                    (
                      BinHeapCondition8[nextTemp_3,
                                       temp_3]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_15]
                          and 
                          (
                            nullDerefBool_22=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_15])
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
                          BinHeapCondition8[nextTemp_3,
                                           temp_3]
                        )
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
                      BinHeapCondition0[throw_15]
                      and 
                      (
                        sibling_26=(sibling_25)++((temp_3)->(nextTemp_3.sibling_25)))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_15])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        sibling_25=sibling_26)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition10[nextTemp_3]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_15]
                          and 
                          (
                            nullDerefBool_23=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_15])
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
                          BinHeapCondition10[nextTemp_3])
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
                      BinHeapCondition0[throw_15]
                      and 
                      (
                        parent_3=(parent_2)++((nextTemp_3)->(temp_3)))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_15])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        parent_2=parent_3)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition12[nextTemp_3,
                                        temp_3]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_15]
                          and 
                          (
                            nullDerefBool_24=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_15])
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
                          BinHeapCondition12[nextTemp_3,
                                            temp_3]
                        )
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
                      BinHeapCondition0[throw_15]
                      and 
                      (
                        sibling_27=(sibling_26)++((nextTemp_3)->(temp_3.child_2)))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_15])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        sibling_26=sibling_27)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition14[temp_3]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_15]
                          and 
                          (
                            nullDerefBool_25=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_15])
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
                          BinHeapCondition14[temp_3])
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
                      BinHeapCondition0[throw_15]
                      and 
                      (
                        child_3=(child_2)++((temp_3)->(nextTemp_3)))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_15])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        child_2=child_3)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition16[temp_3]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_15]
                          and 
                          (
                            nullDerefBool_26=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_15])
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
                          BinHeapCondition16[temp_3])
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
                      BinHeapCondition0[throw_15]
                      and 
                      (
                        degree_3=(degree_2)++((temp_3)->(add[temp_3.degree_2,1])))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_15])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        degree_2=degree_3)
                    )
                  )
                  and 
                  (
                    head_12=head_13)
                  and 
                  (
                    temp_3=temp_4)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition24[lte_3])
                  )
                  and 
                  (
                    (
                      BinHeapCondition20[prevTemp_3]
                      and 
                      (
                        (
                          BinHeapCondition2[thiz_0]
                          and 
                          (
                            (
                              BinHeapCondition0[throw_15]
                              and 
                              (
                                nullDerefBool_22=true)
                            )
                            or 
                            (
                              (
                                not (
                                  BinHeapCondition0[throw_15])
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
                              BinHeapCondition2[thiz_0])
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
                          BinHeapCondition0[throw_15]
                          and 
                          (
                            head_13=(head_12)++((thiz_0)->(nextTemp_3)))
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_15])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            head_12=head_13)
                        )
                      )
                      and 
                      (
                        sibling_25=sibling_26)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition20[prevTemp_3])
                      )
                      and 
                      (
                        (
                          BinHeapCondition18[prevTemp_3]
                          and 
                          (
                            (
                              BinHeapCondition0[throw_15]
                              and 
                              (
                                nullDerefBool_22=true)
                            )
                            or 
                            (
                              (
                                not (
                                  BinHeapCondition0[throw_15])
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
                              BinHeapCondition18[prevTemp_3])
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
                          BinHeapCondition0[throw_15]
                          and 
                          (
                            sibling_26=(sibling_25)++((prevTemp_3)->(nextTemp_3)))
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_15])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            sibling_25=sibling_26)
                        )
                      )
                      and 
                      (
                        head_12=head_13)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition14[temp_3]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_15]
                          and 
                          (
                            nullDerefBool_23=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_15])
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
                          BinHeapCondition14[temp_3])
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
                      BinHeapCondition0[throw_15]
                      and 
                      (
                        parent_3=(parent_2)++((temp_3)->(nextTemp_3)))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_15])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        parent_2=parent_3)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition8[nextTemp_3,
                                       temp_3]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_15]
                          and 
                          (
                            nullDerefBool_24=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_15])
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
                          BinHeapCondition8[nextTemp_3,
                                           temp_3]
                        )
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
                      BinHeapCondition0[throw_15]
                      and 
                      (
                        sibling_27=(sibling_26)++((temp_3)->(nextTemp_3.child_2)))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_15])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        sibling_26=sibling_27)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition10[nextTemp_3]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_15]
                          and 
                          (
                            nullDerefBool_25=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_15])
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
                          BinHeapCondition10[nextTemp_3])
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
                      BinHeapCondition0[throw_15]
                      and 
                      (
                        child_3=(child_2)++((nextTemp_3)->(temp_3)))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_15])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        child_2=child_3)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition22[nextTemp_3]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_15]
                          and 
                          (
                            nullDerefBool_26=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_15])
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
                          BinHeapCondition22[nextTemp_3])
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
                      BinHeapCondition0[throw_15]
                      and 
                      (
                        degree_3=(degree_2)++((nextTemp_3)->(add[nextTemp_3.degree_2,1])))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_15])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        degree_2=degree_3)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_15]
                      and 
                      (
                        temp_4=nextTemp_3)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_15])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        temp_3=temp_4)
                    )
                  )
                )
              )
              and 
              (
                prevTemp_3=prevTemp_4)
            )
          )
          and 
          (
            (
              BinHeapCondition14[temp_4]
              and 
              (
                (
                  BinHeapCondition0[throw_15]
                  and 
                  (
                    nullDerefBool_27=true)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_15])
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
                  BinHeapCondition14[temp_4])
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
              BinHeapCondition0[throw_15]
              and 
              (
                nextTemp_4=temp_4.sibling_27)
            )
            or 
            (
              (
                not (
                  BinHeapCondition0[throw_15])
              )
              and 
              TruePred[]
              and 
              (
                nextTemp_3=nextTemp_4)
            )
          )
        )
        or 
        (
          TruePred[]
          and 
          (
            parent_2=parent_3)
          and 
          (
            nullDerefBool_19=nullDerefBool_27)
          and 
          (
            l4_l0_nullDerefBool_0=l4_l0_nullDerefBool_1)
          and 
          (
            l4_nullDerefBool_0=l4_nullDerefBool_1)
          and 
          (
            l4_lte_0=l4_lte_2)
          and 
          (
            child_2=child_3)
          and 
          (
            nextTemp_3=nextTemp_4)
          and 
          (
            throw_11=throw_15)
          and 
          (
            degree_2=degree_3)
          and 
          (
            prevTemp_3=prevTemp_4)
          and 
          (
            l4_l0_result_0=l4_l0_result_2)
          and 
          (
            sibling_25=sibling_27)
          and 
          (
            temp_3=temp_4)
          and 
          (
            head_12=head_13)
          and 
          (
            lte_2=lte_3)
          and 
          (
            l4_lt_0=l4_lt_1)
        )
      )
      and 
      (
        (
          BinHeapCondition28[nextTemp_4]
          and 
          (
            (
              BinHeapCondition6[nextTemp_4,
                               sibling_27,
                               temp_4]
              and 
              (
                (
                  BinHeapCondition0[throw_15]
                  and 
                  (
                    nullDerefBool_28=true)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_15])
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
                  BinHeapCondition6[nextTemp_4,
                                   sibling_27,
                                   temp_4]
                )
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
              BinHeapCondition26[degree_3,
                                nextTemp_4,
                                sibling_27,
                                temp_4]
              and 
              (
                (
                  BinHeapCondition0[throw_15]
                  and 
                  (
                    prevTemp_5=temp_4)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_15])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    prevTemp_4=prevTemp_5)
                )
              )
              and 
              (
                (
                  BinHeapCondition0[throw_15]
                  and 
                  (
                    temp_5=nextTemp_4)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_15])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    temp_4=temp_5)
                )
              )
              and 
              (
                l5_l0_result_0=l5_l0_result_2)
              and 
              (
                parent_3=parent_4)
              and 
              (
                nullDerefBool_28=nullDerefBool_34)
              and 
              (
                l5_lt_0=l5_lt_1)
              and 
              (
                child_3=child_4)
              and 
              (
                l5_l0_nullDerefBool_0=l5_l0_nullDerefBool_1)
              and 
              (
                l5_nullDerefBool_0=l5_nullDerefBool_1)
              and 
              (
                l5_lte_0=l5_lte_2)
              and 
              (
                head_13=head_14)
              and 
              (
                lte_3=lte_4)
              and 
              (
                throw_15=throw_19)
              and 
              (
                degree_3=degree_4)
              and 
              (
                sibling_27=sibling_29)
            )
            or 
            (
              (
                not (
                  BinHeapCondition26[degree_3,
                                    nextTemp_4,
                                    sibling_27,
                                    temp_4]
                )
              )
              and 
              TruePred[]
              and 
              (
                (
                  BinHeapCondition8[nextTemp_4,
                                   temp_4]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_15]
                      and 
                      (
                        nullDerefBool_29=true)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_15])
                      )
                      and 
                      TruePred[]
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
                      BinHeapCondition8[nextTemp_4,
                                       temp_4]
                    )
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
                  BinHeapCondition0[throw_15]
                  and 
                  Data_data_lte_0[temp_4.element_0,
                                 throw_15,
                                 throw_16,
                                 throw_17,
                                 throw_18,
                                 throw_19,
                                 lte_3,
                                 lte_4,
                                 nextTemp_4.element_0,
                                 l5_lt_0,
                                 l5_lt_1,
                                 l5_nullDerefBool_0,
                                 l5_nullDerefBool_1,
                                 l5_lte_0,
                                 l5_lte_1,
                                 l5_lte_2,
                                 l5_l0_result_0,
                                 l5_l0_result_1,
                                 l5_l0_result_2,
                                 l5_l0_nullDerefBool_0,
                                 l5_l0_nullDerefBool_1]
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_15])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    l5_l0_result_0=l5_l0_result_2)
                  and 
                  (
                    l5_l0_nullDerefBool_0=l5_l0_nullDerefBool_1)
                  and 
                  (
                    l5_nullDerefBool_0=l5_nullDerefBool_1)
                  and 
                  (
                    l5_lte_0=l5_lte_2)
                  and 
                  (
                    lte_3=lte_4)
                  and 
                  (
                    l5_lt_0=l5_lt_1)
                  and 
                  (
                    throw_15=throw_19)
                )
              )
              and 
              (
                (
                  BinHeapCondition24[lte_4]
                  and 
                  (
                    (
                      BinHeapCondition8[nextTemp_4,
                                       temp_4]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_19]
                          and 
                          (
                            nullDerefBool_30=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_19])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_29=nullDerefBool_30)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition8[nextTemp_4,
                                           temp_4]
                        )
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
                      BinHeapCondition0[throw_19]
                      and 
                      (
                        sibling_28=(sibling_27)++((temp_4)->(nextTemp_4.sibling_27)))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_19])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        sibling_27=sibling_28)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition10[nextTemp_4]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_19]
                          and 
                          (
                            nullDerefBool_31=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_19])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_30=nullDerefBool_31)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition10[nextTemp_4])
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
                      BinHeapCondition0[throw_19]
                      and 
                      (
                        parent_4=(parent_3)++((nextTemp_4)->(temp_4)))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_19])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        parent_3=parent_4)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition12[nextTemp_4,
                                        temp_4]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_19]
                          and 
                          (
                            nullDerefBool_32=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_19])
                          )
                          and 
                          TruePred[]
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
                          BinHeapCondition12[nextTemp_4,
                                            temp_4]
                        )
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
                      BinHeapCondition0[throw_19]
                      and 
                      (
                        sibling_29=(sibling_28)++((nextTemp_4)->(temp_4.child_3)))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_19])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        sibling_28=sibling_29)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition14[temp_4]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_19]
                          and 
                          (
                            nullDerefBool_33=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_19])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_32=nullDerefBool_33)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition14[temp_4])
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
                      BinHeapCondition0[throw_19]
                      and 
                      (
                        child_4=(child_3)++((temp_4)->(nextTemp_4)))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_19])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        child_3=child_4)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition16[temp_4]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_19]
                          and 
                          (
                            nullDerefBool_34=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_19])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_33=nullDerefBool_34)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition16[temp_4])
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
                    (
                      BinHeapCondition0[throw_19]
                      and 
                      (
                        degree_4=(degree_3)++((temp_4)->(add[temp_4.degree_3,1])))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_19])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        degree_3=degree_4)
                    )
                  )
                  and 
                  (
                    head_13=head_14)
                  and 
                  (
                    temp_4=temp_5)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition24[lte_4])
                  )
                  and 
                  (
                    (
                      BinHeapCondition20[prevTemp_4]
                      and 
                      (
                        (
                          BinHeapCondition2[thiz_0]
                          and 
                          (
                            (
                              BinHeapCondition0[throw_19]
                              and 
                              (
                                nullDerefBool_30=true)
                            )
                            or 
                            (
                              (
                                not (
                                  BinHeapCondition0[throw_19])
                              )
                              and 
                              TruePred[]
                              and 
                              (
                                nullDerefBool_29=nullDerefBool_30)
                            )
                          )
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition2[thiz_0])
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
                          BinHeapCondition0[throw_19]
                          and 
                          (
                            head_14=(head_13)++((thiz_0)->(nextTemp_4)))
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_19])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            head_13=head_14)
                        )
                      )
                      and 
                      (
                        sibling_27=sibling_28)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition20[prevTemp_4])
                      )
                      and 
                      (
                        (
                          BinHeapCondition18[prevTemp_4]
                          and 
                          (
                            (
                              BinHeapCondition0[throw_19]
                              and 
                              (
                                nullDerefBool_30=true)
                            )
                            or 
                            (
                              (
                                not (
                                  BinHeapCondition0[throw_19])
                              )
                              and 
                              TruePred[]
                              and 
                              (
                                nullDerefBool_29=nullDerefBool_30)
                            )
                          )
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition18[prevTemp_4])
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
                          BinHeapCondition0[throw_19]
                          and 
                          (
                            sibling_28=(sibling_27)++((prevTemp_4)->(nextTemp_4)))
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_19])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            sibling_27=sibling_28)
                        )
                      )
                      and 
                      (
                        head_13=head_14)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition14[temp_4]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_19]
                          and 
                          (
                            nullDerefBool_31=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_19])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_30=nullDerefBool_31)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition14[temp_4])
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
                      BinHeapCondition0[throw_19]
                      and 
                      (
                        parent_4=(parent_3)++((temp_4)->(nextTemp_4)))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_19])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        parent_3=parent_4)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition8[nextTemp_4,
                                       temp_4]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_19]
                          and 
                          (
                            nullDerefBool_32=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_19])
                          )
                          and 
                          TruePred[]
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
                          BinHeapCondition8[nextTemp_4,
                                           temp_4]
                        )
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
                      BinHeapCondition0[throw_19]
                      and 
                      (
                        sibling_29=(sibling_28)++((temp_4)->(nextTemp_4.child_3)))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_19])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        sibling_28=sibling_29)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition10[nextTemp_4]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_19]
                          and 
                          (
                            nullDerefBool_33=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_19])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_32=nullDerefBool_33)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition10[nextTemp_4])
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
                      BinHeapCondition0[throw_19]
                      and 
                      (
                        child_4=(child_3)++((nextTemp_4)->(temp_4)))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_19])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        child_3=child_4)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition22[nextTemp_4]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_19]
                          and 
                          (
                            nullDerefBool_34=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_19])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_33=nullDerefBool_34)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition22[nextTemp_4])
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
                    (
                      BinHeapCondition0[throw_19]
                      and 
                      (
                        degree_4=(degree_3)++((nextTemp_4)->(add[nextTemp_4.degree_3,1])))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_19])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        degree_3=degree_4)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_19]
                      and 
                      (
                        temp_5=nextTemp_4)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_19])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        temp_4=temp_5)
                    )
                  )
                )
              )
              and 
              (
                prevTemp_4=prevTemp_5)
            )
          )
          and 
          (
            (
              BinHeapCondition14[temp_5]
              and 
              (
                (
                  BinHeapCondition0[throw_19]
                  and 
                  (
                    nullDerefBool_35=true)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_19])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_34=nullDerefBool_35)
                )
              )
            )
            or 
            (
              (
                not (
                  BinHeapCondition14[temp_5])
              )
              and 
              TruePred[]
              and 
              (
                nullDerefBool_34=nullDerefBool_35)
            )
          )
          and 
          (
            (
              BinHeapCondition0[throw_19]
              and 
              (
                nextTemp_5=temp_5.sibling_29)
            )
            or 
            (
              (
                not (
                  BinHeapCondition0[throw_19])
              )
              and 
              TruePred[]
              and 
              (
                nextTemp_4=nextTemp_5)
            )
          )
        )
        or 
        (
          TruePred[]
          and 
          (
            l5_l0_result_0=l5_l0_result_2)
          and 
          (
            parent_3=parent_4)
          and 
          (
            nullDerefBool_27=nullDerefBool_35)
          and 
          (
            l5_lt_0=l5_lt_1)
          and 
          (
            child_3=child_4)
          and 
          (
            nextTemp_4=nextTemp_5)
          and 
          (
            throw_15=throw_19)
          and 
          (
            degree_3=degree_4)
          and 
          (
            prevTemp_4=prevTemp_5)
          and 
          (
            l5_l0_nullDerefBool_0=l5_l0_nullDerefBool_1)
          and 
          (
            sibling_27=sibling_29)
          and 
          (
            l5_nullDerefBool_0=l5_nullDerefBool_1)
          and 
          (
            temp_4=temp_5)
          and 
          (
            l5_lte_0=l5_lte_2)
          and 
          (
            head_13=head_14)
          and 
          (
            lte_3=lte_4)
        )
      )
      and 
      (
        (
          BinHeapCondition28[nextTemp_5]
          and 
          (
            (
              BinHeapCondition6[nextTemp_5,
                               sibling_29,
                               temp_5]
              and 
              (
                (
                  BinHeapCondition0[throw_19]
                  and 
                  (
                    nullDerefBool_36=true)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_19])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_35=nullDerefBool_36)
                )
              )
            )
            or 
            (
              (
                not (
                  BinHeapCondition6[nextTemp_5,
                                   sibling_29,
                                   temp_5]
                )
              )
              and 
              TruePred[]
              and 
              (
                nullDerefBool_35=nullDerefBool_36)
            )
          )
          and 
          (
            (
              BinHeapCondition26[degree_4,
                                nextTemp_5,
                                sibling_29,
                                temp_5]
              and 
              (
                (
                  BinHeapCondition0[throw_19]
                  and 
                  (
                    prevTemp_6=temp_5)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_19])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    prevTemp_5=prevTemp_6)
                )
              )
              and 
              (
                (
                  BinHeapCondition0[throw_19]
                  and 
                  (
                    temp_6=nextTemp_5)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_19])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    temp_5=temp_6)
                )
              )
              and 
              (
                l6_l0_result_0=l6_l0_result_2)
              and 
              (
                parent_4=parent_5)
              and 
              (
                nullDerefBool_36=nullDerefBool_42)
              and 
              (
                child_4=child_5)
              and 
              (
                l6_lt_0=l6_lt_1)
              and 
              (
                l6_l0_nullDerefBool_0=l6_l0_nullDerefBool_1)
              and 
              (
                l6_nullDerefBool_0=l6_nullDerefBool_1)
              and 
              (
                head_14=head_15)
              and 
              (
                lte_4=lte_5)
              and 
              (
                l6_lte_0=l6_lte_2)
              and 
              (
                throw_19=throw_23)
              and 
              (
                degree_4=degree_5)
              and 
              (
                sibling_29=sibling_31)
            )
            or 
            (
              (
                not (
                  BinHeapCondition26[degree_4,
                                    nextTemp_5,
                                    sibling_29,
                                    temp_5]
                )
              )
              and 
              TruePred[]
              and 
              (
                (
                  BinHeapCondition8[nextTemp_5,
                                   temp_5]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_19]
                      and 
                      (
                        nullDerefBool_37=true)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_19])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_36=nullDerefBool_37)
                    )
                  )
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition8[nextTemp_5,
                                       temp_5]
                    )
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_36=nullDerefBool_37)
                )
              )
              and 
              (
                (
                  BinHeapCondition0[throw_19]
                  and 
                  Data_data_lte_0[temp_5.element_0,
                                 throw_19,
                                 throw_20,
                                 throw_21,
                                 throw_22,
                                 throw_23,
                                 lte_4,
                                 lte_5,
                                 nextTemp_5.element_0,
                                 l6_lt_0,
                                 l6_lt_1,
                                 l6_nullDerefBool_0,
                                 l6_nullDerefBool_1,
                                 l6_lte_0,
                                 l6_lte_1,
                                 l6_lte_2,
                                 l6_l0_result_0,
                                 l6_l0_result_1,
                                 l6_l0_result_2,
                                 l6_l0_nullDerefBool_0,
                                 l6_l0_nullDerefBool_1]
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_19])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    l6_l0_result_0=l6_l0_result_2)
                  and 
                  (
                    l6_l0_nullDerefBool_0=l6_l0_nullDerefBool_1)
                  and 
                  (
                    l6_lt_0=l6_lt_1)
                  and 
                  (
                    l6_nullDerefBool_0=l6_nullDerefBool_1)
                  and 
                  (
                    lte_4=lte_5)
                  and 
                  (
                    l6_lte_0=l6_lte_2)
                  and 
                  (
                    throw_19=throw_23)
                )
              )
              and 
              (
                (
                  BinHeapCondition24[lte_5]
                  and 
                  (
                    (
                      BinHeapCondition8[nextTemp_5,
                                       temp_5]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_23]
                          and 
                          (
                            nullDerefBool_38=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_23])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_37=nullDerefBool_38)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition8[nextTemp_5,
                                           temp_5]
                        )
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_37=nullDerefBool_38)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_23]
                      and 
                      (
                        sibling_30=(sibling_29)++((temp_5)->(nextTemp_5.sibling_29)))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_23])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        sibling_29=sibling_30)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition10[nextTemp_5]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_23]
                          and 
                          (
                            nullDerefBool_39=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_23])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_38=nullDerefBool_39)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition10[nextTemp_5])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_38=nullDerefBool_39)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_23]
                      and 
                      (
                        parent_5=(parent_4)++((nextTemp_5)->(temp_5)))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_23])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        parent_4=parent_5)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition12[nextTemp_5,
                                        temp_5]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_23]
                          and 
                          (
                            nullDerefBool_40=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_23])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_39=nullDerefBool_40)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition12[nextTemp_5,
                                            temp_5]
                        )
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_39=nullDerefBool_40)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_23]
                      and 
                      (
                        sibling_31=(sibling_30)++((nextTemp_5)->(temp_5.child_4)))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_23])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        sibling_30=sibling_31)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition14[temp_5]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_23]
                          and 
                          (
                            nullDerefBool_41=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_23])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_40=nullDerefBool_41)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition14[temp_5])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_40=nullDerefBool_41)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_23]
                      and 
                      (
                        child_5=(child_4)++((temp_5)->(nextTemp_5)))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_23])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        child_4=child_5)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition16[temp_5]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_23]
                          and 
                          (
                            nullDerefBool_42=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_23])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_41=nullDerefBool_42)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition16[temp_5])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_41=nullDerefBool_42)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_23]
                      and 
                      (
                        degree_5=(degree_4)++((temp_5)->(add[temp_5.degree_4,1])))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_23])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        degree_4=degree_5)
                    )
                  )
                  and 
                  (
                    head_14=head_15)
                  and 
                  (
                    temp_5=temp_6)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition24[lte_5])
                  )
                  and 
                  (
                    (
                      BinHeapCondition20[prevTemp_5]
                      and 
                      (
                        (
                          BinHeapCondition2[thiz_0]
                          and 
                          (
                            (
                              BinHeapCondition0[throw_23]
                              and 
                              (
                                nullDerefBool_38=true)
                            )
                            or 
                            (
                              (
                                not (
                                  BinHeapCondition0[throw_23])
                              )
                              and 
                              TruePred[]
                              and 
                              (
                                nullDerefBool_37=nullDerefBool_38)
                            )
                          )
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition2[thiz_0])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_37=nullDerefBool_38)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition0[throw_23]
                          and 
                          (
                            head_15=(head_14)++((thiz_0)->(nextTemp_5)))
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_23])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            head_14=head_15)
                        )
                      )
                      and 
                      (
                        sibling_29=sibling_30)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition20[prevTemp_5])
                      )
                      and 
                      (
                        (
                          BinHeapCondition18[prevTemp_5]
                          and 
                          (
                            (
                              BinHeapCondition0[throw_23]
                              and 
                              (
                                nullDerefBool_38=true)
                            )
                            or 
                            (
                              (
                                not (
                                  BinHeapCondition0[throw_23])
                              )
                              and 
                              TruePred[]
                              and 
                              (
                                nullDerefBool_37=nullDerefBool_38)
                            )
                          )
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition18[prevTemp_5])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_37=nullDerefBool_38)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition0[throw_23]
                          and 
                          (
                            sibling_30=(sibling_29)++((prevTemp_5)->(nextTemp_5)))
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_23])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            sibling_29=sibling_30)
                        )
                      )
                      and 
                      (
                        head_14=head_15)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition14[temp_5]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_23]
                          and 
                          (
                            nullDerefBool_39=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_23])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_38=nullDerefBool_39)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition14[temp_5])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_38=nullDerefBool_39)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_23]
                      and 
                      (
                        parent_5=(parent_4)++((temp_5)->(nextTemp_5)))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_23])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        parent_4=parent_5)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition8[nextTemp_5,
                                       temp_5]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_23]
                          and 
                          (
                            nullDerefBool_40=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_23])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_39=nullDerefBool_40)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition8[nextTemp_5,
                                           temp_5]
                        )
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_39=nullDerefBool_40)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_23]
                      and 
                      (
                        sibling_31=(sibling_30)++((temp_5)->(nextTemp_5.child_4)))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_23])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        sibling_30=sibling_31)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition10[nextTemp_5]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_23]
                          and 
                          (
                            nullDerefBool_41=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_23])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_40=nullDerefBool_41)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition10[nextTemp_5])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_40=nullDerefBool_41)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_23]
                      and 
                      (
                        child_5=(child_4)++((nextTemp_5)->(temp_5)))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_23])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        child_4=child_5)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition22[nextTemp_5]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_23]
                          and 
                          (
                            nullDerefBool_42=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_23])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_41=nullDerefBool_42)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition22[nextTemp_5])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_41=nullDerefBool_42)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_23]
                      and 
                      (
                        degree_5=(degree_4)++((nextTemp_5)->(add[nextTemp_5.degree_4,1])))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_23])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        degree_4=degree_5)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_23]
                      and 
                      (
                        temp_6=nextTemp_5)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_23])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        temp_5=temp_6)
                    )
                  )
                )
              )
              and 
              (
                prevTemp_5=prevTemp_6)
            )
          )
          and 
          (
            (
              BinHeapCondition14[temp_6]
              and 
              (
                (
                  BinHeapCondition0[throw_23]
                  and 
                  (
                    nullDerefBool_43=true)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_23])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_42=nullDerefBool_43)
                )
              )
            )
            or 
            (
              (
                not (
                  BinHeapCondition14[temp_6])
              )
              and 
              TruePred[]
              and 
              (
                nullDerefBool_42=nullDerefBool_43)
            )
          )
          and 
          (
            (
              BinHeapCondition0[throw_23]
              and 
              (
                nextTemp_6=temp_6.sibling_31)
            )
            or 
            (
              (
                not (
                  BinHeapCondition0[throw_23])
              )
              and 
              TruePred[]
              and 
              (
                nextTemp_5=nextTemp_6)
            )
          )
        )
        or 
        (
          TruePred[]
          and 
          (
            l6_l0_result_0=l6_l0_result_2)
          and 
          (
            parent_4=parent_5)
          and 
          (
            nullDerefBool_35=nullDerefBool_43)
          and 
          (
            child_4=child_5)
          and 
          (
            nextTemp_5=nextTemp_6)
          and 
          (
            throw_19=throw_23)
          and 
          (
            degree_4=degree_5)
          and 
          (
            prevTemp_5=prevTemp_6)
          and 
          (
            sibling_29=sibling_31)
          and 
          (
            l6_lt_0=l6_lt_1)
          and 
          (
            l6_l0_nullDerefBool_0=l6_l0_nullDerefBool_1)
          and 
          (
            temp_5=temp_6)
          and 
          (
            l6_nullDerefBool_0=l6_nullDerefBool_1)
          and 
          (
            head_14=head_15)
          and 
          (
            lte_4=lte_5)
          and 
          (
            l6_lte_0=l6_lte_2)
        )
      )
      and 
      (
        (
          BinHeapCondition28[nextTemp_6]
          and 
          (
            (
              BinHeapCondition6[nextTemp_6,
                               sibling_31,
                               temp_6]
              and 
              (
                (
                  BinHeapCondition0[throw_23]
                  and 
                  (
                    nullDerefBool_44=true)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_23])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_43=nullDerefBool_44)
                )
              )
            )
            or 
            (
              (
                not (
                  BinHeapCondition6[nextTemp_6,
                                   sibling_31,
                                   temp_6]
                )
              )
              and 
              TruePred[]
              and 
              (
                nullDerefBool_43=nullDerefBool_44)
            )
          )
          and 
          (
            (
              BinHeapCondition26[degree_5,
                                nextTemp_6,
                                sibling_31,
                                temp_6]
              and 
              (
                (
                  BinHeapCondition0[throw_23]
                  and 
                  (
                    prevTemp_7=temp_6)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_23])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    prevTemp_6=prevTemp_7)
                )
              )
              and 
              (
                (
                  BinHeapCondition0[throw_23]
                  and 
                  (
                    temp_7=nextTemp_6)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_23])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    temp_6=temp_7)
                )
              )
              and 
              (
                l7_lt_0=l7_lt_1)
              and 
              (
                parent_5=parent_6)
              and 
              (
                nullDerefBool_44=nullDerefBool_50)
              and 
              (
                l7_l0_nullDerefBool_0=l7_l0_nullDerefBool_1)
              and 
              (
                child_5=child_6)
              and 
              (
                l7_nullDerefBool_0=l7_nullDerefBool_1)
              and 
              (
                head_15=head_16)
              and 
              (
                lte_5=lte_6)
              and 
              (
                l7_lte_0=l7_lte_2)
              and 
              (
                l7_l0_result_0=l7_l0_result_2)
              and 
              (
                throw_23=throw_27)
              and 
              (
                degree_5=degree_6)
              and 
              (
                sibling_31=sibling_33)
            )
            or 
            (
              (
                not (
                  BinHeapCondition26[degree_5,
                                    nextTemp_6,
                                    sibling_31,
                                    temp_6]
                )
              )
              and 
              TruePred[]
              and 
              (
                (
                  BinHeapCondition8[nextTemp_6,
                                   temp_6]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_23]
                      and 
                      (
                        nullDerefBool_45=true)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_23])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_44=nullDerefBool_45)
                    )
                  )
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition8[nextTemp_6,
                                       temp_6]
                    )
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_44=nullDerefBool_45)
                )
              )
              and 
              (
                (
                  BinHeapCondition0[throw_23]
                  and 
                  Data_data_lte_0[temp_6.element_0,
                                 throw_23,
                                 throw_24,
                                 throw_25,
                                 throw_26,
                                 throw_27,
                                 lte_5,
                                 lte_6,
                                 nextTemp_6.element_0,
                                 l7_lt_0,
                                 l7_lt_1,
                                 l7_nullDerefBool_0,
                                 l7_nullDerefBool_1,
                                 l7_lte_0,
                                 l7_lte_1,
                                 l7_lte_2,
                                 l7_l0_result_0,
                                 l7_l0_result_1,
                                 l7_l0_result_2,
                                 l7_l0_nullDerefBool_0,
                                 l7_l0_nullDerefBool_1]
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_23])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    l7_lt_0=l7_lt_1)
                  and 
                  (
                    l7_nullDerefBool_0=l7_nullDerefBool_1)
                  and 
                  (
                    l7_l0_nullDerefBool_0=l7_l0_nullDerefBool_1)
                  and 
                  (
                    lte_5=lte_6)
                  and 
                  (
                    l7_lte_0=l7_lte_2)
                  and 
                  (
                    l7_l0_result_0=l7_l0_result_2)
                  and 
                  (
                    throw_23=throw_27)
                )
              )
              and 
              (
                (
                  BinHeapCondition24[lte_6]
                  and 
                  (
                    (
                      BinHeapCondition8[nextTemp_6,
                                       temp_6]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_27]
                          and 
                          (
                            nullDerefBool_46=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_27])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_45=nullDerefBool_46)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition8[nextTemp_6,
                                           temp_6]
                        )
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_45=nullDerefBool_46)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_27]
                      and 
                      (
                        sibling_32=(sibling_31)++((temp_6)->(nextTemp_6.sibling_31)))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_27])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        sibling_31=sibling_32)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition10[nextTemp_6]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_27]
                          and 
                          (
                            nullDerefBool_47=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_27])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_46=nullDerefBool_47)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition10[nextTemp_6])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_46=nullDerefBool_47)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_27]
                      and 
                      (
                        parent_6=(parent_5)++((nextTemp_6)->(temp_6)))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_27])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        parent_5=parent_6)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition12[nextTemp_6,
                                        temp_6]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_27]
                          and 
                          (
                            nullDerefBool_48=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_27])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_47=nullDerefBool_48)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition12[nextTemp_6,
                                            temp_6]
                        )
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_47=nullDerefBool_48)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_27]
                      and 
                      (
                        sibling_33=(sibling_32)++((nextTemp_6)->(temp_6.child_5)))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_27])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        sibling_32=sibling_33)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition14[temp_6]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_27]
                          and 
                          (
                            nullDerefBool_49=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_27])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_48=nullDerefBool_49)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition14[temp_6])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_48=nullDerefBool_49)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_27]
                      and 
                      (
                        child_6=(child_5)++((temp_6)->(nextTemp_6)))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_27])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        child_5=child_6)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition16[temp_6]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_27]
                          and 
                          (
                            nullDerefBool_50=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_27])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_49=nullDerefBool_50)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition16[temp_6])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_49=nullDerefBool_50)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_27]
                      and 
                      (
                        degree_6=(degree_5)++((temp_6)->(add[temp_6.degree_5,1])))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_27])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        degree_5=degree_6)
                    )
                  )
                  and 
                  (
                    head_15=head_16)
                  and 
                  (
                    temp_6=temp_7)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition24[lte_6])
                  )
                  and 
                  (
                    (
                      BinHeapCondition20[prevTemp_6]
                      and 
                      (
                        (
                          BinHeapCondition2[thiz_0]
                          and 
                          (
                            (
                              BinHeapCondition0[throw_27]
                              and 
                              (
                                nullDerefBool_46=true)
                            )
                            or 
                            (
                              (
                                not (
                                  BinHeapCondition0[throw_27])
                              )
                              and 
                              TruePred[]
                              and 
                              (
                                nullDerefBool_45=nullDerefBool_46)
                            )
                          )
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition2[thiz_0])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_45=nullDerefBool_46)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition0[throw_27]
                          and 
                          (
                            head_16=(head_15)++((thiz_0)->(nextTemp_6)))
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_27])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            head_15=head_16)
                        )
                      )
                      and 
                      (
                        sibling_31=sibling_32)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition20[prevTemp_6])
                      )
                      and 
                      (
                        (
                          BinHeapCondition18[prevTemp_6]
                          and 
                          (
                            (
                              BinHeapCondition0[throw_27]
                              and 
                              (
                                nullDerefBool_46=true)
                            )
                            or 
                            (
                              (
                                not (
                                  BinHeapCondition0[throw_27])
                              )
                              and 
                              TruePred[]
                              and 
                              (
                                nullDerefBool_45=nullDerefBool_46)
                            )
                          )
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition18[prevTemp_6])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_45=nullDerefBool_46)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition0[throw_27]
                          and 
                          (
                            sibling_32=(sibling_31)++((prevTemp_6)->(nextTemp_6)))
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_27])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            sibling_31=sibling_32)
                        )
                      )
                      and 
                      (
                        head_15=head_16)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition14[temp_6]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_27]
                          and 
                          (
                            nullDerefBool_47=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_27])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_46=nullDerefBool_47)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition14[temp_6])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_46=nullDerefBool_47)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_27]
                      and 
                      (
                        parent_6=(parent_5)++((temp_6)->(nextTemp_6)))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_27])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        parent_5=parent_6)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition8[nextTemp_6,
                                       temp_6]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_27]
                          and 
                          (
                            nullDerefBool_48=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_27])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_47=nullDerefBool_48)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition8[nextTemp_6,
                                           temp_6]
                        )
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_47=nullDerefBool_48)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_27]
                      and 
                      (
                        sibling_33=(sibling_32)++((temp_6)->(nextTemp_6.child_5)))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_27])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        sibling_32=sibling_33)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition10[nextTemp_6]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_27]
                          and 
                          (
                            nullDerefBool_49=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_27])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_48=nullDerefBool_49)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition10[nextTemp_6])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_48=nullDerefBool_49)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_27]
                      and 
                      (
                        child_6=(child_5)++((nextTemp_6)->(temp_6)))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_27])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        child_5=child_6)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition22[nextTemp_6]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_27]
                          and 
                          (
                            nullDerefBool_50=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_27])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_49=nullDerefBool_50)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition22[nextTemp_6])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_49=nullDerefBool_50)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_27]
                      and 
                      (
                        degree_6=(degree_5)++((nextTemp_6)->(add[nextTemp_6.degree_5,1])))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_27])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        degree_5=degree_6)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_27]
                      and 
                      (
                        temp_7=nextTemp_6)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_27])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        temp_6=temp_7)
                    )
                  )
                )
              )
              and 
              (
                prevTemp_6=prevTemp_7)
            )
          )
          and 
          (
            (
              BinHeapCondition14[temp_7]
              and 
              (
                (
                  BinHeapCondition0[throw_27]
                  and 
                  (
                    nullDerefBool_51=true)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_27])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_50=nullDerefBool_51)
                )
              )
            )
            or 
            (
              (
                not (
                  BinHeapCondition14[temp_7])
              )
              and 
              TruePred[]
              and 
              (
                nullDerefBool_50=nullDerefBool_51)
            )
          )
          and 
          (
            (
              BinHeapCondition0[throw_27]
              and 
              (
                nextTemp_7=temp_7.sibling_33)
            )
            or 
            (
              (
                not (
                  BinHeapCondition0[throw_27])
              )
              and 
              TruePred[]
              and 
              (
                nextTemp_6=nextTemp_7)
            )
          )
        )
        or 
        (
          TruePred[]
          and 
          (
            l7_lt_0=l7_lt_1)
          and 
          (
            parent_5=parent_6)
          and 
          (
            nullDerefBool_43=nullDerefBool_51)
          and 
          (
            l7_l0_nullDerefBool_0=l7_l0_nullDerefBool_1)
          and 
          (
            child_5=child_6)
          and 
          (
            nextTemp_6=nextTemp_7)
          and 
          (
            throw_23=throw_27)
          and 
          (
            degree_5=degree_6)
          and 
          (
            prevTemp_6=prevTemp_7)
          and 
          (
            l7_nullDerefBool_0=l7_nullDerefBool_1)
          and 
          (
            sibling_31=sibling_33)
          and 
          (
            temp_6=temp_7)
          and 
          (
            head_15=head_16)
          and 
          (
            lte_5=lte_6)
          and 
          (
            l7_lte_0=l7_lte_2)
          and 
          (
            l7_l0_result_0=l7_l0_result_2)
        )
      )
      and 
      (
        (
          BinHeapCondition28[nextTemp_7]
          and 
          (
            (
              BinHeapCondition6[nextTemp_7,
                               sibling_33,
                               temp_7]
              and 
              (
                (
                  BinHeapCondition0[throw_27]
                  and 
                  (
                    nullDerefBool_52=true)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_27])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_51=nullDerefBool_52)
                )
              )
            )
            or 
            (
              (
                not (
                  BinHeapCondition6[nextTemp_7,
                                   sibling_33,
                                   temp_7]
                )
              )
              and 
              TruePred[]
              and 
              (
                nullDerefBool_51=nullDerefBool_52)
            )
          )
          and 
          (
            (
              BinHeapCondition26[degree_6,
                                nextTemp_7,
                                sibling_33,
                                temp_7]
              and 
              (
                (
                  BinHeapCondition0[throw_27]
                  and 
                  (
                    prevTemp_8=temp_7)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_27])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    prevTemp_7=prevTemp_8)
                )
              )
              and 
              (
                (
                  BinHeapCondition0[throw_27]
                  and 
                  (
                    temp_8=nextTemp_7)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_27])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    temp_7=temp_8)
                )
              )
              and 
              (
                l8_nullDerefBool_0=l8_nullDerefBool_1)
              and 
              (
                l8_lte_0=l8_lte_2)
              and 
              (
                parent_6=parent_7)
              and 
              (
                nullDerefBool_52=nullDerefBool_58)
              and 
              (
                l8_lt_0=l8_lt_1)
              and 
              (
                child_6=child_7)
              and 
              (
                l8_l0_nullDerefBool_0=l8_l0_nullDerefBool_1)
              and 
              (
                head_16=head_17)
              and 
              (
                lte_6=lte_7)
              and 
              (
                l8_l0_result_0=l8_l0_result_2)
              and 
              (
                throw_27=throw_31)
              and 
              (
                degree_6=degree_7)
              and 
              (
                sibling_33=sibling_35)
            )
            or 
            (
              (
                not (
                  BinHeapCondition26[degree_6,
                                    nextTemp_7,
                                    sibling_33,
                                    temp_7]
                )
              )
              and 
              TruePred[]
              and 
              (
                (
                  BinHeapCondition8[nextTemp_7,
                                   temp_7]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_27]
                      and 
                      (
                        nullDerefBool_53=true)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_27])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_52=nullDerefBool_53)
                    )
                  )
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition8[nextTemp_7,
                                       temp_7]
                    )
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_52=nullDerefBool_53)
                )
              )
              and 
              (
                (
                  BinHeapCondition0[throw_27]
                  and 
                  Data_data_lte_0[temp_7.element_0,
                                 throw_27,
                                 throw_28,
                                 throw_29,
                                 throw_30,
                                 throw_31,
                                 lte_6,
                                 lte_7,
                                 nextTemp_7.element_0,
                                 l8_lt_0,
                                 l8_lt_1,
                                 l8_nullDerefBool_0,
                                 l8_nullDerefBool_1,
                                 l8_lte_0,
                                 l8_lte_1,
                                 l8_lte_2,
                                 l8_l0_result_0,
                                 l8_l0_result_1,
                                 l8_l0_result_2,
                                 l8_l0_nullDerefBool_0,
                                 l8_l0_nullDerefBool_1]
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_27])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    l8_l0_nullDerefBool_0=l8_l0_nullDerefBool_1)
                  and 
                  (
                    l8_nullDerefBool_0=l8_nullDerefBool_1)
                  and 
                  (
                    l8_lte_0=l8_lte_2)
                  and 
                  (
                    l8_lt_0=l8_lt_1)
                  and 
                  (
                    lte_6=lte_7)
                  and 
                  (
                    l8_l0_result_0=l8_l0_result_2)
                  and 
                  (
                    throw_27=throw_31)
                )
              )
              and 
              (
                (
                  BinHeapCondition24[lte_7]
                  and 
                  (
                    (
                      BinHeapCondition8[nextTemp_7,
                                       temp_7]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_31]
                          and 
                          (
                            nullDerefBool_54=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_31])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_53=nullDerefBool_54)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition8[nextTemp_7,
                                           temp_7]
                        )
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_53=nullDerefBool_54)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_31]
                      and 
                      (
                        sibling_34=(sibling_33)++((temp_7)->(nextTemp_7.sibling_33)))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_31])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        sibling_33=sibling_34)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition10[nextTemp_7]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_31]
                          and 
                          (
                            nullDerefBool_55=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_31])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_54=nullDerefBool_55)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition10[nextTemp_7])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_54=nullDerefBool_55)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_31]
                      and 
                      (
                        parent_7=(parent_6)++((nextTemp_7)->(temp_7)))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_31])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        parent_6=parent_7)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition12[nextTemp_7,
                                        temp_7]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_31]
                          and 
                          (
                            nullDerefBool_56=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_31])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_55=nullDerefBool_56)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition12[nextTemp_7,
                                            temp_7]
                        )
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_55=nullDerefBool_56)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_31]
                      and 
                      (
                        sibling_35=(sibling_34)++((nextTemp_7)->(temp_7.child_6)))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_31])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        sibling_34=sibling_35)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition14[temp_7]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_31]
                          and 
                          (
                            nullDerefBool_57=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_31])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_56=nullDerefBool_57)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition14[temp_7])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_56=nullDerefBool_57)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_31]
                      and 
                      (
                        child_7=(child_6)++((temp_7)->(nextTemp_7)))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_31])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        child_6=child_7)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition16[temp_7]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_31]
                          and 
                          (
                            nullDerefBool_58=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_31])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_57=nullDerefBool_58)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition16[temp_7])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_57=nullDerefBool_58)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_31]
                      and 
                      (
                        degree_7=(degree_6)++((temp_7)->(add[temp_7.degree_6,1])))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_31])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        degree_6=degree_7)
                    )
                  )
                  and 
                  (
                    head_16=head_17)
                  and 
                  (
                    temp_7=temp_8)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition24[lte_7])
                  )
                  and 
                  (
                    (
                      BinHeapCondition20[prevTemp_7]
                      and 
                      (
                        (
                          BinHeapCondition2[thiz_0]
                          and 
                          (
                            (
                              BinHeapCondition0[throw_31]
                              and 
                              (
                                nullDerefBool_54=true)
                            )
                            or 
                            (
                              (
                                not (
                                  BinHeapCondition0[throw_31])
                              )
                              and 
                              TruePred[]
                              and 
                              (
                                nullDerefBool_53=nullDerefBool_54)
                            )
                          )
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition2[thiz_0])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_53=nullDerefBool_54)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition0[throw_31]
                          and 
                          (
                            head_17=(head_16)++((thiz_0)->(nextTemp_7)))
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_31])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            head_16=head_17)
                        )
                      )
                      and 
                      (
                        sibling_33=sibling_34)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition20[prevTemp_7])
                      )
                      and 
                      (
                        (
                          BinHeapCondition18[prevTemp_7]
                          and 
                          (
                            (
                              BinHeapCondition0[throw_31]
                              and 
                              (
                                nullDerefBool_54=true)
                            )
                            or 
                            (
                              (
                                not (
                                  BinHeapCondition0[throw_31])
                              )
                              and 
                              TruePred[]
                              and 
                              (
                                nullDerefBool_53=nullDerefBool_54)
                            )
                          )
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition18[prevTemp_7])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_53=nullDerefBool_54)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition0[throw_31]
                          and 
                          (
                            sibling_34=(sibling_33)++((prevTemp_7)->(nextTemp_7)))
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_31])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            sibling_33=sibling_34)
                        )
                      )
                      and 
                      (
                        head_16=head_17)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition14[temp_7]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_31]
                          and 
                          (
                            nullDerefBool_55=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_31])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_54=nullDerefBool_55)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition14[temp_7])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_54=nullDerefBool_55)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_31]
                      and 
                      (
                        parent_7=(parent_6)++((temp_7)->(nextTemp_7)))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_31])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        parent_6=parent_7)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition8[nextTemp_7,
                                       temp_7]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_31]
                          and 
                          (
                            nullDerefBool_56=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_31])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_55=nullDerefBool_56)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition8[nextTemp_7,
                                           temp_7]
                        )
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_55=nullDerefBool_56)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_31]
                      and 
                      (
                        sibling_35=(sibling_34)++((temp_7)->(nextTemp_7.child_6)))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_31])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        sibling_34=sibling_35)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition10[nextTemp_7]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_31]
                          and 
                          (
                            nullDerefBool_57=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_31])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_56=nullDerefBool_57)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition10[nextTemp_7])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_56=nullDerefBool_57)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_31]
                      and 
                      (
                        child_7=(child_6)++((nextTemp_7)->(temp_7)))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_31])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        child_6=child_7)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition22[nextTemp_7]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_31]
                          and 
                          (
                            nullDerefBool_58=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_31])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_57=nullDerefBool_58)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition22[nextTemp_7])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_57=nullDerefBool_58)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_31]
                      and 
                      (
                        degree_7=(degree_6)++((nextTemp_7)->(add[nextTemp_7.degree_6,1])))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_31])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        degree_6=degree_7)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_31]
                      and 
                      (
                        temp_8=nextTemp_7)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_31])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        temp_7=temp_8)
                    )
                  )
                )
              )
              and 
              (
                prevTemp_7=prevTemp_8)
            )
          )
          and 
          (
            (
              BinHeapCondition14[temp_8]
              and 
              (
                (
                  BinHeapCondition0[throw_31]
                  and 
                  (
                    nullDerefBool_59=true)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_31])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_58=nullDerefBool_59)
                )
              )
            )
            or 
            (
              (
                not (
                  BinHeapCondition14[temp_8])
              )
              and 
              TruePred[]
              and 
              (
                nullDerefBool_58=nullDerefBool_59)
            )
          )
          and 
          (
            (
              BinHeapCondition0[throw_31]
              and 
              (
                nextTemp_8=temp_8.sibling_35)
            )
            or 
            (
              (
                not (
                  BinHeapCondition0[throw_31])
              )
              and 
              TruePred[]
              and 
              (
                nextTemp_7=nextTemp_8)
            )
          )
        )
        or 
        (
          TruePred[]
          and 
          (
            l8_nullDerefBool_0=l8_nullDerefBool_1)
          and 
          (
            l8_lte_0=l8_lte_2)
          and 
          (
            parent_6=parent_7)
          and 
          (
            nullDerefBool_51=nullDerefBool_59)
          and 
          (
            l8_lt_0=l8_lt_1)
          and 
          (
            child_6=child_7)
          and 
          (
            nextTemp_7=nextTemp_8)
          and 
          (
            l8_l0_nullDerefBool_0=l8_l0_nullDerefBool_1)
          and 
          (
            throw_27=throw_31)
          and 
          (
            degree_6=degree_7)
          and 
          (
            prevTemp_7=prevTemp_8)
          and 
          (
            sibling_33=sibling_35)
          and 
          (
            temp_7=temp_8)
          and 
          (
            head_16=head_17)
          and 
          (
            lte_6=lte_7)
          and 
          (
            l8_l0_result_0=l8_l0_result_2)
        )
      )
      and 
      (
        (
          BinHeapCondition28[nextTemp_8]
          and 
          (
            (
              BinHeapCondition6[nextTemp_8,
                               sibling_35,
                               temp_8]
              and 
              (
                (
                  BinHeapCondition0[throw_31]
                  and 
                  (
                    nullDerefBool_60=true)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_31])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_59=nullDerefBool_60)
                )
              )
            )
            or 
            (
              (
                not (
                  BinHeapCondition6[nextTemp_8,
                                   sibling_35,
                                   temp_8]
                )
              )
              and 
              TruePred[]
              and 
              (
                nullDerefBool_59=nullDerefBool_60)
            )
          )
          and 
          (
            (
              BinHeapCondition26[degree_7,
                                nextTemp_8,
                                sibling_35,
                                temp_8]
              and 
              (
                (
                  BinHeapCondition0[throw_31]
                  and 
                  (
                    prevTemp_9=temp_8)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_31])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    prevTemp_8=prevTemp_9)
                )
              )
              and 
              (
                (
                  BinHeapCondition0[throw_31]
                  and 
                  (
                    temp_9=nextTemp_8)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_31])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    temp_8=temp_9)
                )
              )
              and 
              (
                parent_7=parent_8)
              and 
              (
                nullDerefBool_60=nullDerefBool_66)
              and 
              (
                l9_l0_nullDerefBool_0=l9_l0_nullDerefBool_1)
              and 
              (
                child_7=child_8)
              and 
              (
                l9_l0_result_0=l9_l0_result_2)
              and 
              (
                l9_lt_0=l9_lt_1)
              and 
              (
                l9_nullDerefBool_0=l9_nullDerefBool_1)
              and 
              (
                head_17=head_18)
              and 
              (
                l9_lte_0=l9_lte_2)
              and 
              (
                lte_7=lte_8)
              and 
              (
                throw_31=throw_35)
              and 
              (
                degree_7=degree_8)
              and 
              (
                sibling_35=sibling_37)
            )
            or 
            (
              (
                not (
                  BinHeapCondition26[degree_7,
                                    nextTemp_8,
                                    sibling_35,
                                    temp_8]
                )
              )
              and 
              TruePred[]
              and 
              (
                (
                  BinHeapCondition8[nextTemp_8,
                                   temp_8]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_31]
                      and 
                      (
                        nullDerefBool_61=true)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_31])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_60=nullDerefBool_61)
                    )
                  )
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition8[nextTemp_8,
                                       temp_8]
                    )
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_60=nullDerefBool_61)
                )
              )
              and 
              (
                (
                  BinHeapCondition0[throw_31]
                  and 
                  Data_data_lte_0[temp_8.element_0,
                                 throw_31,
                                 throw_32,
                                 throw_33,
                                 throw_34,
                                 throw_35,
                                 lte_7,
                                 lte_8,
                                 nextTemp_8.element_0,
                                 l9_lt_0,
                                 l9_lt_1,
                                 l9_nullDerefBool_0,
                                 l9_nullDerefBool_1,
                                 l9_lte_0,
                                 l9_lte_1,
                                 l9_lte_2,
                                 l9_l0_result_0,
                                 l9_l0_result_1,
                                 l9_l0_result_2,
                                 l9_l0_nullDerefBool_0,
                                 l9_l0_nullDerefBool_1]
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_31])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    l9_l0_result_0=l9_l0_result_2)
                  and 
                  (
                    l9_lt_0=l9_lt_1)
                  and 
                  (
                    l9_nullDerefBool_0=l9_nullDerefBool_1)
                  and 
                  (
                    l9_l0_nullDerefBool_0=l9_l0_nullDerefBool_1)
                  and 
                  (
                    l9_lte_0=l9_lte_2)
                  and 
                  (
                    lte_7=lte_8)
                  and 
                  (
                    throw_31=throw_35)
                )
              )
              and 
              (
                (
                  BinHeapCondition24[lte_8]
                  and 
                  (
                    (
                      BinHeapCondition8[nextTemp_8,
                                       temp_8]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_35]
                          and 
                          (
                            nullDerefBool_62=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_35])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_61=nullDerefBool_62)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition8[nextTemp_8,
                                           temp_8]
                        )
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_61=nullDerefBool_62)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_35]
                      and 
                      (
                        sibling_36=(sibling_35)++((temp_8)->(nextTemp_8.sibling_35)))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_35])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        sibling_35=sibling_36)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition10[nextTemp_8]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_35]
                          and 
                          (
                            nullDerefBool_63=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_35])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_62=nullDerefBool_63)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition10[nextTemp_8])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_62=nullDerefBool_63)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_35]
                      and 
                      (
                        parent_8=(parent_7)++((nextTemp_8)->(temp_8)))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_35])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        parent_7=parent_8)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition12[nextTemp_8,
                                        temp_8]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_35]
                          and 
                          (
                            nullDerefBool_64=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_35])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_63=nullDerefBool_64)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition12[nextTemp_8,
                                            temp_8]
                        )
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_63=nullDerefBool_64)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_35]
                      and 
                      (
                        sibling_37=(sibling_36)++((nextTemp_8)->(temp_8.child_7)))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_35])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        sibling_36=sibling_37)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition14[temp_8]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_35]
                          and 
                          (
                            nullDerefBool_65=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_35])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_64=nullDerefBool_65)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition14[temp_8])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_64=nullDerefBool_65)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_35]
                      and 
                      (
                        child_8=(child_7)++((temp_8)->(nextTemp_8)))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_35])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        child_7=child_8)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition16[temp_8]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_35]
                          and 
                          (
                            nullDerefBool_66=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_35])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_65=nullDerefBool_66)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition16[temp_8])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_65=nullDerefBool_66)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_35]
                      and 
                      (
                        degree_8=(degree_7)++((temp_8)->(add[temp_8.degree_7,1])))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_35])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        degree_7=degree_8)
                    )
                  )
                  and 
                  (
                    head_17=head_18)
                  and 
                  (
                    temp_8=temp_9)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition24[lte_8])
                  )
                  and 
                  (
                    (
                      BinHeapCondition20[prevTemp_8]
                      and 
                      (
                        (
                          BinHeapCondition2[thiz_0]
                          and 
                          (
                            (
                              BinHeapCondition0[throw_35]
                              and 
                              (
                                nullDerefBool_62=true)
                            )
                            or 
                            (
                              (
                                not (
                                  BinHeapCondition0[throw_35])
                              )
                              and 
                              TruePred[]
                              and 
                              (
                                nullDerefBool_61=nullDerefBool_62)
                            )
                          )
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition2[thiz_0])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_61=nullDerefBool_62)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition0[throw_35]
                          and 
                          (
                            head_18=(head_17)++((thiz_0)->(nextTemp_8)))
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_35])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            head_17=head_18)
                        )
                      )
                      and 
                      (
                        sibling_35=sibling_36)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition20[prevTemp_8])
                      )
                      and 
                      (
                        (
                          BinHeapCondition18[prevTemp_8]
                          and 
                          (
                            (
                              BinHeapCondition0[throw_35]
                              and 
                              (
                                nullDerefBool_62=true)
                            )
                            or 
                            (
                              (
                                not (
                                  BinHeapCondition0[throw_35])
                              )
                              and 
                              TruePred[]
                              and 
                              (
                                nullDerefBool_61=nullDerefBool_62)
                            )
                          )
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition18[prevTemp_8])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_61=nullDerefBool_62)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition0[throw_35]
                          and 
                          (
                            sibling_36=(sibling_35)++((prevTemp_8)->(nextTemp_8)))
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_35])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            sibling_35=sibling_36)
                        )
                      )
                      and 
                      (
                        head_17=head_18)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition14[temp_8]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_35]
                          and 
                          (
                            nullDerefBool_63=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_35])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_62=nullDerefBool_63)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition14[temp_8])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_62=nullDerefBool_63)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_35]
                      and 
                      (
                        parent_8=(parent_7)++((temp_8)->(nextTemp_8)))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_35])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        parent_7=parent_8)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition8[nextTemp_8,
                                       temp_8]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_35]
                          and 
                          (
                            nullDerefBool_64=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_35])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_63=nullDerefBool_64)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition8[nextTemp_8,
                                           temp_8]
                        )
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_63=nullDerefBool_64)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_35]
                      and 
                      (
                        sibling_37=(sibling_36)++((temp_8)->(nextTemp_8.child_7)))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_35])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        sibling_36=sibling_37)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition10[nextTemp_8]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_35]
                          and 
                          (
                            nullDerefBool_65=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_35])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_64=nullDerefBool_65)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition10[nextTemp_8])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_64=nullDerefBool_65)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_35]
                      and 
                      (
                        child_8=(child_7)++((nextTemp_8)->(temp_8)))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_35])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        child_7=child_8)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition22[nextTemp_8]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_35]
                          and 
                          (
                            nullDerefBool_66=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_35])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_65=nullDerefBool_66)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition22[nextTemp_8])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_65=nullDerefBool_66)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_35]
                      and 
                      (
                        degree_8=(degree_7)++((nextTemp_8)->(add[nextTemp_8.degree_7,1])))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_35])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        degree_7=degree_8)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_35]
                      and 
                      (
                        temp_9=nextTemp_8)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_35])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        temp_8=temp_9)
                    )
                  )
                )
              )
              and 
              (
                prevTemp_8=prevTemp_9)
            )
          )
          and 
          (
            (
              BinHeapCondition14[temp_9]
              and 
              (
                (
                  BinHeapCondition0[throw_35]
                  and 
                  (
                    nullDerefBool_67=true)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_35])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_66=nullDerefBool_67)
                )
              )
            )
            or 
            (
              (
                not (
                  BinHeapCondition14[temp_9])
              )
              and 
              TruePred[]
              and 
              (
                nullDerefBool_66=nullDerefBool_67)
            )
          )
          and 
          (
            (
              BinHeapCondition0[throw_35]
              and 
              (
                nextTemp_9=temp_9.sibling_37)
            )
            or 
            (
              (
                not (
                  BinHeapCondition0[throw_35])
              )
              and 
              TruePred[]
              and 
              (
                nextTemp_8=nextTemp_9)
            )
          )
        )
        or 
        (
          TruePred[]
          and 
          (
            parent_7=parent_8)
          and 
          (
            nullDerefBool_59=nullDerefBool_67)
          and 
          (
            l9_l0_nullDerefBool_0=l9_l0_nullDerefBool_1)
          and 
          (
            child_7=child_8)
          and 
          (
            nextTemp_8=nextTemp_9)
          and 
          (
            l9_l0_result_0=l9_l0_result_2)
          and 
          (
            throw_31=throw_35)
          and 
          (
            degree_7=degree_8)
          and 
          (
            l9_lt_0=l9_lt_1)
          and 
          (
            prevTemp_8=prevTemp_9)
          and 
          (
            sibling_35=sibling_37)
          and 
          (
            l9_nullDerefBool_0=l9_nullDerefBool_1)
          and 
          (
            temp_8=temp_9)
          and 
          (
            head_17=head_18)
          and 
          (
            l9_lte_0=l9_lte_2)
          and 
          (
            lte_7=lte_8)
        )
      )
      and 
      (
        (
          BinHeapCondition28[nextTemp_9]
          and 
          (
            (
              BinHeapCondition6[nextTemp_9,
                               sibling_37,
                               temp_9]
              and 
              (
                (
                  BinHeapCondition0[throw_35]
                  and 
                  (
                    nullDerefBool_68=true)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_35])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_67=nullDerefBool_68)
                )
              )
            )
            or 
            (
              (
                not (
                  BinHeapCondition6[nextTemp_9,
                                   sibling_37,
                                   temp_9]
                )
              )
              and 
              TruePred[]
              and 
              (
                nullDerefBool_67=nullDerefBool_68)
            )
          )
          and 
          (
            (
              BinHeapCondition26[degree_8,
                                nextTemp_9,
                                sibling_37,
                                temp_9]
              and 
              (
                (
                  BinHeapCondition0[throw_35]
                  and 
                  (
                    prevTemp_10=temp_9)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_35])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    prevTemp_9=prevTemp_10)
                )
              )
              and 
              (
                (
                  BinHeapCondition0[throw_35]
                  and 
                  (
                    temp_10=nextTemp_9)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_35])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    temp_9=temp_10)
                )
              )
              and 
              (
                l10_lt_0=l10_lt_1)
              and 
              (
                parent_8=parent_9)
              and 
              (
                nullDerefBool_68=nullDerefBool_74)
              and 
              (
                l10_l0_result_0=l10_l0_result_2)
              and 
              (
                l10_l0_nullDerefBool_0=l10_l0_nullDerefBool_1)
              and 
              (
                child_8=child_9)
              and 
              (
                l10_lte_0=l10_lte_2)
              and 
              (
                l10_nullDerefBool_0=l10_nullDerefBool_1)
              and 
              (
                head_18=head_19)
              and 
              (
                lte_8=lte_9)
              and 
              (
                throw_35=throw_39)
              and 
              (
                degree_8=degree_9)
              and 
              (
                sibling_37=sibling_39)
            )
            or 
            (
              (
                not (
                  BinHeapCondition26[degree_8,
                                    nextTemp_9,
                                    sibling_37,
                                    temp_9]
                )
              )
              and 
              TruePred[]
              and 
              (
                (
                  BinHeapCondition8[nextTemp_9,
                                   temp_9]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_35]
                      and 
                      (
                        nullDerefBool_69=true)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_35])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_68=nullDerefBool_69)
                    )
                  )
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition8[nextTemp_9,
                                       temp_9]
                    )
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_68=nullDerefBool_69)
                )
              )
              and 
              (
                (
                  BinHeapCondition0[throw_35]
                  and 
                  Data_data_lte_0[temp_9.element_0,
                                 throw_35,
                                 throw_36,
                                 throw_37,
                                 throw_38,
                                 throw_39,
                                 lte_8,
                                 lte_9,
                                 nextTemp_9.element_0,
                                 l10_lt_0,
                                 l10_lt_1,
                                 l10_nullDerefBool_0,
                                 l10_nullDerefBool_1,
                                 l10_lte_0,
                                 l10_lte_1,
                                 l10_lte_2,
                                 l10_l0_result_0,
                                 l10_l0_result_1,
                                 l10_l0_result_2,
                                 l10_l0_nullDerefBool_0,
                                 l10_l0_nullDerefBool_1]
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_35])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    l10_lt_0=l10_lt_1)
                  and 
                  (
                    l10_lte_0=l10_lte_2)
                  and 
                  (
                    l10_nullDerefBool_0=l10_nullDerefBool_1)
                  and 
                  (
                    l10_l0_result_0=l10_l0_result_2)
                  and 
                  (
                    l10_l0_nullDerefBool_0=l10_l0_nullDerefBool_1)
                  and 
                  (
                    lte_8=lte_9)
                  and 
                  (
                    throw_35=throw_39)
                )
              )
              and 
              (
                (
                  BinHeapCondition24[lte_9]
                  and 
                  (
                    (
                      BinHeapCondition8[nextTemp_9,
                                       temp_9]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_39]
                          and 
                          (
                            nullDerefBool_70=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_39])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_69=nullDerefBool_70)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition8[nextTemp_9,
                                           temp_9]
                        )
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_69=nullDerefBool_70)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_39]
                      and 
                      (
                        sibling_38=(sibling_37)++((temp_9)->(nextTemp_9.sibling_37)))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_39])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        sibling_37=sibling_38)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition10[nextTemp_9]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_39]
                          and 
                          (
                            nullDerefBool_71=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_39])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_70=nullDerefBool_71)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition10[nextTemp_9])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_70=nullDerefBool_71)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_39]
                      and 
                      (
                        parent_9=(parent_8)++((nextTemp_9)->(temp_9)))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_39])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        parent_8=parent_9)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition12[nextTemp_9,
                                        temp_9]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_39]
                          and 
                          (
                            nullDerefBool_72=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_39])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_71=nullDerefBool_72)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition12[nextTemp_9,
                                            temp_9]
                        )
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_71=nullDerefBool_72)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_39]
                      and 
                      (
                        sibling_39=(sibling_38)++((nextTemp_9)->(temp_9.child_8)))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_39])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        sibling_38=sibling_39)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition14[temp_9]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_39]
                          and 
                          (
                            nullDerefBool_73=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_39])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_72=nullDerefBool_73)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition14[temp_9])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_72=nullDerefBool_73)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_39]
                      and 
                      (
                        child_9=(child_8)++((temp_9)->(nextTemp_9)))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_39])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        child_8=child_9)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition16[temp_9]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_39]
                          and 
                          (
                            nullDerefBool_74=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_39])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_73=nullDerefBool_74)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition16[temp_9])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_73=nullDerefBool_74)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_39]
                      and 
                      (
                        degree_9=(degree_8)++((temp_9)->(add[temp_9.degree_8,1])))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_39])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        degree_8=degree_9)
                    )
                  )
                  and 
                  (
                    head_18=head_19)
                  and 
                  (
                    temp_9=temp_10)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition24[lte_9])
                  )
                  and 
                  (
                    (
                      BinHeapCondition20[prevTemp_9]
                      and 
                      (
                        (
                          BinHeapCondition2[thiz_0]
                          and 
                          (
                            (
                              BinHeapCondition0[throw_39]
                              and 
                              (
                                nullDerefBool_70=true)
                            )
                            or 
                            (
                              (
                                not (
                                  BinHeapCondition0[throw_39])
                              )
                              and 
                              TruePred[]
                              and 
                              (
                                nullDerefBool_69=nullDerefBool_70)
                            )
                          )
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition2[thiz_0])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_69=nullDerefBool_70)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition0[throw_39]
                          and 
                          (
                            head_19=(head_18)++((thiz_0)->(nextTemp_9)))
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_39])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            head_18=head_19)
                        )
                      )
                      and 
                      (
                        sibling_37=sibling_38)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition20[prevTemp_9])
                      )
                      and 
                      (
                        (
                          BinHeapCondition18[prevTemp_9]
                          and 
                          (
                            (
                              BinHeapCondition0[throw_39]
                              and 
                              (
                                nullDerefBool_70=true)
                            )
                            or 
                            (
                              (
                                not (
                                  BinHeapCondition0[throw_39])
                              )
                              and 
                              TruePred[]
                              and 
                              (
                                nullDerefBool_69=nullDerefBool_70)
                            )
                          )
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition18[prevTemp_9])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_69=nullDerefBool_70)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition0[throw_39]
                          and 
                          (
                            sibling_38=(sibling_37)++((prevTemp_9)->(nextTemp_9)))
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_39])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            sibling_37=sibling_38)
                        )
                      )
                      and 
                      (
                        head_18=head_19)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition14[temp_9]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_39]
                          and 
                          (
                            nullDerefBool_71=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_39])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_70=nullDerefBool_71)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition14[temp_9])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_70=nullDerefBool_71)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_39]
                      and 
                      (
                        parent_9=(parent_8)++((temp_9)->(nextTemp_9)))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_39])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        parent_8=parent_9)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition8[nextTemp_9,
                                       temp_9]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_39]
                          and 
                          (
                            nullDerefBool_72=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_39])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_71=nullDerefBool_72)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition8[nextTemp_9,
                                           temp_9]
                        )
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_71=nullDerefBool_72)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_39]
                      and 
                      (
                        sibling_39=(sibling_38)++((temp_9)->(nextTemp_9.child_8)))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_39])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        sibling_38=sibling_39)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition10[nextTemp_9]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_39]
                          and 
                          (
                            nullDerefBool_73=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_39])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_72=nullDerefBool_73)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition10[nextTemp_9])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_72=nullDerefBool_73)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_39]
                      and 
                      (
                        child_9=(child_8)++((nextTemp_9)->(temp_9)))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_39])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        child_8=child_9)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition22[nextTemp_9]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_39]
                          and 
                          (
                            nullDerefBool_74=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_39])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_73=nullDerefBool_74)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition22[nextTemp_9])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_73=nullDerefBool_74)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_39]
                      and 
                      (
                        degree_9=(degree_8)++((nextTemp_9)->(add[nextTemp_9.degree_8,1])))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_39])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        degree_8=degree_9)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_39]
                      and 
                      (
                        temp_10=nextTemp_9)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_39])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        temp_9=temp_10)
                    )
                  )
                )
              )
              and 
              (
                prevTemp_9=prevTemp_10)
            )
          )
          and 
          (
            (
              BinHeapCondition14[temp_10]
              and 
              (
                (
                  BinHeapCondition0[throw_39]
                  and 
                  (
                    nullDerefBool_75=true)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_39])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_74=nullDerefBool_75)
                )
              )
            )
            or 
            (
              (
                not (
                  BinHeapCondition14[temp_10])
              )
              and 
              TruePred[]
              and 
              (
                nullDerefBool_74=nullDerefBool_75)
            )
          )
          and 
          (
            (
              BinHeapCondition0[throw_39]
              and 
              (
                nextTemp_10=temp_10.sibling_39)
            )
            or 
            (
              (
                not (
                  BinHeapCondition0[throw_39])
              )
              and 
              TruePred[]
              and 
              (
                nextTemp_9=nextTemp_10)
            )
          )
        )
        or 
        (
          TruePred[]
          and 
          (
            l10_lt_0=l10_lt_1)
          and 
          (
            parent_8=parent_9)
          and 
          (
            nullDerefBool_67=nullDerefBool_75)
          and 
          (
            l10_l0_result_0=l10_l0_result_2)
          and 
          (
            l10_l0_nullDerefBool_0=l10_l0_nullDerefBool_1)
          and 
          (
            child_8=child_9)
          and 
          (
            nextTemp_9=nextTemp_10)
          and 
          (
            throw_35=throw_39)
          and 
          (
            degree_8=degree_9)
          and 
          (
            prevTemp_9=prevTemp_10)
          and 
          (
            sibling_37=sibling_39)
          and 
          (
            l10_lte_0=l10_lte_2)
          and 
          (
            l10_nullDerefBool_0=l10_nullDerefBool_1)
          and 
          (
            temp_9=temp_10)
          and 
          (
            head_18=head_19)
          and 
          (
            lte_8=lte_9)
        )
      )
      and 
      (
        (
          BinHeapCondition28[nextTemp_10]
          and 
          (
            (
              BinHeapCondition6[nextTemp_10,
                               sibling_39,
                               temp_10]
              and 
              (
                (
                  BinHeapCondition0[throw_39]
                  and 
                  (
                    nullDerefBool_76=true)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_39])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_75=nullDerefBool_76)
                )
              )
            )
            or 
            (
              (
                not (
                  BinHeapCondition6[nextTemp_10,
                                   sibling_39,
                                   temp_10]
                )
              )
              and 
              TruePred[]
              and 
              (
                nullDerefBool_75=nullDerefBool_76)
            )
          )
          and 
          (
            (
              BinHeapCondition26[degree_9,
                                nextTemp_10,
                                sibling_39,
                                temp_10]
              and 
              (
                (
                  BinHeapCondition0[throw_39]
                  and 
                  (
                    prevTemp_11=temp_10)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_39])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    prevTemp_10=prevTemp_11)
                )
              )
              and 
              (
                (
                  BinHeapCondition0[throw_39]
                  and 
                  (
                    temp_11=nextTemp_10)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_39])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    temp_10=temp_11)
                )
              )
              and 
              (
                l11_l0_result_0=l11_l0_result_2)
              and 
              (
                l11_nullDerefBool_0=l11_nullDerefBool_1)
              and 
              (
                parent_9=parent_10)
              and 
              (
                l11_lte_0=l11_lte_2)
              and 
              (
                nullDerefBool_76=nullDerefBool_82)
              and 
              (
                l11_lt_0=l11_lt_1)
              and 
              (
                child_9=child_10)
              and 
              (
                l11_l0_nullDerefBool_0=l11_l0_nullDerefBool_1)
              and 
              (
                head_19=head_20)
              and 
              (
                lte_9=lte_10)
              and 
              (
                throw_39=throw_43)
              and 
              (
                degree_9=degree_10)
              and 
              (
                sibling_39=sibling_41)
            )
            or 
            (
              (
                not (
                  BinHeapCondition26[degree_9,
                                    nextTemp_10,
                                    sibling_39,
                                    temp_10]
                )
              )
              and 
              TruePred[]
              and 
              (
                (
                  BinHeapCondition8[nextTemp_10,
                                   temp_10]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_39]
                      and 
                      (
                        nullDerefBool_77=true)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_39])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_76=nullDerefBool_77)
                    )
                  )
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition8[nextTemp_10,
                                       temp_10]
                    )
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_76=nullDerefBool_77)
                )
              )
              and 
              (
                (
                  BinHeapCondition0[throw_39]
                  and 
                  Data_data_lte_0[temp_10.element_0,
                                 throw_39,
                                 throw_40,
                                 throw_41,
                                 throw_42,
                                 throw_43,
                                 lte_9,
                                 lte_10,
                                 nextTemp_10.element_0,
                                 l11_lt_0,
                                 l11_lt_1,
                                 l11_nullDerefBool_0,
                                 l11_nullDerefBool_1,
                                 l11_lte_0,
                                 l11_lte_1,
                                 l11_lte_2,
                                 l11_l0_result_0,
                                 l11_l0_result_1,
                                 l11_l0_result_2,
                                 l11_l0_nullDerefBool_0,
                                 l11_l0_nullDerefBool_1]
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_39])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    l11_l0_result_0=l11_l0_result_2)
                  and 
                  (
                    l11_nullDerefBool_0=l11_nullDerefBool_1)
                  and 
                  (
                    l11_lte_0=l11_lte_2)
                  and 
                  (
                    l11_l0_nullDerefBool_0=l11_l0_nullDerefBool_1)
                  and 
                  (
                    lte_9=lte_10)
                  and 
                  (
                    l11_lt_0=l11_lt_1)
                  and 
                  (
                    throw_39=throw_43)
                )
              )
              and 
              (
                (
                  BinHeapCondition24[lte_10]
                  and 
                  (
                    (
                      BinHeapCondition8[nextTemp_10,
                                       temp_10]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_43]
                          and 
                          (
                            nullDerefBool_78=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_43])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_77=nullDerefBool_78)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition8[nextTemp_10,
                                           temp_10]
                        )
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_77=nullDerefBool_78)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_43]
                      and 
                      (
                        sibling_40=(sibling_39)++((temp_10)->(nextTemp_10.sibling_39)))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_43])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        sibling_39=sibling_40)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition10[nextTemp_10]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_43]
                          and 
                          (
                            nullDerefBool_79=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_43])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_78=nullDerefBool_79)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition10[nextTemp_10])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_78=nullDerefBool_79)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_43]
                      and 
                      (
                        parent_10=(parent_9)++((nextTemp_10)->(temp_10)))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_43])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        parent_9=parent_10)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition12[nextTemp_10,
                                        temp_10]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_43]
                          and 
                          (
                            nullDerefBool_80=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_43])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_79=nullDerefBool_80)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition12[nextTemp_10,
                                            temp_10]
                        )
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_79=nullDerefBool_80)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_43]
                      and 
                      (
                        sibling_41=(sibling_40)++((nextTemp_10)->(temp_10.child_9)))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_43])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        sibling_40=sibling_41)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition14[temp_10]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_43]
                          and 
                          (
                            nullDerefBool_81=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_43])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_80=nullDerefBool_81)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition14[temp_10])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_80=nullDerefBool_81)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_43]
                      and 
                      (
                        child_10=(child_9)++((temp_10)->(nextTemp_10)))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_43])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        child_9=child_10)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition16[temp_10]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_43]
                          and 
                          (
                            nullDerefBool_82=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_43])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_81=nullDerefBool_82)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition16[temp_10])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_81=nullDerefBool_82)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_43]
                      and 
                      (
                        degree_10=(degree_9)++((temp_10)->(add[temp_10.degree_9,1])))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_43])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        degree_9=degree_10)
                    )
                  )
                  and 
                  (
                    head_19=head_20)
                  and 
                  (
                    temp_10=temp_11)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition24[lte_10])
                  )
                  and 
                  (
                    (
                      BinHeapCondition20[prevTemp_10]
                      and 
                      (
                        (
                          BinHeapCondition2[thiz_0]
                          and 
                          (
                            (
                              BinHeapCondition0[throw_43]
                              and 
                              (
                                nullDerefBool_78=true)
                            )
                            or 
                            (
                              (
                                not (
                                  BinHeapCondition0[throw_43])
                              )
                              and 
                              TruePred[]
                              and 
                              (
                                nullDerefBool_77=nullDerefBool_78)
                            )
                          )
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition2[thiz_0])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_77=nullDerefBool_78)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition0[throw_43]
                          and 
                          (
                            head_20=(head_19)++((thiz_0)->(nextTemp_10)))
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_43])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            head_19=head_20)
                        )
                      )
                      and 
                      (
                        sibling_39=sibling_40)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition20[prevTemp_10])
                      )
                      and 
                      (
                        (
                          BinHeapCondition18[prevTemp_10]
                          and 
                          (
                            (
                              BinHeapCondition0[throw_43]
                              and 
                              (
                                nullDerefBool_78=true)
                            )
                            or 
                            (
                              (
                                not (
                                  BinHeapCondition0[throw_43])
                              )
                              and 
                              TruePred[]
                              and 
                              (
                                nullDerefBool_77=nullDerefBool_78)
                            )
                          )
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition18[prevTemp_10])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_77=nullDerefBool_78)
                        )
                      )
                      and 
                      (
                        (
                          BinHeapCondition0[throw_43]
                          and 
                          (
                            sibling_40=(sibling_39)++((prevTemp_10)->(nextTemp_10)))
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_43])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            sibling_39=sibling_40)
                        )
                      )
                      and 
                      (
                        head_19=head_20)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition14[temp_10]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_43]
                          and 
                          (
                            nullDerefBool_79=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_43])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_78=nullDerefBool_79)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition14[temp_10])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_78=nullDerefBool_79)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_43]
                      and 
                      (
                        parent_10=(parent_9)++((temp_10)->(nextTemp_10)))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_43])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        parent_9=parent_10)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition8[nextTemp_10,
                                       temp_10]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_43]
                          and 
                          (
                            nullDerefBool_80=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_43])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_79=nullDerefBool_80)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition8[nextTemp_10,
                                           temp_10]
                        )
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_79=nullDerefBool_80)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_43]
                      and 
                      (
                        sibling_41=(sibling_40)++((temp_10)->(nextTemp_10.child_9)))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_43])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        sibling_40=sibling_41)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition10[nextTemp_10]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_43]
                          and 
                          (
                            nullDerefBool_81=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_43])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_80=nullDerefBool_81)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition10[nextTemp_10])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_80=nullDerefBool_81)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_43]
                      and 
                      (
                        child_10=(child_9)++((nextTemp_10)->(temp_10)))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_43])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        child_9=child_10)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition22[nextTemp_10]
                      and 
                      (
                        (
                          BinHeapCondition0[throw_43]
                          and 
                          (
                            nullDerefBool_82=true)
                        )
                        or 
                        (
                          (
                            not (
                              BinHeapCondition0[throw_43])
                          )
                          and 
                          TruePred[]
                          and 
                          (
                            nullDerefBool_81=nullDerefBool_82)
                        )
                      )
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition22[nextTemp_10])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        nullDerefBool_81=nullDerefBool_82)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_43]
                      and 
                      (
                        degree_10=(degree_9)++((nextTemp_10)->(add[nextTemp_10.degree_9,1])))
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_43])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        degree_9=degree_10)
                    )
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_43]
                      and 
                      (
                        temp_11=nextTemp_10)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_43])
                      )
                      and 
                      TruePred[]
                      and 
                      (
                        temp_10=temp_11)
                    )
                  )
                )
              )
              and 
              (
                prevTemp_10=prevTemp_11)
            )
          )
          and 
          (
            (
              BinHeapCondition14[temp_11]
              and 
              (
                (
                  BinHeapCondition0[throw_43]
                  and 
                  (
                    nullDerefBool_83=true)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_43])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_82=nullDerefBool_83)
                )
              )
            )
            or 
            (
              (
                not (
                  BinHeapCondition14[temp_11])
              )
              and 
              TruePred[]
              and 
              (
                nullDerefBool_82=nullDerefBool_83)
            )
          )
          and 
          (
            (
              BinHeapCondition0[throw_43]
              and 
              (
                nextTemp_11=temp_11.sibling_41)
            )
            or 
            (
              (
                not (
                  BinHeapCondition0[throw_43])
              )
              and 
              TruePred[]
              and 
              (
                nextTemp_10=nextTemp_11)
            )
          )
        )
        or 
        (
          TruePred[]
          and 
          (
            l11_l0_result_0=l11_l0_result_2)
          and 
          (
            l11_nullDerefBool_0=l11_nullDerefBool_1)
          and 
          (
            parent_9=parent_10)
          and 
          (
            l11_lte_0=l11_lte_2)
          and 
          (
            nullDerefBool_75=nullDerefBool_83)
          and 
          (
            l11_lt_0=l11_lt_1)
          and 
          (
            child_9=child_10)
          and 
          (
            nextTemp_10=nextTemp_11)
          and 
          (
            throw_39=throw_43)
          and 
          (
            degree_9=degree_10)
          and 
          (
            prevTemp_10=prevTemp_11)
          and 
          (
            sibling_39=sibling_41)
          and 
          (
            temp_10=temp_11)
          and 
          (
            l11_l0_nullDerefBool_0=l11_l0_nullDerefBool_1)
          and 
          (
            head_19=head_20)
          and 
          (
            lte_9=lte_10)
        )
      )
      and 
      BinHeapCondition29[nextTemp_11]
    )
    or 
    (
      (
        not (
          BinHeapCondition0[throw_3])
      )
      and 
      TruePred[]
      and 
      (
        l8_nullDerefBool_0=l8_nullDerefBool_1)
      and 
      (
        nullDerefBool_3=nullDerefBool_83)
      and 
      (
        l8_lt_0=l8_lt_1)
      and 
      (
        l10_l0_nullDerefBool_0=l10_l0_nullDerefBool_1)
      and 
      (
        l9_l0_nullDerefBool_0=l9_l0_nullDerefBool_1)
      and 
      (
        l5_lt_0=l5_lt_1)
      and 
      (
        l9_lt_0=l9_lt_1)
      and 
      (
        l5_l0_nullDerefBool_0=l5_l0_nullDerefBool_1)
      and 
      (
        l6_l0_nullDerefBool_0=l6_l0_nullDerefBool_1)
      and 
      (
        l10_lte_0=l10_lte_2)
      and 
      (
        head_10=head_20)
      and 
      (
        l6_lte_0=l6_lte_2)
      and 
      (
        l8_l0_result_0=l8_l0_result_2)
      and 
      (
        l10_lt_0=l10_lt_1)
      and 
      (
        l11_l0_result_0=l11_l0_result_2)
      and 
      (
        l3_l0_nullDerefBool_0=l3_l0_nullDerefBool_1)
      and 
      (
        l11_nullDerefBool_0=l11_nullDerefBool_1)
      and 
      (
        parent_0=parent_10)
      and 
      (
        l3_lt_0=l3_lt_1)
      and 
      (
        l3_l0_result_0=l3_l0_result_2)
      and 
      (
        l2_l0_nullDerefBool_0=l2_l0_nullDerefBool_1)
      and 
      (
        l11_lt_0=l11_lt_1)
      and 
      (
        l2_nullDerefBool_0=l2_nullDerefBool_1)
      and 
      (
        l4_lte_0=l4_lte_2)
      and 
      (
        l8_l0_nullDerefBool_0=l8_l0_nullDerefBool_1)
      and 
      (
        l9_l0_result_0=l9_l0_result_2)
      and 
      (
        l7_nullDerefBool_0=l7_nullDerefBool_1)
      and 
      (
        l4_l0_result_0=l4_l0_result_2)
      and 
      (
        temp_1=temp_11)
      and 
      (
        l3_lte_0=l3_lte_2)
      and 
      (
        lte_0=lte_10)
      and 
      (
        l7_lte_0=l7_lte_2)
      and 
      (
        l8_lte_0=l8_lte_2)
      and 
      (
        l11_lte_0=l11_lte_2)
      and 
      (
        l4_nullDerefBool_0=l4_nullDerefBool_1)
      and 
      (
        l7_l0_nullDerefBool_0=l7_l0_nullDerefBool_1)
      and 
      (
        child_0=child_10)
      and 
      (
        nextTemp_1=nextTemp_11)
      and 
      (
        l6_lt_0=l6_lt_1)
      and 
      (
        l9_nullDerefBool_0=l9_nullDerefBool_1)
      and 
      (
        l5_nullDerefBool_0=l5_nullDerefBool_1)
      and 
      (
        l5_lte_0=l5_lte_2)
      and 
      (
        l6_nullDerefBool_0=l6_nullDerefBool_1)
      and 
      (
        l9_lte_0=l9_lte_2)
      and 
      (
        l11_l0_nullDerefBool_0=l11_l0_nullDerefBool_1)
      and 
      (
        l7_l0_result_0=l7_l0_result_2)
      and 
      (
        l4_lt_0=l4_lt_1)
      and 
      (
        l2_l0_result_0=l2_l0_result_2)
      and 
      (
        l3_nullDerefBool_0=l3_nullDerefBool_1)
      and 
      (
        l5_l0_result_0=l5_l0_result_2)
      and 
      (
        l2_lte_0=l2_lte_2)
      and 
      (
        l6_l0_result_0=l6_l0_result_2)
      and 
      (
        l7_lt_0=l7_lt_1)
      and 
      (
        l4_l0_nullDerefBool_0=l4_l0_nullDerefBool_1)
      and 
      (
        l10_l0_result_0=l10_l0_result_2)
      and 
      (
        l2_lt_0=l2_lt_1)
      and 
      (
        degree_0=degree_10)
      and 
      (
        prevTemp_1=prevTemp_11)
      and 
      (
        sibling_21=sibling_41)
      and 
      (
        l10_nullDerefBool_0=l10_nullDerefBool_1)
      and 
      (
        throw_3=throw_43)
    )
  )
  and 
  (
    (
      BinHeapCondition30[nullDerefBool_83,
                        throw_43]
      and 
      (
        (
          BinHeapCondition0[throw_43]
          and 
          (
            throw_44=NullPointerExceptionLit)
        )
        or 
        (
          (
            not (
              BinHeapCondition0[throw_43])
          )
          and 
          TruePred[]
          and 
          (
            throw_43=throw_44)
        )
      )
    )
    or 
    (
      (
        not (
          BinHeapCondition30[nullDerefBool_83,
                            throw_43]
        )
      )
      and 
      TruePred[]
      and 
      (
        throw_43=throw_44)
    )
  )

}

one sig QF {
  bchild_0,fchild_0: ( BinHeapNode ) -> lone ( BinHeapNode + null ),
  child_1: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  child_10: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  child_2: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  child_3: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  child_4: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  child_5: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  child_6: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  child_7: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  child_8: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  child_9: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  data_value_0: Data + null,
  degree_0: ( BinHeapNode ) -> one ( Int ),
  degree_1: ( BinHeapNode ) -> one ( Int ),
  degree_10: ( BinHeapNode ) -> one ( Int ),
  degree_2: ( BinHeapNode ) -> one ( Int ),
  degree_3: ( BinHeapNode ) -> one ( Int ),
  degree_4: ( BinHeapNode ) -> one ( Int ),
  degree_5: ( BinHeapNode ) -> one ( Int ),
  degree_6: ( BinHeapNode ) -> one ( Int ),
  degree_7: ( BinHeapNode ) -> one ( Int ),
  degree_8: ( BinHeapNode ) -> one ( Int ),
  degree_9: ( BinHeapNode ) -> one ( Int ),
  element_0: ( BinHeapNode ) -> one ( Data + null ),
  element_1: ( BinHeapNode ) -> one ( Data + null ),
  fresh_node_0: BinHeapNode + null,
  head_0: ( BinHeap ) -> one ( BinHeapNode + null ),
  head_1: ( BinHeap ) -> one ( BinHeapNode + null ),
  head_10: ( BinHeap ) -> one ( BinHeapNode + null ),
  head_11: ( BinHeap ) -> one ( BinHeapNode + null ),
  head_12: ( BinHeap ) -> one ( BinHeapNode + null ),
  head_13: ( BinHeap ) -> one ( BinHeapNode + null ),
  head_14: ( BinHeap ) -> one ( BinHeapNode + null ),
  head_15: ( BinHeap ) -> one ( BinHeapNode + null ),
  head_16: ( BinHeap ) -> one ( BinHeapNode + null ),
  head_17: ( BinHeap ) -> one ( BinHeapNode + null ),
  head_18: ( BinHeap ) -> one ( BinHeapNode + null ),
  head_19: ( BinHeap ) -> one ( BinHeapNode + null ),
  head_2: ( BinHeap ) -> one ( BinHeapNode + null ),
  head_20: ( BinHeap ) -> one ( BinHeapNode + null ),
  head_3: ( BinHeap ) -> one ( BinHeapNode + null ),
  head_4: ( BinHeap ) -> one ( BinHeapNode + null ),
  head_5: ( BinHeap ) -> one ( BinHeapNode + null ),
  head_6: ( BinHeap ) -> one ( BinHeapNode + null ),
  head_7: ( BinHeap ) -> one ( BinHeapNode + null ),
  head_8: ( BinHeap ) -> one ( BinHeapNode + null ),
  head_9: ( BinHeap ) -> one ( BinHeapNode + null ),
  l13_l12_l10_l0_nullDerefBool_0: boolean,
  l13_l12_l10_l0_nullDerefBool_1: boolean,
  l13_l12_l10_l0_result_0: boolean,
  l13_l12_l10_l0_result_1: boolean,
  l13_l12_l10_l0_result_2: boolean,
  l13_l12_l10_lt_0: boolean,
  l13_l12_l10_lt_1: boolean,
  l13_l12_l10_lte_0: boolean,
  l13_l12_l10_lte_1: boolean,
  l13_l12_l10_lte_2: boolean,
  l13_l12_l10_nullDerefBool_0: boolean,
  l13_l12_l10_nullDerefBool_1: boolean,
  l13_l12_l11_l0_nullDerefBool_0: boolean,
  l13_l12_l11_l0_nullDerefBool_1: boolean,
  l13_l12_l11_l0_result_0: boolean,
  l13_l12_l11_l0_result_1: boolean,
  l13_l12_l11_l0_result_2: boolean,
  l13_l12_l11_lt_0: boolean,
  l13_l12_l11_lt_1: boolean,
  l13_l12_l11_lte_0: boolean,
  l13_l12_l11_lte_1: boolean,
  l13_l12_l11_lte_2: boolean,
  l13_l12_l11_nullDerefBool_0: boolean,
  l13_l12_l11_nullDerefBool_1: boolean,
  l13_l12_l1_nullDerefBool_0: boolean,
  l13_l12_l1_nullDerefBool_1: boolean,
  l13_l12_l1_nullDerefBool_10: boolean,
  l13_l12_l1_nullDerefBool_11: boolean,
  l13_l12_l1_nullDerefBool_12: boolean,
  l13_l12_l1_nullDerefBool_13: boolean,
  l13_l12_l1_nullDerefBool_14: boolean,
  l13_l12_l1_nullDerefBool_15: boolean,
  l13_l12_l1_nullDerefBool_16: boolean,
  l13_l12_l1_nullDerefBool_17: boolean,
  l13_l12_l1_nullDerefBool_18: boolean,
  l13_l12_l1_nullDerefBool_19: boolean,
  l13_l12_l1_nullDerefBool_2: boolean,
  l13_l12_l1_nullDerefBool_20: boolean,
  l13_l12_l1_nullDerefBool_21: boolean,
  l13_l12_l1_nullDerefBool_22: boolean,
  l13_l12_l1_nullDerefBool_23: boolean,
  l13_l12_l1_nullDerefBool_24: boolean,
  l13_l12_l1_nullDerefBool_25: boolean,
  l13_l12_l1_nullDerefBool_26: boolean,
  l13_l12_l1_nullDerefBool_27: boolean,
  l13_l12_l1_nullDerefBool_28: boolean,
  l13_l12_l1_nullDerefBool_29: boolean,
  l13_l12_l1_nullDerefBool_3: boolean,
  l13_l12_l1_nullDerefBool_30: boolean,
  l13_l12_l1_nullDerefBool_31: boolean,
  l13_l12_l1_nullDerefBool_32: boolean,
  l13_l12_l1_nullDerefBool_33: boolean,
  l13_l12_l1_nullDerefBool_34: boolean,
  l13_l12_l1_nullDerefBool_35: boolean,
  l13_l12_l1_nullDerefBool_36: boolean,
  l13_l12_l1_nullDerefBool_37: boolean,
  l13_l12_l1_nullDerefBool_38: boolean,
  l13_l12_l1_nullDerefBool_39: boolean,
  l13_l12_l1_nullDerefBool_4: boolean,
  l13_l12_l1_nullDerefBool_40: boolean,
  l13_l12_l1_nullDerefBool_41: boolean,
  l13_l12_l1_nullDerefBool_42: boolean,
  l13_l12_l1_nullDerefBool_43: boolean,
  l13_l12_l1_nullDerefBool_44: boolean,
  l13_l12_l1_nullDerefBool_45: boolean,
  l13_l12_l1_nullDerefBool_46: boolean,
  l13_l12_l1_nullDerefBool_47: boolean,
  l13_l12_l1_nullDerefBool_48: boolean,
  l13_l12_l1_nullDerefBool_49: boolean,
  l13_l12_l1_nullDerefBool_5: boolean,
  l13_l12_l1_nullDerefBool_50: boolean,
  l13_l12_l1_nullDerefBool_51: boolean,
  l13_l12_l1_nullDerefBool_52: boolean,
  l13_l12_l1_nullDerefBool_53: boolean,
  l13_l12_l1_nullDerefBool_54: boolean,
  l13_l12_l1_nullDerefBool_55: boolean,
  l13_l12_l1_nullDerefBool_56: boolean,
  l13_l12_l1_nullDerefBool_57: boolean,
  l13_l12_l1_nullDerefBool_58: boolean,
  l13_l12_l1_nullDerefBool_59: boolean,
  l13_l12_l1_nullDerefBool_6: boolean,
  l13_l12_l1_nullDerefBool_60: boolean,
  l13_l12_l1_nullDerefBool_61: boolean,
  l13_l12_l1_nullDerefBool_62: boolean,
  l13_l12_l1_nullDerefBool_63: boolean,
  l13_l12_l1_nullDerefBool_64: boolean,
  l13_l12_l1_nullDerefBool_65: boolean,
  l13_l12_l1_nullDerefBool_66: boolean,
  l13_l12_l1_nullDerefBool_67: boolean,
  l13_l12_l1_nullDerefBool_68: boolean,
  l13_l12_l1_nullDerefBool_69: boolean,
  l13_l12_l1_nullDerefBool_7: boolean,
  l13_l12_l1_nullDerefBool_70: boolean,
  l13_l12_l1_nullDerefBool_71: boolean,
  l13_l12_l1_nullDerefBool_72: boolean,
  l13_l12_l1_nullDerefBool_73: boolean,
  l13_l12_l1_nullDerefBool_74: boolean,
  l13_l12_l1_nullDerefBool_75: boolean,
  l13_l12_l1_nullDerefBool_76: boolean,
  l13_l12_l1_nullDerefBool_77: boolean,
  l13_l12_l1_nullDerefBool_78: boolean,
  l13_l12_l1_nullDerefBool_79: boolean,
  l13_l12_l1_nullDerefBool_8: boolean,
  l13_l12_l1_nullDerefBool_80: boolean,
  l13_l12_l1_nullDerefBool_81: boolean,
  l13_l12_l1_nullDerefBool_82: boolean,
  l13_l12_l1_nullDerefBool_83: boolean,
  l13_l12_l1_nullDerefBool_84: boolean,
  l13_l12_l1_nullDerefBool_85: boolean,
  l13_l12_l1_nullDerefBool_9: boolean,
  l13_l12_l1_temp1_0: BinHeapNode + null,
  l13_l12_l1_temp1_1: BinHeapNode + null,
  l13_l12_l1_temp1_10: BinHeapNode + null,
  l13_l12_l1_temp1_11: BinHeapNode + null,
  l13_l12_l1_temp1_12: BinHeapNode + null,
  l13_l12_l1_temp1_13: BinHeapNode + null,
  l13_l12_l1_temp1_14: BinHeapNode + null,
  l13_l12_l1_temp1_15: BinHeapNode + null,
  l13_l12_l1_temp1_16: BinHeapNode + null,
  l13_l12_l1_temp1_17: BinHeapNode + null,
  l13_l12_l1_temp1_18: BinHeapNode + null,
  l13_l12_l1_temp1_19: BinHeapNode + null,
  l13_l12_l1_temp1_2: BinHeapNode + null,
  l13_l12_l1_temp1_20: BinHeapNode + null,
  l13_l12_l1_temp1_21: BinHeapNode + null,
  l13_l12_l1_temp1_22: BinHeapNode + null,
  l13_l12_l1_temp1_3: BinHeapNode + null,
  l13_l12_l1_temp1_4: BinHeapNode + null,
  l13_l12_l1_temp1_5: BinHeapNode + null,
  l13_l12_l1_temp1_6: BinHeapNode + null,
  l13_l12_l1_temp1_7: BinHeapNode + null,
  l13_l12_l1_temp1_8: BinHeapNode + null,
  l13_l12_l1_temp1_9: BinHeapNode + null,
  l13_l12_l1_temp2_0: BinHeapNode + null,
  l13_l12_l1_temp2_1: BinHeapNode + null,
  l13_l12_l1_temp2_10: BinHeapNode + null,
  l13_l12_l1_temp2_11: BinHeapNode + null,
  l13_l12_l1_temp2_2: BinHeapNode + null,
  l13_l12_l1_temp2_3: BinHeapNode + null,
  l13_l12_l1_temp2_4: BinHeapNode + null,
  l13_l12_l1_temp2_5: BinHeapNode + null,
  l13_l12_l1_temp2_6: BinHeapNode + null,
  l13_l12_l1_temp2_7: BinHeapNode + null,
  l13_l12_l1_temp2_8: BinHeapNode + null,
  l13_l12_l1_temp2_9: BinHeapNode + null,
  l13_l12_l1_tmp_0: BinHeapNode + null,
  l13_l12_l1_tmp_1: BinHeapNode + null,
  l13_l12_l1_tmp_10: BinHeapNode + null,
  l13_l12_l1_tmp_2: BinHeapNode + null,
  l13_l12_l1_tmp_3: BinHeapNode + null,
  l13_l12_l1_tmp_4: BinHeapNode + null,
  l13_l12_l1_tmp_5: BinHeapNode + null,
  l13_l12_l1_tmp_6: BinHeapNode + null,
  l13_l12_l1_tmp_7: BinHeapNode + null,
  l13_l12_l1_tmp_8: BinHeapNode + null,
  l13_l12_l1_tmp_9: BinHeapNode + null,
  l13_l12_l2_l0_nullDerefBool_0: boolean,
  l13_l12_l2_l0_nullDerefBool_1: boolean,
  l13_l12_l2_l0_result_0: boolean,
  l13_l12_l2_l0_result_1: boolean,
  l13_l12_l2_l0_result_2: boolean,
  l13_l12_l2_lt_0: boolean,
  l13_l12_l2_lt_1: boolean,
  l13_l12_l2_lte_0: boolean,
  l13_l12_l2_lte_1: boolean,
  l13_l12_l2_lte_2: boolean,
  l13_l12_l2_nullDerefBool_0: boolean,
  l13_l12_l2_nullDerefBool_1: boolean,
  l13_l12_l3_l0_nullDerefBool_0: boolean,
  l13_l12_l3_l0_nullDerefBool_1: boolean,
  l13_l12_l3_l0_result_0: boolean,
  l13_l12_l3_l0_result_1: boolean,
  l13_l12_l3_l0_result_2: boolean,
  l13_l12_l3_lt_0: boolean,
  l13_l12_l3_lt_1: boolean,
  l13_l12_l3_lte_0: boolean,
  l13_l12_l3_lte_1: boolean,
  l13_l12_l3_lte_2: boolean,
  l13_l12_l3_nullDerefBool_0: boolean,
  l13_l12_l3_nullDerefBool_1: boolean,
  l13_l12_l4_l0_nullDerefBool_0: boolean,
  l13_l12_l4_l0_nullDerefBool_1: boolean,
  l13_l12_l4_l0_result_0: boolean,
  l13_l12_l4_l0_result_1: boolean,
  l13_l12_l4_l0_result_2: boolean,
  l13_l12_l4_lt_0: boolean,
  l13_l12_l4_lt_1: boolean,
  l13_l12_l4_lte_0: boolean,
  l13_l12_l4_lte_1: boolean,
  l13_l12_l4_lte_2: boolean,
  l13_l12_l4_nullDerefBool_0: boolean,
  l13_l12_l4_nullDerefBool_1: boolean,
  l13_l12_l5_l0_nullDerefBool_0: boolean,
  l13_l12_l5_l0_nullDerefBool_1: boolean,
  l13_l12_l5_l0_result_0: boolean,
  l13_l12_l5_l0_result_1: boolean,
  l13_l12_l5_l0_result_2: boolean,
  l13_l12_l5_lt_0: boolean,
  l13_l12_l5_lt_1: boolean,
  l13_l12_l5_lte_0: boolean,
  l13_l12_l5_lte_1: boolean,
  l13_l12_l5_lte_2: boolean,
  l13_l12_l5_nullDerefBool_0: boolean,
  l13_l12_l5_nullDerefBool_1: boolean,
  l13_l12_l6_l0_nullDerefBool_0: boolean,
  l13_l12_l6_l0_nullDerefBool_1: boolean,
  l13_l12_l6_l0_result_0: boolean,
  l13_l12_l6_l0_result_1: boolean,
  l13_l12_l6_l0_result_2: boolean,
  l13_l12_l6_lt_0: boolean,
  l13_l12_l6_lt_1: boolean,
  l13_l12_l6_lte_0: boolean,
  l13_l12_l6_lte_1: boolean,
  l13_l12_l6_lte_2: boolean,
  l13_l12_l6_nullDerefBool_0: boolean,
  l13_l12_l6_nullDerefBool_1: boolean,
  l13_l12_l7_l0_nullDerefBool_0: boolean,
  l13_l12_l7_l0_nullDerefBool_1: boolean,
  l13_l12_l7_l0_result_0: boolean,
  l13_l12_l7_l0_result_1: boolean,
  l13_l12_l7_l0_result_2: boolean,
  l13_l12_l7_lt_0: boolean,
  l13_l12_l7_lt_1: boolean,
  l13_l12_l7_lte_0: boolean,
  l13_l12_l7_lte_1: boolean,
  l13_l12_l7_lte_2: boolean,
  l13_l12_l7_nullDerefBool_0: boolean,
  l13_l12_l7_nullDerefBool_1: boolean,
  l13_l12_l8_l0_nullDerefBool_0: boolean,
  l13_l12_l8_l0_nullDerefBool_1: boolean,
  l13_l12_l8_l0_result_0: boolean,
  l13_l12_l8_l0_result_1: boolean,
  l13_l12_l8_l0_result_2: boolean,
  l13_l12_l8_lt_0: boolean,
  l13_l12_l8_lt_1: boolean,
  l13_l12_l8_lte_0: boolean,
  l13_l12_l8_lte_1: boolean,
  l13_l12_l8_lte_2: boolean,
  l13_l12_l8_nullDerefBool_0: boolean,
  l13_l12_l8_nullDerefBool_1: boolean,
  l13_l12_l9_l0_nullDerefBool_0: boolean,
  l13_l12_l9_l0_nullDerefBool_1: boolean,
  l13_l12_l9_l0_result_0: boolean,
  l13_l12_l9_l0_result_1: boolean,
  l13_l12_l9_l0_result_2: boolean,
  l13_l12_l9_lt_0: boolean,
  l13_l12_l9_lt_1: boolean,
  l13_l12_l9_lte_0: boolean,
  l13_l12_l9_lte_1: boolean,
  l13_l12_l9_lte_2: boolean,
  l13_l12_l9_nullDerefBool_0: boolean,
  l13_l12_l9_nullDerefBool_1: boolean,
  l13_l12_lte_0: boolean,
  l13_l12_lte_1: boolean,
  l13_l12_lte_10: boolean,
  l13_l12_lte_2: boolean,
  l13_l12_lte_3: boolean,
  l13_l12_lte_4: boolean,
  l13_l12_lte_5: boolean,
  l13_l12_lte_6: boolean,
  l13_l12_lte_7: boolean,
  l13_l12_lte_8: boolean,
  l13_l12_lte_9: boolean,
  l13_l12_nextTemp_0: BinHeapNode + null,
  l13_l12_nextTemp_1: BinHeapNode + null,
  l13_l12_nextTemp_10: BinHeapNode + null,
  l13_l12_nextTemp_11: BinHeapNode + null,
  l13_l12_nextTemp_2: BinHeapNode + null,
  l13_l12_nextTemp_3: BinHeapNode + null,
  l13_l12_nextTemp_4: BinHeapNode + null,
  l13_l12_nextTemp_5: BinHeapNode + null,
  l13_l12_nextTemp_6: BinHeapNode + null,
  l13_l12_nextTemp_7: BinHeapNode + null,
  l13_l12_nextTemp_8: BinHeapNode + null,
  l13_l12_nextTemp_9: BinHeapNode + null,
  l13_l12_nullDerefBool_0: boolean,
  l13_l12_nullDerefBool_1: boolean,
  l13_l12_nullDerefBool_10: boolean,
  l13_l12_nullDerefBool_11: boolean,
  l13_l12_nullDerefBool_12: boolean,
  l13_l12_nullDerefBool_13: boolean,
  l13_l12_nullDerefBool_14: boolean,
  l13_l12_nullDerefBool_15: boolean,
  l13_l12_nullDerefBool_16: boolean,
  l13_l12_nullDerefBool_17: boolean,
  l13_l12_nullDerefBool_18: boolean,
  l13_l12_nullDerefBool_19: boolean,
  l13_l12_nullDerefBool_2: boolean,
  l13_l12_nullDerefBool_20: boolean,
  l13_l12_nullDerefBool_21: boolean,
  l13_l12_nullDerefBool_22: boolean,
  l13_l12_nullDerefBool_23: boolean,
  l13_l12_nullDerefBool_24: boolean,
  l13_l12_nullDerefBool_25: boolean,
  l13_l12_nullDerefBool_26: boolean,
  l13_l12_nullDerefBool_27: boolean,
  l13_l12_nullDerefBool_28: boolean,
  l13_l12_nullDerefBool_29: boolean,
  l13_l12_nullDerefBool_3: boolean,
  l13_l12_nullDerefBool_30: boolean,
  l13_l12_nullDerefBool_31: boolean,
  l13_l12_nullDerefBool_32: boolean,
  l13_l12_nullDerefBool_33: boolean,
  l13_l12_nullDerefBool_34: boolean,
  l13_l12_nullDerefBool_35: boolean,
  l13_l12_nullDerefBool_36: boolean,
  l13_l12_nullDerefBool_37: boolean,
  l13_l12_nullDerefBool_38: boolean,
  l13_l12_nullDerefBool_39: boolean,
  l13_l12_nullDerefBool_4: boolean,
  l13_l12_nullDerefBool_40: boolean,
  l13_l12_nullDerefBool_41: boolean,
  l13_l12_nullDerefBool_42: boolean,
  l13_l12_nullDerefBool_43: boolean,
  l13_l12_nullDerefBool_44: boolean,
  l13_l12_nullDerefBool_45: boolean,
  l13_l12_nullDerefBool_46: boolean,
  l13_l12_nullDerefBool_47: boolean,
  l13_l12_nullDerefBool_48: boolean,
  l13_l12_nullDerefBool_49: boolean,
  l13_l12_nullDerefBool_5: boolean,
  l13_l12_nullDerefBool_50: boolean,
  l13_l12_nullDerefBool_51: boolean,
  l13_l12_nullDerefBool_52: boolean,
  l13_l12_nullDerefBool_53: boolean,
  l13_l12_nullDerefBool_54: boolean,
  l13_l12_nullDerefBool_55: boolean,
  l13_l12_nullDerefBool_56: boolean,
  l13_l12_nullDerefBool_57: boolean,
  l13_l12_nullDerefBool_58: boolean,
  l13_l12_nullDerefBool_59: boolean,
  l13_l12_nullDerefBool_6: boolean,
  l13_l12_nullDerefBool_60: boolean,
  l13_l12_nullDerefBool_61: boolean,
  l13_l12_nullDerefBool_62: boolean,
  l13_l12_nullDerefBool_63: boolean,
  l13_l12_nullDerefBool_64: boolean,
  l13_l12_nullDerefBool_65: boolean,
  l13_l12_nullDerefBool_66: boolean,
  l13_l12_nullDerefBool_67: boolean,
  l13_l12_nullDerefBool_68: boolean,
  l13_l12_nullDerefBool_69: boolean,
  l13_l12_nullDerefBool_7: boolean,
  l13_l12_nullDerefBool_70: boolean,
  l13_l12_nullDerefBool_71: boolean,
  l13_l12_nullDerefBool_72: boolean,
  l13_l12_nullDerefBool_73: boolean,
  l13_l12_nullDerefBool_74: boolean,
  l13_l12_nullDerefBool_75: boolean,
  l13_l12_nullDerefBool_76: boolean,
  l13_l12_nullDerefBool_77: boolean,
  l13_l12_nullDerefBool_78: boolean,
  l13_l12_nullDerefBool_79: boolean,
  l13_l12_nullDerefBool_8: boolean,
  l13_l12_nullDerefBool_80: boolean,
  l13_l12_nullDerefBool_81: boolean,
  l13_l12_nullDerefBool_82: boolean,
  l13_l12_nullDerefBool_83: boolean,
  l13_l12_nullDerefBool_9: boolean,
  l13_l12_prevTemp_0: BinHeapNode + null,
  l13_l12_prevTemp_1: BinHeapNode + null,
  l13_l12_prevTemp_10: BinHeapNode + null,
  l13_l12_prevTemp_11: BinHeapNode + null,
  l13_l12_prevTemp_2: BinHeapNode + null,
  l13_l12_prevTemp_3: BinHeapNode + null,
  l13_l12_prevTemp_4: BinHeapNode + null,
  l13_l12_prevTemp_5: BinHeapNode + null,
  l13_l12_prevTemp_6: BinHeapNode + null,
  l13_l12_prevTemp_7: BinHeapNode + null,
  l13_l12_prevTemp_8: BinHeapNode + null,
  l13_l12_prevTemp_9: BinHeapNode + null,
  l13_l12_temp_0: BinHeapNode + null,
  l13_l12_temp_1: BinHeapNode + null,
  l13_l12_temp_10: BinHeapNode + null,
  l13_l12_temp_11: BinHeapNode + null,
  l13_l12_temp_2: BinHeapNode + null,
  l13_l12_temp_3: BinHeapNode + null,
  l13_l12_temp_4: BinHeapNode + null,
  l13_l12_temp_5: BinHeapNode + null,
  l13_l12_temp_6: BinHeapNode + null,
  l13_l12_temp_7: BinHeapNode + null,
  l13_l12_temp_8: BinHeapNode + null,
  l13_l12_temp_9: BinHeapNode + null,
  l13_nullDerefBool_0: boolean,
  l13_nullDerefBool_1: boolean,
  l13_nullDerefBool_2: boolean,
  l13_nullDerefBool_3: boolean,
  l13_nullDerefBool_4: boolean,
  l13_nullDerefBool_5: boolean,
  l13_temp_0_0: BinHeapNode + null,
  l13_temp_0_1: BinHeapNode + null,
  nextData_0: ( Data ) -> one ( Data + null ),
  nodes_0: ( BinHeap ) -> ( BinHeapNode ),
  nodes_1: ( BinHeap ) -> ( BinHeapNode ),
  bparent_0,fparent_0: ( BinHeapNode ) -> lone ( BinHeapNode + null ),
  parent_1: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  parent_10: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  parent_2: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  parent_3: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  parent_4: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  parent_5: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  parent_6: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  parent_7: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  parent_8: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  parent_9: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  bsibling_0,fsibling_0: ( BinHeapNode ) -> lone ( BinHeapNode + null ),
  sibling_1: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_10: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_11: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_12: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_13: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_14: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_15: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_16: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_17: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_18: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_19: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_2: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_20: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_21: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_22: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_23: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_24: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_25: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_26: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_27: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_28: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_29: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_3: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_30: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_31: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_32: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_33: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_34: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_35: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_36: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_37: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_38: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_39: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_4: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_40: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_41: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_5: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_6: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_7: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_8: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  sibling_9: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  size_0: ( BinHeap ) -> one ( Int ),
  size_1: ( BinHeap ) -> one ( Int ),
  thiz_0: BinHeap,
  throw_0: Throwable + null,
  throw_1: Throwable + null,
  throw_10: Throwable + null,
  throw_11: Throwable + null,
  throw_12: Throwable + null,
  throw_13: Throwable + null,
  throw_14: Throwable + null,
  throw_15: Throwable + null,
  throw_16: Throwable + null,
  throw_17: Throwable + null,
  throw_18: Throwable + null,
  throw_19: Throwable + null,
  throw_2: Throwable + null,
  throw_20: Throwable + null,
  throw_21: Throwable + null,
  throw_22: Throwable + null,
  throw_23: Throwable + null,
  throw_24: Throwable + null,
  throw_25: Throwable + null,
  throw_26: Throwable + null,
  throw_27: Throwable + null,
  throw_28: Throwable + null,
  throw_29: Throwable + null,
  throw_3: Throwable + null,
  throw_30: Throwable + null,
  throw_31: Throwable + null,
  throw_32: Throwable + null,
  throw_33: Throwable + null,
  throw_34: Throwable + null,
  throw_35: Throwable + null,
  throw_36: Throwable + null,
  throw_37: Throwable + null,
  throw_38: Throwable + null,
  throw_39: Throwable + null,
  throw_4: Throwable + null,
  throw_40: Throwable + null,
  throw_41: Throwable + null,
  throw_42: Throwable + null,
  throw_43: Throwable + null,
  throw_44: Throwable + null,
  throw_45: Throwable + null,
  throw_46: Throwable + null,
  throw_5: Throwable + null,
  throw_6: Throwable + null,
  throw_7: Throwable + null,
  throw_8: Throwable + null,
  throw_9: Throwable + null
}


fact {
  precondition_BinHeap_insert_0[(QF.fchild_0+QF.bchild_0),
                               QF.data_value_0,
                               QF.degree_0,
                               QF.element_0,
                               QF.fresh_node_0,
                               QF.head_0,
                               QF.nextData_0,
                               QF.nodes_0,
                               (QF.fparent_0+QF.bparent_0),
                               (QF.fsibling_0+QF.bsibling_0),
                               QF.size_0,
                               QF.thiz_0,
                               QF.throw_0]

}

fact {
  BinHeap_insert_0[QF.thiz_0,
                  QF.throw_0,
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
                  QF.throw_25,
                  QF.throw_26,
                  QF.throw_27,
                  QF.throw_28,
                  QF.throw_29,
                  QF.throw_30,
                  QF.throw_31,
                  QF.throw_32,
                  QF.throw_33,
                  QF.throw_34,
                  QF.throw_35,
                  QF.throw_36,
                  QF.throw_37,
                  QF.throw_38,
                  QF.throw_39,
                  QF.throw_40,
                  QF.throw_41,
                  QF.throw_42,
                  QF.throw_43,
                  QF.throw_44,
                  QF.throw_45,
                  QF.throw_46,
                  QF.fresh_node_0,
                  QF.data_value_0,
                  QF.head_0,
                  QF.head_1,
                  QF.head_2,
                  QF.head_3,
                  QF.head_4,
                  QF.head_5,
                  QF.head_6,
                  QF.head_7,
                  QF.head_8,
                  QF.head_9,
                  QF.head_10,
                  QF.head_11,
                  QF.head_12,
                  QF.head_13,
                  QF.head_14,
                  QF.head_15,
                  QF.head_16,
                  QF.head_17,
                  QF.head_18,
                  QF.head_19,
                  QF.head_20,
                  QF.degree_0,
                  QF.degree_1,
                  QF.degree_2,
                  QF.degree_3,
                  QF.degree_4,
                  QF.degree_5,
                  QF.degree_6,
                  QF.degree_7,
                  QF.degree_8,
                  QF.degree_9,
                  QF.degree_10,
                  (QF.fsibling_0+QF.bsibling_0),
                  QF.sibling_1,
                  QF.sibling_2,
                  QF.sibling_3,
                  QF.sibling_4,
                  QF.sibling_5,
                  QF.sibling_6,
                  QF.sibling_7,
                  QF.sibling_8,
                  QF.sibling_9,
                  QF.sibling_10,
                  QF.sibling_11,
                  QF.sibling_12,
                  QF.sibling_13,
                  QF.sibling_14,
                  QF.sibling_15,
                  QF.sibling_16,
                  QF.sibling_17,
                  QF.sibling_18,
                  QF.sibling_19,
                  QF.sibling_20,
                  QF.sibling_21,
                  QF.sibling_22,
                  QF.sibling_23,
                  QF.sibling_24,
                  QF.sibling_25,
                  QF.sibling_26,
                  QF.sibling_27,
                  QF.sibling_28,
                  QF.sibling_29,
                  QF.sibling_30,
                  QF.sibling_31,
                  QF.sibling_32,
                  QF.sibling_33,
                  QF.sibling_34,
                  QF.sibling_35,
                  QF.sibling_36,
                  QF.sibling_37,
                  QF.sibling_38,
                  QF.sibling_39,
                  QF.sibling_40,
                  QF.sibling_41,
                  QF.element_0,
                  QF.element_1,
                  (QF.fchild_0+QF.bchild_0),
                  QF.child_1,
                  QF.child_2,
                  QF.child_3,
                  QF.child_4,
                  QF.child_5,
                  QF.child_6,
                  QF.child_7,
                  QF.child_8,
                  QF.child_9,
                  QF.child_10,
                  (QF.fparent_0+QF.bparent_0),
                  QF.parent_1,
                  QF.parent_2,
                  QF.parent_3,
                  QF.parent_4,
                  QF.parent_5,
                  QF.parent_6,
                  QF.parent_7,
                  QF.parent_8,
                  QF.parent_9,
                  QF.parent_10,
                  QF.size_0,
                  QF.size_1,
                  QF.l13_temp_0_0,
                  QF.l13_temp_0_1,
                  QF.l13_nullDerefBool_0,
                  QF.l13_nullDerefBool_1,
                  QF.l13_nullDerefBool_2,
                  QF.l13_nullDerefBool_3,
                  QF.l13_nullDerefBool_4,
                  QF.l13_nullDerefBool_5,
                  QF.l13_l12_nextTemp_0,
                  QF.l13_l12_nextTemp_1,
                  QF.l13_l12_nextTemp_2,
                  QF.l13_l12_nextTemp_3,
                  QF.l13_l12_nextTemp_4,
                  QF.l13_l12_nextTemp_5,
                  QF.l13_l12_nextTemp_6,
                  QF.l13_l12_nextTemp_7,
                  QF.l13_l12_nextTemp_8,
                  QF.l13_l12_nextTemp_9,
                  QF.l13_l12_nextTemp_10,
                  QF.l13_l12_nextTemp_11,
                  QF.l13_l12_l2_l0_result_0,
                  QF.l13_l12_l2_l0_result_1,
                  QF.l13_l12_l2_l0_result_2,
                  QF.l13_l12_l2_nullDerefBool_0,
                  QF.l13_l12_l2_nullDerefBool_1,
                  QF.l13_l12_l3_lt_0,
                  QF.l13_l12_l3_lt_1,
                  QF.l13_l12_l11_lt_0,
                  QF.l13_l12_l11_lt_1,
                  QF.l13_l12_l9_lte_0,
                  QF.l13_l12_l9_lte_1,
                  QF.l13_l12_l9_lte_2,
                  QF.l13_l12_l4_l0_nullDerefBool_0,
                  QF.l13_l12_l4_l0_nullDerefBool_1,
                  QF.l13_l12_l6_lte_0,
                  QF.l13_l12_l6_lte_1,
                  QF.l13_l12_l6_lte_2,
                  QF.l13_l12_l9_lt_0,
                  QF.l13_l12_l9_lt_1,
                  QF.l13_l12_l5_l0_result_0,
                  QF.l13_l12_l5_l0_result_1,
                  QF.l13_l12_l5_l0_result_2,
                  QF.l13_l12_l8_lte_0,
                  QF.l13_l12_l8_lte_1,
                  QF.l13_l12_l8_lte_2,
                  QF.l13_l12_l8_l0_nullDerefBool_0,
                  QF.l13_l12_l8_l0_nullDerefBool_1,
                  QF.l13_l12_l8_nullDerefBool_0,
                  QF.l13_l12_l8_nullDerefBool_1,
                  QF.l13_l12_l10_lt_0,
                  QF.l13_l12_l10_lt_1,
                  QF.l13_l12_l10_lte_0,
                  QF.l13_l12_l10_lte_1,
                  QF.l13_l12_l10_lte_2,
                  QF.l13_l12_l7_lte_0,
                  QF.l13_l12_l7_lte_1,
                  QF.l13_l12_l7_lte_2,
                  QF.l13_l12_l6_l0_nullDerefBool_0,
                  QF.l13_l12_l6_l0_nullDerefBool_1,
                  QF.l13_l12_l4_lt_0,
                  QF.l13_l12_l4_lt_1,
                  QF.l13_l12_l2_lte_0,
                  QF.l13_l12_l2_lte_1,
                  QF.l13_l12_l2_lte_2,
                  QF.l13_l12_l7_l0_result_0,
                  QF.l13_l12_l7_l0_result_1,
                  QF.l13_l12_l7_l0_result_2,
                  QF.l13_l12_l2_lt_0,
                  QF.l13_l12_l2_lt_1,
                  QF.l13_l12_l4_nullDerefBool_0,
                  QF.l13_l12_l4_nullDerefBool_1,
                  QF.l13_l12_l5_nullDerefBool_0,
                  QF.l13_l12_l5_nullDerefBool_1,
                  QF.l13_l12_l3_l0_nullDerefBool_0,
                  QF.l13_l12_l3_l0_nullDerefBool_1,
                  QF.l13_l12_temp_0,
                  QF.l13_l12_temp_1,
                  QF.l13_l12_temp_2,
                  QF.l13_l12_temp_3,
                  QF.l13_l12_temp_4,
                  QF.l13_l12_temp_5,
                  QF.l13_l12_temp_6,
                  QF.l13_l12_temp_7,
                  QF.l13_l12_temp_8,
                  QF.l13_l12_temp_9,
                  QF.l13_l12_temp_10,
                  QF.l13_l12_temp_11,
                  QF.l13_l12_l1_nullDerefBool_0,
                  QF.l13_l12_l1_nullDerefBool_1,
                  QF.l13_l12_l1_nullDerefBool_2,
                  QF.l13_l12_l1_nullDerefBool_3,
                  QF.l13_l12_l1_nullDerefBool_4,
                  QF.l13_l12_l1_nullDerefBool_5,
                  QF.l13_l12_l1_nullDerefBool_6,
                  QF.l13_l12_l1_nullDerefBool_7,
                  QF.l13_l12_l1_nullDerefBool_8,
                  QF.l13_l12_l1_nullDerefBool_9,
                  QF.l13_l12_l1_nullDerefBool_10,
                  QF.l13_l12_l1_nullDerefBool_11,
                  QF.l13_l12_l1_nullDerefBool_12,
                  QF.l13_l12_l1_nullDerefBool_13,
                  QF.l13_l12_l1_nullDerefBool_14,
                  QF.l13_l12_l1_nullDerefBool_15,
                  QF.l13_l12_l1_nullDerefBool_16,
                  QF.l13_l12_l1_nullDerefBool_17,
                  QF.l13_l12_l1_nullDerefBool_18,
                  QF.l13_l12_l1_nullDerefBool_19,
                  QF.l13_l12_l1_nullDerefBool_20,
                  QF.l13_l12_l1_nullDerefBool_21,
                  QF.l13_l12_l1_nullDerefBool_22,
                  QF.l13_l12_l1_nullDerefBool_23,
                  QF.l13_l12_l1_nullDerefBool_24,
                  QF.l13_l12_l1_nullDerefBool_25,
                  QF.l13_l12_l1_nullDerefBool_26,
                  QF.l13_l12_l1_nullDerefBool_27,
                  QF.l13_l12_l1_nullDerefBool_28,
                  QF.l13_l12_l1_nullDerefBool_29,
                  QF.l13_l12_l1_nullDerefBool_30,
                  QF.l13_l12_l1_nullDerefBool_31,
                  QF.l13_l12_l1_nullDerefBool_32,
                  QF.l13_l12_l1_nullDerefBool_33,
                  QF.l13_l12_l1_nullDerefBool_34,
                  QF.l13_l12_l1_nullDerefBool_35,
                  QF.l13_l12_l1_nullDerefBool_36,
                  QF.l13_l12_l1_nullDerefBool_37,
                  QF.l13_l12_l1_nullDerefBool_38,
                  QF.l13_l12_l1_nullDerefBool_39,
                  QF.l13_l12_l1_nullDerefBool_40,
                  QF.l13_l12_l1_nullDerefBool_41,
                  QF.l13_l12_l1_nullDerefBool_42,
                  QF.l13_l12_l1_nullDerefBool_43,
                  QF.l13_l12_l1_nullDerefBool_44,
                  QF.l13_l12_l1_nullDerefBool_45,
                  QF.l13_l12_l1_nullDerefBool_46,
                  QF.l13_l12_l1_nullDerefBool_47,
                  QF.l13_l12_l1_nullDerefBool_48,
                  QF.l13_l12_l1_nullDerefBool_49,
                  QF.l13_l12_l1_nullDerefBool_50,
                  QF.l13_l12_l1_nullDerefBool_51,
                  QF.l13_l12_l1_nullDerefBool_52,
                  QF.l13_l12_l1_nullDerefBool_53,
                  QF.l13_l12_l1_nullDerefBool_54,
                  QF.l13_l12_l1_nullDerefBool_55,
                  QF.l13_l12_l1_nullDerefBool_56,
                  QF.l13_l12_l1_nullDerefBool_57,
                  QF.l13_l12_l1_nullDerefBool_58,
                  QF.l13_l12_l1_nullDerefBool_59,
                  QF.l13_l12_l1_nullDerefBool_60,
                  QF.l13_l12_l1_nullDerefBool_61,
                  QF.l13_l12_l1_nullDerefBool_62,
                  QF.l13_l12_l1_nullDerefBool_63,
                  QF.l13_l12_l1_nullDerefBool_64,
                  QF.l13_l12_l1_nullDerefBool_65,
                  QF.l13_l12_l1_nullDerefBool_66,
                  QF.l13_l12_l1_nullDerefBool_67,
                  QF.l13_l12_l1_nullDerefBool_68,
                  QF.l13_l12_l1_nullDerefBool_69,
                  QF.l13_l12_l1_nullDerefBool_70,
                  QF.l13_l12_l1_nullDerefBool_71,
                  QF.l13_l12_l1_nullDerefBool_72,
                  QF.l13_l12_l1_nullDerefBool_73,
                  QF.l13_l12_l1_nullDerefBool_74,
                  QF.l13_l12_l1_nullDerefBool_75,
                  QF.l13_l12_l1_nullDerefBool_76,
                  QF.l13_l12_l1_nullDerefBool_77,
                  QF.l13_l12_l1_nullDerefBool_78,
                  QF.l13_l12_l1_nullDerefBool_79,
                  QF.l13_l12_l1_nullDerefBool_80,
                  QF.l13_l12_l1_nullDerefBool_81,
                  QF.l13_l12_l1_nullDerefBool_82,
                  QF.l13_l12_l1_nullDerefBool_83,
                  QF.l13_l12_l1_nullDerefBool_84,
                  QF.l13_l12_l1_nullDerefBool_85,
                  QF.l13_l12_l3_lte_0,
                  QF.l13_l12_l3_lte_1,
                  QF.l13_l12_l3_lte_2,
                  QF.l13_l12_l5_lt_0,
                  QF.l13_l12_l5_lt_1,
                  QF.l13_l12_l5_l0_nullDerefBool_0,
                  QF.l13_l12_l5_l0_nullDerefBool_1,
                  QF.l13_l12_lte_0,
                  QF.l13_l12_lte_1,
                  QF.l13_l12_lte_2,
                  QF.l13_l12_lte_3,
                  QF.l13_l12_lte_4,
                  QF.l13_l12_lte_5,
                  QF.l13_l12_lte_6,
                  QF.l13_l12_lte_7,
                  QF.l13_l12_lte_8,
                  QF.l13_l12_lte_9,
                  QF.l13_l12_lte_10,
                  QF.l13_l12_l11_nullDerefBool_0,
                  QF.l13_l12_l11_nullDerefBool_1,
                  QF.l13_l12_l9_l0_nullDerefBool_0,
                  QF.l13_l12_l9_l0_nullDerefBool_1,
                  QF.l13_l12_l9_nullDerefBool_0,
                  QF.l13_l12_l9_nullDerefBool_1,
                  QF.l13_l12_l10_nullDerefBool_0,
                  QF.l13_l12_l10_nullDerefBool_1,
                  QF.l13_l12_l10_l0_nullDerefBool_0,
                  QF.l13_l12_l10_l0_nullDerefBool_1,
                  QF.l13_l12_l6_nullDerefBool_0,
                  QF.l13_l12_l6_nullDerefBool_1,
                  QF.l13_l12_l8_lt_0,
                  QF.l13_l12_l8_lt_1,
                  QF.l13_l12_l3_l0_result_0,
                  QF.l13_l12_l3_l0_result_1,
                  QF.l13_l12_l3_l0_result_2,
                  QF.l13_l12_l6_lt_0,
                  QF.l13_l12_l6_lt_1,
                  QF.l13_l12_l11_l0_result_0,
                  QF.l13_l12_l11_l0_result_1,
                  QF.l13_l12_l11_l0_result_2,
                  QF.l13_l12_l11_lte_0,
                  QF.l13_l12_l11_lte_1,
                  QF.l13_l12_l11_lte_2,
                  QF.l13_l12_l2_l0_nullDerefBool_0,
                  QF.l13_l12_l2_l0_nullDerefBool_1,
                  QF.l13_l12_prevTemp_0,
                  QF.l13_l12_prevTemp_1,
                  QF.l13_l12_prevTemp_2,
                  QF.l13_l12_prevTemp_3,
                  QF.l13_l12_prevTemp_4,
                  QF.l13_l12_prevTemp_5,
                  QF.l13_l12_prevTemp_6,
                  QF.l13_l12_prevTemp_7,
                  QF.l13_l12_prevTemp_8,
                  QF.l13_l12_prevTemp_9,
                  QF.l13_l12_prevTemp_10,
                  QF.l13_l12_prevTemp_11,
                  QF.l13_l12_l4_lte_0,
                  QF.l13_l12_l4_lte_1,
                  QF.l13_l12_l4_lte_2,
                  QF.l13_l12_l7_lt_0,
                  QF.l13_l12_l7_lt_1,
                  QF.l13_l12_l6_l0_result_0,
                  QF.l13_l12_l6_l0_result_1,
                  QF.l13_l12_l6_l0_result_2,
                  QF.l13_l12_l3_nullDerefBool_0,
                  QF.l13_l12_l3_nullDerefBool_1,
                  QF.l13_l12_l10_l0_result_0,
                  QF.l13_l12_l10_l0_result_1,
                  QF.l13_l12_l10_l0_result_2,
                  QF.l13_l12_l11_l0_nullDerefBool_0,
                  QF.l13_l12_l11_l0_nullDerefBool_1,
                  QF.l13_l12_l5_lte_0,
                  QF.l13_l12_l5_lte_1,
                  QF.l13_l12_l5_lte_2,
                  QF.l13_l12_nullDerefBool_0,
                  QF.l13_l12_nullDerefBool_1,
                  QF.l13_l12_nullDerefBool_2,
                  QF.l13_l12_nullDerefBool_3,
                  QF.l13_l12_nullDerefBool_4,
                  QF.l13_l12_nullDerefBool_5,
                  QF.l13_l12_nullDerefBool_6,
                  QF.l13_l12_nullDerefBool_7,
                  QF.l13_l12_nullDerefBool_8,
                  QF.l13_l12_nullDerefBool_9,
                  QF.l13_l12_nullDerefBool_10,
                  QF.l13_l12_nullDerefBool_11,
                  QF.l13_l12_nullDerefBool_12,
                  QF.l13_l12_nullDerefBool_13,
                  QF.l13_l12_nullDerefBool_14,
                  QF.l13_l12_nullDerefBool_15,
                  QF.l13_l12_nullDerefBool_16,
                  QF.l13_l12_nullDerefBool_17,
                  QF.l13_l12_nullDerefBool_18,
                  QF.l13_l12_nullDerefBool_19,
                  QF.l13_l12_nullDerefBool_20,
                  QF.l13_l12_nullDerefBool_21,
                  QF.l13_l12_nullDerefBool_22,
                  QF.l13_l12_nullDerefBool_23,
                  QF.l13_l12_nullDerefBool_24,
                  QF.l13_l12_nullDerefBool_25,
                  QF.l13_l12_nullDerefBool_26,
                  QF.l13_l12_nullDerefBool_27,
                  QF.l13_l12_nullDerefBool_28,
                  QF.l13_l12_nullDerefBool_29,
                  QF.l13_l12_nullDerefBool_30,
                  QF.l13_l12_nullDerefBool_31,
                  QF.l13_l12_nullDerefBool_32,
                  QF.l13_l12_nullDerefBool_33,
                  QF.l13_l12_nullDerefBool_34,
                  QF.l13_l12_nullDerefBool_35,
                  QF.l13_l12_nullDerefBool_36,
                  QF.l13_l12_nullDerefBool_37,
                  QF.l13_l12_nullDerefBool_38,
                  QF.l13_l12_nullDerefBool_39,
                  QF.l13_l12_nullDerefBool_40,
                  QF.l13_l12_nullDerefBool_41,
                  QF.l13_l12_nullDerefBool_42,
                  QF.l13_l12_nullDerefBool_43,
                  QF.l13_l12_nullDerefBool_44,
                  QF.l13_l12_nullDerefBool_45,
                  QF.l13_l12_nullDerefBool_46,
                  QF.l13_l12_nullDerefBool_47,
                  QF.l13_l12_nullDerefBool_48,
                  QF.l13_l12_nullDerefBool_49,
                  QF.l13_l12_nullDerefBool_50,
                  QF.l13_l12_nullDerefBool_51,
                  QF.l13_l12_nullDerefBool_52,
                  QF.l13_l12_nullDerefBool_53,
                  QF.l13_l12_nullDerefBool_54,
                  QF.l13_l12_nullDerefBool_55,
                  QF.l13_l12_nullDerefBool_56,
                  QF.l13_l12_nullDerefBool_57,
                  QF.l13_l12_nullDerefBool_58,
                  QF.l13_l12_nullDerefBool_59,
                  QF.l13_l12_nullDerefBool_60,
                  QF.l13_l12_nullDerefBool_61,
                  QF.l13_l12_nullDerefBool_62,
                  QF.l13_l12_nullDerefBool_63,
                  QF.l13_l12_nullDerefBool_64,
                  QF.l13_l12_nullDerefBool_65,
                  QF.l13_l12_nullDerefBool_66,
                  QF.l13_l12_nullDerefBool_67,
                  QF.l13_l12_nullDerefBool_68,
                  QF.l13_l12_nullDerefBool_69,
                  QF.l13_l12_nullDerefBool_70,
                  QF.l13_l12_nullDerefBool_71,
                  QF.l13_l12_nullDerefBool_72,
                  QF.l13_l12_nullDerefBool_73,
                  QF.l13_l12_nullDerefBool_74,
                  QF.l13_l12_nullDerefBool_75,
                  QF.l13_l12_nullDerefBool_76,
                  QF.l13_l12_nullDerefBool_77,
                  QF.l13_l12_nullDerefBool_78,
                  QF.l13_l12_nullDerefBool_79,
                  QF.l13_l12_nullDerefBool_80,
                  QF.l13_l12_nullDerefBool_81,
                  QF.l13_l12_nullDerefBool_82,
                  QF.l13_l12_nullDerefBool_83,
                  QF.l13_l12_l1_temp1_0,
                  QF.l13_l12_l1_temp1_1,
                  QF.l13_l12_l1_temp1_2,
                  QF.l13_l12_l1_temp1_3,
                  QF.l13_l12_l1_temp1_4,
                  QF.l13_l12_l1_temp1_5,
                  QF.l13_l12_l1_temp1_6,
                  QF.l13_l12_l1_temp1_7,
                  QF.l13_l12_l1_temp1_8,
                  QF.l13_l12_l1_temp1_9,
                  QF.l13_l12_l1_temp1_10,
                  QF.l13_l12_l1_temp1_11,
                  QF.l13_l12_l1_temp1_12,
                  QF.l13_l12_l1_temp1_13,
                  QF.l13_l12_l1_temp1_14,
                  QF.l13_l12_l1_temp1_15,
                  QF.l13_l12_l1_temp1_16,
                  QF.l13_l12_l1_temp1_17,
                  QF.l13_l12_l1_temp1_18,
                  QF.l13_l12_l1_temp1_19,
                  QF.l13_l12_l1_temp1_20,
                  QF.l13_l12_l1_temp1_21,
                  QF.l13_l12_l1_temp1_22,
                  QF.l13_l12_l4_l0_result_0,
                  QF.l13_l12_l4_l0_result_1,
                  QF.l13_l12_l4_l0_result_2,
                  QF.l13_l12_l1_temp2_0,
                  QF.l13_l12_l1_temp2_1,
                  QF.l13_l12_l1_temp2_2,
                  QF.l13_l12_l1_temp2_3,
                  QF.l13_l12_l1_temp2_4,
                  QF.l13_l12_l1_temp2_5,
                  QF.l13_l12_l1_temp2_6,
                  QF.l13_l12_l1_temp2_7,
                  QF.l13_l12_l1_temp2_8,
                  QF.l13_l12_l1_temp2_9,
                  QF.l13_l12_l1_temp2_10,
                  QF.l13_l12_l1_temp2_11,
                  QF.l13_l12_l9_l0_result_0,
                  QF.l13_l12_l9_l0_result_1,
                  QF.l13_l12_l9_l0_result_2,
                  QF.l13_l12_l8_l0_result_0,
                  QF.l13_l12_l8_l0_result_1,
                  QF.l13_l12_l8_l0_result_2,
                  QF.l13_l12_l7_nullDerefBool_0,
                  QF.l13_l12_l7_nullDerefBool_1,
                  QF.l13_l12_l7_l0_nullDerefBool_0,
                  QF.l13_l12_l7_l0_nullDerefBool_1,
                  QF.l13_l12_l1_tmp_0,
                  QF.l13_l12_l1_tmp_1,
                  QF.l13_l12_l1_tmp_2,
                  QF.l13_l12_l1_tmp_3,
                  QF.l13_l12_l1_tmp_4,
                  QF.l13_l12_l1_tmp_5,
                  QF.l13_l12_l1_tmp_6,
                  QF.l13_l12_l1_tmp_7,
                  QF.l13_l12_l1_tmp_8,
                  QF.l13_l12_l1_tmp_9,
                  QF.l13_l12_l1_tmp_10]

}

fact {
  havocVariable2[QF.nodes_1]
}

fact {
  BinHeapCondition64[QF.child_10,
                    QF.head_20,
                    QF.nodes_1,
                    QF.sibling_41,
                    QF.thiz_0]

}

assert BinHeap_m3{
  postcondition_BinHeap_insert_0[QF.child_10,
                                QF.data_value_0,
                                QF.degree_10,
                                QF.element_1,
                                QF.fresh_node_0,
                                QF.head_20,
                                QF.nextData_0,
                                QF.nodes_0,
                                QF.nodes_1,
                                QF.parent_10,
                                QF.sibling_41,
                                QF.size_1,
                                QF.thiz_0,
                                QF.thiz_0,
                                QF.throw_46]
}
check BinHeap_m3 for 0 but 
                 exactly 1 BinHeap, 
                 exactly 15 BinHeapNode,
                 exactly 1 D0,
                 exactly 1 D1,
                 exactly 1 D2,
                 exactly 1 D3,
                 exactly 1 D4,
                 exactly 1 D5,
                 exactly 1 D6,
                 exactly 1 D7,
                 exactly 1 D8,
                 exactly 1 D9,
                 exactly 1 D10,
                 exactly 1 D11,
                 exactly 1 D12,
                 exactly 1 D13,
                 exactly 1 D14,
                 5 int  



one sig N0,N1,N2,N3,N4,N5,N6,N7,N8,N9,N10,N11,N12,N13,N14 extends BinHeapNode {} 

fun globalMin[s : set (BinHeapNode + BinHeap)] : lone (BinHeapNode + BinHeap) {
	s - s.^(BinHeap->N0 + node_next[])
}

fun minP[n : BinHeapNode] : BinHeapNode {
	globalMin[(QF.fsibling_0 + QF.fchild_0 + QF.fparent_0 + QF.head_0).n ]
}

pred data_lte[e1,e2: Data] { 
   e1 in data_prevs[e2]  or e1 = e2
} 

fun FReach[] : set univ {
	(QF.thiz_0).(QF.head_0).*(QF.fsibling_0 + QF.fchild_0 + QF.fparent_0) - null
}

fact { 
let 	
  fsibling = QF.fsibling_0,
  bsibling = QF.bsibling_0,
  fchild  = QF.fchild_0,
  bchild  = QF.bchild_0,
  fparent = QF.fparent_0,
  bparent = QF.bparent_0 | {
		
  no ((fsibling.univ) & (bsibling.univ))  
  BinHeapNode = fsibling.univ + bsibling.univ 

  no ((fchild.univ) & (bchild.univ))  
  BinHeapNode = fchild.univ + bchild.univ 

  no ((fparent.univ) & (bparent.univ))   
  BinHeapNode = fparent.univ + bparent.univ
				
}}

fact orderBinHeapNodeCondition_c{
( all disj o1, o2, o3 : BinHeapNode |
  let a = minP[o1] | let b = minP[o2] | let c = minP[o3] |
  ( o1+o2+o3 in FReach[] and
    some a and some b and some c and a = b and b=c and a in BinHeapNode and
    o1 = a.(QF.fsibling_0) and
    o2 = a.(QF.fchild_0) and
    o3 = a.(QF.fparent_0)
  ) implies  (o2 = o1.node_next[] and o3 = o2.node_next[])
)
&&
( all disj o1, o2 : BinHeapNode |
  let a = minP[o1] | let b = minP[o2] |
	( 	o1+o2 in FReach[] 
		and	some a and some b and a = b and a in BinHeapNode
		and (no o3 : BinHeapNode | o3 != o1 and o3 != o2 and minP[o3] = a) 
		and	o1 = a.(QF.fsibling_0)
	) implies o2 = o1.node_next[]
)
&&
( all disj o1, o2 : BinHeapNode |
  let a = minP[o1] | let b = minP[o2] |
	( 	o1+o2 in FReach[] 
		and	some a and some b and a = b and a in BinHeapNode
		and (no o3 : BinHeapNode | o3 != o1 and o3 != o2 and minP[o3] = a) 
		and o1 != a.(QF.fsibling_0) and o2 != a.(QF.fsibling_0) and o1 = a.(QF.fchild_0)
	) implies o2 = o1.node_next[]
)
}

fact orderBinHeapNodeCondition_d { 
  all disj o1, o2 : BinHeapNode | 
    let a = minP[o1] | let b = minP[o2] | 
      (o1+o2 in FReach[] and some a and some b and 
        a!=b and a+b in BinHeapNode and a in node_prevs[b]) 
           implies o1 in node_prevs[o2]
} 

fact orderBinHeapNodeCondition_e {
  all disj o1, o2 : BinHeapNode | 
    let a = minP[o1] | let b = minP[o2] | 
      (o1+o2 in FReach[] and some a and some b and 
        a in BinHeap and b in BinHeapNode) 
           implies o1 in node_prevs[o2]
}

fact compactBinHeapNode { all o : BinHeapNode | o in FReach[] 
    implies node_prevs[o] in FReach[]
} 

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
//fact ffields_bfields 
fact { 
QF.fparent_0 in N0->null 
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
+N11->null 
+N12->null 
+N13->null 
+N14->null 
 
QF.fsibling_0 in N0->N1 
+N0->null 
+N1->N2 
+N1->N3 
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
+N5->N7 
+N5->N8 
+N5->null 
+N6->N8 
+N6->N9 
+N6->null 
+N7->N9 
+N7->N10 
+N7->null 
+N8->N10 
+N8->N11 
+N8->null 
+N9->N11 
+N9->N12 
+N9->null 
+N10->N13 
+N10->null 
+N11->null 
+N12->null 
+N13->null 
+N14->null 
 
QF.bchild_0 in none->none 
QF.fchild_0 in N0->N1 
+N0->N2 
+N0->null 
+N1->N2 
+N1->N3 
+N1->N4 
+N1->null 
+N2->N4 
+N2->N5 
+N2->null 
+N3->N5 
+N3->N6 
+N3->N7 
+N3->null 
+N4->N6 
+N4->N7 
+N4->N8 
+N4->null 
+N5->N8 
+N5->N9 
+N5->null 
+N6->N9 
+N6->N10 
+N6->null 
+N7->N10 
+N7->N11 
+N7->null 
+N8->N11 
+N8->N12 
+N8->null 
+N9->N12 
+N9->N13 
+N9->null 
+N10->N14 
+N10->null 
+N11->null 
+N12->null 
+N13->null 
+N14->null 
 
QF.bparent_0 in N1->N0 
+N2->N0 
+N2->N1 
+N3->N1 
+N4->N0 
+N4->N1 
+N4->N2 
+N5->N1 
+N5->N2 
+N5->N3 
+N6->N1 
+N6->N3 
+N6->N4 
+N7->N2 
+N7->N3 
+N7->N4 
+N8->N1 
+N8->N3 
+N8->N4 
+N8->N5 
+N9->N2 
+N9->N4 
+N9->N5 
+N9->N6 
+N10->N3 
+N10->N6 
+N10->N7 
+N11->N4 
+N11->N7 
+N11->N8 
+N12->N5 
+N12->N8 
+N12->N9 
+N13->N6 
+N13->N9 
+N14->N10 
 
QF.bsibling_0 in none->none 
} 
// fact int_fields 
fact { 
QF.degree_0 in N0->0 
+N0->1 
+N0->2 
+N0->3 
+N1->0 
+N1->1 
+N1->2 
+N1->3 
+N2->0 
+N2->1 
+N2->2 
+N2->3 
+N3->0 
+N3->1 
+N3->2 
+N3->3 
+N4->0 
+N4->1 
+N4->2 
+N4->3 
+N5->0 
+N5->1 
+N5->2 
+N6->0 
+N6->1 
+N6->2 
+N7->0 
+N7->1 
+N8->0 
+N8->1 
+N9->0 
+N9->1 
+N10->0 
+N10->1 
+N11->0 
+N12->0 
+N13->0 
+N14->0 

} 
//fact data_fields 
fact { 
QF.element_0 in N0->D0 
+N0->D1 
+N0->D2 
+N0->D3 
+N0->D4 
+N0->D5 
+N0->D6 
+N0->D7 
+N0->D8 
+N0->D9 
+N0->D10 
+N0->D11 
+N0->D12 
+N0->D13 
+N0->D14 
+N1->D0 
+N1->D1 
+N1->D2 
+N1->D3 
+N1->D4 
+N1->D5 
+N1->D6 
+N1->D7 
+N1->D8 
+N1->D9 
+N1->D10 
+N1->D11 
+N1->D12 
+N1->D13 
+N1->D14 
+N2->D0 
+N2->D1 
+N2->D2 
+N2->D3 
+N2->D4 
+N2->D5 
+N2->D6 
+N2->D7 
+N2->D8 
+N2->D9 
+N2->D10 
+N2->D11 
+N2->D12 
+N2->D13 
+N2->D14 
+N3->D0 
+N3->D1 
+N3->D2 
+N3->D3 
+N3->D4 
+N3->D5 
+N3->D6 
+N3->D7 
+N3->D8 
+N3->D9 
+N3->D10 
+N3->D11 
+N3->D12 
+N3->D13 
+N3->D14 
+N4->D0 
+N4->D1 
+N4->D2 
+N4->D3 
+N4->D4 
+N4->D5 
+N4->D6 
+N4->D7 
+N4->D8 
+N4->D9 
+N4->D10 
+N4->D11 
+N4->D12 
+N4->D13 
+N4->D14 
+N5->D0 
+N5->D1 
+N5->D2 
+N5->D3 
+N5->D4 
+N5->D5 
+N5->D6 
+N5->D7 
+N5->D8 
+N5->D9 
+N5->D10 
+N5->D11 
+N5->D12 
+N5->D13 
+N5->D14 
+N6->D0 
+N6->D1 
+N6->D2 
+N6->D3 
+N6->D4 
+N6->D5 
+N6->D6 
+N6->D7 
+N6->D8 
+N6->D9 
+N6->D10 
+N6->D11 
+N6->D12 
+N6->D13 
+N6->D14 
+N7->D0 
+N7->D1 
+N7->D2 
+N7->D3 
+N7->D4 
+N7->D5 
+N7->D6 
+N7->D7 
+N7->D8 
+N7->D9 
+N7->D10 
+N7->D11 
+N7->D12 
+N7->D13 
+N7->D14 
+N8->D0 
+N8->D1 
+N8->D2 
+N8->D3 
+N8->D4 
+N8->D5 
+N8->D6 
+N8->D7 
+N8->D8 
+N8->D9 
+N8->D10 
+N8->D11 
+N8->D12 
+N8->D13 
+N8->D14 
+N9->D0 
+N9->D1 
+N9->D2 
+N9->D3 
+N9->D4 
+N9->D5 
+N9->D6 
+N9->D7 
+N9->D8 
+N9->D9 
+N9->D10 
+N9->D11 
+N9->D12 
+N9->D13 
+N9->D14 
+N10->D0 
+N10->D1 
+N10->D2 
+N10->D3 
+N10->D4 
+N10->D5 
+N10->D6 
+N10->D7 
+N10->D8 
+N10->D9 
+N10->D10 
+N10->D11 
+N10->D12 
+N10->D13 
+N10->D14 
+N11->D0 
+N11->D1 
+N11->D2 
+N11->D3 
+N11->D4 
+N11->D5 
+N11->D6 
+N11->D7 
+N11->D8 
+N11->D9 
+N11->D10 
+N11->D11 
+N11->D12 
+N11->D13 
+N11->D14 
+N12->D0 
+N12->D1 
+N12->D2 
+N12->D3 
+N12->D4 
+N12->D5 
+N12->D6 
+N12->D7 
+N12->D8 
+N12->D9 
+N12->D10 
+N12->D11 
+N12->D12 
+N12->D13 
+N12->D14 
+N13->D0 
+N13->D1 
+N13->D2 
+N13->D3 
+N13->D4 
+N13->D5 
+N13->D6 
+N13->D7 
+N13->D8 
+N13->D9 
+N13->D10 
+N13->D11 
+N13->D12 
+N13->D13 
+N13->D14 
+N14->D0 
+N14->D1 
+N14->D2 
+N14->D3 
+N14->D4 
+N14->D5 
+N14->D6 
+N14->D7 
+N14->D8 
+N14->D9 
+N14->D10 
+N14->D11 
+N14->D12 
+N14->D13 
+N14->D14 

} 
//fact root_int_fields 
fact { 
(QF.size_0) in QF.thiz_0->0 
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
+QF.thiz_0->12 
+QF.thiz_0->13 
+QF.thiz_0->14 
+QF.thiz_0->15 

} 
//fact root_node_fields 
fact { 
(QF.head_0) in QF.thiz_0->N0 
+QF.thiz_0->null 

} 
