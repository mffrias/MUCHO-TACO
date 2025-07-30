/* 
 * DynAlloy translator options 
 * --------------------------- 
 * applySimplifications= true
 * assertionId= BinHeap_m2
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




pred BinHeapCondition15[
  z:univ
]{
   not (
     neq[z,
        null]
   )

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

pred BinHeapCondition14[
  z:univ
]{
   neq[z,
      null]

}

pred postcondition_BinHeap_decreaseKey_0[
  child':univ->univ,
  degree':univ->univ,
  element:univ->univ,
  element':univ->univ,
  head':univ->univ,
  k':univ,
  nextData':univ->univ,
  nodes:univ->univ,
  nodes':univ->univ,
  parent':univ->univ,
  sibling':univ->univ,
  size':univ->univ,
  thiz:univ,
  thiz':univ,
  throw':univ,
  x:univ,
  x':univ
]{
   BinHeap_ensures[element,
                  element',
                  k',
                  nodes,
                  nodes',
                  thiz,
                  throw',
                  x,
                  x']
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

pred BinHeap_requires[
  element:univ->univ,
  k:univ,
  nextData:univ->univ,
  nodes:univ->univ,
  thiz:univ,
  x:univ
]{
   isSubset[x,
           thiz.nodes]
   and 
   isSubset[x.element,
           k.(fun_reflexive_closure[nextData])]
   and 
   neq[k,
      null]

}

pred precondition_BinHeap_decreaseKey_0[
  child:univ->univ,
  degree:univ->univ,
  element:univ->univ,
  head:univ->univ,
  k:univ,
  nextData:univ->univ,
  nodes:univ->univ,
  parent:univ->univ,
  sibling:univ->univ,
  size:univ->univ,
  thiz:univ,
  throw:univ,
  x:univ
]{
   equ[throw,
      null]
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
   BinHeap_requires[element,
                   k,
                   nextData,
                   nodes,
                   thiz,
                   x]
   and 
   Data_object_invariant[nextData]

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

pred BinHeapCondition7[
  y:univ
]{
   not (
     isEmptyOrNull[y])

}

pred BinHeapCondition6[
  y:univ
]{
   isEmptyOrNull[y]

}

pred BinHeapCondition10[
  y:univ,
  z:univ
]{
   isEmptyOrNull[y]
   and 
   isEmptyOrNull[z]

}

pred BinHeapCondition2[
  x:univ
]{
   isEmptyOrNull[x]

}

pred BinHeapCondition9[
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

pred BinHeap_ensures[
  element:univ->univ,
  element':univ->univ,
  k':univ,
  nodes:univ->univ,
  nodes':univ->univ,
  thiz:univ,
  throw':univ,
  x:univ,
  x':univ
]{
   (
     {
     some other:BinHeapNode | {
       isSubset[other,
               thiz.nodes']
       and 
       neq[other,
          x']
       and 
       equ[other.element,
          x.element]
     
     }} => {
       equ[(thiz.nodes').element',
          ((thiz.nodes).element)+k']
     
     }else{
       equ[(thiz.nodes').element',
          fun_set_difference[(thiz.nodes).element,x.element]+k']
     
     }
   )
   and 
   equ[throw',
      null]

}

pred BinHeapCondition4[
  x:univ,
  y:univ
]{
   isEmptyOrNull[x]
   and 
   isEmptyOrNull[y]

}

pred BinHeapCondition5[
  x:univ,
  y:univ
]{
   not (
     isEmptyOrNull[x]
     and 
     isEmptyOrNull[y]
   )

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

pred BinHeapCondition12[
  lt:univ
]{
   equ[lt,
      true]

}

pred BinHeapCondition3[
  x:univ
]{
   not (
     isEmptyOrNull[x])

}

pred BinHeapCondition8[
  nullDerefBool:univ,
  throw:univ
]{
   equ[nullDerefBool,
      true]
   and 
   equ[throw,
      null]

}

pred BinHeapCondition13[
  lt:univ
]{
   not (
     equ[lt,
        true]
   )

}

pred BinHeapCondition17[
  b:univ
]{
   not (
     equ[b,
        true]
   )

}

pred BinHeapCondition16[
  b:univ
]{
   equ[b,
      true]

}

pred BinHeapCondition11[
  y:univ,
  z:univ
]{
   not (
     isEmptyOrNull[y]
     and 
     isEmptyOrNull[z]
   )

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

pred DataCondition56[
  thiz:univ
]{
   instanceOf[thiz,
             D11]

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



pred BinHeap_decreaseKey_0[
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
  x_0: BinHeapNode + null,
  k_0: Data + null,
  element_0: ( BinHeapNode ) -> one ( Data + null ),
  element_1: ( BinHeapNode ) -> one ( Data + null ),
  element_2: ( BinHeapNode ) -> one ( Data + null ),
  element_3: ( BinHeapNode ) -> one ( Data + null ),
  element_4: ( BinHeapNode ) -> one ( Data + null ),
  element_5: ( BinHeapNode ) -> one ( Data + null ),
  element_6: ( BinHeapNode ) -> one ( Data + null ),
  element_7: ( BinHeapNode ) -> one ( Data + null ),
  element_8: ( BinHeapNode ) -> one ( Data + null ),
  element_9: ( BinHeapNode ) -> one ( Data + null ),
  element_10: ( BinHeapNode ) -> one ( Data + null ),
  element_11: ( BinHeapNode ) -> one ( Data + null ),
  element_12: ( BinHeapNode ) -> one ( Data + null ),
  element_13: ( BinHeapNode ) -> one ( Data + null ),
  element_14: ( BinHeapNode ) -> one ( Data + null ),
  element_15: ( BinHeapNode ) -> one ( Data + null ),
  element_16: ( BinHeapNode ) -> one ( Data + null ),
  element_17: ( BinHeapNode ) -> one ( Data + null ),
  element_18: ( BinHeapNode ) -> one ( Data + null ),
  element_19: ( BinHeapNode ) -> one ( Data + null ),
  element_20: ( BinHeapNode ) -> one ( Data + null ),
  element_21: ( BinHeapNode ) -> one ( Data + null ),
  parent_0: ( BinHeapNode ) -> one ( BinHeapNode + null ),
  lt_0: boolean,
  lt_1: boolean,
  lt_2: boolean,
  lt_3: boolean,
  lt_4: boolean,
  lt_5: boolean,
  lt_6: boolean,
  lt_7: boolean,
  lt_8: boolean,
  lt_9: boolean,
  lt_10: boolean,
  lt_11: boolean,
  b_0: boolean,
  b_1: boolean,
  b_2: boolean,
  b_3: boolean,
  b_4: boolean,
  b_5: boolean,
  b_6: boolean,
  b_7: boolean,
  b_8: boolean,
  b_9: boolean,
  b_10: boolean,
  b_11: boolean,
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
  z_0: BinHeapNode + null,
  z_1: BinHeapNode + null,
  z_2: BinHeapNode + null,
  z_3: BinHeapNode + null,
  z_4: BinHeapNode + null,
  z_5: BinHeapNode + null,
  z_6: BinHeapNode + null,
  z_7: BinHeapNode + null,
  z_8: BinHeapNode + null,
  z_9: BinHeapNode + null,
  z_10: BinHeapNode + null,
  z_11: BinHeapNode + null,
  y_0: BinHeapNode + null,
  y_1: BinHeapNode + null,
  y_2: BinHeapNode + null,
  y_3: BinHeapNode + null,
  y_4: BinHeapNode + null,
  y_5: BinHeapNode + null,
  y_6: BinHeapNode + null,
  y_7: BinHeapNode + null,
  y_8: BinHeapNode + null,
  y_9: BinHeapNode + null,
  y_10: BinHeapNode + null,
  y_11: BinHeapNode + null,
  l14_result_0: boolean,
  l14_result_1: boolean,
  l14_result_2: boolean,
  l8_nullDerefBool_0: boolean,
  l8_nullDerefBool_1: boolean,
  l9_temp_0: Data + null,
  l9_temp_1: Data + null,
  l13_nullDerefBool_0: boolean,
  l13_nullDerefBool_1: boolean,
  l13_nullDerefBool_2: boolean,
  l13_nullDerefBool_3: boolean,
  l13_nullDerefBool_4: boolean,
  l8_result_0: boolean,
  l8_result_1: boolean,
  l8_result_2: boolean,
  l16_nullDerefBool_0: boolean,
  l16_nullDerefBool_1: boolean,
  l11_nullDerefBool_0: boolean,
  l11_nullDerefBool_1: boolean,
  l11_nullDerefBool_2: boolean,
  l11_nullDerefBool_3: boolean,
  l11_nullDerefBool_4: boolean,
  l0_result_0: boolean,
  l0_result_1: boolean,
  l0_result_2: boolean,
  l0_nullDerefBool_0: boolean,
  l0_nullDerefBool_1: boolean,
  l4_result_0: boolean,
  l4_result_1: boolean,
  l4_result_2: boolean,
  l17_temp_0: Data + null,
  l17_temp_1: Data + null,
  l11_temp_0: Data + null,
  l11_temp_1: Data + null,
  l2_nullDerefBool_0: boolean,
  l2_nullDerefBool_1: boolean,
  l7_nullDerefBool_0: boolean,
  l7_nullDerefBool_1: boolean,
  l7_nullDerefBool_2: boolean,
  l7_nullDerefBool_3: boolean,
  l7_nullDerefBool_4: boolean,
  l6_result_0: boolean,
  l6_result_1: boolean,
  l6_result_2: boolean,
  l18_result_0: boolean,
  l18_result_1: boolean,
  l18_result_2: boolean,
  l19_nullDerefBool_0: boolean,
  l19_nullDerefBool_1: boolean,
  l19_nullDerefBool_2: boolean,
  l19_nullDerefBool_3: boolean,
  l19_nullDerefBool_4: boolean,
  l14_nullDerefBool_0: boolean,
  l14_nullDerefBool_1: boolean,
  l1_temp_0: Data + null,
  l1_temp_1: Data + null,
  l5_temp_0: Data + null,
  l5_temp_1: Data + null,
  l4_nullDerefBool_0: boolean,
  l4_nullDerefBool_1: boolean,
  l10_result_0: boolean,
  l10_result_1: boolean,
  l10_result_2: boolean,
  l20_result_0: boolean,
  l20_result_1: boolean,
  l20_result_2: boolean,
  l9_nullDerefBool_0: boolean,
  l9_nullDerefBool_1: boolean,
  l9_nullDerefBool_2: boolean,
  l9_nullDerefBool_3: boolean,
  l9_nullDerefBool_4: boolean,
  l19_temp_0: Data + null,
  l19_temp_1: Data + null,
  l5_nullDerefBool_0: boolean,
  l5_nullDerefBool_1: boolean,
  l5_nullDerefBool_2: boolean,
  l5_nullDerefBool_3: boolean,
  l5_nullDerefBool_4: boolean,
  l6_nullDerefBool_0: boolean,
  l6_nullDerefBool_1: boolean,
  l15_temp_0: Data + null,
  l15_temp_1: Data + null,
  l16_result_0: boolean,
  l16_result_1: boolean,
  l16_result_2: boolean,
  l18_nullDerefBool_0: boolean,
  l18_nullDerefBool_1: boolean,
  l3_nullDerefBool_0: boolean,
  l3_nullDerefBool_1: boolean,
  l3_nullDerefBool_2: boolean,
  l3_nullDerefBool_3: boolean,
  l3_nullDerefBool_4: boolean,
  l20_nullDerefBool_0: boolean,
  l20_nullDerefBool_1: boolean,
  l15_nullDerefBool_0: boolean,
  l15_nullDerefBool_1: boolean,
  l15_nullDerefBool_2: boolean,
  l15_nullDerefBool_3: boolean,
  l15_nullDerefBool_4: boolean,
  l1_nullDerefBool_0: boolean,
  l1_nullDerefBool_1: boolean,
  l1_nullDerefBool_2: boolean,
  l1_nullDerefBool_3: boolean,
  l1_nullDerefBool_4: boolean,
  l12_nullDerefBool_0: boolean,
  l12_nullDerefBool_1: boolean,
  l13_temp_0: Data + null,
  l13_temp_1: Data + null,
  l12_result_0: boolean,
  l12_result_1: boolean,
  l12_result_2: boolean,
  l7_temp_0: Data + null,
  l7_temp_1: Data + null,
  l2_result_0: boolean,
  l2_result_1: boolean,
  l2_result_2: boolean,
  l3_temp_0: Data + null,
  l3_temp_1: Data + null,
  l17_nullDerefBool_0: boolean,
  l17_nullDerefBool_1: boolean,
  l17_nullDerefBool_2: boolean,
  l17_nullDerefBool_3: boolean,
  l17_nullDerefBool_4: boolean,
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
      BinHeapCondition2[x_0]
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
          BinHeapCondition2[x_0])
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
        element_1=(element_0)++((x_0)->(k_0)))
    )
    or 
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
  TruePred[]
  and 
  (
    (
      BinHeapCondition0[throw_1]
      and 
      (
        y_1=x_0)
    )
    or 
    (
      (
        not (
          BinHeapCondition0[throw_1])
      )
      and 
      TruePred[]
      and 
      (
        y_0=y_1)
    )
  )
  and 
  TruePred[]
  and 
  (
    (
      BinHeapCondition6[y_1]
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
          BinHeapCondition6[y_1])
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
      BinHeapCondition0[throw_1]
      and 
      (
        z_1=y_1.parent_0)
    )
    or 
    (
      (
        not (
          BinHeapCondition0[throw_1])
      )
      and 
      TruePred[]
      and 
      (
        z_0=z_1)
    )
  )
  and 
  TruePred[]
  and 
  TruePred[]
  and 
  (
    (
      BinHeapCondition14[z_1]
      and 
      (
        (
          BinHeapCondition10[y_1,
                            z_1]
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
              BinHeapCondition10[y_1,
                                z_1]
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
          BinHeapCondition0[throw_1]
          and 
          Data_data_lt_0[y_1.element_1,
                        throw_1,
                        throw_2,
                        throw_3,
                        lt_0,
                        lt_1,
                        z_1.element_1,
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
              BinHeapCondition0[throw_1])
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
          BinHeapCondition12[lt_1]
          and 
          (
            (
              BinHeapCondition0[throw_3]
              and 
              (
                b_1=true)
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
                b_0=b_1)
            )
          )
        )
        or 
        (
          (
            not (
              BinHeapCondition12[lt_1])
          )
          and 
          (
            (
              BinHeapCondition0[throw_3]
              and 
              (
                b_1=false)
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
                b_0=b_1)
            )
          )
        )
      )
    )
    or 
    (
      (
        not (
          BinHeapCondition14[z_1])
      )
      and 
      (
        (
          BinHeapCondition0[throw_1]
          and 
          (
            b_1=false)
        )
        or 
        (
          (
            not (
              BinHeapCondition0[throw_1])
          )
          and 
          TruePred[]
          and 
          (
            b_0=b_1)
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
        nullDerefBool_3=nullDerefBool_4)
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
      BinHeapCondition0[throw_3]
      and 
      (
        (
          BinHeapCondition16[b_1]
          and 
          (
            (
              BinHeapCondition0[throw_3]
              and 
              BinHeap_swapElements_0[throw_3,
                                    throw_4,
                                    throw_5,
                                    y_1,
                                    z_1,
                                    element_1,
                                    element_2,
                                    element_3,
                                    l1_nullDerefBool_0,
                                    l1_nullDerefBool_1,
                                    l1_nullDerefBool_2,
                                    l1_nullDerefBool_3,
                                    l1_nullDerefBool_4,
                                    l1_temp_0,
                                    l1_temp_1]
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
                element_1=element_3)
              and 
              (
                l1_temp_0=l1_temp_1)
              and 
              (
                l1_nullDerefBool_0=l1_nullDerefBool_4)
              and 
              (
                throw_3=throw_5)
            )
          )
          and 
          (
            (
              BinHeapCondition0[throw_5]
              and 
              (
                y_2=z_1)
            )
            or 
            (
              (
                not (
                  BinHeapCondition0[throw_5])
              )
              and 
              TruePred[]
              and 
              (
                y_1=y_2)
            )
          )
          and 
          (
            (
              BinHeapCondition6[y_2]
              and 
              (
                (
                  BinHeapCondition0[throw_5]
                  and 
                  (
                    nullDerefBool_5=true)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_5])
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
                  BinHeapCondition6[y_2])
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
              BinHeapCondition0[throw_5]
              and 
              (
                z_2=y_2.parent_0)
            )
            or 
            (
              (
                not (
                  BinHeapCondition0[throw_5])
              )
              and 
              TruePred[]
              and 
              (
                z_1=z_2)
            )
          )
          and 
          (
            (
              BinHeapCondition14[z_2]
              and 
              (
                (
                  BinHeapCondition10[y_2,
                                    z_2]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_5]
                      and 
                      (
                        nullDerefBool_6=true)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_5])
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
                      BinHeapCondition10[y_2,
                                        z_2]
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
                  BinHeapCondition0[throw_5]
                  and 
                  Data_data_lt_0[y_2.element_3,
                                throw_5,
                                throw_6,
                                throw_7,
                                lt_1,
                                lt_2,
                                z_2.element_3,
                                l2_result_0,
                                l2_result_1,
                                l2_result_2,
                                l2_nullDerefBool_0,
                                l2_nullDerefBool_1]
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_5])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    l2_nullDerefBool_0=l2_nullDerefBool_1)
                  and 
                  (
                    lt_1=lt_2)
                  and 
                  (
                    l2_result_0=l2_result_2)
                  and 
                  (
                    throw_5=throw_7)
                )
              )
              and 
              (
                (
                  BinHeapCondition12[lt_2]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_7]
                      and 
                      (
                        b_2=true)
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
                        b_1=b_2)
                    )
                  )
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition12[lt_2])
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_7]
                      and 
                      (
                        b_2=false)
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
                        b_1=b_2)
                    )
                  )
                )
              )
            )
            or 
            (
              (
                not (
                  BinHeapCondition14[z_2])
              )
              and 
              (
                (
                  BinHeapCondition0[throw_5]
                  and 
                  (
                    b_2=false)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_5])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    b_1=b_2)
                )
              )
              and 
              (
                l2_nullDerefBool_0=l2_nullDerefBool_1)
              and 
              (
                nullDerefBool_5=nullDerefBool_6)
              and 
              (
                lt_1=lt_2)
              and 
              (
                l2_result_0=l2_result_2)
              and 
              (
                throw_5=throw_7)
            )
          )
        )
        or 
        (
          TruePred[]
          and 
          (
            element_1=element_3)
          and 
          (
            l1_temp_0=l1_temp_1)
          and 
          (
            b_1=b_2)
          and 
          (
            l1_nullDerefBool_0=l1_nullDerefBool_4)
          and 
          (
            nullDerefBool_4=nullDerefBool_6)
          and 
          (
            lt_1=lt_2)
          and 
          (
            l2_result_0=l2_result_2)
          and 
          (
            l2_nullDerefBool_0=l2_nullDerefBool_1)
          and 
          (
            throw_3=throw_7)
          and 
          (
            z_1=z_2)
          and 
          (
            y_1=y_2)
        )
      )
      and 
      (
        (
          BinHeapCondition16[b_2]
          and 
          (
            (
              BinHeapCondition0[throw_7]
              and 
              BinHeap_swapElements_0[throw_7,
                                    throw_8,
                                    throw_9,
                                    y_2,
                                    z_2,
                                    element_3,
                                    element_4,
                                    element_5,
                                    l3_nullDerefBool_0,
                                    l3_nullDerefBool_1,
                                    l3_nullDerefBool_2,
                                    l3_nullDerefBool_3,
                                    l3_nullDerefBool_4,
                                    l3_temp_0,
                                    l3_temp_1]
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
                element_3=element_5)
              and 
              (
                l3_nullDerefBool_0=l3_nullDerefBool_4)
              and 
              (
                l3_temp_0=l3_temp_1)
              and 
              (
                throw_7=throw_9)
            )
          )
          and 
          (
            (
              BinHeapCondition0[throw_9]
              and 
              (
                y_3=z_2)
            )
            or 
            (
              (
                not (
                  BinHeapCondition0[throw_9])
              )
              and 
              TruePred[]
              and 
              (
                y_2=y_3)
            )
          )
          and 
          (
            (
              BinHeapCondition6[y_3]
              and 
              (
                (
                  BinHeapCondition0[throw_9]
                  and 
                  (
                    nullDerefBool_7=true)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_9])
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
                  BinHeapCondition6[y_3])
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
              BinHeapCondition0[throw_9]
              and 
              (
                z_3=y_3.parent_0)
            )
            or 
            (
              (
                not (
                  BinHeapCondition0[throw_9])
              )
              and 
              TruePred[]
              and 
              (
                z_2=z_3)
            )
          )
          and 
          (
            (
              BinHeapCondition14[z_3]
              and 
              (
                (
                  BinHeapCondition10[y_3,
                                    z_3]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_9]
                      and 
                      (
                        nullDerefBool_8=true)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_9])
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
                      BinHeapCondition10[y_3,
                                        z_3]
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
                  BinHeapCondition0[throw_9]
                  and 
                  Data_data_lt_0[y_3.element_5,
                                throw_9,
                                throw_10,
                                throw_11,
                                lt_2,
                                lt_3,
                                z_3.element_5,
                                l4_result_0,
                                l4_result_1,
                                l4_result_2,
                                l4_nullDerefBool_0,
                                l4_nullDerefBool_1]
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_9])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    l4_result_0=l4_result_2)
                  and 
                  (
                    lt_2=lt_3)
                  and 
                  (
                    l4_nullDerefBool_0=l4_nullDerefBool_1)
                  and 
                  (
                    throw_9=throw_11)
                )
              )
              and 
              (
                (
                  BinHeapCondition12[lt_3]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_11]
                      and 
                      (
                        b_3=true)
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
                        b_2=b_3)
                    )
                  )
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition12[lt_3])
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_11]
                      and 
                      (
                        b_3=false)
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
                        b_2=b_3)
                    )
                  )
                )
              )
            )
            or 
            (
              (
                not (
                  BinHeapCondition14[z_3])
              )
              and 
              (
                (
                  BinHeapCondition0[throw_9]
                  and 
                  (
                    b_3=false)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_9])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    b_2=b_3)
                )
              )
              and 
              (
                l4_result_0=l4_result_2)
              and 
              (
                nullDerefBool_7=nullDerefBool_8)
              and 
              (
                l4_nullDerefBool_0=l4_nullDerefBool_1)
              and 
              (
                lt_2=lt_3)
              and 
              (
                throw_9=throw_11)
            )
          )
        )
        or 
        (
          TruePred[]
          and 
          (
            element_3=element_5)
          and 
          (
            l3_nullDerefBool_0=l3_nullDerefBool_4)
          and 
          (
            b_2=b_3)
          and 
          (
            l4_result_0=l4_result_2)
          and 
          (
            nullDerefBool_6=nullDerefBool_8)
          and 
          (
            l4_nullDerefBool_0=l4_nullDerefBool_1)
          and 
          (
            lt_2=lt_3)
          and 
          (
            l3_temp_0=l3_temp_1)
          and 
          (
            throw_7=throw_11)
          and 
          (
            z_2=z_3)
          and 
          (
            y_2=y_3)
        )
      )
      and 
      (
        (
          BinHeapCondition16[b_3]
          and 
          (
            (
              BinHeapCondition0[throw_11]
              and 
              BinHeap_swapElements_0[throw_11,
                                    throw_12,
                                    throw_13,
                                    y_3,
                                    z_3,
                                    element_5,
                                    element_6,
                                    element_7,
                                    l5_nullDerefBool_0,
                                    l5_nullDerefBool_1,
                                    l5_nullDerefBool_2,
                                    l5_nullDerefBool_3,
                                    l5_nullDerefBool_4,
                                    l5_temp_0,
                                    l5_temp_1]
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
                element_5=element_7)
              and 
              (
                l5_temp_0=l5_temp_1)
              and 
              (
                l5_nullDerefBool_0=l5_nullDerefBool_4)
              and 
              (
                throw_11=throw_13)
            )
          )
          and 
          (
            (
              BinHeapCondition0[throw_13]
              and 
              (
                y_4=z_3)
            )
            or 
            (
              (
                not (
                  BinHeapCondition0[throw_13])
              )
              and 
              TruePred[]
              and 
              (
                y_3=y_4)
            )
          )
          and 
          (
            (
              BinHeapCondition6[y_4]
              and 
              (
                (
                  BinHeapCondition0[throw_13]
                  and 
                  (
                    nullDerefBool_9=true)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_13])
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
                  BinHeapCondition6[y_4])
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
              BinHeapCondition0[throw_13]
              and 
              (
                z_4=y_4.parent_0)
            )
            or 
            (
              (
                not (
                  BinHeapCondition0[throw_13])
              )
              and 
              TruePred[]
              and 
              (
                z_3=z_4)
            )
          )
          and 
          (
            (
              BinHeapCondition14[z_4]
              and 
              (
                (
                  BinHeapCondition10[y_4,
                                    z_4]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_13]
                      and 
                      (
                        nullDerefBool_10=true)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_13])
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
                      BinHeapCondition10[y_4,
                                        z_4]
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
                  BinHeapCondition0[throw_13]
                  and 
                  Data_data_lt_0[y_4.element_7,
                                throw_13,
                                throw_14,
                                throw_15,
                                lt_3,
                                lt_4,
                                z_4.element_7,
                                l6_result_0,
                                l6_result_1,
                                l6_result_2,
                                l6_nullDerefBool_0,
                                l6_nullDerefBool_1]
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_13])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    lt_3=lt_4)
                  and 
                  (
                    l6_result_0=l6_result_2)
                  and 
                  (
                    l6_nullDerefBool_0=l6_nullDerefBool_1)
                  and 
                  (
                    throw_13=throw_15)
                )
              )
              and 
              (
                (
                  BinHeapCondition12[lt_4]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_15]
                      and 
                      (
                        b_4=true)
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
                        b_3=b_4)
                    )
                  )
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition12[lt_4])
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_15]
                      and 
                      (
                        b_4=false)
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
                        b_3=b_4)
                    )
                  )
                )
              )
            )
            or 
            (
              (
                not (
                  BinHeapCondition14[z_4])
              )
              and 
              (
                (
                  BinHeapCondition0[throw_13]
                  and 
                  (
                    b_4=false)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_13])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    b_3=b_4)
                )
              )
              and 
              (
                nullDerefBool_9=nullDerefBool_10)
              and 
              (
                lt_3=lt_4)
              and 
              (
                l6_nullDerefBool_0=l6_nullDerefBool_1)
              and 
              (
                l6_result_0=l6_result_2)
              and 
              (
                throw_13=throw_15)
            )
          )
        )
        or 
        (
          TruePred[]
          and 
          (
            element_5=element_7)
          and 
          (
            b_3=b_4)
          and 
          (
            l5_temp_0=l5_temp_1)
          and 
          (
            nullDerefBool_8=nullDerefBool_10)
          and 
          (
            lt_3=lt_4)
          and 
          (
            throw_11=throw_15)
          and 
          (
            l5_nullDerefBool_0=l5_nullDerefBool_4)
          and 
          (
            l6_nullDerefBool_0=l6_nullDerefBool_1)
          and 
          (
            l6_result_0=l6_result_2)
          and 
          (
            z_3=z_4)
          and 
          (
            y_3=y_4)
        )
      )
      and 
      (
        (
          BinHeapCondition16[b_4]
          and 
          (
            (
              BinHeapCondition0[throw_15]
              and 
              BinHeap_swapElements_0[throw_15,
                                    throw_16,
                                    throw_17,
                                    y_4,
                                    z_4,
                                    element_7,
                                    element_8,
                                    element_9,
                                    l7_nullDerefBool_0,
                                    l7_nullDerefBool_1,
                                    l7_nullDerefBool_2,
                                    l7_nullDerefBool_3,
                                    l7_nullDerefBool_4,
                                    l7_temp_0,
                                    l7_temp_1]
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
                element_7=element_9)
              and 
              (
                l7_nullDerefBool_0=l7_nullDerefBool_4)
              and 
              (
                l7_temp_0=l7_temp_1)
              and 
              (
                throw_15=throw_17)
            )
          )
          and 
          (
            (
              BinHeapCondition0[throw_17]
              and 
              (
                y_5=z_4)
            )
            or 
            (
              (
                not (
                  BinHeapCondition0[throw_17])
              )
              and 
              TruePred[]
              and 
              (
                y_4=y_5)
            )
          )
          and 
          (
            (
              BinHeapCondition6[y_5]
              and 
              (
                (
                  BinHeapCondition0[throw_17]
                  and 
                  (
                    nullDerefBool_11=true)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_17])
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
                  BinHeapCondition6[y_5])
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
              BinHeapCondition0[throw_17]
              and 
              (
                z_5=y_5.parent_0)
            )
            or 
            (
              (
                not (
                  BinHeapCondition0[throw_17])
              )
              and 
              TruePred[]
              and 
              (
                z_4=z_5)
            )
          )
          and 
          (
            (
              BinHeapCondition14[z_5]
              and 
              (
                (
                  BinHeapCondition10[y_5,
                                    z_5]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_17]
                      and 
                      (
                        nullDerefBool_12=true)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_17])
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
                      BinHeapCondition10[y_5,
                                        z_5]
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
                  BinHeapCondition0[throw_17]
                  and 
                  Data_data_lt_0[y_5.element_9,
                                throw_17,
                                throw_18,
                                throw_19,
                                lt_4,
                                lt_5,
                                z_5.element_9,
                                l8_result_0,
                                l8_result_1,
                                l8_result_2,
                                l8_nullDerefBool_0,
                                l8_nullDerefBool_1]
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_17])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    l8_nullDerefBool_0=l8_nullDerefBool_1)
                  and 
                  (
                    l8_result_0=l8_result_2)
                  and 
                  (
                    lt_4=lt_5)
                  and 
                  (
                    throw_17=throw_19)
                )
              )
              and 
              (
                (
                  BinHeapCondition12[lt_5]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_19]
                      and 
                      (
                        b_5=true)
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
                        b_4=b_5)
                    )
                  )
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition12[lt_5])
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_19]
                      and 
                      (
                        b_5=false)
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
                        b_4=b_5)
                    )
                  )
                )
              )
            )
            or 
            (
              (
                not (
                  BinHeapCondition14[z_5])
              )
              and 
              (
                (
                  BinHeapCondition0[throw_17]
                  and 
                  (
                    b_5=false)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_17])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    b_4=b_5)
                )
              )
              and 
              (
                l8_nullDerefBool_0=l8_nullDerefBool_1)
              and 
              (
                l8_result_0=l8_result_2)
              and 
              (
                nullDerefBool_11=nullDerefBool_12)
              and 
              (
                lt_4=lt_5)
              and 
              (
                throw_17=throw_19)
            )
          )
        )
        or 
        (
          TruePred[]
          and 
          (
            element_7=element_9)
          and 
          (
            l8_nullDerefBool_0=l8_nullDerefBool_1)
          and 
          (
            b_4=b_5)
          and 
          (
            l8_result_0=l8_result_2)
          and 
          (
            nullDerefBool_10=nullDerefBool_12)
          and 
          (
            lt_4=lt_5)
          and 
          (
            l7_temp_0=l7_temp_1)
          and 
          (
            throw_15=throw_19)
          and 
          (
            l7_nullDerefBool_0=l7_nullDerefBool_4)
          and 
          (
            z_4=z_5)
          and 
          (
            y_4=y_5)
        )
      )
      and 
      (
        (
          BinHeapCondition16[b_5]
          and 
          (
            (
              BinHeapCondition0[throw_19]
              and 
              BinHeap_swapElements_0[throw_19,
                                    throw_20,
                                    throw_21,
                                    y_5,
                                    z_5,
                                    element_9,
                                    element_10,
                                    element_11,
                                    l9_nullDerefBool_0,
                                    l9_nullDerefBool_1,
                                    l9_nullDerefBool_2,
                                    l9_nullDerefBool_3,
                                    l9_nullDerefBool_4,
                                    l9_temp_0,
                                    l9_temp_1]
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
                element_9=element_11)
              and 
              (
                l9_temp_0=l9_temp_1)
              and 
              (
                l9_nullDerefBool_0=l9_nullDerefBool_4)
              and 
              (
                throw_19=throw_21)
            )
          )
          and 
          (
            (
              BinHeapCondition0[throw_21]
              and 
              (
                y_6=z_5)
            )
            or 
            (
              (
                not (
                  BinHeapCondition0[throw_21])
              )
              and 
              TruePred[]
              and 
              (
                y_5=y_6)
            )
          )
          and 
          (
            (
              BinHeapCondition6[y_6]
              and 
              (
                (
                  BinHeapCondition0[throw_21]
                  and 
                  (
                    nullDerefBool_13=true)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_21])
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
                  BinHeapCondition6[y_6])
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
              BinHeapCondition0[throw_21]
              and 
              (
                z_6=y_6.parent_0)
            )
            or 
            (
              (
                not (
                  BinHeapCondition0[throw_21])
              )
              and 
              TruePred[]
              and 
              (
                z_5=z_6)
            )
          )
          and 
          (
            (
              BinHeapCondition14[z_6]
              and 
              (
                (
                  BinHeapCondition10[y_6,
                                    z_6]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_21]
                      and 
                      (
                        nullDerefBool_14=true)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_21])
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
                      BinHeapCondition10[y_6,
                                        z_6]
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
                  BinHeapCondition0[throw_21]
                  and 
                  Data_data_lt_0[y_6.element_11,
                                throw_21,
                                throw_22,
                                throw_23,
                                lt_5,
                                lt_6,
                                z_6.element_11,
                                l10_result_0,
                                l10_result_1,
                                l10_result_2,
                                l10_nullDerefBool_0,
                                l10_nullDerefBool_1]
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_21])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    l10_nullDerefBool_0=l10_nullDerefBool_1)
                  and 
                  (
                    lt_5=lt_6)
                  and 
                  (
                    l10_result_0=l10_result_2)
                  and 
                  (
                    throw_21=throw_23)
                )
              )
              and 
              (
                (
                  BinHeapCondition12[lt_6]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_23]
                      and 
                      (
                        b_6=true)
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
                        b_5=b_6)
                    )
                  )
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition12[lt_6])
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_23]
                      and 
                      (
                        b_6=false)
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
                        b_5=b_6)
                    )
                  )
                )
              )
            )
            or 
            (
              (
                not (
                  BinHeapCondition14[z_6])
              )
              and 
              (
                (
                  BinHeapCondition0[throw_21]
                  and 
                  (
                    b_6=false)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_21])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    b_5=b_6)
                )
              )
              and 
              (
                l10_nullDerefBool_0=l10_nullDerefBool_1)
              and 
              (
                nullDerefBool_13=nullDerefBool_14)
              and 
              (
                lt_5=lt_6)
              and 
              (
                l10_result_0=l10_result_2)
              and 
              (
                throw_21=throw_23)
            )
          )
        )
        or 
        (
          TruePred[]
          and 
          (
            element_9=element_11)
          and 
          (
            l9_temp_0=l9_temp_1)
          and 
          (
            b_5=b_6)
          and 
          (
            nullDerefBool_12=nullDerefBool_14)
          and 
          (
            lt_5=lt_6)
          and 
          (
            l10_result_0=l10_result_2)
          and 
          (
            throw_19=throw_23)
          and 
          (
            l9_nullDerefBool_0=l9_nullDerefBool_4)
          and 
          (
            l10_nullDerefBool_0=l10_nullDerefBool_1)
          and 
          (
            z_5=z_6)
          and 
          (
            y_5=y_6)
        )
      )
      and 
      (
        (
          BinHeapCondition16[b_6]
          and 
          (
            (
              BinHeapCondition0[throw_23]
              and 
              BinHeap_swapElements_0[throw_23,
                                    throw_24,
                                    throw_25,
                                    y_6,
                                    z_6,
                                    element_11,
                                    element_12,
                                    element_13,
                                    l11_nullDerefBool_0,
                                    l11_nullDerefBool_1,
                                    l11_nullDerefBool_2,
                                    l11_nullDerefBool_3,
                                    l11_nullDerefBool_4,
                                    l11_temp_0,
                                    l11_temp_1]
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
                element_11=element_13)
              and 
              (
                l11_nullDerefBool_0=l11_nullDerefBool_4)
              and 
              (
                l11_temp_0=l11_temp_1)
              and 
              (
                throw_23=throw_25)
            )
          )
          and 
          (
            (
              BinHeapCondition0[throw_25]
              and 
              (
                y_7=z_6)
            )
            or 
            (
              (
                not (
                  BinHeapCondition0[throw_25])
              )
              and 
              TruePred[]
              and 
              (
                y_6=y_7)
            )
          )
          and 
          (
            (
              BinHeapCondition6[y_7]
              and 
              (
                (
                  BinHeapCondition0[throw_25]
                  and 
                  (
                    nullDerefBool_15=true)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_25])
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
                  BinHeapCondition6[y_7])
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
              BinHeapCondition0[throw_25]
              and 
              (
                z_7=y_7.parent_0)
            )
            or 
            (
              (
                not (
                  BinHeapCondition0[throw_25])
              )
              and 
              TruePred[]
              and 
              (
                z_6=z_7)
            )
          )
          and 
          (
            (
              BinHeapCondition14[z_7]
              and 
              (
                (
                  BinHeapCondition10[y_7,
                                    z_7]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_25]
                      and 
                      (
                        nullDerefBool_16=true)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_25])
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
                      BinHeapCondition10[y_7,
                                        z_7]
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
                  BinHeapCondition0[throw_25]
                  and 
                  Data_data_lt_0[y_7.element_13,
                                throw_25,
                                throw_26,
                                throw_27,
                                lt_6,
                                lt_7,
                                z_7.element_13,
                                l12_result_0,
                                l12_result_1,
                                l12_result_2,
                                l12_nullDerefBool_0,
                                l12_nullDerefBool_1]
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_25])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    l12_nullDerefBool_0=l12_nullDerefBool_1)
                  and 
                  (
                    l12_result_0=l12_result_2)
                  and 
                  (
                    lt_6=lt_7)
                  and 
                  (
                    throw_25=throw_27)
                )
              )
              and 
              (
                (
                  BinHeapCondition12[lt_7]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_27]
                      and 
                      (
                        b_7=true)
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
                        b_6=b_7)
                    )
                  )
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition12[lt_7])
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_27]
                      and 
                      (
                        b_7=false)
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
                        b_6=b_7)
                    )
                  )
                )
              )
            )
            or 
            (
              (
                not (
                  BinHeapCondition14[z_7])
              )
              and 
              (
                (
                  BinHeapCondition0[throw_25]
                  and 
                  (
                    b_7=false)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_25])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    b_6=b_7)
                )
              )
              and 
              (
                l12_nullDerefBool_0=l12_nullDerefBool_1)
              and 
              (
                nullDerefBool_15=nullDerefBool_16)
              and 
              (
                l12_result_0=l12_result_2)
              and 
              (
                lt_6=lt_7)
              and 
              (
                throw_25=throw_27)
            )
          )
        )
        or 
        (
          TruePred[]
          and 
          (
            element_11=element_13)
          and 
          (
            b_6=b_7)
          and 
          (
            l11_nullDerefBool_0=l11_nullDerefBool_4)
          and 
          (
            l12_nullDerefBool_0=l12_nullDerefBool_1)
          and 
          (
            nullDerefBool_14=nullDerefBool_16)
          and 
          (
            l12_result_0=l12_result_2)
          and 
          (
            lt_6=lt_7)
          and 
          (
            l11_temp_0=l11_temp_1)
          and 
          (
            throw_23=throw_27)
          and 
          (
            z_6=z_7)
          and 
          (
            y_6=y_7)
        )
      )
      and 
      (
        (
          BinHeapCondition16[b_7]
          and 
          (
            (
              BinHeapCondition0[throw_27]
              and 
              BinHeap_swapElements_0[throw_27,
                                    throw_28,
                                    throw_29,
                                    y_7,
                                    z_7,
                                    element_13,
                                    element_14,
                                    element_15,
                                    l13_nullDerefBool_0,
                                    l13_nullDerefBool_1,
                                    l13_nullDerefBool_2,
                                    l13_nullDerefBool_3,
                                    l13_nullDerefBool_4,
                                    l13_temp_0,
                                    l13_temp_1]
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
                element_13=element_15)
              and 
              (
                l13_nullDerefBool_0=l13_nullDerefBool_4)
              and 
              (
                l13_temp_0=l13_temp_1)
              and 
              (
                throw_27=throw_29)
            )
          )
          and 
          (
            (
              BinHeapCondition0[throw_29]
              and 
              (
                y_8=z_7)
            )
            or 
            (
              (
                not (
                  BinHeapCondition0[throw_29])
              )
              and 
              TruePred[]
              and 
              (
                y_7=y_8)
            )
          )
          and 
          (
            (
              BinHeapCondition6[y_8]
              and 
              (
                (
                  BinHeapCondition0[throw_29]
                  and 
                  (
                    nullDerefBool_17=true)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_29])
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
                  BinHeapCondition6[y_8])
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
              BinHeapCondition0[throw_29]
              and 
              (
                z_8=y_8.parent_0)
            )
            or 
            (
              (
                not (
                  BinHeapCondition0[throw_29])
              )
              and 
              TruePred[]
              and 
              (
                z_7=z_8)
            )
          )
          and 
          (
            (
              BinHeapCondition14[z_8]
              and 
              (
                (
                  BinHeapCondition10[y_8,
                                    z_8]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_29]
                      and 
                      (
                        nullDerefBool_18=true)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_29])
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
                      BinHeapCondition10[y_8,
                                        z_8]
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
                  BinHeapCondition0[throw_29]
                  and 
                  Data_data_lt_0[y_8.element_15,
                                throw_29,
                                throw_30,
                                throw_31,
                                lt_7,
                                lt_8,
                                z_8.element_15,
                                l14_result_0,
                                l14_result_1,
                                l14_result_2,
                                l14_nullDerefBool_0,
                                l14_nullDerefBool_1]
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_29])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    l14_nullDerefBool_0=l14_nullDerefBool_1)
                  and 
                  (
                    l14_result_0=l14_result_2)
                  and 
                  (
                    lt_7=lt_8)
                  and 
                  (
                    throw_29=throw_31)
                )
              )
              and 
              (
                (
                  BinHeapCondition12[lt_8]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_31]
                      and 
                      (
                        b_8=true)
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
                        b_7=b_8)
                    )
                  )
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition12[lt_8])
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_31]
                      and 
                      (
                        b_8=false)
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
                        b_7=b_8)
                    )
                  )
                )
              )
            )
            or 
            (
              (
                not (
                  BinHeapCondition14[z_8])
              )
              and 
              (
                (
                  BinHeapCondition0[throw_29]
                  and 
                  (
                    b_8=false)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_29])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    b_7=b_8)
                )
              )
              and 
              (
                l14_nullDerefBool_0=l14_nullDerefBool_1)
              and 
              (
                l14_result_0=l14_result_2)
              and 
              (
                nullDerefBool_17=nullDerefBool_18)
              and 
              (
                lt_7=lt_8)
              and 
              (
                throw_29=throw_31)
            )
          )
        )
        or 
        (
          TruePred[]
          and 
          (
            l14_nullDerefBool_0=l14_nullDerefBool_1)
          and 
          (
            element_13=element_15)
          and 
          (
            l14_result_0=l14_result_2)
          and 
          (
            b_7=b_8)
          and 
          (
            l13_nullDerefBool_0=l13_nullDerefBool_4)
          and 
          (
            nullDerefBool_16=nullDerefBool_18)
          and 
          (
            l13_temp_0=l13_temp_1)
          and 
          (
            lt_7=lt_8)
          and 
          (
            throw_27=throw_31)
          and 
          (
            z_7=z_8)
          and 
          (
            y_7=y_8)
        )
      )
      and 
      (
        (
          BinHeapCondition16[b_8]
          and 
          (
            (
              BinHeapCondition0[throw_31]
              and 
              BinHeap_swapElements_0[throw_31,
                                    throw_32,
                                    throw_33,
                                    y_8,
                                    z_8,
                                    element_15,
                                    element_16,
                                    element_17,
                                    l15_nullDerefBool_0,
                                    l15_nullDerefBool_1,
                                    l15_nullDerefBool_2,
                                    l15_nullDerefBool_3,
                                    l15_nullDerefBool_4,
                                    l15_temp_0,
                                    l15_temp_1]
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
                element_15=element_17)
              and 
              (
                l15_nullDerefBool_0=l15_nullDerefBool_4)
              and 
              (
                l15_temp_0=l15_temp_1)
              and 
              (
                throw_31=throw_33)
            )
          )
          and 
          (
            (
              BinHeapCondition0[throw_33]
              and 
              (
                y_9=z_8)
            )
            or 
            (
              (
                not (
                  BinHeapCondition0[throw_33])
              )
              and 
              TruePred[]
              and 
              (
                y_8=y_9)
            )
          )
          and 
          (
            (
              BinHeapCondition6[y_9]
              and 
              (
                (
                  BinHeapCondition0[throw_33]
                  and 
                  (
                    nullDerefBool_19=true)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_33])
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
                  BinHeapCondition6[y_9])
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
              BinHeapCondition0[throw_33]
              and 
              (
                z_9=y_9.parent_0)
            )
            or 
            (
              (
                not (
                  BinHeapCondition0[throw_33])
              )
              and 
              TruePred[]
              and 
              (
                z_8=z_9)
            )
          )
          and 
          (
            (
              BinHeapCondition14[z_9]
              and 
              (
                (
                  BinHeapCondition10[y_9,
                                    z_9]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_33]
                      and 
                      (
                        nullDerefBool_20=true)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_33])
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
                      BinHeapCondition10[y_9,
                                        z_9]
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
                  BinHeapCondition0[throw_33]
                  and 
                  Data_data_lt_0[y_9.element_17,
                                throw_33,
                                throw_34,
                                throw_35,
                                lt_8,
                                lt_9,
                                z_9.element_17,
                                l16_result_0,
                                l16_result_1,
                                l16_result_2,
                                l16_nullDerefBool_0,
                                l16_nullDerefBool_1]
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_33])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    l16_nullDerefBool_0=l16_nullDerefBool_1)
                  and 
                  (
                    lt_8=lt_9)
                  and 
                  (
                    l16_result_0=l16_result_2)
                  and 
                  (
                    throw_33=throw_35)
                )
              )
              and 
              (
                (
                  BinHeapCondition12[lt_9]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_35]
                      and 
                      (
                        b_9=true)
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
                        b_8=b_9)
                    )
                  )
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition12[lt_9])
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_35]
                      and 
                      (
                        b_9=false)
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
                        b_8=b_9)
                    )
                  )
                )
              )
            )
            or 
            (
              (
                not (
                  BinHeapCondition14[z_9])
              )
              and 
              (
                (
                  BinHeapCondition0[throw_33]
                  and 
                  (
                    b_9=false)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_33])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    b_8=b_9)
                )
              )
              and 
              (
                nullDerefBool_19=nullDerefBool_20)
              and 
              (
                l16_nullDerefBool_0=l16_nullDerefBool_1)
              and 
              (
                lt_8=lt_9)
              and 
              (
                l16_result_0=l16_result_2)
              and 
              (
                throw_33=throw_35)
            )
          )
        )
        or 
        (
          TruePred[]
          and 
          (
            element_15=element_17)
          and 
          (
            l15_nullDerefBool_0=l15_nullDerefBool_4)
          and 
          (
            b_8=b_9)
          and 
          (
            nullDerefBool_18=nullDerefBool_20)
          and 
          (
            l16_nullDerefBool_0=l16_nullDerefBool_1)
          and 
          (
            lt_8=lt_9)
          and 
          (
            throw_31=throw_35)
          and 
          (
            l15_temp_0=l15_temp_1)
          and 
          (
            z_8=z_9)
          and 
          (
            y_8=y_9)
          and 
          (
            l16_result_0=l16_result_2)
        )
      )
      and 
      (
        (
          BinHeapCondition16[b_9]
          and 
          (
            (
              BinHeapCondition0[throw_35]
              and 
              BinHeap_swapElements_0[throw_35,
                                    throw_36,
                                    throw_37,
                                    y_9,
                                    z_9,
                                    element_17,
                                    element_18,
                                    element_19,
                                    l17_nullDerefBool_0,
                                    l17_nullDerefBool_1,
                                    l17_nullDerefBool_2,
                                    l17_nullDerefBool_3,
                                    l17_nullDerefBool_4,
                                    l17_temp_0,
                                    l17_temp_1]
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
                element_17=element_19)
              and 
              (
                l17_nullDerefBool_0=l17_nullDerefBool_4)
              and 
              (
                l17_temp_0=l17_temp_1)
              and 
              (
                throw_35=throw_37)
            )
          )
          and 
          (
            (
              BinHeapCondition0[throw_37]
              and 
              (
                y_10=z_9)
            )
            or 
            (
              (
                not (
                  BinHeapCondition0[throw_37])
              )
              and 
              TruePred[]
              and 
              (
                y_9=y_10)
            )
          )
          and 
          (
            (
              BinHeapCondition6[y_10]
              and 
              (
                (
                  BinHeapCondition0[throw_37]
                  and 
                  (
                    nullDerefBool_21=true)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_37])
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
                  BinHeapCondition6[y_10])
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
              BinHeapCondition0[throw_37]
              and 
              (
                z_10=y_10.parent_0)
            )
            or 
            (
              (
                not (
                  BinHeapCondition0[throw_37])
              )
              and 
              TruePred[]
              and 
              (
                z_9=z_10)
            )
          )
          and 
          (
            (
              BinHeapCondition14[z_10]
              and 
              (
                (
                  BinHeapCondition10[y_10,
                                    z_10]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_37]
                      and 
                      (
                        nullDerefBool_22=true)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_37])
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
                      BinHeapCondition10[y_10,
                                        z_10]
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
                  BinHeapCondition0[throw_37]
                  and 
                  Data_data_lt_0[y_10.element_19,
                                throw_37,
                                throw_38,
                                throw_39,
                                lt_9,
                                lt_10,
                                z_10.element_19,
                                l18_result_0,
                                l18_result_1,
                                l18_result_2,
                                l18_nullDerefBool_0,
                                l18_nullDerefBool_1]
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_37])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    l18_nullDerefBool_0=l18_nullDerefBool_1)
                  and 
                  (
                    lt_9=lt_10)
                  and 
                  (
                    l18_result_0=l18_result_2)
                  and 
                  (
                    throw_37=throw_39)
                )
              )
              and 
              (
                (
                  BinHeapCondition12[lt_10]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_39]
                      and 
                      (
                        b_10=true)
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
                        b_9=b_10)
                    )
                  )
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition12[lt_10])
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_39]
                      and 
                      (
                        b_10=false)
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
                        b_9=b_10)
                    )
                  )
                )
              )
            )
            or 
            (
              (
                not (
                  BinHeapCondition14[z_10])
              )
              and 
              (
                (
                  BinHeapCondition0[throw_37]
                  and 
                  (
                    b_10=false)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_37])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    b_9=b_10)
                )
              )
              and 
              (
                l18_nullDerefBool_0=l18_nullDerefBool_1)
              and 
              (
                nullDerefBool_21=nullDerefBool_22)
              and 
              (
                lt_9=lt_10)
              and 
              (
                l18_result_0=l18_result_2)
              and 
              (
                throw_37=throw_39)
            )
          )
        )
        or 
        (
          TruePred[]
          and 
          (
            l18_nullDerefBool_0=l18_nullDerefBool_1)
          and 
          (
            element_17=element_19)
          and 
          (
            b_9=b_10)
          and 
          (
            nullDerefBool_20=nullDerefBool_22)
          and 
          (
            l17_temp_0=l17_temp_1)
          and 
          (
            lt_9=lt_10)
          and 
          (
            throw_35=throw_39)
          and 
          (
            l17_nullDerefBool_0=l17_nullDerefBool_4)
          and 
          (
            z_9=z_10)
          and 
          (
            y_9=y_10)
          and 
          (
            l18_result_0=l18_result_2)
        )
      )
      and 
      (
        (
          BinHeapCondition16[b_10]
          and 
          (
            (
              BinHeapCondition0[throw_39]
              and 
              BinHeap_swapElements_0[throw_39,
                                    throw_40,
                                    throw_41,
                                    y_10,
                                    z_10,
                                    element_19,
                                    element_20,
                                    element_21,
                                    l19_nullDerefBool_0,
                                    l19_nullDerefBool_1,
                                    l19_nullDerefBool_2,
                                    l19_nullDerefBool_3,
                                    l19_nullDerefBool_4,
                                    l19_temp_0,
                                    l19_temp_1]
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
                element_19=element_21)
              and 
              (
                l19_nullDerefBool_0=l19_nullDerefBool_4)
              and 
              (
                l19_temp_0=l19_temp_1)
              and 
              (
                throw_39=throw_41)
            )
          )
          and 
          (
            (
              BinHeapCondition0[throw_41]
              and 
              (
                y_11=z_10)
            )
            or 
            (
              (
                not (
                  BinHeapCondition0[throw_41])
              )
              and 
              TruePred[]
              and 
              (
                y_10=y_11)
            )
          )
          and 
          (
            (
              BinHeapCondition6[y_11]
              and 
              (
                (
                  BinHeapCondition0[throw_41]
                  and 
                  (
                    nullDerefBool_23=true)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_41])
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
                  BinHeapCondition6[y_11])
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
              BinHeapCondition0[throw_41]
              and 
              (
                z_11=y_11.parent_0)
            )
            or 
            (
              (
                not (
                  BinHeapCondition0[throw_41])
              )
              and 
              TruePred[]
              and 
              (
                z_10=z_11)
            )
          )
          and 
          (
            (
              BinHeapCondition14[z_11]
              and 
              (
                (
                  BinHeapCondition10[y_11,
                                    z_11]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_41]
                      and 
                      (
                        nullDerefBool_24=true)
                    )
                    or 
                    (
                      (
                        not (
                          BinHeapCondition0[throw_41])
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
                      BinHeapCondition10[y_11,
                                        z_11]
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
                  BinHeapCondition0[throw_41]
                  and 
                  Data_data_lt_0[y_11.element_21,
                                throw_41,
                                throw_42,
                                throw_43,
                                lt_10,
                                lt_11,
                                z_11.element_21,
                                l20_result_0,
                                l20_result_1,
                                l20_result_2,
                                l20_nullDerefBool_0,
                                l20_nullDerefBool_1]
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_41])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    l20_nullDerefBool_0=l20_nullDerefBool_1)
                  and 
                  (
                    l20_result_0=l20_result_2)
                  and 
                  (
                    lt_10=lt_11)
                  and 
                  (
                    throw_41=throw_43)
                )
              )
              and 
              (
                (
                  BinHeapCondition12[lt_11]
                  and 
                  (
                    (
                      BinHeapCondition0[throw_43]
                      and 
                      (
                        b_11=true)
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
                        b_10=b_11)
                    )
                  )
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition12[lt_11])
                  )
                  and 
                  (
                    (
                      BinHeapCondition0[throw_43]
                      and 
                      (
                        b_11=false)
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
                        b_10=b_11)
                    )
                  )
                )
              )
            )
            or 
            (
              (
                not (
                  BinHeapCondition14[z_11])
              )
              and 
              (
                (
                  BinHeapCondition0[throw_41]
                  and 
                  (
                    b_11=false)
                )
                or 
                (
                  (
                    not (
                      BinHeapCondition0[throw_41])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    b_10=b_11)
                )
              )
              and 
              (
                l20_nullDerefBool_0=l20_nullDerefBool_1)
              and 
              (
                l20_result_0=l20_result_2)
              and 
              (
                nullDerefBool_23=nullDerefBool_24)
              and 
              (
                lt_10=lt_11)
              and 
              (
                throw_41=throw_43)
            )
          )
        )
        or 
        (
          TruePred[]
          and 
          (
            l19_nullDerefBool_0=l19_nullDerefBool_4)
          and 
          (
            element_19=element_21)
          and 
          (
            l20_nullDerefBool_0=l20_nullDerefBool_1)
          and 
          (
            b_10=b_11)
          and 
          (
            nullDerefBool_22=nullDerefBool_24)
          and 
          (
            lt_10=lt_11)
          and 
          (
            throw_39=throw_43)
          and 
          (
            l20_result_0=l20_result_2)
          and 
          (
            l19_temp_0=l19_temp_1)
          and 
          (
            z_10=z_11)
          and 
          (
            y_10=y_11)
        )
      )
      and 
      BinHeapCondition17[b_11]
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
        l9_temp_0=l9_temp_1)
      and 
      (
        l14_result_0=l14_result_2)
      and 
      (
        l8_nullDerefBool_0=l8_nullDerefBool_1)
      and 
      (
        l13_nullDerefBool_0=l13_nullDerefBool_4)
      and 
      (
        l8_result_0=l8_result_2)
      and 
      (
        nullDerefBool_4=nullDerefBool_24)
      and 
      (
        l16_nullDerefBool_0=l16_nullDerefBool_1)
      and 
      (
        element_1=element_21)
      and 
      (
        l11_nullDerefBool_0=l11_nullDerefBool_4)
      and 
      (
        l4_result_0=l4_result_2)
      and 
      (
        l17_temp_0=l17_temp_1)
      and 
      (
        l11_temp_0=l11_temp_1)
      and 
      (
        l2_nullDerefBool_0=l2_nullDerefBool_1)
      and 
      (
        l7_nullDerefBool_0=l7_nullDerefBool_4)
      and 
      (
        l6_result_0=l6_result_2)
      and 
      (
        l18_result_0=l18_result_2)
      and 
      (
        l19_nullDerefBool_0=l19_nullDerefBool_4)
      and 
      (
        l14_nullDerefBool_0=l14_nullDerefBool_1)
      and 
      (
        l1_temp_0=l1_temp_1)
      and 
      (
        l5_temp_0=l5_temp_1)
      and 
      (
        lt_1=lt_11)
      and 
      (
        l4_nullDerefBool_0=l4_nullDerefBool_1)
      and 
      (
        l10_result_0=l10_result_2)
      and 
      (
        l20_result_0=l20_result_2)
      and 
      (
        l9_nullDerefBool_0=l9_nullDerefBool_4)
      and 
      (
        l5_nullDerefBool_0=l5_nullDerefBool_4)
      and 
      (
        l19_temp_0=l19_temp_1)
      and 
      (
        l6_nullDerefBool_0=l6_nullDerefBool_1)
      and 
      (
        l15_temp_0=l15_temp_1)
      and 
      (
        l16_result_0=l16_result_2)
      and 
      (
        l18_nullDerefBool_0=l18_nullDerefBool_1)
      and 
      (
        l3_nullDerefBool_0=l3_nullDerefBool_4)
      and 
      (
        l20_nullDerefBool_0=l20_nullDerefBool_1)
      and 
      (
        b_1=b_11)
      and 
      (
        l15_nullDerefBool_0=l15_nullDerefBool_4)
      and 
      (
        l1_nullDerefBool_0=l1_nullDerefBool_4)
      and 
      (
        l12_nullDerefBool_0=l12_nullDerefBool_1)
      and 
      (
        l13_temp_0=l13_temp_1)
      and 
      (
        l12_result_0=l12_result_2)
      and 
      (
        l7_temp_0=l7_temp_1)
      and 
      (
        l3_temp_0=l3_temp_1)
      and 
      (
        l2_result_0=l2_result_2)
      and 
      (
        l17_nullDerefBool_0=l17_nullDerefBool_4)
      and 
      (
        l10_nullDerefBool_0=l10_nullDerefBool_1)
      and 
      (
        z_1=z_11)
      and 
      (
        y_1=y_11)
      and 
      (
        throw_3=throw_43)
    )
  )
  and 
  (
    (
      BinHeapCondition8[nullDerefBool_24,
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
          BinHeapCondition8[nullDerefBool_24,
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



pred BinHeap_swapElements_0[
  throw_0: Throwable + null,
  throw_1: Throwable + null,
  throw_2: Throwable + null,
  x_0: BinHeapNode + null,
  y_0: BinHeapNode + null,
  element_0: ( BinHeapNode ) -> one ( Data + null ),
  element_1: ( BinHeapNode ) -> one ( Data + null ),
  element_2: ( BinHeapNode ) -> one ( Data + null ),
  nullDerefBool_0: boolean,
  nullDerefBool_1: boolean,
  nullDerefBool_2: boolean,
  nullDerefBool_3: boolean,
  nullDerefBool_4: boolean,
  temp_0: Data + null,
  temp_1: Data + null
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
      BinHeapCondition2[x_0]
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
          BinHeapCondition2[x_0])
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
        temp_1=x_0.element_0)
    )
    or 
    (
      (
        not (
          BinHeapCondition0[throw_1])
      )
      and 
      TruePred[]
      and 
      (
        temp_0=temp_1)
    )
  )
  and 
  (
    (
      BinHeapCondition4[x_0,
                       y_0]
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
          BinHeapCondition4[x_0,
                           y_0]
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
      BinHeapCondition0[throw_1]
      and 
      (
        element_1=(element_0)++((x_0)->(y_0.element_0)))
    )
    or 
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
      BinHeapCondition6[y_0]
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
          BinHeapCondition6[y_0])
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
        element_2=(element_1)++((y_0)->(temp_1)))
    )
    or 
    (
      (
        not (
          BinHeapCondition0[throw_1])
      )
      and 
      TruePred[]
      and 
      (
        element_1=element_2)
    )
  )
  and 
  (
    (
      BinHeapCondition8[nullDerefBool_4,
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
          BinHeapCondition8[nullDerefBool_4,
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
  bchild_0,fchild_0: ( BinHeapNode ) -> lone ( BinHeapNode + null ),
  degree_0: ( BinHeapNode ) -> one ( Int ),
  element_0: ( BinHeapNode ) -> one ( Data + null ),
  element_1: ( BinHeapNode ) -> one ( Data + null ),
  element_10: ( BinHeapNode ) -> one ( Data + null ),
  element_11: ( BinHeapNode ) -> one ( Data + null ),
  element_12: ( BinHeapNode ) -> one ( Data + null ),
  element_13: ( BinHeapNode ) -> one ( Data + null ),
  element_14: ( BinHeapNode ) -> one ( Data + null ),
  element_15: ( BinHeapNode ) -> one ( Data + null ),
  element_16: ( BinHeapNode ) -> one ( Data + null ),
  element_17: ( BinHeapNode ) -> one ( Data + null ),
  element_18: ( BinHeapNode ) -> one ( Data + null ),
  element_19: ( BinHeapNode ) -> one ( Data + null ),
  element_2: ( BinHeapNode ) -> one ( Data + null ),
  element_20: ( BinHeapNode ) -> one ( Data + null ),
  element_21: ( BinHeapNode ) -> one ( Data + null ),
  element_3: ( BinHeapNode ) -> one ( Data + null ),
  element_4: ( BinHeapNode ) -> one ( Data + null ),
  element_5: ( BinHeapNode ) -> one ( Data + null ),
  element_6: ( BinHeapNode ) -> one ( Data + null ),
  element_7: ( BinHeapNode ) -> one ( Data + null ),
  element_8: ( BinHeapNode ) -> one ( Data + null ),
  element_9: ( BinHeapNode ) -> one ( Data + null ),
  head_0: ( BinHeap ) -> one ( BinHeapNode + null ),
  k_0: Data + null,
  l21_b_0: boolean,
  l21_b_1: boolean,
  l21_b_10: boolean,
  l21_b_11: boolean,
  l21_b_2: boolean,
  l21_b_3: boolean,
  l21_b_4: boolean,
  l21_b_5: boolean,
  l21_b_6: boolean,
  l21_b_7: boolean,
  l21_b_8: boolean,
  l21_b_9: boolean,
  l21_l0_nullDerefBool_0: boolean,
  l21_l0_nullDerefBool_1: boolean,
  l21_l0_result_0: boolean,
  l21_l0_result_1: boolean,
  l21_l0_result_2: boolean,
  l21_l10_nullDerefBool_0: boolean,
  l21_l10_nullDerefBool_1: boolean,
  l21_l10_result_0: boolean,
  l21_l10_result_1: boolean,
  l21_l10_result_2: boolean,
  l21_l11_nullDerefBool_0: boolean,
  l21_l11_nullDerefBool_1: boolean,
  l21_l11_nullDerefBool_2: boolean,
  l21_l11_nullDerefBool_3: boolean,
  l21_l11_nullDerefBool_4: boolean,
  l21_l11_temp_0: Data + null,
  l21_l11_temp_1: Data + null,
  l21_l12_nullDerefBool_0: boolean,
  l21_l12_nullDerefBool_1: boolean,
  l21_l12_result_0: boolean,
  l21_l12_result_1: boolean,
  l21_l12_result_2: boolean,
  l21_l13_nullDerefBool_0: boolean,
  l21_l13_nullDerefBool_1: boolean,
  l21_l13_nullDerefBool_2: boolean,
  l21_l13_nullDerefBool_3: boolean,
  l21_l13_nullDerefBool_4: boolean,
  l21_l13_temp_0: Data + null,
  l21_l13_temp_1: Data + null,
  l21_l14_nullDerefBool_0: boolean,
  l21_l14_nullDerefBool_1: boolean,
  l21_l14_result_0: boolean,
  l21_l14_result_1: boolean,
  l21_l14_result_2: boolean,
  l21_l15_nullDerefBool_0: boolean,
  l21_l15_nullDerefBool_1: boolean,
  l21_l15_nullDerefBool_2: boolean,
  l21_l15_nullDerefBool_3: boolean,
  l21_l15_nullDerefBool_4: boolean,
  l21_l15_temp_0: Data + null,
  l21_l15_temp_1: Data + null,
  l21_l16_nullDerefBool_0: boolean,
  l21_l16_nullDerefBool_1: boolean,
  l21_l16_result_0: boolean,
  l21_l16_result_1: boolean,
  l21_l16_result_2: boolean,
  l21_l17_nullDerefBool_0: boolean,
  l21_l17_nullDerefBool_1: boolean,
  l21_l17_nullDerefBool_2: boolean,
  l21_l17_nullDerefBool_3: boolean,
  l21_l17_nullDerefBool_4: boolean,
  l21_l17_temp_0: Data + null,
  l21_l17_temp_1: Data + null,
  l21_l18_nullDerefBool_0: boolean,
  l21_l18_nullDerefBool_1: boolean,
  l21_l18_result_0: boolean,
  l21_l18_result_1: boolean,
  l21_l18_result_2: boolean,
  l21_l19_nullDerefBool_0: boolean,
  l21_l19_nullDerefBool_1: boolean,
  l21_l19_nullDerefBool_2: boolean,
  l21_l19_nullDerefBool_3: boolean,
  l21_l19_nullDerefBool_4: boolean,
  l21_l19_temp_0: Data + null,
  l21_l19_temp_1: Data + null,
  l21_l1_nullDerefBool_0: boolean,
  l21_l1_nullDerefBool_1: boolean,
  l21_l1_nullDerefBool_2: boolean,
  l21_l1_nullDerefBool_3: boolean,
  l21_l1_nullDerefBool_4: boolean,
  l21_l1_temp_0: Data + null,
  l21_l1_temp_1: Data + null,
  l21_l20_nullDerefBool_0: boolean,
  l21_l20_nullDerefBool_1: boolean,
  l21_l20_result_0: boolean,
  l21_l20_result_1: boolean,
  l21_l20_result_2: boolean,
  l21_l2_nullDerefBool_0: boolean,
  l21_l2_nullDerefBool_1: boolean,
  l21_l2_result_0: boolean,
  l21_l2_result_1: boolean,
  l21_l2_result_2: boolean,
  l21_l3_nullDerefBool_0: boolean,
  l21_l3_nullDerefBool_1: boolean,
  l21_l3_nullDerefBool_2: boolean,
  l21_l3_nullDerefBool_3: boolean,
  l21_l3_nullDerefBool_4: boolean,
  l21_l3_temp_0: Data + null,
  l21_l3_temp_1: Data + null,
  l21_l4_nullDerefBool_0: boolean,
  l21_l4_nullDerefBool_1: boolean,
  l21_l4_result_0: boolean,
  l21_l4_result_1: boolean,
  l21_l4_result_2: boolean,
  l21_l5_nullDerefBool_0: boolean,
  l21_l5_nullDerefBool_1: boolean,
  l21_l5_nullDerefBool_2: boolean,
  l21_l5_nullDerefBool_3: boolean,
  l21_l5_nullDerefBool_4: boolean,
  l21_l5_temp_0: Data + null,
  l21_l5_temp_1: Data + null,
  l21_l6_nullDerefBool_0: boolean,
  l21_l6_nullDerefBool_1: boolean,
  l21_l6_result_0: boolean,
  l21_l6_result_1: boolean,
  l21_l6_result_2: boolean,
  l21_l7_nullDerefBool_0: boolean,
  l21_l7_nullDerefBool_1: boolean,
  l21_l7_nullDerefBool_2: boolean,
  l21_l7_nullDerefBool_3: boolean,
  l21_l7_nullDerefBool_4: boolean,
  l21_l7_temp_0: Data + null,
  l21_l7_temp_1: Data + null,
  l21_l8_nullDerefBool_0: boolean,
  l21_l8_nullDerefBool_1: boolean,
  l21_l8_result_0: boolean,
  l21_l8_result_1: boolean,
  l21_l8_result_2: boolean,
  l21_l9_nullDerefBool_0: boolean,
  l21_l9_nullDerefBool_1: boolean,
  l21_l9_nullDerefBool_2: boolean,
  l21_l9_nullDerefBool_3: boolean,
  l21_l9_nullDerefBool_4: boolean,
  l21_l9_temp_0: Data + null,
  l21_l9_temp_1: Data + null,
  l21_lt_0: boolean,
  l21_lt_1: boolean,
  l21_lt_10: boolean,
  l21_lt_11: boolean,
  l21_lt_2: boolean,
  l21_lt_3: boolean,
  l21_lt_4: boolean,
  l21_lt_5: boolean,
  l21_lt_6: boolean,
  l21_lt_7: boolean,
  l21_lt_8: boolean,
  l21_lt_9: boolean,
  l21_nullDerefBool_0: boolean,
  l21_nullDerefBool_1: boolean,
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
  l21_nullDerefBool_2: boolean,
  l21_nullDerefBool_20: boolean,
  l21_nullDerefBool_21: boolean,
  l21_nullDerefBool_22: boolean,
  l21_nullDerefBool_23: boolean,
  l21_nullDerefBool_24: boolean,
  l21_nullDerefBool_3: boolean,
  l21_nullDerefBool_4: boolean,
  l21_nullDerefBool_5: boolean,
  l21_nullDerefBool_6: boolean,
  l21_nullDerefBool_7: boolean,
  l21_nullDerefBool_8: boolean,
  l21_nullDerefBool_9: boolean,
  l21_y_0: BinHeapNode + null,
  l21_y_1: BinHeapNode + null,
  l21_y_10: BinHeapNode + null,
  l21_y_11: BinHeapNode + null,
  l21_y_2: BinHeapNode + null,
  l21_y_3: BinHeapNode + null,
  l21_y_4: BinHeapNode + null,
  l21_y_5: BinHeapNode + null,
  l21_y_6: BinHeapNode + null,
  l21_y_7: BinHeapNode + null,
  l21_y_8: BinHeapNode + null,
  l21_y_9: BinHeapNode + null,
  l21_z_0: BinHeapNode + null,
  l21_z_1: BinHeapNode + null,
  l21_z_10: BinHeapNode + null,
  l21_z_11: BinHeapNode + null,
  l21_z_2: BinHeapNode + null,
  l21_z_3: BinHeapNode + null,
  l21_z_4: BinHeapNode + null,
  l21_z_5: BinHeapNode + null,
  l21_z_6: BinHeapNode + null,
  l21_z_7: BinHeapNode + null,
  l21_z_8: BinHeapNode + null,
  l21_z_9: BinHeapNode + null,
  nextData_0: ( Data ) -> one ( Data + null ),
  nodes_0: ( BinHeap ) -> ( BinHeapNode ),
  bparent_0,fparent_0: ( BinHeapNode ) -> lone ( BinHeapNode + null ),
  bsibling_0,fsibling_0: ( BinHeapNode ) -> lone ( BinHeapNode + null ),
  size_0: ( BinHeap ) -> one ( Int ),
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
  throw_5: Throwable + null,
  throw_6: Throwable + null,
  throw_7: Throwable + null,
  throw_8: Throwable + null,
  throw_9: Throwable + null,
  x_0: BinHeapNode + null
}


fact {
  precondition_BinHeap_decreaseKey_0[(QF.fchild_0+QF.bchild_0),
                                    QF.degree_0,
                                    QF.element_0,
                                    QF.head_0,
                                    QF.k_0,
                                    QF.nextData_0,
                                    QF.nodes_0,
                                    (QF.fparent_0+QF.bparent_0),
                                    (QF.fsibling_0+QF.bsibling_0),
                                    QF.size_0,
                                    QF.thiz_0,
                                    QF.throw_0,
                                    QF.x_0]

}

fact {
  BinHeap_decreaseKey_0[QF.throw_0,
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
                       QF.x_0,
                       QF.k_0,
                       QF.element_0,
                       QF.element_1,
                       QF.element_2,
                       QF.element_3,
                       QF.element_4,
                       QF.element_5,
                       QF.element_6,
                       QF.element_7,
                       QF.element_8,
                       QF.element_9,
                       QF.element_10,
                       QF.element_11,
                       QF.element_12,
                       QF.element_13,
                       QF.element_14,
                       QF.element_15,
                       QF.element_16,
                       QF.element_17,
                       QF.element_18,
                       QF.element_19,
                       QF.element_20,
                       QF.element_21,
                       (QF.fparent_0+QF.bparent_0),
                       QF.l21_lt_0,
                       QF.l21_lt_1,
                       QF.l21_lt_2,
                       QF.l21_lt_3,
                       QF.l21_lt_4,
                       QF.l21_lt_5,
                       QF.l21_lt_6,
                       QF.l21_lt_7,
                       QF.l21_lt_8,
                       QF.l21_lt_9,
                       QF.l21_lt_10,
                       QF.l21_lt_11,
                       QF.l21_b_0,
                       QF.l21_b_1,
                       QF.l21_b_2,
                       QF.l21_b_3,
                       QF.l21_b_4,
                       QF.l21_b_5,
                       QF.l21_b_6,
                       QF.l21_b_7,
                       QF.l21_b_8,
                       QF.l21_b_9,
                       QF.l21_b_10,
                       QF.l21_b_11,
                       QF.l21_nullDerefBool_0,
                       QF.l21_nullDerefBool_1,
                       QF.l21_nullDerefBool_2,
                       QF.l21_nullDerefBool_3,
                       QF.l21_nullDerefBool_4,
                       QF.l21_nullDerefBool_5,
                       QF.l21_nullDerefBool_6,
                       QF.l21_nullDerefBool_7,
                       QF.l21_nullDerefBool_8,
                       QF.l21_nullDerefBool_9,
                       QF.l21_nullDerefBool_10,
                       QF.l21_nullDerefBool_11,
                       QF.l21_nullDerefBool_12,
                       QF.l21_nullDerefBool_13,
                       QF.l21_nullDerefBool_14,
                       QF.l21_nullDerefBool_15,
                       QF.l21_nullDerefBool_16,
                       QF.l21_nullDerefBool_17,
                       QF.l21_nullDerefBool_18,
                       QF.l21_nullDerefBool_19,
                       QF.l21_nullDerefBool_20,
                       QF.l21_nullDerefBool_21,
                       QF.l21_nullDerefBool_22,
                       QF.l21_nullDerefBool_23,
                       QF.l21_nullDerefBool_24,
                       QF.l21_z_0,
                       QF.l21_z_1,
                       QF.l21_z_2,
                       QF.l21_z_3,
                       QF.l21_z_4,
                       QF.l21_z_5,
                       QF.l21_z_6,
                       QF.l21_z_7,
                       QF.l21_z_8,
                       QF.l21_z_9,
                       QF.l21_z_10,
                       QF.l21_z_11,
                       QF.l21_y_0,
                       QF.l21_y_1,
                       QF.l21_y_2,
                       QF.l21_y_3,
                       QF.l21_y_4,
                       QF.l21_y_5,
                       QF.l21_y_6,
                       QF.l21_y_7,
                       QF.l21_y_8,
                       QF.l21_y_9,
                       QF.l21_y_10,
                       QF.l21_y_11,
                       QF.l21_l14_result_0,
                       QF.l21_l14_result_1,
                       QF.l21_l14_result_2,
                       QF.l21_l8_nullDerefBool_0,
                       QF.l21_l8_nullDerefBool_1,
                       QF.l21_l9_temp_0,
                       QF.l21_l9_temp_1,
                       QF.l21_l13_nullDerefBool_0,
                       QF.l21_l13_nullDerefBool_1,
                       QF.l21_l13_nullDerefBool_2,
                       QF.l21_l13_nullDerefBool_3,
                       QF.l21_l13_nullDerefBool_4,
                       QF.l21_l8_result_0,
                       QF.l21_l8_result_1,
                       QF.l21_l8_result_2,
                       QF.l21_l16_nullDerefBool_0,
                       QF.l21_l16_nullDerefBool_1,
                       QF.l21_l11_nullDerefBool_0,
                       QF.l21_l11_nullDerefBool_1,
                       QF.l21_l11_nullDerefBool_2,
                       QF.l21_l11_nullDerefBool_3,
                       QF.l21_l11_nullDerefBool_4,
                       QF.l21_l0_result_0,
                       QF.l21_l0_result_1,
                       QF.l21_l0_result_2,
                       QF.l21_l0_nullDerefBool_0,
                       QF.l21_l0_nullDerefBool_1,
                       QF.l21_l4_result_0,
                       QF.l21_l4_result_1,
                       QF.l21_l4_result_2,
                       QF.l21_l17_temp_0,
                       QF.l21_l17_temp_1,
                       QF.l21_l11_temp_0,
                       QF.l21_l11_temp_1,
                       QF.l21_l2_nullDerefBool_0,
                       QF.l21_l2_nullDerefBool_1,
                       QF.l21_l7_nullDerefBool_0,
                       QF.l21_l7_nullDerefBool_1,
                       QF.l21_l7_nullDerefBool_2,
                       QF.l21_l7_nullDerefBool_3,
                       QF.l21_l7_nullDerefBool_4,
                       QF.l21_l6_result_0,
                       QF.l21_l6_result_1,
                       QF.l21_l6_result_2,
                       QF.l21_l18_result_0,
                       QF.l21_l18_result_1,
                       QF.l21_l18_result_2,
                       QF.l21_l19_nullDerefBool_0,
                       QF.l21_l19_nullDerefBool_1,
                       QF.l21_l19_nullDerefBool_2,
                       QF.l21_l19_nullDerefBool_3,
                       QF.l21_l19_nullDerefBool_4,
                       QF.l21_l14_nullDerefBool_0,
                       QF.l21_l14_nullDerefBool_1,
                       QF.l21_l1_temp_0,
                       QF.l21_l1_temp_1,
                       QF.l21_l5_temp_0,
                       QF.l21_l5_temp_1,
                       QF.l21_l4_nullDerefBool_0,
                       QF.l21_l4_nullDerefBool_1,
                       QF.l21_l10_result_0,
                       QF.l21_l10_result_1,
                       QF.l21_l10_result_2,
                       QF.l21_l20_result_0,
                       QF.l21_l20_result_1,
                       QF.l21_l20_result_2,
                       QF.l21_l9_nullDerefBool_0,
                       QF.l21_l9_nullDerefBool_1,
                       QF.l21_l9_nullDerefBool_2,
                       QF.l21_l9_nullDerefBool_3,
                       QF.l21_l9_nullDerefBool_4,
                       QF.l21_l19_temp_0,
                       QF.l21_l19_temp_1,
                       QF.l21_l5_nullDerefBool_0,
                       QF.l21_l5_nullDerefBool_1,
                       QF.l21_l5_nullDerefBool_2,
                       QF.l21_l5_nullDerefBool_3,
                       QF.l21_l5_nullDerefBool_4,
                       QF.l21_l6_nullDerefBool_0,
                       QF.l21_l6_nullDerefBool_1,
                       QF.l21_l15_temp_0,
                       QF.l21_l15_temp_1,
                       QF.l21_l16_result_0,
                       QF.l21_l16_result_1,
                       QF.l21_l16_result_2,
                       QF.l21_l18_nullDerefBool_0,
                       QF.l21_l18_nullDerefBool_1,
                       QF.l21_l3_nullDerefBool_0,
                       QF.l21_l3_nullDerefBool_1,
                       QF.l21_l3_nullDerefBool_2,
                       QF.l21_l3_nullDerefBool_3,
                       QF.l21_l3_nullDerefBool_4,
                       QF.l21_l20_nullDerefBool_0,
                       QF.l21_l20_nullDerefBool_1,
                       QF.l21_l15_nullDerefBool_0,
                       QF.l21_l15_nullDerefBool_1,
                       QF.l21_l15_nullDerefBool_2,
                       QF.l21_l15_nullDerefBool_3,
                       QF.l21_l15_nullDerefBool_4,
                       QF.l21_l1_nullDerefBool_0,
                       QF.l21_l1_nullDerefBool_1,
                       QF.l21_l1_nullDerefBool_2,
                       QF.l21_l1_nullDerefBool_3,
                       QF.l21_l1_nullDerefBool_4,
                       QF.l21_l12_nullDerefBool_0,
                       QF.l21_l12_nullDerefBool_1,
                       QF.l21_l13_temp_0,
                       QF.l21_l13_temp_1,
                       QF.l21_l12_result_0,
                       QF.l21_l12_result_1,
                       QF.l21_l12_result_2,
                       QF.l21_l7_temp_0,
                       QF.l21_l7_temp_1,
                       QF.l21_l2_result_0,
                       QF.l21_l2_result_1,
                       QF.l21_l2_result_2,
                       QF.l21_l3_temp_0,
                       QF.l21_l3_temp_1,
                       QF.l21_l17_nullDerefBool_0,
                       QF.l21_l17_nullDerefBool_1,
                       QF.l21_l17_nullDerefBool_2,
                       QF.l21_l17_nullDerefBool_3,
                       QF.l21_l17_nullDerefBool_4,
                       QF.l21_l10_nullDerefBool_0,
                       QF.l21_l10_nullDerefBool_1]

}

assert BinHeap_m2{
  postcondition_BinHeap_decreaseKey_0[(QF.fchild_0+QF.bchild_0),
                                     QF.degree_0,
                                     QF.element_0,
                                     QF.element_21,
                                     QF.head_0,
                                     QF.k_0,
                                     QF.nextData_0,
                                     QF.nodes_0,
                                     QF.nodes_0,
                                     (QF.fparent_0+QF.bparent_0),
                                     (QF.fsibling_0+QF.bsibling_0),
                                     QF.size_0,
                                     QF.thiz_0,
                                     QF.thiz_0,
                                     QF.throw_44,
                                     QF.x_0,
                                     QF.x_0]
}
check BinHeap_m2 for 0 but 
                 exactly 1 BinHeap, 
                 exactly 17 BinHeapNode,
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
                 exactly 1 D15,
                 exactly 1 D16,
                 6 int  



one sig N0,N1,N2,N3,N4,N5,N6,N7,N8,N9,N10,N11,N12,N13,N14,N15,N16 extends BinHeapNode {} 

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
+N15->null 
+N16->null 
 
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
+N4->N8 
+N4->null 
+N5->N7 
+N5->N8 
+N5->N9 
+N5->N10 
+N5->null 
+N6->N8 
+N6->N9 
+N6->N11 
+N6->N12 
+N6->null 
+N7->N9 
+N7->N10 
+N7->N13 
+N7->N14 
+N7->null 
+N8->N10 
+N8->N11 
+N8->N15 
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
+N15->null 
+N16->null 
 
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
+N4->N9 
+N4->null 
+N5->N8 
+N5->N9 
+N5->N10 
+N5->N11 
+N5->null 
+N6->N9 
+N6->N10 
+N6->N12 
+N6->N13 
+N6->null 
+N7->N10 
+N7->N11 
+N7->N14 
+N7->N15 
+N7->null 
+N8->N11 
+N8->N12 
+N8->N16 
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
+N15->null 
+N16->null 
 
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
+N8->N0 
+N8->N1 
+N8->N3 
+N8->N4 
+N8->N5 
+N9->N1 
+N9->N2 
+N9->N4 
+N9->N5 
+N9->N6 
+N10->N2 
+N10->N3 
+N10->N5 
+N10->N6 
+N10->N7 
+N11->N3 
+N11->N4 
+N11->N5 
+N11->N7 
+N11->N8 
+N12->N1 
+N12->N5 
+N12->N6 
+N12->N8 
+N12->N9 
+N13->N2 
+N13->N6 
+N13->N9 
+N14->N3 
+N14->N7 
+N14->N10 
+N15->N4 
+N15->N7 
+N16->N8 
 
QF.bsibling_0 in none->none 
} 
// fact int_fields 
fact { 
QF.degree_0 in N0->0 
+N0->1 
+N0->2 
+N0->3 
+N0->4 
+N1->0 
+N1->1 
+N1->2 
+N1->3 
+N1->4 
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
+N15->0 
+N16->0 

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
+N0->D15 
+N0->D16 
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
+N1->D15 
+N1->D16 
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
+N2->D15 
+N2->D16 
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
+N3->D15 
+N3->D16 
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
+N4->D15 
+N4->D16 
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
+N5->D15 
+N5->D16 
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
+N6->D15 
+N6->D16 
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
+N7->D15 
+N7->D16 
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
+N8->D15 
+N8->D16 
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
+N9->D15 
+N9->D16 
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
+N10->D15 
+N10->D16 
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
+N11->D15 
+N11->D16 
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
+N12->D15 
+N12->D16 
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
+N13->D15 
+N13->D16 
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
+N14->D15 
+N14->D16 
+N15->D0 
+N15->D1 
+N15->D2 
+N15->D3 
+N15->D4 
+N15->D5 
+N15->D6 
+N15->D7 
+N15->D8 
+N15->D9 
+N15->D10 
+N15->D11 
+N15->D12 
+N15->D13 
+N15->D14 
+N15->D15 
+N15->D16 
+N16->D0 
+N16->D1 
+N16->D2 
+N16->D3 
+N16->D4 
+N16->D5 
+N16->D6 
+N16->D7 
+N16->D8 
+N16->D9 
+N16->D10 
+N16->D11 
+N16->D12 
+N16->D13 
+N16->D14 
+N16->D15 
+N16->D16 

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
+QF.thiz_0->16 
+QF.thiz_0->17 

} 
//fact root_node_fields 
fact { 
(QF.head_0) in QF.thiz_0->N0 
+QF.thiz_0->null 

} 
