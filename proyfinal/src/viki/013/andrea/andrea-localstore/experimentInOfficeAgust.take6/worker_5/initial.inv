/* 
 * DynAlloy translator options 
 * --------------------------- 
 * applySimplifications= true
 * assertionId= BinHeap_m1
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




//-------------- amelia_data_Data--------------//
abstract sig Data extends Object {}
{}


fact {null !in BinHeap.(QF.head_0)}



one sig QF {
  bchild_0,fchild_0: ( BinHeapNode ) -> lone ( BinHeapNode + null ),
  degree_0: ( BinHeapNode ) -> one ( Int ),
  element_0: ( BinHeapNode ) -> one ( Data + null ),
  head_0: ( BinHeap ) -> one ( BinHeapNode + null ),
  nextData_0: ( Data ) -> one ( Data + null ),
  nodes_0: ( BinHeap ) -> ( BinHeapNode ),
  bparent_0,fparent_0: ( BinHeapNode ) -> lone ( BinHeapNode + null ),
  bsibling_0,fsibling_0: ( BinHeapNode ) -> lone ( BinHeapNode + null ),
  size_0: ( BinHeap ) -> one ( Int ),
  thiz_0: BinHeap
}





run {BinHeap_object_invariant[
  QF.fchild_0 + QF.bchild_0,
  QF.degree_0,
  QF.element_0,
  QF.head_0,
  QF.nextData_0,
  QF.fparent_0 + QF.bparent_0,
  QF.fsibling_0 + QF.bsibling_0,
  QF.size_0,
  QF.thiz_0]} for 0 but 
                 exactly 1 BinHeap, 
                 exactly 20 BinHeapNode,
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
                 exactly 1 D17,
                 exactly 1 D18,
                 exactly 1 D19,
                 6 int  



one sig N0,N1,N2,N3,N4,N5,N6,N7,N8,N9,N10,N11,N12,N13,N14,N15,N16,N17,N18,N19 extends BinHeapNode {} 

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
+N17->null 
+N18->null 
+N19->null 
 
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
+N6->N10 
+N6->N11 
+N6->N12 
+N6->null 
+N7->N9 
+N7->N10 
+N7->N11 
+N7->N12 
+N7->N13 
+N7->N14 
+N7->null 
+N8->N10 
+N8->N11 
+N8->N12 
+N8->N13 
+N8->N14 
+N8->N15 
+N8->null 
+N9->N11 
+N9->N12 
+N9->N14 
+N9->N15 
+N9->N16 
+N9->null 
+N10->N13 
+N10->N16 
+N10->N17 
+N10->null 
+N11->N18 
+N11->null 
+N12->null 
+N13->null 
+N14->null 
+N15->null 
+N16->null 
+N17->null 
+N18->null 
+N19->null 
 
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
+N6->N11 
+N6->N12 
+N6->N13 
+N6->null 
+N7->N10 
+N7->N11 
+N7->N12 
+N7->N13 
+N7->N14 
+N7->N15 
+N7->null 
+N8->N11 
+N8->N12 
+N8->N13 
+N8->N14 
+N8->N15 
+N8->N16 
+N8->null 
+N9->N12 
+N9->N13 
+N9->N15 
+N9->N16 
+N9->N17 
+N9->null 
+N10->N14 
+N10->N17 
+N10->N18 
+N10->null 
+N11->N19 
+N11->null 
+N12->null 
+N13->null 
+N14->null 
+N15->null 
+N16->null 
+N17->null 
+N18->null 
+N19->null 
 
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
+N10->N1 
+N10->N2 
+N10->N3 
+N10->N5 
+N10->N6 
+N10->N7 
+N11->N2 
+N11->N3 
+N11->N4 
+N11->N5 
+N11->N6 
+N11->N7 
+N11->N8 
+N12->N1 
+N12->N4 
+N12->N5 
+N12->N6 
+N12->N7 
+N12->N8 
+N12->N9 
+N13->N2 
+N13->N5 
+N13->N6 
+N13->N7 
+N13->N8 
+N13->N9 
+N14->N3 
+N14->N6 
+N14->N7 
+N14->N8 
+N14->N10 
+N15->N4 
+N15->N7 
+N15->N8 
+N15->N9 
+N16->N3 
+N16->N5 
+N16->N8 
+N16->N9 
+N17->N6 
+N17->N9 
+N17->N10 
+N18->N7 
+N18->N10 
+N19->N11 
 
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
+N2->4 
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
+N7->2 
+N8->0 
+N8->1 
+N9->0 
+N9->1 
+N10->0 
+N10->1 
+N11->0 
+N11->1 
+N12->0 
+N13->0 
+N14->0 
+N15->0 
+N16->0 
+N17->0 
+N18->0 
+N19->0 

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
+N0->D17 
+N0->D18 
+N0->D19 
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
+N1->D17 
+N1->D18 
+N1->D19 
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
+N2->D17 
+N2->D18 
+N2->D19 
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
+N3->D17 
+N3->D18 
+N3->D19 
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
+N4->D17 
+N4->D18 
+N4->D19 
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
+N5->D17 
+N5->D18 
+N5->D19 
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
+N6->D17 
+N6->D18 
+N6->D19 
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
+N7->D17 
+N7->D18 
+N7->D19 
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
+N8->D17 
+N8->D18 
+N8->D19 
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
+N9->D17 
+N9->D18 
+N9->D19 
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
+N10->D17 
+N10->D18 
+N10->D19 
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
+N11->D17 
+N11->D18 
+N11->D19 
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
+N12->D17 
+N12->D18 
+N12->D19 
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
+N13->D17 
+N13->D18 
+N13->D19 
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
+N14->D17 
+N14->D18 
+N14->D19 
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
+N15->D17 
+N15->D18 
+N15->D19 
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
+N16->D17 
+N16->D18 
+N16->D19 
+N17->D0 
+N17->D1 
+N17->D2 
+N17->D3 
+N17->D4 
+N17->D5 
+N17->D6 
+N17->D7 
+N17->D8 
+N17->D9 
+N17->D10 
+N17->D11 
+N17->D12 
+N17->D13 
+N17->D14 
+N17->D15 
+N17->D16 
+N17->D17 
+N17->D18 
+N17->D19 
+N18->D0 
+N18->D1 
+N18->D2 
+N18->D3 
+N18->D4 
+N18->D5 
+N18->D6 
+N18->D7 
+N18->D8 
+N18->D9 
+N18->D10 
+N18->D11 
+N18->D12 
+N18->D13 
+N18->D14 
+N18->D15 
+N18->D16 
+N18->D17 
+N18->D18 
+N18->D19 
+N19->D0 
+N19->D1 
+N19->D2 
+N19->D3 
+N19->D4 
+N19->D5 
+N19->D6 
+N19->D7 
+N19->D8 
+N19->D9 
+N19->D10 
+N19->D11 
+N19->D12 
+N19->D13 
+N19->D14 
+N19->D15 
+N19->D16 
+N19->D17 
+N19->D18 
+N19->D19 

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
+QF.thiz_0->18 
+QF.thiz_0->19 
+QF.thiz_0->20 

} 
//fact root_node_fields 
fact { 
(QF.head_0) in QF.thiz_0->N0 
+QF.thiz_0->null 

} 
