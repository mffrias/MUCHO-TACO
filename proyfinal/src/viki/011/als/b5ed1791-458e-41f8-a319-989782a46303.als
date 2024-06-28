/* 
 * DynAlloy translator options 
 * --------------------------- 
 * applySimplifications= true
 * assertionId= TreeSet_m1
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





//-------------- amelia_data_D10--------------//
sig D10 extends Data {}
{}





//-------------- amelia_data_D8--------------//
sig D8 extends Data {}
{}





//-------------- amelia_data_D7--------------//
sig D7 extends Data {}
{}





//-------------- amelia_rbtree_TreeSet--------------//
sig TreeSet extends Object {}
{}




pred TreeSetCondition13[
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

pred TreeSetNode_blackHeight_abstraction[
  blackHeight:univ->univ,
  color:univ->univ,
  left:univ->univ,
  right:univ->univ,
  thiz:univ
]{
   (
     (
       equ[thiz.left,
          null]
       and 
       equ[thiz.right,
          null]
     )
     implies 
             equ[thiz.blackHeight,
                1]
   )
   and 
   (
     (
       neq[thiz.left,
          null]
       and 
       equ[thiz.right,
          null]
     )
     implies 
             (
               (
                 isSubset[thiz,
                         fun_set_difference[(thiz.left).(fun_reflexive_closure[left+right]),null]]
                 implies 
                         equ[thiz.blackHeight,
                            0]
               )
               and 
               (
                 isNotSubset[thiz,
                            fun_set_difference[(thiz.left).(fun_reflexive_closure[left+right]),null]]
                 implies 
                         (
                           (
                             equ[(thiz.left).color,
                                true]
                             implies 
                                     equ[thiz.blackHeight,
                                        add[(thiz.left).blackHeight,1]]
                           )
                           and 
                           (
                             equ[(thiz.left).color,
                                false]
                             implies 
                                     equ[thiz.blackHeight,
                                        (thiz.left).blackHeight]
                           )
                         )
               )
             )
   )
   and 
   (
     (
       equ[thiz.left,
          null]
       and 
       neq[thiz.right,
          null]
     )
     implies 
             (
               (
                 isSubset[thiz,
                         fun_set_difference[(thiz.right).(fun_reflexive_closure[left+right]),null]]
                 implies 
                         equ[thiz.blackHeight,
                            0]
               )
               and 
               (
                 isNotSubset[thiz,
                            fun_set_difference[(thiz.right).(fun_reflexive_closure[left+right]),null]]
                 implies 
                         (
                           (
                             equ[(thiz.right).color,
                                true]
                             implies 
                                     equ[thiz.blackHeight,
                                        add[(thiz.right).blackHeight,1]]
                           )
                           and 
                           (
                             equ[(thiz.right).color,
                                false]
                             implies 
                                     equ[thiz.blackHeight,
                                        (thiz.right).blackHeight]
                           )
                         )
               )
             )
   )
   and 
   (
     (
       neq[thiz.left,
          null]
       and 
       neq[thiz.right,
          null]
     )
     implies 
             (
               (
                 isSubset[thiz,
                         fun_set_difference[thiz.(fun_closure[left+right]),null]]
                 implies 
                         equ[thiz.blackHeight,
                            0]
               )
               and 
               (
                 isNotSubset[thiz,
                            fun_set_difference[thiz.(fun_closure[left+right]),null]]
                 implies 
                         (
                           (
                             equ[(thiz.left).color,
                                true]
                             implies 
                                     equ[thiz.blackHeight,
                                        add[(thiz.left).blackHeight,1]]
                           )
                           and 
                           (
                             equ[(thiz.left).color,
                                false]
                             implies 
                                     equ[thiz.blackHeight,
                                        (thiz.left).blackHeight]
                           )
                         )
               )
             )
   )

}

pred TreeSet_invariant[
  BLACK:univ->univ,
  RED:univ->univ,
  blackHeight:univ->univ,
  color:univ->univ,
  key:univ->univ,
  left:univ->univ,
  nextData:univ->univ,
  parent:univ->univ,
  right:univ->univ,
  root:univ->univ,
  thiz:univ
]{
   equ[thiz.BLACK,
      true]
   and 
   isSubset[(thiz.root).parent,
           null]
   and 
   equ[thiz.RED,
      false]
   and 
   (
     all n:TreeSetNode | {
       isSubset[n,
               fun_set_difference[(thiz.root).(fun_reflexive_closure[left+right+parent]),null]]
       implies 
               (
                 neq[n.key,
                    null]
                 and 
                 (
                   neq[n.left,
                      null]
                   implies 
                           equ[(n.left).parent,
                              n]
                 )
                 and 
                 (
                   neq[n.right,
                      null]
                   implies 
                           equ[(n.right).parent,
                              n]
                 )
                 and 
                 (
                   neq[n.parent,
                      null]
                   implies 
                           isSubset[n,
                                   (n.parent).(left+right)]
                 )
                 and 
                 isNotSubset[n,
                            n.(fun_closure[parent])]
                 and 
                 (
                   all x:fun_set_difference[((n.left).(fun_closure[left+right]))+(n.left),null] | {
                     isSubset[n.key,
                             (x.key).(fun_closure[nextData])]
                   
                   }
                 )
                 and 
                 (
                   all x:fun_set_difference[((n.right).(fun_closure[left+right]))+(n.right),null] | {
                     isSubset[x.key,
                             (n.key).(fun_closure[nextData])]
                   
                   }
                 )
                 and 
                 (
                   (
                     equ[n.color,
                        thiz.RED]
                     and 
                     neq[n.parent,
                        null]
                   )
                   implies 
                           equ[(n.parent).color,
                              thiz.BLACK]
                 )
                 and 
                 (
                   (
                     equ[n.left,
                        null]
                     and 
                     equ[n.right,
                        null]
                   )
                   implies 
                           equ[n.blackHeight,
                              1]
                 )
                 and 
                 (
                   (
                     neq[n.left,
                        null]
                     and 
                     equ[n.right,
                        null]
                   )
                   implies 
                           (
                             equ[(n.left).color,
                                thiz.RED]
                             and 
                             equ[(n.left).blackHeight,
                                1]
                             and 
                             equ[n.blackHeight,
                                1]
                           )
                 )
                 and 
                 (
                   (
                     equ[n.left,
                        null]
                     and 
                     neq[n.right,
                        null]
                   )
                   implies 
                           (
                             equ[(n.right).color,
                                thiz.RED]
                             and 
                             equ[(n.right).blackHeight,
                                1]
                             and 
                             equ[n.blackHeight,
                                1]
                           )
                 )
                 and 
                 (
                   (
                     neq[n.left,
                        null]
                     and 
                     neq[n.right,
                        null]
                     and 
                     equ[(n.left).color,
                        thiz.RED]
                     and 
                     equ[(n.right).color,
                        thiz.RED]
                   )
                   implies 
                           (
                             equ[(n.left).blackHeight,
                                (n.right).blackHeight]
                             and 
                             equ[n.blackHeight,
                                (n.left).blackHeight]
                           )
                 )
                 and 
                 (
                   (
                     neq[n.left,
                        null]
                     and 
                     neq[n.right,
                        null]
                     and 
                     equ[(n.left).color,
                        thiz.BLACK]
                     and 
                     equ[(n.right).color,
                        thiz.BLACK]
                   )
                   implies 
                           (
                             equ[(n.left).blackHeight,
                                (n.right).blackHeight]
                             and 
                             equ[n.blackHeight,
                                add[(n.left).blackHeight,1]]
                           )
                 )
                 and 
                 (
                   (
                     neq[n.left,
                        null]
                     and 
                     neq[n.right,
                        null]
                     and 
                     equ[(n.left).color,
                        thiz.RED]
                     and 
                     equ[(n.right).color,
                        thiz.BLACK]
                   )
                   implies 
                           (
                             equ[(n.left).blackHeight,
                                add[(n.right).blackHeight,1]]
                             and 
                             equ[n.blackHeight,
                                (n.left).blackHeight]
                           )
                 )
                 and 
                 (
                   (
                     neq[n.left,
                        null]
                     and 
                     neq[n.right,
                        null]
                     and 
                     equ[(n.left).color,
                        thiz.BLACK]
                     and 
                     equ[(n.right).color,
                        thiz.RED]
                   )
                   implies 
                           (
                             equ[(n.right).blackHeight,
                                add[(n.left).blackHeight,1]]
                             and 
                             equ[n.blackHeight,
                                (n.right).blackHeight]
                           )
                 )
               )
     
     }
   )
   and 
   (
     neq[thiz.root,
        null]
     implies 
             equ[(thiz.root).color,
                thiz.BLACK]
   )

}

pred TreeSetCondition8[
  found:univ,
  p:univ
]{
   neq[p,
      null]
   and 
   equ[found,
      null]

}

pred TreeSetCondition3[
  p:univ
]{
   not (
     isEmptyOrNull[p])

}

pred TreeSetCondition2[
  p:univ
]{
   isEmptyOrNull[p]

}

pred TreeSet_nodes_abstraction[
  left:univ->univ,
  nodes:univ->univ,
  right:univ->univ,
  root:univ->univ,
  thiz:univ
]{
   equ[thiz.nodes,
      fun_set_difference[(thiz.root).(fun_reflexive_closure[left+right]),null]]

}

pred TreeSetCondition12[
  nullDerefBool:univ,
  throw:univ
]{
   equ[nullDerefBool,
      true]
   and 
   equ[throw,
      null]

}

pred TreeSetCondition1[
  thiz:univ
]{
   not (
     isEmptyOrNull[thiz])

}

pred TreeSetCondition10[
  myKey:univ
]{
   equ[myKey,
      null]

}

pred TreeSetCondition11[
  myKey:univ
]{
   not (
     equ[myKey,
        null]
   )

}

pred TreeSet_ensures[
  key':univ->univ,
  nodes':univ->univ,
  o':univ,
  return':univ,
  thiz:univ
]{
   equ[return',
      true]
   iff
   some n:TreeSetNode | {
     isSubset[n,
             thiz.nodes']
     and 
     equ[n.key',
        o']
   
   }

}

pred TreeSetCondition7[
  lt:univ
]{
   not (
     equ[lt,
        true]
   )

}

pred Data_invariant[
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

pred precondition_TreeSet_contains_0[
  BLACK:univ->univ,
  RED:univ->univ,
  blackHeight:univ->univ,
  color:univ->univ,
  key:univ->univ,
  left:univ->univ,
  nextData:univ->univ,
  nodes:univ->univ,
  o:univ,
  parent:univ->univ,
  right:univ->univ,
  root:univ->univ,
  thiz:univ
]{
   TreeSet_nodes_abstraction[left,
                            nodes,
                            right,
                            root,
                            thiz]
   and 
   TreeSet_invariant[BLACK,
                    RED,
                    blackHeight,
                    color,
                    key,
                    left,
                    nextData,
                    parent,
                    right,
                    root,
                    thiz]
   and 
   (
     all objx:TreeSetNode | {
       TreeSetNode_blackHeight_abstraction[blackHeight,
                                          color,
                                          left,
                                          right,
                                          objx]
     
     }
   )
   and 
   TreeSet_requires[o]
   and 
   Data_invariant[nextData]

}

pred TreeSetCondition6[
  lt:univ
]{
   equ[lt,
      true]

}

pred TreeSet_requires[
  o:univ
]{
   neq[o,
      null]

}

pred TreeSetCondition9[
  found:univ,
  p:univ
]{
   not (
     neq[p,
        null]
     and 
     equ[found,
        null]
   )

}

pred TreeSetCondition0[
  thiz:univ
]{
   isEmptyOrNull[thiz]

}

pred TreeSetCondition15[
  entry:univ
]{
   not (
     equ[entry,
        null]
   )

}

pred TreeSetCondition14[
  entry:univ
]{
   equ[entry,
      null]

}

pred TreeSetCondition5[
  gt:univ
]{
   not (
     equ[gt,
        true]
   )

}

pred TreeSetCondition4[
  gt:univ
]{
   equ[gt,
      true]

}

pred postcondition_TreeSet_contains_0[
  key':univ->univ,
  nodes':univ->univ,
  o':univ,
  return':univ,
  thiz:univ,
  throw':univ
]{
   TreeSet_ensures[key',
                  nodes',
                  o',
                  return',
                  thiz]
   and 
   equ[throw',
      null]

}
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




pred DataCondition76[
  thiz:univ
]{
   instanceOf[thiz,
             D3]

}

pred DataCondition77[
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

pred DataCondition36[
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

pred DataCondition53[
  thiz:univ
]{
   not (
     instanceOf[thiz,
               D15]
   )

}

pred DataCondition52[
  thiz:univ
]{
   instanceOf[thiz,
             D15]

}

pred DataCondition67[
  thiz:univ
]{
   not (
     instanceOf[thiz,
               D8]
   )

}

pred DataCondition20[
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

pred DataCondition13[
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

pred DataCondition21[
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

pred DataCondition14[
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

pred DataCondition15[
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

pred DataCondition12[
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

pred DataCondition66[
  thiz:univ
]{
   instanceOf[thiz,
             D8]

}

pred DataCondition39[
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

pred DataCondition38[
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

pred DataCondition78[
  thiz:univ
]{
   instanceOf[thiz,
             D2]

}

pred DataCondition51[
  thiz:univ
]{
   not (
     instanceOf[thiz,
               D16]
   )

}

pred DataCondition79[
  thiz:univ
]{
   not (
     instanceOf[thiz,
               D2]
   )

}

pred DataCondition50[
  thiz:univ
]{
   instanceOf[thiz,
             D16]

}

pred DataCondition69[
  thiz:univ
]{
   not (
     instanceOf[thiz,
               D7]
   )

}

pred DataCondition68[
  thiz:univ
]{
   instanceOf[thiz,
             D7]

}

pred DataCondition49[
  thiz:univ
]{
   not (
     instanceOf[thiz,
               D17]
   )

}

pred DataCondition29[
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

pred DataCondition48[
  thiz:univ
]{
   instanceOf[thiz,
             D17]

}

pred DataCondition28[
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

pred DataCondition70[
  thiz:univ
]{
   instanceOf[thiz,
             D6]

}

pred DataCondition71[
  thiz:univ
]{
   not (
     instanceOf[thiz,
               D6]
   )

}

pred DataCondition19[
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

pred DataCondition18[
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

pred DataCondition84[
  lte:univ
]{
   equ[lte,
      true]

}

pred DataCondition85[
  lte:univ
]{
   not (
     equ[lte,
        true]
   )

}

pred DataCondition81[
  thiz:univ
]{
   not (
     instanceOf[thiz,
               D1]
   )

}

pred DataCondition80[
  thiz:univ
]{
   instanceOf[thiz,
             D1]

}

pred DataCondition32[
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

pred DataCondition33[
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

pred DataCondition82[
  thiz:univ
]{
   instanceOf[thiz,
             D0]

}

pred DataCondition3[
  data:univ,
  thiz:univ
]{
   not (
     equ[thiz,
        data]
   )

}

pred DataCondition83[
  thiz:univ
]{
   not (
     instanceOf[thiz,
               D0]
   )

}

pred DataCondition46[
  thiz:univ
]{
   instanceOf[thiz,
             D18]

}

pred DataCondition2[
  data:univ,
  thiz:univ
]{
   equ[thiz,
      data]

}

pred DataCondition47[
  thiz:univ
]{
   not (
     instanceOf[thiz,
               D18]
   )

}

pred DataCondition57[
  thiz:univ
]{
   not (
     instanceOf[thiz,
               D13]
   )

}

pred DataCondition56[
  thiz:univ
]{
   instanceOf[thiz,
             D13]

}

pred DataCondition60[
  thiz:univ
]{
   instanceOf[thiz,
             D11]

}

pred DataCondition61[
  thiz:univ
]{
   not (
     instanceOf[thiz,
               D11]
   )

}

pred DataCondition35[
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

pred DataCondition4[
  nullDerefBool:univ,
  throw:univ
]{
   equ[nullDerefBool,
      true]
   and 
   equ[throw,
      null]

}

pred DataCondition72[
  thiz:univ
]{
   instanceOf[thiz,
             D5]

}

pred DataCondition5[
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

pred DataCondition73[
  thiz:univ
]{
   not (
     instanceOf[thiz,
               D5]
   )

}

pred DataCondition34[
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

pred DataCondition58[
  thiz:univ
]{
   instanceOf[thiz,
             D12]

}

pred DataCondition59[
  thiz:univ
]{
   not (
     instanceOf[thiz,
               D12]
   )

}

pred DataCondition43[
  data:univ
]{
   not (
     instanceOf[data,
               D19]
   )

}

pred DataCondition42[
  data:univ
]{
   instanceOf[data,
             D19]

}

pred DataCondition17[
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

pred DataCondition8[
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

pred DataCondition16[
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

pred DataCondition1[
  lt:univ
]{
   not (
     equ[lt,
        true]
   )

}

pred DataCondition9[
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

pred DataCondition22[
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

pred DataCondition31[
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

pred DataCondition45[
  thiz:univ
]{
   not (
     instanceOf[thiz,
               D19]
   )

}

pred DataCondition0[
  lt:univ
]{
   equ[lt,
      true]

}

pred DataCondition23[
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

pred DataCondition30[
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

pred DataCondition65[
  thiz:univ
]{
   not (
     instanceOf[thiz,
               D9]
   )

}

pred DataCondition64[
  thiz:univ
]{
   instanceOf[thiz,
             D9]

}

pred DataCondition44[
  thiz:univ
]{
   instanceOf[thiz,
             D19]

}

pred DataCondition41[
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

pred DataCondition25[
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

pred DataCondition62[
  thiz:univ
]{
   instanceOf[thiz,
             D10]

}

pred DataCondition40[
  data:univ
]{
   instanceOf[data,
             D18]
   or 
   instanceOf[data,
             D19]

}

pred DataCondition55[
  thiz:univ
]{
   not (
     instanceOf[thiz,
               D14]
   )

}

pred DataCondition63[
  thiz:univ
]{
   not (
     instanceOf[thiz,
               D10]
   )

}

pred DataCondition54[
  thiz:univ
]{
   instanceOf[thiz,
             D14]

}

pred DataCondition24[
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

pred DataCondition75[
  thiz:univ
]{
   not (
     instanceOf[thiz,
               D4]
   )

}

pred DataCondition74[
  thiz:univ
]{
   instanceOf[thiz,
             D4]

}

pred DataCondition11[
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

pred DataCondition27[
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

pred DataCondition6[
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

pred DataCondition10[
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

pred DataCondition26[
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

pred DataCondition7[
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
//-------------- amelia_rbtree_TreeSetNode--------------//
sig TreeSetNode extends Object {}
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


pred TreeSet_getEntry_0[
  thiz_0: TreeSet,
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
  throw_47: Throwable + null,
  throw_48: Throwable + null,
  throw_49: Throwable + null,
  throw_50: Throwable + null,
  throw_51: Throwable + null,
  throw_52: Throwable + null,
  throw_53: Throwable + null,
  throw_54: Throwable + null,
  throw_55: Throwable + null,
  throw_56: Throwable + null,
  throw_57: Throwable + null,
  throw_58: Throwable + null,
  throw_59: Throwable + null,
  throw_60: Throwable + null,
  throw_61: Throwable + null,
  throw_62: Throwable + null,
  throw_63: Throwable + null,
  throw_64: Throwable + null,
  throw_65: Throwable + null,
  throw_66: Throwable + null,
  throw_67: Throwable + null,
  throw_68: Throwable + null,
  throw_69: Throwable + null,
  throw_70: Throwable + null,
  throw_71: Throwable + null,
  throw_72: Throwable + null,
  throw_73: Throwable + null,
  throw_74: Throwable + null,
  throw_75: Throwable + null,
  throw_76: Throwable + null,
  throw_77: Throwable + null,
  throw_78: Throwable + null,
  throw_79: Throwable + null,
  throw_80: Throwable + null,
  throw_81: Throwable + null,
  throw_82: Throwable + null,
  return_1: TreeSetNode + null,
  myKey_0: Data + null,
  root_0: ( TreeSet ) -> one ( TreeSetNode + null ),
  right_0: ( TreeSetNode ) -> one ( TreeSetNode + null ),
  left_0: ( TreeSetNode ) -> one ( TreeSetNode + null ),
  key_0: ( TreeSetNode ) -> one ( Data + null ),
  ex_0: NullPointerException + null,
  ex_1: NullPointerException + null,
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
  p_0: TreeSetNode + null,
  p_1: TreeSetNode + null,
  p_2: TreeSetNode + null,
  p_3: TreeSetNode + null,
  p_4: TreeSetNode + null,
  p_5: TreeSetNode + null,
  p_6: TreeSetNode + null,
  p_7: TreeSetNode + null,
  p_8: TreeSetNode + null,
  p_9: TreeSetNode + null,
  p_10: TreeSetNode + null,
  p_11: TreeSetNode + null,
  gt_0: boolean,
  gt_1: boolean,
  gt_2: boolean,
  gt_3: boolean,
  gt_4: boolean,
  gt_5: boolean,
  gt_6: boolean,
  gt_7: boolean,
  gt_8: boolean,
  gt_9: boolean,
  gt_10: boolean,
  found_1: TreeSetNode + null,
  found_2: TreeSetNode + null,
  found_3: TreeSetNode + null,
  found_4: TreeSetNode + null,
  found_5: TreeSetNode + null,
  found_6: TreeSetNode + null,
  found_7: TreeSetNode + null,
  found_8: TreeSetNode + null,
  found_9: TreeSetNode + null,
  found_10: TreeSetNode + null,
  found_11: TreeSetNode + null,
  l14_result_0: boolean,
  l14_result_1: boolean,
  l14_result_2: boolean,
  l8_nullDerefBool_0: boolean,
  l8_nullDerefBool_1: boolean,
  l15_l2_l1_nullDerefBool_0: boolean,
  l15_l2_l1_nullDerefBool_1: boolean,
  l21_nullDerefBool_0: boolean,
  l21_nullDerefBool_1: boolean,
  l15_lte_0: boolean,
  l15_lte_1: boolean,
  l13_gt_0: boolean,
  l13_gt_1: boolean,
  l16_nullDerefBool_0: boolean,
  l16_nullDerefBool_1: boolean,
  l13_l2_l1_result_0: boolean,
  l13_l2_l1_result_1: boolean,
  l13_l2_l1_result_2: boolean,
  l17_l2_lt_0: boolean,
  l17_l2_lt_1: boolean,
  l13_lte_0: boolean,
  l13_lte_1: boolean,
  l19_gt_0: boolean,
  l19_gt_1: boolean,
  l5_l2_l1_result_0: boolean,
  l5_l2_l1_result_1: boolean,
  l5_l2_l1_result_2: boolean,
  l9_l2_l1_nullDerefBool_0: boolean,
  l9_l2_l1_nullDerefBool_1: boolean,
  l5_l2_l1_nullDerefBool_0: boolean,
  l5_l2_l1_nullDerefBool_1: boolean,
  l21_gt_0: boolean,
  l21_gt_1: boolean,
  l4_result_0: boolean,
  l4_result_1: boolean,
  l4_result_2: boolean,
  l13_l2_lte_0: boolean,
  l13_l2_lte_1: boolean,
  l13_l2_lte_2: boolean,
  l19_lte_0: boolean,
  l19_lte_1: boolean,
  l11_gt_0: boolean,
  l11_gt_1: boolean,
  l7_l2_l1_nullDerefBool_0: boolean,
  l7_l2_l1_nullDerefBool_1: boolean,
  l7_nullDerefBool_0: boolean,
  l7_nullDerefBool_1: boolean,
  l3_lte_0: boolean,
  l3_lte_1: boolean,
  l5_l2_nullDerefBool_0: boolean,
  l5_l2_nullDerefBool_1: boolean,
  l18_result_0: boolean,
  l18_result_1: boolean,
  l18_result_2: boolean,
  l19_nullDerefBool_0: boolean,
  l19_nullDerefBool_1: boolean,
  l3_l2_l1_nullDerefBool_0: boolean,
  l3_l2_l1_nullDerefBool_1: boolean,
  l11_l2_l1_result_0: boolean,
  l11_l2_l1_result_1: boolean,
  l11_l2_l1_result_2: boolean,
  l7_l2_l1_result_0: boolean,
  l7_l2_l1_result_1: boolean,
  l7_l2_l1_result_2: boolean,
  l4_nullDerefBool_0: boolean,
  l4_nullDerefBool_1: boolean,
  l10_result_0: boolean,
  l10_result_1: boolean,
  l10_result_2: boolean,
  l9_l2_l1_result_0: boolean,
  l9_l2_l1_result_1: boolean,
  l9_l2_l1_result_2: boolean,
  l9_nullDerefBool_0: boolean,
  l9_nullDerefBool_1: boolean,
  l5_nullDerefBool_0: boolean,
  l5_nullDerefBool_1: boolean,
  l6_nullDerefBool_0: boolean,
  l6_nullDerefBool_1: boolean,
  l3_gt_0: boolean,
  l3_gt_1: boolean,
  l5_l2_lt_0: boolean,
  l5_l2_lt_1: boolean,
  l19_l2_lt_0: boolean,
  l19_l2_lt_1: boolean,
  l9_lte_0: boolean,
  l9_lte_1: boolean,
  l21_l2_lt_0: boolean,
  l21_l2_lt_1: boolean,
  l15_l2_l1_result_0: boolean,
  l15_l2_l1_result_1: boolean,
  l15_l2_l1_result_2: boolean,
  l19_l2_l1_result_0: boolean,
  l19_l2_l1_result_1: boolean,
  l19_l2_l1_result_2: boolean,
  l7_l2_lt_0: boolean,
  l7_l2_lt_1: boolean,
  l16_result_0: boolean,
  l16_result_1: boolean,
  l16_result_2: boolean,
  l18_nullDerefBool_0: boolean,
  l18_nullDerefBool_1: boolean,
  l3_nullDerefBool_0: boolean,
  l3_nullDerefBool_1: boolean,
  l15_nullDerefBool_0: boolean,
  l15_nullDerefBool_1: boolean,
  l21_lte_0: boolean,
  l21_lte_1: boolean,
  l5_gt_0: boolean,
  l5_gt_1: boolean,
  l12_result_0: boolean,
  l12_result_1: boolean,
  l12_result_2: boolean,
  l19_l2_nullDerefBool_0: boolean,
  l19_l2_nullDerefBool_1: boolean,
  l7_gt_0: boolean,
  l7_gt_1: boolean,
  l17_nullDerefBool_0: boolean,
  l17_nullDerefBool_1: boolean,
  l3_l2_nullDerefBool_0: boolean,
  l3_l2_nullDerefBool_1: boolean,
  l11_l2_lte_0: boolean,
  l11_l2_lte_1: boolean,
  l11_l2_lte_2: boolean,
  l21_l2_nullDerefBool_0: boolean,
  l21_l2_nullDerefBool_1: boolean,
  l3_l2_l1_result_0: boolean,
  l3_l2_l1_result_1: boolean,
  l3_l2_l1_result_2: boolean,
  l21_l2_l1_nullDerefBool_0: boolean,
  l21_l2_l1_nullDerefBool_1: boolean,
  l13_nullDerefBool_0: boolean,
  l13_nullDerefBool_1: boolean,
  l8_result_0: boolean,
  l8_result_1: boolean,
  l8_result_2: boolean,
  l15_gt_0: boolean,
  l15_gt_1: boolean,
  l11_l2_lt_0: boolean,
  l11_l2_lt_1: boolean,
  l13_l2_l1_nullDerefBool_0: boolean,
  l13_l2_l1_nullDerefBool_1: boolean,
  l9_l2_lte_0: boolean,
  l9_l2_lte_1: boolean,
  l9_l2_lte_2: boolean,
  l5_l2_lte_0: boolean,
  l5_l2_lte_1: boolean,
  l5_l2_lte_2: boolean,
  l19_l2_lte_0: boolean,
  l19_l2_lte_1: boolean,
  l19_l2_lte_2: boolean,
  l11_nullDerefBool_0: boolean,
  l11_nullDerefBool_1: boolean,
  l0_result_0: boolean,
  l0_result_1: boolean,
  l0_result_2: boolean,
  l17_lte_0: boolean,
  l17_lte_1: boolean,
  l11_l2_l1_nullDerefBool_0: boolean,
  l11_l2_l1_nullDerefBool_1: boolean,
  l17_l2_nullDerefBool_0: boolean,
  l17_l2_nullDerefBool_1: boolean,
  l0_nullDerefBool_0: boolean,
  l0_nullDerefBool_1: boolean,
  l15_l2_nullDerefBool_0: boolean,
  l15_l2_nullDerefBool_1: boolean,
  l17_l2_l1_result_0: boolean,
  l17_l2_l1_result_1: boolean,
  l17_l2_l1_result_2: boolean,
  l7_l2_nullDerefBool_0: boolean,
  l7_l2_nullDerefBool_1: boolean,
  l9_gt_0: boolean,
  l9_gt_1: boolean,
  l17_gt_0: boolean,
  l17_gt_1: boolean,
  l6_result_0: boolean,
  l6_result_1: boolean,
  l6_result_2: boolean,
  l7_lte_0: boolean,
  l7_lte_1: boolean,
  l3_l2_lte_0: boolean,
  l3_l2_lte_1: boolean,
  l3_l2_lte_2: boolean,
  l14_nullDerefBool_0: boolean,
  l14_nullDerefBool_1: boolean,
  l9_l2_lt_0: boolean,
  l9_l2_lt_1: boolean,
  l11_lte_0: boolean,
  l11_lte_1: boolean,
  l17_l2_l1_nullDerefBool_0: boolean,
  l17_l2_l1_nullDerefBool_1: boolean,
  l17_l2_lte_0: boolean,
  l17_l2_lte_1: boolean,
  l17_l2_lte_2: boolean,
  l15_l2_lte_0: boolean,
  l15_l2_lte_1: boolean,
  l15_l2_lte_2: boolean,
  l21_l2_lte_0: boolean,
  l21_l2_lte_1: boolean,
  l21_l2_lte_2: boolean,
  l7_l2_lte_0: boolean,
  l7_l2_lte_1: boolean,
  l7_l2_lte_2: boolean,
  l20_result_0: boolean,
  l20_result_1: boolean,
  l20_result_2: boolean,
  l5_lte_0: boolean,
  l5_lte_1: boolean,
  l9_l2_nullDerefBool_0: boolean,
  l9_l2_nullDerefBool_1: boolean,
  l15_l2_lt_0: boolean,
  l15_l2_lt_1: boolean,
  l3_l2_lt_0: boolean,
  l3_l2_lt_1: boolean,
  l20_nullDerefBool_0: boolean,
  l20_nullDerefBool_1: boolean,
  l13_l2_nullDerefBool_0: boolean,
  l13_l2_nullDerefBool_1: boolean,
  l12_nullDerefBool_0: boolean,
  l12_nullDerefBool_1: boolean,
  l21_l2_l1_result_0: boolean,
  l21_l2_l1_result_1: boolean,
  l21_l2_l1_result_2: boolean,
  l19_l2_l1_nullDerefBool_0: boolean,
  l19_l2_l1_nullDerefBool_1: boolean,
  l13_l2_lt_0: boolean,
  l13_l2_lt_1: boolean,
  l10_nullDerefBool_0: boolean,
  l10_nullDerefBool_1: boolean,
  l11_l2_nullDerefBool_0: boolean,
  l11_l2_nullDerefBool_1: boolean
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
    found_1=null)
  and 
  (
    (
      TreeSetCondition10[myKey_0]
      and 
      TruePred[]
      and 
      (
        ex_1=NullPointerExceptionLit)
      and 
      (
        throw_81=ex_1)
      and 
      (
        l8_nullDerefBool_0=l8_nullDerefBool_1)
      and 
      (
        l14_result_0=l14_result_2)
      and 
      (
        l15_l2_l1_nullDerefBool_0=l15_l2_l1_nullDerefBool_1)
      and 
      (
        l21_nullDerefBool_0=l21_nullDerefBool_1)
      and 
      (
        l15_lte_0=l15_lte_1)
      and 
      (
        l16_nullDerefBool_0=l16_nullDerefBool_1)
      and 
      (
        l13_gt_0=l13_gt_1)
      and 
      (
        l13_l2_l1_result_0=l13_l2_l1_result_2)
      and 
      (
        l17_l2_lt_0=l17_l2_lt_1)
      and 
      (
        l13_lte_0=l13_lte_1)
      and 
      (
        l19_gt_0=l19_gt_1)
      and 
      (
        l9_l2_l1_nullDerefBool_0=l9_l2_l1_nullDerefBool_1)
      and 
      (
        l5_l2_l1_result_0=l5_l2_l1_result_2)
      and 
      (
        l5_l2_l1_nullDerefBool_0=l5_l2_l1_nullDerefBool_1)
      and 
      (
        l21_gt_0=l21_gt_1)
      and 
      (
        l4_result_0=l4_result_2)
      and 
      (
        l13_l2_lte_0=l13_l2_lte_2)
      and 
      (
        l19_lte_0=l19_lte_1)
      and 
      (
        l11_gt_0=l11_gt_1)
      and 
      (
        l7_l2_l1_nullDerefBool_0=l7_l2_l1_nullDerefBool_1)
      and 
      (
        l7_nullDerefBool_0=l7_nullDerefBool_1)
      and 
      (
        gt_0=gt_10)
      and 
      (
        l3_lte_0=l3_lte_1)
      and 
      (
        l5_l2_nullDerefBool_0=l5_l2_nullDerefBool_1)
      and 
      (
        l18_result_0=l18_result_2)
      and 
      (
        l19_nullDerefBool_0=l19_nullDerefBool_1)
      and 
      (
        l3_l2_l1_nullDerefBool_0=l3_l2_l1_nullDerefBool_1)
      and 
      (
        l11_l2_l1_result_0=l11_l2_l1_result_2)
      and 
      (
        l7_l2_l1_result_0=l7_l2_l1_result_2)
      and 
      (
        l4_nullDerefBool_0=l4_nullDerefBool_1)
      and 
      (
        lt_0=lt_10)
      and 
      (
        l10_result_0=l10_result_2)
      and 
      (
        l9_l2_l1_result_0=l9_l2_l1_result_2)
      and 
      (
        l9_nullDerefBool_0=l9_nullDerefBool_1)
      and 
      (
        l5_nullDerefBool_0=l5_nullDerefBool_1)
      and 
      (
        l5_l2_lt_0=l5_l2_lt_1)
      and 
      (
        l3_gt_0=l3_gt_1)
      and 
      (
        l6_nullDerefBool_0=l6_nullDerefBool_1)
      and 
      (
        l9_lte_0=l9_lte_1)
      and 
      (
        l19_l2_lt_0=l19_l2_lt_1)
      and 
      (
        l7_l2_lt_0=l7_l2_lt_1)
      and 
      (
        l19_l2_l1_result_0=l19_l2_l1_result_2)
      and 
      (
        l15_l2_l1_result_0=l15_l2_l1_result_2)
      and 
      (
        l21_l2_lt_0=l21_l2_lt_1)
      and 
      (
        l16_result_0=l16_result_2)
      and 
      (
        l18_nullDerefBool_0=l18_nullDerefBool_1)
      and 
      (
        l3_nullDerefBool_0=l3_nullDerefBool_1)
      and 
      (
        l21_lte_0=l21_lte_1)
      and 
      (
        l15_nullDerefBool_0=l15_nullDerefBool_1)
      and 
      (
        l5_gt_0=l5_gt_1)
      and 
      (
        l19_l2_nullDerefBool_0=l19_l2_nullDerefBool_1)
      and 
      (
        l12_result_0=l12_result_2)
      and 
      (
        l7_gt_0=l7_gt_1)
      and 
      (
        l17_nullDerefBool_0=l17_nullDerefBool_1)
      and 
      (
        l3_l2_nullDerefBool_0=l3_l2_nullDerefBool_1)
      and 
      (
        p_0=p_11)
      and 
      (
        l11_l2_lte_0=l11_l2_lte_2)
      and 
      (
        l21_l2_nullDerefBool_0=l21_l2_nullDerefBool_1)
      and 
      (
        l21_l2_l1_nullDerefBool_0=l21_l2_l1_nullDerefBool_1)
      and 
      (
        l3_l2_l1_result_0=l3_l2_l1_result_2)
      and 
      (
        l8_result_0=l8_result_2)
      and 
      (
        l13_nullDerefBool_0=l13_nullDerefBool_1)
      and 
      (
        nullDerefBool_1=nullDerefBool_32)
      and 
      (
        l11_l2_lt_0=l11_l2_lt_1)
      and 
      (
        l15_gt_0=l15_gt_1)
      and 
      (
        l13_l2_l1_nullDerefBool_0=l13_l2_l1_nullDerefBool_1)
      and 
      (
        l9_l2_lte_0=l9_l2_lte_2)
      and 
      (
        l5_l2_lte_0=l5_l2_lte_2)
      and 
      (
        l19_l2_lte_0=l19_l2_lte_2)
      and 
      (
        l17_lte_0=l17_lte_1)
      and 
      (
        l0_result_0=l0_result_2)
      and 
      (
        l11_nullDerefBool_0=l11_nullDerefBool_1)
      and 
      (
        l17_l2_nullDerefBool_0=l17_l2_nullDerefBool_1)
      and 
      (
        l11_l2_l1_nullDerefBool_0=l11_l2_l1_nullDerefBool_1)
      and 
      (
        l0_nullDerefBool_0=l0_nullDerefBool_1)
      and 
      (
        l15_l2_nullDerefBool_0=l15_l2_nullDerefBool_1)
      and 
      (
        l17_l2_l1_result_0=l17_l2_l1_result_2)
      and 
      (
        l7_l2_nullDerefBool_0=l7_l2_nullDerefBool_1)
      and 
      (
        l9_gt_0=l9_gt_1)
      and 
      (
        l6_result_0=l6_result_2)
      and 
      (
        l17_gt_0=l17_gt_1)
      and 
      (
        l7_lte_0=l7_lte_1)
      and 
      (
        l3_l2_lte_0=l3_l2_lte_2)
      and 
      (
        l14_nullDerefBool_0=l14_nullDerefBool_1)
      and 
      (
        l9_l2_lt_0=l9_l2_lt_1)
      and 
      (
        l17_l2_l1_nullDerefBool_0=l17_l2_l1_nullDerefBool_1)
      and 
      (
        l11_lte_0=l11_lte_1)
      and 
      (
        l15_l2_lte_0=l15_l2_lte_2)
      and 
      (
        l17_l2_lte_0=l17_l2_lte_2)
      and 
      (
        l21_l2_lte_0=l21_l2_lte_2)
      and 
      (
        l7_l2_lte_0=l7_l2_lte_2)
      and 
      (
        l20_result_0=l20_result_2)
      and 
      (
        l5_lte_0=l5_lte_1)
      and 
      (
        l9_l2_nullDerefBool_0=l9_l2_nullDerefBool_1)
      and 
      (
        l15_l2_lt_0=l15_l2_lt_1)
      and 
      (
        l3_l2_lt_0=l3_l2_lt_1)
      and 
      (
        l20_nullDerefBool_0=l20_nullDerefBool_1)
      and 
      (
        l13_l2_nullDerefBool_0=l13_l2_nullDerefBool_1)
      and 
      (
        l12_nullDerefBool_0=l12_nullDerefBool_1)
      and 
      (
        l21_l2_l1_result_0=l21_l2_l1_result_2)
      and 
      (
        l19_l2_l1_nullDerefBool_0=l19_l2_l1_nullDerefBool_1)
      and 
      (
        l13_l2_lt_0=l13_l2_lt_1)
      and 
      (
        l10_nullDerefBool_0=l10_nullDerefBool_1)
      and 
      (
        l11_l2_nullDerefBool_0=l11_l2_nullDerefBool_1)
      and 
      (
        found_1=found_11)
    )
    or 
    (
      (
        not (
          TreeSetCondition10[myKey_0])
      )
      and 
      TruePred[]
      and 
      (
        (
          TreeSetCondition0[thiz_0]
          and 
          (
            nullDerefBool_2=true)
        )
        or 
        (
          (
            not (
              TreeSetCondition0[thiz_0])
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
        p_1=thiz_0.root_0)
      and 
      (
        (
          TreeSetCondition8[found_1,
                           p_1]
          and 
          TruePred[]
          and 
          (
            (
              TreeSetCondition2[p_1]
              and 
              (
                nullDerefBool_3=true)
            )
            or 
            (
              (
                not (
                  TreeSetCondition2[p_1])
              )
              and 
              TruePred[]
              and 
              (
                nullDerefBool_2=nullDerefBool_3)
            )
          )
          and 
          Data_data_lt_0[myKey_0,
                        throw_2,
                        throw_3,
                        lt_1,
                        p_1.key_0,
                        l0_result_1,
                        l0_result_2,
                        l0_nullDerefBool_1]
          and 
          (
            (
              TreeSetCondition6[lt_1]
              and 
              (
                (
                  TreeSetCondition2[p_1]
                  and 
                  (
                    nullDerefBool_5=true)
                )
                or 
                (
                  (
                    not (
                      TreeSetCondition2[p_1])
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
                p_2=p_1.left_0)
              and 
              (
                l3_l2_lt_0=l3_l2_lt_1)
              and 
              (
                l3_nullDerefBool_0=l3_nullDerefBool_1)
              and 
              (
                l3_l2_l1_result_0=l3_l2_l1_result_2)
              and 
              (
                l3_l2_l1_nullDerefBool_0=l3_l2_l1_nullDerefBool_1)
              and 
              (
                throw_3=throw_9)
              and 
              (
                l3_l2_nullDerefBool_0=l3_l2_nullDerefBool_1)
              and 
              (
                gt_0=gt_1)
              and 
              (
                l3_lte_0=l3_lte_1)
              and 
              (
                l3_gt_0=l3_gt_1)
              and 
              (
                l3_l2_lte_0=l3_l2_lte_2)
              and 
              (
                found_1=found_2)
            )
            or 
            (
              (
                not (
                  TreeSetCondition6[lt_1])
              )
              and 
              TruePred[]
              and 
              (
                (
                  TreeSetCondition2[p_1]
                  and 
                  (
                    nullDerefBool_4=true)
                )
                or 
                (
                  (
                    not (
                      TreeSetCondition2[p_1])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_3=nullDerefBool_4)
                )
              )
              and 
              Data_data_gt_0[myKey_0,
                            throw_4,
                            throw_5,
                            throw_6,
                            throw_7,
                            throw_8,
                            throw_9,
                            gt_1,
                            p_1.key_0,
                            l3_nullDerefBool_1,
                            l3_gt_1,
                            l3_lte_1,
                            l3_l2_nullDerefBool_1,
                            l3_l2_lt_0,
                            l3_l2_lt_1,
                            l3_l2_l1_nullDerefBool_0,
                            l3_l2_l1_nullDerefBool_1,
                            l3_l2_lte_1,
                            l3_l2_lte_2,
                            l3_l2_l1_result_0,
                            l3_l2_l1_result_1,
                            l3_l2_l1_result_2]
              and 
              (
                (
                  TreeSetCondition4[gt_1]
                  and 
                  (
                    (
                      TreeSetCondition2[p_1]
                      and 
                      (
                        nullDerefBool_5=true)
                    )
                    or 
                    (
                      (
                        not (
                          TreeSetCondition2[p_1])
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
                    p_2=p_1.right_0)
                  and 
                  (
                    found_1=found_2)
                )
                or 
                (
                  (
                    not (
                      TreeSetCondition4[gt_1])
                  )
                  and 
                  (
                    found_2=p_1)
                  and 
                  (
                    nullDerefBool_4=nullDerefBool_5)
                  and 
                  (
                    p_1=p_2)
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
            l3_nullDerefBool_0=l3_nullDerefBool_1)
          and 
          (
            l3_l2_lt_0=l3_l2_lt_1)
          and 
          (
            l3_l2_l1_result_0=l3_l2_l1_result_2)
          and 
          (
            l3_l2_l1_nullDerefBool_0=l3_l2_l1_nullDerefBool_1)
          and 
          (
            l0_result_0=l0_result_2)
          and 
          (
            l0_nullDerefBool_0=l0_nullDerefBool_1)
          and 
          (
            nullDerefBool_2=nullDerefBool_5)
          and 
          (
            lt_0=lt_1)
          and 
          (
            throw_1=throw_9)
          and 
          (
            l3_l2_nullDerefBool_0=l3_l2_nullDerefBool_1)
          and 
          (
            p_1=p_2)
          and 
          (
            l3_lte_0=l3_lte_1)
          and 
          (
            gt_0=gt_1)
          and 
          (
            l3_gt_0=l3_gt_1)
          and 
          (
            l3_l2_lte_0=l3_l2_lte_2)
          and 
          (
            found_1=found_2)
        )
      )
      and 
      (
        (
          TreeSetCondition8[found_2,
                           p_2]
          and 
          TruePred[]
          and 
          (
            (
              TreeSetCondition2[p_2]
              and 
              (
                nullDerefBool_6=true)
            )
            or 
            (
              (
                not (
                  TreeSetCondition2[p_2])
              )
              and 
              TruePred[]
              and 
              (
                nullDerefBool_5=nullDerefBool_6)
            )
          )
          and 
          Data_data_lt_0[myKey_0,
                        throw_10,
                        throw_11,
                        lt_2,
                        p_2.key_0,
                        l4_result_1,
                        l4_result_2,
                        l4_nullDerefBool_1]
          and 
          (
            (
              TreeSetCondition6[lt_2]
              and 
              (
                (
                  TreeSetCondition2[p_2]
                  and 
                  (
                    nullDerefBool_8=true)
                )
                or 
                (
                  (
                    not (
                      TreeSetCondition2[p_2])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_6=nullDerefBool_8)
                )
              )
              and 
              (
                p_3=p_2.left_0)
              and 
              (
                l5_l2_l1_result_0=l5_l2_l1_result_2)
              and 
              (
                l5_gt_0=l5_gt_1)
              and 
              (
                l5_l2_l1_nullDerefBool_0=l5_l2_l1_nullDerefBool_1)
              and 
              (
                throw_11=throw_17)
              and 
              (
                l5_l2_lte_0=l5_l2_lte_2)
              and 
              (
                l5_nullDerefBool_0=l5_nullDerefBool_1)
              and 
              (
                l5_lte_0=l5_lte_1)
              and 
              (
                gt_1=gt_2)
              and 
              (
                l5_l2_lt_0=l5_l2_lt_1)
              and 
              (
                l5_l2_nullDerefBool_0=l5_l2_nullDerefBool_1)
              and 
              (
                found_2=found_3)
            )
            or 
            (
              (
                not (
                  TreeSetCondition6[lt_2])
              )
              and 
              TruePred[]
              and 
              (
                (
                  TreeSetCondition2[p_2]
                  and 
                  (
                    nullDerefBool_7=true)
                )
                or 
                (
                  (
                    not (
                      TreeSetCondition2[p_2])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_6=nullDerefBool_7)
                )
              )
              and 
              Data_data_gt_0[myKey_0,
                            throw_12,
                            throw_13,
                            throw_14,
                            throw_15,
                            throw_16,
                            throw_17,
                            gt_2,
                            p_2.key_0,
                            l5_nullDerefBool_1,
                            l5_gt_1,
                            l5_lte_1,
                            l5_l2_nullDerefBool_1,
                            l5_l2_lt_0,
                            l5_l2_lt_1,
                            l5_l2_l1_nullDerefBool_0,
                            l5_l2_l1_nullDerefBool_1,
                            l5_l2_lte_1,
                            l5_l2_lte_2,
                            l5_l2_l1_result_0,
                            l5_l2_l1_result_1,
                            l5_l2_l1_result_2]
              and 
              (
                (
                  TreeSetCondition4[gt_2]
                  and 
                  (
                    (
                      TreeSetCondition2[p_2]
                      and 
                      (
                        nullDerefBool_8=true)
                    )
                    or 
                    (
                      (
                        not (
                          TreeSetCondition2[p_2])
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
                    p_3=p_2.right_0)
                  and 
                  (
                    found_2=found_3)
                )
                or 
                (
                  (
                    not (
                      TreeSetCondition4[gt_2])
                  )
                  and 
                  (
                    found_3=p_2)
                  and 
                  (
                    nullDerefBool_7=nullDerefBool_8)
                  and 
                  (
                    p_2=p_3)
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
            l5_l2_l1_result_0=l5_l2_l1_result_2)
          and 
          (
            l5_gt_0=l5_gt_1)
          and 
          (
            l5_l2_l1_nullDerefBool_0=l5_l2_l1_nullDerefBool_1)
          and 
          (
            l4_result_0=l4_result_2)
          and 
          (
            nullDerefBool_5=nullDerefBool_8)
          and 
          (
            lt_1=lt_2)
          and 
          (
            l4_nullDerefBool_0=l4_nullDerefBool_1)
          and 
          (
            throw_9=throw_17)
          and 
          (
            l5_l2_lte_0=l5_l2_lte_2)
          and 
          (
            p_2=p_3)
          and 
          (
            l5_nullDerefBool_0=l5_nullDerefBool_1)
          and 
          (
            l5_lte_0=l5_lte_1)
          and 
          (
            gt_1=gt_2)
          and 
          (
            l5_l2_lt_0=l5_l2_lt_1)
          and 
          (
            l5_l2_nullDerefBool_0=l5_l2_nullDerefBool_1)
          and 
          (
            found_2=found_3)
        )
      )
      and 
      (
        (
          TreeSetCondition8[found_3,
                           p_3]
          and 
          TruePred[]
          and 
          (
            (
              TreeSetCondition2[p_3]
              and 
              (
                nullDerefBool_9=true)
            )
            or 
            (
              (
                not (
                  TreeSetCondition2[p_3])
              )
              and 
              TruePred[]
              and 
              (
                nullDerefBool_8=nullDerefBool_9)
            )
          )
          and 
          Data_data_lt_0[myKey_0,
                        throw_18,
                        throw_19,
                        lt_3,
                        p_3.key_0,
                        l6_result_1,
                        l6_result_2,
                        l6_nullDerefBool_1]
          and 
          (
            (
              TreeSetCondition6[lt_3]
              and 
              (
                (
                  TreeSetCondition2[p_3]
                  and 
                  (
                    nullDerefBool_11=true)
                )
                or 
                (
                  (
                    not (
                      TreeSetCondition2[p_3])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_9=nullDerefBool_11)
                )
              )
              and 
              (
                p_4=p_3.left_0)
              and 
              (
                l7_l2_l1_result_0=l7_l2_l1_result_2)
              and 
              (
                l7_l2_l1_nullDerefBool_0=l7_l2_l1_nullDerefBool_1)
              and 
              (
                l7_gt_0=l7_gt_1)
              and 
              (
                throw_19=throw_25)
              and 
              (
                l7_l2_lte_0=l7_l2_lte_2)
              and 
              (
                l7_nullDerefBool_0=l7_nullDerefBool_1)
              and 
              (
                l7_l2_nullDerefBool_0=l7_l2_nullDerefBool_1)
              and 
              (
                gt_2=gt_3)
              and 
              (
                l7_lte_0=l7_lte_1)
              and 
              (
                l7_l2_lt_0=l7_l2_lt_1)
              and 
              (
                found_3=found_4)
            )
            or 
            (
              (
                not (
                  TreeSetCondition6[lt_3])
              )
              and 
              TruePred[]
              and 
              (
                (
                  TreeSetCondition2[p_3]
                  and 
                  (
                    nullDerefBool_10=true)
                )
                or 
                (
                  (
                    not (
                      TreeSetCondition2[p_3])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_9=nullDerefBool_10)
                )
              )
              and 
              Data_data_gt_0[myKey_0,
                            throw_20,
                            throw_21,
                            throw_22,
                            throw_23,
                            throw_24,
                            throw_25,
                            gt_3,
                            p_3.key_0,
                            l7_nullDerefBool_1,
                            l7_gt_1,
                            l7_lte_1,
                            l7_l2_nullDerefBool_1,
                            l7_l2_lt_0,
                            l7_l2_lt_1,
                            l7_l2_l1_nullDerefBool_0,
                            l7_l2_l1_nullDerefBool_1,
                            l7_l2_lte_1,
                            l7_l2_lte_2,
                            l7_l2_l1_result_0,
                            l7_l2_l1_result_1,
                            l7_l2_l1_result_2]
              and 
              (
                (
                  TreeSetCondition4[gt_3]
                  and 
                  (
                    (
                      TreeSetCondition2[p_3]
                      and 
                      (
                        nullDerefBool_11=true)
                    )
                    or 
                    (
                      (
                        not (
                          TreeSetCondition2[p_3])
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
                    p_4=p_3.right_0)
                  and 
                  (
                    found_3=found_4)
                )
                or 
                (
                  (
                    not (
                      TreeSetCondition4[gt_3])
                  )
                  and 
                  (
                    found_4=p_3)
                  and 
                  (
                    nullDerefBool_10=nullDerefBool_11)
                  and 
                  (
                    p_3=p_4)
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
            l7_l2_l1_result_0=l7_l2_l1_result_2)
          and 
          (
            nullDerefBool_8=nullDerefBool_11)
          and 
          (
            lt_2=lt_3)
          and 
          (
            l7_l2_l1_nullDerefBool_0=l7_l2_l1_nullDerefBool_1)
          and 
          (
            l7_gt_0=l7_gt_1)
          and 
          (
            throw_17=throw_25)
          and 
          (
            l7_l2_lte_0=l7_l2_lte_2)
          and 
          (
            l7_nullDerefBool_0=l7_nullDerefBool_1)
          and 
          (
            p_3=p_4)
          and 
          (
            l7_l2_nullDerefBool_0=l7_l2_nullDerefBool_1)
          and 
          (
            gt_2=gt_3)
          and 
          (
            l6_nullDerefBool_0=l6_nullDerefBool_1)
          and 
          (
            l6_result_0=l6_result_2)
          and 
          (
            l7_lte_0=l7_lte_1)
          and 
          (
            l7_l2_lt_0=l7_l2_lt_1)
          and 
          (
            found_3=found_4)
        )
      )
      and 
      (
        (
          TreeSetCondition8[found_4,
                           p_4]
          and 
          TruePred[]
          and 
          (
            (
              TreeSetCondition2[p_4]
              and 
              (
                nullDerefBool_12=true)
            )
            or 
            (
              (
                not (
                  TreeSetCondition2[p_4])
              )
              and 
              TruePred[]
              and 
              (
                nullDerefBool_11=nullDerefBool_12)
            )
          )
          and 
          Data_data_lt_0[myKey_0,
                        throw_26,
                        throw_27,
                        lt_4,
                        p_4.key_0,
                        l8_result_1,
                        l8_result_2,
                        l8_nullDerefBool_1]
          and 
          (
            (
              TreeSetCondition6[lt_4]
              and 
              (
                (
                  TreeSetCondition2[p_4]
                  and 
                  (
                    nullDerefBool_14=true)
                )
                or 
                (
                  (
                    not (
                      TreeSetCondition2[p_4])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_12=nullDerefBool_14)
                )
              )
              and 
              (
                p_5=p_4.left_0)
              and 
              (
                l9_l2_l1_nullDerefBool_0=l9_l2_l1_nullDerefBool_1)
              and 
              (
                l9_l2_lt_0=l9_l2_lt_1)
              and 
              (
                l9_l2_lte_0=l9_l2_lte_2)
              and 
              (
                throw_27=throw_33)
              and 
              (
                l9_l2_l1_result_0=l9_l2_l1_result_2)
              and 
              (
                l9_nullDerefBool_0=l9_nullDerefBool_1)
              and 
              (
                l9_gt_0=l9_gt_1)
              and 
              (
                gt_3=gt_4)
              and 
              (
                l9_l2_nullDerefBool_0=l9_l2_nullDerefBool_1)
              and 
              (
                l9_lte_0=l9_lte_1)
              and 
              (
                found_4=found_5)
            )
            or 
            (
              (
                not (
                  TreeSetCondition6[lt_4])
              )
              and 
              TruePred[]
              and 
              (
                (
                  TreeSetCondition2[p_4]
                  and 
                  (
                    nullDerefBool_13=true)
                )
                or 
                (
                  (
                    not (
                      TreeSetCondition2[p_4])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_12=nullDerefBool_13)
                )
              )
              and 
              Data_data_gt_0[myKey_0,
                            throw_28,
                            throw_29,
                            throw_30,
                            throw_31,
                            throw_32,
                            throw_33,
                            gt_4,
                            p_4.key_0,
                            l9_nullDerefBool_1,
                            l9_gt_1,
                            l9_lte_1,
                            l9_l2_nullDerefBool_1,
                            l9_l2_lt_0,
                            l9_l2_lt_1,
                            l9_l2_l1_nullDerefBool_0,
                            l9_l2_l1_nullDerefBool_1,
                            l9_l2_lte_1,
                            l9_l2_lte_2,
                            l9_l2_l1_result_0,
                            l9_l2_l1_result_1,
                            l9_l2_l1_result_2]
              and 
              (
                (
                  TreeSetCondition4[gt_4]
                  and 
                  (
                    (
                      TreeSetCondition2[p_4]
                      and 
                      (
                        nullDerefBool_14=true)
                    )
                    or 
                    (
                      (
                        not (
                          TreeSetCondition2[p_4])
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
                    p_5=p_4.right_0)
                  and 
                  (
                    found_4=found_5)
                )
                or 
                (
                  (
                    not (
                      TreeSetCondition4[gt_4])
                  )
                  and 
                  (
                    found_5=p_4)
                  and 
                  (
                    nullDerefBool_13=nullDerefBool_14)
                  and 
                  (
                    p_4=p_5)
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
            l8_nullDerefBool_0=l8_nullDerefBool_1)
          and 
          (
            l9_l2_l1_nullDerefBool_0=l9_l2_l1_nullDerefBool_1)
          and 
          (
            l9_l2_lt_0=l9_l2_lt_1)
          and 
          (
            l8_result_0=l8_result_2)
          and 
          (
            nullDerefBool_11=nullDerefBool_14)
          and 
          (
            lt_3=lt_4)
          and 
          (
            throw_25=throw_33)
          and 
          (
            l9_l2_lte_0=l9_l2_lte_2)
          and 
          (
            l9_l2_l1_result_0=l9_l2_l1_result_2)
          and 
          (
            p_4=p_5)
          and 
          (
            l9_nullDerefBool_0=l9_nullDerefBool_1)
          and 
          (
            l9_gt_0=l9_gt_1)
          and 
          (
            gt_3=gt_4)
          and 
          (
            l9_l2_nullDerefBool_0=l9_l2_nullDerefBool_1)
          and 
          (
            l9_lte_0=l9_lte_1)
          and 
          (
            found_4=found_5)
        )
      )
      and 
      (
        (
          TreeSetCondition8[found_5,
                           p_5]
          and 
          TruePred[]
          and 
          (
            (
              TreeSetCondition2[p_5]
              and 
              (
                nullDerefBool_15=true)
            )
            or 
            (
              (
                not (
                  TreeSetCondition2[p_5])
              )
              and 
              TruePred[]
              and 
              (
                nullDerefBool_14=nullDerefBool_15)
            )
          )
          and 
          Data_data_lt_0[myKey_0,
                        throw_34,
                        throw_35,
                        lt_5,
                        p_5.key_0,
                        l10_result_1,
                        l10_result_2,
                        l10_nullDerefBool_1]
          and 
          (
            (
              TreeSetCondition6[lt_5]
              and 
              (
                (
                  TreeSetCondition2[p_5]
                  and 
                  (
                    nullDerefBool_17=true)
                )
                or 
                (
                  (
                    not (
                      TreeSetCondition2[p_5])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_15=nullDerefBool_17)
                )
              )
              and 
              (
                p_6=p_5.left_0)
              and 
              (
                l11_nullDerefBool_0=l11_nullDerefBool_1)
              and 
              (
                l11_l2_l1_result_0=l11_l2_l1_result_2)
              and 
              (
                l11_l2_l1_nullDerefBool_0=l11_l2_l1_nullDerefBool_1)
              and 
              (
                l11_lte_0=l11_lte_1)
              and 
              (
                l11_l2_lt_0=l11_l2_lt_1)
              and 
              (
                l11_gt_0=l11_gt_1)
              and 
              (
                throw_35=throw_41)
              and 
              (
                l11_l2_nullDerefBool_0=l11_l2_nullDerefBool_1)
              and 
              (
                gt_4=gt_5)
              and 
              (
                l11_l2_lte_0=l11_l2_lte_2)
              and 
              (
                found_5=found_6)
            )
            or 
            (
              (
                not (
                  TreeSetCondition6[lt_5])
              )
              and 
              TruePred[]
              and 
              (
                (
                  TreeSetCondition2[p_5]
                  and 
                  (
                    nullDerefBool_16=true)
                )
                or 
                (
                  (
                    not (
                      TreeSetCondition2[p_5])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_15=nullDerefBool_16)
                )
              )
              and 
              Data_data_gt_0[myKey_0,
                            throw_36,
                            throw_37,
                            throw_38,
                            throw_39,
                            throw_40,
                            throw_41,
                            gt_5,
                            p_5.key_0,
                            l11_nullDerefBool_1,
                            l11_gt_1,
                            l11_lte_1,
                            l11_l2_nullDerefBool_1,
                            l11_l2_lt_0,
                            l11_l2_lt_1,
                            l11_l2_l1_nullDerefBool_0,
                            l11_l2_l1_nullDerefBool_1,
                            l11_l2_lte_1,
                            l11_l2_lte_2,
                            l11_l2_l1_result_0,
                            l11_l2_l1_result_1,
                            l11_l2_l1_result_2]
              and 
              (
                (
                  TreeSetCondition4[gt_5]
                  and 
                  (
                    (
                      TreeSetCondition2[p_5]
                      and 
                      (
                        nullDerefBool_17=true)
                    )
                    or 
                    (
                      (
                        not (
                          TreeSetCondition2[p_5])
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
                    p_6=p_5.right_0)
                  and 
                  (
                    found_5=found_6)
                )
                or 
                (
                  (
                    not (
                      TreeSetCondition4[gt_5])
                  )
                  and 
                  (
                    found_6=p_5)
                  and 
                  (
                    nullDerefBool_16=nullDerefBool_17)
                  and 
                  (
                    p_5=p_6)
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
            l11_nullDerefBool_0=l11_nullDerefBool_1)
          and 
          (
            l11_l2_l1_result_0=l11_l2_l1_result_2)
          and 
          (
            l11_l2_l1_nullDerefBool_0=l11_l2_l1_nullDerefBool_1)
          and 
          (
            l11_lte_0=l11_lte_1)
          and 
          (
            nullDerefBool_14=nullDerefBool_17)
          and 
          (
            l11_l2_lt_0=l11_l2_lt_1)
          and 
          (
            lt_4=lt_5)
          and 
          (
            l10_result_0=l10_result_2)
          and 
          (
            l11_gt_0=l11_gt_1)
          and 
          (
            throw_33=throw_41)
          and 
          (
            p_5=p_6)
          and 
          (
            l10_nullDerefBool_0=l10_nullDerefBool_1)
          and 
          (
            l11_l2_nullDerefBool_0=l11_l2_nullDerefBool_1)
          and 
          (
            gt_4=gt_5)
          and 
          (
            l11_l2_lte_0=l11_l2_lte_2)
          and 
          (
            found_5=found_6)
        )
      )
      and 
      (
        (
          TreeSetCondition8[found_6,
                           p_6]
          and 
          TruePred[]
          and 
          (
            (
              TreeSetCondition2[p_6]
              and 
              (
                nullDerefBool_18=true)
            )
            or 
            (
              (
                not (
                  TreeSetCondition2[p_6])
              )
              and 
              TruePred[]
              and 
              (
                nullDerefBool_17=nullDerefBool_18)
            )
          )
          and 
          Data_data_lt_0[myKey_0,
                        throw_42,
                        throw_43,
                        lt_6,
                        p_6.key_0,
                        l12_result_1,
                        l12_result_2,
                        l12_nullDerefBool_1]
          and 
          (
            (
              TreeSetCondition6[lt_6]
              and 
              (
                (
                  TreeSetCondition2[p_6]
                  and 
                  (
                    nullDerefBool_20=true)
                )
                or 
                (
                  (
                    not (
                      TreeSetCondition2[p_6])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_18=nullDerefBool_20)
                )
              )
              and 
              (
                p_7=p_6.left_0)
              and 
              (
                l13_lte_0=l13_lte_1)
              and 
              (
                l13_l2_nullDerefBool_0=l13_l2_nullDerefBool_1)
              and 
              (
                l13_nullDerefBool_0=l13_nullDerefBool_1)
              and 
              (
                l13_l2_lte_0=l13_l2_lte_2)
              and 
              (
                l13_gt_0=l13_gt_1)
              and 
              (
                l13_l2_l1_nullDerefBool_0=l13_l2_l1_nullDerefBool_1)
              and 
              (
                throw_43=throw_49)
              and 
              (
                l13_l2_l1_result_0=l13_l2_l1_result_2)
              and 
              (
                l13_l2_lt_0=l13_l2_lt_1)
              and 
              (
                gt_5=gt_6)
              and 
              (
                found_6=found_7)
            )
            or 
            (
              (
                not (
                  TreeSetCondition6[lt_6])
              )
              and 
              TruePred[]
              and 
              (
                (
                  TreeSetCondition2[p_6]
                  and 
                  (
                    nullDerefBool_19=true)
                )
                or 
                (
                  (
                    not (
                      TreeSetCondition2[p_6])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_18=nullDerefBool_19)
                )
              )
              and 
              Data_data_gt_0[myKey_0,
                            throw_44,
                            throw_45,
                            throw_46,
                            throw_47,
                            throw_48,
                            throw_49,
                            gt_6,
                            p_6.key_0,
                            l13_nullDerefBool_1,
                            l13_gt_1,
                            l13_lte_1,
                            l13_l2_nullDerefBool_1,
                            l13_l2_lt_0,
                            l13_l2_lt_1,
                            l13_l2_l1_nullDerefBool_0,
                            l13_l2_l1_nullDerefBool_1,
                            l13_l2_lte_1,
                            l13_l2_lte_2,
                            l13_l2_l1_result_0,
                            l13_l2_l1_result_1,
                            l13_l2_l1_result_2]
              and 
              (
                (
                  TreeSetCondition4[gt_6]
                  and 
                  (
                    (
                      TreeSetCondition2[p_6]
                      and 
                      (
                        nullDerefBool_20=true)
                    )
                    or 
                    (
                      (
                        not (
                          TreeSetCondition2[p_6])
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
                    p_7=p_6.right_0)
                  and 
                  (
                    found_6=found_7)
                )
                or 
                (
                  (
                    not (
                      TreeSetCondition4[gt_6])
                  )
                  and 
                  (
                    found_7=p_6)
                  and 
                  (
                    nullDerefBool_19=nullDerefBool_20)
                  and 
                  (
                    p_6=p_7)
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
            l13_lte_0=l13_lte_1)
          and 
          (
            l13_l2_nullDerefBool_0=l13_l2_nullDerefBool_1)
          and 
          (
            l12_nullDerefBool_0=l12_nullDerefBool_1)
          and 
          (
            l13_nullDerefBool_0=l13_nullDerefBool_1)
          and 
          (
            nullDerefBool_17=nullDerefBool_20)
          and 
          (
            l13_l2_lte_0=l13_l2_lte_2)
          and 
          (
            l13_gt_0=l13_gt_1)
          and 
          (
            l12_result_0=l12_result_2)
          and 
          (
            l13_l2_l1_nullDerefBool_0=l13_l2_l1_nullDerefBool_1)
          and 
          (
            lt_5=lt_6)
          and 
          (
            throw_41=throw_49)
          and 
          (
            l13_l2_l1_result_0=l13_l2_l1_result_2)
          and 
          (
            l13_l2_lt_0=l13_l2_lt_1)
          and 
          (
            p_6=p_7)
          and 
          (
            gt_5=gt_6)
          and 
          (
            found_6=found_7)
        )
      )
      and 
      (
        (
          TreeSetCondition8[found_7,
                           p_7]
          and 
          TruePred[]
          and 
          (
            (
              TreeSetCondition2[p_7]
              and 
              (
                nullDerefBool_21=true)
            )
            or 
            (
              (
                not (
                  TreeSetCondition2[p_7])
              )
              and 
              TruePred[]
              and 
              (
                nullDerefBool_20=nullDerefBool_21)
            )
          )
          and 
          Data_data_lt_0[myKey_0,
                        throw_50,
                        throw_51,
                        lt_7,
                        p_7.key_0,
                        l14_result_1,
                        l14_result_2,
                        l14_nullDerefBool_1]
          and 
          (
            (
              TreeSetCondition6[lt_7]
              and 
              (
                (
                  TreeSetCondition2[p_7]
                  and 
                  (
                    nullDerefBool_23=true)
                )
                or 
                (
                  (
                    not (
                      TreeSetCondition2[p_7])
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
                p_8=p_7.left_0)
              and 
              (
                l15_l2_l1_nullDerefBool_0=l15_l2_l1_nullDerefBool_1)
              and 
              (
                l15_nullDerefBool_0=l15_nullDerefBool_1)
              and 
              (
                l15_lte_0=l15_lte_1)
              and 
              (
                l15_gt_0=l15_gt_1)
              and 
              (
                l15_l2_nullDerefBool_0=l15_l2_nullDerefBool_1)
              and 
              (
                l15_l2_lte_0=l15_l2_lte_2)
              and 
              (
                throw_51=throw_57)
              and 
              (
                gt_6=gt_7)
              and 
              (
                l15_l2_l1_result_0=l15_l2_l1_result_2)
              and 
              (
                l15_l2_lt_0=l15_l2_lt_1)
              and 
              (
                found_7=found_8)
            )
            or 
            (
              (
                not (
                  TreeSetCondition6[lt_7])
              )
              and 
              TruePred[]
              and 
              (
                (
                  TreeSetCondition2[p_7]
                  and 
                  (
                    nullDerefBool_22=true)
                )
                or 
                (
                  (
                    not (
                      TreeSetCondition2[p_7])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_21=nullDerefBool_22)
                )
              )
              and 
              Data_data_gt_0[myKey_0,
                            throw_52,
                            throw_53,
                            throw_54,
                            throw_55,
                            throw_56,
                            throw_57,
                            gt_7,
                            p_7.key_0,
                            l15_nullDerefBool_1,
                            l15_gt_1,
                            l15_lte_1,
                            l15_l2_nullDerefBool_1,
                            l15_l2_lt_0,
                            l15_l2_lt_1,
                            l15_l2_l1_nullDerefBool_0,
                            l15_l2_l1_nullDerefBool_1,
                            l15_l2_lte_1,
                            l15_l2_lte_2,
                            l15_l2_l1_result_0,
                            l15_l2_l1_result_1,
                            l15_l2_l1_result_2]
              and 
              (
                (
                  TreeSetCondition4[gt_7]
                  and 
                  (
                    (
                      TreeSetCondition2[p_7]
                      and 
                      (
                        nullDerefBool_23=true)
                    )
                    or 
                    (
                      (
                        not (
                          TreeSetCondition2[p_7])
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
                    p_8=p_7.right_0)
                  and 
                  (
                    found_7=found_8)
                )
                or 
                (
                  (
                    not (
                      TreeSetCondition4[gt_7])
                  )
                  and 
                  (
                    found_8=p_7)
                  and 
                  (
                    nullDerefBool_22=nullDerefBool_23)
                  and 
                  (
                    p_7=p_8)
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
            l14_nullDerefBool_0=l14_nullDerefBool_1)
          and 
          (
            l14_result_0=l14_result_2)
          and 
          (
            l15_l2_l1_nullDerefBool_0=l15_l2_l1_nullDerefBool_1)
          and 
          (
            l15_nullDerefBool_0=l15_nullDerefBool_1)
          and 
          (
            l15_lte_0=l15_lte_1)
          and 
          (
            nullDerefBool_20=nullDerefBool_23)
          and 
          (
            l15_gt_0=l15_gt_1)
          and 
          (
            lt_6=lt_7)
          and 
          (
            l15_l2_nullDerefBool_0=l15_l2_nullDerefBool_1)
          and 
          (
            l15_l2_lte_0=l15_l2_lte_2)
          and 
          (
            throw_49=throw_57)
          and 
          (
            p_7=p_8)
          and 
          (
            gt_6=gt_7)
          and 
          (
            l15_l2_l1_result_0=l15_l2_l1_result_2)
          and 
          (
            l15_l2_lt_0=l15_l2_lt_1)
          and 
          (
            found_7=found_8)
        )
      )
      and 
      (
        (
          TreeSetCondition8[found_8,
                           p_8]
          and 
          TruePred[]
          and 
          (
            (
              TreeSetCondition2[p_8]
              and 
              (
                nullDerefBool_24=true)
            )
            or 
            (
              (
                not (
                  TreeSetCondition2[p_8])
              )
              and 
              TruePred[]
              and 
              (
                nullDerefBool_23=nullDerefBool_24)
            )
          )
          and 
          Data_data_lt_0[myKey_0,
                        throw_58,
                        throw_59,
                        lt_8,
                        p_8.key_0,
                        l16_result_1,
                        l16_result_2,
                        l16_nullDerefBool_1]
          and 
          (
            (
              TreeSetCondition6[lt_8]
              and 
              (
                (
                  TreeSetCondition2[p_8]
                  and 
                  (
                    nullDerefBool_26=true)
                )
                or 
                (
                  (
                    not (
                      TreeSetCondition2[p_8])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_24=nullDerefBool_26)
                )
              )
              and 
              (
                p_9=p_8.left_0)
              and 
              (
                l17_lte_0=l17_lte_1)
              and 
              (
                l17_l2_nullDerefBool_0=l17_l2_nullDerefBool_1)
              and 
              (
                l17_l2_l1_nullDerefBool_0=l17_l2_l1_nullDerefBool_1)
              and 
              (
                l17_l2_l1_result_0=l17_l2_l1_result_2)
              and 
              (
                l17_l2_lte_0=l17_l2_lte_2)
              and 
              (
                throw_59=throw_65)
              and 
              (
                l17_nullDerefBool_0=l17_nullDerefBool_1)
              and 
              (
                l17_l2_lt_0=l17_l2_lt_1)
              and 
              (
                gt_7=gt_8)
              and 
              (
                l17_gt_0=l17_gt_1)
              and 
              (
                found_8=found_9)
            )
            or 
            (
              (
                not (
                  TreeSetCondition6[lt_8])
              )
              and 
              TruePred[]
              and 
              (
                (
                  TreeSetCondition2[p_8]
                  and 
                  (
                    nullDerefBool_25=true)
                )
                or 
                (
                  (
                    not (
                      TreeSetCondition2[p_8])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_24=nullDerefBool_25)
                )
              )
              and 
              Data_data_gt_0[myKey_0,
                            throw_60,
                            throw_61,
                            throw_62,
                            throw_63,
                            throw_64,
                            throw_65,
                            gt_8,
                            p_8.key_0,
                            l17_nullDerefBool_1,
                            l17_gt_1,
                            l17_lte_1,
                            l17_l2_nullDerefBool_1,
                            l17_l2_lt_0,
                            l17_l2_lt_1,
                            l17_l2_l1_nullDerefBool_0,
                            l17_l2_l1_nullDerefBool_1,
                            l17_l2_lte_1,
                            l17_l2_lte_2,
                            l17_l2_l1_result_0,
                            l17_l2_l1_result_1,
                            l17_l2_l1_result_2]
              and 
              (
                (
                  TreeSetCondition4[gt_8]
                  and 
                  (
                    (
                      TreeSetCondition2[p_8]
                      and 
                      (
                        nullDerefBool_26=true)
                    )
                    or 
                    (
                      (
                        not (
                          TreeSetCondition2[p_8])
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
                    p_9=p_8.right_0)
                  and 
                  (
                    found_8=found_9)
                )
                or 
                (
                  (
                    not (
                      TreeSetCondition4[gt_8])
                  )
                  and 
                  (
                    found_9=p_8)
                  and 
                  (
                    nullDerefBool_25=nullDerefBool_26)
                  and 
                  (
                    p_8=p_9)
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
            l17_lte_0=l17_lte_1)
          and 
          (
            l17_l2_nullDerefBool_0=l17_l2_nullDerefBool_1)
          and 
          (
            l17_l2_l1_nullDerefBool_0=l17_l2_l1_nullDerefBool_1)
          and 
          (
            nullDerefBool_23=nullDerefBool_26)
          and 
          (
            l16_nullDerefBool_0=l16_nullDerefBool_1)
          and 
          (
            lt_7=lt_8)
          and 
          (
            l17_l2_l1_result_0=l17_l2_l1_result_2)
          and 
          (
            l17_l2_lte_0=l17_l2_lte_2)
          and 
          (
            throw_57=throw_65)
          and 
          (
            l17_nullDerefBool_0=l17_nullDerefBool_1)
          and 
          (
            p_8=p_9)
          and 
          (
            l17_l2_lt_0=l17_l2_lt_1)
          and 
          (
            gt_7=gt_8)
          and 
          (
            l17_gt_0=l17_gt_1)
          and 
          (
            l16_result_0=l16_result_2)
          and 
          (
            found_8=found_9)
        )
      )
      and 
      (
        (
          TreeSetCondition8[found_9,
                           p_9]
          and 
          TruePred[]
          and 
          (
            (
              TreeSetCondition2[p_9]
              and 
              (
                nullDerefBool_27=true)
            )
            or 
            (
              (
                not (
                  TreeSetCondition2[p_9])
              )
              and 
              TruePred[]
              and 
              (
                nullDerefBool_26=nullDerefBool_27)
            )
          )
          and 
          Data_data_lt_0[myKey_0,
                        throw_66,
                        throw_67,
                        lt_9,
                        p_9.key_0,
                        l18_result_1,
                        l18_result_2,
                        l18_nullDerefBool_1]
          and 
          (
            (
              TreeSetCondition6[lt_9]
              and 
              (
                (
                  TreeSetCondition2[p_9]
                  and 
                  (
                    nullDerefBool_29=true)
                )
                or 
                (
                  (
                    not (
                      TreeSetCondition2[p_9])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_27=nullDerefBool_29)
                )
              )
              and 
              (
                p_10=p_9.left_0)
              and 
              (
                l19_gt_0=l19_gt_1)
              and 
              (
                l19_nullDerefBool_0=l19_nullDerefBool_1)
              and 
              (
                l19_lte_0=l19_lte_1)
              and 
              (
                l19_l2_nullDerefBool_0=l19_l2_nullDerefBool_1)
              and 
              (
                throw_67=throw_73)
              and 
              (
                l19_l2_l1_nullDerefBool_0=l19_l2_l1_nullDerefBool_1)
              and 
              (
                l19_l2_lte_0=l19_l2_lte_2)
              and 
              (
                gt_8=gt_9)
              and 
              (
                l19_l2_lt_0=l19_l2_lt_1)
              and 
              (
                l19_l2_l1_result_0=l19_l2_l1_result_2)
              and 
              (
                found_9=found_10)
            )
            or 
            (
              (
                not (
                  TreeSetCondition6[lt_9])
              )
              and 
              TruePred[]
              and 
              (
                (
                  TreeSetCondition2[p_9]
                  and 
                  (
                    nullDerefBool_28=true)
                )
                or 
                (
                  (
                    not (
                      TreeSetCondition2[p_9])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_27=nullDerefBool_28)
                )
              )
              and 
              Data_data_gt_0[myKey_0,
                            throw_68,
                            throw_69,
                            throw_70,
                            throw_71,
                            throw_72,
                            throw_73,
                            gt_9,
                            p_9.key_0,
                            l19_nullDerefBool_1,
                            l19_gt_1,
                            l19_lte_1,
                            l19_l2_nullDerefBool_1,
                            l19_l2_lt_0,
                            l19_l2_lt_1,
                            l19_l2_l1_nullDerefBool_0,
                            l19_l2_l1_nullDerefBool_1,
                            l19_l2_lte_1,
                            l19_l2_lte_2,
                            l19_l2_l1_result_0,
                            l19_l2_l1_result_1,
                            l19_l2_l1_result_2]
              and 
              (
                (
                  TreeSetCondition4[gt_9]
                  and 
                  (
                    (
                      TreeSetCondition2[p_9]
                      and 
                      (
                        nullDerefBool_29=true)
                    )
                    or 
                    (
                      (
                        not (
                          TreeSetCondition2[p_9])
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
                    p_10=p_9.right_0)
                  and 
                  (
                    found_9=found_10)
                )
                or 
                (
                  (
                    not (
                      TreeSetCondition4[gt_9])
                  )
                  and 
                  (
                    found_10=p_9)
                  and 
                  (
                    nullDerefBool_28=nullDerefBool_29)
                  and 
                  (
                    p_9=p_10)
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
            l18_nullDerefBool_0=l18_nullDerefBool_1)
          and 
          (
            l19_gt_0=l19_gt_1)
          and 
          (
            l19_nullDerefBool_0=l19_nullDerefBool_1)
          and 
          (
            nullDerefBool_26=nullDerefBool_29)
          and 
          (
            l19_l2_nullDerefBool_0=l19_l2_nullDerefBool_1)
          and 
          (
            l19_lte_0=l19_lte_1)
          and 
          (
            lt_8=lt_9)
          and 
          (
            throw_65=throw_73)
          and 
          (
            l19_l2_l1_nullDerefBool_0=l19_l2_l1_nullDerefBool_1)
          and 
          (
            l19_l2_lte_0=l19_l2_lte_2)
          and 
          (
            p_9=p_10)
          and 
          (
            gt_8=gt_9)
          and 
          (
            l19_l2_lt_0=l19_l2_lt_1)
          and 
          (
            l19_l2_l1_result_0=l19_l2_l1_result_2)
          and 
          (
            l18_result_0=l18_result_2)
          and 
          (
            found_9=found_10)
        )
      )
      and 
      (
        (
          TreeSetCondition8[found_10,
                           p_10]
          and 
          TruePred[]
          and 
          (
            (
              TreeSetCondition2[p_10]
              and 
              (
                nullDerefBool_30=true)
            )
            or 
            (
              (
                not (
                  TreeSetCondition2[p_10])
              )
              and 
              TruePred[]
              and 
              (
                nullDerefBool_29=nullDerefBool_30)
            )
          )
          and 
          Data_data_lt_0[myKey_0,
                        throw_74,
                        throw_75,
                        lt_10,
                        p_10.key_0,
                        l20_result_1,
                        l20_result_2,
                        l20_nullDerefBool_1]
          and 
          (
            (
              TreeSetCondition6[lt_10]
              and 
              (
                (
                  TreeSetCondition2[p_10]
                  and 
                  (
                    nullDerefBool_32=true)
                )
                or 
                (
                  (
                    not (
                      TreeSetCondition2[p_10])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_30=nullDerefBool_32)
                )
              )
              and 
              (
                p_11=p_10.left_0)
              and 
              (
                l21_l2_nullDerefBool_0=l21_l2_nullDerefBool_1)
              and 
              (
                l21_l2_l1_nullDerefBool_0=l21_l2_l1_nullDerefBool_1)
              and 
              (
                l21_lte_0=l21_lte_1)
              and 
              (
                l21_nullDerefBool_0=l21_nullDerefBool_1)
              and 
              (
                l21_gt_0=l21_gt_1)
              and 
              (
                l21_l2_l1_result_0=l21_l2_l1_result_2)
              and 
              (
                l21_l2_lte_0=l21_l2_lte_2)
              and 
              (
                throw_75=throw_81)
              and 
              (
                gt_9=gt_10)
              and 
              (
                l21_l2_lt_0=l21_l2_lt_1)
              and 
              (
                found_10=found_11)
            )
            or 
            (
              (
                not (
                  TreeSetCondition6[lt_10])
              )
              and 
              TruePred[]
              and 
              (
                (
                  TreeSetCondition2[p_10]
                  and 
                  (
                    nullDerefBool_31=true)
                )
                or 
                (
                  (
                    not (
                      TreeSetCondition2[p_10])
                  )
                  and 
                  TruePred[]
                  and 
                  (
                    nullDerefBool_30=nullDerefBool_31)
                )
              )
              and 
              Data_data_gt_0[myKey_0,
                            throw_76,
                            throw_77,
                            throw_78,
                            throw_79,
                            throw_80,
                            throw_81,
                            gt_10,
                            p_10.key_0,
                            l21_nullDerefBool_1,
                            l21_gt_1,
                            l21_lte_1,
                            l21_l2_nullDerefBool_1,
                            l21_l2_lt_0,
                            l21_l2_lt_1,
                            l21_l2_l1_nullDerefBool_0,
                            l21_l2_l1_nullDerefBool_1,
                            l21_l2_lte_1,
                            l21_l2_lte_2,
                            l21_l2_l1_result_0,
                            l21_l2_l1_result_1,
                            l21_l2_l1_result_2]
              and 
              (
                (
                  TreeSetCondition4[gt_10]
                  and 
                  (
                    (
                      TreeSetCondition2[p_10]
                      and 
                      (
                        nullDerefBool_32=true)
                    )
                    or 
                    (
                      (
                        not (
                          TreeSetCondition2[p_10])
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
                    p_11=p_10.right_0)
                  and 
                  (
                    found_10=found_11)
                )
                or 
                (
                  (
                    not (
                      TreeSetCondition4[gt_10])
                  )
                  and 
                  (
                    found_11=p_10)
                  and 
                  (
                    nullDerefBool_31=nullDerefBool_32)
                  and 
                  (
                    p_10=p_11)
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
            l21_l2_nullDerefBool_0=l21_l2_nullDerefBool_1)
          and 
          (
            l21_l2_l1_nullDerefBool_0=l21_l2_l1_nullDerefBool_1)
          and 
          (
            l20_nullDerefBool_0=l20_nullDerefBool_1)
          and 
          (
            l21_nullDerefBool_0=l21_nullDerefBool_1)
          and 
          (
            l21_lte_0=l21_lte_1)
          and 
          (
            l21_gt_0=l21_gt_1)
          and 
          (
            l21_l2_l1_result_0=l21_l2_l1_result_2)
          and 
          (
            nullDerefBool_29=nullDerefBool_32)
          and 
          (
            lt_9=lt_10)
          and 
          (
            throw_73=throw_81)
          and 
          (
            l21_l2_lte_0=l21_l2_lte_2)
          and 
          (
            l20_result_0=l20_result_2)
          and 
          (
            p_10=p_11)
          and 
          (
            gt_9=gt_10)
          and 
          (
            l21_l2_lt_0=l21_l2_lt_1)
          and 
          (
            found_10=found_11)
        )
      )
      and 
      TreeSetCondition9[found_11,
                       p_11]
      and 
      (
        ex_0=ex_1)
    )
  )
  and 
  (
    return_1=found_11)
  and 
  (
    (
      TreeSetCondition12[nullDerefBool_32,
                        throw_81]
      and 
      (
        throw_82=NullPointerExceptionLit)
    )
    or 
    (
      (
        not (
          TreeSetCondition12[nullDerefBool_32,
                            throw_81]
        )
      )
      and 
      TruePred[]
      and 
      (
        throw_81=throw_82)
    )
  )

}



pred Data_data_lte_0[
  thiz_0: Data,
  throw_1: Throwable + null,
  throw_2: Throwable + null,
  throw_3: Throwable + null,
  throw_4: Throwable + null,
  return_1: boolean,
  data_0: Data + null,
  lt_0: boolean,
  lt_1: boolean,
  nullDerefBool_1: boolean,
  lte_1: boolean,
  lte_2: boolean,
  l1_nullDerefBool_0: boolean,
  l1_nullDerefBool_1: boolean,
  l1_result_0: boolean,
  l1_result_1: boolean,
  l1_result_2: boolean
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
    lte_1=false)
  and 
  (
    (
      DataCondition2[data_0,
                    thiz_0]
      and 
      (
        lte_2=true)
      and 
      (
        throw_1=throw_3)
      and 
      (
        l1_nullDerefBool_0=l1_nullDerefBool_1)
      and 
      (
        l1_result_0=l1_result_2)
      and 
      (
        lt_0=lt_1)
    )
    or 
    (
      (
        not (
          DataCondition2[data_0,
                        thiz_0]
        )
      )
      and 
      TruePred[]
      and 
      Data_data_lt_0[thiz_0,
                    throw_2,
                    throw_3,
                    lt_1,
                    data_0,
                    l1_result_1,
                    l1_result_2,
                    l1_nullDerefBool_1]
      and 
      (
        (
          DataCondition0[lt_1]
          and 
          (
            lte_2=true)
        )
        or 
        (
          (
            not (
              DataCondition0[lt_1])
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
    return_1=lte_2)
  and 
  (
    (
      DataCondition4[nullDerefBool_1,
                    throw_3]
      and 
      (
        throw_4=NullPointerExceptionLit)
    )
    or 
    (
      (
        not (
          DataCondition4[nullDerefBool_1,
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



pred Data_data_gt_0[
  thiz_0: Data,
  throw_1: Throwable + null,
  throw_2: Throwable + null,
  throw_3: Throwable + null,
  throw_4: Throwable + null,
  throw_5: Throwable + null,
  throw_6: Throwable + null,
  return_1: boolean,
  data_0: Data + null,
  nullDerefBool_1: boolean,
  gt_1: boolean,
  lte_1: boolean,
  l2_nullDerefBool_1: boolean,
  l2_lt_0: boolean,
  l2_lt_1: boolean,
  l2_l1_nullDerefBool_0: boolean,
  l2_l1_nullDerefBool_1: boolean,
  l2_lte_1: boolean,
  l2_lte_2: boolean,
  l2_l1_result_0: boolean,
  l2_l1_result_1: boolean,
  l2_l1_result_2: boolean
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
  Data_data_lte_0[thiz_0,
                 throw_2,
                 throw_3,
                 throw_4,
                 throw_5,
                 lte_1,
                 data_0,
                 l2_lt_0,
                 l2_lt_1,
                 l2_nullDerefBool_1,
                 l2_lte_1,
                 l2_lte_2,
                 l2_l1_nullDerefBool_0,
                 l2_l1_nullDerefBool_1,
                 l2_l1_result_0,
                 l2_l1_result_1,
                 l2_l1_result_2]
  and 
  TruePred[]
  and 
  (
    (
      DataCondition84[lte_1]
      and 
      (
        gt_1=false)
    )
    or 
    (
      (
        not (
          DataCondition84[lte_1])
      )
      and 
      (
        gt_1=true)
    )
  )
  and 
  (
    return_1=gt_1)
  and 
  (
    (
      DataCondition4[nullDerefBool_1,
                    throw_5]
      and 
      (
        throw_6=NullPointerExceptionLit)
    )
    or 
    (
      (
        not (
          DataCondition4[nullDerefBool_1,
                        throw_5]
        )
      )
      and 
      TruePred[]
      and 
      (
        throw_5=throw_6)
    )
  )

}



pred TreeSet_contains_0[
  thiz_0: TreeSet,
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
  throw_47: Throwable + null,
  throw_48: Throwable + null,
  throw_49: Throwable + null,
  throw_50: Throwable + null,
  throw_51: Throwable + null,
  throw_52: Throwable + null,
  throw_53: Throwable + null,
  throw_54: Throwable + null,
  throw_55: Throwable + null,
  throw_56: Throwable + null,
  throw_57: Throwable + null,
  throw_58: Throwable + null,
  throw_59: Throwable + null,
  throw_60: Throwable + null,
  throw_61: Throwable + null,
  throw_62: Throwable + null,
  throw_63: Throwable + null,
  throw_64: Throwable + null,
  throw_65: Throwable + null,
  throw_66: Throwable + null,
  throw_67: Throwable + null,
  throw_68: Throwable + null,
  throw_69: Throwable + null,
  throw_70: Throwable + null,
  throw_71: Throwable + null,
  throw_72: Throwable + null,
  throw_73: Throwable + null,
  throw_74: Throwable + null,
  throw_75: Throwable + null,
  throw_76: Throwable + null,
  throw_77: Throwable + null,
  throw_78: Throwable + null,
  throw_79: Throwable + null,
  throw_80: Throwable + null,
  throw_81: Throwable + null,
  throw_82: Throwable + null,
  throw_83: Throwable + null,
  throw_84: Throwable + null,
  return_1: boolean,
  o_0: Data + null,
  root_0: ( TreeSet ) -> one ( TreeSetNode + null ),
  right_0: ( TreeSetNode ) -> one ( TreeSetNode + null ),
  left_0: ( TreeSetNode ) -> one ( TreeSetNode + null ),
  key_0: ( TreeSetNode ) -> one ( Data + null ),
  result_1: boolean,
  entry_1: TreeSetNode + null,
  nullDerefBool_1: boolean,
  l22_l21_l2_nullDerefBool_0: boolean,
  l22_l21_l2_nullDerefBool_1: boolean,
  l22_l12_nullDerefBool_0: boolean,
  l22_l12_nullDerefBool_1: boolean,
  l22_l17_l2_lt_0: boolean,
  l22_l17_l2_lt_1: boolean,
  l22_l5_l2_lte_0: boolean,
  l22_l5_l2_lte_1: boolean,
  l22_l5_l2_lte_2: boolean,
  l22_l21_gt_0: boolean,
  l22_l21_gt_1: boolean,
  l22_l13_l2_l1_nullDerefBool_0: boolean,
  l22_l13_l2_l1_nullDerefBool_1: boolean,
  l22_ex_0: NullPointerException + null,
  l22_ex_1: NullPointerException + null,
  l22_l16_result_0: boolean,
  l22_l16_result_1: boolean,
  l22_l16_result_2: boolean,
  l22_l13_nullDerefBool_0: boolean,
  l22_l13_nullDerefBool_1: boolean,
  l22_l13_l2_lte_0: boolean,
  l22_l13_l2_lte_1: boolean,
  l22_l13_l2_lte_2: boolean,
  l22_l13_lte_0: boolean,
  l22_l13_lte_1: boolean,
  l22_l7_l2_lt_0: boolean,
  l22_l7_l2_lt_1: boolean,
  l22_l8_result_0: boolean,
  l22_l8_result_1: boolean,
  l22_l8_result_2: boolean,
  l22_l11_l2_l1_result_0: boolean,
  l22_l11_l2_l1_result_1: boolean,
  l22_l11_l2_l1_result_2: boolean,
  l22_l15_nullDerefBool_0: boolean,
  l22_l15_nullDerefBool_1: boolean,
  l22_l5_lte_0: boolean,
  l22_l5_lte_1: boolean,
  l22_l5_l2_l1_nullDerefBool_0: boolean,
  l22_l5_l2_l1_nullDerefBool_1: boolean,
  l22_l11_l2_lt_0: boolean,
  l22_l11_l2_lt_1: boolean,
  l22_l17_l2_nullDerefBool_0: boolean,
  l22_l17_l2_nullDerefBool_1: boolean,
  l22_l6_result_0: boolean,
  l22_l6_result_1: boolean,
  l22_l6_result_2: boolean,
  l22_l3_l2_l1_result_0: boolean,
  l22_l3_l2_l1_result_1: boolean,
  l22_l3_l2_l1_result_2: boolean,
  l22_l5_l2_lt_0: boolean,
  l22_l5_l2_lt_1: boolean,
  l22_l7_l2_l1_result_0: boolean,
  l22_l7_l2_l1_result_1: boolean,
  l22_l7_l2_l1_result_2: boolean,
  l22_l19_l2_lte_0: boolean,
  l22_l19_l2_lte_1: boolean,
  l22_l19_l2_lte_2: boolean,
  l22_l21_nullDerefBool_0: boolean,
  l22_l21_nullDerefBool_1: boolean,
  l22_l5_l2_nullDerefBool_0: boolean,
  l22_l5_l2_nullDerefBool_1: boolean,
  l22_l9_l2_nullDerefBool_0: boolean,
  l22_l9_l2_nullDerefBool_1: boolean,
  l22_l11_l2_lte_0: boolean,
  l22_l11_l2_lte_1: boolean,
  l22_l11_l2_lte_2: boolean,
  l22_l0_result_0: boolean,
  l22_l0_result_1: boolean,
  l22_l0_result_2: boolean,
  l22_gt_0: boolean,
  l22_gt_1: boolean,
  l22_gt_2: boolean,
  l22_gt_3: boolean,
  l22_gt_4: boolean,
  l22_gt_5: boolean,
  l22_gt_6: boolean,
  l22_gt_7: boolean,
  l22_gt_8: boolean,
  l22_gt_9: boolean,
  l22_gt_10: boolean,
  l22_l16_nullDerefBool_0: boolean,
  l22_l16_nullDerefBool_1: boolean,
  l22_l9_l2_lt_0: boolean,
  l22_l9_l2_lt_1: boolean,
  l22_l9_l2_lte_0: boolean,
  l22_l9_l2_lte_1: boolean,
  l22_l9_l2_lte_2: boolean,
  l22_l13_l2_l1_result_0: boolean,
  l22_l13_l2_l1_result_1: boolean,
  l22_l13_l2_l1_result_2: boolean,
  l22_l21_l2_lte_0: boolean,
  l22_l21_l2_lte_1: boolean,
  l22_l21_l2_lte_2: boolean,
  l22_l3_l2_l1_nullDerefBool_0: boolean,
  l22_l3_l2_l1_nullDerefBool_1: boolean,
  l22_l10_nullDerefBool_0: boolean,
  l22_l10_nullDerefBool_1: boolean,
  l22_l5_l2_l1_result_0: boolean,
  l22_l5_l2_l1_result_1: boolean,
  l22_l5_l2_l1_result_2: boolean,
  l22_l15_l2_lt_0: boolean,
  l22_l15_l2_lt_1: boolean,
  l22_l11_l2_nullDerefBool_0: boolean,
  l22_l11_l2_nullDerefBool_1: boolean,
  l22_l5_nullDerefBool_0: boolean,
  l22_l5_nullDerefBool_1: boolean,
  l22_l4_result_0: boolean,
  l22_l4_result_1: boolean,
  l22_l4_result_2: boolean,
  l22_l17_l2_lte_0: boolean,
  l22_l17_l2_lte_1: boolean,
  l22_l17_l2_lte_2: boolean,
  l22_l15_lte_0: boolean,
  l22_l15_lte_1: boolean,
  l22_l17_l2_l1_nullDerefBool_0: boolean,
  l22_l17_l2_l1_nullDerefBool_1: boolean,
  l22_l14_result_0: boolean,
  l22_l14_result_1: boolean,
  l22_l14_result_2: boolean,
  l22_l4_nullDerefBool_0: boolean,
  l22_l4_nullDerefBool_1: boolean,
  l22_l19_l2_l1_nullDerefBool_0: boolean,
  l22_l19_l2_l1_nullDerefBool_1: boolean,
  l22_l3_l2_lt_0: boolean,
  l22_l3_l2_lt_1: boolean,
  l22_l19_l2_l1_result_0: boolean,
  l22_l19_l2_l1_result_1: boolean,
  l22_l19_l2_l1_result_2: boolean,
  l22_l0_nullDerefBool_0: boolean,
  l22_l0_nullDerefBool_1: boolean,
  l22_nullDerefBool_1: boolean,
  l22_nullDerefBool_2: boolean,
  l22_nullDerefBool_3: boolean,
  l22_nullDerefBool_4: boolean,
  l22_nullDerefBool_5: boolean,
  l22_nullDerefBool_6: boolean,
  l22_nullDerefBool_7: boolean,
  l22_nullDerefBool_8: boolean,
  l22_nullDerefBool_9: boolean,
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
  l22_nullDerefBool_30: boolean,
  l22_nullDerefBool_31: boolean,
  l22_nullDerefBool_32: boolean,
  l22_l11_nullDerefBool_0: boolean,
  l22_l11_nullDerefBool_1: boolean,
  l22_l9_l2_l1_result_0: boolean,
  l22_l9_l2_l1_result_1: boolean,
  l22_l9_l2_l1_result_2: boolean,
  l22_l19_lte_0: boolean,
  l22_l19_lte_1: boolean,
  l22_l17_l2_l1_result_0: boolean,
  l22_l17_l2_l1_result_1: boolean,
  l22_l17_l2_l1_result_2: boolean,
  l22_l21_l2_l1_nullDerefBool_0: boolean,
  l22_l21_l2_l1_nullDerefBool_1: boolean,
  l22_l7_gt_0: boolean,
  l22_l7_gt_1: boolean,
  l22_l19_nullDerefBool_0: boolean,
  l22_l19_nullDerefBool_1: boolean,
  l22_l21_l2_lt_0: boolean,
  l22_l21_l2_lt_1: boolean,
  l22_l7_l2_nullDerefBool_0: boolean,
  l22_l7_l2_nullDerefBool_1: boolean,
  l22_l10_result_0: boolean,
  l22_l10_result_1: boolean,
  l22_l10_result_2: boolean,
  l22_l6_nullDerefBool_0: boolean,
  l22_l6_nullDerefBool_1: boolean,
  l22_l18_result_0: boolean,
  l22_l18_result_1: boolean,
  l22_l18_result_2: boolean,
  l22_l9_gt_0: boolean,
  l22_l9_gt_1: boolean,
  l22_l11_l2_l1_nullDerefBool_0: boolean,
  l22_l11_l2_l1_nullDerefBool_1: boolean,
  l22_l5_gt_0: boolean,
  l22_l5_gt_1: boolean,
  l22_l7_lte_0: boolean,
  l22_l7_lte_1: boolean,
  l22_l19_gt_0: boolean,
  l22_l19_gt_1: boolean,
  l22_p_0: TreeSetNode + null,
  l22_p_1: TreeSetNode + null,
  l22_p_2: TreeSetNode + null,
  l22_p_3: TreeSetNode + null,
  l22_p_4: TreeSetNode + null,
  l22_p_5: TreeSetNode + null,
  l22_p_6: TreeSetNode + null,
  l22_p_7: TreeSetNode + null,
  l22_p_8: TreeSetNode + null,
  l22_p_9: TreeSetNode + null,
  l22_p_10: TreeSetNode + null,
  l22_p_11: TreeSetNode + null,
  l22_l9_lte_0: boolean,
  l22_l9_lte_1: boolean,
  l22_l3_l2_lte_0: boolean,
  l22_l3_l2_lte_1: boolean,
  l22_l3_l2_lte_2: boolean,
  l22_l8_nullDerefBool_0: boolean,
  l22_l8_nullDerefBool_1: boolean,
  l22_l21_l2_l1_result_0: boolean,
  l22_l21_l2_l1_result_1: boolean,
  l22_l21_l2_l1_result_2: boolean,
  l22_l20_result_0: boolean,
  l22_l20_result_1: boolean,
  l22_l20_result_2: boolean,
  l22_l13_l2_nullDerefBool_0: boolean,
  l22_l13_l2_nullDerefBool_1: boolean,
  l22_l9_nullDerefBool_0: boolean,
  l22_l9_nullDerefBool_1: boolean,
  l22_l17_nullDerefBool_0: boolean,
  l22_l17_nullDerefBool_1: boolean,
  l22_l3_l2_nullDerefBool_0: boolean,
  l22_l3_l2_nullDerefBool_1: boolean,
  l22_l14_nullDerefBool_0: boolean,
  l22_l14_nullDerefBool_1: boolean,
  l22_l17_lte_0: boolean,
  l22_l17_lte_1: boolean,
  l22_l19_l2_lt_0: boolean,
  l22_l19_l2_lt_1: boolean,
  l22_l15_l2_nullDerefBool_0: boolean,
  l22_l15_l2_nullDerefBool_1: boolean,
  l22_l21_lte_0: boolean,
  l22_l21_lte_1: boolean,
  l22_lt_0: boolean,
  l22_lt_1: boolean,
  l22_lt_2: boolean,
  l22_lt_3: boolean,
  l22_lt_4: boolean,
  l22_lt_5: boolean,
  l22_lt_6: boolean,
  l22_lt_7: boolean,
  l22_lt_8: boolean,
  l22_lt_9: boolean,
  l22_lt_10: boolean,
  l22_l7_nullDerefBool_0: boolean,
  l22_l7_nullDerefBool_1: boolean,
  l22_l11_lte_0: boolean,
  l22_l11_lte_1: boolean,
  l22_l9_l2_l1_nullDerefBool_0: boolean,
  l22_l9_l2_l1_nullDerefBool_1: boolean,
  l22_l17_gt_0: boolean,
  l22_l17_gt_1: boolean,
  l22_l19_l2_nullDerefBool_0: boolean,
  l22_l19_l2_nullDerefBool_1: boolean,
  l22_l3_lte_0: boolean,
  l22_l3_lte_1: boolean,
  l22_l3_gt_0: boolean,
  l22_l3_gt_1: boolean,
  l22_l11_gt_0: boolean,
  l22_l11_gt_1: boolean,
  l22_l15_gt_0: boolean,
  l22_l15_gt_1: boolean,
  l22_l15_l2_l1_result_0: boolean,
  l22_l15_l2_l1_result_1: boolean,
  l22_l15_l2_l1_result_2: boolean,
  l22_l3_nullDerefBool_0: boolean,
  l22_l3_nullDerefBool_1: boolean,
  l22_l18_nullDerefBool_0: boolean,
  l22_l18_nullDerefBool_1: boolean,
  l22_l13_l2_lt_0: boolean,
  l22_l13_l2_lt_1: boolean,
  l22_l13_gt_0: boolean,
  l22_l13_gt_1: boolean,
  l22_l15_l2_l1_nullDerefBool_0: boolean,
  l22_l15_l2_l1_nullDerefBool_1: boolean,
  l22_l12_result_0: boolean,
  l22_l12_result_1: boolean,
  l22_l12_result_2: boolean,
  l22_l15_l2_lte_0: boolean,
  l22_l15_l2_lte_1: boolean,
  l22_l15_l2_lte_2: boolean,
  l22_l7_l2_l1_nullDerefBool_0: boolean,
  l22_l7_l2_l1_nullDerefBool_1: boolean,
  l22_l7_l2_lte_0: boolean,
  l22_l7_l2_lte_1: boolean,
  l22_l7_l2_lte_2: boolean,
  l22_l20_nullDerefBool_0: boolean,
  l22_l20_nullDerefBool_1: boolean,
  l22_found_1: TreeSetNode + null,
  l22_found_2: TreeSetNode + null,
  l22_found_3: TreeSetNode + null,
  l22_found_4: TreeSetNode + null,
  l22_found_5: TreeSetNode + null,
  l22_found_6: TreeSetNode + null,
  l22_found_7: TreeSetNode + null,
  l22_found_8: TreeSetNode + null,
  l22_found_9: TreeSetNode + null,
  l22_found_10: TreeSetNode + null,
  l22_found_11: TreeSetNode + null
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
  TreeSet_getEntry_0[thiz_0,
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
                    throw_46,
                    throw_47,
                    throw_48,
                    throw_49,
                    throw_50,
                    throw_51,
                    throw_52,
                    throw_53,
                    throw_54,
                    throw_55,
                    throw_56,
                    throw_57,
                    throw_58,
                    throw_59,
                    throw_60,
                    throw_61,
                    throw_62,
                    throw_63,
                    throw_64,
                    throw_65,
                    throw_66,
                    throw_67,
                    throw_68,
                    throw_69,
                    throw_70,
                    throw_71,
                    throw_72,
                    throw_73,
                    throw_74,
                    throw_75,
                    throw_76,
                    throw_77,
                    throw_78,
                    throw_79,
                    throw_80,
                    throw_81,
                    throw_82,
                    throw_83,
                    entry_1,
                    o_0,
                    root_0,
                    right_0,
                    left_0,
                    key_0,
                    l22_ex_0,
                    l22_ex_1,
                    l22_lt_0,
                    l22_lt_1,
                    l22_lt_2,
                    l22_lt_3,
                    l22_lt_4,
                    l22_lt_5,
                    l22_lt_6,
                    l22_lt_7,
                    l22_lt_8,
                    l22_lt_9,
                    l22_lt_10,
                    l22_nullDerefBool_1,
                    l22_nullDerefBool_2,
                    l22_nullDerefBool_3,
                    l22_nullDerefBool_4,
                    l22_nullDerefBool_5,
                    l22_nullDerefBool_6,
                    l22_nullDerefBool_7,
                    l22_nullDerefBool_8,
                    l22_nullDerefBool_9,
                    l22_nullDerefBool_10,
                    l22_nullDerefBool_11,
                    l22_nullDerefBool_12,
                    l22_nullDerefBool_13,
                    l22_nullDerefBool_14,
                    l22_nullDerefBool_15,
                    l22_nullDerefBool_16,
                    l22_nullDerefBool_17,
                    l22_nullDerefBool_18,
                    l22_nullDerefBool_19,
                    l22_nullDerefBool_20,
                    l22_nullDerefBool_21,
                    l22_nullDerefBool_22,
                    l22_nullDerefBool_23,
                    l22_nullDerefBool_24,
                    l22_nullDerefBool_25,
                    l22_nullDerefBool_26,
                    l22_nullDerefBool_27,
                    l22_nullDerefBool_28,
                    l22_nullDerefBool_29,
                    l22_nullDerefBool_30,
                    l22_nullDerefBool_31,
                    l22_nullDerefBool_32,
                    l22_p_0,
                    l22_p_1,
                    l22_p_2,
                    l22_p_3,
                    l22_p_4,
                    l22_p_5,
                    l22_p_6,
                    l22_p_7,
                    l22_p_8,
                    l22_p_9,
                    l22_p_10,
                    l22_p_11,
                    l22_gt_0,
                    l22_gt_1,
                    l22_gt_2,
                    l22_gt_3,
                    l22_gt_4,
                    l22_gt_5,
                    l22_gt_6,
                    l22_gt_7,
                    l22_gt_8,
                    l22_gt_9,
                    l22_gt_10,
                    l22_found_1,
                    l22_found_2,
                    l22_found_3,
                    l22_found_4,
                    l22_found_5,
                    l22_found_6,
                    l22_found_7,
                    l22_found_8,
                    l22_found_9,
                    l22_found_10,
                    l22_found_11,
                    l22_l14_result_0,
                    l22_l14_result_1,
                    l22_l14_result_2,
                    l22_l8_nullDerefBool_0,
                    l22_l8_nullDerefBool_1,
                    l22_l15_l2_l1_nullDerefBool_0,
                    l22_l15_l2_l1_nullDerefBool_1,
                    l22_l21_nullDerefBool_0,
                    l22_l21_nullDerefBool_1,
                    l22_l15_lte_0,
                    l22_l15_lte_1,
                    l22_l13_gt_0,
                    l22_l13_gt_1,
                    l22_l16_nullDerefBool_0,
                    l22_l16_nullDerefBool_1,
                    l22_l13_l2_l1_result_0,
                    l22_l13_l2_l1_result_1,
                    l22_l13_l2_l1_result_2,
                    l22_l17_l2_lt_0,
                    l22_l17_l2_lt_1,
                    l22_l13_lte_0,
                    l22_l13_lte_1,
                    l22_l19_gt_0,
                    l22_l19_gt_1,
                    l22_l5_l2_l1_result_0,
                    l22_l5_l2_l1_result_1,
                    l22_l5_l2_l1_result_2,
                    l22_l9_l2_l1_nullDerefBool_0,
                    l22_l9_l2_l1_nullDerefBool_1,
                    l22_l5_l2_l1_nullDerefBool_0,
                    l22_l5_l2_l1_nullDerefBool_1,
                    l22_l21_gt_0,
                    l22_l21_gt_1,
                    l22_l4_result_0,
                    l22_l4_result_1,
                    l22_l4_result_2,
                    l22_l13_l2_lte_0,
                    l22_l13_l2_lte_1,
                    l22_l13_l2_lte_2,
                    l22_l19_lte_0,
                    l22_l19_lte_1,
                    l22_l11_gt_0,
                    l22_l11_gt_1,
                    l22_l7_l2_l1_nullDerefBool_0,
                    l22_l7_l2_l1_nullDerefBool_1,
                    l22_l7_nullDerefBool_0,
                    l22_l7_nullDerefBool_1,
                    l22_l3_lte_0,
                    l22_l3_lte_1,
                    l22_l5_l2_nullDerefBool_0,
                    l22_l5_l2_nullDerefBool_1,
                    l22_l18_result_0,
                    l22_l18_result_1,
                    l22_l18_result_2,
                    l22_l19_nullDerefBool_0,
                    l22_l19_nullDerefBool_1,
                    l22_l3_l2_l1_nullDerefBool_0,
                    l22_l3_l2_l1_nullDerefBool_1,
                    l22_l11_l2_l1_result_0,
                    l22_l11_l2_l1_result_1,
                    l22_l11_l2_l1_result_2,
                    l22_l7_l2_l1_result_0,
                    l22_l7_l2_l1_result_1,
                    l22_l7_l2_l1_result_2,
                    l22_l4_nullDerefBool_0,
                    l22_l4_nullDerefBool_1,
                    l22_l10_result_0,
                    l22_l10_result_1,
                    l22_l10_result_2,
                    l22_l9_l2_l1_result_0,
                    l22_l9_l2_l1_result_1,
                    l22_l9_l2_l1_result_2,
                    l22_l9_nullDerefBool_0,
                    l22_l9_nullDerefBool_1,
                    l22_l5_nullDerefBool_0,
                    l22_l5_nullDerefBool_1,
                    l22_l6_nullDerefBool_0,
                    l22_l6_nullDerefBool_1,
                    l22_l3_gt_0,
                    l22_l3_gt_1,
                    l22_l5_l2_lt_0,
                    l22_l5_l2_lt_1,
                    l22_l19_l2_lt_0,
                    l22_l19_l2_lt_1,
                    l22_l9_lte_0,
                    l22_l9_lte_1,
                    l22_l21_l2_lt_0,
                    l22_l21_l2_lt_1,
                    l22_l15_l2_l1_result_0,
                    l22_l15_l2_l1_result_1,
                    l22_l15_l2_l1_result_2,
                    l22_l19_l2_l1_result_0,
                    l22_l19_l2_l1_result_1,
                    l22_l19_l2_l1_result_2,
                    l22_l7_l2_lt_0,
                    l22_l7_l2_lt_1,
                    l22_l16_result_0,
                    l22_l16_result_1,
                    l22_l16_result_2,
                    l22_l18_nullDerefBool_0,
                    l22_l18_nullDerefBool_1,
                    l22_l3_nullDerefBool_0,
                    l22_l3_nullDerefBool_1,
                    l22_l15_nullDerefBool_0,
                    l22_l15_nullDerefBool_1,
                    l22_l21_lte_0,
                    l22_l21_lte_1,
                    l22_l5_gt_0,
                    l22_l5_gt_1,
                    l22_l12_result_0,
                    l22_l12_result_1,
                    l22_l12_result_2,
                    l22_l19_l2_nullDerefBool_0,
                    l22_l19_l2_nullDerefBool_1,
                    l22_l7_gt_0,
                    l22_l7_gt_1,
                    l22_l17_nullDerefBool_0,
                    l22_l17_nullDerefBool_1,
                    l22_l3_l2_nullDerefBool_0,
                    l22_l3_l2_nullDerefBool_1,
                    l22_l11_l2_lte_0,
                    l22_l11_l2_lte_1,
                    l22_l11_l2_lte_2,
                    l22_l21_l2_nullDerefBool_0,
                    l22_l21_l2_nullDerefBool_1,
                    l22_l3_l2_l1_result_0,
                    l22_l3_l2_l1_result_1,
                    l22_l3_l2_l1_result_2,
                    l22_l21_l2_l1_nullDerefBool_0,
                    l22_l21_l2_l1_nullDerefBool_1,
                    l22_l13_nullDerefBool_0,
                    l22_l13_nullDerefBool_1,
                    l22_l8_result_0,
                    l22_l8_result_1,
                    l22_l8_result_2,
                    l22_l15_gt_0,
                    l22_l15_gt_1,
                    l22_l11_l2_lt_0,
                    l22_l11_l2_lt_1,
                    l22_l13_l2_l1_nullDerefBool_0,
                    l22_l13_l2_l1_nullDerefBool_1,
                    l22_l9_l2_lte_0,
                    l22_l9_l2_lte_1,
                    l22_l9_l2_lte_2,
                    l22_l5_l2_lte_0,
                    l22_l5_l2_lte_1,
                    l22_l5_l2_lte_2,
                    l22_l19_l2_lte_0,
                    l22_l19_l2_lte_1,
                    l22_l19_l2_lte_2,
                    l22_l11_nullDerefBool_0,
                    l22_l11_nullDerefBool_1,
                    l22_l0_result_0,
                    l22_l0_result_1,
                    l22_l0_result_2,
                    l22_l17_lte_0,
                    l22_l17_lte_1,
                    l22_l11_l2_l1_nullDerefBool_0,
                    l22_l11_l2_l1_nullDerefBool_1,
                    l22_l17_l2_nullDerefBool_0,
                    l22_l17_l2_nullDerefBool_1,
                    l22_l0_nullDerefBool_0,
                    l22_l0_nullDerefBool_1,
                    l22_l15_l2_nullDerefBool_0,
                    l22_l15_l2_nullDerefBool_1,
                    l22_l17_l2_l1_result_0,
                    l22_l17_l2_l1_result_1,
                    l22_l17_l2_l1_result_2,
                    l22_l7_l2_nullDerefBool_0,
                    l22_l7_l2_nullDerefBool_1,
                    l22_l9_gt_0,
                    l22_l9_gt_1,
                    l22_l17_gt_0,
                    l22_l17_gt_1,
                    l22_l6_result_0,
                    l22_l6_result_1,
                    l22_l6_result_2,
                    l22_l7_lte_0,
                    l22_l7_lte_1,
                    l22_l3_l2_lte_0,
                    l22_l3_l2_lte_1,
                    l22_l3_l2_lte_2,
                    l22_l14_nullDerefBool_0,
                    l22_l14_nullDerefBool_1,
                    l22_l9_l2_lt_0,
                    l22_l9_l2_lt_1,
                    l22_l11_lte_0,
                    l22_l11_lte_1,
                    l22_l17_l2_l1_nullDerefBool_0,
                    l22_l17_l2_l1_nullDerefBool_1,
                    l22_l17_l2_lte_0,
                    l22_l17_l2_lte_1,
                    l22_l17_l2_lte_2,
                    l22_l15_l2_lte_0,
                    l22_l15_l2_lte_1,
                    l22_l15_l2_lte_2,
                    l22_l21_l2_lte_0,
                    l22_l21_l2_lte_1,
                    l22_l21_l2_lte_2,
                    l22_l7_l2_lte_0,
                    l22_l7_l2_lte_1,
                    l22_l7_l2_lte_2,
                    l22_l20_result_0,
                    l22_l20_result_1,
                    l22_l20_result_2,
                    l22_l5_lte_0,
                    l22_l5_lte_1,
                    l22_l9_l2_nullDerefBool_0,
                    l22_l9_l2_nullDerefBool_1,
                    l22_l15_l2_lt_0,
                    l22_l15_l2_lt_1,
                    l22_l3_l2_lt_0,
                    l22_l3_l2_lt_1,
                    l22_l20_nullDerefBool_0,
                    l22_l20_nullDerefBool_1,
                    l22_l13_l2_nullDerefBool_0,
                    l22_l13_l2_nullDerefBool_1,
                    l22_l12_nullDerefBool_0,
                    l22_l12_nullDerefBool_1,
                    l22_l21_l2_l1_result_0,
                    l22_l21_l2_l1_result_1,
                    l22_l21_l2_l1_result_2,
                    l22_l19_l2_l1_nullDerefBool_0,
                    l22_l19_l2_l1_nullDerefBool_1,
                    l22_l13_l2_lt_0,
                    l22_l13_l2_lt_1,
                    l22_l10_nullDerefBool_0,
                    l22_l10_nullDerefBool_1,
                    l22_l11_l2_nullDerefBool_0,
                    l22_l11_l2_nullDerefBool_1]
  and 
  (
    (
      TreeSetCondition14[entry_1]
      and 
      (
        result_1=false)
    )
    or 
    (
      (
        not (
          TreeSetCondition14[entry_1])
      )
      and 
      (
        result_1=true)
    )
  )
  and 
  (
    return_1=result_1)
  and 
  (
    (
      TreeSetCondition12[nullDerefBool_1,
                        throw_83]
      and 
      (
        throw_84=NullPointerExceptionLit)
    )
    or 
    (
      (
        not (
          TreeSetCondition12[nullDerefBool_1,
                            throw_83]
        )
      )
      and 
      TruePred[]
      and 
      (
        throw_83=throw_84)
    )
  )

}



pred Data_data_lt_0[
  thiz_0: Data,
  throw_1: Throwable + null,
  throw_2: Throwable + null,
  return_1: boolean,
  data_0: Data + null,
  result_1: boolean,
  result_2: boolean,
  nullDerefBool_1: boolean
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
    result_1=false)
  and 
  (
    (
      DataCondition82[thiz_0]
      and 
      (
        (
          DataCondition6[data_0]
          and 
          (
            result_2=true)
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
          DataCondition82[thiz_0])
      )
      and 
      (
        (
          DataCondition80[thiz_0]
          and 
          (
            (
              DataCondition8[data_0]
              and 
              (
                result_2=true)
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
              DataCondition80[thiz_0])
          )
          and 
          (
            (
              DataCondition78[thiz_0]
              and 
              (
                (
                  DataCondition10[data_0]
                  and 
                  (
                    result_2=true)
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
                  DataCondition78[thiz_0])
              )
              and 
              (
                (
                  DataCondition76[thiz_0]
                  and 
                  (
                    (
                      DataCondition12[data_0]
                      and 
                      (
                        result_2=true)
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
                      DataCondition76[thiz_0])
                  )
                  and 
                  (
                    (
                      DataCondition74[thiz_0]
                      and 
                      (
                        (
                          DataCondition14[data_0]
                          and 
                          (
                            result_2=true)
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
                          DataCondition74[thiz_0])
                      )
                      and 
                      (
                        (
                          DataCondition72[thiz_0]
                          and 
                          (
                            (
                              DataCondition16[data_0]
                              and 
                              (
                                result_2=true)
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
                              DataCondition72[thiz_0])
                          )
                          and 
                          (
                            (
                              DataCondition70[thiz_0]
                              and 
                              (
                                (
                                  DataCondition18[data_0]
                                  and 
                                  (
                                    result_2=true)
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
                                  DataCondition70[thiz_0])
                              )
                              and 
                              (
                                (
                                  DataCondition68[thiz_0]
                                  and 
                                  (
                                    (
                                      DataCondition20[data_0]
                                      and 
                                      (
                                        result_2=true)
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
                                      DataCondition68[thiz_0])
                                  )
                                  and 
                                  (
                                    (
                                      DataCondition66[thiz_0]
                                      and 
                                      (
                                        (
                                          DataCondition22[data_0]
                                          and 
                                          (
                                            result_2=true)
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
                                          DataCondition66[thiz_0])
                                      )
                                      and 
                                      (
                                        (
                                          DataCondition64[thiz_0]
                                          and 
                                          (
                                            (
                                              DataCondition24[data_0]
                                              and 
                                              (
                                                result_2=true)
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
                                              DataCondition64[thiz_0])
                                          )
                                          and 
                                          (
                                            (
                                              DataCondition62[thiz_0]
                                              and 
                                              (
                                                (
                                                  DataCondition26[data_0]
                                                  and 
                                                  (
                                                    result_2=true)
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
                                                  DataCondition62[thiz_0])
                                              )
                                              and 
                                              (
                                                (
                                                  DataCondition60[thiz_0]
                                                  and 
                                                  (
                                                    (
                                                      DataCondition28[data_0]
                                                      and 
                                                      (
                                                        result_2=true)
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
                                                      DataCondition60[thiz_0])
                                                  )
                                                  and 
                                                  (
                                                    (
                                                      DataCondition58[thiz_0]
                                                      and 
                                                      (
                                                        (
                                                          DataCondition30[data_0]
                                                          and 
                                                          (
                                                            result_2=true)
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
                                                          DataCondition58[thiz_0])
                                                      )
                                                      and 
                                                      (
                                                        (
                                                          DataCondition56[thiz_0]
                                                          and 
                                                          (
                                                            (
                                                              DataCondition32[data_0]
                                                              and 
                                                              (
                                                                result_2=true)
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
                                                              DataCondition56[thiz_0])
                                                          )
                                                          and 
                                                          (
                                                            (
                                                              DataCondition54[thiz_0]
                                                              and 
                                                              (
                                                                (
                                                                  DataCondition34[data_0]
                                                                  and 
                                                                  (
                                                                    result_2=true)
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
                                                                  DataCondition54[thiz_0])
                                                              )
                                                              and 
                                                              (
                                                                (
                                                                  DataCondition52[thiz_0]
                                                                  and 
                                                                  (
                                                                    (
                                                                      DataCondition36[data_0]
                                                                      and 
                                                                      (
                                                                        result_2=true)
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
                                                                      DataCondition52[thiz_0])
                                                                  )
                                                                  and 
                                                                  (
                                                                    (
                                                                      DataCondition50[thiz_0]
                                                                      and 
                                                                      (
                                                                        (
                                                                          DataCondition38[data_0]
                                                                          and 
                                                                          (
                                                                            result_2=true)
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
                                                                          DataCondition50[thiz_0])
                                                                      )
                                                                      and 
                                                                      (
                                                                        (
                                                                          DataCondition48[thiz_0]
                                                                          and 
                                                                          (
                                                                            (
                                                                              DataCondition40[data_0]
                                                                              and 
                                                                              (
                                                                                result_2=true)
                                                                            )
                                                                            or 
                                                                            (
                                                                              (
                                                                                not (
                                                                                  DataCondition40[data_0])
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
                                                                                  DataCondition42[data_0]
                                                                                  and 
                                                                                  (
                                                                                    result_2=true)
                                                                                )
                                                                                or 
                                                                                (
                                                                                  (
                                                                                    not (
                                                                                      DataCondition42[data_0])
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
                                                                                    result_2=false)
                                                                                )
                                                                                or 
                                                                                (
                                                                                  (
                                                                                    not (
                                                                                      DataCondition44[thiz_0])
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
    return_1=result_2)
  and 
  (
    (
      DataCondition4[nullDerefBool_1,
                    throw_1]
      and 
      (
        throw_2=NullPointerExceptionLit)
    )
    or 
    (
      (
        not (
          DataCondition4[nullDerefBool_1,
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
  BLACK_0: ( TreeSet ) -> one ( boolean ),
  RED_0: ( TreeSet ) -> one ( boolean ),
  blackHeight_0: ( TreeSetNode ) -> one ( Int ),
  color_0: ( TreeSetNode ) -> one ( boolean ),
  key_0: ( TreeSetNode ) -> one ( Data + null ),
  l23_entry_1: TreeSetNode + null,
  l23_l22_ex_0: NullPointerException + null,
  l23_l22_ex_1: NullPointerException + null,
  l23_l22_found_1: TreeSetNode + null,
  l23_l22_found_10: TreeSetNode + null,
  l23_l22_found_11: TreeSetNode + null,
  l23_l22_found_2: TreeSetNode + null,
  l23_l22_found_3: TreeSetNode + null,
  l23_l22_found_4: TreeSetNode + null,
  l23_l22_found_5: TreeSetNode + null,
  l23_l22_found_6: TreeSetNode + null,
  l23_l22_found_7: TreeSetNode + null,
  l23_l22_found_8: TreeSetNode + null,
  l23_l22_found_9: TreeSetNode + null,
  l23_l22_gt_0: boolean,
  l23_l22_gt_1: boolean,
  l23_l22_gt_10: boolean,
  l23_l22_gt_2: boolean,
  l23_l22_gt_3: boolean,
  l23_l22_gt_4: boolean,
  l23_l22_gt_5: boolean,
  l23_l22_gt_6: boolean,
  l23_l22_gt_7: boolean,
  l23_l22_gt_8: boolean,
  l23_l22_gt_9: boolean,
  l23_l22_l0_nullDerefBool_0: boolean,
  l23_l22_l0_nullDerefBool_1: boolean,
  l23_l22_l0_result_0: boolean,
  l23_l22_l0_result_1: boolean,
  l23_l22_l0_result_2: boolean,
  l23_l22_l10_nullDerefBool_0: boolean,
  l23_l22_l10_nullDerefBool_1: boolean,
  l23_l22_l10_result_0: boolean,
  l23_l22_l10_result_1: boolean,
  l23_l22_l10_result_2: boolean,
  l23_l22_l11_gt_0: boolean,
  l23_l22_l11_gt_1: boolean,
  l23_l22_l11_l2_l1_nullDerefBool_0: boolean,
  l23_l22_l11_l2_l1_nullDerefBool_1: boolean,
  l23_l22_l11_l2_l1_result_0: boolean,
  l23_l22_l11_l2_l1_result_1: boolean,
  l23_l22_l11_l2_l1_result_2: boolean,
  l23_l22_l11_l2_lt_0: boolean,
  l23_l22_l11_l2_lt_1: boolean,
  l23_l22_l11_l2_lte_0: boolean,
  l23_l22_l11_l2_lte_1: boolean,
  l23_l22_l11_l2_lte_2: boolean,
  l23_l22_l11_l2_nullDerefBool_0: boolean,
  l23_l22_l11_l2_nullDerefBool_1: boolean,
  l23_l22_l11_lte_0: boolean,
  l23_l22_l11_lte_1: boolean,
  l23_l22_l11_nullDerefBool_0: boolean,
  l23_l22_l11_nullDerefBool_1: boolean,
  l23_l22_l12_nullDerefBool_0: boolean,
  l23_l22_l12_nullDerefBool_1: boolean,
  l23_l22_l12_result_0: boolean,
  l23_l22_l12_result_1: boolean,
  l23_l22_l12_result_2: boolean,
  l23_l22_l13_gt_0: boolean,
  l23_l22_l13_gt_1: boolean,
  l23_l22_l13_l2_l1_nullDerefBool_0: boolean,
  l23_l22_l13_l2_l1_nullDerefBool_1: boolean,
  l23_l22_l13_l2_l1_result_0: boolean,
  l23_l22_l13_l2_l1_result_1: boolean,
  l23_l22_l13_l2_l1_result_2: boolean,
  l23_l22_l13_l2_lt_0: boolean,
  l23_l22_l13_l2_lt_1: boolean,
  l23_l22_l13_l2_lte_0: boolean,
  l23_l22_l13_l2_lte_1: boolean,
  l23_l22_l13_l2_lte_2: boolean,
  l23_l22_l13_l2_nullDerefBool_0: boolean,
  l23_l22_l13_l2_nullDerefBool_1: boolean,
  l23_l22_l13_lte_0: boolean,
  l23_l22_l13_lte_1: boolean,
  l23_l22_l13_nullDerefBool_0: boolean,
  l23_l22_l13_nullDerefBool_1: boolean,
  l23_l22_l14_nullDerefBool_0: boolean,
  l23_l22_l14_nullDerefBool_1: boolean,
  l23_l22_l14_result_0: boolean,
  l23_l22_l14_result_1: boolean,
  l23_l22_l14_result_2: boolean,
  l23_l22_l15_gt_0: boolean,
  l23_l22_l15_gt_1: boolean,
  l23_l22_l15_l2_l1_nullDerefBool_0: boolean,
  l23_l22_l15_l2_l1_nullDerefBool_1: boolean,
  l23_l22_l15_l2_l1_result_0: boolean,
  l23_l22_l15_l2_l1_result_1: boolean,
  l23_l22_l15_l2_l1_result_2: boolean,
  l23_l22_l15_l2_lt_0: boolean,
  l23_l22_l15_l2_lt_1: boolean,
  l23_l22_l15_l2_lte_0: boolean,
  l23_l22_l15_l2_lte_1: boolean,
  l23_l22_l15_l2_lte_2: boolean,
  l23_l22_l15_l2_nullDerefBool_0: boolean,
  l23_l22_l15_l2_nullDerefBool_1: boolean,
  l23_l22_l15_lte_0: boolean,
  l23_l22_l15_lte_1: boolean,
  l23_l22_l15_nullDerefBool_0: boolean,
  l23_l22_l15_nullDerefBool_1: boolean,
  l23_l22_l16_nullDerefBool_0: boolean,
  l23_l22_l16_nullDerefBool_1: boolean,
  l23_l22_l16_result_0: boolean,
  l23_l22_l16_result_1: boolean,
  l23_l22_l16_result_2: boolean,
  l23_l22_l17_gt_0: boolean,
  l23_l22_l17_gt_1: boolean,
  l23_l22_l17_l2_l1_nullDerefBool_0: boolean,
  l23_l22_l17_l2_l1_nullDerefBool_1: boolean,
  l23_l22_l17_l2_l1_result_0: boolean,
  l23_l22_l17_l2_l1_result_1: boolean,
  l23_l22_l17_l2_l1_result_2: boolean,
  l23_l22_l17_l2_lt_0: boolean,
  l23_l22_l17_l2_lt_1: boolean,
  l23_l22_l17_l2_lte_0: boolean,
  l23_l22_l17_l2_lte_1: boolean,
  l23_l22_l17_l2_lte_2: boolean,
  l23_l22_l17_l2_nullDerefBool_0: boolean,
  l23_l22_l17_l2_nullDerefBool_1: boolean,
  l23_l22_l17_lte_0: boolean,
  l23_l22_l17_lte_1: boolean,
  l23_l22_l17_nullDerefBool_0: boolean,
  l23_l22_l17_nullDerefBool_1: boolean,
  l23_l22_l18_nullDerefBool_0: boolean,
  l23_l22_l18_nullDerefBool_1: boolean,
  l23_l22_l18_result_0: boolean,
  l23_l22_l18_result_1: boolean,
  l23_l22_l18_result_2: boolean,
  l23_l22_l19_gt_0: boolean,
  l23_l22_l19_gt_1: boolean,
  l23_l22_l19_l2_l1_nullDerefBool_0: boolean,
  l23_l22_l19_l2_l1_nullDerefBool_1: boolean,
  l23_l22_l19_l2_l1_result_0: boolean,
  l23_l22_l19_l2_l1_result_1: boolean,
  l23_l22_l19_l2_l1_result_2: boolean,
  l23_l22_l19_l2_lt_0: boolean,
  l23_l22_l19_l2_lt_1: boolean,
  l23_l22_l19_l2_lte_0: boolean,
  l23_l22_l19_l2_lte_1: boolean,
  l23_l22_l19_l2_lte_2: boolean,
  l23_l22_l19_l2_nullDerefBool_0: boolean,
  l23_l22_l19_l2_nullDerefBool_1: boolean,
  l23_l22_l19_lte_0: boolean,
  l23_l22_l19_lte_1: boolean,
  l23_l22_l19_nullDerefBool_0: boolean,
  l23_l22_l19_nullDerefBool_1: boolean,
  l23_l22_l20_nullDerefBool_0: boolean,
  l23_l22_l20_nullDerefBool_1: boolean,
  l23_l22_l20_result_0: boolean,
  l23_l22_l20_result_1: boolean,
  l23_l22_l20_result_2: boolean,
  l23_l22_l21_gt_0: boolean,
  l23_l22_l21_gt_1: boolean,
  l23_l22_l21_l2_l1_nullDerefBool_0: boolean,
  l23_l22_l21_l2_l1_nullDerefBool_1: boolean,
  l23_l22_l21_l2_l1_result_0: boolean,
  l23_l22_l21_l2_l1_result_1: boolean,
  l23_l22_l21_l2_l1_result_2: boolean,
  l23_l22_l21_l2_lt_0: boolean,
  l23_l22_l21_l2_lt_1: boolean,
  l23_l22_l21_l2_lte_0: boolean,
  l23_l22_l21_l2_lte_1: boolean,
  l23_l22_l21_l2_lte_2: boolean,
  l23_l22_l21_l2_nullDerefBool_0: boolean,
  l23_l22_l21_l2_nullDerefBool_1: boolean,
  l23_l22_l21_lte_0: boolean,
  l23_l22_l21_lte_1: boolean,
  l23_l22_l21_nullDerefBool_0: boolean,
  l23_l22_l21_nullDerefBool_1: boolean,
  l23_l22_l3_gt_0: boolean,
  l23_l22_l3_gt_1: boolean,
  l23_l22_l3_l2_l1_nullDerefBool_0: boolean,
  l23_l22_l3_l2_l1_nullDerefBool_1: boolean,
  l23_l22_l3_l2_l1_result_0: boolean,
  l23_l22_l3_l2_l1_result_1: boolean,
  l23_l22_l3_l2_l1_result_2: boolean,
  l23_l22_l3_l2_lt_0: boolean,
  l23_l22_l3_l2_lt_1: boolean,
  l23_l22_l3_l2_lte_0: boolean,
  l23_l22_l3_l2_lte_1: boolean,
  l23_l22_l3_l2_lte_2: boolean,
  l23_l22_l3_l2_nullDerefBool_0: boolean,
  l23_l22_l3_l2_nullDerefBool_1: boolean,
  l23_l22_l3_lte_0: boolean,
  l23_l22_l3_lte_1: boolean,
  l23_l22_l3_nullDerefBool_0: boolean,
  l23_l22_l3_nullDerefBool_1: boolean,
  l23_l22_l4_nullDerefBool_0: boolean,
  l23_l22_l4_nullDerefBool_1: boolean,
  l23_l22_l4_result_0: boolean,
  l23_l22_l4_result_1: boolean,
  l23_l22_l4_result_2: boolean,
  l23_l22_l5_gt_0: boolean,
  l23_l22_l5_gt_1: boolean,
  l23_l22_l5_l2_l1_nullDerefBool_0: boolean,
  l23_l22_l5_l2_l1_nullDerefBool_1: boolean,
  l23_l22_l5_l2_l1_result_0: boolean,
  l23_l22_l5_l2_l1_result_1: boolean,
  l23_l22_l5_l2_l1_result_2: boolean,
  l23_l22_l5_l2_lt_0: boolean,
  l23_l22_l5_l2_lt_1: boolean,
  l23_l22_l5_l2_lte_0: boolean,
  l23_l22_l5_l2_lte_1: boolean,
  l23_l22_l5_l2_lte_2: boolean,
  l23_l22_l5_l2_nullDerefBool_0: boolean,
  l23_l22_l5_l2_nullDerefBool_1: boolean,
  l23_l22_l5_lte_0: boolean,
  l23_l22_l5_lte_1: boolean,
  l23_l22_l5_nullDerefBool_0: boolean,
  l23_l22_l5_nullDerefBool_1: boolean,
  l23_l22_l6_nullDerefBool_0: boolean,
  l23_l22_l6_nullDerefBool_1: boolean,
  l23_l22_l6_result_0: boolean,
  l23_l22_l6_result_1: boolean,
  l23_l22_l6_result_2: boolean,
  l23_l22_l7_gt_0: boolean,
  l23_l22_l7_gt_1: boolean,
  l23_l22_l7_l2_l1_nullDerefBool_0: boolean,
  l23_l22_l7_l2_l1_nullDerefBool_1: boolean,
  l23_l22_l7_l2_l1_result_0: boolean,
  l23_l22_l7_l2_l1_result_1: boolean,
  l23_l22_l7_l2_l1_result_2: boolean,
  l23_l22_l7_l2_lt_0: boolean,
  l23_l22_l7_l2_lt_1: boolean,
  l23_l22_l7_l2_lte_0: boolean,
  l23_l22_l7_l2_lte_1: boolean,
  l23_l22_l7_l2_lte_2: boolean,
  l23_l22_l7_l2_nullDerefBool_0: boolean,
  l23_l22_l7_l2_nullDerefBool_1: boolean,
  l23_l22_l7_lte_0: boolean,
  l23_l22_l7_lte_1: boolean,
  l23_l22_l7_nullDerefBool_0: boolean,
  l23_l22_l7_nullDerefBool_1: boolean,
  l23_l22_l8_nullDerefBool_0: boolean,
  l23_l22_l8_nullDerefBool_1: boolean,
  l23_l22_l8_result_0: boolean,
  l23_l22_l8_result_1: boolean,
  l23_l22_l8_result_2: boolean,
  l23_l22_l9_gt_0: boolean,
  l23_l22_l9_gt_1: boolean,
  l23_l22_l9_l2_l1_nullDerefBool_0: boolean,
  l23_l22_l9_l2_l1_nullDerefBool_1: boolean,
  l23_l22_l9_l2_l1_result_0: boolean,
  l23_l22_l9_l2_l1_result_1: boolean,
  l23_l22_l9_l2_l1_result_2: boolean,
  l23_l22_l9_l2_lt_0: boolean,
  l23_l22_l9_l2_lt_1: boolean,
  l23_l22_l9_l2_lte_0: boolean,
  l23_l22_l9_l2_lte_1: boolean,
  l23_l22_l9_l2_lte_2: boolean,
  l23_l22_l9_l2_nullDerefBool_0: boolean,
  l23_l22_l9_l2_nullDerefBool_1: boolean,
  l23_l22_l9_lte_0: boolean,
  l23_l22_l9_lte_1: boolean,
  l23_l22_l9_nullDerefBool_0: boolean,
  l23_l22_l9_nullDerefBool_1: boolean,
  l23_l22_lt_0: boolean,
  l23_l22_lt_1: boolean,
  l23_l22_lt_10: boolean,
  l23_l22_lt_2: boolean,
  l23_l22_lt_3: boolean,
  l23_l22_lt_4: boolean,
  l23_l22_lt_5: boolean,
  l23_l22_lt_6: boolean,
  l23_l22_lt_7: boolean,
  l23_l22_lt_8: boolean,
  l23_l22_lt_9: boolean,
  l23_l22_nullDerefBool_1: boolean,
  l23_l22_nullDerefBool_10: boolean,
  l23_l22_nullDerefBool_11: boolean,
  l23_l22_nullDerefBool_12: boolean,
  l23_l22_nullDerefBool_13: boolean,
  l23_l22_nullDerefBool_14: boolean,
  l23_l22_nullDerefBool_15: boolean,
  l23_l22_nullDerefBool_16: boolean,
  l23_l22_nullDerefBool_17: boolean,
  l23_l22_nullDerefBool_18: boolean,
  l23_l22_nullDerefBool_19: boolean,
  l23_l22_nullDerefBool_2: boolean,
  l23_l22_nullDerefBool_20: boolean,
  l23_l22_nullDerefBool_21: boolean,
  l23_l22_nullDerefBool_22: boolean,
  l23_l22_nullDerefBool_23: boolean,
  l23_l22_nullDerefBool_24: boolean,
  l23_l22_nullDerefBool_25: boolean,
  l23_l22_nullDerefBool_26: boolean,
  l23_l22_nullDerefBool_27: boolean,
  l23_l22_nullDerefBool_28: boolean,
  l23_l22_nullDerefBool_29: boolean,
  l23_l22_nullDerefBool_3: boolean,
  l23_l22_nullDerefBool_30: boolean,
  l23_l22_nullDerefBool_31: boolean,
  l23_l22_nullDerefBool_32: boolean,
  l23_l22_nullDerefBool_4: boolean,
  l23_l22_nullDerefBool_5: boolean,
  l23_l22_nullDerefBool_6: boolean,
  l23_l22_nullDerefBool_7: boolean,
  l23_l22_nullDerefBool_8: boolean,
  l23_l22_nullDerefBool_9: boolean,
  l23_l22_p_0: TreeSetNode + null,
  l23_l22_p_1: TreeSetNode + null,
  l23_l22_p_10: TreeSetNode + null,
  l23_l22_p_11: TreeSetNode + null,
  l23_l22_p_2: TreeSetNode + null,
  l23_l22_p_3: TreeSetNode + null,
  l23_l22_p_4: TreeSetNode + null,
  l23_l22_p_5: TreeSetNode + null,
  l23_l22_p_6: TreeSetNode + null,
  l23_l22_p_7: TreeSetNode + null,
  l23_l22_p_8: TreeSetNode + null,
  l23_l22_p_9: TreeSetNode + null,
  l23_nullDerefBool_1: boolean,
  l23_result_1: boolean,
  bleft_0,fleft_0: ( TreeSetNode ) -> lone ( TreeSetNode + null ),
  nextData_0: ( Data ) -> one ( Data + null ),
  nodes_0: ( TreeSet ) -> ( TreeSetNode ),
  o_0: Data + null,
  parent_0: ( TreeSetNode ) -> one ( TreeSetNode + null ),
  return_1: boolean,
  bright_0,fright_0: ( TreeSetNode ) -> lone ( TreeSetNode + null ),
  root_0: ( TreeSet ) -> one ( TreeSetNode + null ),
  thiz_0: TreeSet,
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
  throw_47: Throwable + null,
  throw_48: Throwable + null,
  throw_49: Throwable + null,
  throw_5: Throwable + null,
  throw_50: Throwable + null,
  throw_51: Throwable + null,
  throw_52: Throwable + null,
  throw_53: Throwable + null,
  throw_54: Throwable + null,
  throw_55: Throwable + null,
  throw_56: Throwable + null,
  throw_57: Throwable + null,
  throw_58: Throwable + null,
  throw_59: Throwable + null,
  throw_6: Throwable + null,
  throw_60: Throwable + null,
  throw_61: Throwable + null,
  throw_62: Throwable + null,
  throw_63: Throwable + null,
  throw_64: Throwable + null,
  throw_65: Throwable + null,
  throw_66: Throwable + null,
  throw_67: Throwable + null,
  throw_68: Throwable + null,
  throw_69: Throwable + null,
  throw_7: Throwable + null,
  throw_70: Throwable + null,
  throw_71: Throwable + null,
  throw_72: Throwable + null,
  throw_73: Throwable + null,
  throw_74: Throwable + null,
  throw_75: Throwable + null,
  throw_76: Throwable + null,
  throw_77: Throwable + null,
  throw_78: Throwable + null,
  throw_79: Throwable + null,
  throw_8: Throwable + null,
  throw_80: Throwable + null,
  throw_81: Throwable + null,
  throw_82: Throwable + null,
  throw_83: Throwable + null,
  throw_84: Throwable + null,
  throw_9: Throwable + null
}


fact {
  precondition_TreeSet_contains_0[QF.BLACK_0,
                                 QF.RED_0,
                                 QF.blackHeight_0,
                                 QF.color_0,
                                 QF.key_0,
                                 (QF.fleft_0+QF.bleft_0),
                                 QF.nextData_0,
                                 QF.nodes_0,
                                 QF.o_0,
                                 QF.parent_0,
                                 (QF.fright_0+QF.bright_0),
                                 QF.root_0,
                                 QF.thiz_0]

}

fact {
  TreeSet_contains_0[QF.thiz_0,
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
                    QF.throw_47,
                    QF.throw_48,
                    QF.throw_49,
                    QF.throw_50,
                    QF.throw_51,
                    QF.throw_52,
                    QF.throw_53,
                    QF.throw_54,
                    QF.throw_55,
                    QF.throw_56,
                    QF.throw_57,
                    QF.throw_58,
                    QF.throw_59,
                    QF.throw_60,
                    QF.throw_61,
                    QF.throw_62,
                    QF.throw_63,
                    QF.throw_64,
                    QF.throw_65,
                    QF.throw_66,
                    QF.throw_67,
                    QF.throw_68,
                    QF.throw_69,
                    QF.throw_70,
                    QF.throw_71,
                    QF.throw_72,
                    QF.throw_73,
                    QF.throw_74,
                    QF.throw_75,
                    QF.throw_76,
                    QF.throw_77,
                    QF.throw_78,
                    QF.throw_79,
                    QF.throw_80,
                    QF.throw_81,
                    QF.throw_82,
                    QF.throw_83,
                    QF.throw_84,
                    QF.return_1,
                    QF.o_0,
                    QF.root_0,
                    (QF.fright_0+QF.bright_0),
                    (QF.fleft_0+QF.bleft_0),
                    QF.key_0,
                    QF.l23_result_1,
                    QF.l23_entry_1,
                    QF.l23_nullDerefBool_1,
                    QF.l23_l22_l21_l2_nullDerefBool_0,
                    QF.l23_l22_l21_l2_nullDerefBool_1,
                    QF.l23_l22_l12_nullDerefBool_0,
                    QF.l23_l22_l12_nullDerefBool_1,
                    QF.l23_l22_l17_l2_lt_0,
                    QF.l23_l22_l17_l2_lt_1,
                    QF.l23_l22_l5_l2_lte_0,
                    QF.l23_l22_l5_l2_lte_1,
                    QF.l23_l22_l5_l2_lte_2,
                    QF.l23_l22_l21_gt_0,
                    QF.l23_l22_l21_gt_1,
                    QF.l23_l22_l13_l2_l1_nullDerefBool_0,
                    QF.l23_l22_l13_l2_l1_nullDerefBool_1,
                    QF.l23_l22_ex_0,
                    QF.l23_l22_ex_1,
                    QF.l23_l22_l16_result_0,
                    QF.l23_l22_l16_result_1,
                    QF.l23_l22_l16_result_2,
                    QF.l23_l22_l13_nullDerefBool_0,
                    QF.l23_l22_l13_nullDerefBool_1,
                    QF.l23_l22_l13_l2_lte_0,
                    QF.l23_l22_l13_l2_lte_1,
                    QF.l23_l22_l13_l2_lte_2,
                    QF.l23_l22_l13_lte_0,
                    QF.l23_l22_l13_lte_1,
                    QF.l23_l22_l7_l2_lt_0,
                    QF.l23_l22_l7_l2_lt_1,
                    QF.l23_l22_l8_result_0,
                    QF.l23_l22_l8_result_1,
                    QF.l23_l22_l8_result_2,
                    QF.l23_l22_l11_l2_l1_result_0,
                    QF.l23_l22_l11_l2_l1_result_1,
                    QF.l23_l22_l11_l2_l1_result_2,
                    QF.l23_l22_l15_nullDerefBool_0,
                    QF.l23_l22_l15_nullDerefBool_1,
                    QF.l23_l22_l5_lte_0,
                    QF.l23_l22_l5_lte_1,
                    QF.l23_l22_l5_l2_l1_nullDerefBool_0,
                    QF.l23_l22_l5_l2_l1_nullDerefBool_1,
                    QF.l23_l22_l11_l2_lt_0,
                    QF.l23_l22_l11_l2_lt_1,
                    QF.l23_l22_l17_l2_nullDerefBool_0,
                    QF.l23_l22_l17_l2_nullDerefBool_1,
                    QF.l23_l22_l6_result_0,
                    QF.l23_l22_l6_result_1,
                    QF.l23_l22_l6_result_2,
                    QF.l23_l22_l3_l2_l1_result_0,
                    QF.l23_l22_l3_l2_l1_result_1,
                    QF.l23_l22_l3_l2_l1_result_2,
                    QF.l23_l22_l5_l2_lt_0,
                    QF.l23_l22_l5_l2_lt_1,
                    QF.l23_l22_l7_l2_l1_result_0,
                    QF.l23_l22_l7_l2_l1_result_1,
                    QF.l23_l22_l7_l2_l1_result_2,
                    QF.l23_l22_l19_l2_lte_0,
                    QF.l23_l22_l19_l2_lte_1,
                    QF.l23_l22_l19_l2_lte_2,
                    QF.l23_l22_l21_nullDerefBool_0,
                    QF.l23_l22_l21_nullDerefBool_1,
                    QF.l23_l22_l5_l2_nullDerefBool_0,
                    QF.l23_l22_l5_l2_nullDerefBool_1,
                    QF.l23_l22_l9_l2_nullDerefBool_0,
                    QF.l23_l22_l9_l2_nullDerefBool_1,
                    QF.l23_l22_l11_l2_lte_0,
                    QF.l23_l22_l11_l2_lte_1,
                    QF.l23_l22_l11_l2_lte_2,
                    QF.l23_l22_l0_result_0,
                    QF.l23_l22_l0_result_1,
                    QF.l23_l22_l0_result_2,
                    QF.l23_l22_gt_0,
                    QF.l23_l22_gt_1,
                    QF.l23_l22_gt_2,
                    QF.l23_l22_gt_3,
                    QF.l23_l22_gt_4,
                    QF.l23_l22_gt_5,
                    QF.l23_l22_gt_6,
                    QF.l23_l22_gt_7,
                    QF.l23_l22_gt_8,
                    QF.l23_l22_gt_9,
                    QF.l23_l22_gt_10,
                    QF.l23_l22_l16_nullDerefBool_0,
                    QF.l23_l22_l16_nullDerefBool_1,
                    QF.l23_l22_l9_l2_lt_0,
                    QF.l23_l22_l9_l2_lt_1,
                    QF.l23_l22_l9_l2_lte_0,
                    QF.l23_l22_l9_l2_lte_1,
                    QF.l23_l22_l9_l2_lte_2,
                    QF.l23_l22_l13_l2_l1_result_0,
                    QF.l23_l22_l13_l2_l1_result_1,
                    QF.l23_l22_l13_l2_l1_result_2,
                    QF.l23_l22_l21_l2_lte_0,
                    QF.l23_l22_l21_l2_lte_1,
                    QF.l23_l22_l21_l2_lte_2,
                    QF.l23_l22_l3_l2_l1_nullDerefBool_0,
                    QF.l23_l22_l3_l2_l1_nullDerefBool_1,
                    QF.l23_l22_l10_nullDerefBool_0,
                    QF.l23_l22_l10_nullDerefBool_1,
                    QF.l23_l22_l5_l2_l1_result_0,
                    QF.l23_l22_l5_l2_l1_result_1,
                    QF.l23_l22_l5_l2_l1_result_2,
                    QF.l23_l22_l15_l2_lt_0,
                    QF.l23_l22_l15_l2_lt_1,
                    QF.l23_l22_l11_l2_nullDerefBool_0,
                    QF.l23_l22_l11_l2_nullDerefBool_1,
                    QF.l23_l22_l5_nullDerefBool_0,
                    QF.l23_l22_l5_nullDerefBool_1,
                    QF.l23_l22_l4_result_0,
                    QF.l23_l22_l4_result_1,
                    QF.l23_l22_l4_result_2,
                    QF.l23_l22_l17_l2_lte_0,
                    QF.l23_l22_l17_l2_lte_1,
                    QF.l23_l22_l17_l2_lte_2,
                    QF.l23_l22_l15_lte_0,
                    QF.l23_l22_l15_lte_1,
                    QF.l23_l22_l17_l2_l1_nullDerefBool_0,
                    QF.l23_l22_l17_l2_l1_nullDerefBool_1,
                    QF.l23_l22_l14_result_0,
                    QF.l23_l22_l14_result_1,
                    QF.l23_l22_l14_result_2,
                    QF.l23_l22_l4_nullDerefBool_0,
                    QF.l23_l22_l4_nullDerefBool_1,
                    QF.l23_l22_l19_l2_l1_nullDerefBool_0,
                    QF.l23_l22_l19_l2_l1_nullDerefBool_1,
                    QF.l23_l22_l3_l2_lt_0,
                    QF.l23_l22_l3_l2_lt_1,
                    QF.l23_l22_l19_l2_l1_result_0,
                    QF.l23_l22_l19_l2_l1_result_1,
                    QF.l23_l22_l19_l2_l1_result_2,
                    QF.l23_l22_l0_nullDerefBool_0,
                    QF.l23_l22_l0_nullDerefBool_1,
                    QF.l23_l22_nullDerefBool_1,
                    QF.l23_l22_nullDerefBool_2,
                    QF.l23_l22_nullDerefBool_3,
                    QF.l23_l22_nullDerefBool_4,
                    QF.l23_l22_nullDerefBool_5,
                    QF.l23_l22_nullDerefBool_6,
                    QF.l23_l22_nullDerefBool_7,
                    QF.l23_l22_nullDerefBool_8,
                    QF.l23_l22_nullDerefBool_9,
                    QF.l23_l22_nullDerefBool_10,
                    QF.l23_l22_nullDerefBool_11,
                    QF.l23_l22_nullDerefBool_12,
                    QF.l23_l22_nullDerefBool_13,
                    QF.l23_l22_nullDerefBool_14,
                    QF.l23_l22_nullDerefBool_15,
                    QF.l23_l22_nullDerefBool_16,
                    QF.l23_l22_nullDerefBool_17,
                    QF.l23_l22_nullDerefBool_18,
                    QF.l23_l22_nullDerefBool_19,
                    QF.l23_l22_nullDerefBool_20,
                    QF.l23_l22_nullDerefBool_21,
                    QF.l23_l22_nullDerefBool_22,
                    QF.l23_l22_nullDerefBool_23,
                    QF.l23_l22_nullDerefBool_24,
                    QF.l23_l22_nullDerefBool_25,
                    QF.l23_l22_nullDerefBool_26,
                    QF.l23_l22_nullDerefBool_27,
                    QF.l23_l22_nullDerefBool_28,
                    QF.l23_l22_nullDerefBool_29,
                    QF.l23_l22_nullDerefBool_30,
                    QF.l23_l22_nullDerefBool_31,
                    QF.l23_l22_nullDerefBool_32,
                    QF.l23_l22_l11_nullDerefBool_0,
                    QF.l23_l22_l11_nullDerefBool_1,
                    QF.l23_l22_l9_l2_l1_result_0,
                    QF.l23_l22_l9_l2_l1_result_1,
                    QF.l23_l22_l9_l2_l1_result_2,
                    QF.l23_l22_l19_lte_0,
                    QF.l23_l22_l19_lte_1,
                    QF.l23_l22_l17_l2_l1_result_0,
                    QF.l23_l22_l17_l2_l1_result_1,
                    QF.l23_l22_l17_l2_l1_result_2,
                    QF.l23_l22_l21_l2_l1_nullDerefBool_0,
                    QF.l23_l22_l21_l2_l1_nullDerefBool_1,
                    QF.l23_l22_l7_gt_0,
                    QF.l23_l22_l7_gt_1,
                    QF.l23_l22_l19_nullDerefBool_0,
                    QF.l23_l22_l19_nullDerefBool_1,
                    QF.l23_l22_l21_l2_lt_0,
                    QF.l23_l22_l21_l2_lt_1,
                    QF.l23_l22_l7_l2_nullDerefBool_0,
                    QF.l23_l22_l7_l2_nullDerefBool_1,
                    QF.l23_l22_l10_result_0,
                    QF.l23_l22_l10_result_1,
                    QF.l23_l22_l10_result_2,
                    QF.l23_l22_l6_nullDerefBool_0,
                    QF.l23_l22_l6_nullDerefBool_1,
                    QF.l23_l22_l18_result_0,
                    QF.l23_l22_l18_result_1,
                    QF.l23_l22_l18_result_2,
                    QF.l23_l22_l9_gt_0,
                    QF.l23_l22_l9_gt_1,
                    QF.l23_l22_l11_l2_l1_nullDerefBool_0,
                    QF.l23_l22_l11_l2_l1_nullDerefBool_1,
                    QF.l23_l22_l5_gt_0,
                    QF.l23_l22_l5_gt_1,
                    QF.l23_l22_l7_lte_0,
                    QF.l23_l22_l7_lte_1,
                    QF.l23_l22_l19_gt_0,
                    QF.l23_l22_l19_gt_1,
                    QF.l23_l22_p_0,
                    QF.l23_l22_p_1,
                    QF.l23_l22_p_2,
                    QF.l23_l22_p_3,
                    QF.l23_l22_p_4,
                    QF.l23_l22_p_5,
                    QF.l23_l22_p_6,
                    QF.l23_l22_p_7,
                    QF.l23_l22_p_8,
                    QF.l23_l22_p_9,
                    QF.l23_l22_p_10,
                    QF.l23_l22_p_11,
                    QF.l23_l22_l9_lte_0,
                    QF.l23_l22_l9_lte_1,
                    QF.l23_l22_l3_l2_lte_0,
                    QF.l23_l22_l3_l2_lte_1,
                    QF.l23_l22_l3_l2_lte_2,
                    QF.l23_l22_l8_nullDerefBool_0,
                    QF.l23_l22_l8_nullDerefBool_1,
                    QF.l23_l22_l21_l2_l1_result_0,
                    QF.l23_l22_l21_l2_l1_result_1,
                    QF.l23_l22_l21_l2_l1_result_2,
                    QF.l23_l22_l20_result_0,
                    QF.l23_l22_l20_result_1,
                    QF.l23_l22_l20_result_2,
                    QF.l23_l22_l13_l2_nullDerefBool_0,
                    QF.l23_l22_l13_l2_nullDerefBool_1,
                    QF.l23_l22_l9_nullDerefBool_0,
                    QF.l23_l22_l9_nullDerefBool_1,
                    QF.l23_l22_l17_nullDerefBool_0,
                    QF.l23_l22_l17_nullDerefBool_1,
                    QF.l23_l22_l3_l2_nullDerefBool_0,
                    QF.l23_l22_l3_l2_nullDerefBool_1,
                    QF.l23_l22_l14_nullDerefBool_0,
                    QF.l23_l22_l14_nullDerefBool_1,
                    QF.l23_l22_l17_lte_0,
                    QF.l23_l22_l17_lte_1,
                    QF.l23_l22_l19_l2_lt_0,
                    QF.l23_l22_l19_l2_lt_1,
                    QF.l23_l22_l15_l2_nullDerefBool_0,
                    QF.l23_l22_l15_l2_nullDerefBool_1,
                    QF.l23_l22_l21_lte_0,
                    QF.l23_l22_l21_lte_1,
                    QF.l23_l22_lt_0,
                    QF.l23_l22_lt_1,
                    QF.l23_l22_lt_2,
                    QF.l23_l22_lt_3,
                    QF.l23_l22_lt_4,
                    QF.l23_l22_lt_5,
                    QF.l23_l22_lt_6,
                    QF.l23_l22_lt_7,
                    QF.l23_l22_lt_8,
                    QF.l23_l22_lt_9,
                    QF.l23_l22_lt_10,
                    QF.l23_l22_l7_nullDerefBool_0,
                    QF.l23_l22_l7_nullDerefBool_1,
                    QF.l23_l22_l11_lte_0,
                    QF.l23_l22_l11_lte_1,
                    QF.l23_l22_l9_l2_l1_nullDerefBool_0,
                    QF.l23_l22_l9_l2_l1_nullDerefBool_1,
                    QF.l23_l22_l17_gt_0,
                    QF.l23_l22_l17_gt_1,
                    QF.l23_l22_l19_l2_nullDerefBool_0,
                    QF.l23_l22_l19_l2_nullDerefBool_1,
                    QF.l23_l22_l3_lte_0,
                    QF.l23_l22_l3_lte_1,
                    QF.l23_l22_l3_gt_0,
                    QF.l23_l22_l3_gt_1,
                    QF.l23_l22_l11_gt_0,
                    QF.l23_l22_l11_gt_1,
                    QF.l23_l22_l15_gt_0,
                    QF.l23_l22_l15_gt_1,
                    QF.l23_l22_l15_l2_l1_result_0,
                    QF.l23_l22_l15_l2_l1_result_1,
                    QF.l23_l22_l15_l2_l1_result_2,
                    QF.l23_l22_l3_nullDerefBool_0,
                    QF.l23_l22_l3_nullDerefBool_1,
                    QF.l23_l22_l18_nullDerefBool_0,
                    QF.l23_l22_l18_nullDerefBool_1,
                    QF.l23_l22_l13_l2_lt_0,
                    QF.l23_l22_l13_l2_lt_1,
                    QF.l23_l22_l13_gt_0,
                    QF.l23_l22_l13_gt_1,
                    QF.l23_l22_l15_l2_l1_nullDerefBool_0,
                    QF.l23_l22_l15_l2_l1_nullDerefBool_1,
                    QF.l23_l22_l12_result_0,
                    QF.l23_l22_l12_result_1,
                    QF.l23_l22_l12_result_2,
                    QF.l23_l22_l15_l2_lte_0,
                    QF.l23_l22_l15_l2_lte_1,
                    QF.l23_l22_l15_l2_lte_2,
                    QF.l23_l22_l7_l2_l1_nullDerefBool_0,
                    QF.l23_l22_l7_l2_l1_nullDerefBool_1,
                    QF.l23_l22_l7_l2_lte_0,
                    QF.l23_l22_l7_l2_lte_1,
                    QF.l23_l22_l7_l2_lte_2,
                    QF.l23_l22_l20_nullDerefBool_0,
                    QF.l23_l22_l20_nullDerefBool_1,
                    QF.l23_l22_found_1,
                    QF.l23_l22_found_2,
                    QF.l23_l22_found_3,
                    QF.l23_l22_found_4,
                    QF.l23_l22_found_5,
                    QF.l23_l22_found_6,
                    QF.l23_l22_found_7,
                    QF.l23_l22_found_8,
                    QF.l23_l22_found_9,
                    QF.l23_l22_found_10,
                    QF.l23_l22_found_11]

}

assert TreeSet_m1{
  postcondition_TreeSet_contains_0[QF.key_0,
                                  QF.nodes_0,
                                  QF.o_0,
                                  QF.return_1,
                                  QF.thiz_0,
                                  QF.throw_84]
}
check TreeSet_m1 for 0 but 
                 exactly 1 TreeSet, 
                 exactly 20 TreeSetNode,
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



one sig N0,N1,N2,N3,N4,N5,N6,N7,N8,N9,N10,N11,N12,N13,N14,N15,N16,N17,N18,N19 extends TreeSetNode {}

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
let entry=(QF.thiz_0).(QF.root_0),ff1=QF.fleft_0,ff2=QF.fright_0,bf1=QF.bleft_0,bf2=QF.bright_0 | { 
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
QF.bright_0 in none->none 
QF.bleft_0 in none->none 

QF.fright_0 in
N0->N1
+N1->N3
+N1->N4
+N1->null
+N2->N3
+N2->N4
+N2->N5
+N2->N6
+N2->null
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

QF.fleft_0 in
N0->null
+N1->N3
+N1->null
+N2->N3
+N2->N4
+N2->N5
+N2->null
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
QF.blackHeight_0 in N0->0 
+N0->1 
+N0->2 
+N0->3 
+N0->4 
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
+N5->3 
+N6->0 
+N6->1 
+N6->2 
+N6->3 
+N7->0 
+N7->1 
+N7->2 
+N8->0 
+N8->1 
+N8->2 
+N9->0 
+N9->1 
+N9->2 
+N10->0 
+N10->1 
+N10->2 
+N11->0 
+N11->1 
+N11->2 
+N12->0 
+N12->1 
+N12->2 
+N13->0 
+N13->1 
+N13->2 
+N14->0 
+N14->1 
+N14->2 
+N15->0 
+N15->1 
+N16->0 
+N16->1 
+N17->0 
+N17->1 
+N18->0 
+N18->1 
+N19->0 
+N19->1 

} 
//fact data_fields 
fact { 
QF.key_0 in N0->D0 
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
} 
//fact root_node_fields 
fact { 
} 
