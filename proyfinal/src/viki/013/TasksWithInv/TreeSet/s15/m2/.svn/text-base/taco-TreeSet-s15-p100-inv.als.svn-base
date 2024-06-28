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











one sig QF {
  BLACK_0: ( TreeSet ) -> one ( boolean ),
  RED_0: ( TreeSet ) -> one ( boolean ),
  blackHeight_0: ( TreeSetNode ) -> one ( Int ),
  color_0: ( TreeSetNode ) -> one ( boolean ),
  key_0: ( TreeSetNode ) -> one ( Data + null ),
  bleft_0,fleft_0: ( TreeSetNode ) -> lone ( TreeSetNode + null ),
  nextData_0: ( Data ) -> one ( Data + null ),
  parent_0: ( TreeSetNode ) -> one ( TreeSetNode + null ),
  bright_0,fright_0: ( TreeSetNode ) -> lone ( TreeSetNode + null ),
  root_0: ( TreeSet ) -> one ( TreeSetNode + null ),
  thiz_0: TreeSet
}


fact {null !in TreeSet.(QF.root_0)}

run {TreeSet_invariant[
QF.BLACK_0,
QF.RED_0,
QF.blackHeight_0,
QF.color_0,
QF.key_0,
(QF.fleft_0+QF.bleft_0),
QF.nextData_0,  
QF.parent_0,
(QF.fright_0+QF.bright_0),
QF.root_0,
QF.thiz_0
]} for 0 but 
                 exactly 1 TreeSet, 
                 exactly 15 TreeSetNode,
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



one sig N0,N1,N2,N3,N4,N5,N6,N7,N8,N9,N10,N11,N12,N13,N14 extends TreeSetNode {}

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
let entry=(QF.thiz_0).(QF.root_0),ff1=QF.fleft_0,ff2=QF.fright_0,bf1=QF.bleft_0,bf2=QF.bright_0 | { 
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
QF.bright_0 in none->none 
QF.bleft_0 in none->none 
QF.fright_0 in N0->N1 
+N0->N2 
+N0->null 
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
+N7->null 
+N8->N9 
+N8->N10 
+N8->N11 
+N8->N12 
+N8->N13 
+N8->N14 
+N8->null 
+N9->N10 
+N9->N11 
+N9->N12 
+N9->N13 
+N9->N14 
+N9->null 
+N10->N11 
+N10->N12 
+N10->N13 
+N10->N14 
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
 
QF.fleft_0 in N0->N1 
+N0->null 
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
+N7->null 
+N8->N9 
+N8->N10 
+N8->N11 
+N8->N12 
+N8->N13 
+N8->N14 
+N8->null 
+N9->N10 
+N9->N11 
+N9->N12 
+N9->N13 
+N9->N14 
+N9->null 
+N10->N11 
+N10->N12 
+N10->N13 
+N10->N14 
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
+N4->0 
+N4->1 
+N4->2 
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
+N14->0 
+N14->1 

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
} 
//fact root_node_fields 
fact { 
} 
