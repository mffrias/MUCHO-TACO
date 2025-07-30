/* 
 * DynAlloy translator options 
 * --------------------------- 
 * applySimplifications= true
 * assertionId= AvlTree_m1
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





//-------------- amelia_avltree_AvlTree--------------//
sig AvlTree extends Object {}
{}




pred AvlTreeCondition3[
  maxNode:univ
]{
   not (
     isEmptyOrNull[maxNode])

}

pred AvlTree_ensures[
  element:univ->univ,
  nextData:univ->univ,
  nodes:univ->univ,
  return':univ,
  thiz:univ
]{
   equ[return',
      ((pred_set_some[thiz.nodes])=>({x:thiz.nodes|no y:thiz.nodes | {
        isSubset[y.element,
                (x.element).(fun_closure[nextData])]
      
      }})else(null))
   ]

}

pred postcondition_AvlTree_findMax_0[
  element:univ->univ,
  nextData:univ->univ,
  nodes:univ->univ,
  return':univ,
  thiz:univ,
  throw':univ
]{
   AvlTree_ensures[element,
                  nextData,
                  nodes,
                  return',
                  thiz]
   and 
   equ[throw',
      null]

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

pred AvlTreeCondition2[
  maxNode:univ
]{
   isEmptyOrNull[maxNode]

}

pred precondition_AvlTree_findMax_0[
  element:univ->univ,
  head:univ->univ,
  height:univ->univ,
  left:univ->univ,
  nextData:univ->univ,
  nodes:univ->univ,
  right:univ->univ,
  thiz:univ
]{
   AvlTree_nodes_abstraction[head,
                            left,
                            nodes,
                            right,
                            thiz]
   and 
   AvlTree_invariant[element,
                    head,
                    height,
                    left,
                    nextData,
                    right,
                    thiz]
   and 
   Data_invariant[nextData]

}

pred AvlTreeCondition5[
  maxNode:univ,
  right:univ->univ
]{
   not (
     neq[maxNode.right,
        null]
   )

}

pred AvlTreeCondition9[
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

pred AvlTreeCondition4[
  maxNode:univ,
  right:univ->univ
]{
   neq[maxNode.right,
      null]

}

pred AvlTreeCondition8[
  nullDerefBool:univ,
  throw:univ
]{
   equ[nullDerefBool,
      true]
   and 
   equ[throw,
      null]

}

pred AvlTreeCondition1[
  thiz:univ
]{
   not (
     isEmptyOrNull[thiz])

}

pred AvlTreeCondition0[
  thiz:univ
]{
   isEmptyOrNull[thiz]

}

pred AvlTreeCondition7[
  maxNode:univ
]{
   not (
     equ[maxNode,
        null]
   )

}

pred AvlTreeCondition6[
  maxNode:univ
]{
   equ[maxNode,
      null]

}

pred AvlTree_nodes_abstraction[
  head:univ->univ,
  left:univ->univ,
  nodes:univ->univ,
  right:univ->univ,
  thiz:univ
]{
   equ[thiz.nodes,
      fun_set_difference[(thiz.head).(fun_reflexive_closure[left+right]),null]]

}

pred AvlTree_invariant[
  element:univ->univ,
  head:univ->univ,
  height:univ->univ,
  left:univ->univ,
  nextData:univ->univ,
  right:univ->univ,
  thiz:univ
]{
   all x:AvlNode | {
     isSubset[x,
             fun_set_difference[(thiz.head).(fun_reflexive_closure[left+right]),null]]
     implies 
             (
               neq[x.element,
                  null]
               and 
               isNotSubset[x,
                          x.(fun_closure[left+right])]
               and 
               (
                 all y:AvlNode | {
                   isSubset[y,
                           fun_set_difference[(x.left).(fun_reflexive_closure[left+right]),null]]
                   implies 
                           isSubset[x.element,
                                   (y.element).(fun_closure[nextData])]
                 
                 }
               )
               and 
               (
                 all y:AvlNode | {
                   isSubset[y,
                           fun_set_difference[(x.right).(fun_reflexive_closure[left+right]),null]]
                   implies 
                           isSubset[y.element,
                                   (x.element).(fun_closure[nextData])]
                 
                 }
               )
               and 
               (
                 (
                   equ[x.left,
                      null]
                   and 
                   equ[x.right,
                      null]
                 )
                 implies 
                         equ[x.height,
                            0]
               )
               and 
               (
                 (
                   equ[x.left,
                      null]
                   and 
                   neq[x.right,
                      null]
                 )
                 implies 
                         (
                           equ[x.height,
                              1]
                           and 
                           equ[(x.right).height,
                              0]
                         )
               )
               and 
               (
                 (
                   neq[x.left,
                      null]
                   and 
                   equ[x.right,
                      null]
                 )
                 implies 
                         (
                           equ[x.height,
                              1]
                           and 
                           equ[(x.left).height,
                              0]
                         )
               )
               and 
               (
                 (
                   neq[x.left,
                      null]
                   and 
                   neq[x.right,
                      null]
                 )
                 implies 
                         (
                           equ[x.height,
                              add[((gt[(x.left).height,
                                (x.right).height])=>((x.left).height)else((x.right).height)),1]
                           ]
                           and 
                           lte[((gt[(x.left).height,
                             (x.right).height])=>(sub[(x.left).height,(x.right).height])else(sub[(x.right).height,(x.left).height])),
                              1]
                         )
               )
             )
   
   }

}
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


//-------------- amelia_avltree_AvlNode--------------//
sig AvlNode extends Object {}
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


pred AvlTree_findMax_0[
  thiz_0: AvlTree,
  throw_1: Throwable + null,
  throw_2: Throwable + null,
  return_1: AvlNode + null,
  head_0: ( AvlTree ) -> one ( AvlNode + null ),
  right_0: ( AvlNode ) -> one ( AvlNode + null ),
  result_1: AvlNode + null,
  maxNode_1: AvlNode + null,
  maxNode_2: AvlNode + null,
  maxNode_3: AvlNode + null,
  maxNode_4: AvlNode + null,
  maxNode_5: AvlNode + null,
  maxNode_6: AvlNode + null,
  maxNode_7: AvlNode + null,
  maxNode_8: AvlNode + null,
  maxNode_9: AvlNode + null,
  maxNode_10: AvlNode + null,
  maxNode_11: AvlNode + null,
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
  nullDerefBool_13: boolean
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
    (
      AvlTreeCondition0[thiz_0]
      and 
      (
        nullDerefBool_2=true)
    )
    or 
    (
      (
        not (
          AvlTreeCondition0[thiz_0])
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
    maxNode_1=thiz_0.head_0)
  and 
  TruePred[]
  and 
  (
    (
      AvlTreeCondition6[maxNode_1]
      and 
      (
        result_1=null)
      and 
      (
        nullDerefBool_2=nullDerefBool_13)
      and 
      (
        maxNode_1=maxNode_11)
    )
    or 
    (
      (
        not (
          AvlTreeCondition6[maxNode_1])
      )
      and 
      (
        (
          AvlTreeCondition2[maxNode_1]
          and 
          (
            nullDerefBool_3=true)
        )
        or 
        (
          (
            not (
              AvlTreeCondition2[maxNode_1])
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
          AvlTreeCondition4[maxNode_1,
                           right_0]
          and 
          (
            (
              AvlTreeCondition2[maxNode_1]
              and 
              (
                nullDerefBool_4=true)
            )
            or 
            (
              (
                not (
                  AvlTreeCondition2[maxNode_1])
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
            maxNode_2=maxNode_1.right_0)
        )
        or 
        (
          TruePred[]
          and 
          (
            maxNode_1=maxNode_2)
          and 
          (
            nullDerefBool_3=nullDerefBool_4)
        )
      )
      and 
      (
        (
          AvlTreeCondition4[maxNode_2,
                           right_0]
          and 
          (
            (
              AvlTreeCondition2[maxNode_2]
              and 
              (
                nullDerefBool_5=true)
            )
            or 
            (
              (
                not (
                  AvlTreeCondition2[maxNode_2])
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
            maxNode_3=maxNode_2.right_0)
        )
        or 
        (
          TruePred[]
          and 
          (
            maxNode_2=maxNode_3)
          and 
          (
            nullDerefBool_4=nullDerefBool_5)
        )
      )
      and 
      (
        (
          AvlTreeCondition4[maxNode_3,
                           right_0]
          and 
          (
            (
              AvlTreeCondition2[maxNode_3]
              and 
              (
                nullDerefBool_6=true)
            )
            or 
            (
              (
                not (
                  AvlTreeCondition2[maxNode_3])
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
            maxNode_4=maxNode_3.right_0)
        )
        or 
        (
          TruePred[]
          and 
          (
            maxNode_3=maxNode_4)
          and 
          (
            nullDerefBool_5=nullDerefBool_6)
        )
      )
      and 
      (
        (
          AvlTreeCondition4[maxNode_4,
                           right_0]
          and 
          (
            (
              AvlTreeCondition2[maxNode_4]
              and 
              (
                nullDerefBool_7=true)
            )
            or 
            (
              (
                not (
                  AvlTreeCondition2[maxNode_4])
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
            maxNode_5=maxNode_4.right_0)
        )
        or 
        (
          TruePred[]
          and 
          (
            maxNode_4=maxNode_5)
          and 
          (
            nullDerefBool_6=nullDerefBool_7)
        )
      )
      and 
      (
        (
          AvlTreeCondition4[maxNode_5,
                           right_0]
          and 
          (
            (
              AvlTreeCondition2[maxNode_5]
              and 
              (
                nullDerefBool_8=true)
            )
            or 
            (
              (
                not (
                  AvlTreeCondition2[maxNode_5])
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
            maxNode_6=maxNode_5.right_0)
        )
        or 
        (
          TruePred[]
          and 
          (
            maxNode_5=maxNode_6)
          and 
          (
            nullDerefBool_7=nullDerefBool_8)
        )
      )
      and 
      (
        (
          AvlTreeCondition4[maxNode_6,
                           right_0]
          and 
          (
            (
              AvlTreeCondition2[maxNode_6]
              and 
              (
                nullDerefBool_9=true)
            )
            or 
            (
              (
                not (
                  AvlTreeCondition2[maxNode_6])
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
            maxNode_7=maxNode_6.right_0)
        )
        or 
        (
          TruePred[]
          and 
          (
            maxNode_6=maxNode_7)
          and 
          (
            nullDerefBool_8=nullDerefBool_9)
        )
      )
      and 
      (
        (
          AvlTreeCondition4[maxNode_7,
                           right_0]
          and 
          (
            (
              AvlTreeCondition2[maxNode_7]
              and 
              (
                nullDerefBool_10=true)
            )
            or 
            (
              (
                not (
                  AvlTreeCondition2[maxNode_7])
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
            maxNode_8=maxNode_7.right_0)
        )
        or 
        (
          TruePred[]
          and 
          (
            maxNode_7=maxNode_8)
          and 
          (
            nullDerefBool_9=nullDerefBool_10)
        )
      )
      and 
      (
        (
          AvlTreeCondition4[maxNode_8,
                           right_0]
          and 
          (
            (
              AvlTreeCondition2[maxNode_8]
              and 
              (
                nullDerefBool_11=true)
            )
            or 
            (
              (
                not (
                  AvlTreeCondition2[maxNode_8])
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
            maxNode_9=maxNode_8.right_0)
        )
        or 
        (
          TruePred[]
          and 
          (
            maxNode_8=maxNode_9)
          and 
          (
            nullDerefBool_10=nullDerefBool_11)
        )
      )
      and 
      (
        (
          AvlTreeCondition4[maxNode_9,
                           right_0]
          and 
          (
            (
              AvlTreeCondition2[maxNode_9]
              and 
              (
                nullDerefBool_12=true)
            )
            or 
            (
              (
                not (
                  AvlTreeCondition2[maxNode_9])
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
            maxNode_10=maxNode_9.right_0)
        )
        or 
        (
          TruePred[]
          and 
          (
            maxNode_9=maxNode_10)
          and 
          (
            nullDerefBool_11=nullDerefBool_12)
        )
      )
      and 
      (
        (
          AvlTreeCondition4[maxNode_10,
                           right_0]
          and 
          (
            (
              AvlTreeCondition2[maxNode_10]
              and 
              (
                nullDerefBool_13=true)
            )
            or 
            (
              (
                not (
                  AvlTreeCondition2[maxNode_10])
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
            maxNode_11=maxNode_10.right_0)
        )
        or 
        (
          TruePred[]
          and 
          (
            maxNode_10=maxNode_11)
          and 
          (
            nullDerefBool_12=nullDerefBool_13)
        )
      )
      and 
      AvlTreeCondition5[maxNode_11,
                       right_0]
      and 
      (
        result_1=maxNode_11)
    )
  )
  and 
  (
    return_1=result_1)
  and 
  (
    (
      AvlTreeCondition8[nullDerefBool_13,
                       throw_1]
      and 
      (
        throw_2=NullPointerExceptionLit)
    )
    or 
    (
      (
        not (
          AvlTreeCondition8[nullDerefBool_13,
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
  element_0: ( AvlNode ) -> one ( Data + null ),
  head_0: ( AvlTree ) -> one ( AvlNode + null ),
  height_0: ( AvlNode ) -> one ( Int ),
  l0_maxNode_1: AvlNode + null,
  l0_maxNode_10: AvlNode + null,
  l0_maxNode_11: AvlNode + null,
  l0_maxNode_2: AvlNode + null,
  l0_maxNode_3: AvlNode + null,
  l0_maxNode_4: AvlNode + null,
  l0_maxNode_5: AvlNode + null,
  l0_maxNode_6: AvlNode + null,
  l0_maxNode_7: AvlNode + null,
  l0_maxNode_8: AvlNode + null,
  l0_maxNode_9: AvlNode + null,
  l0_nullDerefBool_1: boolean,
  l0_nullDerefBool_10: boolean,
  l0_nullDerefBool_11: boolean,
  l0_nullDerefBool_12: boolean,
  l0_nullDerefBool_13: boolean,
  l0_nullDerefBool_2: boolean,
  l0_nullDerefBool_3: boolean,
  l0_nullDerefBool_4: boolean,
  l0_nullDerefBool_5: boolean,
  l0_nullDerefBool_6: boolean,
  l0_nullDerefBool_7: boolean,
  l0_nullDerefBool_8: boolean,
  l0_nullDerefBool_9: boolean,
  l0_result_1: AvlNode + null,
  bleft_0,fleft_0: ( AvlNode ) -> lone ( AvlNode + null ),
  nextData_0: ( Data ) -> one ( Data + null ),
  nodes_0: ( AvlTree ) -> ( AvlNode ),
  return_1: AvlNode + null,
  bright_0,fright_0: ( AvlNode ) -> lone ( AvlNode + null ),
  thiz_0: AvlTree,
  throw_1: Throwable + null,
  throw_2: Throwable + null
}


fact {
  precondition_AvlTree_findMax_0[QF.element_0,
                                QF.head_0,
                                QF.height_0,
                                (QF.fleft_0+QF.bleft_0),
                                QF.nextData_0,
                                QF.nodes_0,
                                (QF.fright_0+QF.bright_0),
                                QF.thiz_0]

}

fact {
  AvlTree_findMax_0[QF.thiz_0,
                   QF.throw_1,
                   QF.throw_2,
                   QF.return_1,
                   QF.head_0,
                   (QF.fright_0+QF.bright_0),
                   QF.l0_result_1,
                   QF.l0_maxNode_1,
                   QF.l0_maxNode_2,
                   QF.l0_maxNode_3,
                   QF.l0_maxNode_4,
                   QF.l0_maxNode_5,
                   QF.l0_maxNode_6,
                   QF.l0_maxNode_7,
                   QF.l0_maxNode_8,
                   QF.l0_maxNode_9,
                   QF.l0_maxNode_10,
                   QF.l0_maxNode_11,
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
                   QF.l0_nullDerefBool_13]

}

assert AvlTree_m1{
  postcondition_AvlTree_findMax_0[QF.element_0,
                                 QF.nextData_0,
                                 QF.nodes_0,
                                 QF.return_1,
                                 QF.thiz_0,
                                 QF.throw_2]
}
check AvlTree_m1 for 0 but 
                 exactly 1 AvlTree, 
                 exactly 20 AvlNode,
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



one sig N0,N1,N2,N3,N4,N5,N6,N7,N8,N9,N10,N11,N12,N13,N14,N15,N16,N17,N18,N19 extends AvlNode {}

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
let entry=(QF.thiz_0).(QF.head_0),ff1=QF.fleft_0,ff2=QF.fright_0,bf1=QF.bleft_0,bf2=QF.bright_0 | { 
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
+N3->N6 
+N3->N7 
+N3->N8 
+N3->null 
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
+N7->N11 
+N7->N12 
+N7->N13 
+N7->N14 
+N7->N15 
+N7->N16 
+N7->null 
+N8->N11 
+N8->N12 
+N8->N13 
+N8->N14 
+N8->N15 
+N8->N16 
+N8->N17 
+N8->N18 
+N8->null 
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
+N15->N19 
+N15->null 
+N16->N19 
+N16->null 
+N17->N19 
+N17->null 
+N18->N19 
+N18->null 
+N19->null 
 
QF.fleft_0 in N0->N1 
+N0->null 
+N1->N3 
+N1->null 
+N2->N3 
+N2->N4 
+N2->N5 
+N2->null 
+N3->N6 
+N3->N7 
+N3->null 
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
+N8->N17 
+N8->null 
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
+N15->N19 
+N15->null 
+N16->N19 
+N16->null 
+N17->N19 
+N17->null 
+N18->N19 
+N18->null 
+N19->null 
 
} 
// fact int_fields 
fact { 
QF.height_0 in N0->0 
+N0->1 
+N0->2 
+N0->3 
+N0->4 
+N0->5 
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
+N15->0 
+N15->1 
+N16->0 
+N16->1 
+N17->0 
+N17->1 
+N18->0 
+N18->1 
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
