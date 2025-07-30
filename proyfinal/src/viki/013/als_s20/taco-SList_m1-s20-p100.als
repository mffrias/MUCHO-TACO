/* 
 * DynAlloy translator options 
 * --------------------------- 
 * applySimplifications= true
 * assertionId= SList_m1
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
//-------------- amelia_jml_slist_SList--------------//
sig SList extends Object {}
{}




pred SListCondition13[
  current:univ,
  result:univ
]{
   not (
     equ[result,
        false]
     and 
     neq[current,
        null]
   )

}

pred SListCondition6[
  value_param:univ
]{
   neq[value_param,
      null]

}

pred SListCondition10[
  equalVal:univ
]{
   equ[equalVal,
      true]

}

pred SListCondition11[
  equalVal:univ
]{
   not (
     equ[equalVal,
        true]
   )

}

pred SListCondition8[
  current:univ,
  nodeValue:univ->univ,
  value_param:univ
]{
   equ[value_param,
      null]
   and 
   equ[current.nodeValue,
      null]

}

pred SListCondition9[
  current:univ,
  nodeValue:univ->univ,
  value_param:univ
]{
   not (
     equ[value_param,
        null]
     and 
     equ[current.nodeValue,
        null]
   )

}

pred SList_myseq_abstraction[
  head:univ->univ,
  myseq:univ->(seq univ),
  next:univ->univ,
  thiz:univ
]{
   equ[fun_set_size[fun_reach[thiz.head,SNode,next]],
      fun_list_size[thiz.myseq]]
   and 
   (
     equ[thiz.head,
        null]
     implies 
             pred_empty_list[thiz.myseq]
   )
   and 
   (
     neq[thiz.head,
        null]
     implies 
             equ[thiz.head,
                fun_list_get[thiz.myseq,0]]
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
               equ[fun_list_get[thiz.myseq,add[i,1]],
                  (fun_list_get[thiz.myseq,i]).next]
     
     }
   )

}

pred SListCondition1[
  thiz:univ
]{
   not (
     isEmptyOrNull[thiz])

}

pred SListCondition0[
  thiz:univ
]{
   isEmptyOrNull[thiz]

}

pred precondition_SList_contains_0[
  head:univ->univ,
  myseq:univ->(seq univ),
  next:univ->univ,
  thiz:univ
]{
   SList_invariant[head,
                  next,
                  thiz]
   and 
   SList_myseq_abstraction[head,
                          myseq,
                          next,
                          thiz]

}

pred SListCondition2[
  current:univ
]{
   isEmptyOrNull[current]

}

pred SListCondition3[
  current:univ
]{
   not (
     isEmptyOrNull[current])

}

pred postcondition_SList_contains_0[
  myseq':univ->(seq univ),
  nodeValue':univ->univ,
  return':univ,
  thiz':univ,
  throw':univ,
  value_param:univ
]{
   SList_ensures[myseq',
                nodeValue',
                return',
                thiz',
                value_param]
   and 
   equ[throw',
      null]

}

pred SList_invariant[
  head:univ->univ,
  next:univ->univ,
  thiz:univ
]{
   all n:SNode+null | {
     equ[fun_set_contains[fun_reach[thiz.head,SNode,next],n],
        true]
     implies 
             (
               not (
                 equ[fun_set_contains[fun_reach[n.next,SNode,next],n],
                    true]
               )
             )
   
   }

}

pred SList_ensures[
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
         instanceOf[fun_list_get[thiz'.myseq',i],
                   SNode]
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
                 instanceOf[fun_list_get[thiz'.myseq',i],
                           SNode]
                 and 
                 equ[(fun_list_get[thiz'.myseq',i]).nodeValue',
                    value_param]
               
               }
             )
   )

}

pred SListCondition5[
  current:univ,
  nodeValue:univ->univ,
  value_param:univ
]{
   not (
     equ[value_param,
        current.nodeValue]
   )

}

pred SListCondition12[
  current:univ,
  result:univ
]{
   equ[result,
      false]
   and 
   neq[current,
      null]

}

pred SListCondition15[
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

pred SListCondition4[
  current:univ,
  nodeValue:univ->univ,
  value_param:univ
]{
   equ[value_param,
      current.nodeValue]

}

pred SListCondition14[
  nullDerefBool:univ,
  throw:univ
]{
   equ[nullDerefBool,
      true]
   and 
   equ[throw,
      null]

}

pred SListCondition7[
  value_param:univ
]{
   not (
     neq[value_param,
        null]
   )

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





//-------------- amelia_jml_slist_SNode--------------//
sig SNode extends Object {}
{}





//-------------- java_lang_Object--------------//
abstract sig Object {}
{}





//-------------- amelia_jml_slist_Data--------------//
sig Data extends Object {}
{}





//-------------- java_lang_NullPointerException--------------//
abstract sig NullPointerException extends RuntimeException {}
{}



one
sig NullPointerExceptionLit extends NullPointerException {}
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


pred SList_contains_0[
  thiz_0: SList,
  throw_1: Throwable + null,
  throw_2: Throwable + null,
  return_1: boolean,
  value_param_0: Data + null,
  head_0: ( SList ) -> one ( SNode + null ),
  next_0: ( SNode ) -> one ( SNode + null ),
  nodeValue_0: ( SNode ) -> one ( Data + null ),
  result_1: boolean,
  result_2: boolean,
  result_3: boolean,
  result_4: boolean,
  result_5: boolean,
  result_6: boolean,
  result_7: boolean,
  result_8: boolean,
  result_9: boolean,
  result_10: boolean,
  result_11: boolean,
  equalVal_0: boolean,
  equalVal_1: boolean,
  equalVal_2: boolean,
  equalVal_3: boolean,
  equalVal_4: boolean,
  equalVal_5: boolean,
  equalVal_6: boolean,
  equalVal_7: boolean,
  equalVal_8: boolean,
  equalVal_9: boolean,
  equalVal_10: boolean,
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
  current_1: SNode + null,
  current_2: SNode + null,
  current_3: SNode + null,
  current_4: SNode + null,
  current_5: SNode + null,
  current_6: SNode + null,
  current_7: SNode + null,
  current_8: SNode + null,
  current_9: SNode + null,
  current_10: SNode + null,
  current_11: SNode + null
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
  (
    (
      SListCondition0[thiz_0]
      and 
      (
        nullDerefBool_2=true)
    )
    or 
    (
      (
        not (
          SListCondition0[thiz_0])
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
    current_1=thiz_0.head_0)
  and 
  (
    result_1=false)
  and 
  (
    (
      SListCondition12[current_1,
                      result_1]
      and 
      TruePred[]
      and 
      (
        (
          SListCondition2[current_1]
          and 
          (
            nullDerefBool_3=true)
        )
        or 
        (
          (
            not (
              SListCondition2[current_1])
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
          SListCondition8[current_1,
                         nodeValue_0,
                         value_param_0]
          and 
          (
            equalVal_1=true)
          and 
          (
            nullDerefBool_3=nullDerefBool_4)
        )
        or 
        (
          (
            not (
              SListCondition8[current_1,
                             nodeValue_0,
                             value_param_0]
            )
          )
          and 
          (
            (
              SListCondition6[value_param_0]
              and 
              (
                (
                  SListCondition2[current_1]
                  and 
                  (
                    nullDerefBool_4=true)
                )
                or 
                (
                  (
                    not (
                      SListCondition2[current_1])
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
                  SListCondition4[current_1,
                                 nodeValue_0,
                                 value_param_0]
                  and 
                  (
                    equalVal_1=true)
                )
                or 
                (
                  (
                    not (
                      SListCondition4[current_1,
                                     nodeValue_0,
                                     value_param_0]
                    )
                  )
                  and 
                  (
                    equalVal_1=false)
                )
              )
            )
            or 
            (
              (
                not (
                  SListCondition6[value_param_0])
              )
              and 
              (
                equalVal_1=false)
              and 
              (
                nullDerefBool_3=nullDerefBool_4)
            )
          )
        )
      )
      and 
      (
        (
          SListCondition10[equalVal_1]
          and 
          (
            result_2=true)
        )
        or 
        (
          (
            not (
              SListCondition10[equalVal_1])
          )
          and 
          TruePred[]
          and 
          (
            result_1=result_2)
        )
      )
      and 
      (
        (
          SListCondition2[current_1]
          and 
          (
            nullDerefBool_5=true)
        )
        or 
        (
          (
            not (
              SListCondition2[current_1])
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
        current_2=current_1.next_0)
    )
    or 
    (
      TruePred[]
      and 
      (
        result_1=result_2)
      and 
      (
        equalVal_0=equalVal_1)
      and 
      (
        current_1=current_2)
      and 
      (
        nullDerefBool_2=nullDerefBool_5)
    )
  )
  and 
  (
    (
      SListCondition12[current_2,
                      result_2]
      and 
      TruePred[]
      and 
      (
        (
          SListCondition2[current_2]
          and 
          (
            nullDerefBool_6=true)
        )
        or 
        (
          (
            not (
              SListCondition2[current_2])
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
          SListCondition8[current_2,
                         nodeValue_0,
                         value_param_0]
          and 
          (
            equalVal_2=true)
          and 
          (
            nullDerefBool_6=nullDerefBool_7)
        )
        or 
        (
          (
            not (
              SListCondition8[current_2,
                             nodeValue_0,
                             value_param_0]
            )
          )
          and 
          (
            (
              SListCondition6[value_param_0]
              and 
              (
                (
                  SListCondition2[current_2]
                  and 
                  (
                    nullDerefBool_7=true)
                )
                or 
                (
                  (
                    not (
                      SListCondition2[current_2])
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
                  SListCondition4[current_2,
                                 nodeValue_0,
                                 value_param_0]
                  and 
                  (
                    equalVal_2=true)
                )
                or 
                (
                  (
                    not (
                      SListCondition4[current_2,
                                     nodeValue_0,
                                     value_param_0]
                    )
                  )
                  and 
                  (
                    equalVal_2=false)
                )
              )
            )
            or 
            (
              (
                not (
                  SListCondition6[value_param_0])
              )
              and 
              (
                equalVal_2=false)
              and 
              (
                nullDerefBool_6=nullDerefBool_7)
            )
          )
        )
      )
      and 
      (
        (
          SListCondition10[equalVal_2]
          and 
          (
            result_3=true)
        )
        or 
        (
          (
            not (
              SListCondition10[equalVal_2])
          )
          and 
          TruePred[]
          and 
          (
            result_2=result_3)
        )
      )
      and 
      (
        (
          SListCondition2[current_2]
          and 
          (
            nullDerefBool_8=true)
        )
        or 
        (
          (
            not (
              SListCondition2[current_2])
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
        current_3=current_2.next_0)
    )
    or 
    (
      TruePred[]
      and 
      (
        result_2=result_3)
      and 
      (
        equalVal_1=equalVal_2)
      and 
      (
        current_2=current_3)
      and 
      (
        nullDerefBool_5=nullDerefBool_8)
    )
  )
  and 
  (
    (
      SListCondition12[current_3,
                      result_3]
      and 
      TruePred[]
      and 
      (
        (
          SListCondition2[current_3]
          and 
          (
            nullDerefBool_9=true)
        )
        or 
        (
          (
            not (
              SListCondition2[current_3])
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
          SListCondition8[current_3,
                         nodeValue_0,
                         value_param_0]
          and 
          (
            equalVal_3=true)
          and 
          (
            nullDerefBool_9=nullDerefBool_10)
        )
        or 
        (
          (
            not (
              SListCondition8[current_3,
                             nodeValue_0,
                             value_param_0]
            )
          )
          and 
          (
            (
              SListCondition6[value_param_0]
              and 
              (
                (
                  SListCondition2[current_3]
                  and 
                  (
                    nullDerefBool_10=true)
                )
                or 
                (
                  (
                    not (
                      SListCondition2[current_3])
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
                  SListCondition4[current_3,
                                 nodeValue_0,
                                 value_param_0]
                  and 
                  (
                    equalVal_3=true)
                )
                or 
                (
                  (
                    not (
                      SListCondition4[current_3,
                                     nodeValue_0,
                                     value_param_0]
                    )
                  )
                  and 
                  (
                    equalVal_3=false)
                )
              )
            )
            or 
            (
              (
                not (
                  SListCondition6[value_param_0])
              )
              and 
              (
                equalVal_3=false)
              and 
              (
                nullDerefBool_9=nullDerefBool_10)
            )
          )
        )
      )
      and 
      (
        (
          SListCondition10[equalVal_3]
          and 
          (
            result_4=true)
        )
        or 
        (
          (
            not (
              SListCondition10[equalVal_3])
          )
          and 
          TruePred[]
          and 
          (
            result_3=result_4)
        )
      )
      and 
      (
        (
          SListCondition2[current_3]
          and 
          (
            nullDerefBool_11=true)
        )
        or 
        (
          (
            not (
              SListCondition2[current_3])
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
        current_4=current_3.next_0)
    )
    or 
    (
      TruePred[]
      and 
      (
        result_3=result_4)
      and 
      (
        equalVal_2=equalVal_3)
      and 
      (
        current_3=current_4)
      and 
      (
        nullDerefBool_8=nullDerefBool_11)
    )
  )
  and 
  (
    (
      SListCondition12[current_4,
                      result_4]
      and 
      TruePred[]
      and 
      (
        (
          SListCondition2[current_4]
          and 
          (
            nullDerefBool_12=true)
        )
        or 
        (
          (
            not (
              SListCondition2[current_4])
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
          SListCondition8[current_4,
                         nodeValue_0,
                         value_param_0]
          and 
          (
            equalVal_4=true)
          and 
          (
            nullDerefBool_12=nullDerefBool_13)
        )
        or 
        (
          (
            not (
              SListCondition8[current_4,
                             nodeValue_0,
                             value_param_0]
            )
          )
          and 
          (
            (
              SListCondition6[value_param_0]
              and 
              (
                (
                  SListCondition2[current_4]
                  and 
                  (
                    nullDerefBool_13=true)
                )
                or 
                (
                  (
                    not (
                      SListCondition2[current_4])
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
                  SListCondition4[current_4,
                                 nodeValue_0,
                                 value_param_0]
                  and 
                  (
                    equalVal_4=true)
                )
                or 
                (
                  (
                    not (
                      SListCondition4[current_4,
                                     nodeValue_0,
                                     value_param_0]
                    )
                  )
                  and 
                  (
                    equalVal_4=false)
                )
              )
            )
            or 
            (
              (
                not (
                  SListCondition6[value_param_0])
              )
              and 
              (
                equalVal_4=false)
              and 
              (
                nullDerefBool_12=nullDerefBool_13)
            )
          )
        )
      )
      and 
      (
        (
          SListCondition10[equalVal_4]
          and 
          (
            result_5=true)
        )
        or 
        (
          (
            not (
              SListCondition10[equalVal_4])
          )
          and 
          TruePred[]
          and 
          (
            result_4=result_5)
        )
      )
      and 
      (
        (
          SListCondition2[current_4]
          and 
          (
            nullDerefBool_14=true)
        )
        or 
        (
          (
            not (
              SListCondition2[current_4])
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
        current_5=current_4.next_0)
    )
    or 
    (
      TruePred[]
      and 
      (
        result_4=result_5)
      and 
      (
        equalVal_3=equalVal_4)
      and 
      (
        current_4=current_5)
      and 
      (
        nullDerefBool_11=nullDerefBool_14)
    )
  )
  and 
  (
    (
      SListCondition12[current_5,
                      result_5]
      and 
      TruePred[]
      and 
      (
        (
          SListCondition2[current_5]
          and 
          (
            nullDerefBool_15=true)
        )
        or 
        (
          (
            not (
              SListCondition2[current_5])
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
          SListCondition8[current_5,
                         nodeValue_0,
                         value_param_0]
          and 
          (
            equalVal_5=true)
          and 
          (
            nullDerefBool_15=nullDerefBool_16)
        )
        or 
        (
          (
            not (
              SListCondition8[current_5,
                             nodeValue_0,
                             value_param_0]
            )
          )
          and 
          (
            (
              SListCondition6[value_param_0]
              and 
              (
                (
                  SListCondition2[current_5]
                  and 
                  (
                    nullDerefBool_16=true)
                )
                or 
                (
                  (
                    not (
                      SListCondition2[current_5])
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
                  SListCondition4[current_5,
                                 nodeValue_0,
                                 value_param_0]
                  and 
                  (
                    equalVal_5=true)
                )
                or 
                (
                  (
                    not (
                      SListCondition4[current_5,
                                     nodeValue_0,
                                     value_param_0]
                    )
                  )
                  and 
                  (
                    equalVal_5=false)
                )
              )
            )
            or 
            (
              (
                not (
                  SListCondition6[value_param_0])
              )
              and 
              (
                equalVal_5=false)
              and 
              (
                nullDerefBool_15=nullDerefBool_16)
            )
          )
        )
      )
      and 
      (
        (
          SListCondition10[equalVal_5]
          and 
          (
            result_6=true)
        )
        or 
        (
          (
            not (
              SListCondition10[equalVal_5])
          )
          and 
          TruePred[]
          and 
          (
            result_5=result_6)
        )
      )
      and 
      (
        (
          SListCondition2[current_5]
          and 
          (
            nullDerefBool_17=true)
        )
        or 
        (
          (
            not (
              SListCondition2[current_5])
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
        current_6=current_5.next_0)
    )
    or 
    (
      TruePred[]
      and 
      (
        result_5=result_6)
      and 
      (
        equalVal_4=equalVal_5)
      and 
      (
        current_5=current_6)
      and 
      (
        nullDerefBool_14=nullDerefBool_17)
    )
  )
  and 
  (
    (
      SListCondition12[current_6,
                      result_6]
      and 
      TruePred[]
      and 
      (
        (
          SListCondition2[current_6]
          and 
          (
            nullDerefBool_18=true)
        )
        or 
        (
          (
            not (
              SListCondition2[current_6])
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
          SListCondition8[current_6,
                         nodeValue_0,
                         value_param_0]
          and 
          (
            equalVal_6=true)
          and 
          (
            nullDerefBool_18=nullDerefBool_19)
        )
        or 
        (
          (
            not (
              SListCondition8[current_6,
                             nodeValue_0,
                             value_param_0]
            )
          )
          and 
          (
            (
              SListCondition6[value_param_0]
              and 
              (
                (
                  SListCondition2[current_6]
                  and 
                  (
                    nullDerefBool_19=true)
                )
                or 
                (
                  (
                    not (
                      SListCondition2[current_6])
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
                  SListCondition4[current_6,
                                 nodeValue_0,
                                 value_param_0]
                  and 
                  (
                    equalVal_6=true)
                )
                or 
                (
                  (
                    not (
                      SListCondition4[current_6,
                                     nodeValue_0,
                                     value_param_0]
                    )
                  )
                  and 
                  (
                    equalVal_6=false)
                )
              )
            )
            or 
            (
              (
                not (
                  SListCondition6[value_param_0])
              )
              and 
              (
                equalVal_6=false)
              and 
              (
                nullDerefBool_18=nullDerefBool_19)
            )
          )
        )
      )
      and 
      (
        (
          SListCondition10[equalVal_6]
          and 
          (
            result_7=true)
        )
        or 
        (
          (
            not (
              SListCondition10[equalVal_6])
          )
          and 
          TruePred[]
          and 
          (
            result_6=result_7)
        )
      )
      and 
      (
        (
          SListCondition2[current_6]
          and 
          (
            nullDerefBool_20=true)
        )
        or 
        (
          (
            not (
              SListCondition2[current_6])
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
        current_7=current_6.next_0)
    )
    or 
    (
      TruePred[]
      and 
      (
        result_6=result_7)
      and 
      (
        equalVal_5=equalVal_6)
      and 
      (
        current_6=current_7)
      and 
      (
        nullDerefBool_17=nullDerefBool_20)
    )
  )
  and 
  (
    (
      SListCondition12[current_7,
                      result_7]
      and 
      TruePred[]
      and 
      (
        (
          SListCondition2[current_7]
          and 
          (
            nullDerefBool_21=true)
        )
        or 
        (
          (
            not (
              SListCondition2[current_7])
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
          SListCondition8[current_7,
                         nodeValue_0,
                         value_param_0]
          and 
          (
            equalVal_7=true)
          and 
          (
            nullDerefBool_21=nullDerefBool_22)
        )
        or 
        (
          (
            not (
              SListCondition8[current_7,
                             nodeValue_0,
                             value_param_0]
            )
          )
          and 
          (
            (
              SListCondition6[value_param_0]
              and 
              (
                (
                  SListCondition2[current_7]
                  and 
                  (
                    nullDerefBool_22=true)
                )
                or 
                (
                  (
                    not (
                      SListCondition2[current_7])
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
                  SListCondition4[current_7,
                                 nodeValue_0,
                                 value_param_0]
                  and 
                  (
                    equalVal_7=true)
                )
                or 
                (
                  (
                    not (
                      SListCondition4[current_7,
                                     nodeValue_0,
                                     value_param_0]
                    )
                  )
                  and 
                  (
                    equalVal_7=false)
                )
              )
            )
            or 
            (
              (
                not (
                  SListCondition6[value_param_0])
              )
              and 
              (
                equalVal_7=false)
              and 
              (
                nullDerefBool_21=nullDerefBool_22)
            )
          )
        )
      )
      and 
      (
        (
          SListCondition10[equalVal_7]
          and 
          (
            result_8=true)
        )
        or 
        (
          (
            not (
              SListCondition10[equalVal_7])
          )
          and 
          TruePred[]
          and 
          (
            result_7=result_8)
        )
      )
      and 
      (
        (
          SListCondition2[current_7]
          and 
          (
            nullDerefBool_23=true)
        )
        or 
        (
          (
            not (
              SListCondition2[current_7])
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
        current_8=current_7.next_0)
    )
    or 
    (
      TruePred[]
      and 
      (
        result_7=result_8)
      and 
      (
        equalVal_6=equalVal_7)
      and 
      (
        current_7=current_8)
      and 
      (
        nullDerefBool_20=nullDerefBool_23)
    )
  )
  and 
  (
    (
      SListCondition12[current_8,
                      result_8]
      and 
      TruePred[]
      and 
      (
        (
          SListCondition2[current_8]
          and 
          (
            nullDerefBool_24=true)
        )
        or 
        (
          (
            not (
              SListCondition2[current_8])
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
          SListCondition8[current_8,
                         nodeValue_0,
                         value_param_0]
          and 
          (
            equalVal_8=true)
          and 
          (
            nullDerefBool_24=nullDerefBool_25)
        )
        or 
        (
          (
            not (
              SListCondition8[current_8,
                             nodeValue_0,
                             value_param_0]
            )
          )
          and 
          (
            (
              SListCondition6[value_param_0]
              and 
              (
                (
                  SListCondition2[current_8]
                  and 
                  (
                    nullDerefBool_25=true)
                )
                or 
                (
                  (
                    not (
                      SListCondition2[current_8])
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
                  SListCondition4[current_8,
                                 nodeValue_0,
                                 value_param_0]
                  and 
                  (
                    equalVal_8=true)
                )
                or 
                (
                  (
                    not (
                      SListCondition4[current_8,
                                     nodeValue_0,
                                     value_param_0]
                    )
                  )
                  and 
                  (
                    equalVal_8=false)
                )
              )
            )
            or 
            (
              (
                not (
                  SListCondition6[value_param_0])
              )
              and 
              (
                equalVal_8=false)
              and 
              (
                nullDerefBool_24=nullDerefBool_25)
            )
          )
        )
      )
      and 
      (
        (
          SListCondition10[equalVal_8]
          and 
          (
            result_9=true)
        )
        or 
        (
          (
            not (
              SListCondition10[equalVal_8])
          )
          and 
          TruePred[]
          and 
          (
            result_8=result_9)
        )
      )
      and 
      (
        (
          SListCondition2[current_8]
          and 
          (
            nullDerefBool_26=true)
        )
        or 
        (
          (
            not (
              SListCondition2[current_8])
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
        current_9=current_8.next_0)
    )
    or 
    (
      TruePred[]
      and 
      (
        result_8=result_9)
      and 
      (
        equalVal_7=equalVal_8)
      and 
      (
        current_8=current_9)
      and 
      (
        nullDerefBool_23=nullDerefBool_26)
    )
  )
  and 
  (
    (
      SListCondition12[current_9,
                      result_9]
      and 
      TruePred[]
      and 
      (
        (
          SListCondition2[current_9]
          and 
          (
            nullDerefBool_27=true)
        )
        or 
        (
          (
            not (
              SListCondition2[current_9])
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
          SListCondition8[current_9,
                         nodeValue_0,
                         value_param_0]
          and 
          (
            equalVal_9=true)
          and 
          (
            nullDerefBool_27=nullDerefBool_28)
        )
        or 
        (
          (
            not (
              SListCondition8[current_9,
                             nodeValue_0,
                             value_param_0]
            )
          )
          and 
          (
            (
              SListCondition6[value_param_0]
              and 
              (
                (
                  SListCondition2[current_9]
                  and 
                  (
                    nullDerefBool_28=true)
                )
                or 
                (
                  (
                    not (
                      SListCondition2[current_9])
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
                  SListCondition4[current_9,
                                 nodeValue_0,
                                 value_param_0]
                  and 
                  (
                    equalVal_9=true)
                )
                or 
                (
                  (
                    not (
                      SListCondition4[current_9,
                                     nodeValue_0,
                                     value_param_0]
                    )
                  )
                  and 
                  (
                    equalVal_9=false)
                )
              )
            )
            or 
            (
              (
                not (
                  SListCondition6[value_param_0])
              )
              and 
              (
                equalVal_9=false)
              and 
              (
                nullDerefBool_27=nullDerefBool_28)
            )
          )
        )
      )
      and 
      (
        (
          SListCondition10[equalVal_9]
          and 
          (
            result_10=true)
        )
        or 
        (
          (
            not (
              SListCondition10[equalVal_9])
          )
          and 
          TruePred[]
          and 
          (
            result_9=result_10)
        )
      )
      and 
      (
        (
          SListCondition2[current_9]
          and 
          (
            nullDerefBool_29=true)
        )
        or 
        (
          (
            not (
              SListCondition2[current_9])
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
        current_10=current_9.next_0)
    )
    or 
    (
      TruePred[]
      and 
      (
        result_9=result_10)
      and 
      (
        equalVal_8=equalVal_9)
      and 
      (
        current_9=current_10)
      and 
      (
        nullDerefBool_26=nullDerefBool_29)
    )
  )
  and 
  (
    (
      SListCondition12[current_10,
                      result_10]
      and 
      TruePred[]
      and 
      (
        (
          SListCondition2[current_10]
          and 
          (
            nullDerefBool_30=true)
        )
        or 
        (
          (
            not (
              SListCondition2[current_10])
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
          SListCondition8[current_10,
                         nodeValue_0,
                         value_param_0]
          and 
          (
            equalVal_10=true)
          and 
          (
            nullDerefBool_30=nullDerefBool_31)
        )
        or 
        (
          (
            not (
              SListCondition8[current_10,
                             nodeValue_0,
                             value_param_0]
            )
          )
          and 
          (
            (
              SListCondition6[value_param_0]
              and 
              (
                (
                  SListCondition2[current_10]
                  and 
                  (
                    nullDerefBool_31=true)
                )
                or 
                (
                  (
                    not (
                      SListCondition2[current_10])
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
                  SListCondition4[current_10,
                                 nodeValue_0,
                                 value_param_0]
                  and 
                  (
                    equalVal_10=true)
                )
                or 
                (
                  (
                    not (
                      SListCondition4[current_10,
                                     nodeValue_0,
                                     value_param_0]
                    )
                  )
                  and 
                  (
                    equalVal_10=false)
                )
              )
            )
            or 
            (
              (
                not (
                  SListCondition6[value_param_0])
              )
              and 
              (
                equalVal_10=false)
              and 
              (
                nullDerefBool_30=nullDerefBool_31)
            )
          )
        )
      )
      and 
      (
        (
          SListCondition10[equalVal_10]
          and 
          (
            result_11=true)
        )
        or 
        (
          (
            not (
              SListCondition10[equalVal_10])
          )
          and 
          TruePred[]
          and 
          (
            result_10=result_11)
        )
      )
      and 
      (
        (
          SListCondition2[current_10]
          and 
          (
            nullDerefBool_32=true)
        )
        or 
        (
          (
            not (
              SListCondition2[current_10])
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
        current_11=current_10.next_0)
    )
    or 
    (
      TruePred[]
      and 
      (
        result_10=result_11)
      and 
      (
        equalVal_9=equalVal_10)
      and 
      (
        current_10=current_11)
      and 
      (
        nullDerefBool_29=nullDerefBool_32)
    )
  )
  and 
  SListCondition13[current_11,
                  result_11]
  and 
  (
    return_1=result_11)
  and 
  (
    (
      SListCondition14[nullDerefBool_32,
                      throw_1]
      and 
      (
        throw_2=NullPointerExceptionLit)
    )
    or 
    (
      (
        not (
          SListCondition14[nullDerefBool_32,
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
  head_0: ( SList ) -> one ( SNode + null ),
  l0_current_1: SNode + null,
  l0_current_10: SNode + null,
  l0_current_11: SNode + null,
  l0_current_2: SNode + null,
  l0_current_3: SNode + null,
  l0_current_4: SNode + null,
  l0_current_5: SNode + null,
  l0_current_6: SNode + null,
  l0_current_7: SNode + null,
  l0_current_8: SNode + null,
  l0_current_9: SNode + null,
  l0_equalVal_0: boolean,
  l0_equalVal_1: boolean,
  l0_equalVal_10: boolean,
  l0_equalVal_2: boolean,
  l0_equalVal_3: boolean,
  l0_equalVal_4: boolean,
  l0_equalVal_5: boolean,
  l0_equalVal_6: boolean,
  l0_equalVal_7: boolean,
  l0_equalVal_8: boolean,
  l0_equalVal_9: boolean,
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
  l0_nullDerefBool_29: boolean,
  l0_nullDerefBool_3: boolean,
  l0_nullDerefBool_30: boolean,
  l0_nullDerefBool_31: boolean,
  l0_nullDerefBool_32: boolean,
  l0_nullDerefBool_4: boolean,
  l0_nullDerefBool_5: boolean,
  l0_nullDerefBool_6: boolean,
  l0_nullDerefBool_7: boolean,
  l0_nullDerefBool_8: boolean,
  l0_nullDerefBool_9: boolean,
  l0_result_1: boolean,
  l0_result_10: boolean,
  l0_result_11: boolean,
  l0_result_2: boolean,
  l0_result_3: boolean,
  l0_result_4: boolean,
  l0_result_5: boolean,
  l0_result_6: boolean,
  l0_result_7: boolean,
  l0_result_8: boolean,
  l0_result_9: boolean,
  myseq_0: ( SList ) -> ( seq ( null + Object ) ),
  bnext_0,fnext_0: ( SNode ) -> lone ( SNode + null ),
  nodeValue_0: ( SNode ) -> one ( Data + null ),
  return_1: boolean,
  thiz_0: SList,
  throw_1: Throwable + null,
  throw_2: Throwable + null,
  value_param_0: Data + null
}


fact {
  precondition_SList_contains_0[QF.head_0,
                               QF.myseq_0,
                               (QF.fnext_0+QF.bnext_0),
                               QF.thiz_0]

}

fact {
  SList_contains_0[QF.thiz_0,
                  QF.throw_1,
                  QF.throw_2,
                  QF.return_1,
                  QF.value_param_0,
                  QF.head_0,
                  (QF.fnext_0+QF.bnext_0),
                  QF.nodeValue_0,
                  QF.l0_result_1,
                  QF.l0_result_2,
                  QF.l0_result_3,
                  QF.l0_result_4,
                  QF.l0_result_5,
                  QF.l0_result_6,
                  QF.l0_result_7,
                  QF.l0_result_8,
                  QF.l0_result_9,
                  QF.l0_result_10,
                  QF.l0_result_11,
                  QF.l0_equalVal_0,
                  QF.l0_equalVal_1,
                  QF.l0_equalVal_2,
                  QF.l0_equalVal_3,
                  QF.l0_equalVal_4,
                  QF.l0_equalVal_5,
                  QF.l0_equalVal_6,
                  QF.l0_equalVal_7,
                  QF.l0_equalVal_8,
                  QF.l0_equalVal_9,
                  QF.l0_equalVal_10,
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
                  QF.l0_nullDerefBool_29,
                  QF.l0_nullDerefBool_30,
                  QF.l0_nullDerefBool_31,
                  QF.l0_nullDerefBool_32,
                  QF.l0_current_1,
                  QF.l0_current_2,
                  QF.l0_current_3,
                  QF.l0_current_4,
                  QF.l0_current_5,
                  QF.l0_current_6,
                  QF.l0_current_7,
                  QF.l0_current_8,
                  QF.l0_current_9,
                  QF.l0_current_10,
                  QF.l0_current_11]

}

assert SList_m1{
  postcondition_SList_contains_0[QF.myseq_0,
                                QF.nodeValue_0,
                                QF.return_1,
                                QF.thiz_0,
                                QF.throw_2,
                                QF.value_param_0]
}
check SList_m1 for 0 but 
                 exactly 1 SList, 
                 exactly 20 Data,
                 exactly 20 SNode,
                 20 seq, 
                 6 int  



one sig N0,N1,N2,N3,N4,N5,N6,N7,N8,N9,N10,N11,N12,N13,N14,N15,N16,N17,N18,N19 extends SNode {}
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
//fact orderingAxiom1 
fact { 
let entry=(QF.thiz_0).(QF.head_0),ff1=QF.fnext_0,bf1=QF.bnext_0 | { 
-- forwardPlusBackwardAreFunctions
no ((ff1.univ) & (bf1.univ)) 
N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14+N15+N16+N17+N18+N19 = ff1.univ + bf1.univ 
--forwardIsIndeedForward 
entry in N0+null 
all n : entry.*ff1 - null | node_min[ff1.n] in node_prevs[n] 
all disj n1, n2 : entry.*ff1 - null | 
{ 
      ( some (ff1.n1 ) && some (ff1.n2 ) && node_min[ff1.n1 ] in 
      node_prevs[node_min[ff1.n2 ]] ) 
        implies n1 in node_prevs[n2] 
  } 
  --backwardsIsIndeedBackwards 
   (bf1 in node_relprevs)
  --prefixReachableForward 
    all x : entry.*(ff1) -null | node_prevs[x] in entry.*(ff1) 
} 
} 
//fact ffields_bfields 
fact { 
QF.bnext_0 in none->none 
QF.fnext_0 in N0->N1 
+N0->null 
+N1->N2 
+N1->null 
+N2->N3 
+N2->null 
+N3->N4 
+N3->null 
+N4->N5 
+N4->null 
+N5->N6 
+N5->null 
+N6->N7 
+N6->null 
+N7->N8 
+N7->null 
+N8->N9 
+N8->null 
+N9->N10 
+N9->null 
+N10->N11 
+N10->null 
+N11->N12 
+N11->null 
+N12->N13 
+N12->null 
+N13->N14 
+N13->null 
+N14->N15 
+N14->null 
+N15->N16 
+N15->null 
+N16->N17 
+N16->null 
+N17->N18 
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
} 
//fact root_node_fields 
fact { 
} 
