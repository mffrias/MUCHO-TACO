/* 
 * DynAlloy translator options 
 * --------------------------- 
 * applySimplifications= true
 * assertionId= SList_m2
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




pred SList_ensures[
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

pred SList_requires[
  freshNode:univ,
  myseq:univ->(seq univ),
  thiz:univ
]{
   neq[freshNode,
      null]
   and 
   (
     not (
       some i:Int | {
         gte[i,
            0]
         and 
         lt[i,
           fun_list_size[thiz.myseq]]
         and 
         equ[fun_list_get[thiz.myseq,i],
            freshNode]
       
       }
     )
   )

}

pred SListCondition4[
  current:univ
]{
   isEmptyOrNull[current]

}

pred postcondition_SList_insertBack_0[
  freshNode:univ,
  head':univ->univ,
  myseq:univ->(seq univ),
  myseq':univ->(seq univ),
  next':univ->univ,
  thiz:univ,
  thiz':univ,
  throw':univ
]{
   SList_ensures[freshNode,
                myseq,
                myseq',
                thiz,
                thiz']
   and 
   SList_invariant[head',
                  next',
                  thiz']
   and 
   equ[throw',
      null]

}

pred SListCondition5[
  current:univ
]{
   not (
     isEmptyOrNull[current])

}

pred SListCondition12[
  head:univ->univ,
  myseq:univ->(seq univ),
  next:univ->univ,
  thiz:univ
]{
   SList_myseq_abstraction[head,
                          myseq,
                          next,
                          thiz]

}

pred SListCondition3[
  thiz:univ
]{
   not (
     isEmptyOrNull[thiz])

}

pred SListCondition7[
  current:univ,
  next:univ->univ
]{
   not (
     neq[current.next,
        null]
   )

}

pred SListCondition2[
  thiz:univ
]{
   isEmptyOrNull[thiz]

}

pred SListCondition6[
  current:univ,
  next:univ->univ
]{
   neq[current.next,
      null]

}

pred SListCondition9[
  head:univ->univ,
  thiz:univ
]{
   not (
     equ[thiz.head,
        null]
   )

}

pred SListCondition8[
  head:univ->univ,
  thiz:univ
]{
   equ[thiz.head,
      null]

}

pred precondition_SList_insertBack_0[
  freshNode:univ,
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
   and 
   SList_requires[freshNode,
                 myseq,
                 thiz]

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

pred SListCondition0[
  freshNode:univ
]{
   isEmptyOrNull[freshNode]

}

pred SListCondition11[
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

pred SListCondition10[
  nullDerefBool:univ,
  throw:univ
]{
   equ[nullDerefBool,
      true]
   and 
   equ[throw,
      null]

}

pred SListCondition1[
  freshNode:univ
]{
   not (
     isEmptyOrNull[freshNode])

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


pred SList_insertBack_0[
  thiz_0: SList,
  throw_1: Throwable + null,
  throw_2: Throwable + null,
  data_0: Data + null,
  freshNode_0: SNode + null,
  head_0: ( SList ) -> one ( SNode + null ),
  head_1: ( SList ) -> one ( SNode + null ),
  next_0: ( SNode ) -> one ( SNode + null ),
  next_1: ( SNode ) -> one ( SNode + null ),
  next_2: ( SNode ) -> one ( SNode + null ),
  nodeValue_0: ( SNode ) -> one ( Data + null ),
  nodeValue_1: ( SNode ) -> one ( Data + null ),
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
  current_0: SNode + null,
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
  (
    (
      SListCondition0[freshNode_0]
      and 
      (
        nullDerefBool_2=true)
    )
    or 
    (
      (
        not (
          SListCondition0[freshNode_0])
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
    nodeValue_1=(nodeValue_0)++((freshNode_0)->(data_0)))
  and 
  (
    (
      SListCondition0[freshNode_0]
      and 
      (
        nullDerefBool_3=true)
    )
    or 
    (
      (
        not (
          SListCondition0[freshNode_0])
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
    next_1=(next_0)++((freshNode_0)->(null)))
  and 
  (
    (
      SListCondition2[thiz_0]
      and 
      (
        nullDerefBool_4=true)
    )
    or 
    (
      (
        not (
          SListCondition2[thiz_0])
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
      SListCondition8[head_0,
                     thiz_0]
      and 
      (
        (
          SListCondition2[thiz_0]
          and 
          (
            nullDerefBool_17=true)
        )
        or 
        (
          (
            not (
              SListCondition2[thiz_0])
          )
          and 
          TruePred[]
          and 
          (
            nullDerefBool_4=nullDerefBool_17)
        )
      )
      and 
      (
        head_1=(head_0)++((thiz_0)->(freshNode_0)))
      and 
      (
        next_1=next_2)
      and 
      (
        current_0=current_11)
    )
    or 
    (
      (
        not (
          SListCondition8[head_0,
                         thiz_0]
        )
      )
      and 
      TruePred[]
      and 
      (
        (
          SListCondition2[thiz_0]
          and 
          (
            nullDerefBool_5=true)
        )
        or 
        (
          (
            not (
              SListCondition2[thiz_0])
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
        current_1=thiz_0.head_0)
      and 
      (
        (
          SListCondition4[current_1]
          and 
          (
            nullDerefBool_6=true)
        )
        or 
        (
          (
            not (
              SListCondition4[current_1])
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
          SListCondition6[current_1,
                         next_1]
          and 
          (
            (
              SListCondition4[current_1]
              and 
              (
                nullDerefBool_7=true)
            )
            or 
            (
              (
                not (
                  SListCondition4[current_1])
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
            current_2=current_1.next_1)
        )
        or 
        (
          TruePred[]
          and 
          (
            current_1=current_2)
          and 
          (
            nullDerefBool_6=nullDerefBool_7)
        )
      )
      and 
      (
        (
          SListCondition6[current_2,
                         next_1]
          and 
          (
            (
              SListCondition4[current_2]
              and 
              (
                nullDerefBool_8=true)
            )
            or 
            (
              (
                not (
                  SListCondition4[current_2])
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
            current_3=current_2.next_1)
        )
        or 
        (
          TruePred[]
          and 
          (
            current_2=current_3)
          and 
          (
            nullDerefBool_7=nullDerefBool_8)
        )
      )
      and 
      (
        (
          SListCondition6[current_3,
                         next_1]
          and 
          (
            (
              SListCondition4[current_3]
              and 
              (
                nullDerefBool_9=true)
            )
            or 
            (
              (
                not (
                  SListCondition4[current_3])
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
            current_4=current_3.next_1)
        )
        or 
        (
          TruePred[]
          and 
          (
            current_3=current_4)
          and 
          (
            nullDerefBool_8=nullDerefBool_9)
        )
      )
      and 
      (
        (
          SListCondition6[current_4,
                         next_1]
          and 
          (
            (
              SListCondition4[current_4]
              and 
              (
                nullDerefBool_10=true)
            )
            or 
            (
              (
                not (
                  SListCondition4[current_4])
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
            current_5=current_4.next_1)
        )
        or 
        (
          TruePred[]
          and 
          (
            current_4=current_5)
          and 
          (
            nullDerefBool_9=nullDerefBool_10)
        )
      )
      and 
      (
        (
          SListCondition6[current_5,
                         next_1]
          and 
          (
            (
              SListCondition4[current_5]
              and 
              (
                nullDerefBool_11=true)
            )
            or 
            (
              (
                not (
                  SListCondition4[current_5])
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
            current_6=current_5.next_1)
        )
        or 
        (
          TruePred[]
          and 
          (
            current_5=current_6)
          and 
          (
            nullDerefBool_10=nullDerefBool_11)
        )
      )
      and 
      (
        (
          SListCondition6[current_6,
                         next_1]
          and 
          (
            (
              SListCondition4[current_6]
              and 
              (
                nullDerefBool_12=true)
            )
            or 
            (
              (
                not (
                  SListCondition4[current_6])
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
            current_7=current_6.next_1)
        )
        or 
        (
          TruePred[]
          and 
          (
            current_6=current_7)
          and 
          (
            nullDerefBool_11=nullDerefBool_12)
        )
      )
      and 
      (
        (
          SListCondition6[current_7,
                         next_1]
          and 
          (
            (
              SListCondition4[current_7]
              and 
              (
                nullDerefBool_13=true)
            )
            or 
            (
              (
                not (
                  SListCondition4[current_7])
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
            current_8=current_7.next_1)
        )
        or 
        (
          TruePred[]
          and 
          (
            current_7=current_8)
          and 
          (
            nullDerefBool_12=nullDerefBool_13)
        )
      )
      and 
      (
        (
          SListCondition6[current_8,
                         next_1]
          and 
          (
            (
              SListCondition4[current_8]
              and 
              (
                nullDerefBool_14=true)
            )
            or 
            (
              (
                not (
                  SListCondition4[current_8])
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
            current_9=current_8.next_1)
        )
        or 
        (
          TruePred[]
          and 
          (
            current_8=current_9)
          and 
          (
            nullDerefBool_13=nullDerefBool_14)
        )
      )
      and 
      (
        (
          SListCondition6[current_9,
                         next_1]
          and 
          (
            (
              SListCondition4[current_9]
              and 
              (
                nullDerefBool_15=true)
            )
            or 
            (
              (
                not (
                  SListCondition4[current_9])
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
            current_10=current_9.next_1)
        )
        or 
        (
          TruePred[]
          and 
          (
            current_9=current_10)
          and 
          (
            nullDerefBool_14=nullDerefBool_15)
        )
      )
      and 
      (
        (
          SListCondition6[current_10,
                         next_1]
          and 
          (
            (
              SListCondition4[current_10]
              and 
              (
                nullDerefBool_16=true)
            )
            or 
            (
              (
                not (
                  SListCondition4[current_10])
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
            current_11=current_10.next_1)
        )
        or 
        (
          TruePred[]
          and 
          (
            current_10=current_11)
          and 
          (
            nullDerefBool_15=nullDerefBool_16)
        )
      )
      and 
      SListCondition7[current_11,
                     next_1]
      and 
      (
        (
          SListCondition4[current_11]
          and 
          (
            nullDerefBool_17=true)
        )
        or 
        (
          (
            not (
              SListCondition4[current_11])
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
        next_2=(next_1)++((current_11)->(freshNode_0)))
      and 
      (
        head_0=head_1)
    )
  )
  and 
  (
    (
      SListCondition10[nullDerefBool_17,
                      throw_1]
      and 
      (
        throw_2=NullPointerExceptionLit)
    )
    or 
    (
      (
        not (
          SListCondition10[nullDerefBool_17,
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
  data_0: Data + null,
  freshNode_0: SNode + null,
  head_0: ( SList ) -> one ( SNode + null ),
  head_1: ( SList ) -> one ( SNode + null ),
  l0_current_0: SNode + null,
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
  l0_nullDerefBool_1: boolean,
  l0_nullDerefBool_10: boolean,
  l0_nullDerefBool_11: boolean,
  l0_nullDerefBool_12: boolean,
  l0_nullDerefBool_13: boolean,
  l0_nullDerefBool_14: boolean,
  l0_nullDerefBool_15: boolean,
  l0_nullDerefBool_16: boolean,
  l0_nullDerefBool_17: boolean,
  l0_nullDerefBool_2: boolean,
  l0_nullDerefBool_3: boolean,
  l0_nullDerefBool_4: boolean,
  l0_nullDerefBool_5: boolean,
  l0_nullDerefBool_6: boolean,
  l0_nullDerefBool_7: boolean,
  l0_nullDerefBool_8: boolean,
  l0_nullDerefBool_9: boolean,
  myseq_0: ( SList ) -> ( seq ( null + Object ) ),
  myseq_1: ( SList ) -> ( seq ( null + Object ) ),
  bnext_0,fnext_0: ( SNode ) -> lone ( SNode + null ),
  next_1: ( SNode ) -> one ( SNode + null ),
  next_2: ( SNode ) -> one ( SNode + null ),
  nodeValue_0: ( SNode ) -> one ( Data + null ),
  nodeValue_1: ( SNode ) -> one ( Data + null ),
  thiz_0: SList,
  throw_1: Throwable + null,
  throw_2: Throwable + null
}


fact {
  precondition_SList_insertBack_0[QF.freshNode_0,
                                 QF.head_0,
                                 QF.myseq_0,
                                 (QF.fnext_0+QF.bnext_0),
                                 QF.thiz_0]

}

fact {
  SList_insertBack_0[QF.thiz_0,
                    QF.throw_1,
                    QF.throw_2,
                    QF.data_0,
                    QF.freshNode_0,
                    QF.head_0,
                    QF.head_1,
                    (QF.fnext_0+QF.bnext_0),
                    QF.next_1,
                    QF.next_2,
                    QF.nodeValue_0,
                    QF.nodeValue_1,
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
                    QF.l0_current_0,
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

fact {
  havocVariable3[QF.myseq_1]
}

fact {
  SListCondition12[QF.head_1,
                  QF.myseq_1,
                  QF.next_2,
                  QF.thiz_0]

}

assert SList_m2{
  postcondition_SList_insertBack_0[QF.freshNode_0,
                                  QF.head_1,
                                  QF.myseq_0,
                                  QF.myseq_1,
                                  QF.next_2,
                                  QF.thiz_0,
                                  QF.thiz_0,
                                  QF.throw_2]
}
check SList_m2 for 0 but 
                 exactly 1 SList, 
                 exactly 15 Data,
                 exactly 15 SNode,
                 15 seq, 
                 5 int  



one sig N0,N1,N2,N3,N4,N5,N6,N7,N8,N9,N10,N11,N12,N13,N14 extends SNode {}
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
//fact orderingAxiom1 
fact { 
let entry=(QF.thiz_0).(QF.head_0),ff1=QF.fnext_0,bf1=QF.bnext_0 | { 
-- forwardPlusBackwardAreFunctions
no ((ff1.univ) & (bf1.univ)) 
N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14 = ff1.univ + bf1.univ 
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
} 
//fact root_node_fields 
fact { 
} 
