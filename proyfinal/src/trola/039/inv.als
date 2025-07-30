//-------------- prelude--------------//
module moduleId
open util/integer
open util/sequniv as sequniv
one sig null {}
fun fun_reach[h: univ, type: set univ, field: univ -> univ ]: set univ {
  h.*(field & type->(type+null)) & type
}
abstract sig boolean {}
one sig true extends boolean {}
one sig false extends boolean {}

pred TruePred[] {}
pred FalsePred[] { not TruePred[] }
pred equ[l,r:univ] {l=r}
pred neq[l,r:univ] {l!=r}


//-------------- amelia_data_D0--------------//
sig D0 extends Data {}
{}

//-------------- amelia_rbtree1_TreeSet--------------//
sig TreeSet extends Object {}
{}

//-------------- amelia_data_D1--------------//
sig D1 extends Data {}
{}

//-------------- amelia_data_D2--------------//
sig D2 extends Data {}
{}

//-------------- java_lang_Throwable--------------//
sig Throwable extends Object {}
{}

//-------------- amelia_rbtree1_TreeSetNode--------------//
sig TreeSetNode extends Object {}
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
sig RuntimeException extends Exception {}
{}
//-------------- java_lang_IndexOutOfBoundException--------------//
sig IndexOutOfBoundsException extends RuntimeException {}
{}
//-------------- java_lang_Exception--------------//
sig Exception extends Throwable {}
{}
//-------------- java_lang_NullPointerException--------------//
sig NullPointerException extends RuntimeException {}
{}
//-------------- amelia_data_Data--------------//
abstract sig Data extends Object {}
{}








one sig QF {
blackHeight_0 :  ( TreeSetNode ) -> one ( Int ) ,
color_0 :  ( TreeSetNode ) -> one ( boolean ) ,
key_0 :  ( TreeSetNode ) -> one ( Data + null ) ,
fleft_0 :  ( TreeSetNode ) -> lone ( TreeSetNode + null ) ,
bleft_0 :  ( TreeSetNode ) -> lone ( TreeSetNode + null ) ,
nextData_0 :  ( Data ) -> one ( Data + null ) ,
parent_0 :  ( TreeSetNode ) -> one ( TreeSetNode + null ) ,
fright_0 :  ( TreeSetNode ) -> lone ( TreeSetNode + null ) ,
bright_0 :  ( TreeSetNode ) -> lone ( TreeSetNode + null ) ,
root_0 :  ( TreeSet ) -> one ( TreeSetNode + null ) ,
thiz_0 :  TreeSet}


fact repOk {
   let RED = false,
       BLACK = true,
       key = QF.key_0,
       blackHeight = QF.blackHeight_0,
       left = QF.fleft_0 +QF.bleft_0,
       right = QF.fright_0+QF.bright_0,
       color = QF.color_0,
       parent = QF.parent_0,
       root = QF.root_0,
       nextData = QF.nextData_0,
       thiz = QF.thiz_0
   | {

RED==false &&
BLACK==true &&
thiz.root.parent in null &&
( thiz.root!=null => thiz.root.color = BLACK ) &&
( all n: TreeSetNode | n in thiz.root.*(left + right + parent) - null => (

/*non_null*/
                                (n.key != null ) &&

/* parent left */
                                ( n.left != null => n.left.parent = n ) &&

/* parent right */
( n.right != null => n.right.parent = n ) &&

/* parent */
( n.parent != null => n in n.parent.(left + right) ) &&

/* form a tree */
( n !in n.^parent ) &&

/* left sorted */
( all x : n.left.^(left + right) + n.left - null | n.key in x.key.^nextData
) &&

/* right sorted */
( all x : n.right.^(left + right) + n.right - null | x.key in
n.key.^nextData ) &&

/* no red node has a red parent */
( n.color = RED && n.parent != null => n.parent.color = BLACK ) &&

/* black height leaf */
( ( n.left=null && n.right=null ) => ( n.blackHeight=1 ) ) &&

/* black height left non null */
( n.left!=null && n.right=null => (
      ( n.left.color = RED ) &&
      ( n.left.blackHeight = 1 ) &&
      ( n.blackHeight = 1 )
)) &&

/* black height right non null */
( n.left=null && n.right!=null =>  (
      ( n.right.color = RED ) &&
      ( n.right.blackHeight = 1 ) &&
      ( n.blackHeight = 1 )
 )) &&

/* inner node (RED/RED) */
( n.left!=null && n.right!=null && n.left.color=RED && n.right.color=RED =>
(
        ( n.left.blackHeight = n.right.blackHeight ) &&
        ( n.blackHeight = n.left.blackHeight )
)) &&

/* inner node (BLACK/BLACK) */
( n.left!=null && n.right!=null && n.left.color=BLACK && n.right.color=BLACK
=> (
        ( n.left.blackHeight=n.right.blackHeight ) &&
        ( n.blackHeight=n.left.blackHeight + 1 )
)) &&

/* inner node (RED/BLACK) */
( n.left!=null && n.right!=null && n.left.color=RED && n.right.color=BLACK
=> (
        ( n.left.blackHeight=n.right.blackHeight + 1 ) &&
        ( n.blackHeight = n.left.blackHeight  )
)) &&

/* inner node (BLACK/RED) */
( n.left!=null && n.right!=null && n.left.color=BLACK && n.right.color=RED
=> (
        ( n.right.blackHeight=n.left.blackHeight + 1 ) &&
        ( n.blackHeight = n.right.blackHeight  )   ))

) )

}}


one sig N0,N1,N2,N3,N4,N5,N6,N7,N8,N9,N10,N11,N12,N13,N14 extends
TreeSetNode {}
//fact ffields_bfields

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
//fact (QF.root_0)_int_fields
fact {
}
fact orderingAxiom2 {
let
entry=(QF.thiz_0).(QF.root_0),ff1=QF.fleft_0,ff2=QF.fright_0,bf1=QF.bleft_0,bf2=QF.bright_0
| {
   -- forwardPlusBackwardAreFunctions
   no ((ff1.univ) & (bf1.univ))
   no ((ff2.univ) & (bf2.univ))
   N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14 = ff1.univ + bf1.univ

   N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14 = ff2.univ + bf2.univ


  --forwardIsIndeedForward
  entry in N0+null and
  (all n : entry.*(ff1 + ff2) - null | (
   min[(ff1).n] in prevs[n]) and (
    min[(ff2).n] in prevs[n])) and
  (all disj n1, n2 : entry.*((ff1) + (ff2)) - null | (
        (    some ((ff1).n1 + (ff2).n1) and
            some ((ff1).n2 + (ff2).n2) and
                min[(ff1).n1 + (ff2).n1] in prevs[min[(ff1).n2 + (ff2).n2]]
             ) implies n1 in this/prevs[n2]
   )
   and
     let a = min[(ff1).n1 + (ff2).n1] |
     let b = min[(ff1).n2 + (ff2).n2] |
     (some ((ff1).n1 + (ff2).n1) and a = b and a.(ff1) = n1 and a.(ff2) =
n2) implies n2 = n1.this/next[]
   )

  --backwardsIsIndeedBackwards
   (bf1 in relprevs) && (bf2 in relprevs)

  --prefixReachableForward
    all x : entry.*(ff1 +ff2) -null | this/prevs[x] in entry.*(ff1 + ff2)

}
}
fun next[]: (N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14) -> lone
(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14)
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
fun prevs[e: N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14] :set
(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14)
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
fun data_prevs[e: D0+D1+D2+D3+D4+D5+D6+D7+D8+D9+D10+D11+D12+D13+D14] : set
(D0+D1+D2+D3+D4+D5+D6+D7+D8+D9+D10+D11+D12+D13+D14)
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
pred data_lt[e1,e2: D0+D1+D2+D3+D4+D5+D6+D7+D8+D9+D10+D11+D12+D13+D14] {
   e1 in data_prevs[e2]
 }
fun rprevs[e: N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14] :set
(N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14)
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
fun relprevs[] :( N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14 ) -> set
( N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14 )
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
fun min [es: set ( N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14 )] :
lone ( N0+N1+N2+N3+N4+N5+N6+N7+N8+N9+N10+N11+N12+N13+N14 )
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

pred notNull[]{(QF.thiz_0).(QF.root_0) != null}
run {notNull[]} for 0 but exactly 1 TreeSet, exactly 1 NullPointerException,
exactly 15 TreeSetNode, exactly 1 D0, exactly 1 D1, exactly 1 D2, exactly 1
D3, exactly 1 D4, exactly 1 D5, exactly 1 D6, exactly 1 D7, exactly 1 D8,
exactly 1 D9, exactly 1 D10, exactly 1 D11, exactly 1 D12, exactly 1 D13,
exactly 1 D14, 5 int

fact{
QF.bright_0 in none->none
QF.bleft_0 in none->none
}

fact {

QF.fleft_0 in N14->null 
+N0->N1 
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


QF.fright_0 in N14->null 
+N0->N1 
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

}
