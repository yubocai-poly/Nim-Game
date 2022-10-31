From mathcomp Require Import ssreflect.


Parameter A B C D : Prop.

Check (A->(A\/B)).

Lemma l1 : A -> A.
  move => a.
  exact a.
Qed.

Check l1.

Lemma l2 : A -> (B -> A).
  move => a.
  move => b.
  exact a.
Qed.

Lemma l3 : B -> A -> A.
  move => b.
  move => a.
  exact a.
Qed.


Lemma l4 : (A -> B) -> (B -> C) -> A -> C.
move => ab.
move => bc.
move => a.

apply bc.

apply ab.
exact a.
Qed.


(* an example with conjucntion *)
Lemma l5 : A/\B -> B/\A.
move => [a b].
split.
- exact b.
- exact a.
Qed.


(* Not done in the lecture,  examples
with disjunction *)

Lemma l6 : A -> A\/B.
  move => a.
  left.
  exact a.
Qed.

  
Lemma l7 : B -> A\/B.
  move => b.
  right.
  exact b.
Qed.

    
Lemma l8 : B\/A -> A\/B.
  move => [b | a].
  - right.
    exact b.
  - left.
    exact a.
Qed.

