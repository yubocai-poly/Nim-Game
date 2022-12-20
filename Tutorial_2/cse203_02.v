(* -------------------------------------------------------------------- *)
Require Import ssreflect.

(* Predicates                                                           *)
(* ==================================================================== *)

Lemma p1 (P : nat -> Prop) (n : nat) : P n ->  P n.
Proof. 
move => pn.
apply pn.
Qed.


(* Quantifiers                                                          *)
(* ==================================================================== *)

Parameter P : nat -> Prop.
Parameter Q : nat -> Prop.

Axiom PQ : forall n, P n -> Q n.

Lemma q1 : (P 3) -> exists x, Q x.
Proof. 
move => p3.
exists 3.
apply PQ.
apply p3.
Qed.


Lemma q1' : (exists x, P x) -> exists x, Q x.
Proof.
move => ex.
case ex.
move => x px.
exists x.
apply PQ.
apply px.
Qed. 


Lemma q2 : ~(exists x, P x) -> forall x, ~P x.
Proof. 
move => nex x px.
apply nex.
exists x.
apply px.
Qed.


(* Here you may want to use the tactic  apply ... with ... *)
Lemma q3 : (forall x, ~P x) -> ~(exists x, P x).
Proof.
move => px. move => ex.
move: ex => [x px'].
apply (px x). apply px'.
Qed.

(* Here you may want to use the tactic  apply ... with ... *)


Lemma q4 (R : nat -> nat -> Prop) :
  (exists x, forall y, R x y) -> (forall y, exists x, R x y).
  Proof. 
  move => ex. move => y. 
  case ex. move => x rx.
  exists x. apply rx.
  Qed.

(* Leibniz equality                                                     *)
(* ==================================================================== *)

Definition Leibniz (T:Type) (x : T) :=
  fun y => forall P : T->Prop, (P y) -> (P x).


Lemma Lte : forall T x y, Leibniz T x y -> x = y.
Proof. 
move => T x y lei.
apply lei.
reflexivity.
Qed.

Lemma etL : forall T x y, x = y -> Leibniz T x y.
Proof. 
move => T x y eq P py.
rewrite eq. apply py.
Qed.

(* Do the following ones without using the two previous lemmas          *)
Lemma L_sym : forall T x y, Leibniz T x y -> Leibniz T y x.
Proof. 
move => T x y lei P.
apply lei.
move => py.
apply py.
Qed.


Lemma L_trans : forall T x y z,
  Leibniz  T x y -> Leibniz T y z ->  Leibniz T x z.
Proof. 
move => T x y z.
move => lei1.
move => lei2.
apply lei1.
apply lei2.
Qed.

(* Using negation                                                       *)
(* ==================================================================== *)
Lemma ex_neg :forall A B : Prop, A -> ~A -> B.
Proof.
move => A B a na.

(* The following command eliminates the False in 'na' and then asks to  *)
(* prove the assumption A left of the -> in ~A                          *)
case na.

assumption.
Qed.


(* Classical reasonning                                                 *)
(* ==================================================================== *)

(* By default, in Coq, one does not have the principle that any         *)
(* proposition is either true or false (the excluded middle).  We will  *)
(* come back to the reason behind this surprising fact in later         *)
(* lessons. But it is possible to assume the excluded middle as an      *)
(* axiom.                                                               *)

(* Here we start by assuming another classical axiom                    *)
Axiom DNE : forall A : Prop, ~(~A) -> A.

(* Show this axiom entails the excluded middle:                         *)
(* Difficulty: HARD                                                     *)
Lemma excluded_middle : forall A:Prop, A \/ ~A.
Proof.
move => A. apply DNE.
move => na.
apply na.
right. move => a. apply na.
left. apply a.
Qed.


Lemma cl1 : exists x, (exists y, P y) -> P x. 
Proof.
(* See here how one can use the excluded_middle "lemma" by              *)
(* instantiating the universally quantified variable A                  *)
move: (excluded_middle (exists x, P x)).

(* now finish the proof                                                 *)
move => ex. case ex.
move => ex1. move: ex1 => [x px]. exists x. move => py. apply px.
move => nex. exists 0. move => py. case nex. move: py => [y py]. exists y. apply py. 
Qed.

(* The following lemma is known as the "drinker's paradox": In any      *)
(*pub, there is one person x such that, if that person drinks, the      *)
(*everybody in the pub also drinks                                      *)

(* Formally, it is a slightly more complicated variant of the previous  *)
(* lemma.                                                               *)
(* Difficulty: HARD                                                     *)
Lemma drinker_paradox (P : nat -> Prop) :
  exists x : nat, forall y : nat, P x -> P y.
Proof. 
move: (excluded_middle (exists x, ~(P x))).
move => p.
case p.
move => [x npx].
exists x.
move => y.
move => px.
case npx.
apply px.
move => npx.
exists 0.
move => y.
move => P0.
move: (excluded_middle (P y)).
move => py2.
case: py2.
move => py.
apply py.
move => npy.
case npx.
exists y.
apply npy.
Qed.


