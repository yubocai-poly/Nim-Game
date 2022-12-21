(* Functional Programming *)

From mathcomp Require Import all_ssreflect.



(* Some remarks or helps about the current assignment including :
 - the done tactic and the by tactical
 - the use of elim instead of induction
 *)


 Lemma le_trans : forall n m p,
 n <= m ->  m <= p ->  n <= p.
Proof.
(* first we can try this 
induction n; move => [ | m][ | p]; simpl.

we see that many goals are trivial...

one can also put /= after an intro-pattern to force simpl
or //= to force simpl+trivial+discriminate
*)

(* Here we use elim instead of induction; n is either 0 or
S n, followed by the indcution hypothesis for n (hn) 
elim => [| n hn][| m][| p].


Combining these techniques can give a two-line proof.

*)
elim => [| n hn][| m][| p]//= h1 h2.
 apply hn with m; done.
Qed.

(* or :
elim => [| n hn][| m][| p]//= h1 h2.
 apply hn with m; done. *)

Lemma le_antisym : forall n m, n <= m -> m <= n -> n = m.
(* is similar *)
elim => [| n hn][| m]//= h1 h2.
by rewrite (hn m).
Qed.

(* Lemma leP: forall n m, n <= m -> exists p, m = n + p. *)
(* I had some questions about this lemma after the course.
I suggest you try to do it, but you should not feel too bad if you do
ot manage to do it. Have a look at the correction on Monday though. *)


(* Lists *)

Inductive list : Type :=
| nil  : list
| cons : nat -> list -> list.

(* example of a function over lists *)
Fixpoint suml l :=
  match l with
  | nil => 0
  | cons n l => n + (suml l)
  end.

Definition l123 :=
  (cons 1 (cons 2 (cons 3 nil))).

Eval compute in (suml l123).

Print l123.


(* We define a function for concatenating lists *)
Fixpoint cat (l1 l2 : list) : list :=
  match l1 with
  | nil       => l2
  | cons x tl => cons x (cat tl l2)
  end.
  (* Note that this function is very similar to the addition function
  for nat *)


Lemma cat0s : forall (l : list), cat nil l = l.
Proof.
 move => l; simpl; trivial.
Qed.


Lemma cats0 : forall (l : list), cat l nil = l.
Proof.
  elim => [ | n l Hl].
  (* you can finish *)
Abort.


Lemma cat_ass : forall l1 l2 l3,
    cat l1 (cat l2 l3) = cat (cat l1 l2) l3.
elim => [| n1 l1 hl1] l2 l3.
  simpl.
  reflexivity.
simpl.
rewrite hl1.
reflexivity.

(* or shorter : *)
Restart.
elim => [| n1 l1 hl1] l2 l3 //=.
by rewrite hl1.
Qed.


Lemma suml_cat :
  forall l1 l2,
    suml (cat l1 l2) = suml l1 + suml l2.
 elim => [| n1 l1 hl1]l2 //=.
rewrite hl1.

 Search associative.

rewrite addnA.
done.
Qed.

(* Example of an even more complicated datatype *)


Inductive tree : Type :=
| Leaf
| Node : nat -> tree -> tree -> tree.


Fixpoint tree_sum 
