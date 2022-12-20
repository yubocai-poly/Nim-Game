Require Import ssreflect.

Inductive color :=
  | blue
  | red.

Definition inv (c : color) :=
  match c with
  | red => blue
  | blue => red
  end.

Eval compute in (inv (inv red)).

(* various versions *)
Lemma inv_conv : forall x, inv (inv x) = x.
move => x.
case: x.
- simpl.
  reflexivity.
- reflexivity.
Restart.
  move => x.
  case x; reflexivity.  
Restart.
move => [ | ]; reflexivity.
Qed.

Check true.
(* ===> true : bool *)

  Inductive opt_nat :=
  None
| Some : nat -> opt_nat.

Definition opt_add :=
  fun (n : opt_nat) (m : opt_nat) =>
     match n, m with
     | Some a, Some b => Some (a+b)
     | _ , _ => None
     end.

(* This two a equal
Definition add_opt n m :=
 match n, m with
 | Some a, Some b => Some (a+b)
 | None, Some _ => None
 | Some _, None => None
 | None, None => None
 end.
*)

Eval compute in (opt_add (Some 2)(Some 3)).

Eval compute in (opt_add (Some 2) None).

Definition pred n :=
  match n with
    O => O
  | S m => m
  end.

Eval compute in (pred (pred 6)).

Eval compute in (pred 0).

Eval compute in (pred 5).

Eval compute in (S 3).

Eval compute in (S (pred 3)).

(* The following function prove that if the pred of x plus 1 is iteself then it's 0 *)
Lemma pred_corr :
  forall x, S (pred x) = x \/ x = 0.
move => x.
case: x.
- simpl.
  right; reflexivity.
- move => x.
  simpl.
  left; reflexivity.
Restart.
move => [ | y].
- right; reflexivity.
- left; reflexivity.
Qed.

Fixpoint plus n m :=
  match n with
  | O => m
  | S p => S (plus p m)
  end.

Eval compute in (plus 2 2).
Eval compute in (plus (S O) (S O)).
Lemma dpd : (plus 2 2) = 4.
reflexivity.
Qed.


Lemma l1 : forall x, plus 0 x = x.
move => x.
reflexivity.
Qed.

Lemma l2 : forall x, plus x 0 = x.
  move => x.
  simpl.
  induction x.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHx.
    reflexivity.    
Qed.

Fixpoint double (n : nat) :=
 match n with
 | O => O
 | S m => S (S (double m))
end.

Eval compute in (double 3).


(* Proof by intduction *)
Theorem add_0_r_secondtry : forall n:nat,
  n + 0 = n.
Proof.
  intros n. destruct n as [| n'] eqn:E.
  - (* n = 0 *)
    reflexivity. (* so far so good... *)
  - (* n = S n' *)
    simpl. (* ...but here we are stuck again *)
Abort.

(* Since for n is an unknown number then therefore we need proof by induction *)
Theorem add_0_r : forall n:nat, n + 0 = n.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *) reflexivity.
  - (* n = S n' *) simpl. rewrite -> IHn'. reflexivity. 
Qed.