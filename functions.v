(* assumption *)
Theorem p_implies_p : forall P : Prop,
  P -> P.
Proof.
  intros P P_holds.
  assumption.
Qed.

(* apply *)
Theorem modus_ponens : forall (P Q : Prop),
  (P -> Q) -> P -> Q.
Proof.
  intros P Q P_implies_Q P_holds.
  apply P_implies_Q in P_holds.
  assumption.
Qed.


  