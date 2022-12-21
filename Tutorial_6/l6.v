

Require Import ssreflect.
Lemma div2 : forall n, exists p,
        n = p+p \/ n = (S (p+p)).
induction n.
- exists 0.
  left.
  reflexivity.
- move: IHn => [p hp].
  case: hp => [hp|hp].
  exists p.
  right.
  rewrite hp.
  done.
- exists (S p).
  left.
  simpl.
  rewrite PeanoNat.Nat.add_succ_r.
  rewrite -hp.
done.
Defined.

Eval compute in (div2 4).
Eval compute in (div2 7).

