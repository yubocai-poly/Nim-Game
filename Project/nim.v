(* Author: Yubo CAI, Junyuan WANG *)
(* CSE203 Logic and Proof Final Project *)

(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect.
(* --------------- *) Import Monoid.

(* -------------------------------------------------------------------- *)
Set   Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set   Printing Projections.
Set   Printing Projections.
Unset SsrOldRewriteGoalsOrder.

(* -------------------------------------------------------------------- *)
Notation "[ 'seq' E | i < n ]" := (mkseq (fun i => E) n)
  (at level 0, E at level 99, i name,
   format "[ 'seq'  E  |  i  <  n ]") : seq_scope.

(* ==================================================================== *)
Lemma mkseqS {T : Type} (f : nat -> T) (n : nat) :
  [seq f i | i < n.+1] = rcons [seq f i | i < n] (f n).
Proof.
by rewrite /mkseq -addn1 iotaD map_cat /= add0n cats1.
Qed.

(* ==================================================================== *)
(* Some extras arithmetic lemmas that are needed later                  *)
Lemma sum_pow2 (n : nat) :
  \sum_(i < n) 2^i = (2^n).-1.
Proof.
elim: n => [|n ih]; first by rewrite big_ord0.
rewrite big_ord_recr //= ih [LHS]addnC -subn1.
rewrite addnBA ?expn_gt0 // subn1; congr _.-1.
by rewrite addnn -mul2n -expnS.
Qed.

(* -------------------------------------------------------------------- *)
Lemma modn2_neq0 (n : nat) : (n %% 2 != 0) = n %% 2 :> nat.
Proof. by rewrite modn2 eqb0 negbK. Qed.

(* -------------------------------------------------------------------- *)
Lemma divnE (n : nat) (p : nat) (k : nat) :
  p != 0 -> k * p <= n < k.+1 * p -> n %/ p = k.
Proof.
move=> nz_p; elim: k n => [|k ih] n.
- by rewrite !simpm => lt; rewrite divn_small.
rewrite [X in X <= _]mulSn [X in _ < X]mulSn => rg; have le_pn: p <= n.
- by case/andP: rg => [+ _] => /(leq_trans _); apply; apply/leq_addr.
move: rg; rewrite -leq_subRL // -ltn_subLR //.
move/ih => <-; rewrite -{1}[n](subnK le_pn) divnDr //.
by rewrite divnn lt0n nz_p addn1.
Qed.

(* -------------------------------------------------------------------- *)
Lemma divn_sumr {I : Type} (P : pred I) (F : I -> nat) (r : seq I) (d : nat) :
  (forall i, P i -> d %| F i) ->
    (\sum_(i <- r | P i) F i) %/ d = \sum_(i <- r | P i) (F i) %/ d.
Proof.
move=> hdvd; elim/big_rec2: _ => //=; first by rewrite div0n.
by move=> i _ n Pi <-; rewrite divnDl ?hdvd.
Qed.

(* ==================================================================== *)
(* We define the discrete logarithm in base 2.                          *)
(*                                                                      *)
(*   - log2(n) = the number of bits needed to represent all `n`         *)
(*               differents values or the range [0..n[                  *)

Definition log2 (n : nat) := trunc_log 2 n.

Lemma log2_0 : log2 0 = 0.
Proof. exact: trunc_log0. Qed.

Lemma log2_1 : log2 1 = 0.
Proof. exact: trunc_log1. Qed.

Lemma log2_expnK n : log2 (2 ^ n) = n.
Proof. exact: trunc_expnK. Qed.

Lemma log2_eq n k : 2 ^ n <= k < 2 ^ n.+1 -> log2 k = n.
Proof. exact: trunc_log_eq. Qed.

Lemma log2_homo : {homo log2 : m n / m <= n}.
Proof. exact: leq_trunc_log. Qed.

Lemma log2_double (n : nat) : 0 < n -> log2 n.*2 = (log2 n).+1.
Proof. exact: trunc_log2_double. Qed.

Lemma log2S (n : nat) : 1 < n -> log2 n = (log2 n./2).+1.
Proof. exact: trunc_log2S. Qed.

Lemma log2_eq0 (n : nat) : (log2 n == 0) = (n < 2).
Proof. by rewrite trunc_log_eq0 /= ltnS. Qed.

Lemma log2_lt2 (n : nat) : n < 2 -> log2 n = 0.
Proof. by rewrite -log2_eq0 => /eqP. Qed.

Lemma log2_ltn (n : nat) : n < 2 ^ (log2 n).+1.
Proof. exact: trunc_log_ltn. Qed.

Lemma log2_bounds (n : nat) : n != 0 -> 2 ^ (log2 n) <= n < 2 ^ (log2 n).+1.
Proof.
by move=> nz_n; apply: (@trunc_log_bounds 2 n) => //; rewrite lt0n.
Qed.

(* ==================================================================== *)
(* We provide a library for bit-vectors. A bit-vector is any sequence   *)
(* of booleans whose last element is not `false`.                       *)

Record bits := Bitseq { bitseq :> seq bool; _ : last true bitseq; }.

Canonical  bits_subType := Eval hnf in [subType for bitseq].
Definition bits_eqMixin := Eval hnf in [eqMixin of bits by <:].
Canonical  bits_eqType  := Eval hnf in EqType bits bits_eqMixin.

Lemma bits_inj : injective bitseq.
Proof. exact: val_inj. Qed.

(* -------------------------------------------------------------------- *)
(* The notation `b.[i]` allows to access the `i`-th bit of a bit-       *)
(* vector `b`. The bit-vector is implicitly padded with a infinite      *)
(* sequence of `false`.                                                 *)

Definition bit i (b : seq bool) := nosimpl (nth false b i).

Notation "b .[ i ]" := (bit i b).

Lemma bit_oversize (b : bits) (i : nat) :
  size b <= i -> b.[i] = false.
Proof. by case: b => /= b _ lti; rewrite /bit nth_default. Qed.

(* -------------------------------------------------------------------- *)
(* We now prove that for any sequence `s` of booleans, there exists a   *)
(* bit-vector `t` with the same bits (once padded with an infinite      *)
(* sequence of `false`), i.e. `t` is `s` with the final `false`         *)
(* elements trimed.                                                     *)

Lemma bits_canon_spec (s : seq bool) :
  { t : seq bool |
        forall i, nth false s i = nth false t i
      & last true t }.
Proof.
elim/last_ind: s => [|s [] ih]; first by exists [::].
- by exists (rcons s true) => //; rewrite last_rcons.
case: ih => bs h1 h2; exists bs => //.
move=> i; rewrite nth_rcons; case: ltnP => // le.
rewrite if_same; apply/esym; case: (ltnP i (size bs)); last first.
- by move=> ?; rewrite nth_default.
move/(leq_ltn_trans le) => {le} lt; absurd false => //.
move: h2; rewrite (last_nth false) -[size bs]prednK //=.
- by apply: (leq_ltn_trans _ lt).
rewrite -h1 nth_default // -ltnS prednK //.
by apply: (leq_ltn_trans _ lt).
Qed.

(* -------------------------------------------------------------------- *)
(* The function `mkbits` allows the creation of a bit-vector from a     *)
(* given sequence of booleans.                                          *)

Definition mkbits_def (s : seq bool) :=
  Bitseq (s2valP' (bits_canon_spec s)).

Fact mkbits_key : unit.
Proof. by []. Qed.

Definition mkbits := locked_with mkbits_key mkbits_def.
Canonical mkbits_unlockable := [unlockable fun mkbits].

(* -------------------------------------------------------------------- *)
Lemma mkbitsE (s : seq bool) (i : nat) : (mkbits s).[i] = s.[i].
Proof. by rewrite unlock; move: (s2valP (bits_canon_spec s) i). Qed.

(* -------------------------------------------------------------------- *)
Lemma size_mkbits_le (s : seq bool) :
  size (mkbits s) <= size s.
Proof.
rewrite leqNgt; apply/negP => lt.
have := mkbitsE s (size (mkbits s)).-1; rewrite [X in _ = X]nth_default.
- by rewrite -ltnS prednK // (leq_ltn_trans _ lt).
rewrite /bit (@set_nth_default _ _ true) ?prednK //.
- by apply: (leq_ltn_trans _ lt).
by rewrite nth_last unlock (s2valP' (bits_canon_spec s)).
Qed.

(* -------------------------------------------------------------------- *)
Lemma mkbitsK (s : seq bool) : last true s -> mkbits s = s :> seq _.
Proof.
move=> h; apply: (@eq_from_nth _ false); last first.
- by move=> i lti; apply: mkbitsE.
have := size_mkbits_le s; rewrite leq_eqVlt => /orP[/eqP //|lt].
absurd (last true s) => //; rewrite -nth_last.
rewrite (@set_nth_default _ _ false).
- by rewrite prednK // (leq_ltn_trans _ lt).
rewrite -/(bit _ _) -mkbitsE /bit nth_default //.
by rewrite -ltnS prednK // (leq_ltn_trans _ lt).
Qed.

(* -------------------------------------------------------------------- *)
(* Two bit-vectors are equal (i.e. represented by the same sequence)    *)
(* iff they have the same bits (once padded with an infinite sequence   *)
(* of `false`.                                                          *)

Lemma bits_eqP (b1 b2 : bits) :
  reflect (forall i, b1.[i] = b2.[i]) (b1 == b2).
Proof.
apply: (iffP eqP) => [->//|].
case: b1 b2 => [b1 h1] [b2 h2] /= eq_bits.
apply/val_eqP/eqP => /=; apply: (@eq_from_nth _ false); last first.
- by move=> i _; apply: eq_bits.
wlog: b1 h1 b2 h2 eq_bits / (size b1 <= size b2) => [wlog|].
- case: (leqP (size b1) (size b2)); first by apply: wlog.
  by move/ltnW => le; apply/esym/wlog.
rewrite leq_eqVlt => /orP[/eqP //|lt_sz].
absurd false => //; move/(_ (size b2).-1): eq_bits.
rewrite [X in _ = X]/bit (set_nth_default true).
- by rewrite ltn_predL (leq_ltn_trans _ lt_sz).
rewrite nth_last h2 -/(is_true _) /bit nth_default //.
by rewrite -ltnS prednK // (leq_ltn_trans _ lt_sz).
Qed.

Lemma bits_eqW (b1 b2 : bits) :
  (forall i, b1.[i] = b2.[i]) <-> (b1 = b2).
Proof. by rewrite (rwP eqP); split=> /bits_eqP. Qed.

(* -------------------------------------------------------------------- *)
(* The empty bit-vector and some related lemmas.                        *)

Definition bits0 := mkbits [::].

Notation "0%:B" := bits0 (at level 0).

Lemma b0E (i : nat) : 0%:B.[i] = false.
Proof. by rewrite mkbitsE /bit nth_nil. Qed.

Lemma val_b0E : val 0%:B = [::].
Proof. by rewrite /mkbits /= mkbitsK. Qed.

Lemma size_b0 : size 0%:B = 0.
Proof. by rewrite val_b0E. Qed.

(* -------------------------------------------------------------------- *)
Lemma size_bits_eq0P (b : bits) :
  (size b == 0) = (b == 0%:B).
Proof. by rewrite -val_eqE /= val_b0E size_eq0. Qed.

(* -------------------------------------------------------------------- *)
Lemma bits_neq0P (b : bits) :
  reflect (exists i, b.[i]) (b != 0%:B).
Proof.
apply: (iffP idP); last first.
- by case=> i nz_bi; apply/contraL: nz_bi => /eqP->; rewrite b0E.
case: b => b hb /=; rewrite -size_bits_eq0P /= => nz_szb.
move: hb; rewrite (last_nth false) -[size b]prednK ?lt0n //=.
by move: _.-1 => i h; exists i.
Qed.

(* -------------------------------------------------------------------- *)
Lemma bits_neq0W (b : bits) : (exists i, b.[i]) <-> (b <> 0%:B).
Proof. by split=> [|/eqP] /bits_neq0P => // /eqP. Qed.

(* -------------------------------------------------------------------- *)
Lemma hibit_neq0P (b : bits) : (b != 0%:B) = b.[(size b).-1].
Proof.
rewrite -size_bits_eq0P; case: b => /= b hb.
by rewrite /bit nth_last; case: b hb.
Qed.

(* -------------------------------------------------------------------- *)
Lemma hibit_neq0W (b : bits) : (b <> 0%:B) <-> b.[(size b).-1].
Proof. by rewrite -hibit_neq0P; split=> /eqP. Qed.

(* -------------------------------------------------------------------- *)
(* The bitwise xor (eXclusive OR) of two bit-vectors                    *)

Definition bxor (b1 b2 : bits) : bits :=
  mkbits [seq b1.[i] (+) b2.[i] | i < maxn (size b1) (size b2)].

Lemma bxorE (b1 b2 : bits) (i : nat) :
  (bxor b1 b2).[i] = b1.[i] (+) b2.[i].
Proof.
rewrite mkbitsE /=; case: (ltnP i (maxn (size b1) (size b2))) => [lt|ge].
- by rewrite /bit nth_mkseq.
rewrite /bit !nth_default ?size_mkseq //;
  by move: ge; rewrite geq_max => /andP[].
Qed.

(* -------------------------------------------------------------------- *)
(* We prove that the set of bitvectors, with 0%:B and (.+), forms a     *)
(* commutative monoid.                                                  *)

Lemma bxor0b : left_id 0%:B bxor.
Proof.
by move=> b; apply/eqP/bits_eqP => i; rewrite !(bxorE, b0E) addFb.
Qed.

Lemma bxorC : commutative bxor.
Proof.
by move=> b1 b2; apply/eqP/bits_eqP => i; rewrite !bxorE addbC.
Qed.

Lemma bxorA : associative bxor.
Proof.
by move=> b1 b2 b3; apply/eqP/bits_eqP => i; rewrite !bxorE addbA.
Qed.

Lemma bxorb0 : right_id 0%:B bxor.
Proof. by move=> b; rewrite bxorC bxor0b. Qed.

Lemma bxorbb : self_inverse 0%:B bxor.
Proof.
by  move=> b; apply/eqP/bits_eqP => i; rewrite bxorE b0E addbb.
Qed.

Notation "b1 .+ b2" := (bxor b1 b2) (at level 50, left associativity).

Canonical bxor_monoid := Monoid.Law bxorA bxor0b bxorb0.
Canonical bxor_comoid := Monoid.ComLaw bxorC.

(* -------------------------------------------------------------------- *)
Lemma bigxorE {I : Type} (P : pred I) (F : I -> bits) (r : seq I) (i : nat) :
    (\big[bxor/0%:B]_(x <- r | P x) F x).[i]
  = \big[addb/false]_(x <- r | P x) (F x).[i].
Proof.
elim/big_ind2: _ => //; first by rewrite b0E.
by move=> _ bs _ cs <- <-; rewrite bxorE.
Qed.

(* ==================================================================== *)
(* We now define functions from converting from bit-vectors to natural  *)
(* numbers, following the 1-complement convention.                      *)
(*                                                                      *)
(* We prove that b2n / n2b are the inverse of each other, along with    *)
(* some more basic properties.                                          *)

Definition b2n (b : bits) : nat :=
  \sum_(i < size b) 2^i * b.[i].

Definition n2b (n : nat) : bits :=
  mkbits [seq (n %/ (2 ^ i)) %% 2 != 0 | i < (log2 n).+1].

(* -------------------------------------------------------------------- *)
Lemma b2nWE (n : nat) (b : bits) :
  size b <= n -> b2n b = \sum_(i < n) 2^i * b.[i].
Proof.
pose F i := 2^i * b.[i]; move=> le; rewrite /b2n.
rewrite (big_ord_widen n F) // big_mkcond /=.
apply: eq_bigr; case=> /= i lti _; rewrite {}/F.
by case: ltnP => // gei; rewrite /bit nth_default ?simpm.
Qed.

(* -------------------------------------------------------------------- *)
Lemma n2b0 : n2b 0 = 0%:B.
Proof. 
apply/eqP/bits_eqP => i; rewrite b0E /n2b mkbitsE.
rewrite log2_0 -(@eq_mkseq _ (fun=> false)) //.
- by move=> j /=; rewrite div0n mod0n eqxx.
case: (ltnP i 1) => ?; first by rewrite /bit nth_mkseq.
by rewrite /bit nth_default.
Qed.

(* -------------------------------------------------------------------- *)
Lemma n2bE (n : nat) (i : nat) :
  (n2b n).[i] = ((n %/ 2 ^ i) %% 2 != 0).
Proof.
case: (n =P 0) => [->|/eqP nz_n].
- by rewrite n2b0 b0E div0n mod0n eqxx.
rewrite mkbitsE; case: (ltnP i (log2 n).+1) => [lt|ge].
- by rewrite /bit nth_mkseq.
rewrite /bit nth_default ?size_mkseq //.
apply/esym/negbTE; rewrite negbK divn_small //.
have /andP [_ +] := log2_bounds nz_n.
by move/leq_trans; apply; apply: leq_pexp2l.
Qed.

(* -------------------------------------------------------------------- *)
Lemma size_n2b (i : nat) : i != 0 -> size (n2b i) = (log2 i).+1.
Proof.
move=> nz_i; set d := (log2 i).+1.
suff nz: (n2b i).[d.-1].
- apply/eqP; rewrite /n2b; set s := (X in mkbits X).
  have := size_mkbits_le s; rewrite size_mkseq -/d.  
  rewrite leq_eqVlt => /orP[//|lt]. absurd (n2b i).[d.-1] => //.
  by rewrite bit_oversize.
have := log2_bounds nz_i; rewrite n2bE /d /=.
rewrite -[X in X <= _]mul1n expnS => /divnE -> //.
by rewrite -lt0n expn_gt0.
Qed.

(* -------------------------------------------------------------------- *)
Lemma size_n2b_half (i : nat) :
  size (n2b i./2) = (size (n2b i)).-1.
Proof.
case: i => /= [|i]; first by rewrite n2b0 /= size_b0.
case: i => /= [|i].
- by rewrite n2b0 size_b0 /n2b log2_1 mkbitsK.
by rewrite !size_n2b //= [in RHS]log2S.
Qed.

(* -------------------------------------------------------------------- *)
Lemma b2nE (b : bits) (i : nat) :
  ((b2n b) %/ 2 ^ i) %% 2 = b.[i].
Proof.
pose F (i : nat) := 2 ^ i * b.[i]; rewrite /b2n.
have dvdF (j : nat) : i <= j -> 2 ^ i %| F j.
- by move=> le_ij; rewrite dvdn_mulr // dvdn_exp2l.
case: (ltnP i (size b)) => [lti|gei]; last first.
- rewrite bit_oversize //= divn_small ?mod0n //.
  apply: (@leq_ltn_trans (\sum_(j < size b) 2 ^ j)).
  - apply: leq_sum; case=> /= j ltj _.
    by case: b.[_]; rewrite simpm.
  by rewrite sum_pow2 prednK ?expn_gt0 // leq_pexp2l.
rewrite -(big_mkord xpredT F) (big_cat_nat _ (n := i.+1)) //=.
rewrite divnDr; first rewrite big_nat dvdn_sum //.
- by move=> j /andP[/ltnW + _]; apply: dvdF.
rewrite -[X in (_ + X)](@divnK 2); last rewrite addnC modnMDl.
- rewrite big_nat divn_sumr.
  - by move=> j /andP[/ltnW + _]; apply: dvdF.
  rewrite dvdn_sum // => j /andP[/[dup] lt_ik / ltnW le_ij _].
  rewrite /F mulnC -muln_divA ?dvdn_exp2l //.
  by rewrite dvdn_mull // -expnB // dvdn_exp // subn_gt0.
rewrite big_nat_recr //= divnDr ?dvdn_mulr //.
rewrite mulKn ?expn_gt0 // [X in X+_](_ : _ = 0); last first.
- by rewrite add0n modn_small // ltnS leq_b1.
rewrite divn_small // (@leq_ltn_trans (\sum_(j < i) 2 ^ j)) //.
- rewrite big_mkord; apply: leq_sum => /= -[/= k ltk] _.
  apply/(@leq_trans (2 ^ k))/leq_pexp2l => //.
  by rewrite /F; case: b.[k]; rewrite simpm.
- by rewrite sum_pow2 ltn_predL expn_gt0.
Qed.

(* -------------------------------------------------------------------- *)
Lemma b2nK : cancel b2n n2b.
Proof.
by move=> b; apply/eqP/bits_eqP => i; rewrite n2bE b2nE eqb0 negbK.
Qed.

(* -------------------------------------------------------------------- *)
Lemma n2bK : cancel n2b b2n.
Proof.
suff: forall l, forall i, log2 i = l -> b2n (n2b i) = i.
- by move=> ih i; apply: (ih (log2 i)).
elim=> [|l ih] i logiE.
- rewrite /n2b logiE mkseqS /= expn0 divn1.
  rewrite (b2nWE (size_mkbits_le _)) /=.
  rewrite big_ord_recl /= big_ord0 addn0.
  rewrite expn0 mul1n mkbitsE /bit /= modn2_neq0.
  by rewrite modn_small // -log2_eq0; apply/eqP.
have gt1_n: 1 < i by rewrite ltnNge -ltnS -log2_eq0 logiE.
pose F i k := 2 ^ k * (n2b i).[k].
have gt0_size: 0 < size (n2b i).
- by rewrite lt0n size_n2b //; case: {+}i gt1_n.
rewrite /b2n -(big_mkord predT (F i)) /= -[size _]prednK //.
rewrite big_nat_recl //= {1}/F expn0 mul1n.
rewrite -(eq_big_nat _ _ (F1 := fun j => (F i./2 j) * 2)).
- move=> k rg_k; rewrite /F n2bE modn2_neq0.
  rewrite mulnAC -expnSr; congr (_ * _).
  by rewrite n2bE modn2_neq0 -divn2 -divnMA -expnS.
rewrite -big_distrl /= -size_n2b_half big_mkord -/(b2n _) ih.
- by rewrite log2S // in logiE; case: logiE.
rewrite n2bE expn0 divn1 modn2_neq0.
by rewrite addnC -divn2; apply/esym/divn_eq.
Qed.

(* -------------------------------------------------------------------- *)
Lemma lt_n2b (b1 b2 : bits) :
  (exists2 k,
      (forall i, k < i -> b1.[i] = b2.[i])
    & b1.[k] < b2.[k])
  -> b2n b1 < b2n b2.
Proof.
case=> k eq lt; pose s := maxn (size b1) (size b2).
rewrite !(@b2nWE s) /=; try by rewrite leq_max leqnn simpm.
pose g (b : bits) (i : nat) := 2^i * b.[i].
have [z_b1k nz_b2k] : (~~ b1.[k]) /\ b2.[k].
- by case: b1.[k] b2.[k] lt => [] [].
rewrite -(big_mkord predT (g b1)) -(big_mkord predT (g b2)) /=.
have lek: k < s.
- apply/(@leq_trans (size b2))/leq_maxr.
  apply/contraLR: lt; rewrite -!(leqNgt, ltnNge).
  by move/bit_oversize => ->.
rewrite [X in X<_](big_cat_nat _ (n := k.+1)) //=.
rewrite [X in _<X](big_cat_nat _ (n := k.+1)) //=.
rewrite -!addSn; apply: leq_add; last first.
- rewrite leq_eqVlt -(rwP orP) /g; left; apply/eqP.
  by apply/eq_big_nat => i /andP[+ _] => /eq ->.
rewrite !big_nat_recr //= {2 4}/g.
rewrite (negbTE z_b1k) nz_b2k ?simpm.
apply: (@leq_trans (2 ^ k)); last by apply: leq_addl.
apply: (@leq_ltn_trans (\sum_(0 <= i < k) 2 ^ i)).
- apply: leq_sum => i _; rewrite {}/g.
  by case: b1.[i]; rewrite ?simpm.
suff ->: \sum_(0 <= i < k) 2 ^ i = (2 ^ k).-1.
- by rewrite prednK // expn_gt0.
- by rewrite big_mkord; apply/sum_pow2.
Qed.

(* ==================================================================== *)
Module Nim.
Context (p : nat).

(* A Nim game is composed of `p` rows of matches. We represents this    *)
(* as a function from [s : 'I_p -> nat] where [s i] denotes the number  *)
(* of matches in the row [i].                                           *)
(*                                                                      *)
(* The type ['I_p] stands for the range [0..p[, i.e. for the set of the *)
(* natural numbers lower then [p].                                      *)
(*                                                                      *)
(* It is defined as the following induction predicate/type:             *)
(*                                                                      *)
(* Inductive ordinal (p : nat) :=                                       *)
(* | Ordinal : forall (i : nat), (i < p) -> ordinal p.                  *)

Definition state := 'I_p -> nat.

(* We now define a function that, given a state [s], returns a list     *)
(* of natural numbers [r] s.t. for any natural number [i] lower than    *)
(* [p], the [i]-th element of [r] is equal to the number of matches     *)
(* in the [i]-th row of [s] (i.e. is equal to [s i])                    *)
(*                                                                      *)
(* The function [map] is defined as follows:                            *)
(*                                                                      *)
(* Fixpoint map (f : T -> U) (s : list T) : list U :=                   *)
(*   match s with                                                       *)
(*   | nil => nil                                                       *)
(*   | cons x s' => cons (f x) (map f s')                               *)
(*   end.                                                               *)
(*                                                                      *)
(* Note that [map (fun i => f i) s] is printed as:                      *)
(*                                                                      *)
(*   [seq s i | i <- s]                                                 *)
(*                                                                      *)
(* Also, note that [enum 'I_p] is the list that contains all the        *)
(* natural numbers from [0] to [p] (excluded).                          *)

Definition rows (s : state) : list nat :=
  map (fun i => s i) (enum 'I_p).

(* We prove that the size of [rows s] if equal to [p] where [size] is   *)
(* defined as follow:                                                   *)
(*                                                                      *)
(* Fixpoint size (s : seq T) :=                                         *)
(*   match s with                                                       *)
(*   | nil => 0                                                         *)
(*   | cons _ s' => S (size s)                                          *)
(*   end.                                                               *)

Lemma size_rows (s : state) : size (rows s) = p.
Proof. by rewrite /rows size_map size_enum_ord. Qed.

(* We also prove that the [i]-th element of [rows s] is equal to [s i]. *)
(* We use the function [nth] for that purpose, whose definition is:     *)
(*                                                                      *)
(* Fixpoint nth (x0 : T) (s : list T) (i : nat) {struct i} :=           *)
(*   match s with                                                       *)
(*   | nil =>                                                           *)
(*       x0                                                             *)
(*   | cons y s' =>                                                     *)
(*       match i with                                                   *)
(*       | O => y                                                       *)
(*       | S j => nth x0 s j                                            *)
(*       end                                                            *)
(*   end.                                                               *)

Lemma nth_rows (s : state) (i : 'I_p) : nth 0 (rows s) i = s i.
Proof. by rewrite (nth_map i) ?size_enum_ord // nth_ord_enum. Qed.

(* At each turn, the running player must select a row and remove at     *)
(* least 1 match from this row. We here denote a binary relation [R]    *)
(* over states s.t. [s1 R_i s2] iff it is possible to move from [s1] to *)
(* [s2] in one turn on row [i].                                         *)

Inductive R (i : 'I_p) (s1 s2 : state) : Prop :=
| Turn :
      (s2 i < s1 i)
   -> (forall j : 'I_p, j != i -> s2 j = s1 j)
   -> R i s1 s2.
  
(* -------------------------------------------------------------------- *)
(* The weight a of Nim state is obtained by xor'ing the number of       *)
(* matches (in 1-complement) for all the game rows.                     *)

(* First, write a function [weight_r] that takes a list [s] of natural  *)
(* numbers, and that returns bit-vector obtained by xor'ing all the     *)
(* elements [s] (in 1-complement).                                      *)
(*                                                                      *)
(* Hint: define a Fixpoint over [s] & use [bits0], [bxor] & [n2b].      *)

Fixpoint weight_r (s : seq nat) {struct s} : bits :=
  match s with
  | nil => bits0
  | cons n s' => bxor (n2b n) (weight_r s')
  end.

(* We define the function [weight] s.t. [weight s] returns the weight   *)
(* of the game state [s].                                               *)

Definition weight (s : state) : bits :=
  weight_r (rows s).

(* -------------------------------------------------------------------- *)
(* Prove that the empty game board has a weight of 0                    *)
(*                                                                      *)
(* Here, [fun=> 0] denotes the constant function equal to 0.            *)

Lemma weight_empty : weight (fun=> 0) = 0%:B.
Proof.
(* We start by unfolding the definition of [weight] & [rows]            *)
rewrite /weight /rows.
(* The proof can now be done by induction over [enum 'I_p]              *)
(* FIXME *)
elim: (enum 'I_p) => [|i s IHs] /=.
- auto.
- rewrite IHs.
  rewrite n2b0.
  rewrite bxor0b.
  auto. 
Qed.


(* -------------------------------------------------------------------- *)
(* We now prove some extra lemmas about [weight_r].                     *)
(*                                                                      *)
(* Hint: you can use the lemmas [bxor??] here.                          *)

Lemma weight_r0: weight_r nil = bits0.
Proof.
rewrite /weight_r.
auto.
Qed.


Lemma weight_r1 (n : nat): weight_r [:: n] = n2b n.
Proof.
rewrite /weight_r.
rewrite bxorb0.
auto.
Qed.


Lemma weight_rS (n : nat) (ns : list nat) :
  weight_r (n :: ns) = n2b n .+ weight_r ns.
Proof.
rewrite /weight_r //=.
Qed.

(* Here, [++] denotes [cat], the list-concatenation function.           *)
(*                                                                      *)
(* The function [cat] is defined as follows:                            *)
(*                                                                      *)
(* Fixpoint cat (r s : seq T) {struct r} :=                             *)
(*   match r with                                                       *)
(*   | nil => s                                                         *)
(*   | cons y r' => cons y (cat r' s)                                   *)
(*   end.                                                               *)

Lemma weight_rD (r s : list nat) :
  weight_r (r ++ s) = bxor (weight_r r) (weight_r s).
Proof.
(* FIXME *)
induction r.
- simpl. rewrite bxor0b. auto.
- simpl. rewrite IHr. rewrite bxorA. auto.
Qed.     

(* -------------------------------------------------------------------- *)
(* We can describe how the weight evolves after one turn                *)
(*                                                                      *)
(* We first  prove a characterization of [R]                            *)

Lemma RP (i : 'I_p) (s1 s2 : state) : R i s1 s2 ->
  exists (p : seq nat) (q : seq nat),
    [/\ size p = i
      , rows s1 = p ++ (s1 i) :: q
      & rows s2 = p ++ (s2 i) :: q].
Proof.
case=> lt_s eq_s; exists (take i (rows s1)), (drop i.+1 (rows s1)); split.
- by rewrite size_take size_rows ltn_ord.
- rewrite -cat1s catA cats1 -[s1 i]nth_rows /=.
  by rewrite -take_nth ?size_rows // cat_take_drop.
rewrite -cat1s catA cats1 -[s2 i]nth_rows /=.
have ->: take i (rows s1) = take i (rows s2).
- rewrite -!(map_nth_iota0 0) ?size_rows 1?ltnW //.
  apply/eq_in_map=> j; rewrite mem_iota /= add0n => lt_ji.
  have lt_jp: j < p by apply: (ltn_trans lt_ji).
  rewrite !(nth_rows _ (Ordinal lt_jp)) /=.
  by apply/esym/eq_s; rewrite -val_eqE /= ltn_eqF.
have ->: drop i.+1 (rows s1) = drop i.+1 (rows s2).
- rewrite -[LHS](take_oversize (n := p - i.+1)).
  - by rewrite size_drop size_rows.
  rewrite -[RHS](take_oversize (n := p - i.+1)).
  - by rewrite size_drop size_rows.
  rewrite -!(map_nth_iota 0) ?size_rows //.
  apply/eq_in_map=> j; rewrite mem_iota => /andP[lt_ij].
  rewrite subnKC // => lt_jp.
  rewrite !(nth_rows _ (Ordinal lt_jp)) /=.
  by apply/esym/eq_s; rewrite -val_eqE /= gtn_eqF.
by rewrite -take_nth ?size_rows // cat_take_drop.
Qed.    

(* We can now state and prove how the weight of the state evolves       *)
(* between two states related by [R].                                   *)
(*                                                                      *)
(* Hint: use [RP] and the [weight_rX] lemmas.                           *)
(* Hint: you will also need the [bxorX] lemmas family.                  *)

(* We write an auxiliary bxor operation here *)
Lemma bxorACA b1 b2 b3: (b1 .+ b2) .+ b3 = (b1 .+ b3) .+ b2.
Proof.
by rewrite -bxorA [b2 .+ b3] bxorC bxorA.
Qed.

Lemma turn_weight (i : 'I_p) (s1 s2 : state) :
  R i s1 s2 -> weight s2 = weight s1 .+ n2b (s1 i) .+ n2b (s2 i).
Proof.
(* FIXME *)
move=> H. apply RP in H.
case: H => p H. case: H => q H. case: H => H1 H2 H3.
rewrite /weight. 
rewrite H2 H3.
rewrite weight_rD.
rewrite weight_rD.
rewrite weight_rS.
rewrite weight_rS.
rewrite bxorA.
rewrite bxorA.
rewrite ![(_ .+ n2b (s1 i)) .+ _]bxorACA.
rewrite -!bxorA.
rewrite bxorbb.
rewrite bxorb0.
rewrite bxorA.
rewrite bxorC.
rewrite bxorA.
rewrite bxorA.
rewrite ![( _ .+ weight_r q)]bxorC.
auto.
Qed.


(* -------------------------------------------------------------------- *)
(* Any move from a 0-weighted game leads to a non 0-weighted game       *)
(*                                                                      *)
(* Hint: you should use [turn_weight] here.                             *)
(* Hint: you can use the injectivity of n2b.                            *)
(* Hint: b1 (+) b2 = true iff b1 = b2.                                  *)
(* Hint: you can use contraposition, e.g. [contra_neq_not].             *)

Lemma ltf (n : nat):
  n < n -> false.
Proof.
intros.
induction n.
- done.
- by apply IHn in H.
Qed.

Lemma b02bnbb (x : 'I_p) (s : state):
  0%:B = n2b (s x) .+ n2b (s x).
Proof.
by rewrite bxorbb.
Qed.

Lemma z2nz (i : 'I_p) (s1 s2 : state) :
  R i s1 s2 -> weight s1 = 0%:B -> weight s2 <> 0%:B.
Proof.
have n2b_inj: forall m n, n2b m = n2b n -> m = n.
- by move=> m n /(can_inj n2bK).
(* FIXME *)

move => H1 H2.
have HR: R i s1 s2.
apply H1.
destruct HR. 
apply turn_weight in H1.
rewrite H2 in H1.
rewrite bxor0b in H1.
move => H3.
rewrite H1 in H3.
rewrite (b02bnbb i s2) in H3.
have contra: n2b (s1 i) .+ n2b (s2 i) .+ n2b (s2 i) = n2b (s2 i) .+ n2b (s2 i) .+ n2b (s2 i).
by rewrite H3.
move: contra.
rewrite -bxorA.
rewrite -bxorA.
rewrite bxorbb.
rewrite bxorb0.
rewrite bxorb0.
move => contra.
apply n2b_inj in contra.
rewrite contra in H.
apply ltf  in H.
auto.
Qed.


(* -------------------------------------------------------------------- *)
(* From any non 0-weight game, it is possible to move to a              *)
(* 0-weighted game.                                                     *)
(*                                                                      *)
(* Hint: for this one, you are on your own.                             *)
(* Hint: https://en.wikipedia.org/wiki/Nim#Proof_of_the_winning_formula *)

Lemma nz2z (s : state) : weight s <> 0%:B ->
  exists (i : 'I_p), exists (s' : state), weight s' = 0%:B /\ R i s s'.
Proof.

(* FIXME *)
intros.
pose w := weight s.
remember (size w).-1 as d.

(* Prove that w.[d] not equal to 0 *)
have hi: w.[d].
rewrite Heqd.
apply hibit_neq0W.
apply H.
have hd := ((hibit_neq0W (weight s)).1 H).
rewrite -Heqd in hd.

(* Prove exist k such that x_k[d] not zero, prove by contradiction *)
have somek : exists (k : 'I_p), (n2b (s k)).[d].
- apply/existsP/existsPn => //=.
intro h2.
unfold weight in hd.
unfold rows in hd.
induction (enum 'I_p).
- rewrite //b0E// in hd.
- rewrite //bxorE in hd.
apply IHl.
rewrite (negbTE (h2 a))// in hd.
move: somek => [k HX].
(* pose x := n2b (s k) .
pose y := w .+ x. *)
remember (weight s) as hw.
remember (n2b (s k)) as x.
remember  ( hw .+ x ) as y.
remember (fun i => if i == k then b2n y else s i) as s'.

have sk' : s' k = b2n y.
    rewrite Heqs'.
    rewrite ifT.
    auto.
    auto.

have sk : s k = b2n x.
    rewrite Heqx.
    rewrite n2bK.
    auto.

have HY: negb y.[d].
    rewrite Heqy.
    rewrite bxorE.
    rewrite hi.
    rewrite HX.
    simpl.
    apply is_true_true.

(* Claim that y_k < x_k *)
have yltx: b2n y < b2n x.       
    apply lt_n2b. 
    exists d.

(* prove for all d<i x_k = y_k *)
have yxw: forall i, d < i -> y.[i] = x.[i].            
    intros i h_i.
    rewrite Heqx.
    rewrite Heqy.
    rewrite Heqhw.
    rewrite bxorE - Heqx.
    rewrite Heqd in h_i.
    have hs: (size (weight s)) <= i.
    unfold w in h_i. rewrite Heqhw in h_i.
    - by (induction (size (weight s)) => //=; rewrite ltnS; apply IHn).
    - rewrite (bit_oversize hs) //. apply yxw. 

have yx: y.[d] < x.[d].
    rewrite HX.
    have yf: y.[d] = false.
    apply negbTE.
    apply HY.
    rewrite yf.
    simpl.
    auto.
    apply yx.

exists k.
exists s'.

(* Finish the prove with weight s' = 0%:B /\ R k s s' *)
have rr: R k s s'.
    split.
    rewrite sk.
    rewrite sk'.
    apply yltx.
    intros.
    rewrite Heqs'.
    rewrite ifF.
    revert H0.
    rewrite neq_ltn => /orP [].
    apply ltn_eqF.
    apply gtn_eqF.
    auto.

split.
revert rr.
have w0: (weight s .+ n2b (s k) .+ n2b (s' k) = 0%:B).
rewrite <- Heqhw.
rewrite <- Heqx.
rewrite <- Heqy.
have skrev': (n2b (s' k) = y).
rewrite sk'.
rewrite b2nK.
auto.
rewrite skrev'.
rewrite bxorbb.
auto.
rewrite <- w0.      
apply turn_weight.
apply rr.
Qed.


End Nim.
