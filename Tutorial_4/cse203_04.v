Require Import ssreflect.


(* We import the following library which gives us a notation for
   the comparision between nat's   *)
Require Import Nat.
Check (leb 3 4).
Eval compute in (3 <=? 4).
Eval compute in (4 <=? 3).



(* The library ssrbool adds a shortcut where booleans can be 
   viewed as propositions. If b is of type bool, it can be 
   viewd as the proposition b = true. *)

Require Import ssrbool.

Check true.

Check (is_true true).

Lemma ex_true : true.
Proof.
reflexivity.
Qed.
(* in general we will rather use the 'trivial' tactic though *)


(* The following command is explained a few lines below *)
Set Implicit Arguments.


(* We define lists as seen; but this time the type of the arguments
   is a parameter. We will be able to have lists for any type.   
   So list : Type -> Type     *)
Inductive list (A : Type) :=
| nil 
| cons : A -> list A -> list A.

Check nil.
Check cons.
(* You see the type A is an argument of nil and cons *)

(* The empty list of nat's  : *)
Check (nil nat).

(* Because of implicit arguments, we can ommit the argument A for 
   cons - it is guessed by the system : *)
Check (cons 1 (cons 2 (nil nat))).

(* We can also often let the system guess the argument of nil : *)
Check (cons 1 (cons 2 (nil _))).


(* A pattern matching :  *)
(* in some versions of Coq you may not have to mention 
   the argument of nil *)

Fixpoint app A (l1 : list A) l2 :=
  match l1 with
  | nil _ => l2  (* here *)
  | cons n l => cons n (app l l2)
  end.

(* examples of adding commands into intro-patterns *)

Lemma app_nil : forall A (l : list A), app l (nil _) = l.
Proof.
move => A.
(* try first 
elim => [ | n l hl].
 *)
(* adding /= forces a 'simpl'
elim => [ | n l hl] /=.
 *)
(* adding //= does simpl + trivial + try discriminate : *)
elim => [ | n l hl] //=.
rewrite hl.

(* The tactic 'done' corresponds to simpl+trivial+try discriminate *)
done.
Qed.

(* one can replace "rewrite hl; done" by  "by rewrite hl." *) 

(* Define the function which computes the length of a list *)
Fixpoint length A (l : list A) :=
  match l with
  | nil _ => 0
  | cons _ m => S(length m)
  end.
  (* put correct code here *)


Lemma app_length : forall A (l1 : list A) l2,
    length (app l1 l2) = (length l1) + (length l2).
Proof.
move => A.
elim => [| x l hl] l2 //=.  
by rewrite hl.
Qed.


(* The following property states that a nat is less than the 
   first element of a list - if it exists. *)
Definition le_head (n:nat)(l : list nat) :=
  match l with
  | nil _ => True
  | cons m _ => n <=? m
  end.

(* Use le_head to define what is means for a (list nat) to be 
   sorted in increasing order   *)
Fixpoint sorted (l : list nat) :=
  match l with
  | nil _ => True
  | cons n l => (le_head n l) /\ (sorted l)
  end.


Definition l123 := (cons 1 (cons 2 (cons 3 (nil _)))).

Lemma s123 : sorted l123.
Proof.
do 4 (split; trivial).
Qed.


(* Using the  <=?  construct, define a function 
   insert : nat -> list nat -> list nat
   which inserts a nat in a sorted list  *)

Fixpoint insert (n:nat) (l : list nat) :=
  match l with
  | nil _ => cons n (nil _)
  | cons m l' =>
    if n <=? m then cons n l
    else cons m (insert n l')
  end.


(* Use insert to define a simple sorting function *)
(* insertion_sort : list nat -> list nat.  *)


Fixpoint insertion_sort (l : list nat) :=
  (* put correct code here *)
  match l with
  | nil _ => nil _
  | cons x l => insert x (insertion_sort l)
  end.

(* Test your function on an example *)
Eval compute in
    (insertion_sort (cons 5 (cons 3 (cons 2 (cons 4 (cons 1 (nil _))))))).


(* Try testing your function on a LARGE example *)

           
Fixpoint revn n  :=
  match n with
  | O => nil _
  | S n => cons n (revn n)
  end.

Definition l1000 :=  (revn 1000).
(* Eval compute in (insertion_sort l1000). *)
(* you can interrupt by ctrl-c if necessary *)

(* What is the complexity of insetion_sort ? *)
(* answer in the comment *)


(* Now we will do two things:
 1 - prove that insertion_sort is indeed a sorting function
 2 - define a more efficient sorting function
*)


(* 1-a : Insertion sort preserves the content of the list. 
   In this part we show that the elements are the same
   at the end of the sorting *)


Fixpoint elem (n:nat) (l : list nat) :=
  match l with
  | nil _ => False
  | cons m l => n = m \/ elem n l
  end.

Lemma ins_elem1 : forall l n m, elem m l -> elem m (insert n l).
Proof.
elim => [| p l hl] n m //=.
move => [e | e]; case (_ <=? _); simpl; auto.
Qed.

Lemma eqn_refl : forall n, n =? n.
elim => [|n e]//=.
Qed.

Lemma eqn_eq : forall n p, n =? p -> n=p.
elim => [|n hn][| p]//= e.
rewrite (hn p) //=.  
Qed.

Lemma ins_elem2 : forall l n, elem n (insert n l).
Proof.
elim => [| p l hl] n //=.
 auto.
case (_ <=? _); simpl; auto.
Qed.


Lemma ins_elem3 : forall l n p, elem p (insert n l) -> p=n \/ elem p l.
Proof.
Proof.
elim => [| m l hl] n p //=.
case (_ <=? _); simpl; auto.
move => [e | e]; auto.
case: (hl n p e).
auto. auto.
Qed.




Lemma insertion_sort_elem1 :
  forall l n, elem n l -> elem n (insertion_sort l).
Proof.
elim => [|m l hl] n //=.
move => [e | e]. rewrite e; apply ins_elem2.
apply ins_elem1; auto.
Qed.

Lemma insertion_sort_elem2 :
  forall l n, elem n (insertion_sort l) -> elem n l.
Proof.
elim => [|m l hl] n //= e.
case: (ins_elem3 _ m n e).
  auto.
by move => h; right; apply hl.
Qed.

(* Question : is this property totally satisfying ? *)



(* 1-b We now prove that the result of the sorting function is indeed
   sorted *)

(* this technical lemma we already saw in the previous class *)
Lemma leb_trans : forall n m p,
    n <=? m -> m <=? p -> n<=? p.
Proof.
elim => [|n hn][|m][|p]//=.
apply hn.
Qed.

(* This one is easy too *)
Lemma leb_anti : forall n m, n <=? m = false -> m <=? n.
Proof.
elim => [| n hn][| m]//=.
by move => nm; apply hn.
Qed.

(* We want to show that insert preserves the property sorted
   One possibility is to prove first this stronger lemma which
   is a good induction property *)

(* We give the begining of the proof in order to show the use of
   the case tactic here *)
Lemma ins_sorted_aux : forall l n,
    sorted l ->
    (sorted (insert n l))
    /\ (forall m, m<=? n ->
                  le_head m l ->
                  le_head m (insert n l)).
Proof.
(* We do an induction over l, move n up *)
elim => [| m l hl]//= n [h1 h2].


(* we get the two induction hypotheses *)
move: (hl n h2) => [h3 h4].

(* Now the trick : we do a case analysis over (n <=? m) but keep track
  wether its value is true, resp. false *)
case nm : (_ <=? _) => /=.
Admitted.

(* The lemma we wanted is now an easy consequence of the previous one *)
Lemma ins_sorted : forall l n,
    sorted l ->
    (sorted (insert n l)).
Proof.
by move => l n sl; case (ins_sorted_aux l n sl).
Admitted.

Lemma insertion_sort_sorted : forall l, sorted (insertion_sort l).
Proof.
elim => [|x l hl]//=.
by apply ins_sorted.
Qed.


(* 2 A more efficient sorting algorithm *)

(* We use this function which merges two sorted lists into
   one sorted list 
  We give the code because the syntex is a little tricky in order
  to "explain" to Coq the it terminates  *)

Fixpoint merge l1 l2 :=
  let fix merge_aux l2 :=
  match l1, l2 with
  | nil _, t2 => t2
  | t1, nil _ => t1
  | cons n1 m1, cons n2 m2=>
    if n1 <=? n2 then
      cons n1 (merge m1 l2) 
    else 
      cons n2 (merge_aux m2)      
  end
  in merge_aux l2.




Eval compute in
    merge (cons 1 (cons 3 (nil _)))(cons 2 (nil _)).


(* This algorithm stores data in binary trees *)
Inductive tree :=
| Leaf
| Node : nat -> tree -> tree -> tree.


(* such a tree is a heap if :
   - the element at the root is smaller than the others
   - the two subtrees are heaps

This property (being a heap) corresponds to the property of being
sorted for lists.

Let us define it :  *)

(* The following prpoerty corresponds to le_head, but for trees: *) 
Definition le_tree n t :=
  match t with
  | Leaf => True
  | Node m _ _ => n <=? m = true
  end.

(* Now define the property "being a heap" *)
Fixpoint heap t :=
  match t with
  | Leaf => True
  | Node n t1 t2 =>
    le_tree n t1 /\ le_tree n t2  /\
    heap t1 /\ heap t2
  end.


(* What does this function do ? *)
Fixpoint ins_tree n t :=
  match t with
  | Leaf => (Node n Leaf Leaf)
  | Node m t1 t2 =>
    if n <=? m then
      (Node n (ins_tree m t2) t1)
    else
      (Node m (ins_tree n t2) t1)
  end.

(* define a function which transforms an usorted list into a tree
   which has the heap property (and is thus partly sorted)  *)

Fixpoint to_heap (l : list nat) :=
  (* correct code here *) Leaf.



(* define a function which transforms a heap into a sorted list 
   with the same elements *)

Fixpoint to_list (t : tree) :=
  (* correct code here *)
  nil nat.

(* use the previous functions to define a new sorting function *)

Definition heap_sort (l : list nat) :=
  (* correct code here *) nil nat.    

(* test it *)
Eval compute in
    heap_sort (cons 3 (cons 5 (cons 1 (cons 2 (cons 4 (nil _)))))).



Eval compute in (heap_sort l1000).



(* Can you see or guess things about the complexity of this 
   new sorting function ? *)

