(* Import cse203_04.v *)

(* Import the library for lists *)

(* There are several things which one may do
then :
A - Proving that heap_sort returns a sorted list
    (like done for insertion sort)

B - Proving that heap_sort preserves the content of 
    input list (like done for insertion sort)

C - Proving a stronger correction property for insertion
    sort, namely that the result is really a permuation
    of the input.


We give some starting points for each.
*)

(*
A Proving that heap_sort returns a sorted list

The proof is similar than the one for insertion sort.
But one needs to prove that insertion in a tree preserves
the heap property.

Like for the correctness of insertion, this is best
done by proving a stronger induction hypothesis.
*)

(* A1 : proving merge preserves sorting *)

(* The main induction *)
Lemma merge_sorted_aux:
  forall l1 l2,
    sorted l1 ->
    sorted l2 ->
       sorted (merge l1 l2)
       /\forall x, le_head x l1 ->
                   le_head x l2 ->
                   le_head x (merge l1 l2).
Proof.
elim =>[| n1 l1 hl1]; elim => [| n2 l2 hl2]//= [s1 h1] [s2 h2].
case n12 : (_ <=? _); simpl.
  by split; auto; split; apply hl1;auto.
split; trivial; split; trivial; case: (hl2) => //= h hh; trivial.
by apply hh; trivial; apply leb_anti.
Admitted.

Lemma to_list_sorted :
  forall t, heap t ->
            sorted (to_list t)
          /\forall m, le_tree m t -> le_head m (to_list t). 
Proof.
Admitted.


(* A2 proving that insertion in the heap preserves
the heap property *)

(* quite easy technical lemma; requires no induction *)
Lemma le_tree_trans : forall n m t,
    n <=? m -> le_tree m t -> le_tree n t.
Proof.
Admitted.

(* the main induction *)
Lemma ins_heap_aux :
  forall t n, heap t ->
              heap (ins_tree n t)
              /\forall m, m <=? n = true ->
                          le_tree m t  ->
                          le_tree m (ins_tree n t).
Proof.
Admitted.

Lemma ins_heap :
  forall t n, heap t ->
              heap (ins_tree n t).
Proof.
Admitted.

Lemma to_heap_heap : forall l,
    heap (to_heap l).
Proof.
Admitted.


(* A3 - pasting it together *)
Lemma heap_sorted :
  forall l, sorted (heap_sort l).
Proof.
Admitted.


(* B - Proving that heapsort preserves the content *)

(* Proving the properties about merge *)
Lemma merge_elem1 : forall l1 l2 n, elem n l1 -> elem n (merge l1 l2).
Proof.
Admitted.

Lemma merge_elem2 : forall l1 l2 n, elem n l2 -> elem n (merge l1 l2).
Proof.
Admitted.

Lemma merge_elem3 :  forall l1 l2 n, elem n (merge l1 l2) ->
                                     (elem n l1)\/(elem n l2).
Admitted.


(* elements of a tree *)

Fixpoint telem n t :=
  match t with
  | Leaf => False
  | Node m t1 t2 => n=m \/ telem n t1 \/ telem n t2
  end.

(* Provving the properties about ins_tree *)

Lemma inst_elem1 : forall t n, telem n (ins_tree n t).
Proof.
Admitted.

Lemma inst_elem2 : forall t n m, telem n t -> telem n (ins_tree m t).
Proof.
Admitted.

Lemma inst_elem3 : forall t n m, telem n (ins_tree m t) ->
                                 n = m \/ telem n t.
Proof.
Admitted.

(* Proving them for to_heap *)
Lemma to_heap_elem1 : forall l n,
    elem n l -> telem n (to_heap l).
Proof.
Admitted.

Lemma to_list_elem1 : forall t n,
    telem n t -> elem n (to_list t).
Proof.
Admitted.

(* Pasting it together *)
Lemma heapsort_elem1 : forall n l,
    elem n l -> elem n (heap_sort l).
Proof.
Admitted.

Lemma to_heap_elem2 : forall l n, telem n (to_heap l) -> elem n l.
Proof.
Admitted.

Lemma to_list_elem2 : forall t n, elem n (to_list t) -> telem n t.
Proof.
Admitted.

Lemma heap_sort_elem2 : forall l n, elem n (heap_sort l) -> elem n l.
Proof.
Admitted.






(* C - Show that insertion sort returns a permutation of the original list *)

(* We fist axiomatize permuations *)

Parameter permutation : forall A, list A -> list A -> Prop.

Axiom perm_refl : forall A (l : list A), permutation l l.
Axiom perm_app : forall A (l1 : list A) l2 x,
    permutation (cons x (app l1 l2))(app l1 (cons x l2)).
Axiom perm_cons : forall A (l1 : list A) l2 x,
    permutation l1 l2 -> permutation (cons x l1)(cons x l2).
Axiom perm_trans : forall A (l1 : list A) l2 l3,
    permutation l1 l2 -> permutation l2 l3 -> permutation l1 l3.
Axiom perm_sym : forall A (l1 : list A) l2, permutation l1 l2 -> permutation l2 l1.


Lemma ins_perm : forall n l, permutation (cons n l) (insert n l).
Admitted

                                         
Lemma sort_perm : forall l, permutation l (insertion_sort l).
Proof.
Admitted.
