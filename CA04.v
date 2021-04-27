(*
I hereby assign copyright in my past and future contributions 
to the Software Foundations project to the Author of Record of 
each volume or component, to be licensed under the same terms 
as the rest of Software Foundations. I understand that, at present, 
the Authors of Record are as follows: For Volumes 1 and 2, known 
until 2016 as "Software Foundations" and from 2016 as (respectively) 
"Logical Foundations" and "Programming Foundations," and for Volume 4, 
"QuickChick: Property-Based Testing in Coq," the Author of Record is 
Benjamin C. Pierce. For Volume 3, "Verified Functional Algorithms", 
the Author of Record is Andrew W. Appel. For components outside of 
designated volumes (e.g., typesetting and grading tools and other 
software infrastructure), the Author of Record is Benjamin Pierce.
*)



(** * Proofs Within Proofs *)

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros.
  induction n.
  - simpl. rewrite <- plus_n_O. reflexivity.
  - simpl. rewrite IHn. rewrite plus_n_Sm. reflexivity.
  Qed.

Theorem mult_0_plus' : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n). { reflexivity. }
  rewrite -> H.
  reflexivity.  Qed.



Theorem plus_rearrange_firsttry : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  (* We just need to swap (n + m) for (m + n)... seems
     like plus_comm should do the trick! *)
  rewrite -> plus_comm.
  (* Doesn't work...Coq rewrote the wrong plus! *)
Abort.


Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
  { rewrite -> plus_comm. reflexivity. }
  rewrite -> H. reflexivity.  Qed.


(** * Lists: Working with Structured Data *)

From LF Require Export Induction.
Module NatList.

(** * Pairs of Numbers *)

Inductive natprod : Type :=
| pair : nat -> nat -> natprod.

Check (pair 3 5).

Definition fst (p : natprod) : nat :=
  match p with
  | pair x y => x
  end.

Definition snd (p : natprod) : nat :=
  match p with
  | pair x y => y
  end.

Compute (fst (pair 3 5)).
(* ===> 3 *)

Notation "( x , y )" := (pair x y).

Compute (fst (3,5)).

Definition fst' (p : natprod) : nat :=
  match p with
  | (x,y) => x
  end.

Definition snd' (p : natprod) : nat :=
  match p with
  | (x,y) => y
  end.

Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x,y) => (y,x)
  end.



Theorem surjective_pairing' : forall (n m : nat),
  (n,m) = (fst (n,m), snd (n,m)).
Proof.
  reflexivity.  Qed.

Theorem surjective_pairing_stuck : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  simpl. (* Doesn't reduce anything! *)
Abort.


Theorem surjective_pairing : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  intros p. destruct p as [n m].  simpl.  reflexivity.  Qed.


(*Exercise 1*)
Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
  intros.
  destruct p.
  reflexivity.
Qed.


(*Exercise 2*)
Theorem fst_swap_is_snd : forall (p : natprod),
  fst (swap_pair p) = snd p.
Proof.
  intros.
  destruct p.
  reflexivity.
Qed.

(*Exercise 3: Prove that swap of swap of pair is itself.*)

Theorem swap_swap : forall (p : natprod),
  swap_pair(swap_pair p) = p.
Proof.
  intros.
  destruct p.
  reflexivity.
Qed.



(** * Lists of Numbers *)
Inductive natlist : Type :=
  | nil  : natlist
  | cons : nat -> natlist -> natlist.

Definition mylist := cons 1 (cons 2 (cons 3 nil)).

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Definition mylist1 := 1 :: (2 :: (3 :: nil)).
Definition mylist2 := 1 :: 2 :: 3 :: nil.
Definition mylist3 := [1;2;3].


Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.

Fixpoint length (l:natlist) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil    => l2
  | h :: t => h :: (app t l2)
  end.

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).

Example test_app1:             [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. reflexivity.  Qed.
Example test_app2:             nil ++ [4;5] = [4;5].
Proof. reflexivity.  Qed.
Example test_app3:             [1;2;3] ++ nil = [1;2;3].
Proof. reflexivity.  Qed.


Definition hd (default:nat) (l:natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.

Definition tl (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => t
  end.

Example test_hd1:             hd 0 [1;2;3] = 1.
Proof. reflexivity.  Qed.
Example test_hd2:             hd 0 [] = 0.
Proof. reflexivity.  Qed.
Example test_tl:              tl [1;2;3] = [2;3].
Proof. reflexivity.  Qed.



(*Exercise 4*)
Fixpoint nonzeros (l:natlist) : natlist :=
  match l with
  | nil => nil
  | O :: t => nonzeros t
  | h :: t => h :: (nonzeros t)
  end.

Example test_nonzeros:
  nonzeros [0;1;0;2;3;0;0] = [1;2;3].
  Proof. reflexivity. Qed.



(*Exercise 5*)
Fixpoint oddmembers (l:natlist) : natlist :=
  match l with
  |nil => nil
  |h :: t => match oddb  h with 
             | true => h :: oddmembers t
             | false => oddmembers t
             end
end.


Example test_oddmembers:
  oddmembers [0;1;0;2;3;0;0] = [1;3].
  Proof. reflexivity. Qed.

(*Exercise 6*)
Definition countoddmembers (l:natlist) : nat :=
  match l with
  | nil => O
  | h :: t => length (oddmembers l)
end.

Example test_countoddmembers1:
  countoddmembers [1;0;3;1;4;5] = 4.
  Proof. reflexivity. Qed.

Example test_countoddmembers2:
  countoddmembers [0;2;4] = 0.
  Proof. reflexivity. Qed.

Example test_countoddmembers3:
  countoddmembers nil = 0.
  Proof. reflexivity. Qed.


(*Exercise 7*)
(** Complete the definition of [alternate], which "zips up" two lists
    into one, alternating between elements taken from the first list
    and elements from the second.  See the tests below for more
    specific examples.
*)

Fixpoint alternate (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | h1 :: t1 => match l2 with
              | nil => l1
              | h2 :: t2 => h1 :: h2 :: (alternate t1 t2)
              end
 end.
 
Example test_alternate1:
  alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
  Proof. reflexivity. Qed.

Example test_alternate2:
  alternate [1] [4;5;6] = [1;4;5;6].
  Proof. reflexivity. Qed.

Example test_alternate3:
  alternate [1;2;3] [4] = [1;4;2;3].
  Proof. reflexivity. Qed.

Example test_alternate4:
  alternate [] [20;30] = [20;30].
  Proof. reflexivity. Qed.



(** *** Bags via Lists *)
Definition bag := natlist.


(*Exercise 8*)
Fixpoint count (v:nat) (s:bag) : nat :=
  match s with
  | nil => 0
  | h :: t => match eqb v h with
              | true => S (count v t)
              | false => count v t
              end
 end.

Example test_count1:              count 1 [1;2;3;1;4;1] = 3.
 Proof. reflexivity. Qed.
Example test_count2:              count 6 [1;2;3;1;4;1] = 0.
 Proof. reflexivity. Qed.


(*Exercise 9*)
Definition member (v:nat) (s:bag) : bool :=
  match s with
  | nil => false
  | h :: t => match eqb (count v s) O with
              | true => false
              | false => true
              end
end.

Example test_member1:             member 1 [1;4;1] = true.
 Proof. reflexivity. Qed.

Example test_member2:             member 2 [1;4;1] = false.
 Proof. reflexivity. Qed.


(*Exercise 10*)
Fixpoint remove_one (v:nat) (s:bag) : bag :=
  match s with
    | [] => []
    | h::t => if (eqb h v) then t else h::(remove_one v t)
  end.
  

Example test_remove_one1:
  count 5 (remove_one 5 [2;1;5;4;1]) = 0.
  Proof. reflexivity. Qed.

Example test_remove_one2:
  count 5 (remove_one 5 [2;1;4;1]) = 0.
  Proof. reflexivity. Qed.

Example test_remove_one3:
  count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
  Proof. reflexivity. Qed.

Example test_remove_one4:
  count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
  Proof. reflexivity. Qed.


(*Exercise 11*)
Fixpoint remove_all (v:nat) (s:bag) : bag :=
  match s with
    | [] => []
    | h::t => if (eqb h v) then (remove_all v t) else h::(remove_all v t)
  end.

Example test_remove_all1:  count 5 (remove_all 5 [2;1;5;4;1]) = 0.
 Proof. reflexivity. Qed.
Example test_remove_all2:  count 5 (remove_all 5 [2;1;4;1]) = 0.
 Proof. reflexivity. Qed.
Example test_remove_all3:  count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
 Proof. reflexivity. Qed.
Example test_remove_all4:  count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
 Proof. reflexivity. Qed.


(*Exercise 12*)
Fixpoint subset (s1:bag) (s2:bag) : bool :=
  match s1 with 
  | nil => true
  | h :: t => match member h s2 with
                | false => false
                | true => subset t (remove_one h s2)
                end
end.


Example test_subset1:              subset [1;2] [2;1;4;1] = true.
 Proof. reflexivity. Qed.
Example test_subset2:              subset [1;2;2] [2;1;4;1] = false.
 Proof. reflexivity. Qed.
(** [] *)

(*Exercise 13*)
(** Write down a theorem that shows when you add an element to a bag
the count of that element in the bag increases by one. You don't have
to prove it. *)

Theorem question_13: forall (n:nat) (b:bag),
S (count n b) = count n (n :: b).






