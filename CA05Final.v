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

Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
  destruct p. reflexivity. Qed.

Theorem fst_swap_is_snd : forall (p : natprod),
  fst (swap_pair p) = snd p.
Proof.
  destruct p. reflexivity. Qed.

Theorem swap_swap:
  forall p, swap_pair (swap_pair p) = p.

Proof. destruct p. reflexivity. Qed.




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


Fixpoint nonzeros (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => match h with
              | O => nonzeros t
              | S _ => h :: (nonzeros t)
              end
  end.

Example test_nonzeros:
  nonzeros [0;1;0;2;3;0;0] = [1;2;3].

Proof. reflexivity. Qed.

Fixpoint oddmembers (l:natlist) : natlist
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *) :=
  match l with
  | nil => nil
  | h :: t => match oddb h with
              | true => h :: (oddmembers t)
              | false => oddmembers t
              end
  end.
  

Example test_oddmembers:
  oddmembers [0;1;0;2;3;0;0] = [1;3].

Proof. reflexivity. Qed.

Definition countoddmembers (l:natlist) : nat
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *) := 
  length (oddmembers l).

Example test_countoddmembers1:
  countoddmembers [1;0;3;1;4;5] = 4.

Proof. reflexivity. Qed.

Example test_countoddmembers2:
  countoddmembers [0;2;4] = 0.

Proof. reflexivity. Qed.

Example test_countoddmembers3:
  countoddmembers nil = 0.

Proof. reflexivity. Qed.


(** Complete the definition of [alternate], which "zips up" two lists
    into one, alternating between elements taken from the first list
    and elements from the second.  See the tests below for more
    specific examples.
*)

Fixpoint alternate (l1 l2 : natlist) : natlist
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *) :=
  match l1, l2 with
  | nil, _ => l2
  | _, nil => l1
  | h1 :: t1, h2 :: t2 =>  h1 :: h2 :: (alternate t1 t2)
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


Fixpoint count (v:nat) (s:bag) : nat
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *) :=
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



Definition member (v:nat) (s:bag) : bool
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *) :=
  match count v s with
  | O => false
  | _ => true
  end.

Example test_member1:             member 1 [1;4;1] = true.

Proof. reflexivity. Qed.

Example test_member2:             member 2 [1;4;1] = false.

Proof. reflexivity. Qed.


Fixpoint remove_one (v:nat) (s:bag) : bag
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *) :=
  match s with
  | nil => nil
  | h :: t => match eqb v h with
              | true => t
              | false => h :: (remove_one v t)
              end
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


Fixpoint remove_all (v:nat) (s:bag) : bag
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *) :=
  match s with
  | nil => nil
  | h :: t => match beq_nat v h with
              | true => remove_all v t
              | false => h :: (remove_all v t)
              end
  end.  

Example test_remove_all1:  count 5 (remove_all 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.

Example test_remove_all2:  count 5 (remove_all 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.

Example test_remove_all3:  count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity. Qed.

Example test_remove_all4:  count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
Proof. reflexivity. Qed.


Fixpoint subset (s1:bag) (s2:bag) : bool
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *) :=
  match s1 with
  | nil => true
  | h1 :: t1 => match member h1 s2 with
                | true =>  subset t1 (remove_one h1 s2)
                | false => false
                end
  end.

Example test_subset1:              subset [1;2] [2;1;4;1] = true.
Proof. reflexivity. Qed.
Example test_subset2:              subset [1;2;2] [2;1;4;1] = false.
Proof. reflexivity. Qed.


(** Write down a theorem that shows when you add an element to a bag
the count of that element in the bag increases by one. You don't have
to prove it. *)

Theorem bag_add_count:
  forall (v: nat) (s: bag), 
  count v (v :: s) = S (count v s).

Proof.
  Admitted.

(*New session*)

Theorem nil_app : forall l:natlist,
  [] ++ l = l.
Proof. reflexivity. Qed.

Theorem tl_length_pred : forall l:natlist,
  pred (length l) = length (tl l).
Proof.
  intros l. destruct l as [| n l'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons n l' *)
    reflexivity.  Qed.

Theorem app_assoc : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons n l1' *)
    simpl. rewrite -> IHl1'. reflexivity.  Qed.


Fixpoint rev (l:natlist) : natlist :=
  match l with
  | nil    => nil
  | h :: t => rev t ++ [h]
  end.

Example test_rev1:            rev [1;2;3] = [3;2;1].
Proof. reflexivity.  Qed.
Example test_rev2:            rev nil = nil.
Proof. reflexivity.  Qed.


Theorem rev_length_firsttry : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - (* l = [] *)
    reflexivity.
  - (* l = n :: l' *)
    simpl.
    rewrite <- IHl'.
    (* ... but now we can't go any further. *)
Abort.

Theorem app_length : forall l1 l2 : natlist,
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  (* WORKED IN CLASS *)
  intros l1 l2. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons *)
    simpl. rewrite -> IHl1'. reflexivity.  Qed.

Theorem rev_length : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons *)
    simpl. rewrite -> app_length, plus_comm.
    simpl. rewrite -> IHl'. reflexivity.  Qed.



(*Exercise 1*)
Theorem app_nil_r : forall l : natlist,
  l ++ [] = l.
Proof.
  intros l. induction l as [| h t T'].
  -reflexivity.
  -simpl. rewrite T'. reflexivity.
Qed.

(*Exercise 2*)
Theorem rev_app_distr: forall l1 l2 : natlist,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros. induction l1 as [| h t T'].
  -simpl. rewrite app_nil_r. reflexivity.
  -simpl. rewrite T'. rewrite app_assoc. reflexivity.
Qed.

(*Exercise 3*)
Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  intros. induction l as [| h t T'].
  -reflexivity.
  -simpl. rewrite rev_app_distr. simpl. rewrite T'. reflexivity.
Qed.

(*Exercise 4*)
Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  intros l1 l2 l3 l4. induction l1 as [| h t T'].
  -simpl. rewrite app_assoc. reflexivity.
  -simpl. rewrite T'. reflexivity.
Qed.

(*Exercise 5*)
Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  intros. induction l1 as [| h t T'].
  -reflexivity.
  -simpl. destruct h. 
    + rewrite T'. reflexivity.
    + simpl. rewrite <- T'. reflexivity.
Qed.

(*Exercise 6*)Fixpoint beq_natlist (l1 l2 : natlist) : bool := 
 match l1 with     
 | nil => match l2 with
          | nil => true
          | h::t => false   
          end      
 | h :: t => match l2 with     
             |nil => false             
             |h2::t2 => match eqb h2 h with   
                        |true => beq_natlist t t2               
                        |false => false              
                        end
end
end.




Example test_beq_natlist1 :
  (beq_natlist nil nil = true).
Proof. intros. reflexivity. Qed.

Example test_beq_natlist2 :
  beq_natlist [1;2;3] [1;2;3] = true.
Proof. intros. reflexivity. Qed.

Example test_beq_natlist3 :
  beq_natlist [1;2;3] [1;2;4] = false.
Proof. intros. reflexivity. Qed.

(*Exercise 7*)
Theorem beq_natlist_refl : forall l:natlist,
  true = beq_natlist l l.
Proof.
  intros. induction l as [| h t T'].
  - simpl. reflexivity.
  - induction h as [| h']. 
    + simpl. rewrite T'. reflexivity.
    + simpl. rewrite IHh'. reflexivity.
Qed.


(*Exercise 8*)
Theorem count_member_nonzero : forall (s : bag),
  leb 1 (count 1 (1 :: s)) = true.
Proof.
 intros. destruct s as [| h t T']. 
 - simpl. reflexivity. 
 - simpl. reflexivity.
Qed.




Theorem ble_n_Sn : forall n,
  leb n (S n) = true.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* 0 *)
    simpl.  reflexivity.
  - (* S n' *)
    simpl.  rewrite IHn'.  reflexivity.  Qed.

Lemma leb_n_Sn : forall n,
  leb n (S n) = true.
Proof.
  intros.
  induction n as [| n' IH].
  - reflexivity.
  - simpl. rewrite -> IH. reflexivity.
Qed.

(*Exercise 9*)
Theorem remove_decreases_count: forall (s : bag),
  leb (count 0 (remove_one 0 s)) (count 0 s) = true.
Proof.
  intros. 
  induction s as [| h t IH].
  - simpl. reflexivity.
  - destruct h as [| h'].
    + simpl. rewrite -> leb_n_Sn. reflexivity.
    + simpl. rewrite -> IH. reflexivity.
Qed.


(*Exercise 10*)
Theorem question_10: forall (s s1: bag)(n:nat),
leb (count n s) (count n (app s s1) ) = true.
Proof.
  intros. induction s as [|h t T'].
  - simpl. reflexivity.
  - simpl. destruct (eqb n h).
    + simpl. rewrite T'. reflexivity.
    + rewrite T'. reflexivity.
Qed.


(*Exercise 11*)
Theorem rev_injective: forall (l1 l2 : natlist),
  rev l1 = rev l2 -> l1 = l2.
Proof.
  intros.
  rewrite <- rev_involutive.
  rewrite <- H.
  rewrite -> rev_involutive.
  reflexivity.
Qed.