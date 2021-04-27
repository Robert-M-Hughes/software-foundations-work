(* Brandon Reno | Robbie Hughs ----- KNAPSACK PROBLEM ----- Course Project Phase 2 - Implementation *)
From LF Require Import Poly.
From LF Require Export Induction.
From LF Require Export Lists.


(* WEIGHTCHECK DEFINITION: Purpose, get the weight of a group of items *)

Fixpoint WeightCheck (l:list (nat * nat)): nat :=
match l with
| [] => 0
| h :: t => snd h + WeightCheck t
end.

Lemma weightCheck_test1: WeightCheck [(3,4);(5,6);(7,8)] = 18.
Proof. reflexivity. Qed.

Lemma weightCheck_test2: WeightCheck [(3,6);(5,8);(7,1)] = 15.
Proof. reflexivity. Qed.







(* VALUECHECK DEFINITION: Purpose, get the value of a group of items *)

Fixpoint ValueCheck (l:list (nat * nat)): nat :=
match l with
| [] => 0
| h :: t => fst h + ValueCheck t
end.

Lemma valueCheck_test1: ValueCheck [(3,4);(5,6);(7,8)] = 15.
Proof. reflexivity. Qed.

Lemma valueCheck_test2: ValueCheck [(1,6);(5,8);(20,1)] = 26.
Proof. reflexivity. Qed.







(*FILTERWEIGHTS DEFINITION: Purpose, to filter a group of items and return only the groups
 of items less than equal to max weight does this by utilizing weight check function defined above *)

Fixpoint FilterWeights (l:list(list (nat * nat))) (max: nat): list(list(nat * nat)) :=
match l with
| [] => [[(0,0)]]
| h :: t => if leb (WeightCheck h) max then h :: (FilterWeights t max) else FilterWeights t max
end.

Lemma filter_test1: FilterWeights [[(3,4) ; (5,6) ; (7,8) ; (9,10)] ; [(1,6);(5,8);(20,1)] ; [(3,2) ; (2,3)]] 10 = [[(3,2) ; (2,3)]; [(0,0)]].
Proof. reflexivity. Qed.

Lemma filter_test2: FilterWeights [[(3,4) ; (5,6) ; (7,8) ; (9,10)] ; [(1,6);(5,8);(20,1)] ; [(3,2) ; (2,3)]] 15 = [[(1, 6); (5, 8); (20, 1)]; [(3, 2); (2, 3)]; [(0, 0)]].
Proof. reflexivity. Qed.







(*SUBSETS DEFINITION: Purpose, generates subsets of differen combinations of items *)

Fixpoint Subsets (l:list (nat * nat)): (list (list (nat * nat))) :=
match l with
| [] => [[]]
| h::t => Subsets t ++ map (app [h]) (Subsets t)
end.
Compute Subsets [(3,4) ; (5,6) ; (7,8)].

Lemma subset_test: Subsets [(3,4) ; (5,6) ; (7,8)] = [[ ]; [(7, 8)]; [(5, 6)]; [(5, 6); (7, 8)]; 
       [(3, 4)]; [(3, 4); (7, 8)]; [(3, 4); (5, 6)];
       [(3, 4); (5, 6); (7, 8)]].
Proof. reflexivity. Qed.







(* KNAPSACK DEFINITION: Purpose find the list that gets the greatest value
   KNAPSACKDRIVER DEFINITION: Purpose generate subsets of the given list, filter the subsets based on 
        the max weight and then return the list from knapsack which gives best value *)

Fixpoint Knapsack (l:list (list (nat * nat))) (l2:list (nat * nat)) (value:nat): list (nat * nat) :=
match l with
|[] => l2
|h :: t => if leb value (ValueCheck h) then Knapsack t h (ValueCheck h) else Knapsack t l2 value
end.

Definition Knapsack_Driver (l:list (nat * nat)) (l2:list (nat * nat)) (max_weight: nat) : list (nat * nat) :=
match max_weight with
|O => l2
|S n => Knapsack (FilterWeights(Subsets l) max_weight) [] 0
end.


(* Testing the knapsack problem now with some test lemmas *)


Lemma Knapsack_Test: Knapsack_Driver [(3,4) ; (5,6) ; (7,8) ; (9,10)] [] 15 = [(3, 4); (9, 10)].
Proof. reflexivity. Qed.

Lemma Knapsack_Test2: Knapsack_Driver [(3,6) ; (5,2) ; (7,5) ; (30,10)] [] 15 =[(7, 5); (30, 10)].
Proof. reflexivity. Qed.

Lemma Knapsack_Test3: Knapsack_Driver [(3,6) ; (5,2) ; (7,5) ; (30,10)] [] 10 =[(30, 10)].
Proof. reflexivity. Qed.

Lemma Knapsack_Test4: Knapsack_Driver [(33,20) ; (56,23) ; (21,15) ; (30,10) ; (40,1) ; (23,13)] [] 10 =[(40, 1)].
Proof. reflexivity. Qed.

Lemma Knapsack_Test5: Knapsack_Driver [(33,20) ; (56,23) ; (21,15) ; (30,10) ; (40,1) ; (23,13)] [] 54 = [(33, 20); (56, 23); (30, 10); (40, 1)].
Proof. reflexivity. Qed.


(* Verification phase *)

Fixpoint max_val_perm (l : list(list(nat * nat))) (n : nat) : nat :=
match l with
| [] => n
| h :: t => if leb n (ValueCheck h) then max_val_perm t (ValueCheck h) else max_val_perm t n
end.

Lemma max_val_perm_test1: max_val_perm(FilterWeights [[(3,4) ; (5,6) ; (7,8) ; (9,10)] ; [(1,6);(5,8);(20,1)] ; [(3,2) ; (2,3)]] 10) 0 = 5.
Proof. intros. reflexivity. Qed.

Lemma max_val_perm_test2: max_val_perm(FilterWeights [[(3,4) ; (5,6) ; (7,8) ; (9,10)] ; [(1,6);(5,8);(20,1)] ; [(3,2) ; (2,3)]] 20) 0 = 26.
Proof. intros. reflexivity. Qed.

Lemma max_val_perm_test3: max_val_perm(FilterWeights [[(3,4) ; (5,6) ; (7,8) ; (9,10)] ; [(1,6);(5,8);(20,1)] ; [(3,2) ; (2,3)]] 30) 0 = 26.
Proof. intros. reflexivity. Qed.

Lemma ksg0: forall (l : list(nat * nat)) (w :nat), leb 0 (ValueCheck(Knapsack_Driver l [] w)) = true.
Proof. intros. induction l.
  simpl. reflexivity.
  simpl. reflexivity.
Qed.

Lemma vcg0: forall (l : list(nat * nat)) (w : nat), leb 0 (max_val_perm(FilterWeights(Subsets l) w) 0) = true.
Proof. intros. induction l.
  simpl. reflexivity. 
  simpl. reflexivity.
Qed.


Lemma ks_help: forall (l : list(nat * nat)) (w : nat) (x : (nat * nat)),
(Knapsack_Driver l [] w) = (Knapsack_Driver (x :: l) [] w).
Proof. intros. induction w. reflexivity. Admitted.


Lemma vc_help: forall (l : list(nat * nat)) (w : nat) (x : (nat * nat)),
(max_val_perm (FilterWeights (Subsets l ) w)0) =  (max_val_perm (FilterWeights (Subsets (x::l)) w)0).
Proof. Admitted.


Lemma Knap_help: forall (l : list(nat * nat)) (w : nat) (x : (nat * nat)), 
      (ValueCheck (Knapsack_Driver l [ ] w)) =? (max_val_perm (FilterWeights (Subsets l) w) 0) = true-> 
      (ValueCheck (Knapsack_Driver (x::l) [ ] w)) =? (max_val_perm (FilterWeights (Subsets (x::l)) w)0) = true.
Proof. intros. rewrite <- ks_help. rewrite <- vc_help. assumption.
Qed.

Theorem KnapSack_verification: forall (l: list(nat * nat)) (w: nat), 
eqb (ValueCheck(Knapsack_Driver l [] w)) (max_val_perm(FilterWeights(Subsets l) w) 0) = true.
Proof. intros. induction l. induction w.
      - reflexivity.
      - reflexivity.
      - simpl. apply Knap_help. assumption.
Qed.
      









