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

From LF Require Export Tactics.

(*Exercise 1*)
(** Define two recursive [Fixpoints], [forallb] and [existsb].  The
    first checks whether every element in a list satisfies a given
    predicate:

      forallb oddb [1;3;5;7;9] = true

      forallb negb [false;false] = true

      forallb evenb [0;2;4;5] = false

      forallb (beq_nat 5) [] = true

    The second checks whether there exists an element in the list that
    satisfies a given predicate:

      existsb (beq_nat 5) [0;2;3;6] = false

      existsb (andb true) [true;true;false] = true

      existsb oddb [1;0;0;0;0;3] = true

      existsb evenb [] = false

    Next, define a _nonrecursive_ version of [existsb] -- call it
    [existsb'] -- using [forallb] and [negb].

    Finally, prove a theorem [existsb_existsb'] stating that
    [existsb'] and [existsb] have the same behavior. *)

(* FILL IN HERE *)
Fixpoint forallb {X: Type} (test: X -> bool) (l: list X) : bool :=
  match l with
  | [] => true
  | h :: t => if (test h) then forallb test t else false
  end.

Fixpoint existsb {X: Type} (test: X -> bool) (l: list X) : bool :=
  match l with
  | [] => false
  | h :: t => if (test h) then true else existsb test t
  end.

Definition existsb' {X: Type} (test: X -> bool) (l: list X) : bool :=
  negb (forallb (fun x => negb (test x)) l).

Theorem existb_existb':
  forall (X: Type) (test: X -> bool) (l: list X),
  existsb test l = existsb' test l.

Proof.
  induction l.
  - reflexivity.
  - simpl. destruct (test x) eqn:H1.
    + unfold existsb'. simpl. rewrite H1. reflexivity.
    + unfold existsb'. simpl. rewrite H1. simpl. unfold existsb' in IHl.
      assumption.
  Qed.


Require Export Tactics.


Check 3 = 3.
Check forall n m : nat, n + m = m + n.
Check 2 = 2.
Check forall n : nat, n = 2.
Check 3 = 4.

Theorem plus_2_2_is_4 :
  2 + 2 = 4.
Proof. reflexivity.  Qed.

Definition plus_fact : Prop := 2 + 2 = 4.
Check plus_fact.

Theorem plus_fact_is_true :
  plus_fact.
Proof. reflexivity.  Qed.

Definition is_three (n : nat) : Prop :=
  n = 3.
Check is_three.

Definition injective {A B} (f : A -> B) :=
  forall x y : A, f x = f y -> x = y.

Lemma succ_inj : injective S.
Proof.
  intros n m H. inversion H. reflexivity.
Qed.

Check @eq.



Check and.

Example and_example : 3 + 4 = 7 /\ 2 * 2 = 4.

Proof.
  (* WORKED IN CLASS *)
  split.
  - (* 3 + 4 = 7 *) reflexivity.
  - (* 2 + 2 = 4 *) reflexivity.
Qed.

Lemma and_intro : forall A B : Prop, A -> B -> A /\ B.
Proof.
  intros A B HA HB. split.
  - apply HA.
  - apply HB.
Qed.

Example and_example' : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  apply and_intro.
  - (* 3 + 4 = 7 *) reflexivity.
  - (* 2 + 2 = 4 *) reflexivity.
Qed.


Example and_exercise :
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  (* FILL IN HERE *)
  intros. split.
  destruct n.
  - reflexivity.
  - inversion H.
  - rewrite plus_comm in H. destruct m.
    + reflexivity.
    + inversion H.
  Qed.
  
Lemma and_example2 :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  (* WORKED IN CLASS *)
  intros n m H.
  destruct H as [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

Lemma and_example2' :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

Lemma and_example2'' :
  forall n m : nat, n = 0 -> m = 0 -> n + m = 0.
Proof.
  intros n m Hn Hm.
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

Lemma and_example3 :
  forall n m : nat, n + m = 0 -> n * m = 0.
Proof.
  (* WORKED IN CLASS *)
  intros n m H.
  assert (H' : n = 0 /\ m = 0).
  { apply and_exercise. apply H. }
  destruct H' as [Hn Hm].
  rewrite Hn. reflexivity.
Qed.

Lemma proj1 : forall P Q : Prop,
  P /\ Q -> P.
Proof.
  intros P Q [HP HQ].
  apply HP.  Qed.

Lemma proj2 : forall P Q : Prop,
  P /\ Q -> Q.
Proof.
  (* FILL IN HERE *)
  intros.
  destruct H.
  assumption.
  Qed.

Theorem and_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
  intros P Q [HP HQ].
  split.
    - (* left *) apply HQ.
    - (* right *) apply HP.  Qed.

Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]].
  (* FILL IN HERE *)
  split. split.
  assumption. assumption. assumption.
  Qed.



Check or.

Lemma or_example :
  forall n m : nat, n = 0 \/ m = 0 -> n * m = 0.
Proof.
  intros n m [Hn | Hm].
  - (* Here, [n = 0] *)
    rewrite Hn. reflexivity.
  - (* Here, [m = 0] *)
    rewrite Hm. rewrite <- mult_n_O.
    reflexivity.
Qed.


Lemma or_intro : forall A B : Prop, A -> A \/ B.
Proof.
  intros A B HA.
  left.
  apply HA.
Qed.

Lemma zero_or_succ :
  forall n : nat, n = 0 \/ n = S (pred n).
Proof.
  (* WORKED IN CLASS *)
  intros [|n].
  - left. reflexivity.
  - right. reflexivity.
Qed.

Lemma mult_eq_0 :
  forall n m, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  (* FILL IN HERE *)
  destruct n.
  - left. reflexivity.
  - intros. right. destruct m.
    + reflexivity.
    + inversion H.
  Qed.


Theorem or_commut : forall P Q : Prop,
  P \/ Q  -> Q \/ P.
Proof.
  (* FILL IN HERE *)
  intros.
  destruct H.
  - right. assumption.
  - left. assumption.
  Qed.




(*New Session*)


(*Exercise 1*)
Theorem xxx:
  forall n m,
  n <> m -> S n <> S m.

Proof.
  intros. unfold not. unfold not in H. intros. apply H. inversion H0. reflexivity.
Qed.
  

(*Exercise 2*)
Theorem yyy:
  forall (X: Type) (l l': list X),
  length l <> length l' -> l <> l'.

Proof.
  unfold not. intros. apply H. rewrite H0. reflexivity.
Qed.

Check I.

Print True.

Lemma True_is_true : True.
Proof. apply I. Qed.

Example True_hypo:
  forall (P:Prop), True -> P.

Proof.
  intros. destruct H.
  Abort.

Module MyIff.

Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).

Check iff.

Notation "P <-> Q" := (iff P Q)
                      (at level 95, no associativity)
                      : type_scope.

End MyIff.

Theorem iff_sym : forall P Q : Prop,
  (P <-> Q) -> (Q <-> P).
Proof.
  (* WORKED IN CLASS *)
  intros P Q [HAB HBA].
  split.
  - (* -> *) assumption. 
  - (* <- *) assumption. Qed.

Theorem not_true_is_false : forall b : bool,
  b <> true -> b = false.
Proof.
  intros [] H.
  - (* b = true *)
    unfold not in H.
    exfalso.
    apply H. reflexivity.
  - (* b = false *)
    reflexivity.
Qed.

Lemma not_true_iff_false : forall b,
  b <> true <-> b = false.
Proof.
  (* WORKED IN CLASS *)
  intros b. split.
  - (* -> *) apply not_true_is_false.
  - (* <- *)
    intros H. rewrite H. unfold not. intros H'. inversion H'.
Qed.

(*Exercise 3*)
Theorem iff_refl : forall P : Prop,
  P <-> P.
Proof.
  intros. split.
  - intros. assumption.
  - intros. assumption.
Qed.

(*Exercise 4*)
Theorem iff_trans : forall P Q R : Prop,
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  intros. destruct H. destruct H0. split.
  - intros. apply H0. apply H. assumption.
  - intros. apply H1. apply H2. assumption.
Qed.


(*Exercise 5*)
Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
 intros. split.
  - intros. split.
    + destruct H.
      * left. apply H.
      * destruct H. right. apply H.
    + destruct H.
      * left. apply H.
      * destruct H. right. apply H0.
  - intros. destruct H. destruct H.
    + left. apply H.
    + destruct H0.
      * left. apply H0.
      * right. split. apply H. apply H0.
Qed.


Require Import Coq.Setoids.Setoid.

Lemma mult_0 : forall n m, n * m = 0 <-> n = 0 \/ m = 0.
Proof.
  intros.
  split.
  - apply mult_eq_0.
  - apply or_example.
Qed.

Lemma or_assoc :
  forall P Q R : Prop, P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
  intros P Q R. split.
  - intros [H | [H | H]].
    + left. left. apply H.
    + left. right. apply H.
    + right. apply H.
  - intros [[H | H] | H].
    + left. apply H.
    + right. left. apply H.
    + right. right. apply H.
Qed.

Lemma mult_0_3 :
  forall n m p, n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof.
  intros n m p.
  rewrite mult_0. rewrite mult_0. rewrite or_assoc.
  reflexivity.
Qed.

Lemma apply_iff_example :
  forall n m : nat, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros n m H. apply mult_0. assumption.
Qed.

Lemma four_is_even : exists n : nat, 4 = n + n.
Proof.
  exists 2. reflexivity.
Qed.

Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  (* WORKED IN CLASS *)
  intros. destruct H as [m Hm]. (* note implicit [destruct] here *)
  exists (2 + m).
  apply Hm.  Qed.

(*Exercise 6*)
Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  intros. unfold not.
  intros. destruct H0. apply H0. apply H.
Qed.

(*Exercise 7*)

Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
   intros. split.
   - intros. destruct H. destruct H.
    + left. exists x. apply H.
    + right. exists x. apply H.
  - intros. destruct H. destruct H.
    + exists x. left. assumption.
    + destruct H.
      * exists x. right. assumption.
Qed.

