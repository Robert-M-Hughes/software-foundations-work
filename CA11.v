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


From LF Require Export Poly.

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

(*Exercise 2*)
Example and_exercise :
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  intros. split. 
  - destruct n.
    + reflexivity.
    + inversion H.
  - destruct m.
    + reflexivity.
    + rewrite plus_comm in H.
      * inversion H.
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

(*Exercise 3*)
Lemma proj2 : forall P Q : Prop,
  P /\ Q -> Q.
Proof.
  intros. destruct H.
  - assumption.
Qed.

Theorem and_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
  intros P Q [HP HQ].
  split.
    - (* left *) apply HQ.
    - (* right *) apply HP.  Qed.

(*Exercise 4*)
Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]].
  - split.
    + split.
      * assumption.
      * assumption.
    + assumption.
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

(*Exercise 5*)
Lemma mult_eq_0 :
  forall n m, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros [].
  - left. reflexivity.
  - right. destruct m.
    + reflexivity.
    + inversion H.
Qed.
  

(*Exercise 6*)
Theorem or_commut : forall P Q : Prop,
  P \/ Q  -> Q \/ P.
Proof.
  intros. destruct H.
  - right. apply H.
  - left. apply H.
Qed.


Module MyNot.

Definition not (P:Prop) := P -> False.



Notation "~ x" := (not x) : type_scope.

Check not.

End MyNot.

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  (* WORKED IN CLASS *)
  intros P contra.
  destruct contra.  Qed.

(*Exercise 7*)
Fact not_implies_our_not : forall (P:Prop),
  ~ P -> (forall (Q:Prop), P -> Q).
Proof.
  intros . destruct H.
  apply H0.
Qed. 


Theorem zero_not_one : ~(0 = 1).
Proof.
  intros contra. inversion contra.
Qed.

Check (0 <> 1).

Theorem zero_not_one' : 0 <> 1.
Proof.
  intros H. inversion H.
Qed.


Theorem not_False :
  ~ False.
Proof.
  unfold not. intros H. destruct H. Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.
  (* WORKED IN CLASS *)
  intros P Q [HP HNA]. unfold not in HNA.
  apply HNA in HP. destruct HP.  Qed.

Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
  (* WORKED IN CLASS *)
  intros P H. unfold not. intros G. apply G. apply H.  Qed.

(*Exercise 8*)
Theorem contrapositive : forall (P Q : Prop),
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros. unfold not. unfold not in H0. intros. apply H0 in H. assumption. assumption.
Qed.

(*Exercise 9*)
Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof.
  intros. unfold not. intros. destruct H.
  - apply H0 in H. assumption.
Qed.


Theorem not_true_is_false : forall b : bool,
  b <> true -> b = false.
Proof.
  intros [] H.
  - (* b = true *)
    unfold not in H.
    apply ex_falso_quodlibet.
    apply H. reflexivity.
  - (* b = false *)
    reflexivity.
Qed.

Theorem not_true_is_false' : forall b : bool,
  b <> true -> b = false.
Proof.
  intros [] H.
  - (* b = false *)
    unfold not in H.
    exfalso.
    apply H. reflexivity.
  - (* b = true *) reflexivity.
Qed.


(*Exercise 10*)
Theorem xxx:
  forall (P Q R: Prop),
  (P -> Q -> R) -> (P /\ Q -> R).

Proof.
  intros. destruct H0.
  - apply H.
    + apply H0.
    + apply H1.
Qed.

(*Exercise 11*)
Theorem yyy:
  forall (P Q R: Prop),
  (P /\ Q -> R) -> (P -> Q -> R).
Proof.
  intros. apply H. split.
  - apply H0.
  - apply H1.
Qed.

