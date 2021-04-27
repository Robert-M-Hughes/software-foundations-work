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

Fact not_implies_our_not : forall (P:Prop),
  ~ P -> (forall (Q:Prop), P -> Q).
Proof.
  (* FILL IN HERE *)
  intros.
  apply H in H0.
  exfalso. assumption.
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

Theorem contrapositive : forall (P Q : Prop),
  (P -> Q) -> (~Q -> ~P).
Proof.
  (* FILL IN HERE *)
  unfold not.
  intros.
  apply (H0 (H H1)).
  Qed.

Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof.
  (* FILL IN HERE *)
  unfold not.
  intros.
  destruct H.
  apply (H0 H).
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


Theorem xxx:
  forall n m,
  n <> m -> S n <> S m.

Proof.
  unfold not.
  intros.
  apply H.
  inversion H0.
  reflexivity.
  Qed.

Theorem yyy:
  forall (X: Type) (l l': list X),
  length l <> length l' -> l <> l'.

Proof.
  intros.
  assert (l = l' -> length l = length l').
  {
    intros. rewrite H0. reflexivity. 
  }
  apply contrapositive with (length l = length l').
  assumption. assumption.
  Qed.

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
  - (* -> *) apply HBA.
  - (* <- *) apply HAB.  Qed.

Lemma not_true_iff_false : forall b,
  b <> true <-> b = false.
Proof.
  (* WORKED IN CLASS *)
  intros b. split.
  - (* -> *) apply not_true_is_false.
  - (* <- *)
    intros H. rewrite H. intros H'. inversion H'.
Qed.

Theorem iff_refl : forall P : Prop,
  P <-> P.
Proof.
  (* FILL IN HERE *)
  split.
  - intros. assumption.
  - intros. assumption.
  Qed.

Theorem iff_trans : forall P Q R : Prop,
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  (* FILL IN HERE *)
  intros.
  destruct H.
  destruct H0.
  split.
  - intros. apply (H0 (H H3)).
  - intros. apply (H1 (H2 H3)).
  Qed.


Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  (* FILL IN HERE *)
  split.
  - intros. destruct H eqn:H1.
    + split.
      * left. assumption.
      * left. assumption.
    + destruct a. split.
      * right. assumption.
      * right. assumption.
  - intros. destruct H.
    destruct H eqn:H1.
    + left. assumption.
    + destruct H0 eqn:H2. 
      * left. assumption.
      * right. apply (conj q r).
  Qed.

Require Import Coq.Setoids.Setoid.

Lemma mult_0 : forall n m, n * m = 0 <-> n = 0 \/ m = 0.
Proof.
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
  intros n m H. apply mult_0. apply H.
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
  intros n [m Hm]. (* note implicit [destruct] here *)
  exists (2 + m).
  apply Hm.  Qed.

Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  (* FILL IN HERE *)
  intros.
  unfold not.
  intros.
  destruct H0.
  apply H0.
  apply H.
  Qed.


Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
   (* FILL IN HERE *)
   split.
   - intros. destruct H. destruct H.
     + left. exists x. assumption.
     + right. exists x. assumption.
   - intros. destruct H.
     + destruct H. exists x. left. assumption.
     + destruct H. exists x. right. assumption.
   Qed.


Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.

Example In_example_1 : In 4 [1; 2; 3; 4; 5].
Proof.
  (* WORKED IN CLASS *)
  simpl. right. right. right. left. reflexivity.
Qed.

Example In_example_2 :
  forall n, In n [2; 4] ->
  exists n', n = 2 * n'.
Proof.
  (* WORKED IN CLASS *)
  simpl.
  intros n [H | [H | []]].
  - exists 1. rewrite <- H. reflexivity.
  - exists 2. rewrite <- H. reflexivity.
Qed.

Lemma In_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
    In x l ->
    In (f x) (map f l).
Proof.
  intros A B f l x.
  induction l as [|x' l' IHl'].
  - (* l = nil, contradiction *)
    simpl. intros [].
  - (* l = x' :: l' *)
    simpl. intros [H | H].
    + rewrite H. left. reflexivity.
    + right. apply IHl'. apply H.
Qed.

Lemma In_map_iff :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
    In y (map f l) <->
    exists x, f x = y /\ In x l.
Proof.
  (* FILL IN HERE *)
  intros.
  split.
  - intros. induction l.
    + simpl in H. inversion H.
    + simpl in H. destruct H.
      * exists x. split. assumption.
        simpl. left. reflexivity.
      * apply IHl in H. destruct H.
        destruct H. exists x0.
        split. assumption.
        simpl. right. assumption.
  - intros. destruct H. destruct H.
    rewrite <- H. apply In_map. assumption.
  Qed.


Lemma In_app_iff : forall A l l' (a:A),
  In a (l++l') <-> In a l \/ In a l'.
Proof.
  (* FILL IN HERE *)
  split.
  - intros. induction l.
    + simpl in H. right. assumption.
    + simpl in H. destruct H.
      * left. simpl. left. assumption.
      * simpl. apply or_assoc. right.
        apply IHl. assumption.
  - intros. induction l.
    + simpl in H. destruct H.
      * exfalso. assumption.
      * assumption.
    + simpl in H. simpl.
      apply or_assoc in H.
      destruct H.
      * left. assumption. 
      * right. apply IHl. assumption.
  Qed.


Fixpoint All {T : Type} (P : T -> Prop) (l : list T) : Prop
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *) :=
  match l with
  | [] => True
  | h :: t => P h /\ (All P t)
  end.

Lemma All_In :
  forall T (P : T -> Prop) (l : list T),
    (forall x, In x l -> P x) <->
    All P l.
Proof.
  (* FILL IN HERE *)
  intros.
  split.
  - intros. induction l.
    + simpl. apply I.
    + simpl. split.
      * apply H. simpl. left. reflexivity.
      * apply IHl. intros. apply H. simpl. right. assumption.
  - intros. induction l.
    + inversion H0.
    + destruct H0.
      * simpl in H. destruct H. rewrite <- H0. assumption.
      * simpl in H. destruct H. apply (IHl H1 H0).
  Qed.


Definition combine_odd_even (Podd Peven : nat -> Prop) : nat -> Prop
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *) :=
  fun (x:nat) => if oddb x then Podd x else Peven x.


Theorem combine_odd_even_intro :
  forall (Podd Peven : nat -> Prop) (n : nat),
    (oddb n = true -> Podd n) ->
    (oddb n = false -> Peven n) ->
    combine_odd_even Podd Peven n.
Proof.
  (* FILL IN HERE *)
  intros.
  unfold combine_odd_even.
  destruct (oddb n) eqn: H1.
  - apply H. reflexivity.
  - apply H0. reflexivity.
  Qed.

Theorem combine_odd_even_elim_odd :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = true ->
    Podd n.
Proof.
  (* FILL IN HERE *)
  unfold combine_odd_even.
  intros.
  destruct (oddb n) eqn:H1.
  - assumption.
  - inversion H0.
  Qed.

Theorem combine_odd_even_elim_even :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = false ->
    Peven n.
Proof.
  (* FILL IN HERE *)
  unfold combine_odd_even.
  intros.
  destruct (oddb n) eqn:H1.
  - inversion H0.
  - assumption.
  Qed.


Check plus_comm.
(* ===> forall n m : nat, n + m = m + n *)



Lemma plus_comm3 :
  forall x y z, x + (y + z) = (z + y) + x.


Proof.
  intros x y z.
  rewrite plus_comm.
  rewrite plus_comm.
  (* We are back where we started... *)
Abort.

Lemma plus_comm3_take2 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite plus_comm.
  assert (H : y + z = z + y).
  { rewrite plus_comm. reflexivity. }
  rewrite H.
  reflexivity.
Qed.

Lemma plus_comm3_take3 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite plus_comm.
  rewrite (plus_comm y z).
  reflexivity.
Qed.

Example lemma_application_ex :
  forall {n : nat} {ns : list nat},
    In n (map (fun m => m * 0) ns) ->
    n = 0.
Proof.
  intros n ns H. Print In_map_iff.
  destruct (proj1 _ _ (In_map_iff _ _ _ _ _) H)
           as [m [Hm _]].
  rewrite mult_0_r in Hm. rewrite <- Hm. reflexivity.
Qed.



Example function_equality_ex1 : plus 3 = plus (pred 4).
Proof. reflexivity. Qed.

Example function_equality_ex2 :
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
   (* Stuck *)
Abort.

Axiom functional_extensionality : forall {X Y: Type}
                                    {f g : X -> Y},
  (forall (x:X), f x = g x) -> f = g.

Example function_equality_ex2 :
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
  apply functional_extensionality. intros x.
  apply plus_comm.
Qed.

Print Assumptions function_equality_ex2.

Fixpoint rev_append {X} (l1 l2 : list X) : list X :=
  match l1 with
  | [] => l2
  | x :: l1' => rev_append l1' (x :: l2)
  end.

Definition tr_rev {X} (l : list X) : list X :=
  rev_append l [].


Lemma rev_append_app:
  forall (X: Type) (l1 l2: list X),
  rev_append l1 l2 = rev_append l1 [] ++ l2.

Proof.
  induction l1.
  - intros. simpl. reflexivity.
  - intros. simpl. rewrite (IHl1 [x]).
    rewrite <- app_assoc.
    simpl.
    apply (IHl1 (x::l2)).
    Qed.

Lemma tr_rev_correct : forall X, @tr_rev X = @rev X.
(* FILL IN HERE *)
Proof.
  unfold tr_rev.
  intros.
  apply functional_extensionality.
  intros.
  rename x into l.
  induction l.
  - reflexivity.
  - simpl. rewrite <- IHl.
    apply rev_append_app.
    Qed.

Fixpoint tr_length_aux {X: Type} (l: list X) (c: nat) :=
  match l with
  | [] => c
  | h :: t => tr_length_aux t (S c)
  end.

Definition tr_length {X: Type} (l: list X) :=
  tr_length_aux l 0.


Lemma tr_length_aux_S:
  forall (X: Type) (l: list X) (n: nat),
  tr_length_aux l (S n) = S (tr_length_aux l n).

Proof.
  induction l.
  - reflexivity.
  - intros. simpl.
    rewrite (IHl (S n)).
    reflexivity.
    Qed.

Theorem tr_length_correct:
  forall (X: Type), @tr_length X = @length X.

Proof.
  unfold tr_length.
  intros.
  apply functional_extensionality.
  intros.
  rename x into l.
  induction l.
  - reflexivity.
  - simpl. rewrite <- IHl.
    apply tr_length_aux_S.
  Qed.


Theorem evenb_double : forall k, evenb (double k) = true.
Proof.
  intros k. induction k as [|k' IHk'].
  - reflexivity.
  - simpl. apply IHk'.
Qed.
  

Theorem evenb_double_conv : forall n,
  exists k, n = if evenb n then double k
                else S (double k).
Proof.
  (* Hint: Use the [evenb_S] lemma from [Induction.v]. *)
  (* FILL IN HERE *) Print evenb_S.
  intros.
  induction n.
  -  simpl. exists 0. reflexivity.
  - destruct IHn. destruct (evenb n) eqn:H1.
    + exists x. rewrite evenb_S. rewrite H1. simpl.
      rewrite H. reflexivity.
    + rewrite H. simpl. rewrite evenb_double.
      exists (S x). simpl. reflexivity.
  Qed.

Theorem even_bool_prop : forall n,
  evenb n = true <-> exists k, n = double k.
Proof.
  intros n. split.
  - intros H. destruct (evenb_double_conv n) as [k Hk].
    rewrite Hk. rewrite H. exists k. reflexivity.
  - intros [k Hk]. rewrite Hk. apply evenb_double.
Qed.

Theorem beq_nat_true_iff : forall n1 n2 : nat,
  eqb n1 n2 = true <-> n1 = n2.
Proof.
  intros n1 n2. split.
  - apply eqb_true.
  - intros H. rewrite H. rewrite <- eqb_refl. reflexivity.
Qed.

Fail Definition is_even_prime n :=
  if n = 2 then true
  else false.

Example even_1000 : exists k, 1000 = double k.

Proof. exists 500. reflexivity. Qed.

Example even_1000' : evenb 1000 = true.
Proof. reflexivity. Qed.


Example even_1000'' : exists k, 1000 = double k.
Proof. apply even_bool_prop. reflexivity. Qed.


Lemma andb_true_iff : forall b1 b2:bool,
  b1 && b2 = true <-> b1 = true /\ b2 = true.
Proof.
  (* FILL IN HERE *)
  split.
  - destruct b1.
    + simpl. intros. split. reflexivity. assumption.
    + simpl. intros. inversion H.
  - intros. destruct H. rewrite H, H0. reflexivity.
  Qed.

Lemma orb_true_iff : forall b1 b2,
  b1 || b2 = true <-> b1 = true \/ b2 = true.
Proof.
  (* FILL IN HERE *)
  split.
  - destruct b1. 
    + simpl. left. reflexivity.
    + simpl. right. assumption.
  - intros. destruct H.
    + rewrite H. reflexivity.
    + rewrite H. destruct b1. reflexivity. reflexivity.
  Qed.

Theorem beq_nat_false_iff : forall x y : nat,
  eqb x y = false <-> x <> y.
Proof.
  (* FILL IN HERE *)
  split.
  - unfold not.
    intros. rewrite H0 in H. rewrite <- eqb_refl in H.
    inversion H.
  - unfold not. intros.
    assert (eqb x y = true -> x = y).
    {
      apply beq_nat_true_iff.
    }
    apply contrapositive in H0.
    + unfold not in H0.
      destruct (eqb x y).
      * exfalso.  apply H0. reflexivity.
      * reflexivity. 
    + unfold not. apply H.
  Qed.

Fixpoint beq_list {A : Type} (beq : A -> A -> bool)
                  (l1 l2 : list A) : bool
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *) :=
  match l1,l2 with
  | [],[] => true
  | h1 :: t1, h2 :: t2 => if beq h1 h2 then beq_list beq t1 t2 else false
  | _, _ => false
  end.

Lemma beq_list_refl:
  forall (A: Type) (beq: A -> A -> bool) (l: list A),
  (forall a1 a2, beq a1 a2 = true <-> a1 = a2) ->
  beq_list beq l l = true.

Proof.
  intros.
  induction l.
  - reflexivity.
  - simpl. destruct (beq x x) eqn:H1.
    + assumption.
    + assert (x = x). {reflexivity. }
      apply H in H0. rewrite H1 in H0. assumption.
  Qed.

Lemma beq_list_true_iff :
  forall A (beq : A -> A -> bool),
    (forall a1 a2, beq a1 a2 = true <-> a1 = a2) ->
    forall l1 l2, beq_list beq l1 l2 = true <-> l1 = l2.
Proof.
(* FILL IN HERE *)
  split.
  - generalize dependent l2.
    induction l1.
    + destruct l2.
      * reflexivity.
      * simpl. intros. inversion H0.
    + destruct l2.
      * simpl. intros. inversion H0.
      * simpl. destruct (beq x x0) eqn:H1.
        intros. apply H in H1. apply IHl1 in H0. rewrite H1, H0. reflexivity.
        intros. inversion H0.
  - intros. rewrite H0. apply beq_list_refl. assumption. 
  Qed.


Theorem forallb_true_iff : forall X test (l : list X),
   forallb test l = true <-> All (fun x => test x = true) l.
Proof.
  (* FILL IN HERE *)
  split.
  - induction l.
    + simpl. intros. apply I.
    + simpl. intros. destruct (test x) eqn:H1.
      * split. reflexivity. apply (IHl H).
      * inversion H.
  - induction l.
    + simpl. reflexivity.
    + simpl. intros. destruct H. rewrite H. apply IHl.
      assumption.
  Qed.


Fixpoint Exists {T : Type} (P : T -> Prop) (l : list T) : Prop :=
  match l with
  | [] => False
  | h :: t => P h \/ Exists P t
  end.


Theorem existsb_true_iff :
  forall X test (l: list X),
  existsb test l = true <-> Exists (fun x => test x = true) l.

Proof.
  intros.
  split.
  - induction l.
    + simpl. intros. inversion H.
    + simpl. destruct (test x) eqn:H.
      * left. reflexivity.
      * intros. right. apply (IHl H0).
  - induction l.
    + simpl. intros. inversion H.
    + simpl. intros. destruct H.
      * rewrite H. reflexivity.
      * destruct (test x) eqn:H1.
        reflexivity.
        apply (IHl H).
  Qed.


(*New Session*)

Definition excluded_middle := forall P : Prop,
  P \/ ~ P.

Theorem restricted_excluded_middle : forall P b,
  (P <-> b = true) -> P \/ ~ P.
Proof.
  intros P [] H.
  - left. rewrite H. reflexivity.
  - right. rewrite H. intros contra. inversion contra.
Qed.

Theorem restricted_excluded_middle_eq : forall (n m : nat),
  n = m \/ n <> m.
Proof.
  intros n m.
  apply (restricted_excluded_middle (n = m) (eqb n m)).
  symmetry.
  apply beq_nat_true_iff.
Qed.

(*Exercise 1*)
(*The following theorem states that the negation of
excluded middle is not provable for arbitrary proposition P,
i.e., you may find some proposition P for which excluded middle
is provable. *)

Theorem excluded_middle_irrefutable: forall (P:Prop),
  ~ ~ (P \/ ~ P).
Proof.
  unfold not. intros. apply H. right. intros. apply H. left. apply H0.
Qed. 


(*Exercise 2*)
Theorem not_exists_dist :
  excluded_middle ->
  forall (X:Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
  unfold excluded_middle. intros. unfold not in H0. unfold not in H.
  destruct (H (P x)) as [H1 | H2]. apply H1. destruct H0. exists x. apply H2.
Qed.



Definition peirce := forall P Q: Prop,
  ((P->Q)->P)->P.

Definition double_negation_elimination := forall P:Prop,
  ~~P -> P.

Definition de_morgan_not_and_not := forall P Q:Prop,
  ~(~P /\ ~Q) -> P\/Q.

Definition implies_to_or := forall P Q:Prop,
  (P->Q) -> (~P\/Q).

(*In the following exercises, we want to show that these
statements are logically equivalent, i.e.,
it does not really matter which one you add to Coq as an axiom
to make it classical!
For this purpose in the following 8 exercises we show that
peirce <-> double_negation_elimination <-> excluded middle <-> 
implies_to_or
and 
double_negation_elimination <-> de morgan.
*)

(*Exercise 3: double negation elimination implies peirce.*)

Theorem peirce_to_double_negation_elimination:
  peirce -> double_negation_elimination.

Proof.
  unfold peirce. unfold double_negation_elimination.
  intros pe P NNP.
  apply (pe P False).
  intro NP.
  unfold not in NNP.
  destruct (NNP NP).
Qed.


Lemma excluded_middle_to_peirce:
  excluded_middle->peirce.
Proof.
  unfold excluded_middle.
  unfold peirce.
  intros.
  assert (P\/~P).
  apply H.
  destruct H1 as [|].
    - apply H1.
    - unfold not in H1.
      assert (P->Q).
      intros. apply H1 in H2. destruct H2.
      apply H0 in H2. apply H2.
Qed.

Lemma double_negation_elimination_to_excluded_middle_Helper:
  double_negation_elimination -> excluded_middle.

Proof.
   unfold double_negation_elimination.
  unfold excluded_middle.
  intros.
  apply (H _).
  apply excluded_middle_irrefutable.
Qed.


(*Exercise 4: double negation elimination implies peirce*)
Theorem double_negation_elimination_to_peirce:
  double_negation_elimination -> peirce.

Proof.
  intros. apply excluded_middle_to_peirce. apply double_negation_elimination_to_excluded_middle_Helper.
assumption.
Qed.


(*Exercise 5: double negation elimination implies excluded middle*)

Theorem double_negation_elimination_to_excluded_middle:
  double_negation_elimination -> excluded_middle.

Proof.
   unfold double_negation_elimination.
  unfold excluded_middle.
  intros.
  apply (H _).
  apply excluded_middle_irrefutable.
Qed.


(*Exercise 6: excluded middle implies double negation elimination*)

Theorem excluded_middle_to_double_negation_elimination:
  excluded_middle -> double_negation_elimination.

Proof.
   unfold double_negation_elimination.
  unfold excluded_middle. intros.
    assert (P \/ ~ P). apply H.
    destruct H1 as [|].
      + apply H1.
      + apply H0 in H1. destruct H1.
Qed.

(*Exercise 7: double negation elimination implies de morgan*)
Lemma cut:
  forall (P Q R: Prop),
  (P -> Q) -> (Q -> R) -> (P -> R).

Proof.
intros. apply H0. apply H. assumption.
Qed.

Theorem double_negation_elimination_to_de_morgan:
  double_negation_elimination -> de_morgan_not_and_not.

Proof.
  unfold double_negation_elimination.
  unfold de_morgan_not_and_not.
  intros cl P Q H.
  apply (cl (P \/ Q)).
  intro NPQ. apply H.
  split.
    intro HP. apply NPQ. left. apply HP.
    intro HQ. apply NPQ. right. apply HQ.
Qed.

(*Exercise 8: de morgan implies double negation elimination*)

Theorem de_morgan_to_double_negation_elimination:
  de_morgan_not_and_not -> double_negation_elimination.

Proof.
  unfold de_morgan_not_and_not.
  unfold double_negation_elimination.
  unfold not. intros. remember (H P P) as help. 
apply (cut ((P -> False) /\ (P -> False) -> False) (P \/ P) P).
apply help. intros. destruct H1. assumption. assumption.
intros. destruct H1. apply H0 in H1. assumption.
Qed.


(*Exercise 9: excluded middle implies "implies to or"*)

Theorem excluded_middle_to_implies_to_or:
  excluded_middle -> implies_to_or.

Proof.
  unfold excluded_middle, implies_to_or.
intros EM. intros P Q H.
remember (EM P) as either_or. inversion either_or as [T|F].
right. apply (H T).
left. assumption.
Qed.


(*Exercise 10: "implies to or" implies excluded middle*)

Theorem implies_to_or_to_excluded_middle:
  implies_to_or -> excluded_middle.

Proof.
unfold implies_to_or. unfold excluded_middle.  
intros. apply or_commut.  
apply (H P P). 
 intros. apply H0.
Qed.





