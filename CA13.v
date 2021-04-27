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

(*New Session*)

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

(*Exercise 1*)
Lemma In_map_iff :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
    In y (map f l) <->
    exists x, f x = y /\ In x l.
Proof.
  intros. split.
  -  intros H. induction l as [| x' l' IHl'].
      simpl in H. contradiction.
      simpl in H. destruct H as [H1 | H2].
      + exists x'. split.
        * apply H1.
        * simpl. left. reflexivity. 
      + apply IHl' in H2. destruct H2 as [x2 H2]. exists x2. split.
        * apply proj1 in H2. apply H2.
        * simpl. right. apply proj2 in H2. apply H2. 
  - intros H. induction l as [| x' l' IHl'].
      simpl in H. destruct H as [x' H]. apply proj2 in H. contradiction.
      simpl. simpl in H. destruct H as [x'' H]. inversion H. destruct H1 as [H2 | H3].
      + left. rewrite H2. apply H0. 
      + right. apply IHl'. exists x''. split.
        * apply H0.
        * apply H3. 
Qed.


(*Exercise 2*)
Lemma In_app_iff : forall A l l' (a:A),
  In a (l++l') <-> In a l \/ In a l'.
Proof.
  intros.
  split.
  - induction l as [| h t IH].
    + simpl. intros. right. apply H.
    + simpl. intros.
      apply or_assoc.
      destruct H.
      * left. apply H.
      * right. apply IH. apply H.
  - induction l as [| h t IH].
    + simpl. intros. destruct H.
        destruct H.
        apply H.
    + simpl. intros. destruct H. destruct H.
        left. apply H.
        right. apply IH. left. apply H.
        right. apply IH. right. apply H.
Qed.

(*Exercise 3*)
(** Write a recursive function [All]
    stating that some property [P] holds of all elements of a list
    [l]. To make sure your definition is correct, prove the [All_In]
    lemma below.  (Of course, your definition should _not_ just
    restate the left-hand side of [All_In].) *)

Fixpoint All {T : Type} (P : T -> Prop) (l : list T) : Prop :=
  match l with
  | [] => True
  | h :: t => P h /\ All P t
end.

Lemma All_In :
  forall T (P : T -> Prop) (l : list T),
    (forall x, In x l -> P x) <->
    All P l.
Proof.
    intros T.
  induction l as [| a t IH].
  - split.
    + intros H. apply I.
    + intros H0 x H.
      destruct H.
  - split.
    + intros H. split.
      * apply H. left. reflexivity.
      * apply IH. intros x H2.
        apply H. right. apply H2.
    + intros [H1 H2] x H3.
      destruct H3 as [H4 | H5].
      * rewrite <- H4. apply H1.
      * apply IH. apply H2. apply H5.
Qed.
        
      

(*Exercise 4*)
(** Complete the definition of the [combine_odd_even] function below.
    It takes as arguments two properties of numbers, [Podd] and
    [Peven], and it should return a property [P] such that [P n] is
    equivalent to [Podd n] when [n] is odd and equivalent to [Peven n]
    otherwise. *)

Definition combine_odd_even (Podd Peven : nat -> Prop) : nat -> Prop :=
  fun n => match oddb n with
            | true => Podd n
            | false => Peven n
 end.


Theorem combine_odd_even_intro :
  forall (Podd Peven : nat -> Prop) (n : nat),
    (oddb n = true -> Podd n) ->
    (oddb n = false -> Peven n) ->
    combine_odd_even Podd Peven n.
Proof.
  intros. unfold combine_odd_even. destruct (oddb n) eqn:E.
  - apply H. reflexivity.
  - apply H0. reflexivity.
Qed.
  

Theorem combine_odd_even_elim_odd :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = true ->
    Podd n.
Proof.
  intros. unfold combine_odd_even in H. rewrite H0 in H. apply H.
Qed.


Theorem combine_odd_even_elim_even :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = false ->
    Peven n.
Proof.
  intros. unfold combine_odd_even in H. rewrite H0 in H. apply H.
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

(*Exercise 5*)
(*tail-recursive version of list reversing*)

Fixpoint rev_append {X} (l1 l2 : list X) : list X :=
  match l1 with
  | [] => l2
  | x :: l1' => rev_append l1' (x :: l2)
  end.

Definition tr_rev {X} (l : list X) : list X :=
  rev_append l [].

Lemma tr_rev_correct : forall X, @tr_rev X = @rev X.
  Proof.
  intros. apply functional_extensionality.
  intros. unfold tr_rev.
  induction x as [|h t].
  - reflexivity.
  - simpl. rewrite <- IHt.
    assert ( H: forall T l1 l2, @rev_append T l1 l2 = @rev_append T l1 [] ++ l2).
    { intros T. induction l1 as [|h' t'].
      - reflexivity.
      - simpl. rewrite IHt'. intros. 
        rewrite (IHt' (h'::l2)).
        rewrite <- app_assoc. reflexivity. }
    apply H.
Qed.



(*Exercise 6*)
(*define tail-recursive version of list length function
and prove that the function is the same as "length" function.*)

Fixpoint tr_length {X} (l: list X) (n:nat) :=
  match l with
  | [] => n
  | h ::t => tr_length t (S n)
end.

Lemma Helper_Func : forall (X:Type) (l: list X) (n:nat),
 S (tr_length l n) = tr_length l (S n).
Proof.
  induction l.
  intros.
  - reflexivity.
  - intros. apply IHl.
Qed.


Theorem Exc_6 : forall (X:Type) (l:list X), length l = tr_length l 0.
Proof.
  intros.
  induction l.
  - reflexivity.
  - simpl. rewrite IHl. apply Helper_Func.
Qed.








