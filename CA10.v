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

Theorem silly1 : forall (n m o p : nat),
     n = m  ->
     [n;o] = [n;p] ->
     [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  rewrite <- eq1.
  apply eq2.  Qed.

Theorem silly2 : forall (n m o p : nat),
     n = m  ->
     (forall (q r : nat), q = r -> [q;o] = [r;p]) ->
     [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2. apply eq1.  Qed.

Theorem silly2a : forall (n m : nat),
     (n,n) = (m,m)  ->
     (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
     [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2. apply eq1.  Qed.

Theorem silly_ex :
     (forall n, evenb n = true -> oddb (S n) = true) ->
     evenb 3 = true ->
     oddb 4 = true.

Proof. 
  intros.
  apply H. apply H0.
  Qed.

Theorem silly3_firsttry : forall (n : nat),
     true = eqb n 5  ->
     eqb (S (S n)) 7 = true.
Proof.
  intros n H.
  symmetry.
  simpl.
  apply H.  Qed.

Theorem rev_exercise1 : forall (l l' : list nat),
     l = rev l' ->
     l' = rev l.
Proof.
  intros.
  rewrite H.
  symmetry.
  apply rev_involutive.
  Qed.

Example trans_eq_example : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  rewrite -> eq1. rewrite -> eq2. reflexivity.  Qed.

Theorem trans_eq : forall (X:Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2. rewrite -> eq1. rewrite -> eq2.
  reflexivity.  Qed.

Example trans_eq_example' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  apply trans_eq with (m:=[c;d]).
  apply eq1. apply eq2.   Qed.

Example trans_eq_exercise : forall (n m o p : nat),
     m = (minustwo o) ->
     (n + p) = m ->
     (n + p) = (minustwo o).
Proof.
  intros.
  apply trans_eq with m.
  apply H0. apply H.
  Qed.

Theorem S_injective : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H.
  inversion H.
  reflexivity.
Qed.

Theorem inversion_ex1 : forall (n m o : nat),
  [n; m] = [o; o] ->
  [n] = [m].
Proof.
  intros n m o H. inversion H. reflexivity. Qed.

Theorem inversion_ex2 : forall (n m : nat),
  [n] = [m] ->
  n = m.
Proof.
  intros n m H. inversion H as [Hnm]. reflexivity.  Qed.

Example inversion_ex3 : forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j ->
  y :: l = x :: j ->
  x = y.
Proof.
  intros.
  inversion H.
  inversion H0.
  symmetry.
  apply H2.
  Qed.

Theorem beq_nat_0_l : forall n,
   eqb 0 n = true -> n = 0.
Proof.
  intros n.
  destruct n as [| n'].
  - (* n = 0 *)
    intros H. reflexivity.
  - (* n = S n' *)
    simpl.
    intros H. inversion H. Qed.

Theorem inversion_ex4 : forall (n : nat),
  S n = O ->
  2 + 2 = 5.
Proof.
  intros n contra. inversion contra. Qed.

Theorem inversion_ex5 : forall (n m : nat),
  false = true ->
  [n] = [m].
Proof.
  intros n m contra. inversion contra. Qed.

Example inversion_ex6 : forall (X : Type)
                          (x y z : X) (l j : list X),
  x :: y :: l = [] ->
  y :: l = z :: j ->
  x = z.
Proof.
  intros.
  inversion H.
  Qed.

Theorem f_equal : forall (A B : Type) (f: A -> B) (x y: A),
  x = y -> f x = f y.
Proof. intros A B f x y eq. rewrite eq.  reflexivity.  Qed.

Theorem S_inj : forall (n m : nat) (b : bool),
     eqb (S n) (S m) = b  ->
     eqb n m = b.
Proof.
  intros n m b H. simpl in H. apply H.  Qed.

Theorem silly3' : forall (n : nat),
  (eqb n 5 = true -> eqb (S (S n)) 7 = true) ->
  true = eqb n 5  ->
  true = eqb (S (S n)) 7.
Proof.
  intros n eq H.
  symmetry in H. apply eq in H. symmetry in H.
  apply H.  Qed.

Theorem plus_n_n_injective : forall n m,
     n + n = m + m ->
     n = m.
Proof.
  intros n. induction n as [| n'].
  (* FILL IN HERE *)
  - simpl. intros.
    destruct m.
    + reflexivity.
    +  simpl in H. inversion H.
  - simpl. destruct m.
    + simpl. intros. inversion H.
    + simpl. intros. inversion H.
      rewrite plus_comm in H1.
      symmetry in H1.
      rewrite plus_comm in H1.
      simpl in H1.
      inversion H1.
      symmetry in H2.
      apply IHn' in H2.
      rewrite H2.
      reflexivity.
  Qed.


Theorem example1:
  forall p q r,
  (p -> q -> r) -> p -> q -> r.

Proof.
  intros. apply X. apply X0. apply X1. Qed.

Theorem example2:
  forall p q r,
  (p -> q -> r) -> p -> q -> r.

Proof.
  intros. apply X in X0. apply X0. apply X1. Qed.

Theorem length_nil:
  forall (X: Type) (l: list X),
  l = [] -> length l = 0.

Proof.
  intros.
  destruct l.
  - reflexivity.
  - inversion H.
  Qed.

Theorem xxx :
  forall (X: Type) (l t: list X) (h: X),
  l = h :: t -> leb 1 (length l) = true.

Proof.
  intros.
  induction l.
  - inversion H.
  - reflexivity.
  Qed.


(*New Session*)
Theorem double_injective_FAILED : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n m. induction n as [| n'].
  - (* n = O *) simpl. intros eq. destruct m as [| m'].
    + (* m = O *) reflexivity.
    + (* m = S m' *) inversion eq.
  - (* n = S n' *) intros eq. destruct m as [| m'].
    + (* m = O *) inversion eq.
    + (* m = S m' *) apply f_equal.
      Abort.


Theorem double_injective : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n. induction n as [| n'].
  - (* n = O *) simpl. intros m eq. destruct m as [| m'].
    + (* m = O *) reflexivity.
    + (* m = S m' *) inversion eq.

  - (* n = S n' *) simpl.
    intros m eq.
    destruct m as [| m'].
    + (* m = O *) simpl.
      inversion eq.
    + (* m = S m' *)
      apply f_equal.
      apply IHn'. inversion eq. reflexivity. Qed.

(*Exerocise 1*)
Theorem beq_nat_true : forall n m,
    eqb n m = true -> n = m.
Proof.
  intros n. induction n.
  - intros m H. destruct m. reflexivity. inversion H.
  - intros. destruct m. inversion H. simpl in H. apply f_equal. apply IHn in H. apply H. Qed.


Theorem double_injective_take2_FAILED : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n m. induction m as [| m'].
  - (* m = O *) simpl. intros eq. destruct n as [| n'].
    + (* n = O *) reflexivity.
    + (* n = S n' *) inversion eq.
  - (* m = S m' *) intros eq. destruct n as [| n'].
    + (* n = O *) inversion eq.
    + (* n = S n' *) apply f_equal.
Abort.

Theorem double_injective_take2 : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n m.
  generalize dependent n.
  induction m as [| m'].
  - (* m = O *) simpl. intros n eq. destruct n as [| n'].
    + (* n = O *) reflexivity.
    + (* n = S n' *) inversion eq.
  - (* m = S m' *) intros n eq. destruct n as [| n'].
    + (* n = O *) inversion eq.
    + (* n = S n' *) apply f_equal.
      apply IHm'. inversion eq. reflexivity. Qed.



Theorem beq_id_true : forall x y,
  eqb_id x y = true -> x = y.
Proof.
  intros [m] [n]. simpl. intros H.
  assert (H' : m = n). { apply beq_nat_true. apply H. }
  rewrite H'. reflexivity.
Qed.


(*Exercise 2*)
Theorem nth_error_after_last: forall (n : nat) (X : Type) (l : list X),
     length l = n ->
     nth_error l n = None.
Proof.
  intros. generalize dependent n. induction l as [|t IHT].
  - reflexivity.
  - intros. rewrite <- H. simpl. apply IHIHT. reflexivity. Qed.


Definition square n := n * n.

Lemma square_mult : forall n m, square (n * m) = square n * square m.
Proof.
  intros n m.
  simpl.
  unfold square.
  rewrite mult_assoc.
  assert (H : n * m * n = n * n * m).
  { rewrite mult_comm. apply mult_assoc. }
  rewrite H. rewrite mult_assoc. reflexivity.
Qed.

Definition foo (x: nat) := 5.

Fact silly_fact_1 : forall m, foo m + 1 = foo (m + 1) + 1.
Proof.
  intros m.
  simpl.
  reflexivity.
Qed.

Definition bar x :=
  match x with
  | O => 5
  | S _ => 5
  end.

Fact silly_fact_2_FAILED : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  simpl. (* Does nothing! *)
Abort.

Fact silly_fact_2 : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  destruct m.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Fact silly_fact_2' : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  unfold bar.
  destruct m.
  - reflexivity.
  - reflexivity.
Qed.

Definition sillyfun (n : nat) : bool :=
  if eqb n 3 then false
  else if eqb n 5 then false
  else false.

Theorem sillyfun_false : forall (n : nat),
  sillyfun n = false.
Proof.
  intros n. unfold sillyfun.
  destruct (eqb n 3).
    - (* beq_nat n 3 = true *) reflexivity.
    - (* beq_nat n 3 = false *) destruct (eqb n 5).
      + (* beq_nat n 5 = true *) reflexivity.
      + (* beq_nat n 5 = false *) reflexivity.  Qed.


(*Exercise 3*)
Fixpoint split {X Y : Type} (l : list (X*Y))
               : (list X) * (list Y) :=
  match l with
  | [] => ([], [])
  | (x, y) :: t =>
      match split t with
      | (lx, ly) => (x :: lx, y :: ly)
      end
  end.


Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof.
   intros X Y l .
  induction l as [| p l'] .  
  - intros l1 l2 H. inversion H. reflexivity.
  - intros l1 l2 H. inversion H. destruct p as [x y]; destruct (split l') as [xs' ys'];
  inversion H1. simpl. rewrite IHl'. reflexivity. reflexivity. Qed.


Definition sillyfun1 (n : nat) : bool :=
  if eqb n 3 then true
  else if eqb n 5 then true
  else false.

Theorem sillyfun1_odd_FAILED : forall (n : nat),
     sillyfun1 n = true ->
     oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (eqb n 3).
  (* stuck... *)
Abort.

Theorem sillyfun1_odd : forall (n : nat),
     sillyfun1 n = true ->
     oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (eqb n 3) eqn:Heqe3.
    - (* e3 = true *) apply beq_nat_true in Heqe3.
      rewrite -> Heqe3. reflexivity.
    - (* e3 = false *)
      destruct (eqb n 5) eqn:Heqe5.
        + (* e5 = true *)
          apply beq_nat_true in Heqe5.
          rewrite -> Heqe5. reflexivity.
        + (* e5 = false *) inversion eq.  Qed.

(*Exercise 4*)
Theorem bool_fn_applied_thrice :
  forall (f : bool -> bool) (b : bool),
  f (f (f b)) = f b.
Proof.
  intros f b. destruct (f b) eqn:Hyp_bool.
  - destruct b .
    + rewrite Hyp_bool. apply Hyp_bool.
    + destruct (f true) eqn:Hyp_true.
      { rewrite Hyp_true. reflexivity. }
      { apply Hyp_bool. }
  - destruct b .
    + destruct (f false) eqn:Hyp_false.
      { apply Hyp_bool. }
      { apply Hyp_false. }
    + rewrite Hyp_bool. apply Hyp_bool.
Qed.


(*Exercise 5*)
Theorem beq_nat_sym : forall (n m : nat),
  eqb n m = eqb m n.
Proof.
  intros n m. generalize dependent m. induction n as [| n'].
  - simpl. induction m.
    + reflexivity.
    + reflexivity.
  - simpl. induction m.
    + reflexivity.
    + apply IHn'.
Qed.


(*Exercise 6*)
Theorem beq_nat_trans : forall n m p,
  eqb n m = true ->
  eqb m p = true ->
  eqb n p = true.
Proof.
    intros.
  destruct n as [| n'].
  - apply beq_nat_true in H.
    rewrite <- H in H0.
    apply beq_nat_true in H0.
    rewrite <- H0.
    reflexivity.
  - apply beq_nat_true in H.
    rewrite <- H in H0.
    apply H0.
Qed.



(*Exercise 7*)
(** We proved, in an exercise above, that for all lists of pairs,
    [combine] is the inverse of [split].  How would you formalize the
    statement that [split] is the inverse of [combine]?  When is this
    property true?

    Complete the definition of [split_combine_statement] below with a
    property that states that [split] is the inverse of
    [combine]. Then, prove that the property holds. (Be sure to leave
    your induction hypothesis general by not doing [intros] on more
    things than necessary.  Hint: what property do you need of [l1]
    and [l2] for [split] [combine l1 l2 = (l1,l2)] to be true?) *)

Definition split_combine_statement : Prop :=
  forall (X: Type) (l1 l2: list X),
    length l1 = length l2 ->
    split (combine l1 l2) = (l1, l2).

Theorem split_combine : split_combine_statement.
Proof.
 intros X l1.
  induction l1 as [| h1 t1 IH1].
  - intros.
    simpl.
    destruct l2 as [| h2 t2].
    + reflexivity.
    + inversion H.
  - intros.
    inversion H.
    destruct l2 as [| h2 t2].
    + inversion H1.
    + inversion H1.
      apply IH1 in H2.
      simpl.
      rewrite -> H2.
      reflexivity.
Qed.

(*Exercise 8*)
Theorem filter_exercise : forall (X : Type) (test : X -> bool)
                             (x : X) (l lf : list X),
     filter test l = x :: lf ->
     test x = true.
Proof.
   intros.
  generalize dependent lf.
  induction l as [| h t IH].
  - intros.
    simpl in H.
    inversion H.
  - intros.
    generalize dependent H.
    destruct lf as [| hf tf].
    + simpl.
      intros.
      destruct (test h) eqn:testH.
      * inversion H.
        rewrite -> H1 in testH.
        apply testH.
      * apply IH in H.
        apply H.
    + simpl.
      intros.
      destruct (test h) eqn:testH.
      * inversion H.
        rewrite -> H1 in testH.
        apply testH.
      * apply IH in H.
        apply H.
Qed.


(*Exercise 9*)
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


Fixpoint forallb {X: Type} (func: X -> bool) (l: list X) : bool :=
  match l with
  | [] => true
  | h :: t => (func h) && (forallb func t)
  end.

Example forall1: forallb oddb [1;3;5;7;9] = true.
Proof. reflexivity. Qed.

Example forall2: forallb negb [false;false] = true.
Proof. reflexivity. Qed.

Example forall3: forallb evenb [0;2;4;5] = false.
Proof. reflexivity. Qed.

Example forall4: forallb (eqb 5) [] = true.
Proof. reflexivity. Qed.


Fixpoint existsb {X: Type} (func: X -> bool) (l: list X) : bool :=
  match l with
  | [] => false
  | h :: t => (func h) || (existsb func t)
  end.

Example exists1: existsb (eqb 5) [0;2;3;6] = false.
Proof. reflexivity. Qed.

Example exists1': existsb (andb true) [true;true;false] = true.
Proof. reflexivity. Qed.

Example exists1'': existsb oddb [1;0;0;0;0;3] = true.
Proof. reflexivity. Qed.

Example exists1''': existsb evenb [] = false.
Proof. reflexivity. Qed.

Definition existsb' {X: Type} (test: X -> bool) (l: list X) :=
  negb (forallb (fun a => negb (test a)) l).

Theorem existsb_existsb': forall (X: Type) (func: X -> bool) (l: list X),
  existsb func l = existsb' func l.
Proof.
  intros.
  unfold existsb.
  unfold existsb'.
  induction l as [| h t IH].
  - simpl. reflexivity.
  - simpl.
    destruct (func h) eqn:testH.
    + simpl. reflexivity.
    + simpl. apply IH.
Qed.
