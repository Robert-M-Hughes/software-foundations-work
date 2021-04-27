(*Robert Hughes
Comp 293 Hw 1
This is the document for the first homework for the software reliability class*)


(*Question #1*)
Theorem question_1: forall f:bool -> bool, forall x: bool,
  (f x) = x ->
  f(f x) = x.

Proof.
  intros.
  rewrite H.
  rewrite H.
  reflexivity.
Qed.



(*Question 2*)
Theorem question_2: forall b c : bool,
andb b c =  orb b c ->
b = c.

Proof.
  intros b c.
  destruct b. destruct c.
  reflexivity. simpl.
  intros H1. rewrite H1.
  reflexivity. simpl.
  destruct c. intros H2. rewrite H2. reflexivity. reflexivity.
Qed.

(*Question 3*)
Inductive bin: Type :=
| Zero: bin
| Two: bin -> bin
| Two_one: bin -> bin.


(*Question 4*)
Fixpoint bin_inc(b: bin): bin :=
  match b with
    | Zero => Two_one Zero
    | Two x => Two_one x
    | Two_one x => Two (bin_inc x)
  end.

(*Question 5*)
Fixpoint bin_to_nat (b: bin): nat :=
  match b with
    | Zero => O
    | Two x => (bin_to_nat x) + (bin_to_nat x)
    | Two_one x => S  ((bin_to_nat x) + (bin_to_nat x))
  end.


(*Question 6*)
Theorem bin_to_nat_pres_incr_original : forall b : bin,
  bin_to_nat (bin_inc b) = 1 + (bin_to_nat b).
Proof.
  intros b.
  induction b as [|b'|b2'].
  - reflexivity.
  - reflexivity.
  - simpl.
    rewrite -> IHb2'.
    rewrite -> plus_n_Sm.
    reflexivity.
Qed.

(*Question 7 -- from CA03 *)
Theorem question_7 : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros. induction n as [|n' IHn'].
  reflexivity.
  simpl. rewrite -> IHn'. reflexivity.  Qed.

(*Question 8*)

(*taken from class work*)
Lemma mult_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  intros. induction n as [|n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.  Qed.

Lemma plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
    intros. induction n as [|n' IHn'].
    reflexivity.
    simpl. rewrite -> IHn'. reflexivity.  Qed.

Lemma plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros. induction n as [|n' IHn'].
  reflexivity.
  simpl. rewrite -> IHn'. reflexivity.  Qed.

Lemma plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros. induction n as [|n' IHn'].
  - rewrite <- plus_n_O.
    + reflexivity.
  - simpl. rewrite -> IHn'. rewrite plus_n_Sm. reflexivity.  Qed.

(*This is needed for the communative multiply to work for the second half of the theorem*)
Lemma mult_n_Sm : forall n m:nat, n * m + n = n * S m.
Proof.
  intros. induction n as [| n'].
  reflexivity.
  simpl. rewrite <- IHn'.
  simpl. rewrite -> plus_n_Sm. rewrite -> plus_n_Sm. 
  rewrite -> plus_assoc. reflexivity.
Qed.

Theorem question_8 : forall n m : nat,
  n * m = m * n.
Proof.
  intros n m. induction m as [|m' IHm'].
  simpl. rewrite mult_0_r. reflexivity.
  simpl. rewrite <- mult_n_Sm. rewrite <- plus_comm.
  rewrite -> IHm'. reflexivity. Qed.


(*Question 9*)
(*From class work*)
Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.

Theorem question_9 : forall n : nat,
  leb n n = true.
Proof.
  intros. induction n as [| n'].
  simpl. reflexivity.
  simpl. rewrite IHn'. reflexivity.
Qed.
  


(*Question 10*)
Theorem question_10 : forall b : bool,
  andb b false = false.
Proof.
  intros. destruct b. simpl.
  reflexivity. simpl. reflexivity. Qed.


(*Question 11*)
Theorem question_11: forall n m p: nat,
leb n m = true ->
leb (p + n) (p + m) = true.
Proof.
  intros. induction p as [|p' IHp'].
  - simpl. rewrite H. reflexivity.
  - simpl. rewrite IHp'. reflexivity.
Qed.


(*Question 12*)
Lemma plus_n_O : forall n:nat, n = n + 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *)    reflexivity.
  - (* n = S n' *) simpl. rewrite <- IHn'. reflexivity.  Qed.

Theorem question_12: forall n : nat,
  1 * n = n.
Proof.
  intros. induction n as [| n'].
  reflexivity.
  simpl. rewrite plus_n_O. reflexivity.  Qed.


(*Question 13*)
Theorem question_13: forall x y: bool,
orb (andb x y ) (orb (negb x) (negb y)) = true.
Proof.
 intros. destruct x.
  - destruct y.
    + reflexivity.
    + reflexivity.
  - reflexivity.
Qed.



(*Question 14*)

Theorem question_14 : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  intros. induction n as [| n'].
  reflexivity.
  simpl. rewrite IHn'. rewrite plus_assoc. reflexivity.  Qed.


(*Question 15*)

Theorem question_15 : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  intros. induction n as [| n'].
  reflexivity.
  simpl. rewrite IHn'. rewrite question_14. reflexivity.
Qed.


(*Question 16*)

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Fixpoint half (n : nat) : nat :=
    match n with
      | O => O
      | S O => O
      | S (S n) => S (half n)
    end.


Theorem question_16 : forall n : nat,
  half(double(n)) = n.
Proof.
  intros.
  induction n as [| n'].
  - reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.
  



















