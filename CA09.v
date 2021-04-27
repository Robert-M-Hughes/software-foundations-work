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

(*Exercise 1*)
(** Complete the following proof without using [simpl]. *)
Theorem silly_ex :
     (forall n, evenb n = true -> oddb (S n) = true) ->
     evenb 3 = true ->
     oddb 4 = true.
Proof.
  intros. apply H. apply H0. Qed.

Theorem silly3_firsttry : forall (n : nat),
     true = eqb n 5  ->
     eqb (S (S n)) 7 = true.
Proof.
  intros n H.
  symmetry.
  simpl.
  apply H.  Qed.

(*Exercise 2*)
Theorem rev_exercise1 : forall (l l' : list nat),
     l = rev l' ->
     l' = rev l.
Proof.
  intros. rewrite H. symmetry. apply rev_involutive. Qed.

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

(*Exercise 3*)
Example trans_eq_exercise : forall (n m o p : nat),
     m = (minustwo o) ->
     (n + p) = m ->
     (n + p) = (minustwo o).
Proof.
  intros. rewrite <- H. apply H0. Qed.

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

(*Exercise 4*)
Example inversion_ex3 : forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j ->
  y :: l = x :: j ->
  x = y.
Proof.
  intros. inversion H0. reflexivity. Qed.

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

(*Exercise 5*)
Example inversion_ex6 : forall (X : Type)
                          (x y z : X) (l j : list X),
  x :: y :: l = [] ->
  y :: l = z :: j ->
  x = z.
Proof.
  intros. inversion H. Qed.

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

(*Exercise 6*)
Theorem plus_n_n_injective : forall n m,
     n + n = m + m ->
     n = m.
Proof.
  intros n. induction n as [| n'].
   - simpl. intros m eq. destruct m as [| m'].
    + reflexivity.
    +  inversion eq.
  - simpl. intros m eq.
    destruct m as [| m'].
    + simpl. inversion eq.
    + apply f_equal.
      apply IHn'. inversion eq. rewrite plus_comm in H0. symmetry in H0.
    rewrite plus_comm in H0. simpl in H0. 
    inversion H0. reflexivity. Qed.


(*Exercise 7: Use backward reasoning*)
Theorem example1:
  forall p q r,
  (p -> q -> r) -> p -> q -> r.

Proof.
  intros p q r H. apply H. Qed.
  

(*Exercise 8: Use forward reasoning*)
Theorem example2:
  forall p q r,
  (p -> q -> r) -> p -> q -> r.

Proof.
  intros. apply X in X0. apply X0. apply X1. Qed.

(*Exercise 9: Don't use rewrite!*)
Theorem length_nil:
  forall (X: Type) (l: list X),
  l = [] -> length l = 0.

Proof.
  intros. inversion H. simpl. reflexivity. Qed.

(*Exercise 10: *)
Theorem xxx :
  forall (X: Type) (l t: list X) (h: X),
  l = h :: t -> leb 1 (length l) = true.

Proof.
  intros. inversion H. simpl. reflexivity. Qed.
  






