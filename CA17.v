From LF Require Export Logic.
Require Coq.omega.Omega.

Inductive ev : nat -> Prop :=
| ev_0 : ev 0
| ev_SS : forall n : nat, ev n -> ev (S (S n)).


Check ev_0.
Check ev_SS.

Fail Inductive wrong_ev (n : nat) : Prop :=
| wrong_ev_0 : wrong_ev 0
| wrong_ev_SS : forall n, wrong_ev n -> wrong_ev (S (S n)).
(* ===> Error: A parameter of an inductive type n is not
        allowed to be used as a bound variable in the type
        of its constructor. *)


Theorem ev_4 : ev 4.
Proof. apply ev_SS. apply ev_SS. apply ev_0. Qed.

Theorem ev_4' : ev 4.
Proof. apply (ev_SS 2 (ev_SS 0 ev_0)). Qed.

Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof.
  intros n. simpl. intros Hn.
  apply ev_SS. apply ev_SS. apply Hn.
Qed.

Theorem ev_double : forall n,
  ev (double n).
Proof.
  intros. induction n.
  - apply ev_0.
  - simpl. apply ev_SS. assumption.
  Qed.


Theorem ev_minus2 : forall n,
  ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  inversion  E as [| n' E'].
  - (* E = ev_0 *) simpl. apply ev_0.
  - (* E = ev_SS n' E' *) simpl. apply E'.  Qed.

Theorem ev_minus2' : forall n,
  ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  destruct E as [| n' E'].
  - (* E = ev_0 *) simpl. apply ev_0.
  - (* E = ev_SS n' E' *) simpl. apply E'.  Qed.

Theorem evSS_ev : forall n,
  ev (S (S n)) -> ev n.

Proof.
  intros n E.
  destruct E as [| n' E'].
  - (* E = ev_0. *)
    (* We must prove that [n] is even from no assumptions! *)
Abort.

Theorem evSS_ev : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E.
  inversion E as [| n' E'].
  (* We are in the [E = ev_SS n' E'] case now. *)
  apply E'.
Qed.

Theorem one_not_even : ~ ev 1.
Proof.
  intros H. inversion H. Qed.

Theorem SSSSev__even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  (* FILL IN HERE *)
  intros.
  inversion H.
  inversion H1.
  assumption.
  Qed.


Theorem even5_nonsense :
  ev 5 -> 2 + 2 = 9.
Proof.
  (* FILL IN HERE *)
  intros. inversion H. inversion H1. inversion H3.
  Qed.

Lemma ev_even_firsttry : forall n,
  ev n -> exists k, n = double k.
Proof.
  intros n E. inversion E as [| n' E'].
  - (* E = ev_0 *)
    exists 0. reflexivity.
  - (* E = ev_SS n' E' *) simpl.
    assert (I : (exists k', n' = double k') ->
                (exists k, S (S n') = double k)).
    { intros [k' Hk']. rewrite Hk'. exists (S k'). reflexivity. }
    apply I. (* reduce the original goal to the new one *)

Admitted.

Lemma ev_even : forall n,
  ev n -> exists k, n = double k.
Proof.
  intros n E.
  induction E as [|n' E' IH].
  - (* E = ev_0 *)
    exists 0. reflexivity.
  - (* E = ev_SS n' E'
       with IH : exists k', n' = double k' *)
    destruct IH as [k' Hk'].
    rewrite Hk'. exists (S k'). reflexivity.
Qed.

Theorem ev_even_iff : forall n,
  ev n <-> exists k, n = double k.
Proof.
  intros n. split.
  - (* -> *) apply ev_even.
  - (* <- *) intros [k Hk]. rewrite Hk. apply ev_double.
Qed.

Theorem ev_sum : forall n m, ev n -> ev m -> ev (n + m).
Proof.
  (* FILL IN HERE *)
  intros.
  induction H.
  - assumption.
  - simpl. apply ev_SS. assumption.
  Qed.


Inductive ev' : nat -> Prop :=
| ev'_0 : ev' 0
| ev'_2 : ev' 2
| ev'_sum : forall n m, ev' n -> ev' m -> ev' (n + m).

Theorem ev'_ev : forall n, ev' n <-> ev n.
Proof.
 (* FILL IN HERE *)
 split.
 - intros. induction H.
   + constructor.
   + constructor. constructor.
   + apply ev_sum. assumption. assumption.
 - intros. induction H.
   + constructor.
   + apply (ev'_sum 2 n).
     constructor.
     assumption.
 Qed.

Theorem ev_ev__ev : forall n m,
  ev (n+m) -> ev n -> ev m.
Proof.
  (* FILL IN HERE *)
  intros.
  induction H0.
  - assumption.
  - simpl in H. apply IHev. apply evSS_ev. assumption.
  Qed.

Theorem ev_plus_plus : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
  (* FILL IN HERE *)
  intros.
  assert (ev ((n + m) + (n + p))).
  {
    apply ev_sum. assumption. assumption.
  }
  rewrite (plus_assoc) in H1.
  rewrite <- (plus_assoc n m n) in H1.
  rewrite (plus_comm m n) in H1.
  rewrite (plus_assoc) in H1.
  rewrite <- double_plus in H1.
  rewrite <- plus_assoc in H1.
  apply (ev_ev__ev (double n) (m+p) H1).
  apply ev_double.
  Qed.


Theorem ex_mid_ev:
  forall n, ev n \/ ~ ev n.

Proof.
  intros.
  assert (ev n <-> evenb n = true).
  {
    rewrite ev_even_iff. rewrite even_bool_prop. reflexivity.
  }
  apply restricted_excluded_middle with (evenb n).
  assumption.
  Qed.

Theorem ev_n_not_ev_Sn:
  forall n,
  ev n -> ~ ev (S n).

Proof.
  unfold not. 
  - intros. induction H.
    + inversion H0.
    + inversion H0. apply IHev. assumption.
  Qed.


(*New Session*)

Module Playground.


Inductive le : nat -> nat -> Prop :=
  | le_n : forall n, le n n
  | le_S : forall n m, (le n m) -> (le n (S m)).

Notation "m <= n" := (le m n).

Theorem test_le1 :
  3 <= 3.
Proof.
  (* WORKED IN CLASS *)
  apply le_n.  Qed.

Theorem test_le2 :
  3 <= 10.
Proof.
  (* WORKED IN CLASS *)
  apply le_S. apply le_S. apply le_S. 
  apply le_S. apply le_S. apply le_S. apply le_S. apply le_n.  Qed.

Theorem test_leb2:
  leb 3 10 = true.

Proof. reflexivity. Qed.

Theorem test_le3 :
  (2 <= 1) -> 2 + 2 = 5.
Proof.
  (* WORKED IN CLASS *)
  intros H. inversion H. inversion H2.  Qed.


End Playground.

Definition lt (n m:nat) := le (S n) m.

Notation "m < n" := (lt m n).

Inductive square_of : nat -> nat -> Prop :=
  | sq : forall n:nat, square_of n (n * n).

Inductive next_nat : nat -> nat -> Prop :=
  | nn : forall n:nat, next_nat n (S n).

Inductive next_even : nat -> nat -> Prop :=
  | ne_1 : forall n, ev (S n) -> next_even n (S n)
  | ne_2 : forall n, ev (S (S n)) -> next_even n (S (S n)).

(*Exercise 1*)
(** Define an inductive binary relation [total_relation] that holds
    between every pair of natural numbers. *)
Inductive total_relation : nat -> nat -> Prop :=
  tot_rel : forall (n m:nat), total_relation n m.

(*Exercise 2*)
(** Define an inductive binary relation [empty_relation] (on numbers)
    that never holds. *)
Inductive empty_relation : nat -> nat -> Prop :=
  empt_rel : empty_relation 0 0.

(*Exercise 3*)
Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  intros. induction H0. apply H. apply le_S. apply IHle.
Qed.

(*Exercise 4*)
Theorem O_le_n : forall n,
  0 <= n.
Proof.
  intros. induction n. reflexivity. apply le_S. apply IHn. 
Qed.

(*Exercise 5*)
Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
  intros. induction H. reflexivity. apply le_S. apply IHle.
Qed.


(*Exercise 6*)
Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
  intros n m. generalize n. clear n. induction m as [|m].
  intros n H. inversion H. apply le_n. inversion H1.
  intros n H. inversion H. apply le_n. apply IHm in H1. apply le_S in H1. apply H1.
Qed.

(*Exercise 7*)
Theorem le_plus_l : forall a b,
  a <= a + b.
Proof.
  intros. induction b. 
  rewrite plus_comm. simpl. apply le_n.
  rewrite plus_comm. simpl. rewrite plus_comm. apply le_S. apply IHb.
Qed.
 
(*Exercise 8*)
Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof.
 unfold lt.
  intros. apply conj.
  induction H. apply n_le_m__Sn_le_Sm. apply le_plus_l. apply le_S. apply IHle.
  induction H. apply n_le_m__Sn_le_Sm. rewrite -> plus_comm. apply le_plus_l. apply le_S. apply IHle.
Qed.

(*Exercise 9*)
Theorem lt_S : forall n m,
  n < m ->
  n < S m.
Proof.
  unfold lt. intros. apply le_S. apply H.
Qed.

(*Exercise 10*)
Theorem leb_complete : forall n m,
  leb n m = true -> n <= m.
Proof.
  intros n. induction n as [|n].
  intros m H. apply O_le_n.
  intros m H. destruct m. simpl in H. inversion H. apply n_le_m__Sn_le_Sm. apply IHn. simpl in H. apply H.
Qed.


(*Exercise 11*)
(** Hint: The next one may be easiest to prove by induction on [m]. *)
Theorem leb_correct : forall n m,
  n <= m ->
  leb n m = true.
Proof.
  intros n m. generalize n. clear n. induction m as [|m].
  intros. inversion H. simpl. reflexivity.
  intros. destruct n. simpl. reflexivity. simpl. apply IHm.
  apply Sn_le_Sm__n_le_m.  apply H.
Qed.

(*Exercise 12*)
Theorem leb_iff : forall n m,
  leb n m = true <-> n <= m.
Proof.
  intros. split. apply leb_complete. apply leb_correct. 
Qed.

(*Exercise 13*)
(** Hint: This theorem can easily be proved without using [induction]. *)
Theorem leb_true_trans : forall n m o,
  leb n m = true -> leb m o = true -> leb n o = true.
Proof.
  intros. apply leb_iff. apply leb_complete in H. apply leb_complete in H0.
  apply le_trans with (n:=m) (m:=n) (o:=o). apply H. apply H0.
Qed.





