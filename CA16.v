From LF Require Export Logic.
From LF Require Export Basics.
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

(*Exercise 1*)
Theorem ev_double : forall n,
  ev (double n).
Proof.
  intros. unfold double.
  induction n as [|n'].
  - apply ev_0.
  - apply ev_SS. apply IHn'.
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

(*Exercise 2*)
Theorem SSSSev__even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  intros. inversion H. inversion H1. apply H3.
Qed.


(*Exercise 3*)
Theorem even5_nonsense :
  ev 5 -> 2 + 2 = 9.
Proof.
  intros. simpl. exfalso.
  inversion H. inversion H1. inversion H3.
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

(*Exercise 4*)
Theorem ev_sum : forall n m, ev n -> ev m -> ev (n + m).
Proof.
  intros n m In Im. induction In.
  - simpl. apply Im.
  - simpl. apply ev_SS. apply IHIn.
Qed.


(*Exercise 5*)
Inductive ev' : nat -> Prop :=
| ev'_0 : ev' 0
| ev'_2 : ev' 2
| ev'_sum : forall n m, ev' n -> ev' m -> ev' (n + m).

Theorem ev'_ev : forall n, ev' n <-> ev n.
Proof.
  intros. split.
  - intros. induction H.
    + apply ev_0.
    + apply ev_SS. apply ev_0.
    + apply ev_sum. apply IHev'1. apply IHev'2.
  - intros. induction H.
    + apply ev'_0.
    + apply (ev'_sum 2).
      * apply ev'_2.
      * apply IHev.
Qed.

(*Exercise 6*)
Theorem ev_ev__ev : forall n m,
  ev (n+m) -> ev n -> ev m.
Proof.
  intros. induction H0.
  simpl in H. apply H. apply IHev.
  simpl in H. inversion H. apply H2.
Qed.
  
  
Lemma helper_ex7: forall n, ev(n + n).
Proof.
intros. induction n. simpl. apply ev_0.
 simpl. rewrite <- plus_n_Sm. apply ev_SS. apply IHn.
Qed. 

(*Exercise 7*)
Theorem ev_plus_plus : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
intros.
  apply ev_ev__ev with (n:=(n+n)).
  - rewrite <- plus_assoc.
    rewrite plus_assoc with (m:=m).
    rewrite plus_comm.
    rewrite <- plus_assoc.
    rewrite plus_comm with (n:= p).
    apply ev_sum. apply H. apply H0.
  - apply helper_ex7. Qed.

Lemma helper: ev 1.
  Proof. apply (ev_sum 1). Admitted.

(*Exercise 8*)
Theorem ex_mid_ev:
  forall n, ev n \/ ~ ev n.

Proof.
  intros. assert (helper: (forall n, if evenb n then ev n else ~ ev n)).
  { intros.  destruct n0. simpl. apply ev_0. 
    
}Admitted.


(*Exercise 9*)
Theorem ev_n_not_ev_Sn:
  forall n,
  ev n -> ~ ev (S n).

Proof.
  intros. unfold not. destruct n. 
Admitted.



