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
  3 <= 6.
Proof.
  (* WORKED IN CLASS *)
  apply le_S. apply le_S. apply le_S. apply le_n.  Qed.

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

Inductive total_relation: nat -> nat -> Prop :=
  | totrel: forall n m, total_relation n m.

Example tot_rel_example:
  total_relation 3 5.

Proof. constructor. Qed.


Inductive empty_relation: nat -> nat -> Prop :=.

Theorem not_exist_in_empty_rel:
  ~ (exists n m, empty_relation n m).
Proof.
  unfold not.
  intros.
  inversion H.
  inversion H0.
  inversion H1.
  Qed.


Lemma Sn_le_m__n_le_m:
  forall n m,
  S n <= m -> n <= m.

Proof.
  intros.
  induction H.
  - constructor. constructor.
  - constructor. assumption.
  Qed.

Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  (* FILL IN HERE *)
  intros.
  induction H.
  - assumption.
  - apply IHle. apply Sn_le_m__n_le_m.
    assumption.
  Qed.

Theorem O_le_n : forall n,
  0 <= n.
Proof.
  (* FILL IN HERE *)
  induction n.
  - constructor.
  - constructor. assumption.
  Qed.

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
  (* FILL IN HERE *)
  intros.
  induction H.
  - constructor.
  - constructor. assumption.
  Qed.


Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
  (* FILL IN HERE *) 
  intros. inversion H.
  - constructor.
  - apply Sn_le_m__n_le_m. assumption.
  Qed.

Theorem le_plus_l : forall a b,
  a <= a + b.
Proof.
  (* FILL IN HERE *)
  induction a.
  - simpl. apply O_le_n.
  - intros. simpl. apply n_le_m__Sn_le_Sm. 
    apply IHa.
  Qed.

Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof.
 unfold lt.
 (* FILL IN HERE *)
 intros.
 induction H.
 - split.
   + apply n_le_m__Sn_le_Sm. apply le_plus_l.
   + apply n_le_m__Sn_le_Sm. rewrite plus_comm. apply le_plus_l.
 - destruct IHle. split.
   + constructor. assumption.
   + constructor. assumption.
 Qed.

Theorem lt_S : forall n m,
  n < m ->
  n < S m.
Proof.
  (* FILL IN HERE *)
  unfold lt.
  intros. constructor. assumption.
  Qed.

Theorem leb_complete : forall n m,
  leb n m = true -> n <= m.
Proof.
  (* FILL IN HERE *)
  induction n.
  - intros. apply O_le_n.
  - intros. simpl in H. destruct m.
    + inversion H.
    + apply n_le_m__Sn_le_Sm.
      apply IHn. apply H.
  Qed.

Theorem leb_correct : forall n m,
  n <= m ->
  leb n m = true.
Proof.
  (* FILL IN HERE *)
  intros.
  generalize dependent n.
  induction m.
  - intros. inversion H. reflexivity.
  - intros. inversion H.
    + rewrite <- leb_refl. reflexivity.
    + destruct n.
      * reflexivity.
      * simpl. apply IHm. apply Sn_le_Sm__n_le_m. assumption.
  Qed.

Theorem leb_iff : forall n m,
  leb n m = true <-> n <= m.
Proof.
  intros.
  split. apply leb_complete. apply leb_correct.
  Qed.


Theorem leb_true_trans : forall n m o,
  leb n m = true -> leb m o = true -> leb n o = true.
Proof.
  (* FILL IN HERE *)
  intros.
  rewrite leb_iff in H.
  rewrite leb_iff in H0.
  rewrite leb_iff.
  apply le_trans with m.
  assumption.
  assumption.
  Qed.



(*New Session*)

Inductive reg_exp {T : Type} : Type :=
| EmptySet : reg_exp
| EmptyStr : reg_exp
| Char : T -> reg_exp
| App : reg_exp -> reg_exp -> reg_exp
| Union : reg_exp -> reg_exp -> reg_exp
| Star : reg_exp -> reg_exp.


Inductive exp_match {T} : list T -> @reg_exp T -> Prop :=
| MEmpty : exp_match [] EmptyStr
| MChar : forall (x: T), exp_match [x] (Char x)
| MApp : forall s1 re1 s2 re2,
           exp_match s1 re1 ->
           exp_match s2 re2 ->
           exp_match (s1 ++ s2) (App re1 re2)
| MUnionL : forall s1 re1 re2,
              exp_match s1 re1 ->
              exp_match s1 (Union re1 re2)
| MUnionR : forall re1 s2 re2,
              exp_match s2 re2 ->
              exp_match s2 (Union re1 re2)
| MStar0 : forall re, exp_match [] (Star re)
| MStarApp : forall s1 s2 re,
               exp_match s1 re ->
               exp_match s2 (Star re) ->
               exp_match (s1 ++ s2) (Star re).

Notation "s =~ re" := (exp_match s re) (at level 80).


Example reg_exp_ex1 : [1] =~ Char 1.
Proof.
  apply MChar.
Qed.

Example reg_exp_ex2 : [1; 2] =~ App (Char 1) (Char 2).
Proof. 
  apply (MApp [1] _ [2]).
  - apply MChar.
  - apply MChar.
Qed.

Example reg_exp_ex3 : ~ ([1; 2] =~ Char 1).
Proof.
  intros H. inversion H.
Qed.

Fixpoint reg_exp_of_list {T} (l : list T) :=
  match l with
  | [] => EmptyStr
  | x :: l' => App (Char x) (reg_exp_of_list l')
  end.

Compute reg_exp_of_list [1;2;3].

Example reg_exp_ex4 : [1; 2; 3] =~ reg_exp_of_list [1; 2; 3].
Proof.
  simpl. apply (MApp [1]).
  { apply MChar. }
  apply (MApp [2]).
  { apply MChar. }
  apply (MApp [3]).
  { apply MChar. }
  apply MEmpty.
Qed.

Lemma MStar1 :
  forall T s (re : @reg_exp T) ,
    s =~ re ->
    s =~ Star re.
Proof.
  intros T s re H. Check app_nil_r.
  rewrite <- (app_nil_r _ s).
  apply (MStarApp s [] re).
  - apply H.
  - apply MStar0.
Qed.

(*Exercise 1*)
Lemma empty_is_empty : forall T (s : list T),
  ~ (s =~ EmptySet).
Proof.
  intros t s H. inversion H.
Qed.

(*Exercise 2*)
Lemma MUnion' : forall T (s : list T) (re1 re2 : @reg_exp T),
  s =~ re1 \/ s =~ re2 ->
  s =~ Union re1 re2.
Proof.
  intros T s re1 re2 [match1 | match2].
  - constructor. assumption.
  - apply MUnionR. assumption.
Qed.

(*Exercise 3*)
Lemma MStar' : forall T (ss : list (list T)) (re : reg_exp),
  (forall s, In s ss -> s =~ re) ->
  fold app ss [] =~ Star re.
Proof.
   intros T ss re H.
    induction ss as [| a t IH].
    - simpl. apply MStar0.
    - simpl. apply MStarApp.
    apply H. simpl. left. reflexivity.
    apply IH. intros. apply H. simpl. right. assumption.
Qed.

(*Exercise 4*)

Lemma Helper: forall S (x:S) y, [x]++y = x::y.
      Proof.
  intros S x y. simpl. reflexivity. 
Qed. 

Lemma reg_exp_of_list_spec : forall T (s1 s2 : list T),
  s1 =~ reg_exp_of_list s2 <-> s1 = s2.
Proof.
  intros T s1 s2.
  generalize dependent s1.
  induction s2 as [|h t].
    split. 
    + intros H. simpl in H. inversion H. reflexivity.
    + intros H. simpl. rewrite H. apply MEmpty.
    + intros s1. split. 
     intros H. simpl in H. inversion H. 
      inversion H3. simpl. 
      rewrite (IHt s2) in H4. rewrite H4. reflexivity.
     intros H. simpl. rewrite H.
      rewrite <- Helper. apply MApp.
      * apply MChar.
      * apply IHt. reflexivity.
Qed.

Fixpoint re_chars {T} (re : reg_exp) : list T :=
  match re with
  | EmptySet => []
  | EmptyStr => []
  | Char x => [x]
  | App re1 re2 => re_chars re1 ++ re_chars re2
  | Union re1 re2 => re_chars re1 ++ re_chars re2
  | Star re => re_chars re
  end.

Compute re_chars (Union (Char 5) (App (Char 3) (EmptyStr))). (* 5 + 3\epsilon *)

Theorem in_re_match : forall T (s : list T) (re : reg_exp) (x : T),
  s =~ re ->
  In x s ->
  In x (re_chars re).
Proof.
  intros T s re x Hmatch Hin.
  induction Hmatch
    as [| x'
        | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
        | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
        | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2].
  (* WORKED IN CLASS *)
  - (* MEmpty *)
    inversion Hin.
  - (* MChar *)
    inversion Hin. simpl. left. assumption.
    inversion H.
  - (*MApp*) simpl. Check In_app_iff.
    rewrite In_app_iff in *.
    destruct Hin as [Hin | Hin].
    + (* In x s1 *)
      left. apply (IH1 Hin).
    + (* In x s2 *)
      right. apply IH2. apply Hin.
  - (* MUnionL *)
    simpl. rewrite In_app_iff.
    left. apply (IH Hin).
  - (* MUnionR *)
    simpl. rewrite In_app_iff.
    right. apply (IH Hin).
  - (* MStar0 *)
    destruct Hin.
  - (* MStarApp *)
    simpl. rewrite In_app_iff in Hin.
    destruct Hin as [Hin | Hin].
    + (* In x s1 *)
      apply (IH1 Hin).
    + (* In x s2 *)
      simpl in IH2.
      apply (IH2 Hin).
Qed.



Lemma star_app: forall T (s1 s2 : list T) (re : @reg_exp T),
  s1 =~ Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.
  generalize dependent s2.
  induction H1
    as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
        |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].

  - (* MEmpty *)
    simpl. intros. apply H.

  - simpl. intros. (* MChar. Stuck... *)
Abort.

Lemma star_app: forall T (s1 s2 : list T) (re re' : reg_exp),
  re' = Star re ->
  s1 =~ re' ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.


Proof. intros. induction H0.
Abort.


Lemma star_app: forall T (s1 s2 : list T) (re : reg_exp),
  s1 =~ Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.
  remember (Star re) as re'.
  generalize dependent s2.
  induction H1
    as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
        |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].

(** The [Heqre'] is contradictory in most cases, which allows us to
    conclude immediately. *)

  - (* MEmpty *)  inversion Heqre'.
  - (* MChar *)   inversion Heqre'.
  - (* MApp *)    inversion Heqre'.
  - (* MUnionL *) inversion Heqre'.
  - (* MUnionR *) inversion Heqre'.
  - (* MStar0 *)
    inversion Heqre'. intros s H. apply H.
  - (* MStarApp *)
    inversion Heqre'. (*rewrite H0 in IH2, Hmatch1.*)
    intros s2 H1. Check app_assoc.
    rewrite <- app_assoc.
    apply MStarApp.
    + rewrite H0 in Hmatch1. apply Hmatch1. 
    + rewrite H0 in IH2. apply IH2.
      * reflexivity.
      * apply H1.
Qed.

Lemma beq_nat_true_iff : forall x y, eqb x y = true <-> x=y.
Proof. split. apply eqb_true. intros; subst; symmetry; apply eqb_refl. Qed.


Theorem filter_not_empty_In : forall n l,
  filter (eqb n) l <> [] ->
  In n l.
Proof.
  intros n l. induction l as [|m l' IHl'].
  - (* l = [] *)
    simpl. intros H. apply H. reflexivity.
  - (* l = m :: l' *)
    simpl. destruct (eqb n m) eqn:H.
    + (* beq_nat n m = true *)
      intros _. Check beq_nat_true_iff.
      rewrite beq_nat_true_iff in H. rewrite H.
      left. reflexivity.
    + (* beq_nat n m = false *)
      intros H'. right. apply (IHl' H').
Qed.


Inductive reflect (P : Prop) : bool -> Prop :=
| ReflectT : P -> reflect P true
| ReflectF : ~ P -> reflect P false.

Theorem iff_reflect : forall P b, (P <-> b = true) -> reflect P b.
Proof.
  (* WORKED IN CLASS *)
  intros P b H. destruct b.
  - apply ReflectT. rewrite H. reflexivity.
  - apply ReflectF. unfold not. intros. apply H in H0. inversion H0.
Qed.

(*Exercise 5*)
Theorem reflect_iff : forall P b, reflect P b -> (P <-> b = true).
Proof.
  intros. destruct H as [HP | HNP].
  - split. intros. reflexivity. intros. apply HP.
  - split. intros. destruct (HNP H). intros. discriminate.
Qed. 


Lemma beq_natP : forall n m, reflect (n = m) (eqb n m).
Proof.
  intros n m. apply iff_reflect. rewrite beq_nat_true_iff. reflexivity.
Qed.

Theorem filter_not_empty_In' : forall n l,
  filter (eqb n) l <> [] ->
  In n l.
Proof.
  intros n l. induction l as [|m l' IHl'].
  - (* l = [] *)
    simpl. intros H. apply H. reflexivity.
  - (* l = m :: l' *)
    simpl. destruct (beq_natP n m) as [H | H].
    + (* n = m *)
      intros _. rewrite H. left. reflexivity.
    + (* n <> m *)
      intros H'. right. apply IHl'. apply H'.
Qed.

(*Exercise 6: Use beq_natP in the proof.*)
Fixpoint count n l :=
  match l with
  | [] => 0
  | m :: l' => (if eqb n m then 1 else 0) + count n l'
  end.

Theorem beq_natP_practice : forall n l,
  count n l = 0 -> ~(In n l).
Proof.
  intros n l.
  induction l as [| a t IH].
  - simpl. intros _ f. destruct f.
  - simpl. destruct (beq_natP n a) as [H | H].
    + intros H'. discriminate.
    + simpl. intros H1 [H2 | H3].
      * apply H. rewrite H2. reflexivity.
      * apply IH. apply H1. apply H3.
Qed.
