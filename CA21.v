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

Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.
Import ListNotations.

From LF Require Import Maps.

Module AExp.


Inductive aexp : Type :=
  | ANum : nat -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.


Fixpoint aeval (a : aexp) : nat :=
  match a with
  | ANum n => n
  | APlus a1 a2 => (aeval a1) + (aeval a2)
  | AMinus a1 a2  => (aeval a1) - (aeval a2)
  | AMult a1 a2 => (aeval a1) * (aeval a2)
  end.

Example test_aeval1:
  aeval (APlus (ANum 2) (ANum 2)) = 4.
Proof. reflexivity. Qed.

Fixpoint beval (b : bexp) : bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => beq_nat (aeval a1) (aeval a2)
  | BLe a1 a2   => leb (aeval a1) (aeval a2)
  | BNot b1     => negb (beval b1)
  | BAnd b1 b2  => andb (beval b1) (beval b2)
  end.

Fixpoint optimize_0plus (a:aexp) : aexp :=
  match a with
  | ANum n =>
      ANum n
  | APlus (ANum 0) e2 =>
      optimize_0plus e2
  | APlus e1 e2 =>
      APlus (optimize_0plus e1) (optimize_0plus e2)
  | AMinus e1 e2 =>
      AMinus (optimize_0plus e1) (optimize_0plus e2)
  | AMult e1 e2 =>
      AMult (optimize_0plus e1) (optimize_0plus e2)
  end.


Example test_optimize_0plus:
  optimize_0plus (APlus (ANum 2)
                        (APlus (ANum 0)
                               (APlus (ANum 0) (ANum 1))))
  = APlus (ANum 2) (ANum 1).
Proof. reflexivity. Qed.

Theorem optimize_0plus_sound: forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a. induction a.
  - (* ANum *) reflexivity.
  - (* APlus *) destruct a1.
    + (* a1 = ANum n *) destruct n.
      * (* n = 0 *)  simpl. apply IHa2.
      * (* n <> 0 *) simpl. rewrite IHa2. reflexivity.
    + (* a1 = APlus a1_1 a1_2 *)
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
    + (* a1 = AMinus a1_1 a1_2 *)
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
    + (* a1 = AMult a1_1 a1_2 *)
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
  - (* AMinus *)
    simpl. rewrite IHa1. rewrite IHa2. reflexivity.
  - (* AMult *)
    simpl. rewrite IHa1. rewrite IHa2. reflexivity.  Qed.


Theorem silly1 : forall ae, aeval ae = aeval ae.
Proof. try reflexivity. (* this just does [reflexivity] *) Qed.

Theorem silly2 : forall (P : Prop), P -> P.
Proof.
  intros P HP.
  try reflexivity. (* just [reflexivity] would have failed *)
  apply HP. (* we can still finish the proof in some other way *)
Qed.


Lemma foo : forall n, leb 0 n = true.
Proof.
  intros.
  destruct n.
    - (* n=0 *) simpl. reflexivity.
    - (* n=Sn' *) simpl. reflexivity.
Qed.


Lemma foo' : forall n, leb 0 n = true.
Proof.
  intros.
  (* [destruct] the current goal *)
  destruct n;
  (* then [simpl] each resulting subgoal *)
  simpl;
  (* and do [reflexivity] on each resulting subgoal *)
  reflexivity.
Qed.

Theorem optimize_0plus_sound': forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a.
  induction a;
    (* Most cases follow directly by the IH... *)
    try (simpl; rewrite IHa1; rewrite IHa2; reflexivity).
    (* ... but the remaining cases -- ANum and APlus --
       are different: *)
  - (* ANum *) reflexivity.
  - (* APlus *)
    destruct a1;
      (* Again, most cases follow directly by the IH: *)
      try (simpl; simpl in IHa1; rewrite IHa1;
           rewrite IHa2; reflexivity).
    (* The interesting case, on which the [try...]
       does nothing, is when [e1 = ANum n]. In this
       case, we have to destruct [n] (to see whether
       the optimization applies) and rewrite with the
       induction hypothesis. *)
    + (* a1 = ANum n *) destruct n;
      simpl; rewrite IHa2; reflexivity.   Qed.


Theorem optimize_0plus_sound'': forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a.
  induction a;
    (* Most cases follow directly by the IH *)
    try (simpl; rewrite IHa1; rewrite IHa2; reflexivity);
    (* ... or are immediate by definition *)
    try reflexivity.
  (* The interesting case is when a = APlus a1 a2. *)
  - (* APlus *)
    destruct a1; try (simpl; simpl in IHa1; rewrite IHa1;
                      rewrite IHa2; reflexivity).
    + (* a1 = ANum n *) destruct n;
      simpl; rewrite IHa2; reflexivity. Qed.


Theorem In10 : In 10 [1;2;3;4;5;6;7;8;9;10].
Proof.
  repeat (try (left; reflexivity); right).
Qed.


Theorem In10' : In 10 [1;2;3;4;5;6;7;8;9;10].
Proof.
  repeat (left; reflexivity).
  repeat (right; try (left; reflexivity)).
Qed.


Fixpoint optimize_0plus_b (b : bexp) : bexp :=
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *)
  match b with
  | BEq a1 a2 => BEq (optimize_0plus a1) (optimize_0plus a2)
  | BLe a1 a2 => BLe (optimize_0plus a1) (optimize_0plus a2)
  | BNot b' => BNot (optimize_0plus_b b')
  | BAnd b1 b2 => BAnd (optimize_0plus_b b1) (optimize_0plus_b b2)
  | _ => b
  end.

Theorem optimize_0plus_b_sound : forall b,
  beval (optimize_0plus_b b) = beval b.
Proof.
  (* FILL IN HERE *)
  intros.
  induction b;
    try (simpl; reflexivity);
    try (simpl; rewrite optimize_0plus_sound; 
         rewrite optimize_0plus_sound; reflexivity).
    simpl. rewrite IHb. reflexivity.
    simpl. rewrite IHb1. rewrite IHb2. reflexivity.
  Qed.


Tactic Notation "simpl_and_try" tactic(c) :=
  simpl;
  try c.


Example silly_presburger_example : forall m n o p,
  m + n <= n + o /\ o + 3 = p + 3 ->
  m <= p.
Proof.
  intros. omega.
Qed.

Module aevalR_first_try.

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum  : forall (n: nat),
      aevalR (ANum n) n
  | E_APlus : forall (e1 e2: aexp) (n1 n2: nat),
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (APlus e1 e2) (n1 + n2)
  | E_AMinus: forall (e1 e2: aexp) (n1 n2: nat),
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (AMinus e1 e2) (n1 - n2)
  | E_AMult : forall (e1 e2: aexp) (n1 n2: nat),
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (AMult e1 e2) (n1 * n2).


Notation "e '\\' n"
         := (aevalR e n)
            (at level 50, left associativity)
         : type_scope.

End aevalR_first_try.


Reserved Notation "e '\\' n" (at level 50, left associativity).

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum : forall (n:nat),
      (ANum n) \\ n
  | E_APlus : forall (e1 e2: aexp) (n1 n2 : nat),
      (e1 \\ n1) -> (e2 \\ n2) -> (APlus e1 e2) \\ (n1 + n2)
  | E_AMinus : forall (e1 e2: aexp) (n1 n2 : nat),
      (e1 \\ n1) -> (e2 \\ n2) -> (AMinus e1 e2) \\ (n1 - n2)
  | E_AMult :  forall (e1 e2: aexp) (n1 n2 : nat),
      (e1 \\ n1) -> (e2 \\ n2) -> (AMult e1 e2) \\ (n1 * n2)

  where "e '\\' n" := (aevalR e n) : type_scope.


Theorem aeval_iff_aevalR : forall a n,
  (a \\ n) <-> aeval a = n.
Proof.
 split.
 - (* -> *)
   intros H.
   induction H; simpl.
   + (* E_ANum *)
     reflexivity.
   + (* E_APlus *)
     rewrite IHaevalR1.  rewrite IHaevalR2.  reflexivity.
   + (* E_AMinus *)
     rewrite IHaevalR1.  rewrite IHaevalR2.  reflexivity.
   + (* E_AMult *)
     rewrite IHaevalR1.  rewrite IHaevalR2.  reflexivity.
 - (* <- *)
   generalize dependent n.
   induction a;
      simpl; intros; subst.
   + (* ANum *)
     apply E_ANum.
   + (* APlus *)
     apply E_APlus.
      apply IHa1. reflexivity.
      apply IHa2. reflexivity.
   + (* AMinus *)
     apply E_AMinus.
      apply IHa1. reflexivity.
      apply IHa2. reflexivity.
   + (* AMult *)
     apply E_AMult.
      apply IHa1. reflexivity.
      apply IHa2. reflexivity.
Qed.

Theorem aeval_iff_aevalR' : forall a n,
  (a \\ n) <-> aeval a = n.
Proof.
  (* WORKED IN CLASS *)
  split.
  - (* -> *)
    intros H; induction H; subst; reflexivity.
  - (* <- *)
    generalize dependent n.
    induction a; simpl; intros; subst; constructor;
       try apply IHa1; try apply IHa2; reflexivity.
Qed.

Inductive bevalR: bexp -> bool -> Prop :=
  | E_BTrue: bevalR BTrue true
  | E_BFalse: bevalR BFalse false
  | E_BEq1: forall a1 a2 n1 n2,
            aevalR a1 n1 -> aevalR a2 n2 -> n1 = n2 -> bevalR (BEq a1 a2) true
  | E_BEq2: forall a1 a2 n1 n2,
            aevalR a1 n1 -> aevalR a2 n2 -> n1 <> n2 -> bevalR (BEq a1 a2) false
  | E_BLe1: forall a1 a2 n1 n2,
            aevalR a1 n1 -> aevalR a2 n2 -> n1 <= n2 -> bevalR (BLe a1 a2) true
  | E_BLe2: forall a1 a2 n1 n2,
            aevalR a1 n1 -> aevalR a2 n2 -> n2 < n1 -> bevalR (BLe a1 a2) false
  | E_BNot: forall b bb, bevalR b bb -> bevalR (BNot b) (negb bb)
  | E_BAnd: forall b1 b2 bb1 bb2,
            bevalR b1 bb1 -> bevalR b2 bb2 -> bevalR (BAnd b1 b2) (bb1 && bb2).

Lemma n_le_m:
  forall n m,
  leb n m = false -> m < n.

Proof.
  unfold lt.
  intros.
  rewrite <- leb_iff.
  generalize dependent m.
  induction n.
  - intros. simpl in H. inversion H.
  - intros. simpl. simpl in H. destruct m.
    + reflexivity.
    + apply (IHn m H).
  Qed.

Lemma beval_iff_bevalR : forall b bv,
  bevalR b bv <-> beval b = bv.
Proof.
  (* FILL IN HERE *)
  split.
  - intros. induction H;
      try (reflexivity); (*BTrue and BFalse*)
      try (simpl; subst; reflexivity); (*BNot and BAnd*)
      try (apply aeval_iff_aevalR in H; apply aeval_iff_aevalR in H0; simpl;
      subst). (*BEq1,2, BLe1,2 partially*)
      + rewrite H1. rewrite <- beq_nat_refl. reflexivity.
      + rewrite <- beq_nat_false_iff in H1. assumption.
      + apply leb_correct. assumption.
      + apply leb_iff_conv. assumption.
  - generalize dependent bv. induction b.
    + simpl. intros. subst. constructor. 
    + simpl. intros. subst. constructor.
    + simpl. intros. destruct bv.
      * apply (E_BEq1 _ _ (aeval a) (aeval a0)).
        apply aeval_iff_aevalR'. reflexivity.
        apply aeval_iff_aevalR'. reflexivity.
        apply beq_nat_true. assumption.
      * apply (E_BEq2 _ _ (aeval a) (aeval a0)).
        apply aeval_iff_aevalR'. reflexivity.
        apply aeval_iff_aevalR'. reflexivity.
        apply beq_nat_false. assumption.
    + simpl. intros. destruct bv.
      * apply (E_BLe1 _ _ (aeval a) (aeval a0)).
        apply aeval_iff_aevalR'. reflexivity.
        apply aeval_iff_aevalR'. reflexivity.
        apply leb_iff. assumption.
      * apply (E_BLe2 _ _ (aeval a) (aeval a0)).
        apply aeval_iff_aevalR'. reflexivity.
        apply aeval_iff_aevalR'. reflexivity.
        apply n_le_m. assumption.
    + simpl. intros. subst. constructor. 
      apply IHb. reflexivity.
    + simpl. intros. subst. constructor.
      apply IHb1. reflexivity.
      apply IHb2. reflexivity.
  Qed.

End AExp.


Module aevalR_division.


Inductive aexp : Type :=
  | ANum : nat -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp
  | ADiv : aexp -> aexp -> aexp.   (* <--- new *)


Reserved Notation "e '\\' n"
                  (at level 50, left associativity).

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum : forall (n:nat),
      (ANum n) \\ n
  | E_APlus : forall (a1 a2: aexp) (n1 n2 : nat),
      (a1 \\ n1) -> (a2 \\ n2) -> (APlus a1 a2) \\ (n1 + n2)
  | E_AMinus : forall (a1 a2: aexp) (n1 n2 : nat),
      (a1 \\ n1) -> (a2 \\ n2) -> (AMinus a1 a2) \\ (n1 - n2)
  | E_AMult :  forall (a1 a2: aexp) (n1 n2 : nat),
      (a1 \\ n1) -> (a2 \\ n2) -> (AMult a1 a2) \\ (n1 * n2)
  | E_ADiv :  forall (a1 a2: aexp) (n1 n2 n3: nat),
      (a1 \\ n1) -> (a2 \\ n2) -> (n2 > 0) ->
      (mult n2 n3 = n1) -> (ADiv a1 a2) \\ n3

where "a '\\' n" := (aevalR a n) : type_scope.

End aevalR_division.

Module aevalR_extended.


Reserved Notation "e '\\' n" (at level 50, left associativity).

Inductive aexp : Type :=
  | AAny  : aexp                   (* <--- NEW *)
  | ANum : nat -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.


Inductive aevalR : aexp -> nat -> Prop :=
  | E_Any : forall (n:nat),
      AAny \\ n                 (* <--- new *)
  | E_ANum : forall (n:nat),
      (ANum n) \\ n
  | E_APlus : forall (a1 a2: aexp) (n1 n2 : nat),
      (a1 \\ n1) -> (a2 \\ n2) -> (APlus a1 a2) \\ (n1 + n2)
  | E_AMinus : forall (a1 a2: aexp) (n1 n2 : nat),
      (a1 \\ n1) -> (a2 \\ n2) -> (AMinus a1 a2) \\ (n1 - n2)
  | E_AMult :  forall (a1 a2: aexp) (n1 n2 : nat),
      (a1 \\ n1) -> (a2 \\ n2) -> (AMult a1 a2) \\ (n1 * n2)

where "a '\\' n" := (aevalR a n) : type_scope.

End aevalR_extended.

(*New Session*)

Open Scope string_scope.


Definition state := total_map nat.

Definition empty_state : state :=
  t_empty 0.


Inductive aexp : Type :=
  | ANum : nat -> aexp
  | AId : string -> aexp                (* <----- NEW *)
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.


Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".


Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.


Coercion AId : string >-> aexp.
Coercion ANum : nat >-> aexp.
Definition bool_to_bexp (b: bool) : bexp :=
  if b then BTrue else BFalse.
Coercion bool_to_bexp : bool >-> bexp.

Bind Scope aexp_scope with aexp.
Infix "+" := APlus : aexp_scope.
Infix "-" := AMinus : aexp_scope.
Infix "*" := AMult : aexp_scope.
Bind Scope bexp_scope with bexp.
Infix "<=" := BLe : bexp_scope.
Infix "=" := BEq : bexp_scope.
Infix "&&" := BAnd : bexp_scope.
Notation "'!' b" := (BNot b) (at level 60) : bexp_scope.


Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x                                (* <----- NEW *)
  | APlus a1 a2 => (aeval st a1) + (aeval st a2)
  | AMinus a1 a2  => (aeval st a1) - (aeval st a2)
  | AMult a1 a2 => (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st : state) (b : bexp) : bool :=
  match b with
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => beq_nat (aeval st a1) (aeval st a2)
  | BLe a1 a2   => leb (aeval st a1) (aeval st a2)
  | BNot b1     => negb (beval st b1)
  | BAnd b1 b2  => andb (beval st b1) (beval st b2)
  end.

Notation "{ a --> x }" := 
  (t_update { --> 0 } a x) (at level 0).
Notation "{ a --> x ; b --> y }" := 
  (t_update ({ a --> x }) b y) (at level 0).
Notation "{ a --> x ; b --> y ; c --> z }" := 
  (t_update ({ a --> x ; b --> y }) c z) (at level 0). 
Notation "{ a --> x ; b --> y ; c --> z ; d --> t }" := 
    (t_update ({ a --> x ; b --> y ; c --> z }) d t) (at level 0).
Notation "{ a --> x ; b --> y ; c --> z ; d --> t ; e --> u }" :=
  (t_update ({ a --> x ; b --> y ; c --> z ; d --> t }) e u) (at level 0).
Notation "{ a --> x ; b --> y ; c --> z ; d --> t ; e --> u ; f --> v }" :=
  (t_update ({ a --> x ; b --> y ; c --> z ; d --> t ; e --> u }) f v) (at level 0).

Example aexp1 :
  aeval { X --> 5 } (3 + (AMult X 2))
  = 13.
Proof. reflexivity. Qed.

Example bexp1 :
  beval { X --> 5 } (true && BNot (BLe X 4))
  = true.
Proof. reflexivity. Qed.


Inductive com : Type :=
  | CSkip : com
  | CAss : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com.


Bind Scope com_scope with com.
Notation "'SKIP'" :=
   CSkip : com_scope.
Notation "x '::=' a" :=
  (CAss x a) (at level 60) : com_scope.
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity) : com_scope.
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity) : com_scope.
Notation "'IFB' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity) : com_scope.

Open Scope com_scope.

Definition fact_in_coq : com :=
  Z ::= X;;
  Y ::= 1;;
  WHILE ! (BEq Z 0) DO
    Y ::= Y * Z;;
    Z ::= Z - 1 
  END.

Definition plus2 : com :=
  X ::= X + 2.

Definition XtimesYinZ : com :=
  Z ::= X * Y.

Definition subtract_slowly_body : com :=
  Z ::= Z - 1 ;;
  X ::= X - 1.

Definition subtract_slowly : com :=
  WHILE ! (BEq X 0) DO
    subtract_slowly_body
  END.

Definition subtract_3_from_5_slowly : com :=
  X ::= 3 ;;
  Z ::= 5 ;;
  subtract_slowly.

Definition loop : com :=
  WHILE true DO
    SKIP
  END.


Fixpoint ceval_fun_no_while (st : state) (c : com)
                          : state :=
  match c with
    | SKIP =>
        st
    | x ::= a1 =>
        st & { x --> (aeval st a1) }
    | c1 ;; c2 =>
        let st' := ceval_fun_no_while st c1 in
        ceval_fun_no_while st' c2
    | IFB b THEN c1 ELSE c2 FI =>
        if (beval st b)
          then ceval_fun_no_while st c1
          else ceval_fun_no_while st c2
    | WHILE b DO c END =>
        st  (* bogus *)
  end.


Reserved Notation "c1 '/' st '\\' st'"
                  (at level 40, st at level 39).


Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      SKIP / st \\ st
  | E_Ass  : forall st a1 n x,
      aeval st a1 = n ->
      (x ::= a1) / st \\ st & { x --> n }
  | E_Seq : forall c1 c2 st st' st'',
      c1 / st  \\ st' ->
      c2 / st' \\ st'' ->
      (c1 ;; c2) / st \\ st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      c1 / st \\ st' ->
      (IFB b THEN c1 ELSE c2 FI) / st \\ st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      c2 / st \\ st' ->
      (IFB b THEN c1 ELSE c2 FI) / st \\ st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      (WHILE b DO c END) / st \\ st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      c / st \\ st' ->
      (WHILE b DO c END) / st' \\ st'' ->
      (WHILE b DO c END) / st \\ st''

  where "c1 '/' st '\\' st'" := (ceval c1 st st').

Example ceval_example1:
    (X ::= 2;;
     IFB X <= 1
       THEN Y ::= 3
       ELSE Z ::= 4
     FI)
   / { --> 0 } \\ { X --> 2 ; Z --> 4 }.
Proof.
  (* We must supply the intermediate state *)
  apply E_Seq with { X --> 2 }. 
  - (* assignment command *)
    apply E_Ass. reflexivity.
  - (* if command *)
    apply E_IfFalse.
      reflexivity.
      apply E_Ass. reflexivity.  Qed.

(*Exercise 1*)
Example ceval_example2:
  (X ::= 0;; Y ::= 1;; Z ::= 2) / { --> 0 } \\
  { X --> 0 ; Y --> 1 ; Z --> 2 }.
Proof.
  apply E_Seq with (t_update empty_state X 0).
  - apply E_Ass. reflexivity.
  - apply E_Seq with (t_update (t_update empty_state X 0) Y 1).
    + apply E_Ass. reflexivity.
    + apply E_Ass. reflexivity.
Qed.


(*Exercise 2*)
(** Write an Imp program that sums the numbers from [1] to
   [X] (inclusive: [1 + 2 + ... + X]) in the variable [Y].
   Prove that this program executes as intended for [X] = [2]
   (this is trickier than you might expect). *)


Definition pup_to_n : com :=
  (Y ::= (ANum 0) ;; (WHILE (BLe (ANum 1) (AId X))
         DO (Y ::= (APlus (AId X) (AId Y)) ;; X ::= (AMinus (AId X) (ANum 1))) END)).

Theorem pup_to_2_ceval :
  pup_to_n / { X --> 2 }
     \\ { X --> 2 ; Y --> 0 ; Y --> 2 ; X --> 1 ; Y --> 3 ; X --> 0 }.
Proof.
  unfold pup_to_n. apply E_Seq with (t_update (t_update empty_state X 2) Y 0).
  - apply E_Ass. simpl. reflexivity.
  - apply E_WhileTrue with (t_update (t_update (t_update (t_update empty_state X 2) Y 0) Y 2) X 1).
    + simpl. reflexivity.
    + apply E_Seq with (t_update (t_update (t_update empty_state X 2) Y 0) Y 2).
      * apply E_Ass. simpl. rewrite t_update_eq. reflexivity.
      * apply E_Ass. simpl. reflexivity.
    + apply E_WhileTrue with (t_update (t_update (t_update (t_update (t_update (t_update empty_state X 2) Y 0) Y 2) X 1) Y 3) X 0).
      * simpl. reflexivity.
      * apply E_Seq with (t_update (t_update (t_update (t_update (t_update empty_state X 2) Y 0) Y 2) X 1) Y 3).
        { apply E_Ass. simpl. rewrite t_update_shadow. rewrite t_update_permute.
          - rewrite t_update_eq. reflexivity.
          - apply beq_string_false_iff. destruct (beq_string Y X) eqn: H.
            + inversion H.
            + reflexivity. }
        { apply E_Ass. simpl. reflexivity. }
      * apply E_WhileFalse. simpl. reflexivity.
Qed.


Theorem ceval_deterministic: forall c st st1 st2,
     c / st \\ st1  ->
     c / st \\ st2 ->
     st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2.
  induction E1;
           intros st2 E2; inversion E2; subst.
  - (* E_Skip *) reflexivity.
  - (* E_Ass *) reflexivity.
  - (* E_Seq *)
    assert (st' = st'0) as EQ1.
    { (* Proof of assertion *) apply IHE1_1; assumption. }
    subst st'0.
    apply IHE1_2. assumption.
  - (* E_IfTrue, b1 evaluates to true *)
      apply IHE1. assumption.
  - (* E_IfTrue,  b1 evaluates to false (contradiction) *)
      rewrite H in H5. inversion H5.
  - (* E_IfFalse, b1 evaluates to true (contradiction) *)
    rewrite H in H5. inversion H5.
  - (* E_IfFalse, b1 evaluates to false *)
      apply IHE1. assumption.
  - (* E_WhileFalse, b1 evaluates to false *)
    reflexivity.
  - (* E_WhileFalse, b1 evaluates to true (contradiction) *)
    rewrite H in H2. inversion H2.
  - (* E_WhileTrue, b1 evaluates to false (contradiction) *)
    rewrite H in H4. inversion H4.
  - (* E_WhileTrue, b1 evaluates to true *)
      assert (st' = st'0) as EQ1.
      { (* Proof of assertion *) apply IHE1_1; assumption. }
      subst st'0.
      apply IHE1_2. assumption.  Qed.


Theorem plus2_spec : forall st n st',
  st X = n ->
  plus2 / st \\ st' ->
  st' X = (n + 2).
Proof.
  intros st n st' HX Heval.

  inversion Heval. subst. clear Heval. simpl.
  apply t_update_eq.  Qed.


(*Exercise 3*)
Theorem loop_never_stops : forall st st',
  ~(loop / st \\ st').
Proof.
intros st st' contra.
  unfold loop in contra.
  remember (WHILE true DO SKIP END) as loopdef.
  induction contra; inversion Heqloopdef.
  rewrite H1 in H. simpl in H. inversion H.
  apply IHcontra2. subst. reflexivity.
Qed.


Fixpoint no_whiles (c : com) : bool :=
  match c with
  | SKIP =>
      true
  | _ ::= _ =>
      true
  | c1 ;; c2 =>
      andb (no_whiles c1) (no_whiles c2)
  | IFB _ THEN ct ELSE cf FI =>
      andb (no_whiles ct) (no_whiles cf)
  | WHILE _ DO _ END  =>
      false
  end.

(*Exercise 4*)
(*Using [Inductive], write a property [no_whilesR] such that
    [no_whilesR c] is provable exactly when [c] is a program with no
    while loops.  Then prove its equivalence with [no_whiles]. *)

Inductive no_whilesR: com -> Prop :=
  | NW_Skip :  no_whilesR CSkip
  | NW_Ass : forall a x, no_whilesR (CAss x a)
  | NW_Seq : forall c1 c2, no_whilesR c1 -> no_whilesR c2 -> no_whilesR (c1;;c2)
  | NW_If : forall b c1 c2, no_whilesR c1 -> no_whilesR c2 -> no_whilesR (CIf b c1 c2).

(*Exercise 5*)
Theorem no_whiles_eqv:
   forall c, no_whiles c = true <-> no_whilesR c.
Proof.
  split; intros.
  induction c.
  apply NW_Skip.
  apply NW_Ass.
  apply NW_Seq; simpl in H; [apply IHc1 | apply IHc2]; apply andb_true_iff in H; apply H.
  apply NW_If; simpl in H; apply andb_true_iff in H; [apply IHc1 | apply IHc2]; apply H.
  inversion H.

  induction c; try (simpl); try (reflexivity); 
  try (apply andb_true_iff); try(split); try(apply IHc1); try(apply IHc2);
  inversion H; assumption. 
Qed.

(*Exercise 6*)
(** Imp programs that don't involve while loops always terminate.
    State and prove a theorem [no_whiles_terminating] that says this. *)
(** Use either [no_whiles] or [no_whilesR], as you prefer. *)
Theorem no_whiles_terminating : forall c st, no_whilesR c -> exists st', c / st \\ st'.
Proof.
intros.
  generalize dependent st.
  induction H.
    intros.
    exists st. apply E_Skip.
    intros.
    Admitted.