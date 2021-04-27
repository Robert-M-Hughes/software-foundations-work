(*Robert Hughes
Comp 293 Hw 3
This is the document for the third homework for the software reliability class*)



From LF Require Export Logic.
From LF Require Import IndProp.



(*Question #1*)
Theorem question_1a: forall a b c, a + b <= a + c -> b <= c.
Proof.
  intros. induction a.
  simpl in H. assumption. 
 simpl in H. apply Sn_le_Sm__n_le_m in H. apply IHa. assumption.
Qed.

Theorem question_1b : forall a b c, 
  a <= b -> c + a <= c + b.
Proof.
 intros.
 induction c.
  apply H.
  apply n_le_m__Sn_le_Sm.
  apply IHc.
Qed.

Theorem question_1c: forall a b c d,  a <= b -> c <= d -> a + c <= b + d.
Proof.
  intros. induction H. apply question_1b. assumption. rewrite IHle. simpl. apply le_S.
  reflexivity.
Qed.


(*Question #2*)
(*Question #2a*)
Fixpoint question_2a {T:Type} (re: @reg_exp T) : bool :=
  match re with 
   | EmptySet => false
   | EmptyStr => true
   | Char _ => true
   | App r1 r2 => question_2a r1 && question_2a r2
   | Union r1 r2 => question_2a r1 || question_2a r2
   | Star r => true
  end.

(*Question #2b*)
Theorem question_2b :
  forall T s (re : reg_exp T) ,
   (exp_match s re) ->
    s =~ Star re.
Proof.
  intros T s re H.
  rewrite <- (app_nil_r _ s).
  apply (MStarApp s [] re).
  - apply H.
  - apply MStar0.
Qed.


(*Question #3*)
Theorem  question_3 : forall T (s : list T) (re : @reg_exp T),
      s =~ Star re -> exists ss : list (list T),
      s = fold app ss [] /\ forall s', In s' ss -> s' =~ re.
Proof.
  intros.
  remember (Star re) as re'.
  induction H.
  - inversion Heqre'.
  - inversion Heqre'.
  - inversion Heqre'.
  - inversion Heqre'.
  - inversion Heqre'.
  - inversion Heqre'.
     intros.  exists [].  split.  reflexivity.
     intros.  inversion H.
  - destruct (IHexp_match2 Heqre') as [H1 [H2 H3]].  exists(s1::H1).  split.
    + simpl. rewrite <- H2.  reflexivity.
    + intros s' [H4 | H4]. rewrite <- H4. inversion Heqre'.  rewrite H6 in H. apply H.
      apply H3. apply H4.
Qed.

(*Question #4*)
Inductive question_4 {X:Type} : list X -> Prop :=
| ns_nil : question_4 []
| ns_one : forall (x : X), question_4 [x]
| ns_cons: forall (x : X) (h : X) (t : list X), question_4 (h::t) -> x <> h -> question_4 (x::h::t).


Lemma beq_nat_false : forall x y, eqb x y = false -> x<>y.
Proof.
 induction x; destruct y; simpl; auto; intros; discriminate.
Qed.

Example question_4b_a : question_4 [3;1;4;1;5;6;5;6].
Proof. 
apply ns_cons. apply ns_cons. apply ns_cons. apply ns_cons. 
  apply ns_cons. apply ns_cons. 
 apply ns_cons. apply ns_one. 
 - intros. discriminate.
 - intros. discriminate.
 - intros. discriminate.
 - intros. discriminate.
 - intros. discriminate.
 - intros. discriminate.
 - intros. discriminate.
Qed.
Example question_4b_b : question_4 (@nil nat) .
Proof. apply ns_nil. Qed.
Example question_4b_c : question_4 [7].
Proof. apply ns_one. Qed.
Example question_4b_d : not (question_4 [2;5;5;1]).
Proof.
  intro.
  inversion H.
  inversion H2.
  apply H9.
  reflexivity.
Qed.
Example question_4b_e : not (question_4 [true;false;true;true]).
Proof.
  intro.
  inversion H.
  inversion H2.
  inversion H7.
  apply H14.
  reflexivity.
Qed.



(*Question #5a*)
Inductive question_5a { X : Type } : list X -> Prop :=
  | palindrome_nil : question_5a []
  | palindrome_x : forall (x : X), question_5a [x]
  | palindrome_xs : forall (x : X) (l : list X),
	   question_5a l -> question_5a (x::l ++ [x]).

(*Question #5b*)
Theorem question_5b : forall {X : Type} (l : list X),
    question_5a (l ++ rev l). 
Proof. intros X l.
       induction l as [| x l' IHl'].
       - simpl. apply palindrome_nil. 
       - simpl. rewrite app_assoc.
         apply (palindrome_xs x). apply IHl'.
Qed.

(*Question #5c*)
Theorem question_5c { X : Type } : forall (l : list X), question_5a l -> l = rev l.
Proof.
  intros l H.
  induction H.
  - reflexivity.
  - reflexivity.
  - simpl. rewrite rev_app_distr. simpl. rewrite <- IHquestion_5a. reflexivity.
Qed.

(*Question #6*)
(*Question #6a*)
Inductive question_6a {X : Type} : list X -> list X -> Prop :=
  subseq_nil : forall l, question_6a [] l
| subseq_inboth : forall x l1 l2, question_6a l1 l2 -> question_6a (x :: l1) (x :: l2)
| subseq_in2nd  : forall x l1 l2, question_6a l1 l2 -> question_6a l1 (x :: l2).

(*Question #6b*)
Theorem question_6b : forall (X : Type) (l : list X), question_6a l l.
Proof.
  intros. induction l as [|x xs]. apply subseq_nil.
  apply subseq_inboth. apply IHxs.
Qed.


(*Question #6c*)
Theorem question_6c_help : forall (X : Type) (x : X) (l1 l2 : list X),
  x :: (l1 ++ l2) = (x :: l1) ++ l2.
Proof.
  intros. induction l1 as [|y ys].
  simpl. reflexivity.
  simpl. reflexivity.
Qed.

Theorem question_6c : forall (X : Type) (l1 l2 l3 : list X),
  question_6a l1 l2 -> question_6a l1 (l2 ++ l3).
Proof.
  intros X l1 l2 l3 ss. induction ss.
  apply subseq_nil.
  rewrite <- question_6c_help. apply subseq_inboth. apply IHss.
  rewrite <- question_6c_help. apply subseq_in2nd. apply IHss.
Qed.

(*Question #6d*)
Theorem question_6d : forall (X : Type) (l1 l2 l3 : list X),
  question_6a l1 l2 -> question_6a l2 l3 -> question_6a l1 l3.
Proof.
  intros X l1 l2 l3 T12 T23.
  generalize dependent T12.
  generalize dependent l1.
  induction T23. intros. inversion T12. apply subseq_nil.
  intros. inversion T12.
  apply subseq_nil.
  apply subseq_inboth. apply IHT23. apply H1.
  apply subseq_in2nd. apply IHT23. apply H1.
  intros. apply subseq_in2nd. apply IHT23. apply T12.
Qed.


(*Question #6e*)


(*Question #7*)
(*Question #7a*)
Inductive all (X : Type) (P : X -> Prop) : list X -> Prop :=
| all_nil : all X P []
| all_recursive : forall (hd : X) (l : list X), P hd -> all X P l 
                                                -> all X P (hd::l).

Inductive question_7 {X:Type}: list X -> list X -> list X -> Prop :=
| nil_l : forall l, question_7 nil l l
| l_nil : forall l, question_7 l nil l
| head_l: forall (x:X) (l1 l2 l: list X), 
  question_7 l1 l2 l -> question_7 (x::l1) l2 (x::l)
| l_head: forall (x:X) (l1 l2 l: list X), 
  question_7 l1 l2 l -> question_7 l1 (x::l2) (x::l).

(*Question #7b
Lemma question_7b_i : forall (X : Type) (l1 l2 l3 : list X), 
l3 = question_7 l1 l2.
*)

(*Question #7bii*)
Lemma question_7b_self : forall (X : Type) (l : list X) (test: X->bool), 
all X (fun x => test x = true) l -> filter test l = l.
Proof.
intros. induction l as [| hd tl]. 
reflexivity.
inversion H.
apply IHtl in H3.
simpl. rewrite H2. rewrite H3.
reflexivity. Qed.

(*Question #7biii*)
Lemma question_7b_empty : forall (X : Type) (l : list X) (test: X->bool), 
all X (fun x => test x = false) l -> filter test l = [].
Proof.
intros. induction l as [| hd tl].
reflexivity.
inversion H.
apply IHtl in H3.
simpl. rewrite H2. apply H3.
Qed.

(*Question #7b*)
Theorem question_7_filter : forall (X : Type) (l l1 l2 : list X) (test : X -> bool),
all X  (fun x => test x = true) l1 ->
all X  (fun x => test x = false) l2 ->
question_7 l1 l2 l -> 
filter test l = l1.
Proof.
intros.  induction H1. 
apply question_7b_empty. apply H0.
apply question_7b_self. apply H.
inversion H. apply IHquestion_7 in H5. simpl. rewrite H4. rewrite H5. reflexivity. apply H0.
inversion H0. simpl. rewrite H4. apply IHquestion_7. apply H. apply H5.
Qed.





