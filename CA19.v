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

Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Export Coq.Strings.String.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Lists.List.
Import ListNotations.

Definition beq_string x y :=
  if string_dec x y then true else false.

Print sumbool.
Check string_dec.

Theorem beq_string_refl : forall s, true = beq_string s s.
Proof. intros s. unfold beq_string. destruct (string_dec s s) as [|Hs].
  - reflexivity.
  - unfold not in Hs. destruct Hs. reflexivity.
Qed.

Theorem beq_string_true_iff : forall x y : string,
  beq_string x y = true <-> x = y.
Proof.
   intros x y.
   unfold beq_string.
   destruct (string_dec x y) as [|Hs].
   - subst. split. reflexivity. reflexivity.
   - split.
     + intros contra. inversion contra.
     + intros H. inversion H. subst. destruct Hs. reflexivity.
Qed.

Theorem beq_string_false_iff : forall x y : string,
  beq_string x y = false
  <-> x <> y.
Proof.
  intros x y. rewrite <- beq_string_true_iff.
  rewrite not_true_iff_false. reflexivity. Qed.

Theorem false_beq_string : forall x y : string,
   x <> y -> beq_string x y = false.
Proof.
  intros x y. rewrite beq_string_false_iff.
  intros H. apply H. Qed.

Definition total_map (A:Type) := string -> A.

Definition t_empty {A:Type} (v : A) : total_map A :=
  (fun _ => v).

Definition t_update {A:Type} (m : total_map A)
                    (x : string) (v : A) :=
  fun x' => if beq_string x x' then v else m x'.


Definition examplemap :=
  t_update (t_update (t_empty false) "foo" true)
           "bar" true.

Notation "{ --> d }" := (t_empty d) (at level 0).

Notation "m '&' { a --> x }" :=
  (t_update m a x) (at level 20).
Notation "m '&' { a --> x ; b --> y }" :=
  (t_update (m & { a --> x }) b y) (at level 20).
Notation "m '&' { a --> x ; b --> y ; c --> z }" :=
  (t_update (m & { a --> x ; b --> y }) c z) (at level 20).
Notation "m '&' { a --> x ; b --> y ; c --> z ; d --> t }" :=
    (t_update (m & { a --> x ; b --> y ; c --> z }) d t) (at level 20).
Notation "m '&' { a --> x ; b --> y ; c --> z ; d --> t ; e --> u }" :=
    (t_update (m & { a --> x ; b --> y ; c --> z ; d --> t }) e u) (at level 20).
Notation "m '&' { a --> x ; b --> y ; c --> z ; d --> t ; e --> u ; f --> v }" :=
    (t_update (m & { a --> x ; b --> y ; c --> z ; d --> t ; e --> u }) f v) 
      (at level 20).

Definition examplemap' :=
  { --> false } & { "foo" --> true ; "bar" --> true }.


Example update_example1 : examplemap' "baz" = false.
Proof. reflexivity. Qed.

Example update_example2 : examplemap' "foo" = true.
Proof. reflexivity. Qed.

Example update_example3 : examplemap' "quux" = false.
Proof. reflexivity. Qed.

Example update_example4 : examplemap' "bar" = true.
Proof. reflexivity. Qed.

(*Exercise 1*)
Lemma t_apply_empty:  forall (A:Type) (x: string) (v: A), { --> v } x = v.
Proof.
  intros. trivial. Qed.


(*Exercise 2*)
Lemma t_update_eq : forall A (m: total_map A) x v,
  (m & {x --> v}) x = v.
Proof.
  intros. unfold t_update. rewrite <- beq_string_refl. reflexivity.
Qed.


(*Exercise 3*)
Theorem t_update_neq : forall (X:Type) v x1 x2
                         (m : total_map X),
  x1 <> x2 ->
  (m & {x1 --> v}) x2 = m x2.
Proof.
  intros. unfold t_update. rewrite false_beq_string. reflexivity. apply H.
Qed.

(*Exercise 4*)
Lemma t_update_shadow : forall A (m: total_map A) v1 v2 x,
    m & {x --> v1 ; x --> v2} = m & {x --> v2}.
Proof.
  intros. unfold t_update. extensionality i. remember (beq_string x i) as e; induction e.
  trivial. trivial.
Qed.


(*Exercise 5*)
(** Use the proof of [beq_natP] in chapter [IndProp] as a template to
    prove the following: *)
Lemma beq_stringP : forall x y, reflect (x = y) (beq_string x y).
Proof.
  intros. apply iff_reflect. rewrite beq_string_true_iff.
  reflexivity.
Qed.



(*Exercise 6*)
(** With the example in chapter [IndProp] as a template, use
    [beq_stringP] to prove the following theorem, which states that if we
    update a map to assign key [x] the same value as it already has in
    [m], then the result is equal to [m]: *)
Theorem t_update_same : forall X x (m : total_map X),
    m & { x --> m x } = m.
  Proof.
     intros. unfold t_update. extensionality i. remember (beq_string x i) as e; induction e.
      symmetry in Heqe. apply beq_string_true_iff in Heqe. rewrite Heqe. auto. auto.
Qed.
    
    
    


(*Exercise 7*)
(** Use [beq_stringP] to prove one final property of the [update]
    function: If we update a map [m] at two distinct keys, it doesn't
    matter in which order we do the updates. *)
Theorem t_update_permute : forall (X:Type) v1 v2 x1 x2
                             (m : total_map X),
  x2 <> x1 ->
  m & { x2 --> v2 ; x1 --> v1 }
  =  m & { x1 --> v1 ; x2 --> v2 }.
Proof.
  intros. unfold t_update. extensionality i. remember (beq_string x1 i) as e; induction e.
  symmetry in Heqe. apply beq_string_true_iff in Heqe. rewrite <- Heqe. rewrite -> false_beq_string.
  reflexivity. exact H. reflexivity.
Qed.


Definition partial_map (A:Type) := total_map (option A).

Definition empty {A:Type} : partial_map A :=
  t_empty None.

Definition update {A:Type} (m : partial_map A)
           (x : string) (v : A) :=
  m & { x --> (Some v) }.


Notation "m '&' {{ a --> x }}" :=
  (update m a x) (at level 20).
Notation "m '&' {{ a --> x ; b --> y }}" :=
  (update (m & {{ a --> x }}) b y) (at level 20).
Notation "m '&' {{ a --> x ; b --> y ; c --> z }}" :=
  (update (m & {{ a --> x ; b --> y }}) c z) (at level 20).
Notation "m '&' {{ a --> x ; b --> y ; c --> z ; d --> t }}" :=
    (update (m & {{ a --> x ; b --> y ; c --> z }}) d t) (at level 20).
Notation "m '&' {{ a --> x ; b --> y ; c --> z ; d --> t ; e --> u }}" :=
    (update (m & {{ a --> x ; b --> y ; c --> z ; d --> t }}) e u) (at level 20).
Notation "m '&' {{ a --> x ; b --> y ; c --> z ; d --> t ; e --> u ; f --> v }}" :=
    (update (m & {{ a --> x ; b --> y ; c --> z ; d --> t ; e --> u }}) f v) 
    (at level 20).

Lemma apply_empty : forall (A: Type) (x: string),  @empty A x = None.
Proof.
  intros. unfold empty. rewrite t_apply_empty.
  reflexivity.
Qed.

Lemma update_eq : forall A (m: partial_map A) x v,
    (m & {{ x --> v }}) x = Some v.
Proof.
  intros. unfold update. rewrite t_update_eq.
  reflexivity.
Qed.

Theorem update_neq : forall (X:Type) v x1 x2
                       (m : partial_map X),
  x2 <> x1 ->
  (m & {{ x2 --> v }}) x1 = m x1.
Proof.
  intros X v x1 x2 m H.
  unfold update. rewrite t_update_neq. reflexivity.
  apply H. Qed.

Lemma update_shadow : forall A (m: partial_map A) v1 v2 x,
    m & {{ x --> v1 ; x --> v2 }} = m & {{x --> v2}}.
Proof.
  intros A m v1 v2 x1. unfold update. rewrite t_update_shadow.
  reflexivity.
Qed.

Theorem update_same : forall X v x (m : partial_map X),
  m x = Some v ->
  m & {{x --> v}} = m.
Proof.
  intros X v x m H. unfold update. rewrite <- H.
  apply t_update_same.
Qed.

Theorem update_permute : forall (X:Type) v1 v2 x1 x2
                                (m : partial_map X),
  x2 <> x1 ->
  m & {{x2 --> v2 ; x1 --> v1}}
  = m & {{x1 --> v1 ; x2 --> v2}}.
Proof.
  intros X v1 v2 x1 x2 m. unfold update.
  apply t_update_permute.
Qed.


