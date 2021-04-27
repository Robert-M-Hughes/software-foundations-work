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


From LF Require Export Basics.

(* ################################################################# *)
(** * Proof by Induction *)

Theorem plus_n_O_firsttry : forall n:nat,
  n = n + 0.

Proof.
  intros n.
  simpl. (* Does nothing! *)
Abort.

Theorem plus_n_O_secondtry : forall n:nat,
  n = n + 0.
Proof.
  intros n. destruct n as [| n'].
  - (* n = 0 *)
    reflexivity. (* so far so good... *)
  - (* n = S n' *)
    simpl.       (* ...but here we are stuck again *)
Abort.

Theorem plus_n_O : forall n:nat, n = n + 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *)    reflexivity.
  - (* n = S n' *) simpl. rewrite <- IHn'. reflexivity.  Qed.

Theorem minus_diag : forall n,
  minus n n = 0.
Proof.
  (* WORKED IN CLASS *)
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *)
    simpl. reflexivity.
  - (* n = S n' *)
    simpl. rewrite -> IHn'. reflexivity.  Qed.

(** **** Exercise: 2 stars, recommended (basic_induction)  *)
(** Prove the following using induction. You might need previously
    proven results. *)

Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  intros. induction n as [|n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.  Qed.



Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
    intros. induction n as [|n' IHn'].
    reflexivity.
    simpl. rewrite -> IHn'. reflexivity.  Qed.


Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros. induction n as [|n' IHn'].
  - rewrite <- plus_n_O.
    + reflexivity.
  - simpl. rewrite -> IHn'. rewrite plus_n_Sm. reflexivity.  Qed.


Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros. induction n as [|n' IHn'].
  reflexivity.
  simpl. rewrite -> IHn'. reflexivity.  Qed.

(** **** Exercise: 2 stars (double_plus)  *)
(** Consider the following function, which doubles its argument: *)

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

(** Use induction to prove this simple fact about [double]: *)

Lemma double_plus : forall n, double n = n + n .
Proof.
  intros. induction n as [|n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. rewrite plus_n_Sm. reflexivity.  Qed.


Theorem double_plus_2:
  forall m n: nat, double m + double n = double (m + n).

Proof. (*FILL IN HERE *)
  intros. induction m as [|n' IHn'].
  reflexivity.
  simpl. rewrite IHn'. reflexivity. Qed.

(** **** Exercise: 2 stars, optional (evenb_S)  *)
(** One inconvenient aspect of our definition of [evenb n] is the
    recursive call on [n - 2]. This makes proofs about [evenb n]
    harder when done by induction on [n], since we may need an
    induction hypothesis about [n - 2]. The following lemma gives an
    alternative characterization of [evenb (S n)] that works better
    with induction: *)

Theorem evenb_S : forall n : nat,
  evenb (S n) = negb (evenb n).
Proof.
  intros. induction n as [|n' IHn'].
  reflexivity. 
  rewrite IHn'.
  simpl.
  rewrite negb_involutive.
  reflexivity.
  Qed.


