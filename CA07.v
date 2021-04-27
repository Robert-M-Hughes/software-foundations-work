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


From LF Require Export Lists.

Inductive boollist : Type :=
  | bool_nil : boollist
  | bool_cons : bool -> boollist -> boollist.

Inductive bool2natlist : Type :=
  | b2n_nil : bool2natlist
  | b2n_cons: (bool -> nat) -> bool2natlist -> bool2natlist.


Inductive booloption : Type :=
  | Some_bool : bool -> booloption
  | None_bool : booloption.

Inductive bool2natoption: Type :=
  | Some_b2n : (bool -> nat) -> bool2natoption
  | None_b2n : bool2natoption.

Inductive list (X:Type) : Type :=
  | nil : list X
  | cons : X -> list X -> list X.

Check list.
Check (cons (bool-> bool)).


Check (nil nat).
(* ===> nil nat : list nat *)

Check (cons nat 3 (nil nat)).
(* ===> cons nat 3 (nil nat) : list nat *)

Check nil.
(* ===> nil : forall X : Type, list X *)

Check cons.
(* ===> cons : forall X : Type, X -> list X -> list X *)

Check (cons nat 2 (cons nat 1 (nil nat))).

Fixpoint repeat (X : Type) (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat X x count')
  end.

Check repeat.

Example test_repeat1 :
  repeat nat 4 2 = cons nat 4 (cons nat 4 (nil nat)).
Proof. reflexivity.  Qed.

Example test_repeat2 :
  repeat bool false 1 = cons bool false (nil bool).
Proof. reflexivity.  Qed.


Module MumbleGrumble.


(*Exercise1*)
Inductive mumble : Type :=
  | a : mumble
  | b : mumble -> nat -> mumble
  | c : mumble.

Inductive grumble (X:Type) : Type :=
  | d : mumble -> grumble X
  | e : X -> grumble X.

(** Which of the following are well-typed elements of [grumble X] for
    some type [X]?
      - [d (b a 5)]
      - [d mumble (b a 5)]
      - [d bool (b a 5)]
      - [e bool true]
      - [e mumble (b c 0)]
      - [e bool (b c 0)]
      - [c]  *)

Check d mumble (b a 5).
Check d bool (b a 5).
Check e bool true.
Check e mumble (b c 0).
Check c.


End MumbleGrumble.


Fixpoint repeat' X x count : list X :=
  match count with
  | 0        => nil X
  | S count' => cons X x (repeat' X x count')
  end.

Check repeat'.
(* ===> forall X : Type, X -> nat -> list X *)
Check repeat.
(* ===> forall X : Type, X -> nat -> list X *)

Fixpoint repeat'' X x count : list X :=
  match count with
  | 0        => nil _
  | S count' => cons _ x (repeat'' _ x count')
  end.


Definition list123 :=
  cons nat 1 (cons nat 2 (cons nat 3 (nil nat))).

Definition list123' :=
  cons _ 1 (cons _ 2 (cons _ 3 (nil _))).

Arguments nil {X}.
Arguments cons {X} _ _.
Arguments repeat {X} x count.

Definition list123'' := cons 1 (cons 2 (cons 3 nil)).

Fixpoint repeat''' {X : Type} (x : X) (count : nat) : list X :=
  match count with
  | 0        => nil
  | S count' => cons x (repeat''' x count')
  end.


Inductive list' {X:Type} : Type :=
  | nil' : list'
  | cons' : X -> list' -> list'.


Fixpoint app {X : Type} (l1 l2 : list X)
             : (list X) :=
  match l1 with
  | nil      => l2
  | cons h t => cons h (app t l2)
  end.

Fixpoint rev {X:Type} (l:list X) : list X :=
  match l with
  | nil      => nil
  | cons h t => app (rev t) (cons h nil)
  end.

Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | nil => 0
  | cons _ l' => S (length l')
  end.

Check nil.

Example test_rev1 :
  rev (cons 1 (cons 2 nil)) = (cons 2 (cons 1 nil)).
Proof. reflexivity.  Qed.

Example test_rev2:
  rev (cons true nil) = cons true nil.
Proof. reflexivity.  Qed.

Example test_length1: length (cons 1 (cons 2 (cons 3 nil))) = 3.
Proof. reflexivity.  Qed.

Fail Definition mynil := nil.

Definition mynil : list nat := nil.

Check @nil.

Definition mynil' := @nil nat.

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

Definition list123''' := [1; 2; 3].

(*Exercise 2*)
Theorem app_nil_r : forall (X:Type), forall l:list X,
  l ++ [] = l.
Proof.
  intros. induction l as [|l' l'' IHl'].
  - reflexivity.
  - simpl. rewrite IHl'. reflexivity.
Qed.

(*Exercise 3*)
Theorem app_assoc : forall A (l m n:list A),
  l ++ m ++ n = (l ++ m) ++ n.
Proof.
  intros. induction l as [|l' l'' IHl'].
  - reflexivity.
  - simpl. rewrite IHl'. reflexivity.
Qed.

(*Exercise 4*)
Lemma app_length : forall (X:Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros. induction l1 as [| l' l'' IHl'].
  - reflexivity.
  - simpl. rewrite <- IHl'. reflexivity.
Qed.

(*Exercise 5*)
Theorem rev_app_distr: forall X (l1 l2 : list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros. induction l1 as [|l' l'' IHl'].
  - simpl. rewrite app_nil_r. reflexivity.
  - simpl. rewrite IHl'. rewrite app_assoc. reflexivity.
Qed.

(*Exercise 6*)
Theorem rev_involutive : forall X : Type, forall l : list X,
  rev (rev l) = l.
Proof.
  intros. induction l as [|l' l'' IHl'].
  - reflexivity.
  - simpl. rewrite rev_app_distr. rewrite IHl'. reflexivity.
Qed.

Inductive prod (X Y : Type) : Type :=
| pair : X -> Y -> prod X Y.

Arguments pair {X} {Y} _ _.

Notation "( x , y )" := (pair x y).
Notation "X * Y" := (prod X Y) : type_scope.

Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with
  | (x, y) => x
  end.

Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with
  | (x, y) => y
  end.

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y)
           : list (X*Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: (combine tx ty)
  end.

(*Exercise 7*)
(** The function [split] is the right inverse of [combine]: it takes a
    list of pairs and returns a pair of lists.  In many functional
    languages, it is called [unzip].

    Fill in the definition of [split] below.  Make sure it passes the
    given unit test. *)

Fixpoint split {X Y : Type} (l : list (X*Y))
               : (list X) * (list Y) :=
   match l with
  | nil => ([], [])
  | (x, y) :: t => ( x :: (fst (split t)), y :: (snd (split t)))
end.
  

Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof. reflexivity. Qed.

Inductive option (X:Type) : Type :=
  | Some : X -> option X
  | None : option X.

Arguments Some {X} _.
Arguments None {X}.

Fixpoint nth_error {X : Type} (l : list X) (n : nat)
                   : option X :=
  match l with
  | [] => None
  | a :: l' => if eqb n O then Some a else nth_error l' (pred n)
  end.

Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.
Example test_nth_error2 : nth_error [[1];[2]] 1 = Some [2].
Proof. reflexivity. Qed.
Example test_nth_error3 : nth_error [true] 2 = None.
Proof. reflexivity. Qed.

(*Exercise 8*)
Definition hd_error {X : Type} (l : list X) : option X :=
  match l with
  | nil => None 
  | h :: t => Some h
end.

Check @hd_error.

Example test_hd_error1 : hd_error [1;2] = Some 1.
 Proof. reflexivity. Qed.
Example test_hd_error2 : hd_error  [[1];[2]]  = Some [1].
 Proof. reflexivity. Qed.

(*Exercise 9*)
(*Define polymorphic binary trees data structure*)

Inductive poly_b_tree {T: Type}: Type:=
  |emp_tree : poly_b_tree
  |node: T -> poly_b_tree -> poly_b_tree -> poly_b_tree.

(*Exercise 10:
Define a function that receives a polymorphic binary tree and returns 
the number of nodes within that tree.
*)

Fixpoint Exc_10 {T : Type} (x : @poly_b_tree T): nat :=
  match x with
  | emp_tree => O
  | node x y z => S(Exc_10 y) + (Exc_10 z)
end.

(*Exercise 11:
Define a function that returns the height of the input polymorphic 
binary tree.
*)
Fixpoint Exc_11 {T : Type} (x : @poly_b_tree T) : nat :=
    match x with
    | emp_tree => 0
    | node x y z => 1 + max (Exc_11 y) (Exc_11 z)
    end.

(*Exercise 12:
Define a function that decides whether a polymorphic binary is a leaf.
*)
Definition Exc_12 {T : Type} (x : @poly_b_tree T) : bool :=
    match x with
    | node v emp_tree emp_tree => true
    | _ => false
    end.


