(*Robert Hughes
Comp 293 Hw 2
This is the document for the second homework for the software reliability class*)

From LF Require Export Poly.
From LF Require Export Lists.
From LF Require Export Basics.
From LF Require Export Induction.

Definition fold_length {X : Type} (l : list X) : nat :=
fold (fun _ n => S n) l 0.




(*Question #1*)
Theorem question_1: forall X (l : list X),
  fold_length l = length l.
Proof.
  intros.
  induction l as [| h t IH].
  - reflexivity.
  - simpl.
    rewrite <- IH.
    unfold fold_length.
    simpl. reflexivity.
Qed.


(*Question #2*)
Definition fold_map {X Y:Type} (f : X -> Y) (l : list X) : list Y :=
fold (fun x => fun xs => f x :: xs) l [].

Theorem question_2: forall X Y (l : list X) (f: X -> Y),
  fold_map f l = map f l.
Proof.
  intros.
  induction l as [| h t IH].
  - reflexivity.
  - simpl.
    rewrite <- IH.
    unfold fold_map.
    simpl. reflexivity.
Qed.

(*Question 3a*)

Definition Nat := forall X : Type, (X -> X) -> X -> X.


(*Question 3b*)

Definition zero : Nat :=
  fun (X : Type) (f : X -> X) (x : X) => x.

Definition one : Nat := 
  fun (X : Type) (f : X -> X) (x : X) => f x.

Definition two : Nat :=
  fun (X : Type) (f : X -> X) (x : X) => f (f x).

Definition three : Nat :=
  fun (X : Type) (f : X -> X) (x : X) => f( f (f x) ).

(*Question 3c*)

Definition succ (a : Nat) : Nat :=
  fun (X : Type) (f : X -> X) (x: X) => f (a X f x).


(*Question 3d*)

Example succ_1 : succ zero = one.
Proof.
intros. simpl. reflexivity. Qed.

Example succ_2 : succ one = two.
Proof.
intros. reflexivity. Qed.

Example succ_3 : succ two = three.
Proof.
intros. reflexivity. Qed.

(*Question 3e*)
Definition plus (a b : Nat) : Nat :=
  fun (X : Type) (f : X -> X) (x: X) => b X f (a X f x).


(*Question 3f*)

Example plus_1 : plus zero one = one.
  Proof. reflexivity. Qed.

Example plus_2 : plus two three = plus three two.
  Proof. reflexivity. Qed.

Example plus_3 :
  plus (plus two two) three = plus one (plus three three).
  Proof. reflexivity. Qed.

(*Question 3g*)

Definition mult (a b : Nat) : Nat :=
  fun (X : Type) (f : X -> X) => b X (a X f).

(*Question 3h*)

Example mult_1 : mult one one = one.
  Proof. reflexivity. Qed.

Example mult_2 : mult zero (plus three three) = zero.
  Proof. reflexivity. Qed.

Example mult_3 : mult two three = plus three three.
  Proof. reflexivity. Qed.


(*Question 3i*)

Definition exp (a b : Nat) : Nat := 
fun (X : Type) (f : X -> X) (x : X) =>  (b (X -> X) (a X) f) x.

(*Question 3j*)

Example exp_1 : exp two two = plus two two.
Proof. reflexivity. Qed.

Example exp_2 : exp three two = plus (mult two (mult two two)) one.
Proof. reflexivity. Qed.

Example exp_3 : exp three zero = one.
Proof. reflexivity. Qed.


(*Question 3k*)
Theorem question_3k: forall n : Nat,
plus n one = succ n.
Proof.
  intro n.  reflexivity. Qed.






(*Question 3l*)
Theorem question_3l: forall (n m: Nat),
mult n (succ m) = plus (mult n m) n.
Proof.

  intro n. reflexivity. Qed.


(*Question 4*)
Definition func_comp {A B C : Type} (g : B -> C) (f : A -> B) :=
  fun x => g (f x).

(* 
Theorem question_4: forall(),
*)
Theorem composition_associative : forall A B C D (f : A -> B) (g : B -> C) (h : C -> D),
  func_comp (func_comp h g) f = func_comp h (func_comp g f).
Proof.
  intros. reflexivity. Qed.



(*Question 5*)
(*Question 5a*)
Inductive tree (X:Type) : Type :=
  | empty : tree X
  | branch : X -> list (tree X) -> tree X.

Arguments tree {X}.
Arguments empty {X}.
Arguments branch {X}.


(*Question 5b*)
Definition mytree :=
  branch 1 [ branch 5 [ branch 2 [empty] ] ;  branch 8 [empty] ;
          branch 7 [ branch 3 [empty];branch 4 [empty] ] ].

(*Question 5c*)
Definition isleaf {X: Type} (node: @tree X) : bool :=
  match node with
    | empty => true
    | _ => false
  end.

(*Question 5d*)
Example test_isleaf:
  isleaf mytree = false.
Proof.
  simpl. reflexivity.
Qed.

(* Test tree for the height
Definition mytree_test :=
  branch 1[ branch 3 [ branch 5 [ empty]; branch 2 [branch 2 [branch 2 [branch 2 [empty]]]] ]].

*)

(*Question 5e*)

Fixpoint height {X: Type} (tr: @tree X) : nat :=
  let fix subtree_height (l: list tree) : nat := 
        match l with
          |nil => 0
          |h::t => max ( height h ) ( subtree_height t )
        end
  in
  match tr with
  | empty => 0
  | branch _ l => S (subtree_height l)
  end.


(*Compute height mytree_test .*)


(*Question 5f*)

Example test_height:
  height mytree = 3.
Proof.
  simpl. reflexivity.
Qed.



(*Question 5g*)
Fixpoint sum_nodes (tr: @tree nat) : nat :=
  let fix subtree_node (l: list tree) : nat := 
        match l with
          |nil => 0
          |h::t =>  ( sum_nodes h ) + ( subtree_node t )
        end
  in
  match tr with
  | empty => 0
  | branch r l => r + (subtree_node l)
  end.

Compute sum_nodes mytree.



(*Question 5h*)
Example test_sum_nodes:
  sum_nodes mytree = 30.
Proof.
  simpl. reflexivity.
Qed.



(*Question 6*)
(*Question 6a*)

Inductive b_tree (X: Type) : Type :=
  | emp_tree : b_tree X
  | node: X ->b_tree X -> b_tree X-> b_tree X.

Arguments b_tree {X}.
Arguments emp_tree {X}.
Arguments node {X}.

Definition mytree2 :=
node 1
    (node 2
        (node 4 emp_tree emp_tree)
        (node 5 emp_tree emp_tree))
    (node 3 emp_tree emp_tree).




(*Question 6b*)
Fixpoint preorder {X: Type} (btr: b_tree) : list X:=
  match btr with
  | emp_tree => []
  | node p q r =>   [p] ++ preorder q ++ preorder r 
  end.

(*Question 6c*)
Compute preorder mytree2.


(*Question 6d*)
Fixpoint inorder {X: Type} (btr: b_tree) : list X:=
  match btr with
  | emp_tree => []
  | node p q r => inorder q ++ [p] ++ inorder r
  end.


(*Question 6e*)
Compute inorder mytree2.

(*Question 6f*)
Fixpoint postorder {X: Type} (btr: b_tree) : list X:=
  match btr with
  | emp_tree => []
  | node p q r =>  postorder q ++ postorder r ++  [p]
  end.


(*Question 6g*)
Compute postorder mytree2.


(*Question 6h*)
Theorem question_6h : forall (X : Type) ( tree : @b_tree X ),

  length (preorder tree) = length (postorder tree).
Proof.
  intros X tree. induction tree.
  - reflexivity.
  - simpl. rewrite app_length. rewrite app_length. rewrite app_length. simpl. rewrite IHtree1.
 rewrite IHtree2.  rewrite <- plus_n_Sm. rewrite <- plus_n_O. rewrite plus_n_Sm. reflexivity.
Qed.



(*Question 6i*)
Fixpoint count_nodes {X: Type} (btr : @b_tree X) : nat :=
  match btr with 
  |emp_tree => 0
  |node x y z => S( count_nodes y) + (count_nodes z)
end.


Theorem question_6i: forall (X:Type) (tr : @b_tree X),
count_nodes tr = length(preorder tr).
Proof.
  intros. induction tr.
  - reflexivity.
  - simpl. rewrite app_length. rewrite IHtr2. rewrite IHtr1. reflexivity.
Qed.



(*Question 6j*)
Fixpoint height_btr {X: Type} (btr : @b_tree X) : nat :=
  match btr with
  | emp_tree => 0
  | node _ t1 t2 => 1 + max (height_btr t1) (height_btr t2)
  end.

Lemma max_comm :
  forall n m : nat, max n m = max m n.
Proof.
intro n; induction n as [| n' IHn'];
  intro m; destruct m as [| m'];
    simpl; try (rewrite IHn'); trivial.
Qed.

Lemma plus_par : forall n m, n + m = (n + m).
Proof.
  intros n m. reflexivity.
Qed.

Lemma leb_refl : forall n:nat,
  leb n n = true.
Proof.
  intros n. induction n as [|n'].
  - reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.

Lemma leb_max : forall n m,
  leb n (max n m) = true.
Proof.
  intros.
  generalize dependent m.
  induction n.
  -simpl. reflexivity.
  - destruct m.
    + simpl. apply leb_refl.
    + simpl. destruct n.
      * simpl. reflexivity.   
      * rewrite IHn. reflexivity.
Qed.

Lemma leb_plus_max : forall n m,
  leb (max n m) (n + m) = true.
Proof.
  intros.
  generalize dependent m.
  intros. induction n. 
  - simpl. rewrite leb_refl. reflexivity.
Admitted.


Theorem question_6j : forall {X: Type}(t : @b_tree X),
      leb (height_btr t) (count_nodes t)=true. 
Proof.
  intros.
  simpl.
  - induction t.
    apply leb_refl.
  simpl. destruct t1. simpl.
  + rewrite IHt2. reflexivity.
  Admitted.

Theorem question_6j_other: forall (X:Type) (tr : @b_tree X),
  leb (height_btr tr) (count_nodes tr) = true.
Proof.
  intros. induction tr.
  - reflexivity.
  - simpl. 
Admitted.



























