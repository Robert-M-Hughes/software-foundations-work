From LF Require Export Tactics.

(*Midterm #2: 100 points + 15 extra points*)

(*--------------------------------------------------------*)
(*Problem 1a: (10 points)
Define function itemAtIndex that receives an index n 
and a list of any type X, and returns the item in the 
list in the given index n. Note that indexing starts 
from 0. After defining the function make sure that the 
units tests test1_itemAtIndex, test2_itemAtIndex, and 
test3_itemAtIndex succeed.*)

(*Put your definition here. Next, uncomment the following 
unit tests and check their success.*)


Fixpoint itemAtIndex ( n : nat ) {X : Type} (l : list X) : option X :=
  match n, l with
    | O, x :: l' => Some x
    | O, [] => None
    | S m, [] => None
    | S n, x :: l => itemAtIndex n l
  end.



Example test1_itemAtIndex:
  itemAtIndex 2 [1;9;5;2;7] = Some 5.
Proof. reflexivity. Qed.

Example test2_itemAtIndex:
  itemAtIndex 5 [1;9;5;2;7] = None.
Proof. reflexivity. Qed.

Example test3_itemAtIndex:
  itemAtIndex 0 [true;false;false;true] = Some true.
Proof. reflexivity. Qed.



(*--------------------------------------------------------*)
(*Problem 1b: (15 points)
Prove that itemAtIndex function does not return a proper item
of the list, if the input index is greater than or equal to
the number of items in the list.*)
Theorem problem_1b : forall {X : Type} ( n : nat ) ( l : list X ),
  n >= length l -> itemAtIndex n l = None.
  
Proof.
induction l; destruct n; simpl; intros; auto.
    inversion H. 
Admitted.
    
    
    



(*--------------------------------------------------------*)
(*Problem 2a. (10 points)
Define function grabFirstN that receives a number n and a list
of any type X, and returns the first n items of the input list.
After defining the function make sure that the units tests 
test1_grabFirstN, test2_grabFirstN, test3_grabFirstN, and
test4_grabFirstN succeed.*)
Fixpoint grabFirstN {X : Type} (n : nat) (l : list X):list X :=
match n, l with
  | O, l => []
  | S n, [] => [] 
  | S n, h :: t => h :: grabFirstN n t
end.

(*Put your definition here. Next, uncomment the following 
unit tests and check their success.*)


Example test1_grabFirstN:
  grabFirstN 3 [false;false;true;false;true] = [false;false;true].
Proof. reflexivity. Qed.

Example test2_grabFirstN:
  grabFirstN 1 [9;3;7;1;6] = [9].
Proof. reflexivity. Qed.

Example test3_grabFirstN:
  grabFirstN 0 [9;3;7;1;6] = [].
Proof. reflexivity. Qed.

Example test4_grabFirstN:
  grabFirstN 10 [[9;3];[7];[1;6]] = [[9;3];[7];[1;6]].
Proof. reflexivity. Qed.


(*--------------------------------------------------------*)
(*Problem 2b. (10 points)
Let n be the number of items in a list. Prove that grabbing 
the first n items of the list returns that list fully.
*)
Theorem problem_2b: forall {X : Type} ( n : nat ) ( l : list X ),
 length l = n -> (grabFirstN n l) = l.
Proof.
  intros. generalize dependent n. induction l.
  simpl. intros. induction n.
  reflexivity. reflexivity.
Admitted.

(*--------------------------------------------------------*)
(*Problem 2c: (15 points)
Prove that if n is less than or equal to m, then the number of
items in the list resulted by grabbing the first n items of a list l
is less than or equal to the number of items in the list resulted
by grabbing the first m items of l.*)

Theorem problem_2c: forall {X : Type} ( n m : nat ) ( l : list X ),
  leb n m = leb (length (grabFirstN n l)) (length (grabFirstN m l)).
Proof.
  intros.
  destruct n. destruct m. destruct l.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - destruct grabFirstN. simpl.
Admitted.

(*--------------------------------------------------------*)
(*Problem 3a. (10 points)
Define function indexOfItem that receives a number x and a list
of numbers l, and returns the index in which x resides in l.
Note that indexing starts from 0. After defining the function 
make sure that the units tests test1_indexOfItem, test2_indexOfItem, 
and test1_indexOfItem succeed.*)

(*Working but is with a fail recursive method*)
Fixpoint indexOfItem  (x:nat)(l:list nat) (counter: nat) : option nat:=
  match l with
  | [] => None
  | a :: l' => match eqb a x with
              | true => Some counter
              | false => indexOfItem x l' (counter + 1)
              end
  end.


(*Put your definition here. Next, uncomment the following 
unit tests and check their success.*)

Example test1_indexOfItem:
  indexOfItem 5 [1;5;2;3;7] 0 = Some 1.
Proof. reflexivity. Qed.

Example test2_indexOfItem:
  indexOfItem 1 [1;5;2;3;7] 0 = Some 0.
Proof. reflexivity. Qed.

Example test3_indexOfItem:
  indexOfItem 9 [1;5;2;3;7] 0 = None.
Proof. reflexivity. Qed.




(*--------------------------------------------------------*)
(* Problem 3b: (15 points)
Prove that indexOfItem and itemAtIndex are reverse of each other. 
That is, if index of item x in list l is i, then item at index i 
of list l is x. 
*)
Theorem problem_3b: forall {X : Type} ( x i : nat ) ( l : list X ),
 indexOfItem x n l = i -> itemAtIndex i l = x.
Proof.
intros.
Admitted.



(*--------------------------------------------------------*)
(* Problem 4: (15 points)
Consider the following definition of binary trees. A binary tree is a
min-heap, if the value at every node is less than or equal to all 
its child nodes. Define function isMinHeap that receives a binary
tree of numbers as input and returns true if that tree is a min-heap.
Otherwise, it returns false. Make sure that the units tests 
test1_mytree1_minheap, and test2_mytree2_minheap succeed.
Note: Heaps need to also be complete binary trees, but let's
ignore that property in this question for the sake of simplicity.*)

Inductive btree (X: Type) : Type :=
  | emp_btr : btree X
  | node_btr: X -> btree X -> btree X -> btree X.

Arguments emp_btr {X}.
Arguments node_btr {X} _ _ _.

Definition mytree1 : btree nat := 
  node_btr 1 (node_btr 2 (node_btr 2 emp_btr emp_btr) 
                         (node_btr 5 emp_btr (node_btr 7 emp_btr emp_btr))
             )
             (node_btr 3 (node_btr 8 emp_btr emp_btr) emp_btr).

Definition mytree2 : btree nat := 
  node_btr 1 (node_btr 2 (node_btr 2 emp_btr emp_btr) 
                         (node_btr 5 emp_btr (node_btr 4 emp_btr emp_btr))
             )
             (node_btr 3 (node_btr 8 emp_btr emp_btr) emp_btr).

(*Put your definition here. Next, uncomment the following 
unit tests and check their success.*)


Definition get_value (b_tree: btree nat) : nat :=
  match b_tree with
  | emp_btr => 999 (*High number that will not occur*)
  | node_btr p q r => p
  end.


Fixpoint isMinHeap (b_tree: btree nat) : bool :=
  match b_tree with
  | emp_btr => true
  | node_btr p q r => match andb (leb p (get_value q)) (leb p (get_value r)) with
                         | true => andb (isMinHeap q) (isMinHeap r)
                         | false => false
                         end
  end.


Example test1_mytree1_minheap:
  isMinHeap mytree1 = true.
Proof. reflexivity. Qed.

Example test2_mytree2_minheap:
  isMinHeap mytree2 = false.
Proof. reflexivity. Qed.


(*--------------------------------------------------------*)
(*Extra Point Problem: 15 Points
Consider the following definition of general trees, i.e., trees with
arbitrary number of children. Define function multNodes that receives
a general tree of numbers as input and returns the multiplication of
all values in the nodes. Make sure that the unit test 
test_mytree_mult succeeds.
*)

(*Working*)

Inductive tree (X: Type) : Type :=
  | emp_tr : tree X
  | node_tr: X -> list (tree X) -> tree X.

Arguments node_tr {X} _ _.
Arguments emp_tr {X}.
Arguments tree {X}.

Definition mytree3 : @tree nat :=
  node_tr 1 [node_tr 5 [node_tr 2 []];
             node_tr 8 [];
             node_tr 7 [node_tr 3 []; node_tr 4 []]
            ].

(*Put your definition here. Next, uncomment the following 
unit tests and check their success.*)
Fixpoint multNodes (tr: @tree nat) : nat :=
  let fix subtree_node (l: list tree) : nat := 
        match l with
          |nil => 1
          |h::t =>  ( multNodes h ) * ( subtree_node t )
        end
  in
  match tr with
  | emp_tr => 1
  | node_tr r l => r * (subtree_node l)
  end.
Compute multNodes mytree3.

Example test_mytree3_mult:
  multNodes mytree3 = 6720.
Proof. reflexivity. Qed.





