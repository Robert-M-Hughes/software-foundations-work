(*COMP 293: Midterm Exam 1*)
(*There are 100 points + 10 extra points*)
(* You have 120 minutes to submit your work in Canvas.*)


From LF Require Export Induction.

(*Problem 1: 35 points*) 

(* a. (10 points)
Define a type consisting of 6 values, representing 
divisions of a sport league: atlantic, central, southeast, northwest, 
pacific, and southwest.
*)

Inductive divisions : Type :=
  | atlantic : divisions
  | central : divisions
  | southeast : divisions
  | northwest : divisions
  | pacific : divisions
  | southwest : divisions.

(* b. (10 points)
Next define the type of conferences on that sport league: east and west.
*)

Inductive conferences : Type :=
  | east : conferences
  | west : conferences.

(* c. (10 points)
Define a function from divisions to conferences, that specifies
which division is within which conference.
Atlantic, central and southeast divisions are in the eastern conference, and
the other three are in the western conference.
*)

Definition div_to_conf (d:divisions) : conferences :=
  match d with
  | atlantic   => east
  | central    => east
  | southeast  => east
  | northwest  => west
  | pacific    => west
  | southwest  => west
  end.

(* d. (5 points)
Prove that central and southeast are in the same conference. 
*)

Example test_div_to_conf:
  div_to_conf(central) = div_to_conf(southeast).
Proof. reflexivity. Qed.



(*Problem 2: 10 points

Prove that for any two booleans b1 and b2, negation of b1 \/  b2 is 
the same as negation of b1 and negation of b2, i.e.,
negation (b1 \/ b2) = (negation b1) /\ (negation b2)
Note: \/ denotes logical "or".
/\ denotes logical "and".
You will need to specify the theorem in terms of boolean functions representing
logical and (/\), logical or (\/), and negation. 
*)

Theorem problem_2: forall b1 b2,
  negb ( orb b1 b2) = andb (negb b1) (negb b2).
Proof.
  intros. destruct b1.
  - reflexivity.
  - reflexivity.
Qed.

(*Problem 3: 15 points

Prove that for any natural number n, (n - 1) * 2 = n * 2 - 2.
Hint: You may need to define and prove a prerequisite result in order to prove it.
*)
(* From the HW1*)


Theorem problem_3: forall n, 
  (n-1) * 2 = n * 2 - 2.
Proof.
  intros. induction n as [| n'].
  - simpl. reflexivity.
  - simpl. destruct n'. 
    + simpl. reflexivity.
    + simpl. reflexivity.
Qed.




(*Problem 4: 50 points*)

(* a. (20 points)
Define the power function: pow n m, denoted by n^m, 
representing n to the power of m.
(You don't need to define the notation ^. Go with "pow".)
*)

Fixpoint pow (n m : nat) : nat :=
  match m with
    | O => S O
    | S n' => mult n (pow n n')
  end.


(*Compute pow 2 4.*)

(* b. (30 points)
Show that for any n, m, and p: n^m * n^p = n^(m+p). 
(Use "pow" syntax to specify the theorem.)
*)



(*question 14 from hw1*)

Lemma distribute : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  intros. induction n as [| n'].
  reflexivity.
  simpl. rewrite IHn'. rewrite plus_assoc. reflexivity.  Qed.

(* question 15 from hw1*)
Lemma mult_3_dist : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  intros. induction n as [| n'].
  reflexivity.
  simpl. rewrite IHn'. rewrite distribute. reflexivity.
Qed.


Theorem problem_4: forall n m p,
  (pow n m) * (pow n p) = pow n (m + p).
Proof.
  intros. induction m as [| m'].
  - simpl. rewrite <- plus_n_O. reflexivity.
  - simpl. rewrite <- IHm'.  rewrite mult_3_dist. reflexivity.
Qed.



