(*
        #####################################################
        ###  PLEASE DO NOT DISTRIBUTE SOLUTIONS PUBLICLY  ###
        #####################################################
*)
(*
    You are only allowed to use these tactics:

    simpl, reflexivity, intros, rewrite, destruct, induction, apply, assert

    You are not allowed to use theorems outside this file *unless*
    explicitly recommended.
*)

(* ---------------------------------------------------------------------------*)




(**

Show that 5 equals 5.

 *)
Theorem ex1:
  5 = 5.
Proof.
simpl.          (* simplify any expressions if possible *)
reflexivity.    (* prove equality by showing both sides are identical *)
Qed.
(**

Show that equality for natural numbers is reflexive.

 *)
Theorem ex2:
  forall (x:nat), x = x.
Proof.
intros x.       (* introduce x into context *)
simpl.          (* simplify if possible *)
reflexivity.    (* prove equality by showing both sides are identical *)
Qed.

(**

Show that [1 + n] equals the successor of [n].

 *)
Theorem ex3:
  forall n, 1 + n = S n.
Proof.
intros num.     (* introduce n as num into context *)
simpl.          (* simplify 1 + n to S n *)
reflexivity.    (* prove equality by showing both sides are identical *)
Qed.

(**

Show that if [x = y], then [y = x].

 *)
Theorem ex4:
  forall x (y:nat), x = y -> y = x.
Proof.
intros x y H.   (* introduce x, y and hypothesis H into context *)
rewrite -> H.   (* replace x with y based on hypothesis H *)
simpl.          (* simplify if possible *)
reflexivity.    (* prove equality by showing both sides are identical *)
Qed.

(**

Show that if the result of the conjunction and the disjunction equal,
then both boolean values are equal.


 *)
Theorem ex5:
  forall (b c : bool), (andb b c = orb b c) -> b = c.
Proof.
intros b c H.   (* introduce b, c and hypothesis H into context *)
destruct b, c.  (* case analysis on both b and c *)
- reflexivity.  (* true = true case *)
- simpl in H.   (* simplify hypothesis for true = false case *)
  rewrite H.    (* use the hypothesis *)
  reflexivity.  (* prove equality *)
- simpl in H.   (* simplify hypothesis for false = true case *)
  rewrite H.    (* use the hypothesis *)
  reflexivity.  (* prove equality *)
- reflexivity.  (* false = false case *)
Qed.


(**

In an addition, we can move the successor of the left-hand side to
the outer most.


 *)
Theorem ex6:
  forall n m, n + S m = S (n + m).
Proof.
intros.         (* introduce n and m into context *)
induction n.    (* induction on n *)
- simpl.        (* base case: simplify 0 + S m *)
  reflexivity.  (* prove equality *)
- simpl.        (* inductive case: simplify S n + S m *)
  rewrite IHn.  (* use induction hypothesis *)
  reflexivity.  (* prove equality *)
Qed.

(**

If two additions are equal, and the numbers to the left of each addition
are equal, then the numbers to the right of each addition must be equal.
To complete this exercise you will need to use the auxiliary
theorem: eq_add_S

 *)
Check eq_add_S.
Theorem ex7:
  forall x y n, n + x = n + y -> x = y.
Proof.
intros.         (* introduce variables and hypothesis *)
induction n.    (* induction on n *)
- simpl in H.   (* base case: simplify hypothesis *)
  apply H.      (* use hypothesis directly *)
- simpl in H.   (* inductive case: simplify hypothesis *)
  apply eq_add_S in H.  (* use auxiliary theorem *)
  apply IHn.    (* use induction hypothesis *)
  rewrite H.    (* use transformed hypothesis *)
  reflexivity.  (* prove equality *)
Qed.

(**

Show that addition is commutative.
Hint: You might need to prove `x + 0 = x` and `S (y + x) = y + S x`
separately.


 *)

Theorem add_succ_r: 
  forall x y, x + S y = S (x + y).
Proof.
intros x y.     (* introduce x and y into context *)
induction x.    (* induction on x *)
- simpl.        (* base case: simplify 0 + S y *)
  reflexivity.  (* prove equality *)
- simpl.        (* inductive case: simplify S x + S y *)
  rewrite IHx.  (* use induction hypothesis *)
  reflexivity.  (* prove equality *)
Qed.

Theorem ex8:
  forall x y, x + y = y + x.
Proof.
intros x y.     (* introduce x and y into context *)
induction y.    (* induction on y *)
- assert (H: x + 0 = x).  (* create auxiliary hypothesis *)
  { induction x.          (* nested induction on x *)
    - simpl.              (* base case *)
      reflexivity.        (* prove equality *)
    - simpl.              (* inductive case *)
      rewrite IHx.        (* use inner induction hypothesis *)
      reflexivity. }      (* prove equality *)
  rewrite H.              (* use auxiliary hypothesis *)
  reflexivity.            (* prove equality *)
- simpl.                  (* simplify for successor case *)
  rewrite add_succ_r.     (* use auxiliary theorem *)
  rewrite IHy.            (* use induction hypothesis *)
  reflexivity.            (* prove equality *)
Qed.

(**

If two additions are equal, and the numbers to the right of each addition
are equal, then the numbers to the left of each addition must be equal.

Hint: Do not try to prove this theorem directly. You should be using
auxiliary results. You can use Admitted theorems.


 *)
Theorem ex9:
  forall x y n, x + n = y + n -> x = y.
Proof.
intros.         (* introduce variables and hypothesis *)
rewrite ex8 in H.     (* apply commutativity to left side *)
rewrite (ex8 y) in H. (* apply commutativity to right side *)
apply ex7 in H.       (* use auxiliary theorem *)
rewrite H.            (* use transformed hypothesis *)
reflexivity.          (* prove equality *)
Qed.

