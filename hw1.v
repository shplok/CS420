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

simpl.
reflexivity.

Qed.
(**

Show that equality for natural numbers is reflexive.

 *)
Theorem ex2:
  forall (x:nat), x = x.
Proof.
intros x.
simpl.
reflexitivty.
Qed.

(**

Show that [1 + n] equals the successor of [n].

 *)
Theorem ex3:
  forall n, 1 + n = S n.
Proof.
intros n,
simpl.
reflexivity.
Qed.

(**

Show that if [x = y], then [y = x].

 *)
Theorem ex4:
  forall x (y:nat), x = y -> y = x.
Proof.

Admitted.

(**

Show that if the result of the conjunction and the disjunction equal,
then both boolean values are equal.


 *)
Theorem ex5:
  forall (b c : bool), (andb b c = orb b c) -> b = c.
Proof.

Admitted.

(**

In an addition, we can move the successor of the left-hand side to
the outer most.


 *)
Theorem ex6:
  forall n m, n + S m = S (n + m).
Proof.

Admitted.

(**

If two additions are equal, and the numbers to the left of each addition
are equal, then the numbers to the right of each addition must be equal.
To complete this exercise you will need to use the auxiliary
theorem: eq_add_S


 *)
Theorem ex7:
  forall x y n, n + x = n + y -> x = y.
Proof.

Admitted.

(**

Show that addition is commutative.
Hint: You might need to prove `x + 0 = x` and `S (y + x) = y + S x`
separately.


 *)
Theorem ex8:
  forall x y, x + y = y + x.
Proof.

Admitted.

(**

If two additions are equal, and the numbers to the right of each addition
are equal, then the numbers to the left of each addition must be equal.

Hint: Do not try to prove this theorem directly. You should be using
auxiliary results. You can use Admitted theorems.


 *)
Theorem ex9:
  forall x y n, x + n = y + n -> x = y.
Proof.

Admitted.



