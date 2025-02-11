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
reflexivity.
Qed.

(**

Show that [1 + n] equals the successor of [n].

 *)
Theorem ex3:
  forall n, 1 + n = S n.
Proof.
intros num.
simpl.
reflexivity.
Qed.

(**

Show that if [x = y], then [y = x].

 *)
Theorem ex4:
  forall x (y:nat), x = y -> y = x.
Proof.
intros x y H.
rewrite -> H.
simpl.
reflexivity.
Qed.

(**

Show that if the result of the conjunction and the disjunction equal,
then both boolean values are equal.


 *)
Theorem ex5:
  forall (b c : bool), (andb b c = orb b c) -> b = c.
Proof.
intros.
destruct b.
- assert (H' : forall (b : bool), orb true b = true). { reflexivity. }
  rewrite H' in H.
  rewrite <- H.
  reflexivity.
- assert (H': forall (b : bool), andb false b = false). { reflexivity. }
  rewrite H' in H.
  rewrite -> H.
  reflexivity.
Qed.


(**

In an addition, we can move the successor of the left-hand side to
the outer most.


 *)
Theorem ex6:
  forall n m, n + S m = S (n + m).
Proof.
intros.
induction n.

- simpl.
    reflexivity.

- simpl.
    rewrite IHn.
    reflexivity.
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
intros.
induction n.

- simpl in H.
    rewrite H.
    reflexivity.

- simpl in H. apply eq_add_S in H.
    apply IHn.
    rewrite H.
    reflexivity.
Qed.

(**

Show that addition is commutative.
Hint: You might need to prove `x + 0 = x` and `S (y + x) = y + S x`
separately.


 *)

Lemma x_plus0 x :
  x + 0 = x.
Proof.
  induction x.
  - simpl. reflexivity.
  - simpl. rewrite IHx. reflexivity.
Qed.

Lemma x_plusSy x y :
  x + S y = S (x + y).
Proof.
  induction x.
  - simpl. reflexivity.
  - simpl. rewrite IHx. reflexivity.
Qed.

Theorem ex8:
  forall x y, x + y = y + x.
Proof.
  intros x y.
  induction x.
  - (* Case: 0 + y = y + 0 *)
    simpl.
    assert (H: y + 0 = y).
    { apply x_plus0. }
    rewrite H.
    reflexivity.
  - (* Case: S x + y = y + S x *)
    simpl.
    assert (H: y + S x = S (y + x)).
    { apply x_plusSy. }
    rewrite H.
    rewrite IHx.
    reflexivity.
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
intros.
rewrite ex8 in H. rewrite (ex8 y) in H. apply ex7 in H.
rewrite H.
reflexivity.
Qed.



