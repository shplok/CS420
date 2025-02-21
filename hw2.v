(*
        #####################################################
        ###  PLEASE DO NOT DISTRIBUTE SOLUTIONS PUBLICLY  ###
        #####################################################
*)

Require Turing.Util.
Require Import Coq.Lists.List.
Import ListNotations.


(* ----------sawyer----------------------------------------------------*)


(*

Study the definition of [Turing.Util.pow] and [Turing.Util.pow1]
and then show that [Turing.Util.pow1] can be formulated in terms of
[Turing.Util.pow].
Material: https://gitlab.com/umb-svl/turing/blob/main/src/Util.v

 *)
Theorem ex1:
  forall (A:Type) (x:A) n, Util.pow [x] n = Util.pow1 x n.
Proof.
  intros.
  induction n.
  - simpl. (* base case, pow and pow1 both return the identity *)
    reflexivity.
  - simpl. (* recursive case, pow1 should match pow applied to singleton list *)
    rewrite -> IHn. (* applying induction hypothesis *)
    reflexivity.
Qed.

(**

Study recursive definition of [List.In] and the inductive definition of
[List.Exists]. Then show that [List.In] can be formulated in terms
of [List.Exists].

Material: https://coq.inria.fr/library/Coq.Lists.List.html

 *)

Check Exists_cons.

Theorem ex2:
  forall (A:Type) (x:A) l, List.Exists (eq x) l <-> List.In x l.
Proof.
intros.
induction l.
- simpl. (* base case, empty list, Exists_nil applies *)
  apply Exists_nil.
- simpl. (* recursive case, rewriting Exists_cons *)
  rewrite -> Exists_cons.
  rewrite <- IHl. (* applying induction hypothesis *)
  split.
  intros [H | H].
  + simpl.
    inversion H.
    * simpl.
      subst.
      left.
      reflexivity.
  + right.
    exact H.

  + intros [H | H].
    * left. 
      symmetry.
      exact H.
    * right.
      exact H.
Qed.
(**

Create an inductive relation that holds if, and only if, element 'x'
appears before element 'y' in the given list.
We can define `succ` inductively as follows:

                                (x, y) succ l
-----------------------R1     ------------------R2
(x, y) succ x :: y :: l       (x, y) succ z :: l

Rule R1 says that x succeeds y in the list that starts with [x, y].

Rule R2 says that if x succeeds y in list l then x succeeds y in a list
the list that results from adding z to list l.


 *)
Inductive succ {X : Type} (x:X) (y:X): list X -> Prop :=
  | R1 : forall l, succ x y (x :: y :: l) (* base case, x is immediately before y *)
  | R2 : forall z l, succ x y l -> succ x y (z :: l). (* recursive case, x precedes y deeper in l *)



Theorem succ1:
    (* Only one of the following propositions is provable.
       Replace 'False' by the only provable proposition and then prove it:
     1) succ 2 3 [1;2;3;4]
     2) ~ succ 2 3 [1;2;3;4]
     *)
    succ 2 3 [1;2;3;4].
Proof.
apply R2. (* using rule R2 to progress in list *)
apply R1. (* using rule R1 since 2 is immediately before 3 *)
Qed.


Theorem succ2:
    (* Only one of the following propositions is provable.
       Replace 'False' by the only provable proposition and then prove it:
     1) succ 2 3 []
     2) ~ succ 2 3 []
     *)
    ~ succ 2 3 [].
Proof.
unfold not.
intros.
inversion H. (* empty list cannot contain succession *)
Qed.


Theorem succ3:
    (* Only one of the following propositions is provable.
       Replace 'False' by the only provable proposition and then prove it:
     1) succ 2 4 [1;2;3;4]
     2) ~ succ 2 4 [1;2;3;4]
     *)
    ~ succ 2 4 [1;2;3;4].
Proof.
unfold not.
intros.
inversion H. (* checking cases where 2 might precede 4 *)
inversion H1.
inversion H4.
inversion H7.
inversion H10.
Qed.


Theorem succ4:
  forall (X:Type) (x y : Type), succ x y [x;y].
Proof.
intros.
apply R1. (* directly follows from R1 as x precedes y in [x;y] *)
Qed.


Theorem ex3:
  forall (X:Type) (l1 l2:list X) (x y:X), succ x y (l1 ++ (x :: y :: l2)).
Proof.
intros.
induction l1.
  - simpl. (* base case, x and y are contiguous *)
  induction l2.
    + apply R1.
    + apply R1.
 - simpl. (* recursive case, keep propagating using R2 *)
  apply R2.
  apply IHl1.
Qed.


Theorem ex4:
  forall (X:Type) (x y:X) (l:list X), succ x y l -> exists l1 l2, l1 ++ (x :: y :: l2) = l.
Proof.
  intros X x y l H.
  induction H.
  - (* Case R1: l = x :: y :: l *)
    exists []. (* l1 is empty, x and y appear at the start *)
    exists l.
    reflexivity.
  - (* Case R2: succ x y l -> succ x y (z :: l) *)
    destruct IHsucc as [l1 [l2 IH]]. (* breaking down induction hypothesis *)
    exists (z :: l1), l2.
    simpl.
    rewrite IH.
    reflexivity.
Qed.