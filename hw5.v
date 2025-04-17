(*
        #####################################################
        ###  PLEASE DO NOT DISTRIBUTE SOLUTIONS PUBLICLY  ###
        #####################################################
*)

Set Default Goal Selector "!".

Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope char_scope.
Require Import Hw5Util.

(* ---------------------------------------------------------------------------*)




(**

Use `yield_def`.

 *)
Theorem yield_eq:
  forall G A w, List.In (A, w) (Hw5Util.grammar_rules G) -> Hw5Util.Yield G [A] w.
Proof.
intros L M E O. (* Intro Vars *)
apply yield_def with (u := []) (v := []) (w := E) (A := M). (* Apply yield def tactic from Hw5Util.v *)
- apply O. (* Apply grammaer rules to proposed hypothesis *)
- reflexivity.
- rewrite -> app_nil_r. (* [E ++ [] == E *)
simpl. (* [] ++ E == E *)
reflexivity.
Qed.

(**

Use `yield_def` and `app_assoc` to correct the parenthesis.

 *)
Theorem yield_right:
  forall G w1 w2 r w3 w4, Hw5Util.Yield G w1 w2 -> w3 = w1 ++ r -> w4 = w2 ++ r -> Hw5Util.Yield G w3 w4.
Proof.
intros A B C D E F G H I. (* Introduce our vars *)
rewrite -> H. (* Replace E (w3) with B ++ D (w1 ++ r) *)
rewrite -> I. (* Replace F (w4) with C ++ D (w2 ++ r) *)
inversion G. (* Break down the Yield hypothesis to extract its components *)
rewrite -> H1. rewrite -> H2. (* Replace B and C with u ++ v ++ w and u ++ A0 ++ w*)
rewrite <- app_assoc. rewrite <- app_assoc. rewrite <- app_assoc. rewrite <- app_assoc. (* reorganize string concatenations *)
apply yield_def with (u := u) (v:= v ++ D) (w:= w) (A := A0).
-apply H0. (* Prove the first premise: Hw5Util.Rule A0 u v w *)
- reflexivity.
- reflexivity.
Qed.

(**

Similar proof than `yield_right`, but you should rewrite with
`app_assoc` after using `yield_def`, not before.


 *)
Theorem yield_left:
  forall G w1 w2 l w3 w4, Hw5Util.Yield G w1 w2 -> w3 = l ++ w1 -> w4 = l ++ w2 -> Hw5Util.Yield G w3 w4.
Proof.
intros A B C D E F G H I. (* Introduce our vars *)
rewrite -> H. (* Replace E (w3) with B ++ D (w1 ++ r) *)
rewrite -> I. (* Replace F (w4) with C ++ D (w2 ++ r) *)
inversion G. (* Break down the Yield hypothesis to extract its components *)
rewrite -> H1. rewrite -> H2. (* Replace B and C with u ++ v ++ w and u ++ A0 ++ w*)
apply yield_def with (u := D ++ u) (v:= v) (w:= w) (A := A0).
- apply H0. (* Prove the first premise about the Rule A0 u v w *)
- rewrite -> app_assoc. reflexivity. (* Prove D ++ (u ++ v ++ w) = (D ++ u) ++ v ++ w *)
- rewrite -> app_assoc. reflexivity. (* Prove (D ++ u) ++ w ++ v = (D ++ u) ++ w ++ v *)
Qed.

(**

Consider using one of the lemmas you have just proved.
When your goal is `In ("C", ...) (grammar_rules g1)`, `simpl; auto`
should solve it.


 *)
Theorem g1_rule_1:
  Hw5Util.Yield g1 ["C"] ["{"; "C"; "}"].
Proof.
apply yield_eq. (* Proves that the grammar rule C produces {C} exists in grammar g1 *)
simpl; auto. (* Simplify derivation *)
Qed.

(**

Consider using one of the lemmas you have just proved.
When your goal is `In ("C", ...) (grammar_rules g1)`, `simpl; auto`
should solve it.


 *)
Theorem g1_rule_2:
  Hw5Util.Yield g1 ["C"] ["C"; "C"].
Proof.
apply yield_eq. (* Proves that the grammar rule C produces C C exists in grammar g1 *)
simpl; auto. (* Simplify derivation *)
Qed.

(**

Consider using one of the lemmas you have just proved.
When your goal is `In ("C", ...) (grammar_rules g1)`, `simpl; auto`
should solve it.


 *)
Theorem g1_rule_3:
  Hw5Util.Yield g1 ["C"] [].
Proof.
apply yield_eq. (* Proves that the grammar rule C produces "" exists in grammar g1 *)
simpl; auto. (* Simplify derivation *)
Qed.

(**

The proof should proceed by inversion and then case analysis on
string `u`.


 *)
Ltac invc := inversion H; subst; clear.

Theorem yield_inv_start:
  forall G w, Hw5Util.Yield G [Hw5Util.grammar_start G] w -> In (Hw5Util.grammar_start G, w) (Hw5Util.grammar_rules G).
Proof.
intros A B H. (* Introduce defined Vars and Hypothesis *)
invc. (* perform inversion *)
destruct u.
- 
Qed.

(**

You will want to use `yield_inv_start`. Recall that that `List.In`
simplifies to a series of disjunctions.


 *)
Theorem g1_ex1:
  ~ Hw5Util.Yield g1 ["C"] ["{"].
Proof.

Admitted.

(**

The idea is to use either: `yield_left`, `yield_right`, or `yield_def`.


 *)
Theorem g1_step_1:
  Hw5Util.Yield g1 ["C"; "C"] ["{"; "C"; "}"; "C"].
Proof.

Admitted.

(**

The idea is to use either: `yield_left`, `yield_right`, or `yield_def`.


 *)
Theorem g1_step_2:
  Hw5Util.Yield g1 ["{"; "C"; "}"; "C"] ["{"; "}"; "C"].
Proof.

Admitted.

(**

The idea is to use either: `yield_left`, `yield_right`, or `yield_def`.


 *)
Theorem g1_step_3:
  Hw5Util.Yield g1 ["{"; "}"; "C"] ["{"; "}"; "{"; "C"; "}"].
Proof.

Admitted.

(**

The idea is to use either: `yield_left`, `yield_right`, or `yield_def`.


 *)
Theorem g1_step_4:
  Hw5Util.Yield g1 ["{"; "}"; "{"; "C"; "}"] ["{"; "}"; "{"; "}"].
Proof.

Admitted.

(**

Use either `derivation_nil` or `derivation_cons`.

 *)
Theorem g1_der_1:
  Hw5Util.Derivation g1 [["C"]].
Proof.

Admitted.

(**

Use either `derivation_nil` or `derivation_cons`.

 *)
Theorem g1_der_2:
  Hw5Util.Derivation g1 [["C"; "C"]; ["C"]].
Proof.

Admitted.

(**

Use either `derivation_nil` or `derivation_cons`.

 *)
Theorem g1_der_3:
  Hw5Util.Derivation g1 [["{"; "C"; "}"; "C"]; ["C"; "C"]; ["C"]].
Proof.

Admitted.


Theorem g1_der_4:
  Hw5Util.Derivation g1 [
    ["{"; "}"; "C"];
    ["{"; "C"; "}"; "C"];
    ["C"; "C"];
    ["C"]
].
Proof.

Admitted.


Theorem g1_der_5:
  Hw5Util.Derivation g1 [
    ["{"; "}"; "{"; "C"; "}"];
    ["{"; "}"; "C"];
    ["{"; "C"; "}"; "C"];
    ["C"; "C"];
    ["C"]
].
Proof.

Admitted.


Theorem g1_der_6:
  Hw5Util.Derivation g1 [
    ["{"; "}"; "{"; "}"];
    ["{"; "}"; "{"; "C"; "}"];
    ["{"; "}"; "C"];
    ["{"; "C"; "}"; "C"];
    ["C"; "C"];
    ["C"]
].
Proof.

Admitted.

(**

Use `g1_der_6`.

 *)
Theorem ex1:
  Accept g1 ["{"; "}"; "{"; "}"].
Proof.

Admitted.



