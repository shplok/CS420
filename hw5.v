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


Theorem yield_inv_start:
  forall G w, Hw5Util.Yield G [Hw5Util.grammar_start G] w -> In (Hw5Util.grammar_start G, w) (Hw5Util.grammar_rules G).
Proof.
intros. (* Introduce defined Vars and Hypothesis *)
inversion H; subst; clear H. (* perform inversion *)

destruct u. (* Case analysis on whether u is empty or not *)
- inversion H1; subst; clear H1. (* If u is empty, simplify [grammar_start G] = [] ++ v ++ w0 *)
rewrite app_nil_r. (* Simplify by removing empty list at the end *)
apply H0. (* The rule directly gives us what we need to prove *)
- induction u. (* If u is non-empty, we do induction on its structure *)
  + inversion H1. (* Case where u starts as [], but this contradicts our assumption *)
  + inversion H1. (* Case where u starts with a cons, also leads to contradiction *)
Qed.
(**

You will want to use `yield_inv_start`. Recall that that `List.In`
simplifies to a series of disjunctions.


 *)
Theorem g1_ex1:
  ~ Hw5Util.Yield g1 ["C"] ["{"].
Proof.
unfold not. (* unfold the inverse of theorem *)
intros. (* introduce hypothesis *)
apply yield_inv_start in H. (* apply developed inversive theorem *)
destruct H. (* Case analysis on how this element could be in the list *)
- inversion H. (* First case leads to contradiction *)
- unfold In in H. (* Examine what it means for this to be in the list *)
inversion H. (* Break down the disjunction *)
  + inversion H0. (* leads to contradiction *)
  + inversion H0. (* leads to contradiction *)
    * inversion H1. (* leads to contradiction *)
    * inversion H1. (* leads to contradiction *)
Qed.

(**

The idea is to use either: `yield_left`, `yield_right`, or `yield_def`.


 *)
Theorem g1_step_1:
  Hw5Util.Yield g1 ["C"; "C"] ["{"; "C"; "}"; "C"].
Proof.
apply yield_right with (r := ["C"]) (w1 := ["C"]) (w2 := ["{"; "C"; "}"]). (* yield_right with the accurate values*)
- apply yield_eq. simpl; auto. (* apply simpl, auto like before *)
- reflexivity. (* recognize reflexivity and simplify *)
- reflexivity. (* recognize reflexivity and simplify *)
Qed.

(**

The idea is to use either: `yield_left`, `yield_right`, or `yield_def`.


 *)
Theorem g1_step_2:
  Hw5Util.Yield g1 ["{"; "C"; "}"; "C"] ["{"; "}"; "C"].
Proof.
apply yield_def with (u:= ["{"]) (v:= ["}"; "C"]) (w:= []) (A:= "C").
(* Apply yield_def by decomposing the strings appropriately to match the C → ε rule in g1 *)
- simpl; auto. (* Apply the grammar rule that C can produce the empty string *)
- reflexivity. (* Verify first string equals u ++ v ++ w *)
- reflexivity. (* Verify second string equals u ++ A ++ w *)
Qed.

(**

The idea is to use either: `yield_left`, `yield_right`, or `yield_def`.


 *)
Theorem g1_step_3:
  Hw5Util.Yield g1 ["{"; "}"; "C"] ["{"; "}"; "{"; "C"; "}"].
Proof.
simpl.
apply yield_def with (u:= ["{"; "}"]) (v:= []) (w:= ["{"; "C"; "}"]) (A:= "C").
(* show C can produce {C} at the appropriate position *)
- simpl; auto. (* Apply the grammar rule that C can produce {C} *)
- reflexivity. (* sides equal *)
- reflexivity. (* sides equal *)
Qed.

(**

The idea is to use either: `yield_left`, `yield_right`, or `yield_def`.


 *)
Theorem g1_step_4:
  Hw5Util.Yield g1 ["{"; "}"; "{"; "C"; "}"] ["{"; "}"; "{"; "}"].
Proof.
apply yield_def with (u:= ["{"; "}"; "{"]) (v:= ["}"]) (w:= []) (A:= "C"). (* use yield_def with accurate values*)
- simpl; auto. (* apply formatting *)
- reflexivity. (*sides equal *)
- reflexivity. (*sides equal *)
Qed.

(**

Use either `derivation_nil` or `derivation_cons`.

 *)
Theorem g1_der_1:
  Hw5Util.Derivation g1 [["C"]].
Proof.
apply derivation_nil. (* apply base case *)
Qed.

(**

Use either `derivation_nil` or `derivation_cons`.

 *)
Theorem g1_der_2:
  Hw5Util.Derivation g1 [["C"; "C"]; ["C"]].
Proof.
apply derivation_cons. (* apply cons *)
- apply derivation_nil. (* base case *)
- apply yield_eq. (* apply the yield_eq lemma *)
simpl; auto. (* simplify in format *)
Qed.

(**

Use either `derivation_nil` or `derivation_cons`.

 *)
Theorem g1_der_3:
  Hw5Util.Derivation g1 [["{"; "C"; "}"; "C"]; ["C"; "C"]; ["C"]].
Proof.
apply derivation_cons. (* apply cons *)
- apply derivation_cons. (* apply cons *)
  + apply derivation_nil. (* apply nil base case *)
  + apply yield_eq. (* apply yield_eq developed lemma *)
  simpl; auto. (* simplify in format *)
- apply g1_step_1. (* apply previously derived theorem *)
Qed.


Theorem g1_der_4:
  Hw5Util.Derivation g1 [
    ["{"; "}"; "C"];
    ["{"; "C"; "}"; "C"];
    ["C"; "C"];
    ["C"]
].
Proof.
apply derivation_cons. (* Add ["{"; "}"; "C"] to the beginning of the derivation *)
- apply derivation_cons. (* Add ["{"; "C"; "}"; "C"] to the beginning of the derivation *)
  + apply derivation_cons.
    * apply derivation_nil. (* base case *)
    * apply yield_eq. (* Prove that C can yield CC in one step *)
      simpl; auto. (* simplify in format *)
  + apply g1_step_1. (* apply previously derived theorem *)
- apply g1_step_2. (* apply previously derived theorem *)
Qed.


Theorem g1_der_5:
  Hw5Util.Derivation g1 [
    ["{"; "}"; "{"; "C"; "}"];
    ["{"; "}"; "C"];
    ["{"; "C"; "}"; "C"];
    ["C"; "C"];
    ["C"]
].
Proof.
apply derivation_cons. (* Add ["{"; "}"; "{"; "C"; "}"] to the beginning of the derivation *)
- apply derivation_cons. (* Add ["{"; "}"; "C"] to the beginning of the derivation *)
  + apply derivation_cons. (* Add ["{"; "C"; "}"; "C"] to the beginning of the derivation *)
    * apply derivation_cons. (* Add ["C"; "C"] to the beginning of the derivation *)
      -- apply derivation_nil. (* Base Case *)
      -- apply yield_eq. (* Prove that C can yield CC in one step *)
         simpl; auto.
    * apply g1_step_1. (* Apply previously proven step that CC yields {C}C *)
  + apply g1_step_2. (* Apply previously proven step that {C}C yields {}C *)
- apply g1_step_3. (* Apply previously proven step that {}C yields {}{C} *)
Qed.


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
apply derivation_cons. (* apply cons derivation *)
- apply derivation_cons. (* apply cons derivation *)
  + apply derivation_cons. (* apply cons derivation *)
    * apply derivation_cons. (* apply cons derivation *)
      -- apply derivation_cons. (* apply cons derivation *)
          ++ apply derivation_nil. (* apply nil derivation *)
          ++ apply yield_eq. (* Prove that C can yield CC in one step *)
             simpl; auto.
      -- apply g1_step_1. (* apply logic similar to g1_der_5 *)
    * apply g1_step_2. (* apply logic similar to g1_der_5 *)
  + apply g1_step_3. (* apply logic similar to g1_der_5 *)
- apply g1_step_4. (* apply logic similar to g1_der_5 *)
Qed.

(**

Use `g1_der_6`.

 *)
Theorem ex1:
  Accept g1 ["{"; "}"; "{"; "}"].
Proof.
(* Show a derivation exists that accepts the string ["{"; "}"; "{"; "}"] *)
exists [["{"; "}"; "{"; "C"; "}"]; ["{"; "}"; "C"]; ["{"; "C"; "}"; "C"]; ["C"; "C"]; ["C"]].
- apply g1_der_6. (* Use previously proven derivation theorem g1_der_6 *)
- apply Forall_cons. (* Show that final string matches terminals by checking each element *)
  + left. reflexivity.  (* Prove "{" is a terminal *)
  + apply Forall_cons.
    * right.
      left. reflexivity.  (* Prove "}" is a terminal *)
    * apply Forall_cons.
      -- left. reflexivity. (* Prove "{" is a terminal *)
      -- apply Forall_cons.
        ++ right. left. reflexivity.   (* Prove "}" is a terminal *)
        ++ apply Forall_nil. (* base case *)
Qed.



