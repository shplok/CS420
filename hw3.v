(*
        #####################################################
        ###  PLEASE DO NOT DISTRIBUTE SOLUTIONS PUBLICLY  ###
        #####################################################
*)

Set Default Goal Selector "!".

Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
From Turing Require Import Lang.
From Turing Require Import Util.
Import LangNotations.
Import ListNotations.
Import Lang.Examples.
Open Scope lang_scope.
Open Scope char_scope.

(* ---------------------------------------------------------------------------*)





(**
Show that any word that is in L4 is either empty or starts with "a".
 *)
Theorem ex1:
  forall w, L4 w -> w = [] \/ exists w', w = "a" :: w'.
Proof.
  intros w H.
  apply l4_spec in H.
  destruct H as [n Hn].
  destruct n.
  - (* Case: n = 0 *)
    simpl in Hn.
    left.
    symmetry.
    exact Hn.
  - (* Case: n > 0 *)
    simpl in Hn.
    right.
    exists (pow1 "a" n ++ pow1 "b" n).
    rewrite <- Hn.

    reflexivity.
Admitted.

(**

Show that the following word is accepted by the given language.

 *)
Theorem ex2:
  In ["a"; "b"; "b"; "a"] ("a" >> "b" * >> "a").
Proof.
  (* Use app_in to decompose the main concatenation *)
  apply app_in with (w1:=["a";"b";"b"]) (w2:=["a"]).
  
  (* Show that ["a";"b";"b"] is in "a" >> "b"* *)
  - apply app_in with (w1:=["a"]) (w2:=["b";"b"]).
    + (* Show ["a"] is in "a" *)
      apply char_in.
    + (* Show ["b";"b"] is in "b"* *)
      exists 2. (* The exponent is 2 because "b" appears twice *)
      (* Show ["b";"b"] is in "b"^2 *)
      apply pow_cons with (w1:=["b"]) (w2:=["b"]).
      * (* Show ["b"] is in "b" *)
        apply char_in.
      * (* Show ["b"] is in "b"^1 *)
        apply pow_cons with (w1:=["b"]) (w2:=[]).
        -- (* Show ["b"] is in "b" *)
           apply char_in.
        -- (* Show [] is in "b"^0 *)
           apply pow_nil.
  
  (* Show that ["a"] is in "a" *)
  - apply char_in.
Admitted.


(**

Show that the following word is rejected by the given language.

 *)
Theorem ex3:
  ~ In ["b"; "b"] ("a" >> "b" * >> "a").
Proof.
unfold In, App, Star, not.
intros.
destruct H.
destruct H.
destruct H.
destruct H0.
destruct H0.
destruct H0.
destruct H0.
destruct H2.
destruct H3.
unfold Char in H1, H2.
subst.
inversion H.
Qed.

(**

Show that the following language is empty.

 *)
Theorem ex4:
  "0" * >> {} == {}.
Proof.
apply app_r_void_rw.
Qed.

(**

Rearrange the following terms. Hint use the distribution and absorption laws.

 *)
Theorem ex5:
  ("0" U Nil) >> ( "1" * ) == ( "0" >> "1" * ) U ( "1" * ).
Proof.
  (* establish language equivalence *)
  unfold Equiv.
  
  (* prove both directions *)
  split.
  - (* forward direction *)
    intros M.
    rewrite <- app_union_distr_l in M.
    rewrite app_l_nil_rw in M.
    apply M.
  
  (* reverse direction *)
  - intros N.
    rewrite <- app_union_distr_l.
    rewrite app_l_nil_rw.
    exact N.
Qed.

(**

Show that the following langue only accepts two words.

 *)
Theorem ex6:
  ("0" >> "1" U "1" >> "0") == fun w => (w = ["0"; "1"] \/ w = ["1"; "0"]).
Proof.
  unfold Equiv.
  split.
  - (* forward direction *)
    intros A.
    unfold In, App, Union in A.
    destruct A as [H | H].
    * (* "0" >> "1" case *)
      destruct H as [x [y [H1 H2]]].
      destruct H2 as [H2a H2b].
      unfold Char in H2a, H2b.
      left. 
      subst x. 
      subst y.
      simpl in H1.
      exact H1. 
    * (* "1" >> "0" case *)
      destruct H as [x [y [H1 H2]]].
      destruct H2 as [H2a H2b].
      unfold Char in H2a, H2b.
      right. 
      subst x. 
      subst y.
      simpl in H1.
      exact H1.
  - (* reverse direction *)
    intros A.
    destruct A as [H | H].
    * (* ["0"; "1"] case *)
      left.
      exists ["0"], ["1"].
      split.
      + simpl. exact H.
      + split.
        -- unfold Char. reflexivity.
        -- unfold Char. reflexivity.
    * (* ["1"; "0"] case *)
      right.
      exists ["1"], ["0"].
      split.
      + simpl. exact H.
      + split.
        -- unfold Char. reflexivity.
        -- unfold Char. reflexivity.
Qed.

Theorem ex7:
  "b" >> ("a" U "b" U Nil) * >> Nil == "b" >> ("b" U "a") *.
Proof.
split.
- (* forward dir*)
  intros.
  rewrite app_r_nil_rw in H.
  rewrite union_sym_rw in H.
  rewrite star_union_nil_rw in H.
  rewrite union_sym_rw in H.
  exact H.

- (* reverse direction *)
  intros.
  rewrite app_r_nil_rw.
  rewrite union_sym_rw.
  rewrite star_union_nil_rw.
  rewrite union_sym_rw.
  exact H.
Qed.


Theorem ex8:
  (("b" >> ("a" U {}) ) U (Nil >> {} >> "c")* ) * == ("b" >> "a") *.
Proof.
(* prove language equivalence *)
split.
- (* forward direction *)
  intros.
  rewrite union_r_void_rw in H.
  rewrite app_r_void_rw in H.
  rewrite app_l_void_rw in H.
  rewrite star_void_rw in H.
  rewrite union_sym_rw in H.
  rewrite star_union_nil_rw in H.
  exact H.
 
(* reverse direction *)
- intros H.
  rewrite union_r_void_rw.
  rewrite app_r_void_rw.
  rewrite app_l_void_rw.
  rewrite star_void_rw.
  rewrite union_sym_rw.
  rewrite star_union_nil_rw.
  exact H.
Qed.



