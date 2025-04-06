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
  (* Introduce the word w and its hypothesis that it is in L4 *)
  intros w H.
  (* Use the specification of L4 language to break down the hypothesis *)
  apply l4_spec in H.
  (* Destruct the number n used in the language specification *)
  destruct n.
  - (* Case: n = 0 
     When n is 0, the word must be empty *)
    simpl in Hn.
    left.
    symmetry.
    exact Hn.
  - (* Case: n > 0 
     When n is positive, the word must start with "a" *)
    simpl in Hn.
    right.

    (* Reconstruct the word using the power operator *)
    rewrite <- Hn.
    exists (pow1 "a" n ++ pow1 "b" (S n)).
    reflexivity.
Qed.



(**
Show that the following word is accepted by the given language.
 *)
Theorem ex2:
  In ["a"; "b"; "b"; "a"] ("a" >> "b" * >> "a").
Proof.
  (* Unfold the definitions of language operations *)
  unfold Star, In, App.
  
  (* Demonstrate that the word can be split into ["a";"b";"b"] and ["a"] *)
  exists ["a";"b";"b"], ["a"].
  split.
  - (* Verify that the concatenation equals the original word *)
    reflexivity.
  - split.
    * (* Prove that ["a";"b";"b"] is in "a" >> "b"* *)
      exists ["a"], ["b";"b"].
      split.
      + (* Verify the concatenation *)
        reflexivity.
      + split.
        -- (* Show ["a"] is in "a" *)
           reflexivity.
        -- (* Show ["b";"b"] is in "b"* by using the power operator with n=2 *)
           exists 2.
           apply pow_cons with (w1:= ["b"]) (w2:= ["b"]).
           ** (* Show ["b"] is in "b" *)
              apply pow_cons with (w1:= ["b"]) (w2:= []).
              ++ (* Show empty list is in "b"^0 *)
                 apply pow_nil.
              ++ (* Verify ["b"] is "b" *)
                 reflexivity.
              ++ (* Verify concatenation *)
                 reflexivity.
           ** (* Verify ["b"] is "b" *)
              reflexivity.
           ** (* Verify concatenation *)
              reflexivity.
    * (* Show ["a"] is in "a" *)
      reflexivity.
Qed.



(**
Show that the following word is rejected by the given language.
 *)
Theorem ex3:
  ~ In ["b"; "b"] ("a" >> "b" * >> "a").
Proof.
  (* Unfold the negation and language operations *)
  unfold In, App, Star, not.
  intros.
  (* Destructs all the hypotheses to reach a contradiction *)
  destruct H.
  destruct H.
  destruct H.
  destruct H0.
  destruct H0.
  destruct H0.
  destruct H0.
  destruct H2.
  destruct H3.
  (* Expose the contradiction by showing the character requirement is impossible *)
  unfold Char in H1, H2.
  subst.
  (* Inversion shows no valid decomposition exists *)
  inversion H.
Qed.



(**
Show that the following language is empty.
 *)
Theorem ex4:
  "0" * >> {} == {}.
Proof.
  (* Use the rewriting rule for void concatenation *)
  apply app_r_void_rw.
Qed.



(**
Rearrange the following terms. Hint: use the distribution and absorption laws.
 *)
Theorem ex5:
  ("0" U Nil) >> ( "1" * ) == ( "0" >> "1" * ) U ( "1" * ).
Proof.
  (* Establish language equivalence by proving both directions *)
  unfold Equiv.
  
  split.
  - (* Forward direction: use distribution and nil absorption laws *)
    intros M.
    rewrite <- app_union_distr_l in M.
    rewrite app_l_nil_rw in M.
    apply M.
  
  (* Reverse direction: reapply the distribution and nil absorption laws *)
  - intros N.
    rewrite <- app_union_distr_l.
    rewrite app_l_nil_rw.
    exact N.
Qed.



(**
Show that the following language only accepts two words.
 *)
Theorem ex6:
  ("0" >> "1" U "1" >> "0") == fun w => (w = ["0"; "1"] \/ w = ["1"; "0"]).
Proof.
  (* Establish language equivalence *)
  unfold Equiv.
  split.
  - (* Forward direction: break down the union and character requirements *)
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
  - (* Reverse direction: construct the language witnesses *)
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



(**
Show language equivalence by applying various language operation laws.
 *)
Theorem ex7:
  "b" >> ("a" U "b" U Nil) * >> Nil == "b" >> ("b" U "a") *.
Proof.
  (* Prove language equivalence by showing both directions *)
  split.
  - (* Forward direction: apply nil and union rewriting laws *)
    intros.
    rewrite app_r_nil_rw in H.
    rewrite union_sym_rw in H.
    rewrite star_union_nil_rw in H.
    rewrite union_sym_rw in H.
    exact H.

  (* Reverse direction: apply the same rewriting laws *)
  - intros.
    rewrite app_r_nil_rw.
    rewrite union_sym_rw.
    rewrite star_union_nil_rw.
    rewrite union_sym_rw.
    exact H.
Qed.



(**
Reduce a complex language expression to a simpler equivalent language.
 *)
Theorem ex8:
  (("b" >> ("a" U {}) ) U (Nil >> {} >> "c")* ) * == ("b" >> "a") *.
Proof.
  (* Prove language equivalence by reducing complex language terms *)
  split.
  - (* Forward direction: apply various void and union rewriting laws *)
    intros.
    rewrite union_r_void_rw in H.
    rewrite app_r_void_rw in H.
    rewrite app_l_void_rw in H.
    rewrite star_void_rw in H.
    rewrite union_sym_rw in H.
    rewrite star_union_nil_rw in H.
    exact H.
 
  (* Reverse direction: reapply the same language rewriting laws *)
  - intros H.
    rewrite union_r_void_rw.
    rewrite app_r_void_rw.
    rewrite app_l_void_rw.
    rewrite star_void_rw.
    rewrite union_sym_rw.
    rewrite star_union_nil_rw.
    exact H.
Qed.
=======
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
  (* Introduce the word w and its hypothesis that it is in L4 *)
  intros w H.
  (* Use the specification of L4 language to break down the hypothesis *)
  apply l4_spec in H.
  (* Destruct the number n used in the language specification *)
  destruct n.
  - (* Case: n = 0 
     When n is 0, the word must be empty *)
    simpl in Hn.
    left.
    symmetry.
    exact Hn.
  - (* Case: n > 0 
     When n is positive, the word must start with "a" *)
    simpl in Hn.
    right.

    (* Reconstruct the word using the power operator *)
    rewrite <- Hn.
    exists (pow1 "a" n ++ pow1 "b" (S n)).
    reflexivity.
Qed.

(**
Show that the following word is accepted by the given language.
 *)
Theorem ex2:
  In ["a"; "b"; "b"; "a"] ("a" >> "b" * >> "a").
Proof.
  (* Unfold the definitions of language operations *)
  unfold Star, In, App.
  
  (* Demonstrate that the word can be split into ["a";"b";"b"] and ["a"] *)
  exists ["a";"b";"b"], ["a"].
  split.
  - (* Verify that the concatenation equals the original word *)
    reflexivity.
  - split.
    * (* Prove that ["a";"b";"b"] is in "a" >> "b"* *)
      exists ["a"], ["b";"b"].
      split.
      + (* Verify the concatenation *)
        reflexivity.
      + split.
        -- (* Show ["a"] is in "a" *)
           reflexivity.
        -- (* Show ["b";"b"] is in "b"* by using the power operator with n=2 *)
           exists 2.
           apply pow_cons with (w1:= ["b"]) (w2:= ["b"]).
           ** (* Show ["b"] is in "b" *)
              apply pow_cons with (w1:= ["b"]) (w2:= []).
              ++ (* Show empty list is in "b"^0 *)
                 apply pow_nil.
              ++ (* Verify ["b"] is "b" *)
                 reflexivity.
              ++ (* Verify concatenation *)
                 reflexivity.
           ** (* Verify ["b"] is "b" *)
              reflexivity.
           ** (* Verify concatenation *)
              reflexivity.
    * (* Show ["a"] is in "a" *)
      reflexivity.
Qed.

(**
Show that the following word is rejected by the given language.
 *)
Theorem ex3:
  ~ In ["b"; "b"] ("a" >> "b" * >> "a").
Proof.
  (* Unfold the negation and language operations *)
  unfold In, App, Star, not.
  intros.
  (* Destructs all the hypotheses to reach a contradiction *)
  destruct H.
  destruct H.
  destruct H.
  destruct H0.
  destruct H0.
  destruct H0.
  destruct H0.
  destruct H2.
  destruct H3.
  (* Expose the contradiction by showing the character requirement is impossible *)
  unfold Char in H1, H2.
  subst.
  (* Inversion shows no valid decomposition exists *)
  inversion H.
Qed.

(**
Show that the following language is empty.
 *)
Theorem ex4:
  "0" * >> {} == {}.
Proof.
  (* Use the rewriting rule for void concatenation *)
  apply app_r_void_rw.
Qed.

(**
Rearrange the following terms. Hint: use the distribution and absorption laws.
 *)
Theorem ex5:
  ("0" U Nil) >> ( "1" * ) == ( "0" >> "1" * ) U ( "1" * ).
Proof.
  (* Establish language equivalence by proving both directions *)
  unfold Equiv.
  
  split.
  - (* Forward direction: use distribution and nil absorption laws *)
    intros M.
    rewrite <- app_union_distr_l in M.
    rewrite app_l_nil_rw in M.
    apply M.
  
  (* Reverse direction: reapply the distribution and nil absorption laws *)
  - intros N.
    rewrite <- app_union_distr_l.
    rewrite app_l_nil_rw.
    exact N.
Qed.

(**
Show that the following language only accepts two words.
 *)
Theorem ex6:
  ("0" >> "1" U "1" >> "0") == fun w => (w = ["0"; "1"] \/ w = ["1"; "0"]).
Proof.
  (* Establish language equivalence *)
  unfold Equiv.
  split.
  - (* Forward direction: break down the union and character requirements *)
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
  - (* Reverse direction: construct the language witnesses *)
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

(**
Show language equivalence by applying various language operation laws.
 *)
Theorem ex7:
  "b" >> ("a" U "b" U Nil) * >> Nil == "b" >> ("b" U "a") *.
Proof.
  (* Prove language equivalence by showing both directions *)
  split.
  - (* Forward direction: apply nil and union rewriting laws *)
    intros.
    rewrite app_r_nil_rw in H.
    rewrite union_sym_rw in H.
    rewrite star_union_nil_rw in H.
    rewrite union_sym_rw in H.
    exact H.

  (* Reverse direction: apply the same rewriting laws *)
  - intros.
    rewrite app_r_nil_rw.
    rewrite union_sym_rw.
    rewrite star_union_nil_rw.
    rewrite union_sym_rw.
    exact H.
Qed.

(**
Reduce a complex language expression to a simpler equivalent language.
 *)
Theorem ex8:
  (("b" >> ("a" U {}) ) U (Nil >> {} >> "c")* ) * == ("b" >> "a") *.
Proof.
  (* Prove language equivalence by reducing complex language terms *)
  split.
  - (* Forward direction: apply various void and union rewriting laws *)
    intros.
    rewrite union_r_void_rw in H.
    rewrite app_r_void_rw in H.
    rewrite app_l_void_rw in H.
    rewrite star_void_rw in H.
    rewrite union_sym_rw in H.
    rewrite star_union_nil_rw in H.
    exact H.
 
  (* Reverse direction: reapply the same language rewriting laws *)
  - intros H.
    rewrite union_r_void_rw.
    rewrite app_r_void_rw.
    rewrite app_l_void_rw.
    rewrite star_void_rw.
    rewrite union_sym_rw.
    rewrite star_union_nil_rw.
    exact H.
Qed.
