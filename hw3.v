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
intros.
unfold L4 in H.
destruct H as [x H].
destruct x.
- simpl in H. left.
Admitted.

(**

Show that the following word is accepted by the given language.

 *)
Theorem ex2:
  In ["a"; "b"; "b"; "a"] ("a" >> "b" * >> "a").
Proof.
  (* prepare language constructs *)
  unfold Star, In, App.
  
  (* decompose the word into parts *)
  exists ["a";"b";"b"], ["a"].
  
  (* handle first part *)
  split; [reflexivity |].
  
  (* break down the star application *)
  split.

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

Admitted.


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



