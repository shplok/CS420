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

Admitted.

(**

Show that the following word is accepted by the given language.

 *)
Theorem ex2:
  In ["a"; "b"; "b"; "a"] ("a" >> "b" * >> "a").
Proof.

Admitted.

(**

Show that the following word is rejected by the given language.

 *)
Theorem ex3:
  ~ In ["b"; "b"] ("a" >> "b" * >> "a").
Proof.

Admitted.

(**

Show that the following language is empty.

 *)
Theorem ex4:
  "0" * >> {} == {}.
Proof.

Admitted.

(**

Rearrange the following terms. Hint use the distribution and absorption laws.

 *)
Theorem ex5:
  ("0" U Nil) >> ( "1" * ) == ( "0" >> "1" * ) U ( "1" * ).
Proof.

Admitted.

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

Admitted.


Theorem ex8:
  (("b" >> ("a" U {}) ) U (Nil >> {} >> "c")* ) * == ("b" >> "a") *.
Proof.

Admitted.



