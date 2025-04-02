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
From Turing Require Import Regex.

Import Lang.Examples.
Import LangNotations.
Import ListNotations.
Import RegexNotations.

Open Scope lang_scope.
Open Scope char_scope.

(* ---------------------------------------------------------------------------*)




(**

Show that 'aba' is accepted the the following regular expression.

 *)
Theorem ex1:
  ["a"; "b"; "a"] \in (r_star "a" ;; ("b" || "c") ;; r_star "a").
Proof.

Admitted.

(**

Show that 'bb' is rejected by the following regular expression.

 *)
Theorem ex2:
  ~ (["b"; "b"] \in (r_star "a" ;; ("b" || "c") ;; r_star "a")).
Proof.

Admitted.

(**

Function size counts how many operators were used in a regular
expression. Show that (c ;; {})* can be written using a single
regular expression constructor.


 *)
Theorem ex3:
  exists r, size r = 1 /\ (r_star ( "c" ;; r_void ) <==> r).
Proof.

Admitted.

(**

Given that the following regular expression uses 530 constructors
(because size r_all = 514).
Show that you can find an equivalent regular expression that uses
at most 6 constructors.


 *)
Theorem ex4:
  exists r, size r <= 6 /\  ((r_star ( (r_all || r_star "c" ) ;; r_void) ;; r_star ("a" || "b")) ;; r_star r_nil;; "c" <==> r).
Proof.

Admitted.

(**

The following code implements a function that given a string
it returns a regular expression that only accepts that string.

    Fixpoint r_word' l :=
    match l with
    | nil => r_nil
    | x :: l => (r_char x) ;; r_word' l
    end.

Prove that function `r_word'` is correct.
Note that you must copy/paste the function to outside of the comment
and in your proof state: exists r_word'.

The proof must proceed by induction.


 *)
Theorem ex5:
  forall l, exists (r_word:list ascii -> regex), Accept (r_word l) == fun w => w = l.
Proof.

Admitted.

(**

Show that there exists a regular expression with 5 constructs that
recognizes the following language. The idea is to find the smallest
regular expression that recognizes the language.


 *)
Theorem ex6:
  exists r, (Accept r == fun w => w = ["a"; "c"] \/ w = ["b"; "c"]) /\ size r = 5.
Proof.

Admitted.



