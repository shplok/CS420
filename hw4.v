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
(* we need to show that the string can be split into parts that match each piece of the regex *)
apply accept_app with (s1:= ["a";"b"]) (s2:= ["a"]).
  
(* first, prove that ["a","b"] is in (r_star "a" ;; ("b" || "c")) *)
(* split ["a","b"] into parts that match r_star "a" and ("b" || "c") *)
- apply accept_app with (s1:= ["a"]) (s2:= ["b"]).
    
(* prove that ["a"] is in r_star "a" *)
  + apply accept_star_eq. (* r_star accepts the string exactly matching one "a" *)
      apply accept_char.  (* match the character "a" *)
    
  (* prove that ["b"] is in ("b" || "c") *)
  + apply accept_union_l. (* use left option of the union *)
      apply accept_char. (* match the character "b" *)
    
  (* prove that concatenating ["a"] and ["b"] gives ["a","b"] *)
  + reflexivity.
  
  (* then, prove that ["a"] is in r_star "a" *)
  - apply accept_star_eq. (* r_star accepts the string exactly matching one "a" *)
      apply accept_char.  (* match the character "a" *)
  
  (* finally, prove that concatenating ["a","b"] and ["a"] gives ["a","b","a"] *)
- reflexivity.
Qed.

(**

Show that 'bb' is rejected by the following regular expression.

 *)

Ltac invc H := inversion H; subst; clear H.

Theorem ex2:
  ~ (["b"; "b"] \in (r_star "a" ;; ("b" || "c") ;; r_star "a")).
Proof.
intros H. (* assume by contradiction that ["b"; "b"] is in the language *)
invc H. (* break down the concatenation structure into parts s1, s2, s3 *)
invc H2. (* analyze the second concatenation structure *)
invc H1. (* analyze the r_star "a" structure *)
- (* Case where r_star "a" is empty string *)
  invc H4. (* analyze the union "b" || "c" *)
  + (* Case where union is "b" *)
    invc H2. (* analyze the second r_star "a" structure *)
    invc H3. (* further break down r_star "a" *)
    * discriminate. (* contradiction: empty string != ["b";"b"] *)
    * invc H0. discriminate. (* contradiction: "a" != "b" *)
  + invc H2. discriminate. (* contradiction with "c" in middle *)
- invc H0. (* case where r_star "a" has elements *)
discriminate. (* contradiction: "a" != "b" *)
Qed.

(**

Function size counts how many operators were used in a regular
expression. Show that (c ;; {})* can be written using a single
regular expression constructor.


 *)
Theorem ex3:
  exists r, size r = 1 /\ (r_star ( "c" ;; r_void ) <==> r).
Proof.
exists r_nil.
(* r_nil (the empty language) is the solution *)
split.
- reflexivity.
- rewrite r_app_r_void_rw.
  (* Apply the rule that concatenation with r_void yields r_void:
     "c" ;; r_void simplifies to r_void *)
  apply r_star_void_rw.
(* Apply the rule that r_star of r_void is equivalent to r_nil:
     r_star(r_void) <==> r_nil *)
Qed.

(**

Given that the following regular expression uses 530 constructors
(because size r_all = 514).
Show that you can find an equivalent regular expression that uses
at most 6 constructors.


 *)
Notation rapp := r_app_r_void_rw.

Theorem ex4:
  exists r, size r <= 6 /\  ((r_star ( (r_all || r_star "c" ) ;; r_void) ;; r_star ("a" || "b")) ;; r_star r_nil;; "c" <==> r).
Proof.
exists (r_star("a" || "b") ;; "c"). (* claim this regex is equivalent to the complex expression *)
split.
- reflexivity. (* size of r_star("a" || "b") ;; "c" is 6 so size r <= 6 is true *)
- rewrite rapp. (* apply rule that regex concatenated with r_void equals r_void *)
  rewrite r_star_void_rw. (* apply rule that r_star of r_void is equivalent to r_nil *)
  rewrite r_star_nil_rw. (* apply rule that r_star of r_nil is equivalent to r_nil *)
  rewrite r_app_r_nil_rw. (* apply rule that regex concatenated with r_nil on right equals the regex *)
  rewrite r_app_l_nil_rw. (* apply rule that regex concatenated with r_nil on left equals the regex *)
  reflexivity. (* resulting regex matches our claimed solution *)
Qed.

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



