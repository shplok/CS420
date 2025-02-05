(* Defining a basic rgb type representing primary colors *)
Inductive rgb : Type := 
  (* `red`, `green`, and `blue` are the constructors for `rgb`, each representing a color. *)
  | red : rgb                
  | green : rgb              
  | blue : rgb.

(* Defining a color type with simple and compound constructors *)
Inductive color : Type :=
  (* `black` and `white` are simple constructors representing specific colors *)
  | black : color              
  | white : color              
  (* `primary` is a compound constructor that holds an `rgb` value, representing primary colors *)
  | primary : rgb -> color.

(* Flip an RGB color to the next value in the cycle (red → green → blue → red).
   This function uses pattern matching to safely and explicitly handle all possible cases of the `rgb` type. *)
Definition flip (r:rgb) : rgb :=
  (* Pattern matching works by comparing the structure of `r` against specified patterns.
     It ensures:
     - Exhaustiveness: All possible variants of `rgb` must be covered.
     - Type safety: Patterns are checked against the type definition at compile time. *)
  match r with
  | red => green    (* Transition: red → green (cycle to the next color) *)
  | green => blue   (* Transition: green → blue (cycle to the next color) *)
  | blue => red     (* Transition: blue → red (cycle back to the first color) *)
  end. 

   (* Example usage:
   - flip red   → green
   - flip green → blue
   - flip blue  → red *)

(* Testing the `primary` constructor and `flip` function with computations *)
Compute primary red.          (* Tags `red` as a primary color *)
Compute flip red.             (* Flips `red` to `green` *)
Compute primary (flip red).   (* Returns the primary color of flipped `red` (green) *)
Compute flip (flip red).      (* Flips `red` twice to get `blue` *)
Compute primary (flip (flip red)). (* Returns the primary color of flipped `red` twice (blue) *)

(**
  The `color_to_rgb` function extracts the `rgb` value from `color`:
  - For `black` and `white`, it returns `red`.
  - For `primary`, it extracts the contained `rgb` value.
*)
Definition color_to_rgb (c:color) : rgb :=
  (* Pattern match on the `color` type to extract an `rgb` value *)
  match c with
  | black => red        (* Return `red` for `black` *)
  | white => red        (* Return `red` for `white` *)
  | primary x => x      (* Extract and return the contained `rgb` value for `primary` *)
  end.

Definition f2 (c:color) : rgb := 
    match c with
    | black => red
    | white => red
    | primary red => green
    | primary green => blue
    | primary _ => red
    end.

Compute f2 (primary red).
Compute f2 (primary green).
Compute f2 (black).
Compute f2 (white).
Compute f2 (primary blue).

Inductive vec3 : Type :=
| vector : rgb -> rgb -> rgb -> vec3.

Compute vector red (flip (flip red)) (flip red).

Definition add (v1:vec3) (v2:vec3) : rgb :=

match v1 with 
| vector red _ _ => red
| vector _ red _ => red
| vector _ _ red => red
| vector green _ _ => green
| vector _ green _ => green
| vector _ _ green => green
| _ => blue
end.

