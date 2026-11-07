(** * The examples of Hirrolot's CoC gist on the table λC

    "How to implement dependent types in 80 lines of code"
    (https://gist.github.com/Hirrolot/27e6b02a051df333811a23b97c375196):
    the usage examples of its usage.ml, checked by the kernel of lecture 6
    under the table [coc].  No code of the gist is ported; only its CoC,
    two sorts with [∗ : □] and the product in the sort of its codomain, is
    compared with the table, and its examples are rewritten with the
    builder:
    - Church numerals [zero], [succ], [one] … [four] and [add], typed, and
      the equations of [add] the gist asserts, by conversion;
    - Church pairs;
    - a vector module given by assumptions of the context: the family
      [Vect : Nat → ∗ → ∗], an item type and an item, and [replicate],
      [concat], [zip].  [concat] returns a vector of length [add n m], so
      [concat one three] checks against [Vect four] by computing the
      length; [zip] of vectors of lengths four and one is rejected with the
      gist's error: expected [Vect four], got [Vect one], at [vect_one].

    The vectors are assumed, not defined: this demonstrates dependent
    typing on their uses, not an inductive family; there is no data and
    no large elimination in pure CoC.  The family [Vect] needs the rule
    (∗,□), and U⁻ rejects the context at its type. *)

From Stdlib Require Import String List.
Import ListNotations.
From DepTypes.Common Require Import Result.
From DepTypes.PTS Require Import Syntax Named Spec Signature Eval Check EmptySig.
From DepTypes.Configs Require Import Finite.
From DepTypes.SystemU Require Import Looping.
From DepTypes.MLTT Require Import Choose.

Open Scope string_scope.
Open Scope nterm_scope.

Definition gist_fuel : nat := 1000.

(** ** Church numerals *)

Definition n_ty : nterm := Π "a" : ⋆, ("a" ~> "a") ~> "a" ~> "a".
Definition zero : nterm := (λ "a", λ "f", λ "x", "x") ∷ n_ty.
Definition succ : nterm := (λ "n", λ "a", λ "f", λ "x", "f" ("n" "a" "f" "x")) ∷ (n_ty ~> n_ty).
Definition one : nterm := succ zero.
Definition two : nterm := succ one.
Definition three : nterm := succ two.
Definition four : nterm := succ three.

Definition add_ty : nterm := n_ty ~> n_ty ~> n_ty.
Definition add : nterm :=
  (λ "n", λ "m", λ "a", λ "f", λ "x", "n" "a" "f" ("m" "a" "f" "x")) ∷ add_ty.

Example numerals_typed :
  map (fun t => snd (run_infer coc ∅ gist_fuel [] (build [] t))) [zero; one; two; three; four]
  = map (fun _ => Accepted (build [] n_ty)) [zero; one; two; three; four].
Proof. vm_compute. reflexivity. Qed.

Example add_typed :
  snd (run_infer coc ∅ gist_fuel [] (build [] add)) = Accepted (build [] add_ty).
Proof. vm_compute. reflexivity. Qed.

Definition convertible (t u : nterm) : bool :=
  match convert ∅ gist_fuel (build [] t) (build [] u) with
  | ConvEqual _ => true
  | _ => false
  end.

(** The equations of the gist, and one that does not hold. *)
Example add_equations :
  map (fun '(t, u) => convertible t u)
    [ (add zero zero, zero); (add zero one, one); (add one zero, one); (add three one, four);
      (add three one, three) ]
  = [true; true; true; true; false].
Proof. vm_compute. reflexivity. Qed.

(** ** Church pairs *)

Definition pair_ty : nterm := ⋆ ~> ⋆ ~> ⋆.
Definition pair : nterm := (λ "a", λ "b", Π "c" : ⋆, ("a" ~> "b" ~> "c") ~> "c") ∷ pair_ty.

Example pair_typed :
  snd (run_infer coc ∅ gist_fuel [] (build [] pair)) = Accepted (build [] pair_ty).
Proof. vm_compute. reflexivity. Qed.

(** ** Vectors by assumption *)

(** The context of the gist, the innermost entry first. *)
Definition vect_ctx : list (string * nterm) :=
  [ ("zip", Π "n" : n_ty, Π "a" : ⋆, Π "b" : ⋆,
              "Vect" "n" "a" ~> "Vect" "n" "b" ~> "Vect" "n" (pair "a" "b"));
    ("concat", Π "n" : n_ty, Π "m" : n_ty, Π "a" : ⋆,
              "Vect" "n" "a" ~> "Vect" "m" "a" ~> "Vect" (add "n" "m") "a");
    ("replicate", Π "n" : n_ty, Π "a" : ⋆, "a" ~> "Vect" "n" "a");
    ("item", NVar "item_ty");
    ("item_ty", ⋆);
    ("Vect", n_ty ~> ⋆ ~> ⋆) ].

Definition vect_one : nterm := "replicate" one "item_ty" "item".
Definition vect_three : nterm := "replicate" three "item_ty" "item".
Definition vect_four : nterm := "concat" one three "item_ty" vect_one vect_three.

Definition in_vect (t : nterm) : term := term_in vect_ctx t.

Example vectors_typed :
  map (fun '(t, n) => snd (run_check coc ∅ gist_fuel (in_ctx vect_ctx) (in_vect t)
                             (in_vect ("Vect" n "item_ty"))))
    [(vect_one, one); (vect_three, three); (vect_four, four)]
  = [Accepted tt; Accepted tt; Accepted tt].
Proof. vm_compute. reflexivity. Qed.

(** The kernel does not normalize the synthesized type: [concat] gives
    [Vect (add one three)], which converts to [Vect four]. *)
Example concat_type :
  snd (run_infer coc ∅ gist_fuel (in_ctx vect_ctx) (in_vect vect_four))
  = Accepted (in_vect ("Vect" (add one three) "item_ty")).
Proof. vm_compute. reflexivity. Qed.

Example zip_different_lengths_rejected :
  snd (run_infer coc ∅ gist_fuel (in_ctx vect_ctx) (in_vect ("zip" four "item_ty" "item_ty" vect_one vect_four)))
  = Rejected (EMismatch (in_vect vect_one) (in_vect ("Vect" four "item_ty")) (in_vect ("Vect" one "item_ty"))).
Proof. vm_compute. reflexivity. Qed.

(** U⁻ has no rule (∗,□): the type of [Vect] is rejected. *)
Example vect_context_u_minus :
  snd (run_infer system_u_minus ∅ gist_fuel (in_ctx vect_ctx) (in_vect vect_one))
  = Rejected (ENoRule (build [] (n_ty ~> ⋆ ~> ⋆)) Star Box).
Proof. vm_compute. reflexivity. Qed.
