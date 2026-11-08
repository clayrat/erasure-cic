(** * Recursion two ways: fix and match against case trees

    The programs of lecture 7 written again with the [fix] and [match] of
    the kernel, in the signatures where lecture 7 compiled their case
    trees ([compile_checked] through [compile_all], elim-inductive-types):

    - [half], with its call two fields down: the guard accepts it
      directly, where the compiler refuses the direct strategy and goes
      through the history (Programs/Half.v);
    - [plus] on its first argument;
    - [append] on vectors, its index computed by the compiled [plus];
    - [copy] on W, its call under a λ.

    For each, the guard and the checker accept the [fix]; the defining
    equations hold by conversion for each implementation separately; and
    closed runs give the same normal forms, or for [copy] the same
    observation, since the two copies differ under the λ of the children.
    The two implementations are not compared on free arguments: only
    their equations are definitional.

    [g (succ k) = g (pred k)] is refused both ways: by the compiler, which
    finds no path to [pred k], and by the guard, which does not recognize
    [pred k] as a subterm.  The guard checks the recursion of a program;
    the strict positivity of a declaration is the separate check of its
    registration (Data/Positivity.v). *)

From Stdlib Require Import String List Bool.
Import ListNotations.
From DepTypes.Common Require Import Result.
From DepTypes.PTS Require Import Syntax Named Signature Eval EvalSrc Guard Check.
From DepTypes.Configs Require Import Predicative.
From DepTypes.SystemU Require Import Looping.
From DepTypes.MLTT Require Import Constants Families.
From IndTypes.Elim Require Import Declare.
From IndTypes.Data Require Import Nat Lists W.
From IndTypes.Recursion Require Import CaseTree Compile.
From IndTypes.Programs Require Import Direct Half Append Copy Rejected.

Open Scope string_scope.
Open Scope nterm_scope.

Definition nat_case (x z s : nterm) : nterm := NCase "Nat" (Univ 0) (λ "_", Nat) x [z; s].

Definition accepted (sg : signature) (t A : nterm) : bool :=
  match snd (run_check predicative sg prog_fuel [] (build [] t) (build [] A)) with
  | Accepted _ => true
  | _ => false
  end.

(** Two closed programs reach the same normal form. *)
Definition same_result (sg : signature) (t u : nterm) : bool :=
  match normalize sg prog_fuel (build [] t), normalize sg prog_fuel (build [] u) with
  | NormalForm a, NormalForm b => term_eqb a b
  | _, _ => false
  end.

(** ** half *)

Definition half_fix : nterm :=
  NFix "half" (Nat ~> Nat) 0
    (λ "n", nat_case "n" zero (λ "m", nat_case "m" zero (λ "k", succ ("half" "k")))).

Example half_paired :
  accepted sg_half half_fix (Nat ~> Nat) &&
  converts sg_half [] (half_fix zero) zero &&
  converts sg_half [] (half_fix (succ zero)) zero &&
  converts sg_half ["k"] (half_fix (succ (succ "k"))) (succ (half_fix "k")) &&
  converts sg_half [] (half zero) zero &&
  converts sg_half [] (half (succ zero)) zero &&
  converts sg_half ["k"] (half (succ (succ "k"))) (succ (half "k")) &&
  forallb (fun n => same_result sg_half (half_fix (num n)) (half (num n))) [0; 1; 2; 3; 4; 5; 6; 7] = true.
Proof. vm_compute. reflexivity. Qed.

(** The direct strategy of the compiler refuses [half]; the guard does
    not need the history. *)
Example half_direct :
  match refusal (compile_all predicative prog_fuel sg_nat0 [half_fn Direct]) with
  | Some (RCase (CNotImmediate _)) => true
  | _ => false
  end && accepted sg_nat0 half_fix (Nat ~> Nat) = true.
Proof. vm_compute. reflexivity. Qed.

(** ** plus *)

Definition plus_fix : nterm :=
  NFix "plus" (Nat ~> Nat ~> Nat) 0 (λ "n", λ "m", nat_case "n" "m" (λ "k", succ ("plus" "k" "m"))).

Example plus_paired :
  accepted sg_direct plus_fix (Nat ~> Nat ~> Nat) &&
  converts sg_direct ["m"] (plus_fix zero "m") "m" &&
  converts sg_direct ["k"; "m"] (plus_fix (succ "k") "m") (succ (plus_fix "k" "m")) &&
  converts sg_direct ["m"] (plus zero "m") "m" &&
  converts sg_direct ["k"; "m"] (plus (succ "k") "m") (succ (plus "k" "m")) &&
  forallb (fun '(n, m) => same_result sg_direct (plus_fix (num n) (num m)) (plus (num n) (num m)))
    [(0, 0); (2, 3); (4, 1)] = true /\
  eval_src sg_direct prog_fuel (build [] (plus_fix (num 2) (num 3))) = CbvValue (build [] (num 5)) /\
  eval_src sg_direct prog_fuel (build [] (plus (num 2) (num 3))) = CbvValue (build [] (num 5)).
Proof. vm_compute. repeat split. Qed.

(** ** append *)

Definition append_ty : nterm :=
  Π "A" : Type@ 0, Π "n" : Nat, Π "m" : Nat, Vec "A" "n" ~> Vec "A" "m" ~> Vec "A" (plus "n" "m").

Definition append_fix : nterm :=
  NFix "app" append_ty 3
    (λ "A", λ "n", λ "m", λ "xs", λ "ys",
       NCase "Vec" (Univ 0) (λ "k", λ "_", Vec "A" (plus "k" "m")) "xs"
         [NVar "ys"; λ "k", λ "x", λ "xs'", vcons "A" (plus "k" "m") "x" ("app" "A" "k" "m" "xs'" "ys")]).

Example append_paired :
  accepted sg_append append_fix append_ty &&
  converts sg_append ["A"; "m"; "ys"] (append_fix "A" zero "m" (vnil "A") "ys") "ys" &&
  converts sg_append ["A"; "n"; "m"; "x"; "xs"; "ys"]
    (append_fix "A" (succ "n") "m" (vcons "A" "n" "x" "xs") "ys")
    (vcons "A" (plus "n" "m") "x" (append_fix "A" "n" "m" "xs" "ys")) &&
  converts sg_append ["A"; "m"; "ys"] (append "A" zero "m" (vnil "A") "ys") "ys" &&
  converts sg_append ["A"; "n"; "m"; "x"; "xs"; "ys"]
    (append "A" (succ "n") "m" (vcons "A" "n" "x" "xs") "ys")
    (vcons "A" (plus "n" "m") "x" (append "A" "n" "m" "xs" "ys")) &&
  same_result sg_append (append_fix Nat (num 1) (num 2) (vec [7]) (vec [8; 9]))
    (append Nat (num 1) (num 2) (vec [7]) (vec [8; 9])) &&
  same_result sg_append (append_fix Nat (num 0) (num 1) (vec []) (vec [5]))
    (append Nat (num 0) (num 1) (vec []) (vec [5])) = true.
Proof. vm_compute. reflexivity. Qed.

(** ** copy *)

Definition copy_ty : nterm := Π "A" : Type@ 0, Π "B" : ("A" ~> Type@ 0), W "A" "B" ~> W "A" "B".

Definition copy_fix : nterm :=
  NFix "copy" copy_ty 2
    (λ "A", λ "B", λ "w",
       NCase "W" (Univ 0) (λ "_", W "A" "B") "w"
         [λ "a", λ "f", sup "A" "B" "a" (λ "b", "copy" "A" "B" ("f" "b"))]).

(** The copies themselves differ under the λ of the children, an
    eliminator on one side, a [fix] on the other; the parity of a copy of
    three is the same. *)
Example copy_paired :
  accepted sg_copy copy_fix copy_ty &&
  converts sg_copy ["A"; "B"; "a"; "f"]
    (copy_fix "A" "B" (sup "A" "B" "a" "f")) (sup "A" "B" "a" (λ "b", copy_fix "A" "B" ("f" "b"))) &&
  converts sg_copy ["A"; "B"; "a"; "f"]
    (copy "A" "B" (sup "A" "B" "a" "f")) (sup "A" "B" "a" (λ "b", copy "A" "B" ("f" "b"))) &&
  converts sg_copy ["n"] (copy_W copy_fix (succ_W "n")) (succ_W (copy_W copy_fix "n")) &&
  same_result sg_copy (parity_W (copy_W copy_fix three_W)) (parity_W (copy_W copy three_W)) &&
  negb (same_result sg_copy (copy_W copy_fix three_W) (copy_W copy three_W)) = true.
Proof. vm_compute. reflexivity. Qed.

(** ** Refused both ways *)

Definition sg_pred : signature := sg_of (compile_all predicative prog_fuel sg_direct [pred_fn]).

Definition g_fix : nterm := NFix "g" (Nat ~> Nat) 0 (λ "n", nat_case "n" zero (λ "k", "g" (pred "k"))).

Example g_refused :
  is_not_structural (refused_by (compile_all predicative prog_fuel sg_direct [pred_fn; g_fn])) &&
  match snd (run_infer predicative sg_pred prog_fuel [] (build [] g_fix)) with
  | Rejected (ENotGuarded _ (GNotSubterm _ a)) => term_eqb a (App (Const (Def "pred")) (Var 0))
  | _ => false
  end = true.
Proof. vm_compute. reflexivity. Qed.
