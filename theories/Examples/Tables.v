(** * Four tables on one checker

    The checker of lecture 6 is parameterized by a table of sorts, axioms
    and rules.  The terms below are written once, in the sorts ∗ and □,
    and checked under four tables, the sorts renamed for each:

    | table                  | ∗ read as | □ read as |
    |------------------------|-----------|-----------|
    | U⁻                     | ∗         | □         |
    | λC (CoC)               | ∗         | □         |
    | predicative hierarchy  | Type₀     | Type₁     |
    | hierarchy with Prop    | Prop      | Type₁     |

    What a program may do is decided by the rules of sorts, not by the
    constructs of the syntax:

    | term                     | U⁻          | λC      | predicative | with Prop |
    |--------------------------|-------------|---------|-------------|-----------|
    | ΠA:∗. A → A              | ∗           | ∗       | Type₁       | Prop      |
    | id (ΠA:∗. A → A) id      | accepted    | accepted| rejected    | accepted  |
    | A : ∗ ⊢ A → ∗            | no (∗,□)    | □       | Type₁       | Type₁     |
    | ΠA:∗. ∗                  | □           | □       | Type₁       | Type₁     |
    | □                        | △           | no type | Type₂       | Type₂     |

    The polymorphic identity is impredicative in U⁻, in λC and in Prop,
    and can be applied to its own type; in the predicative hierarchy its
    type is a level up and the application is rejected.  A family indexed
    by terms needs the rule (∗,□), which U⁻ lacks.  Prop plays in CIC the
    role of ∗ in λC, while the Type_i above it stay predicative. *)

From Stdlib Require Import String List.
Import ListNotations.
From DepTypes.Common Require Import Result.
From DepTypes.PTS Require Import Syntax Named Spec Signature Check EmptySig.
From DepTypes.Configs Require Import Finite Predicative.
From DepTypes.SystemU Require Import Looping.

Open Scope string_scope.
Open Scope nterm_scope.

Definition tables_fuel : nat := 200.

(** ∗, □, △ read as Prop, Type₁, Type₂. *)
Definition u_to_prop (s : sort) : sort :=
  match s with
  | Star => Prp
  | Box => Univ 1
  | Tri => Univ 2
  | s => s
  end.

Definition tables : list (spec * (sort -> sort)) :=
  [ (system_u_minus, fun s => s);
    (coc, fun s => s);
    (predicative, u_to_univ);
    (predicative_prop, u_to_prop) ].

(** The answers of the four tables to a context and a term in ∗ and □. *)
Definition infer_all (G : ctx) (t : term) : list (answer term) :=
  map (fun '(Sp, r) => snd (run_infer Sp ∅ tables_fuel (map (map_sorts r) G) (map_sorts r t))) tables.

Definition id_ty : nterm := Π "A" : ⋆, "A" ~> "A".
Definition id : nterm := (λ "A", λ "x", "x") ∷ id_ty.

Example id_ty_sorts :
  infer_all [] (build [] id_ty)
  = [Accepted (Srt Star); Accepted (Srt Star); Accepted (Srt (Univ 1)); Accepted (Srt Prp)].
Proof. vm_compute. reflexivity. Qed.

Example id_self_applied :
  infer_all [] (build [] (id id_ty id))
  = [ Accepted (build [] id_ty);
      Accepted (build [] id_ty);
      Rejected (EMismatch (map_sorts u_to_univ (build [] id_ty)) (Srt (Univ 0)) (Srt (Univ 1)));
      Accepted (map_sorts u_to_prop (build [] id_ty)) ].
Proof. vm_compute. reflexivity. Qed.

(** [A : ∗ ⊢ A → ∗]: a family of types indexed by the terms of [A]. *)
Example family_indexed_by_terms :
  infer_all [Srt Star] (build ["A"] ("A" ~> ⋆))
  = [ Rejected (ENoRule (Pi (Var 0) (Srt Star)) Star Box);
      Accepted (Srt Box); Accepted (Srt (Univ 1)); Accepted (Srt (Univ 1)) ].
Proof. vm_compute. reflexivity. Qed.

(** A type operator: rule (□,□). *)
Example type_operator :
  infer_all [] (build [] (Π "A" : ⋆, ⋆))
  = [Accepted (Srt Box); Accepted (Srt Box); Accepted (Srt (Univ 1)); Accepted (Srt (Univ 1))].
Proof. vm_compute. reflexivity. Qed.

(** □ is the top sort of λC; U⁻ has △ above it. *)
Example box_sorts :
  infer_all [] (Srt Box)
  = [Accepted (Srt Tri); Rejected (ETopSort Box); Accepted (Srt (Univ 2)); Accepted (Srt (Univ 2))].
Proof. vm_compute. reflexivity. Qed.
