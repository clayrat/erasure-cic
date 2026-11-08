(** * The checks of the milestone of universes

    Each check of stage 7, computed by the checker of Universes/Check.v:
    - the empty history of [isEven] with the primitive [Unit : Type₀]
      where lecture 7 needed [Unit_1] and [ensure_unit], and the same
      declaration refused without cumulativity;
    - [ΠA:Type u. A → A : Type (u+1)];
    - [id@{u}] with independent instances at two levels, its application
      to itself refused with one instance and accepted with a fresh one,
      and the constraints of a constant substituted at its instances;
    - [Type u : Type u] refused as the cycle [u < u];
    - the cycle [u ≤ v ≤ u] accepted, [u < v ≤ u] refused;
    - cumulativity directed: a universe lifts and does not lower, Π is
      covariant in its codomain only, Σ and conversion are not
      cumulative;
    - the fragment of constraints: a max on the left decomposes, a max on
      the right is accepted only when entailed through one of its
      elements, and is otherwise outside the fragment.
    Then the graph by itself: models, cycles, entailment with
    counter-models. *)

From Stdlib Require Import String List ZArith.
Import ListNotations.
From DepTypes.Common Require Import Result.
From CIC.Universes Require Import Level Graph Constraints Term Check.

Local Open Scope string_scope.

Definition u : level := lvar "u".
Definition v : level := lvar "v".
Definition w : level := lvar "w".
Definition l1 : level := lconst 1.
Definition l2 : level := lconst 2.

Definition fuel : nat := 200.

Definition sig_of (r : result uerror usig) : usig := match r with Ok sg => sg | Err _ => [] end.

(** ** The empty history at level 1

    [Below : (ℕ → Type₁) → ℕ → Type₁], as in lecture 7 for the motive of
    [isEven]:

      Below P := elimNat@{2} (λ_. Type₁) Unit (λ n ih. Σ(_ : P n). ih)

    The method of [zero] is the primitive [Unit : Type₀] checked against
    [Type₁]: accepted by cumulativity, with no constraint left.  Without
    it, conversion requires [Type₀ ≡ Type₁], hence [1 ≤ 0], refused with
    the counter-model of the empty context — the refusal of lecture 7,
    which needed [Unit_1] built by [ensure_unit]. *)
Definition below_type : uterm := UPi (arrow UNat (USort l1)) (arrow UNat (USort l1)).
Definition below_body : uterm :=
  ULam (uapps (UElimNat l2)
          [ULam (USort l1); UUnit; ULam (ULam (USigma (UApp (UVar 2) (UVar 1)) (UVar 1)))]).
Definition below_decl : udecl := UDecl "Below" [] [] Rigid below_type below_body.

Definition sg_below : usig := sig_of (declare true fuel [] below_decl).

Example below_cumulative : map ud_name sg_below = ["Below"] /\ map ud_cstrs sg_below = [[]].
Proof. vm_compute. split; reflexivity. Qed.

Example below_without_cumulativity :
  check_decl false [] fuel below_decl
  = Err (ULevels (CNotImplied (cle l1 lzero) (Some [(LZero, 0)]))).
Proof. vm_compute. reflexivity. Qed.

(** The history computes: [Below P 0 ≡ Unit] and
    [Below P 1 ≡ Σ(_ : P 0). Unit], here with [P := λ_. ℕ], itself a
    family into [Type₁] by cumulativity. *)
Definition const_nat : uterm := ULam UNat.

Example below_computes :
  check_term true sg_below fuel [] [] Rigid UTt (uapps (UConst "Below" []) [const_nat; UZero])
    = Ok ([], [(LZero, 0)]) /\
  check_term true sg_below fuel [] [] Rigid (UPair UZero UTt)
    (uapps (UConst "Below" []) [const_nat; UApp USucc UZero]) = Ok ([], [(LZero, 0)]) /\
  match check_term true sg_below fuel [] [] Rigid UTt
          (uapps (UConst "Below" []) [const_nat; UApp USucc UZero]) with
  | Err (UMismatch UUnit (USigma _ _)) => True
  | _ => False
  end.
Proof. vm_compute. split; [reflexivity | split; [reflexivity | exact I]]. Qed.

(** ** Π at a variable level *)

Definition id_type (l : level) : uterm := UPi (USort l) (arrow (UVar 0) (UVar 0)).

Example pi_level : infer_term true [] fuel ["u"] [] Rigid (id_type u)
  = Ok (USort [(LVar "u", 1)], [], [(LZero, 0)]).
Proof. vm_compute. reflexivity. Qed.

(** ** [id@{u}] and its instances *)

Definition id_decl : udecl := UDecl "id" ["u"] [] Rigid (id_type u) (ULam (ULam (UVar 0))).
Definition sg_id : usig := sig_of (declare true fuel [] id_decl).

(** Two instances, at [0] and at [1], in one closed term each. *)
Example id_two_levels :
  infer_term true sg_id fuel [] [] Rigid (uapps (UConst "id" [lzero]) [UNat; UZero])
    = Ok (UNat, [], [(LZero, 0)]) /\
  infer_term true sg_id fuel [] [] Rigid (uapps (UConst "id" [l1]) [USort lzero; UNat])
    = Ok (USort lzero, [], [(LZero, 0)]).
Proof. vm_compute. split; reflexivity. Qed.

(** [id (ΠA:Type u. A → A) id]: with the same instance [u] for both, the
    argument [ΠA:Type u. A → A : Type (u+1)] is required in [Type u], the
    cycle [u < u]; in a rigid context it is not implied. *)
Definition self_app (outer : list level) : uterm :=
  uapps (UConst "id" outer) [id_type u; UConst "id" [u]].

Example id_one_instance :
  infer_term true sg_id fuel ["u"] [] Extensible (self_app [u])
    = Err (ULevels (CCycle [(LVar "u", 1%Z, LVar "u")])) /\
  infer_term true sg_id fuel ["u"] [] Rigid (self_app [u])
    = Err (ULevels (CNotImplied (cle (lsucc u) u) (Some [(LZero, 0); (LVar "u", 0)]))).
Proof. vm_compute. split; reflexivity. Qed.

(** With a fresh instance [?0] for the outer [id], the requirement is
    [u + 1 ≤ ?0], that is [u < ?0]: accepted, with a model. *)
Example id_fresh_instance :
  infer_term true sg_id fuel ["u"] [] Extensible (self_app [])
    = Ok (id_type u, [cle (lsucc u) (linst 0)], [(LZero, 0); (LVar "u", 0); (LInst 0, 1)]).
Proof. vm_compute. reflexivity. Qed.

(** A rigid declaration names every variable: a fresh instance is
    refused. *)
Example id_rigid_needs_instance :
  infer_term true sg_id fuel ["u"] [] Rigid (self_app []) = Err (UNeedsInstance "id").
Proof. vm_compute. reflexivity. Qed.

(** [idid] is abstracted over [u] and the fresh [?0], with [u < ?0] in
    its context; an instance substitutes its levels in that constraint:
    [idid@{0 1}] is accepted, [idid@{1 1}] is refused by [2 ≤ 1]. *)
Definition idid_decl : udecl := UDecl "idid" ["u"] [] Extensible (id_type u) (self_app []).
Definition sg_idid : usig := sig_of (declare true fuel sg_id idid_decl).

Example idid_context :
  map (fun d => (ud_name d, ud_univs d, ud_cstrs d)) sg_idid
  = [("id", [LVar "u"], []); ("idid", [LVar "u"; LInst 0], [cle (lsucc u) (linst 0)])].
Proof. vm_compute. reflexivity. Qed.

Example idid_instances :
  infer_term true sg_idid fuel [] [] Rigid (UConst "idid" [lzero; l1])
    = Ok (id_type lzero, [], [(LZero, 0)]) /\
  infer_term true sg_idid fuel [] [] Rigid (UConst "idid" [l1; l1])
    = Err (ULevels (CNotImplied (cle l2 l1) (Some [(LZero, 0)]))).
Proof. vm_compute. split; reflexivity. Qed.

(** ** [Type u : Type u] *)

Example type_in_type :
  check_term true [] fuel ["u"] [] Extensible (USort u) (USort u)
    = Err (ULevels (CCycle [(LVar "u", 1%Z, LVar "u")])) /\
  check_term true [] fuel ["u"] [] Rigid (USort u) (USort u)
    = Err (ULevels (CNotImplied (cle (lsucc u) u) (Some [(LZero, 0); (LVar "u", 0)]))) /\
  check_term true [] fuel ["u"] [] Rigid (USort u) (USort (lsucc u)) = Ok ([], [(LZero, 0)]).
Proof. vm_compute. repeat split; reflexivity. Qed.

(** ** Cycles of constraints, and lifting without lowering

    [lift@{u v | u ≤ v} : Type u → Type v := λA. A] lifts a type.  The
    same body at [Type v → Type u] lowers it:
    - refused in a rigid context, [v ≤ u] not implied by [u ≤ v], with
      the counter-model [u = 0, v = 1];
    - in an extensible one it adds [v ≤ u]: the cycle [u ≤ v ≤ u] of
      non-strict edges is accepted, and it forces [u = v];
    - with [u < v] declared, [u < v ≤ u] is a cycle of weight 1, refused.
    Declared directly, [u ≤ v ≤ u] is accepted and [u < v ≤ u] refused
    before any checking. *)
Definition lift_decl : udecl := UDecl "lift" ["u"; "v"] [cle u v] Rigid (arrow (USort u) (USort v)) (ULam (UVar 0)).
Definition lower_decl (md : mode) (C : list constr) : udecl :=
  UDecl "lower" ["u"; "v"] C md (arrow (USort v) (USort u)) (ULam (UVar 0)).

Example lift_lower :
  (match check_decl true [] fuel lift_decl with Ok (d, _) => ud_cstrs d = [cle u v] | Err _ => False end) /\
  check_decl true [] fuel (lower_decl Rigid [cle u v])
    = Err (ULevels (CNotImplied (cle v u) (Some [(LZero, 0); (LVar "u", 0); (LVar "v", 1)]))) /\
  (match check_decl true [] fuel (lower_decl Extensible [cle u v]) with
   | Ok (d, _) => ud_cstrs d = [cle u v; cle v u] | Err _ => False end) /\
  check_decl true [] fuel (lower_decl Extensible [clt u v])
    = Err (ULevels (CCycle [(LVar "u", 1%Z, LVar "v"); (LVar "v", 0%Z, LVar "u")])).
Proof. vm_compute. repeat split; reflexivity. Qed.

Example declared_cycles :
  (match check_decl true [] fuel (lower_decl Rigid [cle u v; cle v u]) with Ok _ => True | Err _ => False end) /\
  check_decl true [] fuel (lower_decl Rigid [clt u v; cle v u])
    = Err (ULevels (CCycle [(LVar "u", 1%Z, LVar "v"); (LVar "v", 0%Z, LVar "u")])).
Proof. vm_compute. split; [exact I | reflexivity]. Qed.

(** The instance [lift@{1 0}] substitutes [1 ≤ 0] for [u ≤ v]. *)
Definition sg_lift : usig := sig_of (declare true fuel [] lift_decl).

Example lift_instances :
  infer_term true sg_lift fuel [] [] Rigid (UConst "lift" [lzero; l1])
    = Ok (arrow (USort lzero) (USort l1), [], [(LZero, 0)]) /\
  infer_term true sg_lift fuel [] [] Rigid (UConst "lift" [l1; lzero])
    = Err (ULevels (CNotImplied (cle l1 lzero) (Some [(LZero, 0)]))).
Proof. vm_compute. split; reflexivity. Qed.

(** ** Cumulativity is directed

    [ℕ : Type₁] by [Type₀ ≤ Type₁]; [Type₁ : Type₁] is refused,
    [Type₂ ≤ Type₁] being [2 ≤ 1].  Without cumulativity [ℕ : Type₁] is
    refused too: conversion requires [Type₀ ≡ Type₁]. *)
Example cumulativity_directed :
  check_term true [] fuel [] [] Rigid UNat (USort l1) = Ok ([], [(LZero, 0)]) /\
  check_term true [] fuel [] [] Rigid (USort l1) (USort l1)
    = Err (ULevels (CNotImplied (cle l2 l1) (Some [(LZero, 0)]))) /\
  check_term false [] fuel [] [] Rigid UNat (USort l1)
    = Err (ULevels (CNotImplied (cle l1 lzero) (Some [(LZero, 0)]))).
Proof. vm_compute. repeat split; reflexivity. Qed.

(** Π: a family [ℕ → Type₀] is a family [ℕ → Type₁], codomains being
    compared by cumulativity; a function [Type₀ → ℕ] is not a function
    [Type₁ → ℕ], domains being compared by conversion.  Σ is not
    cumulative: an annotated pair of [Σ(_:ℕ). Type₁] is not one of
    [Σ(_:ℕ). Type₂], while the same pair checked directly against it is. *)
Definition fam0 : uterm := UAnn (ULam UNat) (arrow UNat (USort lzero)).
Definition fun0 : uterm := UAnn (ULam UZero) (arrow (USort lzero) UNat).
Definition pair0 : uterm := UAnn (UPair UZero UNat) (USigma UNat (USort lzero)).

Example cumulativity_pi_sigma :
  check_term true [] fuel [] [] Rigid fam0 (arrow UNat (USort l1)) = Ok ([], [(LZero, 0)]) /\
  check_term true [] fuel [] [] Rigid fun0 (arrow (USort l1) UNat)
    = Err (ULevels (CNotImplied (cle l1 lzero) (Some [(LZero, 0)]))) /\
  check_term true [] fuel [] [] Rigid pair0 (USigma UNat (USort l1))
    = Err (ULevels (CNotImplied (cle l1 lzero) (Some [(LZero, 0)]))) /\
  check_term true [] fuel [] [] Rigid (UPair UZero UNat) (USigma UNat (USort l1)) = Ok ([], [(LZero, 0)]).
Proof. vm_compute. repeat split; reflexivity. Qed.

(** ** The fragment of constraints

    [max(u, v) ≤ w] is two edges; [w ≤ max(u, v)] is a disjunction and
    is not declared.  A requirement with a max on the right is accepted
    when one of its elements is above in the graph: [A : Type u] at
    [Type (max w v)] under [u ≤ w].  Without such an element it is
    outside the fragment in an extensible context — not refuted, since
    it could hold by [u ≤ w] or by [u ≤ v] — and not implied in a rigid
    one. *)
Example fragment :
  decompose (cle (lmax u v) w) = Some [(LVar "u", 0%Z, LVar "w"); (LVar "v", 0%Z, LVar "w")] /\
  decompose (cle w (lmax u v)) = None /\
  check_decl true [] fuel (UDecl "bad" ["u"; "v"; "w"] [cle w (lmax u v)] Rigid UUnit UTt)
    = Err (ULevels (CNotInFragment (cle w (lmax u v)))).
Proof. vm_compute. repeat split; reflexivity. Qed.

Definition coerce_max (C : list constr) (md : mode) : udecl :=
  UDecl "coerce" ["u"; "v"; "w"] C md (arrow (USort u) (USort (lmax w v))) (ULam (UVar 0)).

Example max_on_the_right :
  (match check_decl true [] fuel (coerce_max [cle u w] Rigid) with Ok _ => True | Err _ => False end) /\
  check_decl true [] fuel (coerce_max [] Extensible)
    = Err (ULevels (CUnsupported (cle u (lmax w v)))) /\
  check_decl true [] fuel (coerce_max [] Rigid)
    = Err (ULevels (CNotImplied (cle u (lmax w v)) None)).
Proof. vm_compute. repeat split; exact I || reflexivity. Qed.

(** ** The graph by itself *)

Definition au : atom := LVar "u".
Definition av : atom := LVar "v".
Definition aw : atom := LVar "w".

Example graph_verdicts :
  solve [(au, 0%Z, av); (av, 0%Z, au)] = Consistent [(LZero, 0); (av, 0); (au, 0)] /\
  solve [(au, 1%Z, av); (av, 0%Z, au)] = Cycle [(au, 1%Z, av); (av, 0%Z, au)] /\
  solve [(au, 1%Z, au)] = Cycle [(au, 1%Z, au)] /\
  solve [(au, 1%Z, LZero)] = Cycle [(au, 1%Z, LZero); (LZero, 0%Z, au)] /\
  solve [(au, 1%Z, av); (av, 1%Z, aw)] = Consistent [(LZero, 0); (au, 0); (av, 1); (aw, 2)].
Proof. vm_compute. repeat split; reflexivity. Qed.

(** [u < v ≤ w] entails [u < w], by the cycle with its negation
    [w ≤ u]; it does not entail [w ≤ u], refuted by [u = 0, v = w = 1]. *)
Example graph_entailment :
  entails [(au, 1%Z, av); (av, 0%Z, aw)] (au, 1%Z, aw)
    = Entailed [(aw, 0%Z, au); (au, 1%Z, av); (av, 0%Z, aw)] /\
  entails [(au, 1%Z, av); (av, 0%Z, aw)] (aw, 0%Z, au)
    = Refuted [(LZero, 0); (au, 0); (av, 1); (aw, 1)].
Proof. vm_compute. split; reflexivity. Qed.
