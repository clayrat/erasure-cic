(** * The redex the annotated rules lose

    The program [((λf x. f x) ∷ ((Bool → Bool) → Bool → Bool)) ((λy. y) ∷
    (Bool → Bool))] checks at [Bool → Bool].  Evaluation by value drops
    the annotations and reduces the β-redex at its head, to
    [λx. (λy. y) x]: a λ in the position of a function, without an
    annotation.  The annotated rules give a λ no type to synthesize, so
    this value does not check, at any type: preservation does not hold
    for [chk] (Contracts.v, [annotated_preservation_fails]).  The
    declarative rules type it, [T_Lam] reading the domain off the Π.

    The same example in the relation of erasure: the function [erase]
    erases the program, the erased program evaluates to the erasure of
    the source value, and both erasures are derivations of [erases]
    (Relation.v), the one of the value through the unannotated redex.
    The function itself would refuse the value: it asks the type of the
    λ in the position of a function. *)

From Stdlib Require Import String List.
Import ListNotations.
From DepTypes.Common Require Import Result.
From DepTypes.PTS Require Import Syntax Spec Signature Reduction EvalSrc Typing Bidir Check CheckSound.
From DepTypes.Configs Require Import Predicative.
From IndTypes.Checked Require Import Steps.
From CIC.Erasure Require Import Target Erase Relation.

Local Open Scope string_scope.

Local Notation BB := (Pi Bool Bool) (only parsing).
Local Notation Sp := predicative_prop (only parsing).

Definition program : term :=
  App (Ann (Lam (Lam (App (Var 1) (Var 0)))) (Pi BB BB)) (Ann (Lam (Var 0)) BB).
Definition program_value : term := Lam (App (Lam (Var 0)) (Var 0)).
Definition program_erased : eterm := EApp (ELam (ELam (EApp (EVar 1) (EVar 0)))) (ELam (EVar 0)).
Definition value_erased : eterm := ELam (EApp (ELam (EVar 0)) (EVar 0)).

(** ** The annotated rules *)

Lemma program_checked : chk Sp ∅ [] program BB.
Proof.
  exact (proj2 (proj2 (run_check_sound Sp ∅ 100 [] program BB tt ltac:(vm_compute; reflexivity)))).
Qed.

Lemma program_evaluates : eval_src ∅ 10 program = CbvValue program_value.
Proof. vm_compute. reflexivity. Qed.

Lemma lam_synthesizes_nothing : forall G b A, ~ synth Sp ∅ G (Lam b) A.
Proof. intros G b A H. inversion H. Qed.

(** A λ applied does not check: the application must synthesize, and its
    function too. *)
Lemma redex_not_checked : forall G b u A, ~ chk Sp ∅ G (App (Lam b) u) A.
Proof.
  intros G b u A H. inversion H as [ | | ? ? A' ? Hs _]; subst.
  inversion Hs; subst.
  match goal with Hf : synth _ _ _ (Lam _) _ |- _ => exact (lam_synthesizes_nothing _ _ _ Hf) end.
Qed.

Lemma value_not_checked : forall T, ~ chk Sp ∅ [] program_value T.
Proof.
  intros T H. inversion H as [? ? ? A B _ Hb | | ? ? ? ? Hs _]; subst.
  - exact (redex_not_checked _ _ _ _ Hb).
  - exact (lam_synthesizes_nothing _ _ _ Hs).
Qed.

(** ** The declarative rules *)

Lemma typed_app : forall G f u A B T,
  has_type Sp ∅ G f (Pi A B) -> has_type Sp ∅ G u A -> T = subst1 B u -> has_type Sp ∅ G (App f u) T.
Proof. intros G f u A B T Hf Hu ->. exact (T_App _ _ _ _ _ _ _ Hf Hu). Qed.

Lemma bool_typed : forall G, wf_ctx Sp ∅ G -> has_type Sp ∅ G Bool (Srt (Univ 0)).
Proof. intros G H. apply T_Bool; [exact H | reflexivity]. Qed.

Lemma bool_ctx : forall G, wf_ctx Sp ∅ G -> wf_ctx Sp ∅ (Bool :: G).
Proof. intros G H. eapply W_Cons. exact (bool_typed G H). Qed.

Lemma bb_typed : forall G, wf_ctx Sp ∅ G -> has_type Sp ∅ G BB (Srt (Univ 0)).
Proof.
  intros G H. eapply T_Pi; [exact (bool_typed G H) | exact (bool_typed _ (bool_ctx G H)) | reflexivity].
Qed.

Lemma bb_ctx : forall G, wf_ctx Sp ∅ G -> wf_ctx Sp ∅ (BB :: G).
Proof. intros G H. eapply W_Cons. exact (bb_typed G H). Qed.

Lemma bool_bool_ctx : wf_ctx Sp ∅ [Bool; Bool].
Proof. exact (bool_ctx _ (bool_ctx _ (W_Nil _ _))). Qed.

Lemma value_typed : has_type Sp ∅ [] program_value BB.
Proof.
  eapply T_Lam; [ | exact (bb_typed _ (W_Nil _ _))].
  eapply typed_app with (A := Bool) (B := Bool); [ | | reflexivity].
  - eapply T_Lam; [ | exact (bb_typed _ (bool_ctx _ (W_Nil _ _)))].
    apply T_Var; [exact bool_bool_ctx | reflexivity].
  - apply T_Var; [exact (bool_ctx _ (W_Nil _ _)) | reflexivity].
Qed.

(** ** Erasure *)

Lemma erases_app : forall G f u A B T f' u',
  erases Sp ∅ G f (Pi A B) f' -> erases Sp ∅ G u A u' -> T = subst1 B u ->
  erases Sp ∅ G (App f u) T (EApp f' u').
Proof. intros G f u A B T f' u' Hf Hu ->. exact (X_App _ _ _ _ _ _ _ _ _ Hf Hu). Qed.

Lemma program_erasure : erase_term Sp ∅ 100 [] program BB = Erased program_erased.
Proof. vm_compute. reflexivity. Qed.

Lemma empty_erasure : erase_env Sp ∅ 100 = Erased prim_entries.
Proof. vm_compute. reflexivity. Qed.

Lemma erased_evaluates : eval_erased prim_entries 10 program_erased = CbvValue value_erased.
Proof. vm_compute. reflexivity. Qed.

(** The function refuses the value: it infers the type of the λ applied. *)
Lemma value_erasure_refused : exists err, erase_term Sp ∅ 100 [] program_value BB = NotErasable err.
Proof. eexists. vm_compute. reflexivity. Qed.

Lemma program_related : erases Sp ∅ [] program BB program_erased.
Proof.
  pose proof (W_Nil Sp ∅) as W0. pose proof (bb_ctx _ W0) as W1.
  pose proof (bool_ctx _ W1) as W2.
  eapply erases_app with (A := BB) (B := BB); [ | | reflexivity].
  - eapply X_Ann; [eapply T_Pi; [exact (bb_typed _ W0) | exact (bb_typed _ W1) | reflexivity] | ].
    eapply X_Lam; [ | eapply T_Pi; [exact (bb_typed _ W0) | exact (bb_typed _ W1) | reflexivity]].
    eapply X_Lam; [ | exact (bb_typed _ W1)].
    eapply erases_app with (A := Bool) (B := Bool); [ | | reflexivity].
    + apply X_Var. apply T_Var; [exact W2 | reflexivity].
    + apply X_Var. apply T_Var; [exact W2 | reflexivity].
  - eapply X_Ann; [exact (bb_typed _ W0) | ].
    eapply X_Lam; [ | exact (bb_typed _ W0)].
    apply X_Var. apply T_Var; [exact (bool_ctx _ W0) | reflexivity].
Qed.

Lemma value_related : erases Sp ∅ [] program_value BB value_erased.
Proof.
  pose proof (W_Nil Sp ∅) as W0. pose proof (bool_ctx _ W0) as W1.
  eapply X_Lam; [ | exact (bb_typed _ W0)].
  eapply erases_app with (A := Bool) (B := Bool); [ | | reflexivity].
  - eapply X_Lam; [ | exact (bb_typed _ W1)].
    apply X_Var. apply T_Var; [exact bool_bool_ctx | reflexivity].
  - apply X_Var. apply T_Var; [exact W1 | reflexivity].
Qed.
