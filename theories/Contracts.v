(** * Contracts of lecture 8: erasure of CIC

    The contracts of the kernel (acceptance of [Case], [Fix] and the guard)
    and of the declarations (sorts of elimination) stay in the contracts
    files of their own branches [cic]; this file re-exports them and adds
    the contracts of erasure.  Of the kernel only PTS/Contracts.v is
    imported: its Contracts.v of lecture 6 needs the PCF translation and
    strictness-pcf, which this project does not build.

    As in the files of the other lectures, a contract followed by a
    theorem [..._holds] is proved; one without is an open obligation,
    stated precisely but not proved.  The contract of erasure itself,
    [erasure_preserves_observations], is open: it rests on the
    obligations below it, which are the lemmas its proof needs.  The
    proved contracts are the pieces that hold by construction: the rules
    of the target evaluator, the soundness of the decision of
    observations, and the erased signature as the erasure of each
    entry. *)

From Stdlib Require Import String List Relations.
Import ListNotations.
From DepTypes.Common Require Import Result.
From DepTypes.PTS Require Import Syntax Spec Signature Reduction EvalSrc Bidir Check.
From DepTypes.Configs Require Import Predicative.
From DepTypes.PTS Require Export Contracts.
From IndTypes Require Export Contracts.
From CIC.Erasure Require Import Target Erase Observe Checked.

(** ** The target evaluator *)

(** The rules of stage 0 that differ from the source: [□] applied to a
    value is [□], a match on [□] is stuck, and a [fix] with its [k + 1]
    arguments unfolds whatever they are. *)
Definition target_rules : Prop :=
  forall se fuel,
  (forall g a, eval_erased se fuel g = CbvValue EBox -> eval_erased se fuel a = CbvValue a ->
     eval_erased se (S fuel) (EApp g a) = CbvValue EBox) /\
  (forall D x bs, eval_erased se fuel x = CbvValue EBox ->
     eval_erased se (S fuel) (ECase D x bs) = CbvStuck (ECase D EBox bs)) /\
  (forall g a vg va k b,
     eval_erased se fuel g = CbvValue vg -> eval_erased se fuel a = CbvValue va ->
     (forall b', vg <> ELam b') -> vg <> EBox ->
     espine_head (EApp vg va) = EFix k b -> length (espine_args (EApp vg va)) = S k ->
     eval_erased se (S fuel) (EApp g a)
     = eval_erased se fuel (eapps (esubst1 b (EFix k b)) (espine_args (EApp vg va)))).

Theorem target_rules_holds : target_rules.
Proof.
  intros se fuel. split; [exact (eval_box_app se fuel) | split; [exact (eval_case_box se fuel) | ]].
  exact (eval_fix_unfolds se fuel).
Qed.

(** ** Observations *)

(** The decision of observations is sound for the relation. *)
Definition observation_decision_sound : Prop :=
  forall sg fuel n T v w, observes sg fuel n T v w = true -> value_observation sg T v w.

Theorem observation_decision_sound_holds : observation_decision_sound.
Proof. intros sg fuel. exact (observes_sound sg fuel). Qed.

(** ** The erased signature *)

(** A δ-constant is found in the erased signature with its body erased
    at its type, and a declaration with its erased description: the
    number of its parameters and indices, its constructors with the
    shape of their fields, and its kind of elimination. *)
Definition erased_signature_entries : Prop :=
  forall Sp sg fuel strict se, erase_env_e Sp sg fuel strict = Ok se ->
  (forall f A b, sig_def sg f = Some (A, b) ->
     exists b', erase Sp sg fuel strict [] b A = Ok b' /\ efind_def se f = Some b') /\
  (forall D d, sig_ind sg D = Some d -> efind_ind se D = Some (erase_ind d)).

Theorem erased_signature_entries_holds : erased_signature_entries.
Proof.
  intros Sp sg fuel strict se H. split.
  - intros f A b Hf. exact (erase_entries_defs Sp sg fuel strict _ _ H f A b Hf).
  - intros D d Hd. exact (erase_entries_inds Sp sg fuel strict _ _ H D d Hd).
Qed.

(** ** The contract of erasure (open)

    For a checked signature, a closed term checked at an observable
    type, a successful erasure of both, and a value of the source
    program, the erased program reaches a related value with some
    budget.  The budgets are independent: the fuel of checking, of
    erasure and of each evaluator.  Running out of fuel, or an undecided
    erasure, does not refute the contract; it does not satisfy its
    premises.  Neither the normalization of the source theory nor the
    totality of erasure with enough fuel follows from it. *)
Definition erasure_preserves_observations : Prop :=
  forall sg t T fenv ferase fsrc se e v,
    wf_checked sg ->
    btype predicative_prop sg [] T -> chk predicative_prop sg [] t T ->
    Observable sg T ->
    erase_env predicative_prop sg fenv = Erased se ->
    erase_term predicative_prop sg ferase [] t T = Erased e ->
    eval_src sg fsrc t = CbvValue v ->
    exists fdst w, eval_erased se fdst e = CbvValue w /\ value_observation sg T v w.

(** ** The obligations behind it *)

(** The walk agrees with the annotated rules: a term erased to [□] is a
    type or a proof in the sense of the kernel, the sort found
    structurally being the sort the kernel gives its type. *)
Definition erasure_decision_consistent : Prop :=
  forall sg fuel G T, wf_checked sg -> bwf_ctx predicative_prop sg G -> btype predicative_prop sg G T ->
  erasable predicative_prop sg fuel G T = Ok true ->
  arity sg T \/ exists K, synth predicative_prop sg G T K /\ red sg K (Srt Prp).

(** Erasure commutes with substitution, up to the evaluation of the
    erased term: the erasure of [b[u/0]] at [B[u/0]] behaves as the
    erasure of [b] with the erasure of [u] substituted. *)
Definition erasure_substitution : Prop :=
  forall sg fuel A B b u eb eu ebu se,
    wf_checked sg -> chk predicative_prop sg [A] b B -> chk predicative_prop sg [] u A ->
    erase predicative_prop sg fuel true [A] b B = Ok eb ->
    erase predicative_prop sg fuel true [] u A = Ok eu ->
    erase predicative_prop sg fuel true [] (subst1 b u) (subst1 B u) = Ok ebu ->
    erase_env predicative_prop sg fuel = Erased se ->
    forall n w, eval_erased se n ebu = CbvValue w ->
    exists m w', eval_erased se m (esubst1 eb eu) = CbvValue w' /\ w' = w.

(** Call-by-value evaluation of the source keeps the type, in a checked
    signature: the subject reduction the simulation needs. *)
Definition source_preservation : Prop :=
  forall sg fuel t T v, wf_checked sg -> chk predicative_prop sg [] t T ->
  eval_src sg fuel t = CbvValue v -> chk predicative_prop sg [] v T.

(** The simulation: a value of the source, at an observable type, is
    reached by the erasure.  The singleton rule on [□], the hypotheses
    of recursive fields of proofs and the unreachability of an empty
    elimination in a successful source run are its cases. *)
Definition erasure_simulation : Prop :=
  forall sg fuel t T v e se,
    wf_checked sg -> chk predicative_prop sg [] t T -> Observable sg T ->
    eval_src sg fuel t = CbvValue v ->
    erase_term predicative_prop sg fuel [] t T = Erased e ->
    erase_env predicative_prop sg fuel = Erased se ->
    exists fdst w, eval_erased se fdst e = CbvValue w /\ value_observation sg T v w.

(** Erasure is total with enough fuel on checked terms of a checked
    signature: a separate obligation, not a premise of the contract. *)
Definition erasure_total : Prop :=
  forall sg t T, wf_checked sg -> btype predicative_prop sg [] T -> chk predicative_prop sg [] t T ->
  exists n, forall m, n <= m ->
    exists e se, erase_term predicative_prop sg m [] t T = Erased e /\ erase_env predicative_prop sg m = Erased se.
