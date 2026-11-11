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
    [erasure_preserves_observations], is proved
    ([erasure_preserves_observations_holds]): it follows from three
    obligations, by a proved decomposition, and the three are proved,
    the soundness of [erase], the simulation and the observation, with
    the obligations of the next level behind them.  The proved contracts are
    the pieces that hold by construction: the rules
    of the target evaluator, the soundness of the decision of
    observations, the erased signature as the erasure of each entry, a
    derivation of the relation of erasure as a typing derivation, and
    the decomposition itself; two obligations of the next level, the
    preservation of the declarative type by evaluation, from the
    subject reduction of the kernel, and the commutation of the
    relation of erasure with substitution; the simulation for a
    signature related to its erasure, and with it the reduction of
    [erasure_simulation] to the relation of a checked signature with its
    erasure; the observation for a type-correct signature whose
    instances are shaped, the instances of a checked signature being
    shaped; the type-correctness of checked signatures, and with it the
    observation and the declarative typing of checked terms; the
    soundness of [erase] for the relation, with the agreement of its
    decision of erasability with the declarative rules; the relation of
    a checked signature with its erasure, and with it the simulation;
    the contract of erasure; and one
    negative result, which fixes the form of preservation: it does not
    hold for the annotated rules.

    The three tiers of readiness of the plan:
    - tier 1, reached: the executable kernel with fuel, extracted
      (extraction/), with regression tests and the native references
      compared with the extract (reference/); the acceptance of [Case],
      [Fix] and the guard proved sound for the subterm relation
      (PTS/Contracts.v of the kernel); [eval_src], [eval_erased], erasure
      and the erasure of signatures implemented and checked on examples;
    - tier 2, reached: the contract of erasure proved
      ([erasure_preserves_observations_holds]).  Its
      decomposition is proved ([erasure_decomposition_holds]): as in
      MetaCoq, the contract follows from the soundness of the function
      [erase] for the relation of erasure (Erasure/Relation.v), the
      simulation of evaluation by value in the relation, and the
      observation of related values at an observable type.  The
      three are proved.
      The simulation is proved for a signature related to its erasure
      (Erasure/Simulation.v, [erasure_simulation_core_holds]), and a
      checked signature is so related ([checked_env_related_holds],
      Erasure/EnvRelated.v): the ι of an instance is
      simulated through the rule of its constructor, typed in its
      generic context as the registration checked and related to its
      structural erasure, the erased arguments of the redex
      substituted; the fields of a singleton proposition are proofs by
      the sorts the checker found for them.  The observation is proved for a
      type-correct signature whose instances have types of the arity of
      their eliminator (Erasure/Observation.v, with the canonical
      forms of PTS/Values.v of the kernel,
      [erasure_observation_core_holds]); the instances of a checked
      signature are so ([checked_instances_shaped_holds]), and a
      checked signature is type-correct
      ([checked_signature_typed_holds]): the observation holds
      ([erasure_observation_holds]).  So does [checked_declarative],
      by the soundness of the kernel for the declarative rules
      ([checked_declarative_holds]), and with it the soundness of
      [erase] ([erasure_sound_holds], Erasure/EraseSound.v): its walk
      relates the types it computes to those of a typing by the
      uniqueness of synthesized types up to conversion, and its
      decision of erasability agrees with the declarative rules
      ([erasure_decision_consistent_holds]).  The
      proofs need subject
      reduction for the declarative rules of
      CIC with [match] and [fix], proved in the kernel with what it
      rests on: confluence and the injectivity of Π, weakening and the
      substitution lemma, validity, the stability of the guard under
      reduction (PTS/Confluence.v, PTS/TypingSubst.v, PTS/Inversion.v,
      PTS/GuardRed.v, PTS/SubjectRed.v).  The preservation of the type
      by evaluation follows ([source_preservation_holds]), and the
      relation commutes with substitution as typing does
      ([erasure_substitution_holds], Erasure/RelationSubst.v).  The
      pairing of the equations and closed results of [fix]/[match]
      with the compiler of lecture 7, also of this tier, is done
      (Examples/Paired.v);
    - tier 3: the obligations of the section "Beyond the contract",
      stated as types of statements with the external results they rest
      on, never as axioms.
    Erasure removes no arguments ([□] keeps their positions), so the
    optimization of argument removal has no contract; the milestone of
    universes has its own, in the last section.

    The last section holds the contracts of the milestone of universes
    (stage 7), a separate checker with its own language: the contract of
    erasure is about the kernel with numeric levels and does not carry
    over to it. *)

From Stdlib Require Import String List Relations.
Import ListNotations.
From DepTypes.Common Require Import Result.
From DepTypes.PTS Require Import Syntax Spec Signature Reduction EvalSrc Typing Inversion Bidir BidirSound Check Values.
From DepTypes.Configs Require Import Predicative.
From DepTypes.PTS Require Export Contracts.
From IndTypes Require Export Contracts.
From IndTypes.Checked Require Import Steps Invariants Shaped IotaTyped SigTyped.
From CIC.Erasure Require Import Target Erase Observe Relation RelationSubst Simulation Observation
  EraseSound EnvRelated Preservation.

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
    shape of their fields, and its kind of elimination.  The primitives
    of the target are found as they are below every erased signature:
    a declaration under the name of one of them would shadow it, so
    that a match on [true] would get stuck after erasure, and the
    erasure of such a signature is refused. *)
Definition erased_signature_entries : Prop :=
  forall Sp sg fuel strict se, erase_env_e Sp sg fuel strict = Ok se ->
  (forall f A b, sig_def sg f = Some (A, b) ->
     exists b', erase Sp sg fuel strict [] b A = Ok b' /\ efind_def se f = Some b') /\
  (forall D d, sig_ind sg D = Some d -> efind_ind se D = Some (erase_ind d)) /\
  (forall D, reserved_name D = true -> efind_ind se D = efind_ind prim_entries D).

Theorem erased_signature_entries_holds : erased_signature_entries.
Proof.
  intros Sp sg fuel strict se H. split; [ | split].
  - intros f A b Hf. exact (erase_entries_defs Sp sg fuel strict _ _ H f A b Hf).
  - intros D d Hd. exact (erase_entries_inds Sp sg fuel strict _ _ H D d Hd).
  - intros D HD. exact (erase_entries_prims Sp sg fuel strict _ _ H D HD).
Qed.

(** ** The contract of erasure

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

(** ** Its decomposition

    The proof of MetaCoq ([MetaCoq 2020], below) goes through a relation
    of erasure: the function [erase] produces erasures in the relation,
    evaluation by value is simulated in the relation, and related values
    are observed alike.  The relation is that of Erasure/Relation.v:
    directed by the type, as [erase], since a λ of the kernel carries no
    domain, and with a typing premise at every rule.  It is needed
    because the function does not survive evaluation: [erase] infers
    the type of every function it meets, and a reduct of a checked
    program need not check ([annotated_preservation_fails] below).  The
    relation survives as the declarative typing does.

    The three obligations, stated for closed terms, as they are used: *)

(** What the function erases, the relation relates. *)
Definition erasure_sound : Prop :=
  forall sg fuel t T e,
    wf_checked sg -> btype predicative_prop sg [] T -> chk predicative_prop sg [] t T ->
    erase predicative_prop sg fuel true [] t T = Ok e -> erases predicative_prop sg [] t T e.

(** A value of the source is reached by every erasure in the relation,
    up to the relation.  The singleton rule on [□], the hypotheses of
    the recursive fields of proofs, the unfolding of a [fix] on [□] and
    the unreachability of an empty elimination in a successful source
    run are its cases. *)
Definition erasure_simulation : Prop :=
  forall sg fenv fsrc se t T e v,
    wf_checked sg -> erase_env predicative_prop sg fenv = Erased se ->
    erases predicative_prop sg [] t T e -> eval_src sg fsrc t = CbvValue v ->
    exists fdst w, eval_erased se fdst e = CbvValue w /\ erases predicative_prop sg [] v T w.

(** Its core is proved for a signature related to its erasure as the
    global environment of MetaCoq is: [erases_env] of
    Erasure/Simulation.v asks that the signature be type-correct, that
    its δ-bodies erase in the relation to the bodies of the erased
    signature, that its declarations and the primitives be found there,
    that the ι of an instance with active rules be simulated by the
    erased ι of its kind, and that the fields of a singleton
    proposition be proofs when its parameters are of the types of its
    parameters. *)
Definition erasure_simulation_core : Prop :=
  forall sg se fsrc t T e v,
    erases_env sg se -> erases predicative_prop sg [] t T e -> eval_src sg fsrc t = CbvValue v ->
    exists fdst w, eval_erased se fdst e = CbvValue w /\ erases predicative_prop sg [] v T w.

Theorem erasure_simulation_core_holds : erasure_simulation_core.
Proof. intros sg se fsrc t T e v Henv H Hv. exact (simulation_src sg se Henv fsrc t T e v H Hv). Qed.

(** A value of the source, related to an erased term at an observable
    type, is observed alike: such a type is not erasable, and its closed
    values are constructors of data. *)
Definition erasure_observation : Prop :=
  forall sg fsrc t T v w,
    wf_checked sg -> Observable sg T -> eval_src sg fsrc t = CbvValue v ->
    erases predicative_prop sg [] v T w -> value_observation sg T v w.

(** Its core is proved for a type-correct signature whose instances
    have types of the arity of their eliminator ([instances_shaped] of
    PTS/Values.v of the kernel): the canonical forms of closed values, read
    off the shape of the head of their types, and the observable types
    outside [erasable_at]. *)
Definition erasure_observation_core : Prop :=
  forall sg fsrc t T v w,
    signature_typed predicative_prop sg -> instances_shaped sg -> Observable sg T ->
    eval_src sg fsrc t = CbvValue v -> erases predicative_prop sg [] v T w -> value_observation sg T v w.

Theorem erasure_observation_core_holds : erasure_observation_core.
Proof. intros sg fsrc t T v w Hsig Hel HO Hv Hw. exact (observation_src sg Hsig Hel fsrc t T v w HO Hv Hw). Qed.

Definition erasure_decomposition : Prop :=
  erasure_sound -> erasure_simulation -> erasure_observation -> erasure_preserves_observations.

Theorem erasure_decomposition_holds : erasure_decomposition.
Proof.
  intros Hsound Hsim Hobs sg t T fenv ferase fsrc se e v Hsg HT Ht HO Hse He Hv.
  apply erase_term_erased in He.
  destruct (Hsim _ _ _ _ _ _ _ _ Hsg Hse (Hsound _ _ _ _ _ Hsg HT Ht He) Hv) as (fdst & w & Hw & Hvw).
  exists fdst, w. exact (conj Hw (Hobs _ _ _ _ _ _ Hsg HO Hv Hvw)).
Qed.

(** A derivation of the relation is a typing derivation of the declarative
    rules: one λ is used at one type throughout. *)
Definition erasure_relation_typed : Prop :=
  forall S sg G t T e, erases S sg G t T e -> has_type S sg G t T.

Theorem erasure_relation_typed_holds : erasure_relation_typed.
Proof. intros S sg. exact (proj1 (erases_typed S sg)). Qed.

(** ** The obligations behind them

    Behind [erasure_sound]: the annotated rules imply the declarative
    ones, and the decision of erasability agrees with them.  Both are
    proved below, and with them [erasure_sound]
    ([erasure_sound_holds]). *)

(** A term the kernel checked in a checked signature is typed by the
    declarative rules of PTS/Typing.v, against which the relation is
    stated.  The soundness of the kernel for the declarative rules is
    proved ([bidir_declarative_sound_holds], and [chk_sound] of
    PTS/BidirSound.v for checking), in a type-correct signature with a
    full table and distinct constructor names; [predicative_prop] is
    full, checked signatures have distinct constructor names
    ([checked_constructors_distinct_holds]) and are type-correct
    ([checked_signature_typed_holds]): proved
    ([checked_declarative_holds]). *)
Definition checked_declarative : Prop :=
  forall sg G t T,
    wf_checked sg -> bwf_ctx predicative_prop sg G -> btype predicative_prop sg G T ->
    chk predicative_prop sg G t T -> has_type predicative_prop sg G t T.

(** The walk agrees with the declarative rules: a term erased to [□] is
    a type or a proof, the sort found structurally being the sort the
    rules give its type. *)
Definition erasure_decision_consistent : Prop :=
  forall sg fuel G T,
    wf_checked sg -> bwf_ctx predicative_prop sg G -> btype predicative_prop sg G T ->
    erasable predicative_prop sg fuel G T = Ok true -> erasable_at predicative_prop sg G T.

(** Behind [erasure_simulation]: a checked signature is related to its
    erasure, type-correct in particular; evaluation keeps the
    declarative type, and the relation commutes with substitution, for
    β and the unfolding of [fix].  The three are proved, and so is
    the simulation for related signatures
    ([erasure_simulation_from_env_holds]): the simulation holds
    ([erasure_simulation_holds]). *)

(** What a registration step checks keeps a signature related to its
    erasure: the δ-bodies are erased by [erase], whose soundness
    relates them to their erasures ([erase_sound] of
    Erasure/EraseSound.v, behind [erasure_sound_holds]); the instances of
    the registration simulate their ι-rules after erasure, the indices
    of the hypotheses of recursive fields erased to [□]; a singleton
    proposition is declared only if the fields of its constructor are
    proofs over its parameters (Elim/Declare.v of elim-inductive-types),
    so they are proofs for parameters of the types of the parameters,
    and not otherwise: [and Bool Bool] has fields of type [Bool].  That the
    primitives are not shadowed holds of every erased signature
    ([erased_signature_entries]). *)
Definition checked_env_related : Prop :=
  forall sg fenv se, wf_checked sg -> erase_env predicative_prop sg fenv = Erased se -> erases_env sg se.

(** Proved (Erasure/EnvRelated.v): the ι of an
    instance is simulated through the rule of the constructor, typed in
    its generic context as the registration checked, related to its
    structural erasure, the erased arguments of the redex substituted;
    the fields of a singleton proposition are proofs by the sorts the
    checker found for them, carried to the final signature
    (Checked/Fields.v of elim-inductive-types). *)
Theorem checked_env_related_holds : checked_env_related.
Proof. exact env_related_checked. Qed.

Definition erasure_simulation_from_env : Prop := checked_env_related -> erasure_simulation.

Theorem erasure_simulation_from_env_holds : erasure_simulation_from_env.
Proof.
  intros Henv sg fenv fsrc se t T e v Hsg Hse H Hv.
  exact (erasure_simulation_core_holds sg se fsrc t T e v (Henv _ _ _ Hsg Hse) H Hv).
Qed.

Theorem erasure_simulation_holds : erasure_simulation.
Proof. exact (erasure_simulation_from_env_holds checked_env_related_holds). Qed.

(** Every registration step checks what [signature_typed] asks: the
    types of the constants are types, the δ-bodies have them, and the
    ι-rules of the instances keep the type of the redex.  The steps
    check in [predicative] or [predicative_prop]; the first is contained
    in the second, which adds Prop.  Proved below
    ([checked_signature_typed_holds]): the registrations keep the
    type-correctness of a signature with the rules of its instances typed
    (Checked/SigTyped.v of elim-inductive-types), by the soundness of the
    kernel's checker for
    the declarative rules, the separate lemma on ι and, for a
    declaration, a renaming of its family. *)
Definition checked_signature_typed : Prop :=
  forall sg, wf_checked sg -> signature_typed predicative_prop sg.

(** The ι-rules of an instance are checked once, in their generic
    context; every ι-contraction of the kernel is an instance of one, the
    context substituted by the arguments of the redex.  So ι keeps the
    declarative type in a signature whose constants have types that are
    types and whose active instances have their rules typed, in a full
    table (Checked/IotaTyped.v of elim-inductive-types): the condition of
    [signature_typed] on ι,
    by a separate lemma. *)
Definition iota_typed_from_rules : Prop :=
  forall S sg G t u T, sig_types_typed S sg -> full_table S -> instances_checked S sg ->
    iota sg t = Some u -> has_type S sg G t T -> has_type S sg G u T.

Theorem iota_typed_from_rules_holds : iota_typed_from_rules.
Proof. intros S sg G t u T Hty Hfull Hi. exact (iota_typed S sg Hty Hfull Hi G t u T). Qed.

(** A δ-constant and an instance are checked in a signature known to be
    type-correct, and the soundness of the checker gives their
    declarative types.  A declaration is checked in the signature that
    already holds it, whose type-correctness asks for the very types
    being checked.  Its check mentions the family only as [Ind D]: renamed
    to an inactive instance of the same type, a constant without rules,
    it is a check in the signature without the declaration, which is
    type-correct once the type of D is; renamed back, the declarative
    judgment holds in the signature with the declaration (the renaming
    of constants of PTS/ConstRename.v of the kernel, applied in
    Checked/SigTyped.v of elim-inductive-types). *)
Definition declarations_typed : Prop := declaration_typed.

Theorem declarations_typed_holds : declarations_typed.
Proof. exact declaration_typed_holds. Qed.

Theorem checked_signature_typed_holds : checked_signature_typed.
Proof. exact checked_typed. Qed.

(** Evaluation by value keeps the declarative type, in a type-correct
    signature: the subject reduction the simulation needs.  A value found
    is a reduct ([eval_src_sound] of the kernel), and a reduct has the
    types of the term ([subject_reduction]).  Not for the annotated
    rules, below. *)
Definition source_preservation : Prop :=
  forall sg fuel t T v,
    signature_typed predicative_prop sg -> has_type predicative_prop sg [] t T ->
    eval_src sg fuel t = CbvValue v -> has_type predicative_prop sg [] v T.

Theorem source_preservation_holds : source_preservation.
Proof.
  intros sg fuel t T v Hsig Ht Hv.
  exact (subject_reduction_holds _ _ _ _ _ _ Hsig Ht (eval_src_sound_holds _ _ _ _ Hv)).
Qed.

(** The relation commutes with substitution, as [typing_substitution]
    of the kernel: the erasure of [b] with the erasure of [u] substituted
    is an erasure of [b[u/0]].  The proof follows that of typing, by
    renaming then substitution (Erasure/RelationSubst.v). *)
Definition erasure_substitution : Prop :=
  forall sg G A b B u eb eu,
    erases predicative_prop sg (A :: G) b B eb -> erases predicative_prop sg G u A eu ->
    erases predicative_prop sg G (subst1 b u) (subst1 B u) (esubst1 eb eu).

Theorem erasure_substitution_holds : erasure_substitution.
Proof. intros sg. exact (erases_subst1 predicative_prop sg). Qed.

(** Behind [erasure_observation]: a checked signature is type-correct
    ([checked_signature_typed]), and the types of its instances are the
    telescopes the registration generates, of the arity of their
    eliminator, which is proved: every registration adds an instance at
    [elim_type d s] for the declaration of its family, and no later entry
    shadows either (Checked/Shaped.v of elim-inductive-types).  With both, the canonical forms of closed values and the
    observable types outside [erasable_at] are proved
    ([erasure_observation_core_holds]).  Uniqueness of types, which
    fails for the unannotated λ, is not needed: the types of values are
    compared by the shape of the head of their reducts. *)
Definition checked_instances_shaped : Prop := forall sg, wf_checked sg -> instances_shaped sg.

Theorem checked_instances_shaped_holds : checked_instances_shaped.
Proof. exact checked_shaped. Qed.

Definition erasure_observation_from_checked : Prop :=
  checked_signature_typed -> checked_instances_shaped -> erasure_observation.

Theorem erasure_observation_from_checked_holds : erasure_observation_from_checked.
Proof.
  intros Hty Hsh sg fsrc t T v w Hsg HO Hv Hw.
  exact (erasure_observation_core_holds sg fsrc t T v w (Hty _ Hsg) (Hsh _ Hsg) HO Hv Hw).
Qed.

(** So the observation follows from the type-correctness of checked
    signatures. *)
Definition erasure_observation_from_typed : Prop := checked_signature_typed -> erasure_observation.

Theorem erasure_observation_from_typed_holds : erasure_observation_from_typed.
Proof. intros Hty. exact (erasure_observation_from_checked_holds Hty checked_instances_shaped_holds). Qed.

(** And checked signatures are type-correct: the observation holds. *)
Theorem erasure_observation_holds : erasure_observation.
Proof. exact (erasure_observation_from_typed_holds checked_signature_typed_holds). Qed.

(** Behind [checked_declarative]: the kernel's soundness for the
    declarative rules assumes distinct constructor names, which every
    registration of a declaration checks (Checked/Shaped.v of
    elim-inductive-types), and a full
    table, which [predicative_prop] is. *)
Definition checked_constructors_distinct : Prop := forall sg, wf_checked sg -> ctors_distinct sg.

Theorem checked_constructors_distinct_holds : checked_constructors_distinct.
Proof. exact checked_ctors_distinct. Qed.

(** So a checked term is typed by the declarative rules once checked
    signatures are type-correct. *)
Definition checked_declarative_from_typed : Prop := checked_signature_typed -> checked_declarative.

Theorem checked_declarative_from_typed_holds : checked_declarative_from_typed.
Proof.
  intros Hty sg G t T Hsg HG HT H.
  exact (chk_sound predicative_prop sg (Hty _ Hsg) (fun _ => predicative_prop_full)
           (checked_ctors_distinct _ Hsg) G t T HG HT H).
Qed.

Theorem checked_declarative_holds : checked_declarative.
Proof. exact (checked_declarative_from_typed_holds checked_signature_typed_holds). Qed.

(** The decision of erasability agrees with the declarative rules in a
    type-correct signature (Erasure/EraseSound.v,
    [erasable_consistent]): the sort that [sort_of_e] finds structurally
    is the one every typing gives the type, a neutral spine by the type
    of its head, which every other type of the head is convertible to
    ([synth_unique]: a term that synthesizes [A] has only types
    convertible to [A]). *)
Theorem erasure_decision_consistent_holds : erasure_decision_consistent.
Proof.
  intros sg fuel G T Hsg HG HT H.
  pose proof (checked_signature_typed_holds _ Hsg) as Hty.
  apply (erasable_consistent sg fuel Hty G T); [ | exact H].
  destruct HT as [(s & -> & _) | (T' & s & HT & Hr)]; [left; exists s; reflexivity | right].
  destruct (synth_sound predicative_prop sg Hty (fun _ => predicative_prop_full) (checked_ctors_distinct _ Hsg)
              G T T' HG HT) as [_ HT'].
  exists s. exact (typed_red_srt predicative_prop sg Hty _ _ _ _ HT' Hr).
Qed.

(** What the function erases, the relation relates: [erase] is sound for
    the declarative typing of a type-correct signature with distinct
    constructor names and generated types of instances
    (Erasure/EraseSound.v, [erase_sound]), and a checked term is so
    typed ([checked_declarative_holds]).  Two choices of [erase] serve
    the proof: the indices of the scrutinee of a match are read off a
    type of it unfolded to its family, and an instance into Prop is
    erased to [□] outright, its type having the sort Prop. *)
Theorem erasure_sound_holds : erasure_sound.
Proof.
  intros sg fuel t T e Hsg HT Ht H.
  exact (erase_sound sg fuel (checked_signature_typed_holds _ Hsg) (checked_ctors_distinct _ Hsg)
           (checked_elim_types _ Hsg) t [] T e (checked_declarative_holds sg [] t T Hsg (BW_Nil _ _) HT Ht) H).
Qed.

(** ** The contract of erasure, proved

    Its three obligations hold: the soundness of [erase]
    ([erasure_sound_holds]), the simulation, a checked signature being
    related to its erasure ([erasure_simulation_holds]), and the
    observation ([erasure_observation_holds]); the decomposition
    ([erasure_decomposition_holds]) gives the contract. *)
Theorem erasure_preserves_observations_holds : erasure_preserves_observations.
Proof. exact (erasure_decomposition_holds erasure_sound_holds erasure_simulation_holds erasure_observation_holds). Qed.

(** Preservation does not hold for the annotated rules, so it is stated
    for the declarative ones.  A checked program,
    [((λf x. f x) ∷ ((Bool → Bool) → Bool → Bool)) ((λy. y) ∷ (Bool → Bool))],
    evaluates to [λx. (λy. y) x], which checks at no type: the
    annotations are dropped and a λ synthesizes nothing.  The
    declarative rules type it (Erasure/Preservation.v), and it is
    related to the value the erased program reaches. *)
Definition annotated_preservation_fails : Prop :=
  ~ (forall sg fuel t T v,
       wf_checked sg -> chk predicative_prop sg [] t T ->
       eval_src sg fuel t = CbvValue v -> chk predicative_prop sg [] v T).

Theorem annotated_preservation_fails_holds : annotated_preservation_fails.
Proof.
  intros H. exact (value_not_checked _ (H _ _ _ _ _ wf_checked_empty program_checked program_evaluates)).
Qed.

(** ** Beyond the contract (tier 3)

    Obligations that the contract does not need and does not give, each
    with the external result it corresponds to.  None is used by a proved
    theorem.  The references:
    - [Werner 1994]: B. Werner, Une théorie des constructions inductives,
      thèse, Université Paris 7, 1994 — strong normalization of CIC with
      eliminators;
    - [Giménez 1995]: E. Giménez, Codifying guarded definitions with
      recursive schemes, TYPES 1994, LNCS 996 — guarded [fix] translated
      into eliminators;
    - [Letouzey 2004]: P. Letouzey, Programmation fonctionnelle certifiée :
      l'extraction de programmes dans l'assistant Coq, thèse, Université
      Paris-Sud, 2004 — the correctness of extraction, and its semantic
      side for values beyond data;
    - [MetaCoq 2020]: M. Sozeau, S. Boulier, Y. Forster, N. Tabareau,
      T. Winterhalter, Coq Coq Correct! Verification of type checking and
      erasure for Coq, in Coq, POPL 2020 — erasure correct for weak
      call-by-value evaluation, normalization taken as an axiom; its
      presentation in Touring the MetaCoq Project, LFMTP 2021, §5;
    - [Forster, Sozeau, Tabareau 2024]: Verified extraction from Coq to
      OCaml, PLDI 2024 — erasure preserving first-order values of
      inductive types. *)

(** Normalization of CIC with the guard, for the evaluator by value: a
    closed checked program of a checked signature reaches a value with
    some budget.  With the progress of [eval_src] (an open obligation of
    the kernel) it rests on [Werner 1994] for the eliminators and on
    [Giménez 1995] for the guarded [fix]; [MetaCoq 2020] assumes it. *)
Definition cbv_normalization : Prop :=
  forall sg t T, wf_checked sg -> chk predicative_prop sg [] t T ->
  exists n v, eval_src sg n t = CbvValue v.

(** Erasure is total with enough fuel on checked terms of a checked
    signature: a separate obligation, not a premise of the contract.  It
    rests on the normalization of types, which [is_arity] and the sorts
    unfold, as the decision [isErasable] of [MetaCoq 2020] does.  The
    signature declares no family under the name of a primitive of the
    target: [erase_env] refuses such a declaration whatever its fuel
    ([XReserved]), and a checked signature may hold one ([raw_shadow] of
    Erasure/Examples.v declares [prim.Bool]).  No other entry of a
    checked signature is refused: its instances have active rules and
    sorts its categories allow. *)
Definition erasure_total : Prop :=
  forall sg t T, wf_checked sg -> (forall D, reserved_name D = true -> sig_ind sg D = None) ->
  btype predicative_prop sg [] T -> chk predicative_prop sg [] t T ->
  exists n, forall m, n <= m ->
    exists e se, erase_term predicative_prop sg m [] t T = Erased e /\ erase_env predicative_prop sg m = Erased se.

(** A wider class of observations: any value of the source without λ and
    [fix] — constructors of any declaration, pairs, the primitives, with
    types and proofs inside — is reached by the erased program exactly as
    its own erasure, not only for the observable types of the contract.
    The first-order values of [Forster, Sozeau, Tabareau 2024]; beyond
    them, functions need the semantic relation of [Letouzey 2004].
    Tested on the thirteen programs of the contract (extraction/regress.ml). *)
Fixpoint lambda_free (t : term) : bool :=
  match t with
  | Lam _ | Fix _ _ _ | Case _ _ _ _ _ => false
  | Pi a b | Sigma a b | App a b | Ann a b | Pair a b | ElimVoid a b => lambda_free a && lambda_free b
  | ElimUnit a b c => lambda_free a && lambda_free b && lambda_free c
  | ElimBool a b c d => lambda_free a && lambda_free b && lambda_free c && lambda_free d
  | Fst p | Snd p => lambda_free p
  | Srt _ | Var _ | Void | Unit | Tt | Bool | BTrue | BFalse | Const _ => true
  end.

Definition erasure_first_order : Prop :=
  forall sg t T fenv ferase fsrc se e v,
    wf_checked sg -> btype predicative_prop sg [] T -> chk predicative_prop sg [] t T ->
    erase_env predicative_prop sg fenv = Erased se ->
    erase_term predicative_prop sg ferase [] t T = Erased e ->
    eval_src sg fsrc t = CbvValue v -> lambda_free v = true ->
    exists fdst fv w, eval_erased se fdst e = CbvValue w /\ erase_term predicative_prop sg fv [] v T = Erased w.

(** ** The milestone of universes (stage 7)

    The checker of theories/Universes is separate from the kernel; its
    contracts are about levels, constraints and their graph.  Proved:
    the operations on levels and the normal form keep the value; the
    fragment of constraints decomposes exactly into edges, and a
    constraint with a max on the right is accepted only when entailed;
    the answers of the graph are certificates — a model, or a cycle of
    positive weight that no valuation satisfies, and for entailment a
    cycle with the negation or a counter-model; the context closed for
    a definition is satisfiable and implies the declared constraints and
    every requirement, and in a rigid declaration it is the declared one;
    cumulativity at sorts requires [ℓ₁ ≤ ℓ₂] and conversion [ℓ₁ = ℓ₂].

    Open: that the graph never answers [Unknown] (the completeness of
    Bellman–Ford with its certificates), and that an accepted
    polymorphic constant is accepted at every closed instance satisfying
    its context.  No declarative judgment with cumulativity is stated for
    this language; the relation of the checker to one is outside the
    milestone. *)

From Stdlib Require Import Bool Arith ZArith Lia.
From CIC.Universes Require Import Level Graph Constraints Term Check.

Definition level_operations : Prop :=
  forall v l l',
    leval v (lnorm l) = leval v l /\
    leval v (lsucc l) = S (leval v l) /\
    leval v (lmax l l') = Nat.max (leval v l) (leval v l').

Theorem level_operations_holds : level_operations.
Proof.
  intros v l l'. split; [apply lnorm_sound | split; [apply lsucc_sound | apply lmax_sound]].
Qed.

Definition constraint_fragment : Prop :=
  forall c,
    (forall es, decompose c = Some es -> forall v, models v es <-> csat v c) /\
    (forall G, implied G c = true -> forall v, models v G -> csat v c).

Theorem constraint_fragment_holds : constraint_fragment.
Proof. intros c. split; [exact (decompose_sound c) | intros G; exact (implied_sound G c)]. Qed.

Definition graph_verdicts : Prop :=
  forall G,
    (forall m, solve G = Consistent m -> models (val_of m) G) /\
    (forall c, solve G = Cycle c -> forall v, ~ models v G) /\
    (forall e c, entails G e = Entailed c -> forall v, models v G -> edge_sat v e) /\
    (forall e m, entails G e = Refuted m -> models (val_of m) G /\ ~ edge_sat (val_of m) e).

Theorem graph_verdicts_holds : graph_verdicts.
Proof.
  intros G. split; [exact (solve_consistent G) | split; [exact (solve_cycle G) | split]].
  - intros e c. exact (entails_entailed G e c).
  - intros e m. exact (entails_refuted G e m).
Qed.

Definition context_closure : Prop :=
  forall md C R ctx m, close_context md C R = Ok (ctx, m) ->
    Forall (csat (val_of m)) ctx /\
    (forall v, Forall (csat v) ctx -> Forall (csat v) C /\ Forall (csat v) R) /\
    (md = Rigid -> ctx = C).

Theorem context_closure_holds : context_closure.
Proof. intros md C R ctx m. exact (close_context_sound md C R ctx m). Qed.

(** Cumulativity at sorts is directed, conversion is not: the
    requirements collected make [ℓ₁ ≤ ℓ₂], respectively [ℓ₁ = ℓ₂], hold
    in every valuation satisfying them. *)
Definition cumulativity_sorts : Prop :=
  forall sg f l1 l2 cs cs',
    (cumul sg (S (S f)) (USort l1) (USort l2) cs = Ok (tt, cs') ->
       forall v, Forall (csat v) cs' -> leval v l1 <= leval v l2) /\
    (conv sg (S (S f)) (USort l1) (USort l2) cs = Ok (tt, cs') ->
       forall v, Forall (csat v) cs' -> leval v l1 = leval v l2).

Lemma req_le_sound : forall l1 l2 cs cs', req_le l1 l2 cs = Ok (tt, cs') ->
  forall v, Forall (csat v) cs' -> leval v l1 <= leval v l2.
Proof.
  intros l1 l2 cs cs' H v Hv. unfold req_le in H. destruct (lle_syn l1 l2) eqn:E.
  - exact (lle_syn_sound v l1 l2 E).
  - unfold emit in H. injection H as <-. apply Forall_app in Hv as [_ Hc].
    inversion Hc as [|? ? Hs _]; subst. unfold csat in Hs; cbn [c_lhs c_off c_rhs cle] in Hs. lia.
Qed.

Lemma req_eq_sound : forall l1 l2 cs cs', req_eq l1 l2 cs = Ok (tt, cs') ->
  forall v, Forall (csat v) cs' -> leval v l1 = leval v l2.
Proof.
  intros l1 l2 cs cs' H v Hv. unfold req_eq in H. destruct (lsame l1 l2) eqn:E.
  - unfold lsame in E. apply andb_prop in E as [E1 E2].
    pose proof (lle_syn_sound v _ _ E1). pose proof (lle_syn_sound v _ _ E2). lia.
  - unfold mbind, emit in H. injection H as <-.
    apply Forall_app in Hv as [Hv H2]. apply Forall_app in Hv as [_ H1].
    inversion H1 as [|? ? Hs1 _]; inversion H2 as [|? ? Hs2 _]; subst.
    unfold csat in Hs1, Hs2; cbn [c_lhs c_off c_rhs cle] in Hs1, Hs2. lia.
Qed.

Theorem cumulativity_sorts_holds : cumulativity_sorts.
Proof.
  intros sg f l1 l2 cs cs'. split; intros H.
  - change (req_le l1 l2 cs = Ok (tt, cs')) in H. exact (req_le_sound _ _ _ _ H).
  - change (req_eq l1 l2 cs = Ok (tt, cs')) in H. exact (req_eq_sound _ _ _ _ H).
Qed.

(** *** Open *)

(** Bellman–Ford with [|V|] rounds always finds a model or a cycle whose
    certificate checks. *)
Definition graph_solve_complete : Prop := forall G, solve G <> Unknown.

(** Polymorphism means every instance: an accepted constant, at closed
    levels given by a valuation satisfying its context, is accepted in
    the empty rigid context, for some budget. *)
Definition instances_accepted : Prop :=
  forall cumulative sg fuel dc d m,
    check_decl cumulative sg fuel dc = Ok (d, m) ->
    forall v, Forall (csat v) (ud_cstrs d) ->
    exists fuel' r, check_term cumulative sg fuel' [] [] Rigid
                      (ulsubst (closed_map v d) (ud_body d)) (ulsubst (closed_map v d) (ud_type d)) = Ok r.
