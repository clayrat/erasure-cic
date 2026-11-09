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
    entry.

    The three tiers of readiness of the plan:
    - tier 1, reached: the executable kernel with fuel, extracted
      (extraction/), with regression tests and the native references
      compared with the extract (reference/); the acceptance of [Case],
      [Fix] and the guard proved sound for the subterm relation
      (PTS/Contracts.v of the kernel); [eval_src], [eval_erased], erasure
      and the erasure of signatures implemented and checked on examples;
    - tier 2, not reached: the contract of erasure proved, with its
      obligations below.  Its proof needs subject reduction for CIC with
      [match] and [fix] ([source_preservation]), hence confluence and the
      injectivity of Π, open in the kernel, before the simulation itself.
      The pairing of the equations and closed results of [fix]/[match]
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
From DepTypes.PTS Require Import Syntax Spec Signature Reduction EvalSrc Typing Bidir Check.
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
    unfold, as the decision [isErasable] of [MetaCoq 2020] does. *)
Definition erasure_total : Prop :=
  forall sg t T, wf_checked sg -> btype predicative_prop sg [] T -> chk predicative_prop sg [] t T ->
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

(** The link with declarative typing: a program the kernel checked in a
    checked signature is typed by the declarative rules of PTS/Typing.v,
    against which [MetaCoq 2020] states erasure.  It follows from
    [bidir_declarative_sound] of the kernel, open, once a checked
    signature is shown type-correct ([signature_typed]). *)
Definition checked_declarative : Prop :=
  forall sg t T, wf_checked sg -> chk predicative_prop sg [] t T -> has_type predicative_prop sg [] t T.

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
