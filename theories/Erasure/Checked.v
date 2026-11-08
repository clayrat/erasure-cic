(** * Checked signatures

    [wf_checked Σ]: the signature is built from the empty one by checked
    steps, each a registration of lectures 7 and 8 through the kernel's
    checker:
    - a declaration by algorithm 1 with strict positivity and the checked
      category of elimination ([declare_checked]), with its instances;
    - a δ-constant whose body checks against its type and passes the
      guard of every [fix] ([define_checked]);
    - functions compiled by algorithm 2 ([compile_all]).
    The modes [Bypass] of positivity and [BypassElim] are not steps, nor
    is any assumption: every constant has a body or active ι-rules.  The
    steps check in the predicative hierarchy, with or without Prop.

    The record of a signature carries a proof of closedness; the
    functions of the kernel and of erasure read only its entries, so
    [wf_checked] holds of every signature with the entries of a checked
    one.  [run_steps] replays a list of steps, and [steps_checked] turns
    a successful replay into [wf_checked]. *)

From Stdlib Require Import String List.
Import ListNotations.
From DepTypes.PTS Require Import Syntax Spec Signature.
From DepTypes.Configs Require Import Predicative.
From IndTypes Require Import Registration.
From IndTypes.Elim Require Import Decl Declare.
From IndTypes.Recursion Require Import CaseTree Compile.

Inductive step : Type :=
| StDeclare : spec -> nat -> raw_decl -> list sort -> step
| StDefine : spec -> nat -> String.string -> term -> term -> step
| StCompile : spec -> nat -> list fun_decl -> step.

Definition step_spec (st : step) : spec :=
  match st with
  | StDeclare Sp _ _ _ | StDefine Sp _ _ _ _ | StCompile Sp _ _ => Sp
  end.

Definition run_step (sg : signature) (st : step) : option signature :=
  match st with
  | StDeclare Sp fuel raw sorts => registered (declare_checked Sp fuel sg raw sorts)
  | StDefine Sp fuel f A b => registered (define_checked Sp fuel sg f A b)
  | StCompile Sp fuel fns => registered (compile_all Sp fuel sg fns)
  end.

Inductive checking_spec : spec -> Prop :=
| CS_Predicative : checking_spec predicative
| CS_Prop : checking_spec predicative_prop.

Inductive wf_checked : signature -> Prop :=
| WF_Empty : forall sg, sig_entries sg = [] -> wf_checked sg
| WF_Step : forall sg st sg' sg'',
    wf_checked sg -> checking_spec (step_spec st) -> run_step sg st = Some sg' ->
    sig_entries sg'' = sig_entries sg' -> wf_checked sg''.

Lemma wf_checked_entries : forall sg sg', wf_checked sg -> sig_entries sg' = sig_entries sg -> wf_checked sg'.
Proof.
  intros sg sg' H E. inversion H; subst.
  - apply WF_Empty. congruence.
  - eapply WF_Step; [eassumption | eassumption | eassumption | congruence].
Qed.

Fixpoint run_steps (sg : signature) (sts : list step) : option signature :=
  match sts with
  | [] => Some sg
  | st :: sts' => match run_step sg st with Some sg' => run_steps sg' sts' | None => None end
  end.

Theorem steps_checked : forall sts sg sg', wf_checked sg ->
  Forall (fun st => checking_spec (step_spec st)) sts -> run_steps sg sts = Some sg' -> wf_checked sg'.
Proof.
  induction sts as [|st sts IH]; intros sg sg' Hsg Hs H; cbn in H.
  - injection H as <-. exact Hsg.
  - inversion Hs as [|? ? Hst Hsts]; subst.
    destruct (run_step sg st) as [sg1|] eqn:E; [ | discriminate H].
    apply (IH sg1); [eapply WF_Step; [exact Hsg | exact Hst | exact E | reflexivity] | exact Hsts | exact H].
Qed.

Lemma wf_checked_empty : wf_checked ∅.
Proof. apply WF_Empty. reflexivity. Qed.
