(** * Erasure with known types

    [erase S sg fuel strict Γ t T] erases a checked term [t] of known type
    [T] in the context [Γ].  At every subterm it decides first whether the
    term is erasable, after the criterion of [isErasable] of MetaCoq:
    - [T] unfolds to an arity, a sort or a Π whose codomain is an arity:
      [t] is a type or a family of types, such as a motive
      [P : ℕ → Type_j] or the parameter [B : A → Type₀] of W;
    - or the sort of [T] is Prop: [t] is a proof.
    Then [t] becomes [□].  Otherwise the walk goes on by the shape of [t],
    passing known types down as checking does:
    - a λ unfolds [T] to a Π and erases its body at the codomain; a pair
      unfolds [T] to a Σ;
    - an application infers the type of its function and erases the
      argument at the domain; the types of all the prefixes of a spine
      come from one run of the kernel ([infer_spine_e]), its head
      inferred once and each argument checked once, so that a spine of
      n arguments does not cost n inferences ([erase_spine]); an
      annotation gives its term a known type and disappears;
    - a [match] on data stays a match, without its motive, each branch
      erased at the type of the branch of stage 3.  On a proposition, the
      result being in Type, the declaration must be a singleton or empty
      by its sort and category: the single branch, erased, is applied to
      [□] for each field; the empty match stays a match without branches,
      stuck if run;
    - a [fix] keeps its body, erased at its type in the context with the
      function, and drops its type;
    - the eliminators of Unit, Bool and Void become matches on the
      primitives of the target, their constructors constructors of it;
    - an instance into Prop is a proof and becomes [□] even when the
      decision above missed it: its type has the sort Prop, but the
      sort of a type convertible to it is not known to be Prop, the
      uniqueness of the sorts of types up to conversion being unproved;
    - the other constants stay constants.
    The function never infers the type of a λ or of a pair: it only asks
    the types of what synthesizes.

    Running out of fuel while recognizing an arity, finding a sort,
    unfolding a type or inferring one gives [UndecidedAt] with that stage,
    not a guess.  A rejection by the kernel on the way means that the
    input was not a checked term.  The fuel of erasure is its own: the
    fuel that checked the term may not suffice.

    [erase_env] erases a signature, oldest entry first: a declaration
    keeps its parameters, indices, constructors with the shape of their
    fields, and its kind of elimination; an instance its kind; a
    δ-constant its body erased at its type.  An instance without active
    rules is an assumption without computation and is refused.  The
    primitives of the target lie below the erased entries and are looked
    up by name, so a declaration under the name of one of them would
    shadow it: it is refused ([XReserved]).

    [strict] is [true] for erasure proper.  With [false] it is the
    demonstration of BypassElim (stage 2): an elimination of a proposition
    into Type that its category forbids is kept as a match, or an
    instance, on data, and gets stuck on [□]. *)

From Stdlib Require Import String List Bool Arith Relations.
Import ListNotations.
From DepTypes.Common Require Import Result Traced.
From DepTypes.PTS Require Import Syntax Spec Signature Reduction NormalOrder Eval Bidir Check CheckSound.
From CIC.Erasure Require Import Target.

Inductive erase_stage : Type :=
| AtArity : erase_stage     (** recognizing an arity *)
| AtSort : erase_stage      (** the sort of a type *)
| AtUnfold : erase_stage    (** unfolding a type to a Π, a Σ or a family *)
| AtType : erase_stage.     (** inferring the type of a subterm *)

Inductive erase_error : Type :=
| XIllTyped : term -> error -> erase_error        (** the kernel rejects a subterm *)
| XNotAType : term -> term -> erase_error         (** a type and its type, not a sort *)
| XShape : term -> term -> erase_error            (** a term and its type, of another shape *)
| XIllegalElim : String.string -> sort -> erase_error   (** an elimination its category forbids *)
| XUnsupported : term -> erase_error              (** a term erasure does not expect *)
| XInactive : String.string -> sort -> erase_error      (** an instance without its rules *)
| XReserved : String.string -> erase_error.             (** a declaration under the name of a primitive *)

Inductive erase_failure : Type :=
| Fail : erase_error -> erase_failure
| Short : erase_stage -> term -> erase_failure.

Inductive erase_result (A : Type) : Type :=
| Erased : A -> erase_result A
| NotErasable : erase_error -> erase_result A
| UndecidedAt : erase_stage -> term -> erase_result A.

Arguments Erased {A} _.
Arguments NotErasable {A} _.
Arguments UndecidedAt {A} _ _.

Definition to_erase_result {A} (r : result erase_failure A) : erase_result A :=
  match r with
  | Ok a => Erased a
  | Err (Fail e) => NotErasable e
  | Err (Short st t) => UndecidedAt st t
  end.

(** ** The kind of a declaration *)

Definition kind_of (d : ind_desc) : elim_kind :=
  if sort_eqb (ind_sort d) Prp then
    match ind_elim d, ind_ctors d with
    | AllSorts, [] => KEmpty
    | AllSorts, [_] => KSingleton
    | _, _ => KProp
    end
  else KData.

Definition efield_of (fd : field) : efield :=
  match fd with
  | FArg _ => ENonRec
  | FRec Bs _ => ERec (length Bs)
  end.

Definition erase_ind (d : ind_desc) : eind :=
  mk_eind (ind_name d) (length (ind_params d)) (length (ind_indices d))
    (map (fun c => mk_ector (ctor_name c) (map efield_of (ctor_fields c))) (ind_ctors d))
    (kind_of d).

(** The names of the primitive families of the target, reserved. *)
Definition reserved_name (D : String.string) : bool :=
  String.eqb D prim_unit || String.eqb D prim_bool || String.eqb D prim_void.

Section Erase.
  Variable Sp : spec.
  Variable sg : signature.
  Variable fuel : nat.
  Variable strict : bool.

  Local Notation E A := (result erase_failure A).

  Definition infer_e (G : ctx) (t : term) : E term :=
    match run_result (infer Sp sg fuel G t) with
    | Ok A => Ok A
    | Err (Reject e) => Err (Fail (XIllTyped t e))
    | Err (NoFuel u) => Err (Short AtType u)
    end.

  (** The types of an application and of its prefixes, outermost first,
      with the answer of [infer_e] on it ([infer_spine] of PTS.Check). *)
  Definition infer_spine_e (G : ctx) (t : term) : E (list term) :=
    match run_result (infer_spine Sp sg fuel G t) with
    | Ok As => Ok As
    | Err (Reject e) => Err (Fail (XIllTyped t e))
    | Err (NoFuel u) => Err (Short AtType u)
    end.

  Definition whnf_e (st : erase_stage) (T : term) : E term :=
    match whnf sg fuel T with
    | HeadForm V => Ok V
    | HeadOutOfFuel u => Err (Short st u)
    end.

  (** [T] unfolds to a sort, or to a Π whose codomain is an arity. *)
  Fixpoint is_arity (n : nat) (T : term) : E bool :=
    match n with
    | O => Err (Short AtArity T)
    | S n' =>
        let* V := whnf_e AtArity T in
        match V with
        | Srt _ => Ok true
        | Pi _ B => is_arity n' B
        | _ => Ok false
        end
    end.

  (** ** The sort of a type

      Types left by substitution need not synthesize: [(λ_. ℕ) n], or a
      family [λ_. Type₀] of [elimBool] once normalization dropped its
      annotation.  The sort of a type is found from its weak-head form,
      without inferring its subterms: a sort by its axiom, Π and Σ by the
      rules of the table, a family of the signature by the sort of its
      description, a neutral spine by the type of its head applied to
      its arguments, a match by its motive.  For a match the type of the
      scrutinee must unfold to its family applied to parameters and
      indices, as for erasing a match ([params_e]): the indices are read
      off this form. *)

  Definition head_type (G : ctx) (h : term) : E term :=
    match h with
    | Var n =>
        match lookup G n with
        | Some A => Ok A
        | None => Err (Fail (XIllTyped h (EUnboundVar n)))
        end
    | Const g =>
        match sig_type sg g with
        | Some A => Ok A
        | None => Err (Fail (XIllTyped h (EUnknownConst g)))
        end
    | Fix A _ _ => Ok A
    | _ => infer_e G h
    end.

  (** [H] applied to [args]: its Π peeled, each codomain instantiated. *)
  Fixpoint instantiate (H : term) (args : list term) : E term :=
    match args with
    | [] => Ok H
    | a :: args' =>
        let* V := whnf_e AtSort H in
        match V with
        | Pi _ B => instantiate (subst1 B a) args'
        | _ => Err (Fail (XShape a V))
        end
    end.

  Definition sort_at (T K : term) : E sort :=
    let* V := whnf_e AtSort K in
    match V with
    | Srt s => Ok s
    | _ => Err (Fail (XNotAType T V))
    end.

  Fixpoint sort_of_e (n : nat) (G : ctx) (T : term) : E sort :=
    match n with
    | O => Err (Short AtSort T)
    | S n' =>
        let* V := whnf_e AtSort T in
        let bad := Err (Fail (XNotAType T V)) in
        match V with
        | Srt s => match spec_axiom Sp s with Some s' => Ok s' | None => bad end
        | Pi A B =>
            let* s1 := sort_of_e n' G A in
            let* s2 := sort_of_e n' (A :: G) B in
            match spec_rule Sp s1 s2 with Some s3 => Ok s3 | None => bad end
        | Sigma A B =>
            let* s1 := sort_of_e n' G A in
            let* s2 := sort_of_e n' (A :: G) B in
            match spec_sigma Sp s1 s2 with Some s3 => Ok s3 | None => bad end
        | Void | Unit | Bool => match spec_prim Sp with Some s0 => Ok s0 | None => bad end
        | _ =>
            match spine_head V with
            | Const (Ind D) =>
                match sig_ind sg D with Some d => Ok (ind_sort d) | None => bad end
            | Case D _ P x _ =>
                match sig_ind sg D with
                | Some d =>
                    let* X := infer_e G x in
                    let* XV := whnf_e AtSort X in
                    let p := length (ind_params d) in
                    let xs := spine_args XV in
                    if term_eqb (spine_head XV) (Const (Ind D)) &&
                       Nat.eqb (length xs) (p + length (ind_indices d)) then
                      let* K := instantiate (apps P (skipn p xs ++ [x])) (spine_args V) in
                      sort_at T K
                    else Err (Fail (XShape x XV))
                | None => bad
                end
            | h =>
                let* H := head_type G h in
                let* K := instantiate H (spine_args V) in
                sort_at T K
            end
        end
    end.

  (** A term of type [T] is a type or a proof. *)
  Definition erasable (G : ctx) (T : term) : E bool :=
    let* a := is_arity fuel T in
    if a then Ok true else
    let* s := sort_of_e fuel G T in
    Ok (sort_eqb s Prp).

  Definition as_pi_e (t T : term) : E (term * term) :=
    let* V := whnf_e AtUnfold T in
    match V with
    | Pi A B => Ok (A, B)
    | _ => Err (Fail (XShape t V))
    end.

  Definition as_sigma_e (t T : term) : E (term * term) :=
    let* V := whnf_e AtUnfold T in
    match V with
    | Sigma A B => Ok (A, B)
    | _ => Err (Fail (XShape t V))
    end.

  (** The type of a scrutinee, unfolded to [D ps us]: the parameters. *)
  Definition params_e (x X : term) (D : String.string) (d : ind_desc) : E (list term) :=
    let* V := whnf_e AtUnfold X in
    let p := length (ind_params d) in
    let args := spine_args V in
    if term_eqb (spine_head V) (Const (Ind D)) && Nat.eqb (length args) (p + length (ind_indices d))
    then Ok (firstn p args)
    else Err (Fail (XShape x V)).

  (** An application [f] at [F], the types [Fs] of its prefixes known
      ([infer_spine_e]): what [erase] does on it, by [er], without
      inferring the type of each prefix again.  For a spine of n
      arguments the head is inferred once, not n times. *)
  Fixpoint erase_spine (er : ctx -> term -> term -> E eterm) (G : ctx) (f F : term) (Fs : list term)
    {struct f} : E eterm :=
    match f with
    | App f1 a1 =>
        let* b := erasable G F in
        if b then Ok EBox else
        match Fs with
        | F1 :: Fs1 =>
            let* p := as_pi_e f1 F1 in
            let* f1' := erase_spine er G f1 F1 Fs1 in
            let* a1' := er G a1 (fst p) in
            Ok (EApp f1' a1')
        | [] => Err (Fail (XUnsupported f))
        end
    | _ => er G f F
    end.

  (** The branches, one per constructor. *)
  Fixpoint erase_each (t : term) (f : ctor_desc -> term -> E eterm) (cs : list ctor_desc) (bs : list term)
    {struct bs} : E (list eterm) :=
    match cs, bs with
    | c :: cs', b :: bs' => let* b' := f c b in let* r := erase_each t f cs' bs' in Ok (b' :: r)
    | [], [] => Ok []
    | _, _ => Err (Fail (XUnsupported t))
    end.

  Fixpoint erase (G : ctx) (t : term) (T : term) {struct t} : E eterm :=
    let* er := erasable G T in
    if er then Ok EBox else
    match t with
    | Var n => Ok (EVar n)
    | Lam b =>
        let* p := as_pi_e t T in
        let* b' := erase (fst p :: G) b (snd p) in
        Ok (ELam b')
    | App f a =>
        let* Fs := infer_spine_e G f in
        match Fs with
        | F :: Fs' =>
            let* p := as_pi_e f F in
            let* f' := erase_spine erase G f F Fs' in
            let* a' := erase G a (fst p) in
            Ok (EApp f' a')
        | [] => Err (Fail (XUnsupported t))
        end
    | Ann u A => erase G u A
    | Const (Def f) => Ok (EConst f)
    | Const (Ctor D c) => Ok (ECtor D c)
    | Const (Elim D s) => if sort_eqb s Prp then Ok EBox else Ok (EPrim D s)
    | Tt => Ok (ECtor prim_unit "tt")
    | BTrue => Ok (ECtor prim_bool "true")
    | BFalse => Ok (ECtor prim_bool "false")
    | ElimUnit C c u =>
        let* c' := erase G c (App C Tt) in
        let* u' := erase G u Unit in
        Ok (ECase prim_unit u' [c'])
    | ElimBool C x y b =>
        let* x' := erase G x (App C BTrue) in
        let* y' := erase G y (App C BFalse) in
        let* b' := erase G b Bool in
        Ok (ECase prim_bool b' [x'; y'])
    | ElimVoid C e =>
        let* e' := erase G e Void in
        Ok (ECase prim_void e' [])
    | Pair a b =>
        let* p := as_sigma_e t T in
        let* a' := erase G a (fst p) in
        let* b' := erase G b (subst1 (snd p) a) in
        Ok (EPair a' b')
    | Fst q =>
        let* Q := infer_e G q in
        let* _ := as_sigma_e q Q in
        let* q' := erase G q Q in
        Ok (EFst q')
    | Snd q =>
        let* Q := infer_e G q in
        let* _ := as_sigma_e q Q in
        let* q' := erase G q Q in
        Ok (ESnd q')
    | Case D s P x bs =>
        match sig_ind sg D with
        | None => Err (Fail (XUnsupported t))
        | Some d =>
            let* X := infer_e G x in
            let* ps := params_e x X D d in
            let* x' := erase G x X in
            let* bs' := erase_each t (fun c b => erase G b (case_branch_type d ps P c)) (ind_ctors d) bs in
            if sort_eqb (ind_sort d) Prp then
              match ind_elim d, ind_ctors d, bs' with
              | AllSorts, [], [] => Ok (ECase D x' [])
              | AllSorts, [c], [b'] => Ok (eapps b' (repeat EBox (length (ctor_fields c))))
              | _, _, _ => if strict then Err (Fail (XIllegalElim D s)) else Ok (ECase D x' bs')
              end
            else Ok (ECase D x' bs')
        end
    | Fix A k b =>
        let* b' := erase (A :: G) b (lift 1 A) in
        Ok (EFix k b')
    | Srt _ | Pi _ _ | Sigma _ _ | Void | Unit | Bool | Const (Ind _) => Err (Fail (XUnsupported t))
    end.

  (** ** The signature *)

  Definition erase_entry (e : entry) : E eentry :=
    match e with
    | EInd d => if reserved_name (ind_name d) then Err (Fail (XReserved (ind_name d))) else Ok (EEInd (erase_ind d))
    | EElim D s _ act =>
        if negb act then Err (Fail (XInactive D s)) else
        match sig_ind sg D with
        | None => Err (Fail (XUnsupported (Const (Elim D s))))
        | Some d =>
            if sort_eqb s Prp then Ok (EEElim D s KProp)
            else match kind_of d with
                 | KProp => if strict then Err (Fail (XIllegalElim D s)) else Ok (EEElim D s KData)
                 | k => Ok (EEElim D s k)
                 end
        end
    | EDef f A b => let* b' := erase [] b A in Ok (EEDef f b')
    end.

  Fixpoint erase_entries (es : list entry) : E esignature :=
    match es with
    | [] => Ok prim_entries
    | e :: es' => let* se := erase_entries es' in let* e' := erase_entry e in Ok (e' :: se)
    end.

  Definition erase_env_e : E esignature := erase_entries (sig_entries sg).

  (** ** The decision of erasability

      [□] is chosen for a term whose type unfolds to an arity, or whose
      type has the sort Prop by [sort_of_e].  That this sort is the one
      the declarative rules give the type is proved in
      Erasure/EraseSound.v ([erasure_decision_consistent_holds] of
      Contracts.v), and so is the soundness of [erase] for the relation
      of erasure ([erasure_sound_holds]). *)

  Inductive arity : term -> Prop :=
  | Ar_Sort : forall T s, red sg T (Srt s) -> arity T
  | Ar_Pi : forall T A B, red sg T (Pi A B) -> arity B -> arity T.

  Lemma whnf_e_red : forall st T V, whnf_e st T = Ok V -> red sg T V.
  Proof.
    intros st T V H. unfold whnf_e in H.
    destruct (whnf sg fuel T) as [V' | ] eqn:W; [ | discriminate H]. injection H as <-.
    exact (nsteps_red T V' (whnf_reduces fuel T V' W)).
  Qed.

  Lemma infer_e_sound : forall G t A, infer_e G t = Ok A -> synth Sp sg G t A.
  Proof.
    intros G t A H. unfold infer_e in H.
    destruct (run_result (infer Sp sg fuel G t)) as [A' | [e | u]] eqn:E; try discriminate H.
    injection H as <-. apply run_result_ok in E as [log E]. exact (infer_sound Sp sg fuel G t [] log A' E).
  Qed.

  Lemma infer_spine_e_ok : forall G t As, infer_spine_e G t = Ok As -> run_result (infer_spine Sp sg fuel G t) = Ok As.
  Proof.
    intros G t As H. unfold infer_spine_e in H.
    destruct (run_result (infer_spine Sp sg fuel G t)) as [As' | [e | u]]; try discriminate H. congruence.
  Qed.

  Lemma infer_spine_e_sound : forall G t A As, infer_spine_e G t = Ok (A :: As) -> synth Sp sg G t A.
  Proof.
    intros G t A As H. apply infer_spine_e_ok, run_result_ok in H as [log H].
    exact (infer_spine_sound Sp sg fuel t G [] log A As H).
  Qed.

  (** The types of the prefixes of [App f u] are those of [f] after its
      own. *)
  Lemma infer_spine_e_app : forall G f u F Fs, infer_spine_e G (App f u) = Ok (F :: Fs) -> infer_spine_e G f = Ok Fs.
  Proof.
    intros G f u F Fs H. apply infer_spine_e_ok, run_result_ok in H as [log H]. cbn [infer_spine] in H.
    tbind_in H Fs0 HFs0. destruct Fs0 as [|F0 Fs0]; [apply tret_ok in H; discriminate H | ].
    tbind_in H p Hp. destruct p as [A B]. tbind_in H v Hv. apply tret_ok in H. injection H as _ ->.
    unfold infer_spine_e, run_result. rewrite HFs0. reflexivity.
  Qed.

  (** [erase_spine] is [erase] on an application whose prefixes have the
      types [infer_spine_e] gives. *)
  Lemma erase_spine_erase : forall G f F Fs, infer_spine_e G f = Ok (F :: Fs) ->
    erase_spine erase G f F Fs = erase G f F.
  Proof.
    intros G f F Fs H. destruct f; try reflexivity.
    apply infer_spine_e_app in H. cbn [erase_spine erase]. rewrite H. reflexivity.
  Qed.

  Lemma is_arity_sound : forall n T, is_arity n T = Ok true -> arity T.
  Proof.
    induction n as [|n IH]; intros T H; cbn [is_arity] in H; [discriminate H | ].
    apply bind_ok in H as (V & HV & H). apply whnf_e_red in HV.
    destruct V; try discriminate H.
    - exact (Ar_Sort _ _ HV).
    - exact (Ar_Pi _ _ _ HV (IH _ H)).
  Qed.

  Theorem erasable_spec : forall G T, erasable G T = Ok true ->
    arity T \/ sort_of_e fuel G T = Ok Prp.
  Proof.
    intros G T H. unfold erasable in H. apply bind_ok in H as (a & Ha & H).
    destruct a; [left; exact (is_arity_sound _ _ Ha) | right].
    apply bind_ok in H as (s & Hs & H). injection H as E. apply sort_eqb_eq in E. subst s. exact Hs.
  Qed.
  (** ** The erased signature is the erasure of each entry

      A δ-constant is found with its body erased at its type; a
      declaration with its erased description. *)

  Lemma erase_entry_def : forall e e', erase_entry e = Ok e' ->
    forall f b', e' = EEDef f b' -> exists A b, e = EDef f A b /\ erase [] b A = Ok b'.
  Proof.
    intros e e' H f b' ->. destruct e as [d | D s T act | g A b]; cbn [erase_entry] in H.
    - destruct (reserved_name _); discriminate H.
    - destruct (negb act); [discriminate H | ].
      destruct (sig_ind sg D); [ | discriminate H].
      destruct (sort_eqb s Prp); [discriminate H | ].
      destruct (kind_of _); try discriminate H. destruct strict; discriminate H.
    - apply bind_ok in H as (b'' & Hb & H). injection H as <- <-. eauto.
  Qed.

  Lemma erase_entry_ind : forall e e', erase_entry e = Ok e' ->
    forall d', e' = EEInd d' -> exists d, e = EInd d /\ d' = erase_ind d /\ reserved_name (ind_name d) = false.
  Proof.
    intros e e' H d' ->. destruct e as [d | D s T act | g A b]; cbn [erase_entry] in H.
    - destruct (reserved_name (ind_name d)) eqn:Er; [discriminate H | ]. injection H as <-. eauto.
    - destruct (negb act); [discriminate H | ].
      destruct (sig_ind sg D); [ | discriminate H].
      destruct (sort_eqb s Prp); [discriminate H | ].
      destruct (kind_of _); try discriminate H. destruct strict; discriminate H.
    - apply bind_ok in H as (b'' & Hb & H). discriminate H.
  Qed.

  Theorem erase_entries_defs : forall es se, erase_entries es = Ok se ->
    forall f A b, find_def es f = Some (A, b) -> exists b', erase [] b A = Ok b' /\ efind_def se f = Some b'.
  Proof.
    induction es as [|e es IH]; intros se H f A b Hf; [discriminate Hf | ].
    cbn [erase_entries] in H. apply bind_ok in H as (se' & Hse' & H).
    apply bind_ok in H as (e' & He' & H). injection H as <-.
    destruct e' as [d' | D' s' k' | g b''] eqn:Ee'.
    - destruct (erase_entry_ind _ _ He' _ eq_refl) as (d & -> & _ & _). cbn in Hf |- *. exact (IH _ Hse' _ _ _ Hf).
    - destruct e as [d | D s T act | g A' b']; cbn [find_def] in Hf.
      + cbn in He'. destruct (reserved_name _); discriminate He'.
      + cbn. exact (IH _ Hse' _ _ _ Hf).
      + cbn in He'. apply bind_ok in He' as (x & _ & He'). discriminate He'.
    - destruct (erase_entry_def _ _ He' _ _ eq_refl) as (A' & b' & -> & Hb). cbn [find_def efind_def] in Hf |- *.
      destruct (String.eqb g f); [injection Hf as <- <-; eauto | exact (IH _ Hse' _ _ _ Hf)].
  Qed.

  Theorem erase_entries_inds : forall es se, erase_entries es = Ok se ->
    forall D d, find_ind es D = Some d -> efind_ind se D = Some (erase_ind d).
  Proof.
    induction es as [|e es IH]; intros se H D d Hd; [discriminate Hd | ].
    cbn [erase_entries] in H. apply bind_ok in H as (se' & Hse' & H).
    apply bind_ok in H as (e' & He' & H). injection H as <-.
    destruct e' as [d' | D' s' k' | g b''] eqn:Ee'.
    - destruct (erase_entry_ind _ _ He' _ eq_refl) as (d0 & -> & -> & _). cbn [find_ind efind_ind] in Hd |- *.
      unfold erase_ind at 1. cbn [eind_name].
      destruct (String.eqb (ind_name d0) D); [injection Hd as <-; reflexivity | exact (IH _ Hse' _ _ Hd)].
    - destruct e as [d0 | D0 s T act | g A' b']; cbn [find_ind] in Hd.
      + cbn in He'. destruct (reserved_name _); discriminate He'.
      + cbn. exact (IH _ Hse' _ _ Hd).
      + cbn in He'. apply bind_ok in He' as (x & _ & He'). discriminate He'.
    - destruct (erase_entry_def _ _ He' _ _ eq_refl) as (A' & b' & -> & Hb). cbn [find_ind efind_ind] in Hd |- *.
      exact (IH _ Hse' _ _ Hd).
  Qed.

  (** No declaration shadows a primitive: the primitives are found in the
      erased signature as in [prim_entries]. *)
  Theorem erase_entries_prims : forall es se, erase_entries es = Ok se ->
    forall D, reserved_name D = true -> efind_ind se D = efind_ind prim_entries D.
  Proof.
    induction es as [|e es IH]; intros se H D HD.
    - cbn [erase_entries] in H. injection H as <-. reflexivity.
    - cbn [erase_entries] in H. apply bind_ok in H as (se' & Hse' & H).
      apply bind_ok in H as (e' & He' & H). injection H as <-.
      destruct e' as [d' | D' s' k' | g b''].
      + destruct (erase_entry_ind _ _ He' _ eq_refl) as (d0 & -> & -> & Hr).
        unfold erase_ind. cbn [efind_ind eind_name].
        destruct (String.eqb (ind_name d0) D) eqn:E.
        * apply String.eqb_eq in E. subst D. rewrite Hr in HD. discriminate HD.
        * exact (IH _ Hse' _ HD).
      + cbn [efind_ind]. exact (IH _ Hse' _ HD).
      + cbn [efind_ind]. exact (IH _ Hse' _ HD).
  Qed.
End Erase.

(** ** Entry points *)

Definition erase_term (S : spec) (sg : signature) (fuel : nat) (G : ctx) (t T : term) : erase_result eterm :=
  to_erase_result (erase S sg fuel true G t T).

Definition erase_env (S : spec) (sg : signature) (fuel : nat) : erase_result esignature :=
  to_erase_result (erase_env_e S sg fuel true).

Corollary erase_env_prims : forall S sg fuel se, erase_env S sg fuel = Erased se ->
  forall D, reserved_name D = true -> efind_ind se D = efind_ind prim_entries D.
Proof.
  intros S sg fuel se H D HD. unfold erase_env, to_erase_result in H.
  destruct (erase_env_e S sg fuel true) as [se' | [e | st t]] eqn:E; try discriminate H.
  injection H as ->. exact (erase_entries_prims S sg fuel true _ _ E D HD).
Qed.

(** The demonstration of BypassElim, outside the contract. *)
Definition erase_term_bypassing (S : spec) (sg : signature) (fuel : nat) (G : ctx) (t T : term)
  : erase_result eterm :=
  to_erase_result (erase S sg fuel false G t T).

Definition erase_env_bypassing (S : spec) (sg : signature) (fuel : nat) : erase_result esignature :=
  to_erase_result (erase_env_e S sg fuel false).
