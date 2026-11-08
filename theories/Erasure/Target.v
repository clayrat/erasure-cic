(** * The target of erasure and its evaluator

    The erased language has variables, λ, application, the erased term
    [□], δ-constants, constructors, [match] without a motive, [fix]
    without its type, pairs and projections, and the eliminator instances
    [elim_D[s]] of lecture 7 kept as primitives.  There are no types and
    no annotations.  What computation needs of a declaration stays as
    metadata of the erased signature: the number of parameters and
    indices, the constructors with, for each field, whether it is
    recursive and with how many positions, and the kind of elimination of
    the declaration.  Erasure keeps the positions of arguments: an erased
    argument is [□], not removed.

    The primitives Unit, Bool and Void of the minimal MLTT have built-in
    declarations [prim.Unit] ([tt]), [prim.Bool] ([true], [false]) and
    [prim.Void], so that their eliminators become matches.

    ** The evaluator

    [eval_erased] evaluates weakly by value, like [eval_src] of the
    kernel: no evaluation under λ, the function and then the argument,
    from left to right.  Values are λ, [□], constructors applied to
    values, pairs of values, and [fix] and eliminators applied to fewer
    arguments than they compute with.  The rules:
    - β for a λ applied to a value, δ for a constant, the projections of
      a pair, and ι for a match on a constructor of its type, the branch
      applied to the fields, the parameters skipped;
    - [□] applied to a value is [□]; a match on [□] is stuck, even on a
      type with one constructor;
    - a [fix] unfolds as soon as it has [k + 1] arguments, whatever its
      structural argument is: [□] included;
    - a saturated eliminator computes by the kind of its declaration:
      on data ([KData]), on a constructor, with the fields and, after a
      recursive one, its hypothesis, as [iota_args] of the kernel; for a
      singleton proposition ([KSingleton]) on any object, [□] after
      erasure, with the only method, [□] for the fields, and the
      hypotheses of the recursive fields built from the description; an
      empty proposition, or one eliminated into Prop only, does not
      compute.  The indices of a hypothesis are [□]: the target never
      reads them.
    The answers are those of [eval_src]: a value, a stuck term, or the
    budget exhausted. *)

From Stdlib Require Import String List Bool Arith.
Import ListNotations.
From DepTypes.PTS Require Import Syntax EvalSrc.

Local Open Scope string_scope.

(** ** Terms *)

Inductive eterm : Type :=
| EBox : eterm
| EVar : nat -> eterm
| ELam : eterm -> eterm
| EApp : eterm -> eterm -> eterm
| EConst : string -> eterm
| ECtor : string -> string -> eterm
| ECase : string -> eterm -> list eterm -> eterm
| EFix : nat -> eterm -> eterm
| EPair : eterm -> eterm -> eterm
| EFst : eterm -> eterm
| ESnd : eterm -> eterm
| EPrim : string -> sort -> eterm.

Definition eterm_eq_dec : forall (t u : eterm), {t = u} + {t <> u}.
Proof.
  fix IH 1. intros t u.
  decide equality;
    first [ apply Nat.eq_dec | apply string_dec | apply sort_eq_dec | apply (list_eq_dec IH) ].
Defined.

Definition eterm_eqb (t u : eterm) : bool := if eterm_eq_dec t u then true else false.

Lemma eterm_eqb_eq : forall t u, eterm_eqb t u = true <-> t = u.
Proof. intros t u. unfold eterm_eqb. destruct (eterm_eq_dec t u); split; congruence. Qed.

(** ** Renaming and substitution *)

Fixpoint erename (r : nat -> nat) (t : eterm) : eterm :=
  match t with
  | EVar n => EVar (r n)
  | ELam b => ELam (erename (up_ren r) b)
  | EApp f a => EApp (erename r f) (erename r a)
  | ECase D x bs => ECase D (erename r x) (map (erename r) bs)
  | EFix k b => EFix k (erename (up_ren r) b)
  | EPair a b => EPair (erename r a) (erename r b)
  | EFst p => EFst (erename r p)
  | ESnd p => ESnd (erename r p)
  | EBox | EConst _ | ECtor _ _ | EPrim _ _ => t
  end.

Definition elift (k : nat) (t : eterm) : eterm := erename (Nat.add k) t.

Definition eup (sb : nat -> eterm) : nat -> eterm :=
  fun n => match n with 0 => EVar 0 | S n' => elift 1 (sb n') end.

Fixpoint esubst (sb : nat -> eterm) (t : eterm) : eterm :=
  match t with
  | EVar n => sb n
  | ELam b => ELam (esubst (eup sb) b)
  | EApp f a => EApp (esubst sb f) (esubst sb a)
  | ECase D x bs => ECase D (esubst sb x) (map (esubst sb) bs)
  | EFix k b => EFix k (esubst (eup sb) b)
  | EPair a b => EPair (esubst sb a) (esubst sb b)
  | EFst p => EFst (esubst sb p)
  | ESnd p => ESnd (esubst sb p)
  | EBox | EConst _ | ECtor _ _ | EPrim _ _ => t
  end.

Definition esubst1 (b u : eterm) : eterm :=
  esubst (fun n => match n with 0 => u | S n' => EVar n' end) b.

Definition eapps (h : eterm) (us : list eterm) : eterm := fold_left EApp us h.

Fixpoint espine_head (t : eterm) : eterm :=
  match t with EApp f _ => espine_head f | _ => t end.

Fixpoint espine_args (t : eterm) : list eterm :=
  match t with EApp f a => espine_args f ++ [a] | _ => [] end.

Fixpoint elams (n : nat) (b : eterm) : eterm :=
  match n with 0 => b | S n' => ELam (elams n' b) end.

(** [EVar (n - 1), …, EVar 0]. *)
Fixpoint evars (n : nat) : list eterm :=
  match n with 0 => [] | S n' => EVar n' :: evars n' end.

(** ** The erased signature *)

(** A field: data, a proof or a type ([ENonRec]), or recursive with [m]
    positions ([ERec m]). *)
Inductive efield : Type :=
| ENonRec : efield
| ERec : nat -> efield.

Record ector : Type := mk_ector {
  ector_name : string;
  ector_fields : list efield;
}.

(** How a declaration computes when eliminated into a type. *)
Inductive elim_kind : Type :=
| KData : elim_kind         (** data: on a constructor *)
| KSingleton : elim_kind    (** a proposition with one constructor of proofs: on any object *)
| KEmpty : elim_kind        (** a proposition without constructors: never *)
| KProp : elim_kind.        (** a proposition eliminated into Prop only: never *)

Record eind : Type := mk_eind {
  eind_name : string;
  eind_params : nat;
  eind_indices : nat;
  eind_ctors : list ector;
  eind_kind : elim_kind;
}.

Inductive eentry : Type :=
| EEInd : eind -> eentry
| EEElim : string -> sort -> elim_kind -> eentry   (** an instance and how it computes *)
| EEDef : string -> eterm -> eentry.

Definition esignature : Type := list eentry.

Definition prim_unit : string := "prim.Unit".
Definition prim_bool : string := "prim.Bool".
Definition prim_void : string := "prim.Void".

(** The declarations of the primitives, below every erased signature. *)
Definition prim_entries : esignature :=
  [EEInd (mk_eind prim_unit 0 0 [mk_ector "tt" []] KData);
   EEInd (mk_eind prim_bool 0 0 [mk_ector "true" []; mk_ector "false" []] KData);
   EEInd (mk_eind prim_void 0 0 [] KData)].

Fixpoint efind_ind (se : esignature) (D : string) : option eind :=
  match se with
  | [] => None
  | EEInd d :: se' => if String.eqb (eind_name d) D then Some d else efind_ind se' D
  | _ :: se' => efind_ind se' D
  end.

Fixpoint efind_elim (se : esignature) (D : string) (s : sort) : option elim_kind :=
  match se with
  | [] => None
  | EEElim D' s' k :: se' => if String.eqb D' D && sort_eqb s' s then Some k else efind_elim se' D s
  | _ :: se' => efind_elim se' D s
  end.

Fixpoint efind_def (se : esignature) (f : string) : option eterm :=
  match se with
  | [] => None
  | EEDef f' b :: se' => if String.eqb f' f then Some b else efind_def se' f
  | _ :: se' => efind_def se' f
  end.

Fixpoint efind_ctor (cs : list ector) (c : string) : option (nat * ector) :=
  match cs with
  | [] => None
  | cd :: cs' =>
      if String.eqb (ector_name cd) c then Some (0, cd)
      else option_map (fun r => (S (fst r), snd r)) (efind_ctor cs' c)
  end.

(** ** ι *)

Section Iota.
  Variable se : esignature.

  (** A match on a constructor of D: its branch applied to the fields. *)
  Definition ecase_iota (D : string) (v : eterm) (bs : list eterm) : option eterm :=
    match espine_head v with
    | ECtor D' c =>
        if String.eqb D' D then
          match efind_ind se D with
          | Some d =>
              match efind_ctor (eind_ctors d) c with
              | Some (i, cd) =>
                  let xa := espine_args v in
                  if Nat.eqb (length xa) (eind_params d + length (ector_fields cd)) then
                    option_map (fun b => eapps b (skipn (eind_params d) xa)) (nth_error bs i)
                  else None
              | None => None
              end
          | None => None
          end
        else None
    | _ => None
    end.

  (** Parameters, motive, methods, indices, object. *)
  Definition earity (d : eind) : nat :=
    eind_params d + 1 + length (eind_ctors d) + eind_indices d + 1.

  (** The hypothesis of a recursive field [a] with [m] positions:
      [λȳ. elim_D[s] pre □… (a ȳ)]. *)
  Definition ehyp (D : string) (s : sort) (pre : list eterm) (q m : nat) (a : eterm) : eterm :=
    elams m (eapps (EPrim D s) (map (elift m) pre ++ repeat EBox q ++ [eapps (elift m a) (evars m)])).

  Fixpoint eiota_args (D : string) (s : sort) (pre : list eterm) (q : nat) (fs : list efield)
    (xs : list eterm) : list eterm :=
    match fs, xs with
    | ENonRec :: fs', a :: xs' => a :: eiota_args D s pre q fs' xs'
    | ERec m :: fs', a :: xs' => a :: ehyp D s pre q m a :: eiota_args D s pre q fs' xs'
    | _, _ => []
    end.

  (** A saturated spine of an eliminator instance, by the kind of its
      declaration. *)
  Definition eelim_iota (t : eterm) : option eterm :=
    match espine_head t with
    | EPrim D s =>
        match efind_elim se D s, efind_ind se D with
        | Some kind, Some d =>
            let args := espine_args t in
            if Nat.eqb (length args) (earity d) then
              let p := eind_params d in
              let k := length (eind_ctors d) in
              let q := eind_indices d in
              let pre := firstn (S p + k) args in
              let methods := firstn k (skipn (S p) args) in
              match kind with
              | KData =>
                  let obj := last args EBox in
                  match espine_head obj with
                  | ECtor D' c =>
                      if String.eqb D' D then
                        match efind_ctor (eind_ctors d) c with
                        | Some (i, cd) =>
                            let xa := espine_args obj in
                            if Nat.eqb (length xa) (p + length (ector_fields cd)) then
                              option_map (fun m => eapps m (eiota_args D s pre q (ector_fields cd) (skipn p xa)))
                                (nth_error methods i)
                            else None
                        | None => None
                        end
                      else None
                  | _ => None
                  end
              | KSingleton =>
                  match eind_ctors d, methods with
                  | [cd], [m] =>
                      Some (eapps m (eiota_args D s pre q (ector_fields cd)
                                       (repeat EBox (length (ector_fields cd)))))
                  | _, _ => None
                  end
              | KEmpty | KProp => None
              end
            else None
        | _, _ => None
        end
    | _ => None
    end.

  (** An eliminator applied to fewer arguments than its arity. *)
  Definition eelim_partial (t : eterm) : bool :=
    match espine_head t with
    | EPrim D s =>
        match efind_elim se D s, efind_ind se D with
        | Some _, Some d => Nat.ltb (length (espine_args t)) (earity d)
        | _, _ => false
        end
    | _ => false
    end.

  (** ** Evaluation *)

  Fixpoint eval_erased (fuel : nat) (t : eterm) {struct fuel} : cbv_result eterm :=
    match fuel with
    | O => CbvOutOfFuel
    | S fuel' =>
        match t with
        | EBox | ELam _ | EFix _ _ | ECtor _ _ | EPrim _ _ => CbvValue t
        | EVar _ => CbvStuck t
        | EConst f =>
            match efind_def se f with
            | Some b => eval_erased fuel' b
            | None => CbvStuck t
            end
        | EApp g a =>
            match eval_erased fuel' g with
            | CbvValue vg =>
                match eval_erased fuel' a with
                | CbvValue va =>
                    match vg with
                    | ELam b => eval_erased fuel' (esubst1 b va)
                    | EBox => CbvValue EBox
                    | _ =>
                        let u := EApp vg va in
                        match espine_head u with
                        | EFix k b =>
                            let args := espine_args u in
                            if Nat.eqb (length args) (S k) then eval_erased fuel' (eapps (esubst1 b (EFix k b)) args)
                            else if Nat.ltb (length args) (S k) then CbvValue u else CbvStuck u
                        | EPrim _ _ =>
                            match eelim_iota u with
                            | Some r => eval_erased fuel' r
                            | None => if eelim_partial u then CbvValue u else CbvStuck u
                            end
                        | ECtor _ _ => CbvValue u
                        | _ => CbvStuck u
                        end
                    end
                | r => r
                end
            | r => r
            end
        | EPair a b =>
            match eval_erased fuel' a with
            | CbvValue va =>
                match eval_erased fuel' b with
                | CbvValue vb => CbvValue (EPair va vb)
                | r => r
                end
            | r => r
            end
        | EFst p =>
            match eval_erased fuel' p with
            | CbvValue (EPair a _) => CbvValue a
            | CbvValue v => CbvStuck (EFst v)
            | r => r
            end
        | ESnd p =>
            match eval_erased fuel' p with
            | CbvValue (EPair _ b) => CbvValue b
            | CbvValue v => CbvStuck (ESnd v)
            | r => r
            end
        | ECase D x bs =>
            match eval_erased fuel' x with
            | CbvValue v =>
                match ecase_iota D v bs with
                | Some r => eval_erased fuel' r
                | None => CbvStuck (ECase D v bs)
                end
            | r => r
            end
        end
    end.

  (** ** The rules, as stated *)

  Lemma eval_box_app : forall fuel g a,
    eval_erased fuel g = CbvValue EBox -> eval_erased fuel a = CbvValue a ->
    eval_erased (S fuel) (EApp g a) = CbvValue EBox.
  Proof. intros fuel g a Hg Ha. cbn [eval_erased]. rewrite Hg, Ha. reflexivity. Qed.

  (** A match on [□] is stuck. *)
  Lemma eval_case_box : forall fuel D x bs,
    eval_erased fuel x = CbvValue EBox -> eval_erased (S fuel) (ECase D x bs) = CbvStuck (ECase D EBox bs).
  Proof. intros fuel D x bs H. cbn [eval_erased]. rewrite H. reflexivity. Qed.

  (** A [fix] with its [k + 1] arguments unfolds, whatever they are. *)
  Lemma eval_fix_unfolds : forall fuel g a vg va k b,
    eval_erased fuel g = CbvValue vg -> eval_erased fuel a = CbvValue va ->
    (forall b', vg <> ELam b') -> vg <> EBox ->
    espine_head (EApp vg va) = EFix k b -> length (espine_args (EApp vg va)) = S k ->
    eval_erased (S fuel) (EApp g a) = eval_erased fuel (eapps (esubst1 b (EFix k b)) (espine_args (EApp vg va))).
  Proof.
    intros fuel g a vg va k b Hg Ha Hl Hb Hh Hn. cbn [eval_erased]. rewrite Hg, Ha.
    destruct vg; try (exfalso; first [exact (Hb eq_refl) | exact (Hl _ eq_refl)]).
    all: cbv zeta; rewrite Hh, Hn, Nat.eqb_refl; reflexivity.
  Qed.
End Iota.
