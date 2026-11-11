(** * The simulation of evaluation by value in the relation of erasure

    The core of [erasure_simulation] (Contracts.v), after the
    correctness of erasure of MetaCoq: if [t] erases to [e] at [T] in the
    empty context and the source evaluator reaches a value [v] of [t],
    then the erased evaluator reaches from [e] a value [w] with [v]
    erasing to [w] at [T] ([simulation]).  It is stated for a relation
    of the signatures ([erases_env]), as MetaCoq states it for a global
    environment related to its erasure:
    - the signature is type-correct, so evaluation keeps the type
      (PTS.SubjectRed of the kernel);
    - every δ-body erases, in the relation, to the body of the erased
      signature;
    - the declarations are erased by [erase_ind], the primitives are at
      the bottom of the erased signature, and every instance into a sort
      other than Prop has an erased kind;
    - the ι of an instance with active rules is simulated by the erased
      ι of its kind, in the relation: the local condition that the
      registration of an instance would check, as [signature_typed]
      asks the ι-rules to keep the type;
    - the fields of the constructor of a singleton proposition are
      proofs, for parameters of the types of the parameters.
    A checked signature and its erasure are so related
    (Erasure/EnvRelated.v; [checked_env_related_holds]
    of Contracts.v).

    The proof goes by the budget of the source evaluator, then by the
    derivation of the relation.  A term erased to [□] reaches a value of
    the same type, erased to [□] again: its type stays erasable.  A
    function erased to [□] is applied to give [□], at a codomain that is
    erasable as the Π is ([erasable_pi_cod]).  Otherwise the erased
    value of a function has the head of the source value: a λ, a
    constructor, an eliminator instance or a [fix] ([erases_spine_inv]),
    and the erased evaluator takes the same step: β by the substitution
    lemma of the relation (Erasure/RelationSubst.v), the unfolding of a
    [fix] whatever its structural argument, ι of an instance by the
    premise, ι of a match on a constructor whose fields are related
    against the telescope of the branch ([eargs]).  A match on a
    singleton proposition is erased to its branch applied to [□] for
    each field, without its scrutinee: the source scrutinee reaches a
    constructor whose fields are proofs.  A match on an empty
    proposition, or an eliminator of Void, never reaches a value in the
    source. *)

From Stdlib Require Import String List Bool Arith Lia Relations.
Import ListNotations.
From DepTypes.Common Require Import Outcome.
From DepTypes.PTS Require Import Syntax Telescope Spec Signature Reduction SubstLaws Confluence Guard Typing
  TypingSubst Inversion SubjectRed BidirSound EvalSrc.
From DepTypes.Configs Require Import Predicative.
From DepTypes.PTS Require Import Values.
From CIC.Erasure Require Import Target Erase Relation RelationSubst.

(** ** The erased evaluator *)

(** The shape of the values of the erased evaluator: no application
    headed by [□] or by a λ. *)
Inductive evalue : eterm -> Prop :=
| EV_Box : evalue EBox
| EV_Lam : forall b, evalue (ELam b)
| EV_Fix : forall k b, evalue (EFix k b)
| EV_Ctor : forall D c, evalue (ECtor D c)
| EV_Prim : forall D s, evalue (EPrim D s)
| EV_Pair : forall a b, evalue a -> evalue b -> evalue (EPair a b)
| EV_App : forall f a, evalue f -> evalue a -> f <> EBox -> (forall b, f <> ELam b) -> evalue (EApp f a).

Lemma eapps_snoc : forall h us u, eapps h (us ++ [u]) = EApp (eapps h us) u.
Proof. intros h us u. unfold eapps. rewrite fold_left_app. reflexivity. Qed.

Lemma espine_head_eapps : forall us h, espine_head (eapps h us) = espine_head h.
Proof.
  intros us. induction us as [|u us IH] using rev_ind; intros h; [reflexivity | ].
  rewrite eapps_snoc. cbn [espine_head]. apply IH.
Qed.

Lemma espine_args_eapps : forall us h, espine_args (eapps h us) = espine_args h ++ us.
Proof.
  intros us. induction us as [|u us IH] using rev_ind; intros h; [rewrite app_nil_r; reflexivity | ].
  rewrite eapps_snoc. cbn [espine_args]. rewrite IH, app_assoc. reflexivity.
Qed.

Section Target.
  Variable se : esignature.

  (** The application of a value that is no λ and no [□]. *)
  Definition eapp_tail (fuel : nat) (vg va : eterm) : cbv_result eterm :=
    let u := EApp vg va in
    match espine_head u with
    | EFix k b =>
        let args := espine_args u in
        if Nat.eqb (length args) (S k) then eval_erased se fuel (eapps (esubst1 b (EFix k b)) args)
        else if Nat.ltb (length args) (S k) then CbvValue u else CbvStuck u
    | EPrim _ _ =>
        match eelim_iota se u with
        | Some r => eval_erased se fuel r
        | None => if eelim_partial se u then CbvValue u else CbvStuck u
        end
    | ECtor _ _ => CbvValue u
    | _ => CbvStuck u
    end.

  Lemma eval_erased_app : forall fuel g a vg va,
    eval_erased se fuel g = CbvValue vg -> eval_erased se fuel a = CbvValue va ->
    eval_erased se (S fuel) (EApp g a) =
    match vg with
    | ELam b => eval_erased se fuel (esubst1 b va)
    | EBox => CbvValue EBox
    | _ => eapp_tail fuel vg va
    end.
  Proof. intros fuel g a vg va Hg Ha. cbn [eval_erased]. rewrite Hg, Ha. destruct vg; reflexivity. Qed.

  (** More budget gives the same value. *)
  Lemma eval_erased_mono : forall n m t v, n <= m -> eval_erased se n t = CbvValue v ->
    eval_erased se m t = CbvValue v.
  Proof.
    induction n as [|n IH]; intros m t v Hle H; [discriminate H | ].
    destruct m as [|m]; [lia | ]. assert (Hle' : n <= m) by lia.
    revert H. cbn [eval_erased].
    destruct t as [ | n0 | b | g a | f | D c | D x bs | k b | a1 b1 | p | p | D s ]; try (intros H; exact H).
    (* an application *)
    - destruct (eval_erased se n g) as [vg|ug|] eqn:Eg; try (intros H; discriminate H).
      rewrite (IH _ _ _ Hle' Eg).
      destruct (eval_erased se n a) as [va|ua|] eqn:Ea; try (intros H; discriminate H).
      rewrite (IH _ _ _ Hle' Ea).
      destruct vg; try (intros H; exact H); try (apply IH, Hle').
      all: cbv zeta.
      all: destruct (espine_head _); try (intros H; exact H).
      all: try (destruct (Nat.eqb _ _); [apply IH, Hle' | intros H; exact H]).
      all: destruct (eelim_iota se _); [apply IH, Hle' | intros H; exact H].
    (* a constant *)
    - destruct (efind_def se f); [apply IH, Hle' | intros H; exact H].
    (* a match *)
    - destruct (eval_erased se n x) as [vx|ux|] eqn:Ex; try (intros H; discriminate H).
      rewrite (IH _ _ _ Hle' Ex).
      destruct (ecase_iota se D vx bs); [apply IH, Hle' | intros H; exact H].
    (* a pair *)
    - destruct (eval_erased se n a1) as [va|ua|] eqn:Ea; try (intros H; discriminate H).
      rewrite (IH _ _ _ Hle' Ea).
      destruct (eval_erased se n b1) as [vb|ub|] eqn:Eb; try (intros H; discriminate H).
      rewrite (IH _ _ _ Hle' Eb). intros H; exact H.
    (* the projections *)
    - destruct (eval_erased se n p) as [vp|up|] eqn:Ep; try (intros H; discriminate H).
      rewrite (IH _ _ _ Hle' Ep). intros H; exact H.
    - destruct (eval_erased se n p) as [vp|up|] eqn:Ep; try (intros H; discriminate H).
      rewrite (IH _ _ _ Hle' Ep). intros H; exact H.
  Qed.

  Lemma eval_erased_evalue : forall n t v, eval_erased se n t = CbvValue v -> evalue v.
  Proof.
    induction n as [|n IH]; intros t v H; [discriminate H | ].
    revert H. cbn [eval_erased].
    destruct t as [ | n0 | b | g a | f | D c | D x bs | k b | a1 b1 | p | p | D s ]; try solve [intros H; injection H as <-; constructor].
    - intros H. discriminate H.
    - destruct (eval_erased se n g) as [vg|ug|] eqn:Eg; try (intros H; discriminate H).
      destruct (eval_erased se n a) as [va|ua|] eqn:Ea; try (intros H; discriminate H).
      pose proof (IH _ _ Eg) as Hg. pose proof (IH _ _ Ea) as Ha.
      destruct vg; try (intros H; exact (IH _ _ H));
        try solve [intros H; injection H as <-; constructor; first [assumption | discriminate | intros ? ?; discriminate]].
      all: cbv beta iota zeta.
      all: destruct (espine_head _); try (intros H; discriminate H).
      all: try (destruct (Nat.eqb _ _); [intros H; exact (IH _ _ H) | ]).
      all: try (destruct (Nat.ltb _ _); [ | intros H; discriminate H]).
      all: try (destruct (eelim_iota se _); [intros H; exact (IH _ _ H) | ]).
      all: try (destruct (eelim_partial se _); [ | intros H; discriminate H]).
      all: intros H; injection H as <-; constructor; first [assumption | discriminate | intros ? ?; discriminate].
    - destruct (efind_def se f); [intros H; exact (IH _ _ H) | intros H; discriminate H].
    - destruct (eval_erased se n x) as [vx|ux|] eqn:Ex; try (intros H; discriminate H).
      destruct (ecase_iota se D vx bs); [intros H; exact (IH _ _ H) | intros H; discriminate H].
    - destruct (eval_erased se n a1) as [va|ua|] eqn:Ea; try (intros H; discriminate H).
      destruct (eval_erased se n b1) as [vb|ub|] eqn:Eb; try (intros H; discriminate H).
      intros H. injection H as <-. constructor; [exact (IH _ _ Ea) | exact (IH _ _ Eb)].
    - destruct (eval_erased se n p) as [vp|up|] eqn:Ep; try (intros H; discriminate H).
      pose proof (IH _ _ Ep) as Hp.
      destruct vp; intros H; try discriminate H. injection H as <-. inversion Hp; assumption.
    - destruct (eval_erased se n p) as [vp|up|] eqn:Ep; try (intros H; discriminate H).
      pose proof (IH _ _ Ep) as Hp.
      destruct vp; intros H; try discriminate H. injection H as <-. inversion Hp; assumption.
  Qed.
End Target.

Local Notation Sp := predicative_prop.

(** ** The source evaluator *)

(** No annotation and no match at the root of a value, nor in a pair. *)
Fixpoint svalue (t : term) : Prop :=
  match t with
  | Pair a b => svalue a /\ svalue b
  | Ann _ _ | Case _ _ _ _ _ => False
  | _ => True
  end.

Lemma apps_const_not_lam : forall g l b, apps (Const g) l <> Lam b.
Proof.
  intros g l b. induction l as [|a l _] using rev_ind; [discriminate | rewrite apps_snoc; discriminate].
Qed.

Section Source.
  Variable sg : signature.

  Lemma eval_nested_svalue : forall n t v, eval_nested sg n t = CbvValue v -> svalue v.
  Proof.
    induction n as [|n IH]; intros t v H; [discriminate H | ].
    cbn [eval_nested] in H. destruct t; cbn [eval_node] in H.
    all: try (injection H as <-; exact I).
    all: try discriminate H.
    (* an application *)
    - unfold nested_app in H.
      destruct (eval_nested sg n t1) as [vf|uf|]; try discriminate H.
      destruct (eval_nested sg n t2) as [va|ua|]; try discriminate H.
      unfold nested_apply in H. destruct vf; try exact (IH _ _ H).
      all: destruct (spine_iota sg _); [exact (IH _ _ H) | ].
      all: destruct (spine_value sg _); [injection H as <-; exact I | discriminate H].
    (* an annotation *)
    - exact (IH _ _ H).
    (* the eliminators of the primitives *)
    - destruct (eval_nested sg n t2); discriminate H.
    - destruct (eval_nested sg n t3) as [vu|uu|]; try discriminate H.
      destruct vu; try discriminate H. exact (IH _ _ H).
    - destruct (eval_nested sg n t4) as [vb|ub|]; try discriminate H.
      destruct vb; try discriminate H; exact (IH _ _ H).
    (* pairs and projections *)
    - destruct (eval_nested sg n t1) as [va|ua|] eqn:Ea; try discriminate H.
      destruct (eval_nested sg n t2) as [vb|ub|] eqn:Eb; try discriminate H.
      injection H as <-. split; [exact (IH _ _ Ea) | exact (IH _ _ Eb)].
    - destruct (eval_nested sg n t) as [vp|up|] eqn:Ep; try discriminate H.
      destruct vp; try discriminate H. injection H as <-. exact (proj1 (IH _ _ Ep)).
    - destruct (eval_nested sg n t) as [vp|up|] eqn:Ep; try discriminate H.
      destruct vp; try discriminate H. injection H as <-. exact (proj2 (IH _ _ Ep)).
    (* a constant *)
    - destruct (sig_delta sg g); [exact (IH _ _ H) | injection H as <-; exact I].
    (* a match *)
    - destruct (eval_nested sg n t2) as [vx|ux|]; try discriminate H.
      destruct (case_iota sg _); [exact (IH _ _ H) | discriminate H].
  Qed.

  (** A spine of an eliminator instance below its arity evaluates to a
      spine of the same length; applied, an instance without active rules
      is stuck. *)
  Lemma eval_elim_spine : forall args n D s v,
    eval_nested sg n (apps (Const (Elim D s)) args) = CbvValue v ->
    (forall D' s' d, elim_head sg (Const (Elim D s)) = Some (D', s', d) -> length args < elim_arity d) ->
    exists vals, v = apps (Const (Elim D s)) vals /\ length vals = length args.
  Proof.
    induction args as [|a args IH] using rev_ind; intros n D s v H Har.
    - destruct n as [|n]; [discriminate H | ]. cbn [eval_nested apps fold_left eval_node] in H.
      destruct (sig_delta sg (Elim D s)) eqn:Ed; [discriminate Ed | ]. injection H as <-.
      exists []. split; reflexivity.
    - destruct n as [|n]; [discriminate H | ]. rewrite apps_snoc in H. cbn [eval_nested eval_node] in H.
      unfold nested_app in H.
      destruct (eval_nested sg n (apps (Const (Elim D s)) args)) as [vf|uf|] eqn:Ef; try discriminate H.
      destruct (eval_nested sg n a) as [va|ua|] eqn:Ea; try discriminate H.
      destruct (IH n D s vf Ef) as (vals & -> & Hl).
      { intros D' s' d Hd. specialize (Har D' s' d Hd). rewrite length_app in Har. cbn in Har. lia. }
      unfold nested_apply in H.
      replace (match apps (Const (Elim D s)) vals with Lam b => eval_nested sg n (subst1 b va) | _ => _ end)
        with (match spine_iota sg (App (apps (Const (Elim D s)) vals) va) with
              | Some r => eval_nested sg n r
              | None => if spine_value sg (App (apps (Const (Elim D s)) vals) va)
                        then CbvValue (App (apps (Const (Elim D s)) vals) va)
                        else CbvStuck (App (apps (Const (Elim D s)) vals) va)
              end) in H
        by (destruct vals as [|x vals] using rev_ind; [reflexivity | rewrite apps_snoc; reflexivity]).
      rewrite spine_iota_head in H. rewrite <- apps_snoc in H.
      rewrite spine_head_apps, spine_args_apps in H. cbn [spine_head spine_args spine_args_acc app] in H.
      unfold spine_value in H. rewrite spine_head_apps, spine_args_apps in H.
      cbn [spine_head spine_args spine_args_acc app] in H. unfold head_value, head_arity in H.
      destruct (elim_head sg (Const (Elim D s))) as [[[D' s'] d]|] eqn:Hd; [ | discriminate H].
      assert (Hlt : length (vals ++ [va]) < elim_arity d)
        by (specialize (Har D' s' d eq_refl); rewrite !length_app in Har |- *; cbn in Har |- *; lia).
      cbn [is_inert orb] in H.
      replace (Nat.eqb (length (vals ++ [va])) (elim_arity d)) with false in H
        by (symmetry; apply Nat.eqb_neq; lia).
      replace (Nat.ltb (length (vals ++ [va])) (elim_arity d)) with true in H
        by (symmetry; apply Nat.ltb_lt; lia).
      injection H as <-. exists (vals ++ [va]). split; [reflexivity | rewrite !length_app; cbn; lia].
  Qed.
End Source.

(** ** The relation, inverted *)

Lemma evalue_app_inv : forall f a, evalue (EApp f a) ->
  evalue f /\ evalue a /\ f <> EBox /\ (forall b, f <> ELam b).
Proof. intros f a H. inversion H; subst. auto. Qed.

Lemma svalue_shape : forall t, svalue t -> (forall u A, t <> Ann u A) /\ (forall D s P x bs, t <> Case D s P x bs).
Proof. intros t H. split; intros; intros ->; exact H. Qed.

Section Relation.
  Variable sg : signature.
  Hypothesis Hsig : signature_typed Sp sg.
  Local Notation typed := (has_type Sp sg).
  Local Notation erases := (erases Sp sg).
  Local Notation ctype := (ctype Sp sg).
  Local Notation erasable_at := (erasable_at Sp sg).
  Local Notation "t ≡ u" := (conv sg t u).

  Lemma erasable_at_conv : forall G A B, erasable_at G A -> A ≡ B -> erasable_at G B.
  Proof.
    intros G A B (T' & Hc & H) HAB. exists T'.
    split; [eapply conv_trans; [apply conv_sym, HAB | exact Hc] | exact H].
  Qed.

  Lemma erases_ctype : forall G t X T e, erases G t X e -> ctype G X T -> erases G t T e.
  Proof. intros G t X T e H [<- | [Hc [s HT]]]; [exact H | exact (X_Conv _ _ _ _ _ _ _ _ H HT Hc)]. Qed.

  Lemma erases_app_inv : forall G f a T e, erases G (App f a) T e ->
    (e = EBox /\ typed G (App f a) T /\ erasable_at G T) \/
    (exists A B f' a', e = EApp f' a' /\ erases G f (Pi A B) f' /\
       (erases G a A a' \/ (a' = EBox /\ typed G a A /\ index_position sg f)) /\
       ctype G (subst1 B a) T).
  Proof.
    intros G f a T e H. remember (App f a) as t eqn:Et. revert f a Et.
    induction H; intros f0 a0 Et; try discriminate Et.
    - left. subst. auto.
    - destruct (IHerases _ _ Et) as [(-> & Ht & HE) | (A' & B' & f' & a' & -> & Hf & Ha & HT)].
      + left. split; [reflexivity | split; [eapply T_Conv; eassumption | eapply erasable_at_conv; eassumption]].
      + right. exists A', B', f', a'. repeat split; try assumption. eapply ctype_conv; eassumption.
    - injection Et as <- <-. right. exists A, B, f', u'. repeat split; auto. apply ctype_refl.
    - injection Et as <- <-. right. exists A, B, f', EBox. repeat split; auto. apply ctype_refl.
  Qed.

  Lemma erases_lam_inv : forall G b T e, erases G (Lam b) T e ->
    (e = EBox /\ erasable_at G T) \/
    (exists A B s b', e = ELam b' /\ erases (A :: G) b B b' /\ typed G (Pi A B) (Srt s) /\
       ctype G (Pi A B) T).
  Proof.
    intros G b T e H. remember (Lam b) as t eqn:Et. revert b Et.
    induction H; intros b0 Et; try discriminate Et.
    - left. auto.
    - destruct (IHerases _ Et) as [(-> & HE) | (A' & B' & s' & b' & -> & Hb & HP & HT)].
      + left. split; [reflexivity | eapply erasable_at_conv; eassumption].
      + right. exists A', B', s', b'. repeat split; try assumption. eapply ctype_conv; eassumption.
    - injection Et as <-. right. exists A, B, s, b'. repeat split; auto. apply ctype_refl.
  Qed.

  Lemma erases_const_inv : forall G g T e, erases G (Const g) T e ->
    e = EBox \/ (exists f, g = Def f /\ e = EConst f) \/ (exists D c, g = Ctor D c /\ e = ECtor D c) \/
    (exists D s, g = Elim D s /\ e = EPrim D s /\ s <> Prp).
  Proof.
    intros G g T e H. remember (Const g) as t eqn:Et. revert g Et.
    induction H; intros g0 Et; try discriminate Et.
    - left. reflexivity.
    - exact (IHerases _ Et).
    - injection Et as <-. right. left. eauto.
    - injection Et as <-. right. right. left. eauto.
    - injection Et as <-. right. right. right. eauto.
  Qed.

  Lemma erases_fix_inv : forall G A k b T e, erases G (Fix A k b) T e ->
    (e = EBox /\ erasable_at G T) \/
    (exists s D b', e = EFix k b' /\ typed G A (Srt s) /\ struct_arg sg A k D /\ sig_ind sg D <> None /\
       erases (A :: G) b (lift 1 A) b' /\ fix_guarded sg k b /\ ctype G A T).
  Proof.
    intros G A k b T e H. remember (Fix A k b) as t eqn:Et. revert A k b Et.
    induction H; intros A0 k0 b0 Et; try discriminate Et.
    - left. auto.
    - destruct (IHerases _ _ _ Et) as [(-> & HE) | (s' & D' & b' & -> & K1 & K2 & K3 & K4 & K5 & K6)].
      + left. split; [reflexivity | eapply erasable_at_conv; eassumption].
      + right. exists s', D', b'. repeat split; try assumption. eapply ctype_conv; eassumption.
    - injection Et as <- <- <-. right. exists s, D, b'. repeat split; auto. apply ctype_refl.
  Qed.

  Lemma erases_pair_inv : forall G a b T e, erases G (Pair a b) T e ->
    (e = EBox /\ erasable_at G T) \/
    (exists A B s a' b', e = EPair a' b' /\ typed G (Sigma A B) (Srt s) /\ erases G a A a' /\
       erases G b (subst1 B a) b' /\ ctype G (Sigma A B) T).
  Proof.
    intros G a b T e H. remember (Pair a b) as t eqn:Et. revert a b Et.
    induction H; intros a0 b0 Et; try discriminate Et.
    - left. auto.
    - destruct (IHerases _ _ Et) as [(-> & HE) | (A' & B' & s' & a' & b' & -> & K1 & K2 & K3 & K4)].
      + left. split; [reflexivity | eapply erasable_at_conv; eassumption].
      + right. exists A', B', s', a', b'. repeat split; try assumption. eapply ctype_conv; eassumption.
    - injection Et as <- <-. right. exists A, B, s, a', b'. repeat split; auto. apply ctype_refl.
  Qed.

  (** The constructors of the primitives. *)
  Lemma erases_prim_ctor_inv : forall G t T e, erases G t T e ->
    (t = Tt \/ t = BTrue \/ t = BFalse) ->
    (e = EBox /\ erasable_at G T) \/
    (t = Tt /\ e = ECtor prim_unit "tt") \/ (t = BTrue /\ e = ECtor prim_bool "true") \/
    (t = BFalse /\ e = ECtor prim_bool "false").
  Proof.
    intros G t T e H Ht. induction H; try (destruct Ht as [Ht | [Ht | Ht]]; discriminate Ht).
    - left. auto.
    - destruct (IHerases Ht) as [(-> & HE) | Hr]; [ | right; exact Hr].
      left. split; [reflexivity | eapply erasable_at_conv; eassumption].
    - right. left. auto.
    - right. right. left. auto.
    - right. right. right. auto.
  Qed.

  (** A term erased to [□] that is no annotation nor match has an
      erasable type. *)
  Lemma box_erasable : forall G t T e, erases G t T e -> e = EBox ->
    (forall u A, t <> Ann u A) -> (forall D s P x bs, t <> Case D s P x bs) -> erasable_at G T.
  Proof.
    intros G t T e H. induction H; intros Ee Ha Hc; try discriminate Ee.
    - assumption.
    - eapply erasable_at_conv; [exact (IHerases Ee Ha Hc) | assumption].
    - exfalso. exact (Ha _ _ eq_refl).
    - exfalso. exact (Hc _ _ _ _ _ eq_refl).
  Qed.

  (** Only a λ, an annotation or a match erases to a λ. *)
  Lemma elam_source : forall G t T e, erases G t T e -> forall b', e = ELam b' -> svalue t ->
    exists b, t = Lam b.
  Proof.
    intros G t T e H. induction H; intros b0 Ee Hv; try discriminate Ee.
    - exact (IHerases _ Ee Hv).
    - eauto.
    - destruct Hv.
    - destruct Hv.
  Qed.

  (** The erased value of a spine: the erased head applied to as many
      erased arguments. *)
  Lemma erases_spine_inv : forall args G h T e, erases G (apps h args) T e -> evalue e -> e <> EBox ->
    exists H eh es, e = eapps eh es /\ length es = length args /\ erases G h H eh /\ eh <> EBox.
  Proof.
    induction args as [|a args IH] using rev_ind; intros G h T e H He Hb.
    - exists T, e, []. auto.
    - rewrite apps_snoc in H.
      destruct (erases_app_inv _ _ _ _ _ H) as [(-> & _) | (A & B & f' & a' & -> & Hf & _ & _)];
        [contradiction | ].
      destruct (evalue_app_inv _ _ He) as (Hf' & _ & Hfb & _).
      destruct (IH _ _ _ _ Hf Hf' Hfb) as (H' & eh & es & -> & Hl & Hh & Hne).
      exists H', eh, (es ++ [a']). rewrite eapps_snoc, !length_app, Hl. auto.
  Qed.

  (** ** Erasable types *)

  Lemma ctype_srt : forall G s s', ctype G (Srt s) (Srt s') -> s = s'.
  Proof. intros G s s' [E | [Hc _]]; [injection E as ->; reflexivity | exact (conv_srt_inj sg _ _ Hc)]. Qed.

  Lemma inv_unit : forall G T, typed G Unit T -> ctype G (Srt (Univ 0)) T.
  Proof.
    intros G T H. remember Unit as t eqn:Et. induction H; try discriminate Et.
    - eapply ctype_conv; [exact (IHhas_type1 Et) | eassumption | eassumption].
    - cbn in H0. injection H0 as <-. apply ctype_refl.
  Qed.

  Lemma inv_bool : forall G T, typed G Bool T -> ctype G (Srt (Univ 0)) T.
  Proof.
    intros G T H. remember Bool as t eqn:Et. induction H; try discriminate Et.
    - eapply ctype_conv; [exact (IHhas_type1 Et) | eassumption | eassumption].
    - cbn in H0. injection H0 as <-. apply ctype_refl.
  Qed.

  (** A type with no reduct, no sort and no Π is erasable only in Prop. *)
  Lemma irreducible_erasable : forall G X, (forall w, ~ red1 sg X w) -> (forall s, X <> Srt s) ->
    (forall A B, X <> Pi A B) -> erasable_at G X -> typed G X (Srt Prp).
  Proof.
    intros G X Hx Hs Hp (T' & Hc & H). destruct (church_rosser sg _ _ Hc) as (W & H1 & H2).
    rewrite (red_fixed sg _ Hx _ H1) in H2.
    destruct H as [Har | HP].
    - exfalso. destruct Har as [T s HT | T A B HT _].
      + destruct (red_confluent sg _ _ _ H2 HT) as (W2 & HW1 & HW2).
        rewrite (red_fixed sg _ Hx _ HW1) in HW2. rewrite (red_fixed sg _ (red1_srt sg s) _ HW2) in Hs.
        exact (Hs s eq_refl).
      + destruct (red_confluent sg _ _ _ H2 HT) as (W2 & HW1 & HW2).
        rewrite (red_fixed sg _ Hx _ HW1) in HW2. destruct (red_pi_inv sg _ _ _ HW2) as (A' & B' & E & _).
        exact (Hp _ _ E).
    - exact (subject_red Sp sg Hsig _ _ _ _ HP H2).
  Qed.

  Lemma unit_not_erasable : forall G, erasable_at G Unit -> False.
  Proof.
    intros G H. apply irreducible_erasable in H; [ | exact (red1_unit sg) | discriminate | discriminate].
    pose proof (ctype_srt _ _ _ (inv_unit _ _ H)) as E. discriminate E.
  Qed.

  Lemma bool_not_erasable : forall G, erasable_at G Bool -> False.
  Proof.
    intros G H. apply irreducible_erasable in H; [ | exact (red1_bool sg) | discriminate | discriminate].
    pose proof (ctype_srt _ _ _ (inv_bool _ _ H)) as E. discriminate E.
  Qed.

  Lemma apps_const_not_pi : forall g l A B, apps (Const g) l <> Pi A B.
  Proof.
    intros g l A B. induction l as [|a l _] using rev_ind; [discriminate | rewrite apps_snoc; discriminate].
  Qed.

  (** A family of data, applied to all its arguments, is not erasable. *)
  Lemma ind_not_erasable : forall G D d args, sig_ind sg D = Some d -> ind_sort d <> Prp ->
    length (ind_params d ++ ind_indices d) = length args ->
    erasable_at G (apps (Const (Ind D)) args) -> False.
  Proof.
    intros G D d args Hd Hs Hl (T' & Hc & H). destruct (church_rosser sg _ _ Hc) as (W & H1 & H2).
    destruct (red_ind_spine sg D args W H1) as (l' & -> & Hl').
    destruct H as [Har | HP].
    - destruct Har as [T s HT | T A B HT _].
      + destruct (red_confluent sg _ _ _ H2 HT) as (W2 & HW1 & HW2).
        rewrite (red_fixed sg _ (red1_srt sg s) _ HW2) in HW1.
        destruct (red_ind_spine sg D l' _ HW1) as (l'' & E & _). symmetry in E.
        exact (apps_const_not_srt _ _ _ E).
      + destruct (red_confluent sg _ _ _ H2 HT) as (W2 & HW1 & HW2).
        destruct (red_pi_inv sg _ _ _ HW2) as (A' & B' & -> & _).
        destruct (red_ind_spine sg D l' _ HW1) as (l'' & E & _). symmetry in E.
        exact (apps_const_not_pi _ _ _ _ E).
    - pose proof (subject_red Sp sg Hsig _ _ _ _ HP H2) as HW.
      pose proof (typed_wf Sp sg _ _ _ HW) as HG.
      assert (Hty : sig_type sg (Ind D) = Some (ind_type d)) by (cbn [sig_type]; rewrite Hd; reflexivity).
      destruct (const_type_typed Sp sg Hsig G _ _ HG Hty) as [s0 Hs0]. unfold ind_type in Hs0.
      assert (Hlen : length (ind_params d ++ ind_indices d) = length l') by (rewrite Hl; exact (Forall2_length Hl')).
      destruct (apps_inv Sp sg l' G (Const (Ind D)) _ _ _ _ Hlen HW (const_head Sp sg _ _ _ Hty) Hs0) as [_ Hcv].
      cbn [subst] in Hcv. exact (Hs (conv_srt_inj sg _ _ Hcv)).
  Qed.

  Lemma sigma_not_erasable : forall G A B, erasable_at G (Sigma A B) -> False.
  Proof.
    intros G A B (T' & Hc & H). destruct (church_rosser sg _ _ Hc) as (W & H1 & H2).
    destruct (red_sigma_inv sg _ _ _ H1) as (A1 & B1 & -> & _ & _).
    destruct H as [Har | HP].
    - destruct Har as [T s HT | T A2 B2 HT _].
      + destruct (red_confluent sg _ _ _ H2 HT) as (W2 & HW1 & HW2).
        rewrite (red_fixed sg _ (red1_srt sg s) _ HW2) in HW1.
        destruct (red_sigma_inv sg _ _ _ HW1) as (? & ? & E & _). discriminate E.
      + destruct (red_confluent sg _ _ _ H2 HT) as (W2 & HW1 & HW2).
        destruct (red_pi_inv sg _ _ _ HW2) as (? & ? & -> & _).
        destruct (red_sigma_inv sg _ _ _ HW1) as (? & ? & E & _). discriminate E.
    - pose proof (subject_red Sp sg Hsig _ _ _ _ HP H2) as HW.
      destruct (inv_sigma Sp sg _ _ _ _ HW) as (s1 & s2 & s3 & _ & _ & Hr & HT).
      rewrite (ctype_srt _ _ _ HT) in Hr.
      destruct s1, s2; cbn in Hr; discriminate Hr.
  Qed.

  (** The codomain of an erasable Π, instantiated, is erasable: a Π is
      an arity when its codomain is, and in Prop when its codomain is. *)
  Lemma erasable_pi_cod : forall G A B u, erasable_at G (Pi A B) -> typed G u A -> erasable_at G (subst1 B u).
  Proof.
    intros G A B u (T' & Hc & H) Hu. destruct (church_rosser sg _ _ Hc) as (W & H1 & H2).
    destruct (red_pi_inv sg _ _ _ H1) as (A1 & B1 & -> & HA1 & HB1).
    destruct H as [Har | HP].
    - destruct Har as [T s HT | T A2 B2 HT Har].
      + exfalso. destruct (red_confluent sg _ _ _ H2 HT) as (W2 & HW1 & HW2).
        rewrite (red_fixed sg _ (red1_srt sg s) _ HW2) in HW1.
        destruct (red_pi_inv sg _ _ _ HW1) as (? & ? & E & _). discriminate E.
      + destruct (red_confluent sg _ _ _ H2 HT) as (W2 & HW1 & HW2).
        destruct (red_pi_inv sg _ _ _ HW1) as (A3 & B3 & -> & _ & HB3).
        destruct (red_pi_inv sg _ _ _ HW2) as (A4 & B4 & E & _ & HB4). injection E as <- <-.
        exists (subst1 B2 u). split; [ | left; exact (arity_subst _ _ Har _)].
        apply conv_subst. eapply conv_trans.
        * apply red_conv. eapply rt_trans; [exact HB1 | exact HB3].
        * apply conv_sym, red_conv, HB4.
    - pose proof (subject_red Sp sg Hsig _ _ _ _ HP H2) as HW.
      destruct (inv_pi Sp sg _ _ _ _ HW) as (s1 & s2 & s3 & HA1' & HB1' & Hr & HT).
      rewrite (ctype_srt _ _ _ HT) in Hr.
      assert (Es2 : s2 = Prp) by (destruct s1, s2; cbn in Hr; try discriminate Hr; reflexivity).
      subst s2.
      pose proof (T_Conv _ _ _ _ _ _ _ Hu HA1' (red_conv _ _ HA1)) as Hu1.
      pose proof (typing_subst1 Sp sg _ _ _ _ _ Hu1 HB1') as H3. change (subst1 (Srt Prp) u) with (Srt Prp) in H3.
      exists (subst1 B1 u). split; [apply conv_subst, red_conv, HB1 | right; exact H3].
  Qed.

  (** ** Arguments erased against a telescope *)

  Inductive eargs (G : ctx) : list term -> list term -> list eterm -> Prop :=
  | EA_Nil : eargs G [] [] []
  | EA_Cons : forall T Ts a args a' args', erases G a T a' ->
      eargs G (subst_tele (scons a Var) Ts) args args' -> eargs G (T :: Ts) (a :: args) (a' :: args').

  Lemma eargs_typed : forall G Ts args es, eargs G Ts args es -> args_typed Sp sg G Ts args.
  Proof.
    intros G Ts args es H. induction H; constructor; [exact (proj1 (erases_typed Sp sg) _ _ _ _ H) | exact IHeargs].
  Qed.

  Lemma eargs_length : forall G Ts args es, eargs G Ts args es -> length es = length args.
  Proof. intros G Ts args es H. induction H; cbn [length]; congruence. Qed.

  Lemma eargs_cons_inv : forall G T Ts a args es, eargs G (T :: Ts) (a :: args) es ->
    exists a' es', es = a' :: es' /\ erases G a T a' /\ eargs G (subst_tele (scons a Var) Ts) args es'.
  Proof. intros G T Ts a args es H. inversion H; subst. eauto. Qed.

  (** A head of type [Π Ts. R] applied to arguments erased against [Ts]. *)
  Lemma erases_apps : forall G Ts args es h eh R, eargs G Ts args es -> erases G h (pis Ts R) eh ->
    erases G (apps h args) (subst (tsub args) R) (eapps eh es).
  Proof.
    intros G Ts args es h eh R H. revert h eh R.
    induction H as [|T Ts a args a' args' Ha Hargs IH]; intros h eh R Hh.
    - rewrite subst_tsub_nil. exact Hh.
    - cbn [pis] in Hh. pose proof (X_App _ _ _ _ _ _ _ _ _ Hh Ha) as H1.
      unfold subst1 in H1. rewrite subst_pis in H1.
      pose proof (IH _ _ _ H1) as H2.
      change (apps h (a :: args)) with (apps (App h a) args).
      change (eapps eh (a' :: args')) with (eapps (EApp eh a') args').
      rewrite (subst_tsub_cons a args (length Ts)) in H2; [exact H2 | ].
      rewrite <- (args_typed_length Sp sg _ _ _ (eargs_typed _ _ _ _ Hargs)), subst_tele_length. reflexivity.
  Qed.

  Lemma eargs_app : forall args1 G Ts1 Ts2 args2 es, length Ts1 = length args1 ->
    eargs G (Ts1 ++ Ts2) (args1 ++ args2) es ->
    eargs G Ts1 args1 (firstn (length args1) es) /\
    eargs G (subst_tele (tsub args1) Ts2) args2 (skipn (length args1) es).
  Proof.
    induction args1 as [|a args1 IH]; intros G Ts1 Ts2 args2 es Hl H.
    - destruct Ts1; [ | discriminate Hl]. cbn [app firstn skipn length] in *.
      rewrite subst_tele_var by exact tsub_nil. split; [constructor | exact H].
    - destruct Ts1 as [|T Ts1]; [discriminate Hl | ]. cbn [app length] in *. injection Hl as Hl.
      destruct (eargs_cons_inv _ _ _ _ _ _ H) as (a' & es' & -> & Ha & H').
      rewrite subst_tele_app in H'.
      destruct (IH _ _ _ _ _ ltac:(rewrite subst_tele_length; exact Hl) H') as [H1 H2].
      cbn [firstn skipn]. split; [constructor; assumption | ].
      rewrite subst_tele_subst_tele in H2.
      replace (subst_tele (tsub (a :: args1)) Ts2)
        with (subst_tele (fun n => subst (tsub args1) (upn (length Ts1) (scons a Var) n)) Ts2); [exact H2 | ].
      apply subst_tele_ext. intros n. rewrite Hl. apply tsub_cons.
  Qed.

  Lemma eargs_app_join : forall args1 G Ts1 Ts2 args2 es1 es2,
    eargs G Ts1 args1 es1 -> eargs G (subst_tele (tsub args1) Ts2) args2 es2 ->
    eargs G (Ts1 ++ Ts2) (args1 ++ args2) (es1 ++ es2).
  Proof.
    induction args1 as [|a args1 IH]; intros G Ts1 Ts2 args2 es1 es2 H1 H2.
    - inversion H1; subst. cbn [app]. rewrite subst_tele_var in H2 by exact tsub_nil. exact H2.
    - destruct Ts1 as [|T Ts1]; [inversion H1 | ].
      destruct (eargs_cons_inv _ _ _ _ _ _ H1) as (a' & es' & -> & Ha & H1').
      cbn [app]. constructor; [exact Ha | ]. rewrite subst_tele_app. apply IH; [exact H1' | ].
      rewrite subst_tele_subst_tele.
      pose proof (args_typed_length Sp sg _ _ _ (eargs_typed _ _ _ _ H1')) as Hl. rewrite subst_tele_length in Hl.
      replace (subst_tele (fun n => subst (tsub args1) (upn (length Ts1) (scons a Var) n)) Ts2)
        with (subst_tele (tsub (a :: args1)) Ts2); [exact H2 | ].
      apply subst_tele_ext. intros n. rewrite Hl. symmetry. apply tsub_cons.
  Qed.

  (** Against a convertible telescope that is well formed. *)
  Lemma eargs_conv : forall G Ts args es, eargs G Ts args es ->
    forall Ts' R s, Forall2 (conv sg) Ts Ts' -> typed G (pis Ts' R) (Srt s) -> eargs G Ts' args es.
  Proof.
    intros G Ts args es H. induction H as [|T Ts a args a' args' Ha _ IH]; intros Ts' R s Hc HP.
    - inversion Hc; subst. constructor.
    - destruct (forall2_cons_inv _ _ _ _ Hc) as (T' & Ts'' & -> & HT & HTs).
      cbn [pis] in HP. destruct (inv_pi Sp sg _ _ _ _ HP) as (s1 & s2 & s3 & HT' & HB & _ & _).
      pose proof (X_Conv _ _ _ _ _ _ _ _ Ha HT' HT) as Ha'.
      constructor; [exact Ha' | ].
      pose proof (typing_subst1 Sp sg _ _ _ _ _ (proj1 (erases_typed Sp sg) _ _ _ _ Ha') HB) as H1.
      change (subst1 (Srt s2) a) with (Srt s2) in H1. unfold subst1 in H1. rewrite subst_pis in H1.
      exact (IH _ _ _ (forall2_conv_subst_tele _ _ _ HTs (scons a Var)) H1).
  Qed.

  (** Arguments whose types are propositions erase to [□]. *)
  Inductive args_props (G : ctx) : list term -> list term -> Prop :=
  | AP_Nil : args_props G [] []
  | AP_Cons : forall T Ts a args, typed G a T -> typed G T (Srt Prp) ->
      args_props G (subst_tele (scons a Var) Ts) args -> args_props G (T :: Ts) (a :: args).

  Lemma args_props_eargs : forall G Ts args, args_props G Ts args ->
    eargs G Ts args (repeat EBox (length args)).
  Proof.
    intros G Ts args H. induction H as [|T Ts a args Ha HT _ IH]; cbn [length repeat]; constructor; [ | exact IH].
    apply X_Box; [exact Ha | exists T; split; [apply conv_refl | right; exact HT]].
  Qed.

  (** The erased value of a spine of a head with known types and
      erasures, at no index position: its arguments erased against the
      telescope of the head. *)
  Theorem erases_apps_inv : forall args G h T e Ts R0 s0 eh0, length Ts = length args ->
    erases G (apps h args) T e -> evalue e -> e <> EBox ->
    (forall H eh, erases G h H eh -> eh <> EBox -> H ≡ pis Ts R0 /\ eh = eh0) ->
    (forall l, ~ index_position sg (apps h l)) ->
    typed G (pis Ts R0) (Srt s0) ->
    exists es, e = eapps eh0 es /\ eargs G Ts args es /\ subst (tsub args) R0 ≡ T.
  Proof.
    induction args as [|a args IH] using rev_ind; intros G h T e Ts R0 s0 eh0 Hl He Hev Hb Hh Hi HP.
    - destruct Ts; [ | discriminate Hl]. destruct (Hh T e He Hb) as [Hc ->].
      exists []. split; [reflexivity | split; [constructor | ]]. rewrite subst_tsub_nil. apply conv_sym, Hc.
    - assert (HTs : Ts <> []) by (intros ->; rewrite length_app in Hl; cbn in Hl; lia).
      destruct (exists_last HTs) as (Ts' & Tl & ->).
      rewrite !length_app in Hl. cbn [length] in Hl.
      rewrite apps_snoc in He.
      destruct (erases_app_inv _ _ _ _ _ He) as [(-> & _) | (A & B & f' & a' & -> & Hf & Ha & HT)];
        [contradiction | ].
      destruct (evalue_app_inv _ _ Hev) as (Hf' & _ & Hfb & _).
      destruct Ha as [Ha | (_ & _ & Hip)]; [ | exfalso; exact (Hi _ Hip)].
      rewrite pis_app in HP. cbn [pis] in HP.
      assert (Hh' : forall H eh, erases G h H eh -> eh <> EBox -> H ≡ pis Ts' (Pi Tl R0) /\ eh = eh0).
      { intros H eh H1 H2. destruct (Hh H eh H1 H2) as [Hc Heq]. rewrite pis_app in Hc. split; [exact Hc | exact Heq]. }
      destruct (IH G h (Pi A B) f' Ts' (Pi Tl R0) s0 eh0 ltac:(lia) Hf Hf' Hfb Hh' Hi HP) as (es & -> & Hargs & Hc).
      cbn [subst] in Hc. apply pi_inj in Hc as [HcA HcB].
      destruct (typed_pis_inst Sp sg _ _ _ _ _ (eargs_typed _ _ _ _ Hargs) HP) as [s' HPi]. cbn [subst] in HPi.
      destruct (inv_pi Sp sg _ _ _ _ HPi) as (s1 & _ & _ & HTl & _ & _ & _).
      pose proof (X_Conv _ _ _ _ _ _ _ _ Ha HTl (conv_sym _ _ HcA)) as Ha'.
      exists (es ++ [a']). split; [rewrite eapps_snoc; reflexivity | split].
      + apply (eargs_app_join args G Ts' [Tl] [a] es [a'] Hargs). cbn [subst_tele]. constructor; [exact Ha' | constructor].
      + rewrite subst_tsub_snoc. eapply conv_trans; [ | exact (ctype_conv_of Sp sg _ _ _ HT)].
        apply conv_subst. exact HcB.
  Qed.

  (** ** The head of a spine replaced *)

  Fixpoint rho_spine (rho : eterm -> eterm) (n : nat) (e : eterm) : eterm :=
    match n with
    | 0 => rho e
    | S n' => match e with EApp f a => EApp (rho_spine rho n' f) a | _ => e end
    end.

  Lemma rho_spine_eapps : forall rho es eh, rho_spine rho (length es) (eapps eh es) = eapps (rho eh) es.
  Proof.
    intros rho es. induction es as [|x es IH] using rev_ind; intros eh; [reflexivity | ].
    rewrite eapps_snoc, length_app, Nat.add_1_r. cbn [rho_spine]. rewrite IH, eapps_snoc. reflexivity.
  Qed.

  Lemma erases_replace_head : forall rho args G h h2 T e, erases G (apps h args) T e ->
    (forall H eh, erases G h H eh -> erases G h2 H (rho eh)) -> (forall H, typed G h H -> typed G h2 H) ->
    (forall l, index_position sg (apps h l) -> index_position sg (apps h2 l)) ->
    erases G (apps h2 args) T (rho_spine rho (length args) e).
  Proof.
    intros rho args. induction args as [|a args IH] using rev_ind; intros G h h2 T e H Hh Ht Hi;
      [exact (Hh _ _ H) | ].
    rewrite length_app, Nat.add_1_r. rewrite apps_snoc in H.
    destruct (erases_app_inv _ _ _ _ _ H) as [(-> & HT & HE) | (A & B & f' & a' & -> & Hf & Ha & HT)].
    - cbn [rho_spine]. apply X_Box; [ | exact HE].
      rewrite <- apps_snoc in HT. exact (apps_replace Sp sg _ _ _ _ _ HT Ht).
    - cbn [rho_spine]. rewrite apps_snoc. pose proof (IH _ _ _ _ _ Hf Hh Ht Hi) as Hf2.
      apply (erases_ctype _ _ (subst1 B a) _ _); [ | exact HT].
      destruct Ha as [Ha | (-> & Ha & Hip)].
      + exact (X_App _ _ _ _ _ _ _ _ _ Hf2 Ha).
      + exact (X_AppIndex _ _ _ _ _ _ _ _ Hf2 Ha (Hi _ Hip)).
  Qed.
End Relation.

(** ** Signatures and their erasures *)

Lemma erases_branches_nth : forall sg G d ps P cs bs bs', erases_branches Sp sg G d ps P cs bs bs' ->
  forall i c b, nth_error cs i = Some c -> nth_error bs i = Some b ->
  exists b', nth_error bs' i = Some b' /\ erases Sp sg G b (case_branch_type d ps P c) b'.
Proof.
  intros sg G d ps P cs bs bs' H. induction H as [|G d ps P c cs b bs b' bs' Hb _ IH]; intros i c0 b0 Hc Hb0.
  - destruct i; discriminate Hc.
  - destruct i as [|i]; cbn [nth_error] in *.
    + injection Hc as <-. injection Hb0 as <-. exists b'. auto.
    + exact (IH i c0 b0 Hc Hb0).
Qed.

Lemma efind_ctor_erase : forall cs c i cd, find_ctor cs c = Some (i, cd) ->
  efind_ctor (map (fun c => mk_ector (ctor_name c) (map efield_of (ctor_fields c))) cs) c =
  Some (i, mk_ector (ctor_name cd) (map efield_of (ctor_fields cd))).
Proof.
  induction cs as [|cd' cs IH]; intros c i cd H; [discriminate H | ]. cbn [find_ctor] in H.
  cbn [map efind_ctor ector_name].
  destruct (String.eqb (ctor_name cd') c) eqn:E.
  - injection H as <- <-. reflexivity.
  - destruct (find_ctor cs c) as [[i' cd'']|] eqn:Ec; [ | discriminate H]. cbn [option_map] in H.
    injection H as <- <-. rewrite (IH _ _ _ Ec). reflexivity.
Qed.

Lemma earity_erase : forall d, earity (erase_ind d) = elim_arity d.
Proof. intros d. unfold earity, elim_arity, erase_ind. cbn. rewrite length_map. reflexivity. Qed.

(** A signature related to an erased one: the premises of the
    simulation. *)
Record erases_env (sg : signature) (se : esignature) : Prop := {
  env_typed : signature_typed Sp sg;
  env_defs : forall f A b, sig_def sg f = Some (A, b) ->
    exists b', efind_def se f = Some b' /\ erases Sp sg [] b A b';
  env_inds : forall D d, sig_ind sg D = Some d -> efind_ind se D = Some (erase_ind d);
  env_unit : efind_ind se prim_unit = efind_ind prim_entries prim_unit;
  env_bool : efind_ind se prim_bool = efind_ind prim_entries prim_bool;
  env_elims : forall D s A act, s <> Prp -> sig_elim sg D s = Some (A, act) -> efind_elim se D s <> None;
  env_iota : forall t u T e, iota sg t = Some u -> erases Sp sg [] t T e -> evalue e ->
    (exists D s, espine_head e = EPrim D s) ->
    exists e2, eelim_iota se e = Some e2 /\ erases Sp sg [] u T e2;
  env_singleton : forall D d c ps xs, sig_ind sg D = Some d -> ind_sort d = Prp -> ind_elim d = AllSorts ->
    ind_ctors d = [c] ->
    args_typed Sp sg [] (ind_params d) ps ->
    args_typed Sp sg [] (subst_tele (tsub ps) (field_types (ind_name d) (length (ind_params d)) 0 (ctor_fields c))) xs ->
    args_props sg [] (subst_tele (tsub ps) (field_types (ind_name d) (length (ind_params d)) 0 (ctor_fields c))) xs
}.

Section Simulation.
  Variable sg : signature.
  Variable se : esignature.
  Hypothesis Henv : erases_env sg se.
  Local Notation typed := (has_type Sp sg).
  Local Notation erases := (erases Sp sg).
  Local Notation "t ≡ u" := (conv sg t u).

  Let Hsig : signature_typed Sp sg := env_typed _ _ Henv.

  Lemma eval_typed : forall n t v T, typed [] t T -> eval_nested sg n t = CbvValue v -> typed [] v T.
  Proof. intros n t v T H Hv. exact (subject_red Sp sg Hsig _ _ _ _ H (eval_nested_reduces n t v Hv)). Qed.

  Lemma eval_red : forall n t v, eval_nested sg n t = CbvValue v -> red sg t v.
  Proof. intros n t v Hv. exact (eval_nested_reduces n t v Hv). Qed.

  (** *** Steps of the erased evaluator on an application *)

  Lemma eapp_tail_iota : forall K wf wa D s e2, espine_head (EApp wf wa) = EPrim D s ->
    eelim_iota se (EApp wf wa) = Some e2 -> eapp_tail se K wf wa = eval_erased se K e2.
  Proof. intros K wf wa D s e2 H1 H2. unfold eapp_tail. cbv zeta. rewrite H1, H2. reflexivity. Qed.

  Lemma eapp_tail_fix : forall K wf wa k b, espine_head (EApp wf wa) = EFix k b ->
    length (espine_args (EApp wf wa)) = S k ->
    eapp_tail se K wf wa = eval_erased se K (eapps (esubst1 b (EFix k b)) (espine_args (EApp wf wa))).
  Proof. intros K wf wa k b H1 H2. unfold eapp_tail. cbv zeta. rewrite H1, H2, Nat.eqb_refl. reflexivity. Qed.

  Lemma eapp_tail_fix_partial : forall K wf wa k b, espine_head (EApp wf wa) = EFix k b ->
    length (espine_args (EApp wf wa)) < S k -> eapp_tail se K wf wa = CbvValue (EApp wf wa).
  Proof.
    intros K wf wa k b H1 H2. unfold eapp_tail. cbv zeta. rewrite H1.
    replace (Nat.eqb _ _) with false by (symmetry; apply Nat.eqb_neq; lia).
    replace (Nat.ltb _ _) with true by (symmetry; apply Nat.ltb_lt; lia). reflexivity.
  Qed.

  Lemma eapp_tail_ctor : forall K wf wa D c, espine_head (EApp wf wa) = ECtor D c ->
    eapp_tail se K wf wa = CbvValue (EApp wf wa).
  Proof. intros K wf wa D c H. unfold eapp_tail. cbv zeta. rewrite H. reflexivity. Qed.

  (** An instance with active rules below its arity is a value. *)
  Lemma eapp_tail_prim_partial : forall K es wa D s d, elim_head sg (Const (Elim D s)) = Some (D, s, d) ->
    s <> Prp -> S (length es) < elim_arity d ->
    eapp_tail se K (eapps (EPrim D s) es) wa = CbvValue (EApp (eapps (EPrim D s) es) wa).
  Proof.
    intros K es wa D s d Hh Hs Hl. destruct (elim_head_spec _ _ _ _ _ _ Hh) as (_ & _ & (A & Hel) & Hd).
    pose proof (env_elims _ _ Henv _ _ _ _ Hs Hel) as Hk.
    destruct (efind_elim se D s) as [kind|] eqn:Ek; [ | contradiction].
    pose proof (env_inds _ _ Henv _ _ Hd) as Hi.
    assert (Hhd : espine_head (EApp (eapps (EPrim D s) es) wa) = EPrim D s)
      by (cbn [espine_head]; rewrite espine_head_eapps; reflexivity).
    assert (Hargs : espine_args (EApp (eapps (EPrim D s) es) wa) = es ++ [wa])
      by (cbn [espine_args]; rewrite espine_args_eapps; reflexivity).
    unfold eapp_tail. cbv zeta. rewrite Hhd.
    unfold eelim_iota, eelim_partial. rewrite Hhd, Ek, Hi, Hargs, earity_erase.
    replace (Nat.eqb _ _) with false by (symmetry; apply Nat.eqb_neq; rewrite length_app; cbn; lia).
    replace (Nat.ltb _ _) with true by (symmetry; apply Nat.ltb_lt; rewrite length_app; cbn; lia).
    reflexivity.
  Qed.

  Lemma ecase_iota_ctor : forall D d c i cd es bs' b', sig_ind sg D = Some d ->
    find_ctor (ind_ctors d) c = Some (i, cd) ->
    length es = length (ind_params d) + length (ctor_fields cd) -> nth_error bs' i = Some b' ->
    ecase_iota se D (eapps (ECtor D c) es) bs' = Some (eapps b' (skipn (length (ind_params d)) es)).
  Proof.
    intros D d c i cd es bs' b' Hd Hc Hl Hb. unfold ecase_iota. rewrite espine_head_eapps.
    cbn [espine_head]. rewrite String.eqb_refl, (env_inds _ _ Henv _ _ Hd).
    unfold erase_ind. cbn [eind_ctors eind_params]. rewrite (efind_ctor_erase _ _ _ _ Hc).
    cbn [ector_fields]. rewrite espine_args_eapps. cbn [espine_args app]. rewrite length_map, Hl, Nat.eqb_refl, Hb.
    reflexivity.
  Qed.

  Lemma ecase_iota_unit : forall c', ecase_iota se prim_unit (ECtor prim_unit "tt") [c'] = Some c'.
  Proof. intros c'. unfold ecase_iota. cbn [espine_head]. rewrite String.eqb_refl, (env_unit _ _ Henv). reflexivity. Qed.

  Lemma ecase_iota_true : forall x' y', ecase_iota se prim_bool (ECtor prim_bool "true") [x'; y'] = Some x'.
  Proof. intros x' y'. unfold ecase_iota. cbn [espine_head]. rewrite String.eqb_refl, (env_bool _ _ Henv). reflexivity. Qed.

  Lemma ecase_iota_false : forall x' y', ecase_iota se prim_bool (ECtor prim_bool "false") [x'; y'] = Some y'.
  Proof. intros x' y'. unfold ecase_iota. cbn [espine_head]. rewrite String.eqb_refl, (env_bool _ _ Henv). reflexivity. Qed.

  (** *** The simulation *)

  Theorem simulation : forall n t T e v, erases [] t T e -> eval_nested sg n t = CbvValue v ->
    exists m w, eval_erased se m e = CbvValue w /\ erases [] v T w.
  Proof.
    induction n as [|n IHn]; intros t T e v H Hev; [discriminate Hev | ].
    remember (@nil term) as G eqn:EG in H. revert v Hev EG.
    induction H as
      [ G t T Ht HE
      | G t A B s e He IHe HB Hc
      | G n0 T Ht
      | G A B b s b' Hb _ HP
      | G f u A B f' u' Hf _ Hu _
      | G f u A B f' Hf _ Hu Hip
      | G t A s e HA He _
      | G f T Ht
      | G D c T Ht
      | G D s T Ht Hs
      | G T Ht | G T Ht | G T Ht
      | G C e0 s e' HC He _
      | G C c u s c' u' HC Hc _ Hu _
      | G C x y b s x' y' b' HC Hx _ Hy _ Hb _
      | G A B a b s a' b' HS Ha _ Hb _
      | G p A B p' Hp _
      | G p A B p' Hp _
      | G D s P x bs d ps us x' bs' Hdec Hd Hel Hlp Hlu Hsort Hx _ HP Hbs
      | G D s P x d ps us x' Hdec Hd Hel Hlp Hlu Hsort Helim Hctors Hx _ HP
      | G D s P x b d c ps us b' Hdec Hd Hel Hlp Hlu Hsort Helim Hctors Hx HP Hb _
      | G A k b s D b' HA Hsa Hne Hb _ Hg ];
      intros v Hev EG; subst G.
    (* [□]: the value has the same erasable type *)
    - exists 1, EBox. split; [reflexivity | apply X_Box; [exact (eval_typed _ _ _ _ Ht Hev) | exact HE]].
    (* a conversion *)
    - destruct (IHe v Hev eq_refl) as (m & w & Hw & Hvw).
      exists m, w. split; [exact Hw | exact (X_Conv _ _ _ _ _ _ _ _ Hvw HB Hc)].
    (* a variable: none in the empty context *)
    - cbn [eval_nested eval_node] in Hev. discriminate Hev.
    (* a λ: a value *)
    - cbn [eval_nested eval_node] in Hev. injection Hev as <-.
      exists 1, (ELam b'). split; [reflexivity | exact (X_Lam _ _ _ _ _ _ _ _ Hb HP)].
    (* an application *)
    - pose proof Hev as Hev0.
      cbn [eval_nested eval_node] in Hev. unfold nested_app in Hev.
      destruct (eval_nested sg n f) as [vf|uf|] eqn:Ef; try discriminate Hev.
      destruct (eval_nested sg n u) as [va|ua|] eqn:Eu; try discriminate Hev.
      destruct (IHn _ _ _ _ Hf Ef) as (m1 & wf & Hwf & Hvf).
      destruct (IHn _ _ _ _ Hu Eu) as (m2 & wa & Hwa & Hva).
      pose proof (eval_erased_evalue se _ _ _ Hwf) as Evf. pose proof (eval_erased_evalue se _ _ _ Hwa) as Eva.
      pose proof (eval_nested_svalue sg _ _ _ Ef) as Svf.
      pose proof (proj1 (erases_typed Sp sg) _ _ _ _ Hf) as Tf.
      pose proof (proj1 (erases_typed Sp sg) _ _ _ _ Hu) as Tu.
      pose proof (eval_typed _ _ _ _ Tu Eu) as Tva.
      destruct (pi_cod_typed Sp sg Hsig _ _ _ _ _ Tf Tu) as [sB HB].
      assert (HcB : subst1 B va ≡ subst1 B u) by (apply conv_sym, red_conv, red_subst1_arg, (eval_red _ _ _ Eu)).
      assert (Hlift : forall K, m1 + m2 <= K -> eval_erased se K f' = CbvValue wf /\ eval_erased se K u' = CbvValue wa)
        by (intros K HK; split; [apply (eval_erased_mono se m1); [lia | exact Hwf]
                                | apply (eval_erased_mono se m2); [lia | exact Hwa]]).
      destruct (eterm_eq_dec wf EBox) as [-> | Hwfb].
      { (* the function erased to [□]: the application too *)
        exists (S (m1 + m2)), EBox. split.
        - destruct (Hlift (m1 + m2) (le_n _)) as [H1 H2]. rewrite (eval_erased_app se _ _ _ _ _ H1 H2). reflexivity.
        - apply X_Box; [exact (eval_typed _ _ _ _ (T_App _ _ _ _ _ _ _ Tf Tu) Hev0) | ].
          destruct (svalue_shape _ Svf) as [Sa Sc].
          exact (erasable_pi_cod sg Hsig _ _ _ _ (box_erasable sg _ _ _ _ Hvf eq_refl Sa Sc) Tu). }
      assert (Hlam : (exists b0, vf = Lam b0) \/ (forall b0, vf <> Lam b0))
        by (destruct vf; try (right; intros ? E; discriminate E); left; eauto).
      destruct Hlam as [[b0 ->] | Hnl].
      { (* β *)
        cbn [nested_apply] in Hev.
        destruct (erases_lam_inv sg _ _ _ _ Hvf) as [(E & _) | (A' & B' & s' & b' & -> & Hb & HP & HT)];
          [contradiction | ].
        apply ctype_conv_of, pi_inj in HT as [HA HB'].
        destruct (inv_pi Sp sg _ _ _ _ HP) as (s1 & _ & _ & HA' & _ & _ & _).
        pose proof (X_Conv _ _ _ _ _ _ _ _ Hva HA' (conv_sym _ _ HA)) as Hva'.
        pose proof (erases_subst1 Sp sg _ _ _ _ _ _ _ Hb Hva') as Hsub.
        destruct (IHn _ _ _ _ Hsub Hev) as (m3 & w & Hw & Hvw).
        exists (S (m1 + m2 + m3)), w. split.
        - destruct (Hlift (m1 + m2 + m3) ltac:(lia)) as [H1 H2]. rewrite (eval_erased_app se _ _ _ _ _ H1 H2).
          apply (eval_erased_mono se m3); [lia | exact Hw].
        - eapply X_Conv; [exact Hvw | exact HB | ]. eapply conv_trans; [apply conv_subst; exact HB' | exact HcB]. }
      assert (Hn : nested_apply sg (eval_nested sg n) vf va =
                   match spine_iota sg (App vf va) with
                   | Some r => eval_nested sg n r
                   | None => if spine_value sg (App vf va) then CbvValue (App vf va) else CbvStuck (App vf va)
                   end) by (unfold nested_apply; destruct vf; try reflexivity; exfalso; exact (Hnl _ eq_refl)).
      rewrite Hn in Hev. clear Hn.
      assert (Hwfl : forall b0, wf <> ELam b0).
      { intros b0 E. subst wf. destruct (elam_source sg _ _ _ _ Hvf _ eq_refl Svf) as [b1 E1]. exact (Hnl _ E1). }
      destruct (erases_spine_inv sg (spine_args vf) [] (spine_head vf) _ wf ltac:(rewrite apps_spine; exact Hvf)
                  Evf Hwfb) as (H0 & eh & es & Ewf & Hles & Hh & Hehb).
      assert (Happ : forall K, m1 + m2 <= K -> eval_erased se (S K) (EApp f' u') = eapp_tail se K wf wa).
      { intros K HK. destruct (Hlift K HK) as [H1 H2]. rewrite (eval_erased_app se _ _ _ _ _ H1 H2).
        clear -Hwfb Hwfl. destruct wf; try reflexivity; exfalso; [exact (Hwfb eq_refl) | exact (Hwfl _ eq_refl)]. }
      assert (Hvapp : erases [] (App vf va) (subst1 B va) (EApp wf wa)) by exact (X_App _ _ _ _ _ _ _ _ _ Hvf Hva).
      assert (Hhd : espine_head (EApp wf wa) = espine_head eh)
        by (rewrite Ewf; cbn [espine_head]; apply espine_head_eapps).
      assert (Hargs : espine_args (EApp wf wa) = espine_args eh ++ es ++ [wa])
        by (rewrite Ewf; cbn [espine_args]; rewrite espine_args_eapps, app_assoc; reflexivity).
      assert (Evapp : evalue (EApp wf wa)) by (constructor; assumption).
      assert (Hhv : spine_head (App vf va) = spine_head vf) by reflexivity.
      assert (Hav : spine_args (App vf va) = spine_args vf ++ [va]) by apply spine_args_App.
      destruct (spine_iota sg (App vf va)) as [r|] eqn:Hsp.
      + unfold spine_iota in Hsp. destruct (iota sg (App vf va)) as [r'|] eqn:Hi.
        * (* ι of an instance: by the premise *)
          injection Hsp as <-. pose proof Hi as Hi0. unfold iota in Hi0.
          destruct (elim_view sg (App vf va)) as [[[D s] d]|] eqn:Ev; [ | discriminate Hi0].
          destruct (elim_view_spec _ _ _ _ _ Ev) as (Eh & _ & _).
          rewrite Hhv in Eh. rewrite Eh in Hh.
          destruct (erases_const_inv sg _ _ _ _ Hh) as [E | [(f0 & E & _) | [(D' & c & E & _) | (D' & s' & E & -> & Hs)]]];
            [contradiction | discriminate E | discriminate E | ]. injection E as <- <-.
          assert (Hhd' : espine_head (EApp wf wa) = EPrim D s) by (rewrite Hhd; reflexivity).
          destruct (env_iota _ _ Henv _ _ _ _ Hi Hvapp Evapp (ex_intro _ D (ex_intro _ s Hhd'))) as (e2 & He2 & Hr).
          destruct (IHn _ _ _ _ Hr Hev) as (m3 & w & Hw & Hvw).
          exists (S (m1 + m2 + m3)), w. split.
          -- rewrite (Happ (m1 + m2 + m3) ltac:(lia)), (eapp_tail_iota _ _ _ _ _ _ Hhd' He2).
             apply (eval_erased_mono se m3); [lia | exact Hw].
          -- eapply X_Conv; [exact Hvw | exact HB | exact HcB].
        * (* the unfolding of a fix: the erased one unfolds whatever its argument *)
          pose proof Hsp as Hfu. unfold fix_unfold in Hfu.
          destruct (fix_view (App vf va)) as [[[Af k] bf]|] eqn:Ev; [ | discriminate Hfu].
          destruct (fix_view_spec _ _ _ _ Ev) as [Eh Hlen].
          unfold fix_at in Hfu.
          assert (Er : r = apps (subst1 bf (Fix Af k bf)) (spine_args (App vf va))).
          { revert Hfu. destruct (spine_head (last (spine_args (App vf va)) (Var 0))); try discriminate.
            destruct g; try discriminate. intros E. injection E as <-. reflexivity. }
          subst r. rewrite Hhv in Eh. rewrite Eh in Hh.
          destruct (erases_fix_inv sg _ _ _ _ _ _ Hh) as [(E & _) | (sf & Df & bf' & -> & HAf & Hsaf & Hnef & Hbf & Hgf & HTf)];
            [contradiction | ].
          assert (Hlen' : length (espine_args (EApp wf wa)) = S k).
          { rewrite Hargs, <- Hlen, Hav. cbn [espine_args app]. rewrite !length_app, Hles. reflexivity. }
          set (rho := fun e => match e with EFix k' b' => esubst1 b' (EFix k' b') | _ => e end).
          assert (Hrel : erases [] (apps (subst1 bf (Fix Af k bf)) (spine_args (App vf va))) (subst1 B va)
                           (rho_spine rho (length (spine_args (App vf va))) (EApp wf wa))).
          { apply (erases_replace_head sg rho (spine_args (App vf va)) [] (Fix Af k bf)).
            - rewrite <- Eh, <- Hhv, apps_spine. exact Hvapp.
            - intros H1 e1 He1.
              destruct (erases_fix_inv sg _ _ _ _ _ _ He1) as [(-> & HE1) | (s2 & D2 & b2 & -> & HA2 & Hsa2 & Hne2 & Hb2 & Hg2 & HT2)].
              + apply X_Box; [ | exact HE1].
                exact (sr_fix_body Sp sg _ _ _ _ _ (proj1 (erases_typed Sp sg) _ _ _ _ He1)).
              + unfold rho. pose proof (X_Fix _ _ _ _ _ _ _ _ _ HA2 Hsa2 Hne2 Hb2 Hg2) as HF.
                pose proof (erases_subst1 Sp sg _ _ _ _ _ _ _ Hb2 HF) as H3. rewrite subst1_lift in H3.
                exact (erases_ctype sg _ _ _ _ _ H3 HT2).
            - intros H1 Ht1. exact (sr_fix_body Sp sg _ _ _ _ _ Ht1).
            - intros l (D2 & s2 & d2 & E & _). rewrite spine_head_apps in E. discriminate E. }
          assert (Erho : rho_spine rho (length (spine_args (App vf va))) (EApp wf wa) =
                         eapps (esubst1 bf' (EFix k bf')) (es ++ [wa])).
          { rewrite Ewf, <- eapps_snoc.
            replace (length (spine_args (App vf va))) with (length (es ++ [wa])) by (rewrite Hav, !length_app, Hles; reflexivity).
            rewrite rho_spine_eapps. reflexivity. }
          rewrite Erho in Hrel.
          destruct (IHn _ _ _ _ Hrel Hev) as (m3 & w & Hw & Hvw).
          exists (S (m1 + m2 + m3)), w. split.
          -- rewrite (Happ (m1 + m2 + m3) ltac:(lia)), (eapp_tail_fix _ _ _ k bf' ltac:(rewrite Hhd; reflexivity) Hlen').
             replace (espine_args (EApp wf wa)) with (es ++ [wa]) by (rewrite Hargs; reflexivity).
             apply (eval_erased_mono se m3); [lia | exact Hw].
          -- eapply X_Conv; [exact Hvw | exact HB | exact HcB].
      + (* no contraction: a value, a constructor, an instance or a fix below its arity *)
        destruct (spine_value sg (App vf va)) eqn:Hsv; [ | discriminate Hev]. injection Hev as <-.
        assert (Hvalw : forall K, eapp_tail se K wf wa = CbvValue (EApp wf wa)).
        { intros K. unfold spine_value, head_value in Hsv. rewrite Hhv, Hav, length_app in Hsv. cbn [length] in Hsv.
          remember (spine_head vf) as h eqn:Eh.
          destruct h; cbn [is_inert orb] in Hsv; unfold head_arity, elim_head in Hsv; try discriminate Hsv.
          - (* a constant *)
            destruct (erases_const_inv sg _ _ _ _ Hh) as [E | [(f0 & E & ->) | [(D' & c & E & ->) | (D' & s' & E & -> & Hs)]]];
              [contradiction | | | ].
            + subst g. discriminate Hsv.
            + exact (eapp_tail_ctor _ _ _ _ _ Hhd).
            + subst g. rewrite Ewf.
              destruct (sig_elim sg D' s') as [[A0 [|]]|] eqn:Hel; try discriminate Hsv.
              destruct (sig_ind sg D') as [d|] eqn:Hd; [ | discriminate Hsv].
              apply Nat.ltb_lt in Hsv.
              assert (Hact : elim_head sg (Const (Elim D' s')) = Some (D', s', d))
                by (unfold elim_head; rewrite Hel, Hd; reflexivity).
              exact (eapp_tail_prim_partial _ _ _ _ _ _ Hact Hs ltac:(rewrite Hles; lia)).
          - (* a fix *)
            destruct (erases_fix_inv sg _ _ _ _ _ _ Hh) as [(E & _) | (sf & Df & bf' & -> & _)]; [contradiction | ].
            apply Nat.ltb_lt in Hsv.
            apply (eapp_tail_fix_partial _ _ _ n0 bf'); [rewrite Hhd; reflexivity | ].
            rewrite Hargs. cbn [espine_args app]. rewrite length_app, Hles. cbn [length]. lia. }
        exists (S (m1 + m2)), (EApp wf wa). split.
        * rewrite (Happ _ (le_n _)). apply Hvalw.
        * eapply X_Conv; [exact Hvapp | exact HB | exact HcB].
    (* an argument at the position of an index, erased to [□] *)
    - pose proof Hev as Hev0.
      cbn [eval_nested eval_node] in Hev. unfold nested_app in Hev.
      destruct (eval_nested sg n f) as [vf|uf|] eqn:Ef; try discriminate Hev.
      destruct (eval_nested sg n u) as [va|ua|] eqn:Eu; try discriminate Hev.
      destruct (IHn _ _ _ _ Hf Ef) as (m1 & wf & Hwf & Hvf).
      pose proof (eval_erased_evalue se _ _ _ Hwf) as Evf.
      pose proof (eval_nested_svalue sg _ _ _ Ef) as Svf.
      pose proof (proj1 (erases_typed Sp sg) _ _ _ _ Hf) as Tf.
      pose proof (eval_typed _ _ _ _ Hu Eu) as Tva.
      destruct (pi_cod_typed Sp sg Hsig _ _ _ _ _ Tf Hu) as [sB HB].
      assert (HcB : subst1 B va ≡ subst1 B u) by (apply conv_sym, red_conv, red_subst1_arg, (eval_red _ _ _ Eu)).
      destruct Hip as (D & s & d & Eh & Hd & Hl1 & Hl2).
      pose proof (apps_spine f) as Ef'. rewrite Eh in Ef'.
      destruct (eval_elim_spine sg (spine_args f) n D s vf ltac:(rewrite Ef'; exact Ef)) as (vals & -> & Hlv).
      { intros D' s' d' He. destruct (elim_head_spec _ _ _ _ _ _ He) as (_ & _ & _ & Hd').
        rewrite Hd in Hd'. injection Hd' as <-. unfold elim_arity. lia. }
      assert (Hn : nested_apply sg (eval_nested sg n) (apps (Const (Elim D s)) vals) va =
                   match spine_iota sg (App (apps (Const (Elim D s)) vals) va) with
                   | Some r => eval_nested sg n r
                   | None => if spine_value sg (App (apps (Const (Elim D s)) vals) va)
                             then CbvValue (App (apps (Const (Elim D s)) vals) va)
                             else CbvStuck (App (apps (Const (Elim D s)) vals) va)
                   end)
        by (unfold nested_apply; destruct vals as [|x vals] using rev_ind; [reflexivity | rewrite apps_snoc; reflexivity]).
      rewrite Hn in Hev. clear Hn.
      rewrite spine_iota_head in Hev. unfold spine_value, head_value in Hev.
      rewrite <- !apps_snoc in Hev. rewrite !spine_head_apps, !spine_args_apps in Hev.
      cbn [spine_head spine_args spine_args_acc app is_inert orb] in Hev.
      unfold head_arity in Hev.
      destruct (elim_head sg (Const (Elim D s))) as [[[D' s'] d']|] eqn:Hact; [ | discriminate Hev].
      destruct (elim_head_spec _ _ _ _ _ _ Hact) as (-> & -> & _ & Hd'). rewrite Hd in Hd'. injection Hd' as <-.
      replace (Nat.eqb (length (vals ++ [va])) (elim_arity d)) with false in Hev
        by (symmetry; apply Nat.eqb_neq; rewrite length_app; cbn; unfold elim_arity; lia).
      replace (Nat.ltb (length (vals ++ [va])) (elim_arity d)) with true in Hev
        by (symmetry; apply Nat.ltb_lt; rewrite length_app; cbn; unfold elim_arity; lia).
      injection Hev as <-. rewrite apps_snoc.
      assert (Hip' : index_position sg (apps (Const (Elim D s)) vals)).
      { exists D, s, d. rewrite spine_head_apps, spine_args_apps. cbn [spine_head spine_args spine_args_acc app].
        rewrite Hlv. auto. }
      assert (Hvrel : erases [] (App (apps (Const (Elim D s)) vals) va) (subst1 B va) (EApp wf EBox))
        by exact (X_AppIndex _ _ _ _ _ _ _ _ Hvf Tva Hip').
      assert (Hbox : eval_erased se m1 EBox = CbvValue EBox) by (destruct m1; [discriminate Hwf | reflexivity]).
      destruct (eterm_eq_dec wf EBox) as [-> | Hwfb].
      + exists (S m1), EBox. split.
        * rewrite (eval_erased_app se _ _ _ _ _ Hwf Hbox). reflexivity.
        * apply X_Box.
          -- rewrite <- apps_snoc. exact (eval_typed _ _ _ _ (T_App _ _ _ _ _ _ _ Tf Hu) Hev0).
          -- destruct (svalue_shape _ Svf) as [Sa Sc].
             exact (erasable_pi_cod sg Hsig _ _ _ _ (box_erasable sg _ _ _ _ Hvf eq_refl Sa Sc) Hu).
      + destruct (erases_spine_inv sg vals [] (Const (Elim D s)) _ wf Hvf Evf Hwfb) as (H0 & eh & es & Ewf & Hles & Hh & Hehb).
        destruct (erases_const_inv sg _ _ _ _ Hh) as [E | [(f0 & E & _) | [(D' & c & E & _) | (D' & s' & E & -> & Hs)]]];
          [contradiction | discriminate E | discriminate E | ]. injection E as <- <-.
        exists (S m1), (EApp wf EBox). split.
        * rewrite (eval_erased_app se _ _ _ _ _ Hwf Hbox).
          assert (Hwfl : forall b0, wf <> ELam b0) by (rewrite Ewf; intros b0 E; destruct es using rev_ind; [discriminate E | rewrite eapps_snoc in E; discriminate E]).
          replace (match wf with ELam b0 => eval_erased se m1 (esubst1 b0 EBox) | EBox => CbvValue EBox | _ => eapp_tail se m1 wf EBox end)
            with (eapp_tail se m1 wf EBox)
            by (clear -Hwfb Hwfl; destruct wf; try reflexivity; exfalso; [exact (Hwfb eq_refl) | exact (Hwfl _ eq_refl)]).
          rewrite Ewf. apply (eapp_tail_prim_partial _ _ _ _ _ d Hact Hs).
          rewrite Hles, Hlv. unfold elim_arity. lia.
        * eapply X_Conv; [exact Hvrel | exact HB | exact HcB].
    (* an annotation, dropped *)
    - cbn [eval_nested eval_node] in Hev. destruct (IHn _ _ _ _ He Hev) as (m & w & Hw & Hvw). eauto.
    (* a δ-constant: its body, related by the premise *)
    - cbn [eval_nested eval_node sig_delta] in Hev.
      destruct (inv_const Sp sg _ _ _ Ht) as (A0 & _ & _ & Hty & HT).
      cbn [sig_type] in Hty. destruct (sig_def sg f) as [[A1 b]|] eqn:Edef; [ | discriminate Hty].
      cbn [option_map fst snd] in Hty, Hev. injection Hty as <-.
      destruct (env_defs _ _ Henv _ _ _ Edef) as (b' & Hb' & Hrel).
      destruct (IHn _ _ _ _ Hrel Hev) as (m & w & Hw & Hvw).
      exists (S m), w. split; [cbn [eval_erased]; rewrite Hb'; exact Hw | exact (erases_ctype sg _ _ _ _ _ Hvw HT)].
    (* constructors and instances: values *)
    - cbn [eval_nested eval_node sig_delta] in Hev. injection Hev as <-.
      exists 1, (ECtor D c). split; [reflexivity | exact (X_Ctor _ _ _ _ _ _ Ht)].
    - cbn [eval_nested eval_node sig_delta] in Hev. injection Hev as <-.
      exists 1, (EPrim D s). split; [reflexivity | exact (X_Elim _ _ _ _ _ _ Ht Hs)].
    - cbn [eval_nested eval_node] in Hev. injection Hev as <-.
      eexists 1, _. split; [reflexivity | exact (X_Tt _ _ _ _ Ht)].
    - cbn [eval_nested eval_node] in Hev. injection Hev as <-.
      eexists 1, _. split; [reflexivity | exact (X_True _ _ _ _ Ht)].
    - cbn [eval_nested eval_node] in Hev. injection Hev as <-.
      eexists 1, _. split; [reflexivity | exact (X_False _ _ _ _ Ht)].
    (* the eliminator of Void: stuck *)
    - cbn [eval_nested eval_node] in Hev. destruct (eval_nested sg n e0); discriminate Hev.
    (* the eliminator of Unit *)
    - cbn [eval_nested eval_node] in Hev.
      destruct (eval_nested sg n u) as [vu|uu|] eqn:Eu; try discriminate Hev.
      destruct vu; try discriminate Hev.
      destruct (IHn _ _ _ _ Hu Eu) as (m1 & wu & Hwu & Hvu).
      destruct (erases_prim_ctor_inv sg _ _ _ _ Hvu (or_introl eq_refl)) as [(-> & HE) | [(_ & ->) | [(E & _) | (E & _)]]];
        [exfalso; exact (unit_not_erasable sg Hsig _ HE) | | discriminate E | discriminate E].
      destruct (IHn _ _ _ _ Hc Hev) as (m2 & w & Hw & Hvw).
      exists (S (m1 + m2)), w. split.
      + cbn [eval_erased]. rewrite (eval_erased_mono se m1 (m1 + m2) _ _ ltac:(lia) Hwu). cbv beta iota.
        rewrite ecase_iota_unit. cbv beta iota. apply (eval_erased_mono se m2); [lia | exact Hw].
      + pose proof (proj1 (erases_typed Sp sg) _ _ _ _ Hu) as Tu.
        eapply X_Conv; [exact Hvw | exact (T_App _ _ _ _ _ _ _ HC Tu) | ].
        apply conv_app_arg, conv_sym, red_conv, (eval_red _ _ _ Eu).
    (* the eliminator of Bool *)
    - cbn [eval_nested eval_node] in Hev.
      destruct (eval_nested sg n b) as [vb|ub|] eqn:Eb; try discriminate Hev.
      destruct (IHn _ _ _ _ Hb Eb) as (m1 & wb & Hwb & Hvb).
      pose proof (proj1 (erases_typed Sp sg) _ _ _ _ Hb) as Tb.
      destruct vb; try discriminate Hev.
      + destruct (erases_prim_ctor_inv sg _ _ _ _ Hvb (or_intror (or_introl eq_refl)))
          as [(-> & HE) | [(E & _) | [(_ & ->) | (E & _)]]];
          [exfalso; exact (bool_not_erasable sg Hsig _ HE) | discriminate E | | discriminate E].
        destruct (IHn _ _ _ _ Hx Hev) as (m2 & w & Hw & Hvw).
        exists (S (m1 + m2)), w. split.
        * cbn [eval_erased]. rewrite (eval_erased_mono se m1 (m1 + m2) _ _ ltac:(lia) Hwb). cbv beta iota.
          rewrite ecase_iota_true. cbv beta iota. apply (eval_erased_mono se m2); [lia | exact Hw].
        * eapply X_Conv; [exact Hvw | exact (T_App _ _ _ _ _ _ _ HC Tb) | ].
          apply conv_app_arg, conv_sym, red_conv, (eval_red _ _ _ Eb).
      + destruct (erases_prim_ctor_inv sg _ _ _ _ Hvb (or_intror (or_intror eq_refl)))
          as [(-> & HE) | [(E & _) | [(E & _) | (_ & ->)]]];
          [exfalso; exact (bool_not_erasable sg Hsig _ HE) | discriminate E | discriminate E | ].
        destruct (IHn _ _ _ _ Hy Hev) as (m2 & w & Hw & Hvw).
        exists (S (m1 + m2)), w. split.
        * cbn [eval_erased]. rewrite (eval_erased_mono se m1 (m1 + m2) _ _ ltac:(lia) Hwb). cbv beta iota.
          rewrite ecase_iota_false. cbv beta iota. apply (eval_erased_mono se m2); [lia | exact Hw].
        * eapply X_Conv; [exact Hvw | exact (T_App _ _ _ _ _ _ _ HC Tb) | ].
          apply conv_app_arg, conv_sym, red_conv, (eval_red _ _ _ Eb).
    (* a pair *)
    - cbn [eval_nested eval_node] in Hev.
      destruct (eval_nested sg n a) as [va|ua|] eqn:Ea; try discriminate Hev.
      destruct (eval_nested sg n b) as [vb|ub|] eqn:Eb; try discriminate Hev.
      injection Hev as <-.
      destruct (IHn _ _ _ _ Ha Ea) as (m1 & wa & Hwa & Hva).
      destruct (IHn _ _ _ _ Hb Eb) as (m2 & wb & Hwb & Hvb).
      exists (S (m1 + m2)), (EPair wa wb). split.
      + cbn [eval_erased]. rewrite (eval_erased_mono se m1 (m1 + m2) _ _ ltac:(lia) Hwa), (eval_erased_mono se m2 (m1 + m2) _ _ ltac:(lia) Hwb).
        reflexivity.
      + pose proof (eval_typed _ _ _ _ (proj1 (erases_typed Sp sg) _ _ _ _ Ha) Ea) as Tva.
        destruct (inv_sigma Sp sg _ _ _ _ HS) as (s1 & s2 & _ & _ & HB & _ & _).
        pose proof (typing_subst1 Sp sg _ _ _ _ _ Tva HB) as HBva. change (subst1 (Srt s2) va) with (Srt s2) in HBva.
        apply (X_Pair _ _ _ _ _ _ _ _ _ _ HS Hva).
        eapply X_Conv; [exact Hvb | exact HBva | ].
        apply red_conv, red_subst1_arg, (eval_red _ _ _ Ea).
    (* the projections *)
    - cbn [eval_nested eval_node] in Hev.
      destruct (eval_nested sg n p) as [vp|up|] eqn:Ep; try discriminate Hev.
      destruct vp; try discriminate Hev. injection Hev as <-.
      destruct (IHn _ _ _ _ Hp Ep) as (m1 & wp & Hwp & Hvp).
      destruct (erases_pair_inv sg _ _ _ _ _ Hvp) as [(-> & HE) | (A' & B' & s' & a' & b' & -> & HS & Ha & Hb & HT)];
        [exfalso; exact (sigma_not_erasable sg Hsig _ _ _ HE) | ].
      apply ctype_conv_of, sigma_inj in HT as [HA _].
      destruct (sigma_dom_typed Sp sg Hsig _ _ _ _ (proj1 (erases_typed Sp sg) _ _ _ _ Hp)) as [s1 HA1].
      exists (S m1), a'. split; [cbn [eval_erased]; rewrite Hwp; reflexivity | exact (X_Conv _ _ _ _ _ _ _ _ Ha HA1 HA)].
    - cbn [eval_nested eval_node] in Hev.
      destruct (eval_nested sg n p) as [vp|up|] eqn:Ep; try discriminate Hev.
      destruct vp; try discriminate Hev. injection Hev as <-.
      destruct (IHn _ _ _ _ Hp Ep) as (m1 & wp & Hwp & Hvp).
      destruct (erases_pair_inv sg _ _ _ _ _ Hvp) as [(-> & HE) | (A' & B' & s' & a' & b' & -> & HS & Ha & Hb & HT)];
        [exfalso; exact (sigma_not_erasable sg Hsig _ _ _ HE) | ].
      apply ctype_conv_of, sigma_inj in HT as [_ HBB].
      pose proof (proj1 (erases_typed Sp sg) _ _ _ _ Hp) as Tp.
      destruct (sigma_cod_typed Sp sg Hsig _ _ _ _ _ Tp (T_Fst _ _ _ _ _ _ Tp)) as [s2 HB2].
      exists (S m1), b'. split; [cbn [eval_erased]; rewrite Hwp; reflexivity | ].
      eapply X_Conv; [exact Hb | exact HB2 | ].
      eapply conv_trans; [apply conv_subst; exact HBB | ].
      apply conv_sym, red_conv, red_subst1_arg.
      eapply rt_trans; [apply red_fst; exact (eval_red _ _ _ Ep) | apply rt_step, R_FstPair].
    (* a match on data: ι on the constructor reached by the scrutinee *)
    - cbn [eval_nested eval_node] in Hev.
      destruct (eval_nested sg n x) as [vx|ux|] eqn:Ex; try discriminate Hev.
      destruct (case_iota sg (Case D s P vx bs)) as [r|] eqn:Hci; [ | discriminate Hev].
      pose proof Hci as Hci0. cbn [case_iota] in Hci0. rewrite Hd in Hci0.
      destruct (ctor_view D d vx) as [[[i cd] xs]|] eqn:Ev; [ | discriminate Hci0].
      destruct (nth_error bs i) as [b|] eqn:Eb; [ | discriminate Hci0]. cbn [option_map] in Hci0. injection Hci0 as <-.
      destruct (ctor_view_spec _ _ _ _ _ _ Ev) as (c & ps' & Evx & Hc & Hlp' & Hlx).
      destruct (IHn _ _ _ _ Hx Ex) as (m1 & wx & Hwx & Hvx).
      pose proof (eval_erased_evalue se _ _ _ Hwx) as Evwx.
      pose proof (eval_nested_svalue sg _ _ _ Ex) as Svx.
      pose proof (proj1 (erases_typed Sp sg) _ _ _ _ Hx) as Tx.
      destruct (validity_type Sp sg Hsig _ _ _ Tx (fun s1 => apps_const_not_srt _ _ s1)) as [sx HX].
      pose proof (case_type_typed Sp sg Hsig _ _ _ _ _ _ _ _ _ Hd Hlp Hlu Tx HP HX) as HPT.
      assert (Hwxb : wx <> EBox).
      { intros ->. destruct (svalue_shape _ Svx) as [Sa Sc].
        apply (ind_not_erasable sg Hsig [] D d (ps ++ us) Hd Hsort ltac:(rewrite !length_app; lia)).
        exact (box_erasable sg _ _ _ _ Hvx eq_refl Sa Sc). }
      subst vx.
      destruct (sig_ind_closed _ _ _ Hd) as [_ Hcs].
      pose proof (find_ctor_closed _ _ _ _ _ Hcs Hc) as Hcc. unfold ctor_closed in Hcc.
      apply andb_prop in Hcc as [Hfc Hic].
      pose proof (sig_ind_name _ _ _ Hd) as Hname. pose proof (find_ctor_name _ _ _ _ Hc) as Hcname.
      set (FT := field_types (ind_name d) (length (ind_params d)) 0 (ctor_fields cd)) in *.
      assert (Hty : sig_type sg (Ctor D c) = Some (ctor_type d cd)) by (cbn [sig_type]; rewrite Hd, Hc; reflexivity).
      destruct (const_type_typed Sp sg Hsig [] _ _ (W_Nil _ _) Hty) as [s0 Hs0].
      unfold ctor_type in Hs0. cbv zeta in Hs0. fold FT in Hs0.
      assert (Hl : length (ind_params d ++ FT) = length (ps' ++ xs))
        by (unfold FT; rewrite !length_app, field_types_length; lia).
      destruct (erases_apps_inv sg (ps' ++ xs) [] (Const (Ctor D c)) _ wx (ind_params d ++ FT)
                  (apps (Const (Ind (ind_name d))) (vars (length (ctor_fields cd)) (length (ind_params d)) ++ ctor_indices cd))
                  s0 (ECtor D c) Hl Hvx Evwx Hwxb) as (es & Ewx & Hes & Hcv).
      { intros H0 eh Hh Hne.
        destruct (erases_const_inv sg _ _ _ _ Hh) as [-> | [(f0 & E & _) | [(D' & c' & E & ->) | (D' & s' & E & _ & _)]]];
          [contradiction | discriminate E | | discriminate E].
        injection E as <- <-. split; [ | reflexivity].
        exact (const_head Sp sg _ _ _ Hty _ (proj1 (erases_typed Sp sg) _ _ _ _ Hh)). }
      { intros l (D' & s' & d' & E & _). rewrite spine_head_apps in E. discriminate E. }
      { exact Hs0. }
      rewrite subst_apps, map_app in Hcv. cbn [subst] in Hcv.
      rewrite <- Hlx, <- Hlp', map_tsub_vars, Hname in Hcv.
      apply conv_ind_spine in Hcv. apply forall2_app_split in Hcv as [Hps Hus]; [ | lia].
      destruct (eargs_app sg ps' [] (ind_params d) FT xs es (eq_sym Hlp') Hes) as [_ Hxs].
      destruct (erases_branches_nth _ _ _ _ _ _ _ _ Hbs i cd b (find_ctor_nth_error _ _ _ _ Hc) Eb) as (b' & Eb' & Hb').
      assert (Hbt : case_branch_type d ps P cd =
        pis (subst_tele (tsub ps) FT)
            (apps (lift (length xs) P)
               (map (subst (upn (length xs) (tsub ps))) (ctor_indices cd) ++
                [apps (Const (Ctor D c)) (map (lift (length xs)) ps ++ vars 0 (length xs))]))).
      { unfold case_branch_type. cbv zeta. fold FT. rewrite Hname, Hcname, Hlx.
        rewrite (inst_tele_tsub FT ps 0).
        2: { unfold FT. rewrite Nat.add_0_l, Hlp.
             pose proof (field_types_closed (ind_name d) _ _ 0 ltac:(rewrite Nat.add_0_r; exact Hfc)) as Hft.
             rewrite Nat.add_0_r in Hft. exact Hft. }
        f_equal. f_equal. f_equal. apply map_ext_in. intros t0 Ht0. apply inst_env_tsub.
        rewrite Hlp, Nat.add_comm. exact (proj1 (List.forallb_forall _ _) Hic t0 Ht0). }
      rewrite Hbt in Hb'.
      pose proof (proj1 (erases_typed Sp sg) _ _ _ _ Hb') as Tb.
      destruct (validity_type Sp sg Hsig _ _ _ Tb (pis_apps_not_srt _ _ _ _)) as [sb HBT].
      pose proof (eargs_conv sg _ _ _ _ Hxs _ _ _ (conv_subst_tele_tsub sg _ _ Hps FT 0) HBT) as Hxs'.
      pose proof (erases_apps sg _ _ _ _ _ _ _ Hxs' Hb') as H1.
      rewrite subst_apps, subst_tsub_lift, map_app, map_map in H1. cbn [map] in H1.
      rewrite subst_apps, map_app, map_tsub_lift, map_tsub_vars0 in H1. cbn [subst] in H1.
      rewrite (map_ext _ _ (fun t0 => subst_subst t0 (tsub xs) (upn (length xs) (tsub ps)))) in H1.
      rewrite (map_ext _ (subst (tsub (ps ++ xs)))) in H1 by (intros t0; apply subst_ext; apply tsub_app).
      assert (Hcx : apps (Const (Ctor D c)) (ps' ++ xs) ≡ x) by (apply conv_sym, red_conv, (eval_red _ _ _ Ex)).
      assert (Hpx : Forall2 (conv sg) (ps ++ xs) (ps' ++ xs))
        by (apply Forall2_app; [apply forall2_conv_sym, Hps | apply forall2_conv_refl]).
      assert (HcT : apps P (map (subst (tsub (ps ++ xs))) (ctor_indices cd) ++ [apps (Const (Ctor D c)) (ps ++ xs)])
                    ≡ apps P (us ++ [x])).
      { apply conv_apps; [apply conv_refl | ]. apply Forall2_app.
        - eapply forall2_conv_trans; [ | exact Hus].
          clear -Hpx. induction (ctor_indices cd) as [|t0 idx IH]; cbn [map]; constructor; [ | exact IH].
          exact (conv_subst_tsub sg _ _ Hpx 0 t0).
        - constructor; [ | constructor]. eapply conv_trans; [apply conv_apps; [apply conv_refl | exact Hpx] | exact Hcx]. }
      pose proof (X_Conv _ _ _ _ _ _ _ _ H1 HPT HcT) as H2.
      destruct (IHn _ _ _ _ H2 Hev) as (m2 & w & Hw & Hvw).
      exists (S (m1 + m2)), w. split; [ | exact Hvw].
      cbn [eval_erased]. rewrite (eval_erased_mono se m1 (m1 + m2) _ _ ltac:(lia) Hwx). cbv beta iota.
      rewrite Ewx, (ecase_iota_ctor D d c i cd es bs' b' Hd Hc
                      ltac:(rewrite (eargs_length sg _ _ _ _ Hes), length_app; lia) Eb').
      cbv beta iota. rewrite <- Hlp'. apply (eval_erased_mono se m2); [lia | exact Hw].
    (* a match on an empty proposition: no constructor to reach *)
    - cbn [eval_nested eval_node] in Hev.
      destruct (eval_nested sg n x) as [vx|ux|]; try discriminate Hev.
      destruct (case_iota sg (Case D s P vx [])) as [r|] eqn:Hci; [ | discriminate Hev].
      cbn [case_iota] in Hci. rewrite Hd in Hci.
      destruct (ctor_view D d vx) as [[[i cd] xs]|] eqn:Ev; [ | discriminate Hci].
      destruct (ctor_view_spec _ _ _ _ _ _ Ev) as (c & ps' & _ & Hc & _ & _).
      rewrite Hctors in Hc. discriminate Hc.
    (* a match on a singleton proposition: its branch applied to [□] *)
    - cbn [eval_nested eval_node] in Hev.
      destruct (eval_nested sg n x) as [vx|ux|] eqn:Ex; try discriminate Hev.
      destruct (case_iota sg (Case D s P vx [b])) as [r|] eqn:Hci; [ | discriminate Hev].
      pose proof Hci as Hci0. cbn [case_iota] in Hci0. rewrite Hd in Hci0.
      destruct (ctor_view D d vx) as [[[i cd] xs]|] eqn:Ev; [ | discriminate Hci0].
      destruct (ctor_view_spec _ _ _ _ _ _ Ev) as (c0 & ps' & Evx & Hc & Hlp' & Hlx).
      pose proof Hc as Hc0. rewrite Hctors in Hc0. cbn [find_ctor] in Hc0.
      destruct (String.eqb (ctor_name c) c0) eqn:Ecn; [ | discriminate Hc0]. injection Hc0 as <- <-.
      cbn [nth_error option_map] in Hci0. injection Hci0 as <-.
      apply String.eqb_eq in Ecn. subst vx.
      pose proof (eval_typed _ _ _ _ Hx Ex) as Tvx.
      destruct (validity_type Sp sg Hsig _ _ _ Hx (fun s1 => apps_const_not_srt _ _ s1)) as [sx HX].
      pose proof (case_type_typed Sp sg Hsig _ _ _ _ _ _ _ _ _ Hd Hlp Hlu Hx HP HX) as HPT.
      destruct (sig_ind_closed _ _ _ Hd) as [_ Hcs]. rewrite Hctors in Hcs. cbn [forallb] in Hcs.
      apply andb_prop in Hcs as [Hcc _]. unfold ctor_closed in Hcc. apply andb_prop in Hcc as [Hfc Hic].
      pose proof (sig_ind_name _ _ _ Hd) as Hname.
      set (FT := field_types (ind_name d) (length (ind_params d)) 0 (ctor_fields c)) in *.
      assert (Hty : sig_type sg (Ctor D c0) = Some (ctor_type d c)) by (cbn [sig_type]; rewrite Hd, Hc; reflexivity).
      destruct (const_type_typed Sp sg Hsig [] _ _ (W_Nil _ _) Hty) as [s0 Hs0].
      unfold ctor_type in Hs0. cbv zeta in Hs0. fold FT in Hs0.
      assert (Hl : length (ind_params d ++ FT) = length (ps' ++ xs))
        by (unfold FT; rewrite !length_app, field_types_length; lia).
      destruct (apps_inv Sp sg (ps' ++ xs) [] (Const (Ctor D c0)) _ _ _ _ Hl Tvx (const_head Sp sg _ _ _ Hty) Hs0)
        as [Hargs Hcv].
      rewrite subst_apps, map_app in Hcv. cbn [subst] in Hcv.
      rewrite <- Hlx, <- Hlp', map_tsub_vars, Hname in Hcv.
      apply conv_ind_spine in Hcv. apply forall2_app_split in Hcv as [Hps Hus]; [ | lia].
      destruct (proj1 (args_typed_app Sp sg ps' [] _ _ xs (eq_sym Hlp')) Hargs) as [Hps' Hxs].
      pose proof (env_singleton _ _ Henv D d c ps' xs Hd Hsort Helim Hctors Hps' Hxs) as Hprops.
      pose proof (args_props_eargs sg _ _ _ Hprops) as Hxs1.
      assert (Hbt : case_branch_type d ps P c =
        pis (subst_tele (tsub ps) FT)
            (apps (lift (length xs) P)
               (map (subst (upn (length xs) (tsub ps))) (ctor_indices c) ++
                [apps (Const (Ctor D c0)) (map (lift (length xs)) ps ++ vars 0 (length xs))]))).
      { unfold case_branch_type. cbv zeta. fold FT. rewrite Hname, Ecn, Hlx.
        rewrite (inst_tele_tsub FT ps 0).
        2: { unfold FT. rewrite Nat.add_0_l, Hlp.
             pose proof (field_types_closed (ind_name d) _ _ 0 ltac:(rewrite Nat.add_0_r; exact Hfc)) as Hft.
             rewrite Nat.add_0_r in Hft. exact Hft. }
        f_equal. f_equal. f_equal. apply map_ext_in. intros t0 Ht0. apply inst_env_tsub.
        rewrite Hlp, Nat.add_comm. exact (proj1 (List.forallb_forall _ _) Hic t0 Ht0). }
      rewrite Hbt in Hb.
      pose proof (proj1 (erases_typed Sp sg) _ _ _ _ Hb) as Tb.
      destruct (validity_type Sp sg Hsig _ _ _ Tb (pis_apps_not_srt _ _ _ _)) as [sb HBT].
      pose proof (eargs_conv sg _ _ _ _ Hxs1 _ _ _ (conv_subst_tele_tsub sg _ _ Hps FT 0) HBT) as Hxs'.
      pose proof (erases_apps sg _ _ _ _ _ _ _ Hxs' Hb) as H1.
      rewrite subst_apps, subst_tsub_lift, map_app, map_map in H1. cbn [map] in H1.
      rewrite subst_apps, map_app, map_tsub_lift, map_tsub_vars0 in H1. cbn [subst] in H1.
      rewrite (map_ext _ _ (fun t0 => subst_subst t0 (tsub xs) (upn (length xs) (tsub ps)))) in H1.
      rewrite (map_ext _ (subst (tsub (ps ++ xs)))) in H1 by (intros t0; apply subst_ext; apply tsub_app).
      assert (Hcx : apps (Const (Ctor D c0)) (ps' ++ xs) ≡ x) by (apply conv_sym, red_conv, (eval_red _ _ _ Ex)).
      assert (Hpx : Forall2 (conv sg) (ps ++ xs) (ps' ++ xs))
        by (apply Forall2_app; [apply forall2_conv_sym, Hps | apply forall2_conv_refl]).
      assert (HcT : apps P (map (subst (tsub (ps ++ xs))) (ctor_indices c) ++ [apps (Const (Ctor D c0)) (ps ++ xs)])
                    ≡ apps P (us ++ [x])).
      { apply conv_apps; [apply conv_refl | ]. apply Forall2_app.
        - eapply forall2_conv_trans; [ | exact Hus].
          clear -Hpx. induction (ctor_indices c) as [|t0 idx IH]; cbn [map]; constructor; [ | exact IH].
          exact (conv_subst_tsub sg _ _ Hpx 0 t0).
        - constructor; [ | constructor]. eapply conv_trans; [apply conv_apps; [apply conv_refl | exact Hpx] | exact Hcx]. }
      pose proof (X_Conv _ _ _ _ _ _ _ _ H1 HPT HcT) as H2. rewrite Hlx in H2.
      exact (IHn _ _ _ _ H2 Hev).
    (* a fix: a value *)
    - cbn [eval_nested eval_node] in Hev. injection Hev as <-.
      exists 1, (EFix k b'). split; [reflexivity | exact (X_Fix _ _ _ _ _ _ _ _ _ HA Hsa Hne Hb Hg)].
  Qed.
End Simulation.

(** For the evaluator of source programs. *)
Corollary simulation_src : forall sg se, erases_env sg se ->
  forall fsrc t T e v, erases Sp sg [] t T e -> eval_src sg fsrc t = CbvValue v ->
  exists fdst w, eval_erased se fdst e = CbvValue w /\ erases Sp sg [] v T w.
Proof.
  intros sg se Henv fsrc t T e v H Hv. rewrite (proj1 (eval_src_nested fsrc) t) in Hv.
  exact (simulation sg se Henv _ _ _ _ _ H Hv).
Qed.
