(** * A checked signature is related to its erasure

    [checked_env_related] of Contracts.v: a checked signature and its
    erased signature satisfy [erases_env] of Erasure/Simulation.v, the
    premises of the simulation.

    - The signature is type-correct (Checked/SigTyped.v of
      elim-inductive-types).
    - Its δ-bodies are erased by [erase], sound for the relation
      (Erasure/EraseSound.v).
    - Its declarations and the primitives are found in the erased
      signature ([erase_entries_inds], [erase_entries_prims]); an
      instance into a sort other than Prop has an erased kind, the
      strict erasure refusing inactive instances.
    - The fields of the constructor of a singleton proposition are
      proofs: the checker found the sort Prop for each of them when the
      declaration was registered, which is what made it a singleton.
      This sort is carried to the final signature by the uniqueness of
      synthesized types ([rec_ok], [singleton_ok] of
      Checked/Invariants.v, proved for checked signatures in
      Checked/Fields.v of elim-inductive-types).
    - The ι of an instance is simulated by the erased ι of its kind.
      The rule of the constructor is typed in its generic context, as
      its registration checked ([rules_typed]); a typed term built from
      variables, λ, applications and constants is related to its
      structural erasure, [□] at the positions of indices
      ([struct_erases]); the redex substitutes its arguments for the
      variables of the context ([erases_subst] of
      Erasure/RelationSubst.v), typed as the type of the instance gives
      them ([redex_typed] of Checked/IotaTyped.v in elim-inductive-types),
      their erasures read off the erased redex.  So the erased contraction is related to the contraction:
      the method applied to the erased fields and the erased
      hypotheses, the indices of the hypotheses [□].  For a singleton
      proposition the erased ι reads no field: [□] stands for each, the
      fields being proofs. *)

From Stdlib Require Import String List Bool Arith Lia Relations.
Import ListNotations.
From DepTypes.Common Require Import Result Traced.
From DepTypes.PTS Require Import Syntax Telescope Spec Signature Reduction SubstLaws Confluence Guard Typing
  TypingSubst Inversion SubjectRed Bidir BidirSound EvalSrc.
From DepTypes.Configs Require Import Predicative.
From IndTypes Require Import Telescope.
From IndTypes.Elim Require Import Generate.
From IndTypes.Checked Require Import Steps Invariants Shaped IotaTyped SigTyped Fields.
From CIC.Erasure Require Import Target TargetSubst Erase Relation RelationSubst Simulation Observation EraseSound.

Local Open Scope list_scope.

Local Notation Sp := predicative_prop.

(** ** The structural erasure of a typed term *)

Section Struct.
  Variable sg : signature.
  Local Notation typed := (has_type Sp sg).

  (** [index_position], decided. *)
  Definition index_position_b (f : term) : bool :=
    match spine_head f with
    | Const (Elim D s) =>
        match sig_ind sg D with
        | Some d =>
            Nat.leb (length (ind_params d) + 1 + length (ind_ctors d)) (length (spine_args f)) &&
            Nat.ltb (length (spine_args f))
              (length (ind_params d) + 1 + length (ind_ctors d) + length (ind_indices d))
        | None => false
        end
    | _ => false
    end.

  Lemma index_position_b_spec : forall f, index_position_b f = true -> index_position sg f.
  Proof.
    intros f H. unfold index_position_b in H.
    destruct (spine_head f) as [| | | | | | | | | | | | | | | | | | | g | | ] eqn:Eh; try discriminate H.
    destruct g as [ | | D s | ]; try discriminate H.
    destruct (sig_ind sg D) as [d|] eqn:Hd; [ | discriminate H].
    apply andb_prop in H as [H1 H2]. apply Nat.leb_le in H1. apply Nat.ltb_lt in H2.
    exists D, s, d. auto.
  Qed.

  (** Terms of variables, λ, applications and constants other than
      families and instances into Prop; the argument at an index
      position is free. *)
  Fixpoint good (t : term) : Prop :=
    match t with
    | Var _ => True
    | Lam b => good b
    | App f a => good f /\ (index_position_b f = true \/ good a)
    | Const (Elim D s) => s <> Prp
    | Const (Ctor _ _) | Const (Def _) => True
    | _ => False
    end.

  Fixpoint eps (t : term) : eterm :=
    match t with
    | Var n => EVar n
    | Lam b => ELam (eps b)
    | App f a => EApp (eps f) (if index_position_b f then EBox else eps a)
    | Const (Elim D s) => EPrim D s
    | Const (Ctor D c) => ECtor D c
    | Const (Def f) => EConst f
    | _ => EBox
    end.

  Theorem struct_erases : forall t G T, typed G t T -> good t -> erases Sp sg G t T (eps t).
  Proof.
    induction t as [ s | n | A IHA B IHB | b IHb | f IHf a IHa | u IHu A IHA | | C IHC e IHe | | | C IHC c IHc u IHu
                   | | | | C IHC x IHx y IHy b IHb | A IHA B IHB | a IHa b IHb | q IHq | q IHq | g
                   | D s P IHP x IHx bs | A IHA k b IHb ];
      intros G T Ht Hg; cbn [good eps] in *; try contradiction.
    - exact (X_Var _ _ _ _ _ Ht).
    - destruct (inv_lam Sp sg _ _ _ Ht) as (A & B & s & Hb & HPi & Hc).
      exact (erases_ctype sg _ _ _ _ _ (X_Lam _ _ _ _ _ _ _ _ (IHb _ _ Hb Hg) HPi) Hc).
    - destruct (inv_app Sp sg _ _ _ _ Ht) as (A & B & Hf & Ha & Hc). destruct Hg as [Hgf Hga].
      refine (erases_ctype sg G _ (subst1 B a) T _ _ Hc).
      destruct (index_position_b f) eqn:Ei.
      + exact (X_AppIndex _ _ _ _ _ _ _ _ (IHf _ _ Hf Hgf) Ha (index_position_b_spec _ Ei)).
      + destruct Hga as [E | Hga]; [discriminate E | ].
        exact (X_App _ _ _ _ _ _ _ _ _ (IHf _ _ Hf Hgf) (IHa _ _ Ha Hga)).
    - destruct g as [D | D c | D s | f]; cbn [good eps] in *; try contradiction.
      + exact (X_Ctor _ _ _ _ _ _ Ht).
      + exact (X_Elim _ _ _ _ _ _ Ht Hg).
      + exact (X_Def _ _ _ _ _ Ht).
  Qed.

  (** *** The structural erasure of the right side of a rule *)

  Lemma eps_snoc : forall h l a, eps (apps h (l ++ [a])) =
    EApp (eps (apps h l)) (if index_position_b (apps h l) then EBox else eps a).
  Proof. intros h l a. rewrite apps_snoc. reflexivity. Qed.

  Lemma good_snoc : forall h l a, good (apps h (l ++ [a])) <->
    good (apps h l) /\ (index_position_b (apps h l) = true \/ good a).
  Proof. intros h l a. rewrite apps_snoc. reflexivity. Qed.

  Lemma index_position_b_var : forall j l, index_position_b (apps (Var j) l) = false.
  Proof. intros j l. unfold index_position_b. rewrite spine_head_apps. reflexivity. Qed.

  Lemma eps_apps_var : forall l j, eps (apps (Var j) l) = eapps (EVar j) (map eps l).
  Proof.
    induction l as [|a l IH] using rev_ind; intros j; [reflexivity | ].
    rewrite eps_snoc, index_position_b_var, IH, map_app. cbn [map]. rewrite eapps_snoc. reflexivity.
  Qed.

  Lemma good_apps_var : forall l j, Forall good l -> good (apps (Var j) l).
  Proof.
    induction l as [|a l IH] using rev_ind; intros j H; [exact I | ].
    apply Forall_app in H as [H1 H2]. inversion H2; subst.
    apply good_snoc. split; [exact (IH _ H1) | right; assumption].
  Qed.

  Variables (D : String.string) (s : sort) (d : ind_desc).
  Hypothesis Hd : sig_ind sg D = Some d.
  Hypothesis Hs : s <> Prp.
  Let p := length (ind_params d).
  Let k := length (ind_ctors d).
  Let q := length (ind_indices d).

  Lemma index_position_b_elim : forall l, index_position_b (apps (Const (Elim D s)) l) =
    Nat.leb (p + 1 + k) (length l) && Nat.ltb (length l) (p + 1 + k + q).
  Proof.
    intros l. unfold index_position_b. rewrite spine_head_apps, spine_args_apps. cbn [spine_head spine_args].
    rewrite Hd. reflexivity.
  Qed.

  Lemma eps_elim_pre : forall l, length l <= p + 1 + k ->
    eps (apps (Const (Elim D s)) l) = eapps (EPrim D s) (map eps l) /\
    (Forall good l -> good (apps (Const (Elim D s)) l)).
  Proof.
    induction l as [|a l IH] using rev_ind; intros Hl; [split; [reflexivity | intros _; exact Hs] | ].
    rewrite length_app in Hl. cbn [length] in Hl. destruct (IH ltac:(lia)) as [IH1 IH2].
    assert (Hi : index_position_b (apps (Const (Elim D s)) l) = false).
    { rewrite index_position_b_elim. apply andb_false_intro1. apply Nat.leb_gt. lia. }
    split.
    - rewrite eps_snoc, Hi, IH1, map_app. cbn [map]. rewrite eapps_snoc. reflexivity.
    - intros H. apply Forall_app in H as [H1 H2]. inversion H2; subst.
      apply good_snoc. split; [exact (IH2 H1) | right; assumption].
  Qed.

  Lemma eps_elim_idx : forall pre is, length pre = p + 1 + k -> length is <= q ->
    eps (apps (Const (Elim D s)) (pre ++ is)) = eapps (EPrim D s) (map eps pre ++ repeat EBox (length is)) /\
    (Forall good pre -> good (apps (Const (Elim D s)) (pre ++ is))).
  Proof.
    intros pre is Hpre. induction is as [|a is IH] using rev_ind; intros Hl.
    - rewrite !app_nil_r. exact (eps_elim_pre pre ltac:(lia)).
    - rewrite length_app in Hl. cbn [length] in Hl. destruct (IH ltac:(lia)) as [IH1 IH2].
      assert (Hi : index_position_b (apps (Const (Elim D s)) (pre ++ is)) = true).
      { rewrite index_position_b_elim, length_app. apply andb_true_intro. split; [apply Nat.leb_le | apply Nat.ltb_lt]; lia. }
      rewrite app_assoc. split.
      + rewrite eps_snoc, Hi, IH1, length_app, repeat_app. cbn [length repeat]. rewrite app_assoc, eapps_snoc.
        reflexivity.
      + intros H. apply good_snoc. split; [exact (IH2 H) | left; exact Hi].
  Qed.

  Lemma eps_elim_full : forall pre is o, length pre = p + 1 + k -> length is = q ->
    eps (apps (Const (Elim D s)) (pre ++ is ++ [o])) =
      eapps (EPrim D s) (map eps pre ++ repeat EBox q ++ [eps o]) /\
    (Forall good pre -> good o -> good (apps (Const (Elim D s)) (pre ++ is ++ [o]))).
  Proof.
    intros pre is o Hpre Hq. destruct (eps_elim_idx pre is Hpre ltac:(lia)) as [H1 H2].
    assert (Hi : index_position_b (apps (Const (Elim D s)) (pre ++ is)) = false).
    { rewrite index_position_b_elim, length_app. apply andb_false_intro2. apply Nat.ltb_ge. lia. }
    rewrite app_assoc. split.
    - rewrite eps_snoc, Hi, H1, Hq, app_assoc, eapps_snoc. reflexivity.
    - intros Hg Ho. apply good_snoc. split; [exact (H2 Hg) | right; exact Ho].
  Qed.

  Definition is_var (t : term) : Prop := exists j, t = Var j.

  Lemma eps_lams : forall m b, eps (lams m b) = elams m (eps b).
  Proof. induction m as [|m IH]; intros b; [reflexivity | cbn [lams eps elams]; rewrite IH; reflexivity]. Qed.

  Lemma good_lams : forall m b, good b -> good (lams m b).
  Proof. induction m as [|m IH]; intros b H; [exact H | exact (IH b H)]. Qed.

  Lemma eps_vars : forall base n, map eps (vars base n) = evarsb base n.
  Proof. intros base n. induction n as [|n IH]; [reflexivity | cbn [vars map eps evarsb]; rewrite IH; reflexivity]. Qed.

  Lemma good_vars : forall base n, Forall good (vars base n).
  Proof. intros base n. induction n as [|n IH]; constructor; [exact I | exact IH]. Qed.

  (** The hypothesis of a recursive field, of variables. *)
  Lemma eps_hyp : forall pre env Bs vs a, Forall is_var pre -> is_var a -> length pre = p + 1 + k ->
    length vs = q ->
    eps (hyp D s pre env Bs vs a) = ehyp D s (map eps pre) q (length Bs) (eps a) /\
    good (hyp D s pre env Bs vs a).
  Proof.
    intros pre env Bs vs a Hpre [j ->] Hl Hq. unfold hyp, ehyp. cbv zeta.
    destruct (eps_elim_full (map (lift (length Bs)) pre) (map (subst (inst (length Bs) env)) vs)
                (apps (lift (length Bs) (Var j)) (vars 0 (length Bs)))
                ltac:(rewrite length_map; exact Hl) ltac:(rewrite length_map; exact Hq)) as [H1 H2].
    rewrite eps_lams, H1. split.
    - f_equal. f_equal. rewrite map_map. f_equal.
      + rewrite map_map. apply map_ext_in. intros t Ht. rewrite Forall_forall in Hpre.
        destruct (Hpre t Ht) as [i ->]. reflexivity.
      + f_equal. change (lift (length Bs) (Var j)) with (Var (length Bs + j)).
        rewrite eps_apps_var, eps_vars, evarsb_0. reflexivity.
    - apply good_lams. apply H2.
      + rewrite Forall_forall in Hpre |- *. intros t Ht. apply in_map_iff in Ht as (t0 & <- & Ht0).
        destruct (Hpre t0 Ht0) as [i ->]. exact I.
      + change (lift (length Bs) (Var j)) with (Var (length Bs + j)). apply good_apps_var. apply good_vars.
  Qed.

  (** The arguments of the method of a rule, of variables. *)
  Lemma eps_iota_args : forall fs pre env xs, Forall is_var pre -> Forall is_var xs -> length pre = p + 1 + k ->
    (forall Bs vs, In (FRec Bs vs) fs -> length vs = q) ->
    map eps (iota_args D s pre env fs xs) = eiota_args D s (map eps pre) q (map efield_of fs) (map eps xs) /\
    Forall good (iota_args D s pre env fs xs).
  Proof.
    induction fs as [|fd fs IH]; intros pre env xs Hpre Hxs Hl Hvs; [split; [reflexivity | constructor] | ].
    destruct xs as [|a xs]; [destruct fd; split; [reflexivity | constructor | reflexivity | constructor] | ].
    inversion Hxs as [| ? ? Ha Hxs']; subst.
    destruct (IH pre (a :: env) xs Hpre Hxs' Hl (fun Bs vs H => Hvs Bs vs (or_intror H))) as [IH1 IH2].
    destruct Ha as [j ->].
    destruct fd as [A | Bs vs]; cbn [iota_args map efield_of eiota_args].
    - split; [rewrite IH1; reflexivity | constructor; [exact I | exact IH2]].
    - destruct (eps_hyp pre env Bs vs (Var j) Hpre (ex_intro _ j eq_refl) Hl (Hvs Bs vs (or_introl eq_refl)))
        as [Hh Hg].
      split; [rewrite IH1, Hh; reflexivity | constructor; [exact I | constructor; [exact Hg | exact IH2]]].
  Qed.

  (** *** Substitution in the structural erasure *)

  Definition is_evar (e : eterm) : Prop := exists j, e = EVar j.

  Lemma esubst_ehyp : forall sb pre m a, Forall is_evar pre -> is_evar a ->
    esubst sb (ehyp D s pre q m a) = ehyp D s (map (esubst sb) pre) q m (esubst sb a).
  Proof.
    intros sb pre m a Hpre [j ->]. unfold ehyp. rewrite esubst_elams, esubst_eapps. cbn [esubst].
    f_equal. f_equal. rewrite !map_app. f_equal; [ | f_equal; [apply map_box; reflexivity | ]].
    - rewrite !map_map. apply map_ext_in. intros e He. rewrite Forall_forall in Hpre.
      destruct (Hpre e He) as [i ->]. unfold elift at 1. cbn [erename esubst]. apply eupn_ge.
    - cbn [map]. f_equal. rewrite esubst_eapps, esubst_evars. f_equal.
      unfold elift at 1. cbn [erename esubst]. apply eupn_ge.
  Qed.

  Lemma esubst_eiota_args : forall sb fs pre xs, Forall is_evar pre -> Forall is_evar xs ->
    map (esubst sb) (eiota_args D s pre q fs xs) = eiota_args D s (map (esubst sb) pre) q fs (map (esubst sb) xs).
  Proof.
    intros sb fs. induction fs as [|fd fs IH]; intros pre xs Hpre Hxs; [reflexivity | ].
    destruct xs as [|a xs]; [destruct fd; reflexivity | ].
    inversion Hxs as [| ? ? Ha Hxs']; subst.
    destruct fd as [|m]; cbn [eiota_args map].
    - f_equal. exact (IH _ _ Hpre Hxs').
    - f_equal. f_equal; [exact (esubst_ehyp sb pre m a Hpre Ha) | exact (IH _ _ Hpre Hxs')].
  Qed.
End Struct.

(** ** Spines in the relation *)

Section Spines.
  Variable sg : signature.
  Hypothesis Hsig : signature_typed Sp sg.
  Local Notation typed := (has_type Sp sg).
  Local Notation erases := (erases Sp sg).
  Local Notation "t ≡ u" := (conv sg t u).

  (** The erasure of a prefix of a spine. *)
  Lemma erases_apps_prefix : forall l2 G h l1 T e, erases G (apps h (l1 ++ l2)) T e -> evalue e -> e <> EBox ->
    exists H e1 es2, e = eapps e1 es2 /\ length es2 = length l2 /\ erases G (apps h l1) H e1 /\
      evalue e1 /\ e1 <> EBox.
  Proof.
    induction l2 as [|a l2 IH] using rev_ind; intros G h l1 T e H He Hb.
    - rewrite app_nil_r in H. exists T, e, []. auto.
    - rewrite app_assoc, apps_snoc in H.
      destruct (erases_app_inv sg _ _ _ _ _ H) as [(-> & _) | (A & B & f' & a' & -> & Hf & _ & _)];
        [contradiction | ].
      destruct (evalue_app_inv _ _ He) as (Hf' & _ & Hfb & _).
      destruct (IH _ _ _ _ _ Hf Hf' Hfb) as (H' & e1 & es2 & -> & Hl & H1 & Hv & Hb1).
      exists H', e1, (es2 ++ [a']). rewrite eapps_snoc, !length_app, Hl. auto.
  Qed.

  (** [erases_apps_inv] of Erasure/Simulation.v, for a spine whose
      prefixes below its length are at no index position. *)
  Theorem erases_apps_inv' : forall args G h T e Ts R0 s0 eh0, length Ts = length args ->
    erases G (apps h args) T e -> evalue e -> e <> EBox ->
    (forall H eh, erases G h H eh -> eh <> EBox -> H ≡ pis Ts R0 /\ eh = eh0) ->
    (forall l, length l < length args -> ~ index_position sg (apps h l)) ->
    typed G (pis Ts R0) (Srt s0) ->
    exists es, e = eapps eh0 es /\ eargs sg G Ts args es /\ subst (tsub args) R0 ≡ T.
  Proof.
    induction args as [|a args IH] using rev_ind; intros G h T e Ts R0 s0 eh0 Hl He Hev Hb Hh Hi HP.
    - destruct Ts; [ | discriminate Hl]. destruct (Hh T e He Hb) as [Hc ->].
      exists []. split; [reflexivity | split; [constructor | ]]. rewrite subst_tsub_nil. apply conv_sym, Hc.
    - assert (HTs : Ts <> []) by (intros ->; rewrite length_app in Hl; cbn in Hl; lia).
      destruct (exists_last HTs) as (Ts' & Tl & ->).
      rewrite !length_app in Hl. cbn [length] in Hl.
      rewrite apps_snoc in He.
      destruct (erases_app_inv sg _ _ _ _ _ He) as [(-> & _) | (A & B & f' & a' & -> & Hf & Ha & HT)];
        [contradiction | ].
      destruct (evalue_app_inv _ _ Hev) as (Hf' & _ & Hfb & _).
      destruct Ha as [Ha | (_ & _ & Hip)];
        [ | exfalso; exact (Hi args ltac:(rewrite length_app; cbn [length]; lia) Hip)].
      rewrite pis_app in HP. cbn [pis] in HP.
      assert (Hh' : forall H eh, erases G h H eh -> eh <> EBox -> H ≡ pis Ts' (Pi Tl R0) /\ eh = eh0).
      { intros H eh H1 H2. destruct (Hh H eh H1 H2) as [Hc Heq]. rewrite pis_app in Hc. split; [exact Hc | exact Heq]. }
      destruct (IH G h (Pi A B) f' Ts' (Pi Tl R0) s0 eh0 ltac:(lia) Hf Hf' Hfb Hh'
                  (fun l Hl' => Hi l ltac:(rewrite length_app; cbn [length]; lia)) HP) as (es & -> & Hargs & Hc).
      cbn [subst] in Hc. apply pi_inj in Hc as [HcA HcB].
      destruct (typed_pis_inst Sp sg _ _ _ _ _ (eargs_typed _ _ _ _ _ Hargs) HP) as [s' HPi]. cbn [subst] in HPi.
      destruct (inv_pi Sp sg _ _ _ _ HPi) as (s1 & _ & _ & HTl & _ & _ & _).
      pose proof (X_Conv _ _ _ _ _ _ _ _ Ha HTl (conv_sym _ _ HcA)) as Ha'.
      exists (es ++ [a']). split; [rewrite eapps_snoc; reflexivity | split].
      + apply (eargs_app_join sg args G Ts' [Tl] [a] es [a'] Hargs). cbn [subst_tele].
        constructor; [exact Ha' | constructor].
      + rewrite subst_tsub_snoc. eapply conv_trans; [ | exact (ctype_conv_of Sp sg _ _ _ HT)].
        apply conv_subst. exact HcB.
  Qed.

  Lemma index_position_elim : forall D s d l, sig_ind sg D = Some d ->
    index_position sg (apps (Const (Elim D s)) l) ->
    length (ind_params d) + 1 + length (ind_ctors d) <= length l /\
    length l < length (ind_params d) + 1 + length (ind_ctors d) + length (ind_indices d).
  Proof.
    intros D s d l Hd (D' & s' & d' & Eh & Hd' & H1 & H2).
    rewrite spine_head_apps in Eh. cbn [spine_head] in Eh. injection Eh as <- <-.
    rewrite Hd in Hd'. injection Hd' as <-. rewrite spine_args_apps in H1, H2. cbn [spine_args app] in H1, H2.
    split; assumption.
  Qed.

  Lemma no_index_ctor : forall D c l, ~ index_position sg (apps (Const (Ctor D c)) l).
  Proof.
    intros D c l (D' & s' & d' & Eh & _). rewrite spine_head_apps in Eh. discriminate Eh.
  Qed.

  (** Arguments erased against a telescope substitute for its variables. *)
  Lemma eargs_esub_ok : forall Ts args es, eargs sg [] Ts args es -> esub_ok Sp sg (rev Ts) [] (tsub args) (etsub es).
  Proof.
    intros Ts args es H n A HA.
    pose proof (eargs_length _ _ _ _ _ H) as Hle.
    pose proof (args_typed_length Sp sg _ _ _ (eargs_typed _ _ _ _ _ H)) as Hlt.
    unfold lookup in HA. destruct (nth_error (rev Ts) n) as [T|] eqn:En; [ | discriminate HA].
    cbn [option_map] in HA. injection HA as <-.
    rewrite nth_error_rev in En. destruct (Nat.ltb n (length Ts)) eqn:Hn; [ | discriminate En].
    apply Nat.ltb_lt in Hn. set (j := length Ts - Datatypes.S n) in *.
    assert (Hj : j < length args) by lia.
    destruct (nth_error args j) as [a|] eqn:Ea; [ | apply nth_error_None in Ea; lia].
    destruct (nth_error es j) as [e|] eqn:Ee; [ | apply nth_error_None in Ee; lia].
    pose proof (eargs_nth _ _ _ _ _ H j T a e En Ea Ee) as Hj'.
    assert (Esb : tsub args n = a).
    { unfold tsub. rewrite rev_nth by lia. replace (length args - Datatypes.S n) with j by lia.
      apply nth_error_nth. exact Ea. }
    assert (Eesb : etsub es n = e).
    { unfold etsub. rewrite rev_nth by lia. replace (length es - Datatypes.S n) with j by lia.
      apply nth_error_nth. exact Ee. }
    rewrite Esb, Eesb. unfold lift. rewrite subst_rename.
    rewrite (subst_ext T _ (tsub (firstn j args))); [exact Hj' | ].
    intros i. rewrite <- (firstn_skipn j args) at 1.
    replace (Datatypes.S n + i) with (length (skipn j args) + i) by (rewrite length_skipn; lia).
    apply tsub_app_ge.
  Qed.

  (** Arguments whose types, instantiated, are propositions. *)
  Lemma args_props_of_nth : forall G Ts args, args_typed Sp sg G Ts args ->
    (forall j T, nth_error Ts j = Some T -> j < length args ->
       typed G (subst (tsub (firstn j args)) T) (Srt Prp)) ->
    args_props sg G Ts args.
  Proof.
    intros G Ts args H. induction H as [|T Ts a args Ha Hargs IH]; intros Hp; constructor.
    - exact Ha.
    - pose proof (Hp 0 T eq_refl ltac:(cbn; lia)) as H0. cbn [firstn] in H0. rewrite subst_tsub_nil in H0. exact H0.
    - apply IH. intros j T' HT' Hj. rewrite nth_error_subst_tele in HT'.
      destruct (nth_error Ts j) as [T0|] eqn:E0; [ | discriminate HT']. cbn [option_map] in HT'. injection HT' as <-.
      pose proof (Hp (Datatypes.S j) T0 E0 ltac:(cbn; lia)) as H1. cbn [firstn] in H1.
      rewrite <- (subst_tsub_cons a (firstn j args) j) in H1; [exact H1 | rewrite length_firstn; lia].
  Qed.
End Spines.

(** ** ι of an instance *)

Section Iota.
  Variable sg : signature.
  Hypothesis Hsig : signature_typed Sp sg.
  Hypothesis Hinst : instances_checked Sp sg.
  Hypothesis Hrec : rec_ok sg.
  Hypothesis Hsing : singleton_ok sg.
  Variable se : esignature.
  Hypothesis Hinds : forall D d, sig_ind sg D = Some d -> efind_ind se D = Some (erase_ind d).
  Hypothesis Hkinds : forall D s A act, s <> Prp -> sig_elim sg D s = Some (A, act) ->
    exists d, sig_ind sg D = Some d /\ efind_elim se D s = Some (kind_of d) /\ kind_of d <> KProp.
  Local Notation typed := (has_type Sp sg).
  Local Notation erases := (erases Sp sg).
  Local Notation "t ≡ u" := (conv sg t u).

  Lemma Htypes : sig_types_typed Sp sg.
  Proof. exact (proj1 Hsig). Qed.

  Local Notation sorted := (type_typed Sp sg Htypes predicative_prop_full).

  (** *** The erased redex: its parameters, motive and methods erased
      against the telescope of the instance, its object at the family *)

  Lemma redex_erased : forall D s d ps P ms is x T e,
    sig_elim sg D s = Some (elim_type d s, true) -> sig_ind sg D = Some d ->
    length ps = length (ind_params d) -> length ms = length (ind_ctors d) -> length is = length (ind_indices d) ->
    erases [] (apps (Const (Elim D s)) (ps ++ [P] ++ ms ++ is ++ [x])) T e -> evalue e -> e <> EBox ->
    typed [] x (apps (Const (Ind D)) (ps ++ is)) ->
    exists pre' ib' x', e = eapps (EPrim D s) (pre' ++ ib' ++ [x']) /\ length ib' = length is /\ s <> Prp /\
      eargs sg [] (ind_params d ++ [motive_type d s] ++ methods d) (ps ++ [P] ++ ms) pre' /\
      erases [] x (apps (Const (Ind D)) (ps ++ is)) x' /\ evalue x'.
  Proof.
    intros D s d ps P ms is x T e Ee Ed Hlp Hlk Hlq He Hev Hb Hxt.
    pose proof (sig_ind_name _ _ _ Ed) as Hname.
    destruct (erases_spine_inv sg _ _ _ _ _ He Hev Hb) as (H0 & eh0 & es0 & _ & _ & Hh & Hhb).
    assert (Hs : s <> Prp).
    { destruct (erases_const_inv sg _ _ _ _ Hh) as [E | [(f & E & _) | [(D' & c' & E & _) | (D' & s' & E & _ & Hs')]]];
        [contradiction | discriminate E | discriminate E | injection E as <- <-; exact Hs']. }
    set (pre := ps ++ [P] ++ ms).
    set (p := length (ind_params d)) in *. set (k := length (ind_ctors d)) in *. set (q := length (ind_indices d)) in *.
    assert (Hlpre : length pre = p + 1 + k) by (unfold pre; rewrite !length_app; cbn [length]; lia).
    assert (Eargs : ps ++ [P] ++ ms ++ is ++ [x] = (pre ++ is) ++ [x]) by (unfold pre; rewrite <- !app_assoc; reflexivity).
    rewrite Eargs, apps_snoc in He.
    destruct (erases_app_inv sg _ _ _ _ _ He) as [(E & _) | (A1 & B1 & f' & x' & -> & Hf & Hx & HT)];
      [contradiction | ].
    destruct (evalue_app_inv _ _ Hev) as (Hf'v & Hx'v & Hf'b & _).
    destruct Hx as [Hx | (_ & _ & Hip)];
      [ | exfalso; destruct (index_position_elim sg _ _ _ _ Ed Hip) as [_ Hl]; rewrite length_app in Hl; fold p k q in Hl; lia].
    destruct (erases_apps_prefix sg is [] _ pre _ _ Hf Hf'v Hf'b) as (H1 & e1 & ib' & -> & Hlib & He1 & He1v & He1b).
    assert (HtyE : sig_type sg (Elim D s) = Some (elim_type d s)) by (cbn [sig_type]; rewrite Ee; reflexivity).
    destruct (const_type_typed_t Sp sg Htypes [] _ _ (W_Nil _ _) HtyE) as [s0 Hs0].
    set (Tpre := ind_params d ++ [motive_type d s] ++ methods d).
    set (Tidx := rename_tele (Nat.add (Datatypes.S k)) (ind_indices d)).
    set (X := apps (Const (Ind D)) (vars (q + Datatypes.S k) p ++ vars 0 q)).
    set (R := apps (Var (Datatypes.S (k + q))) (vars 1 q ++ [Var 0])).
    assert (Etype : elim_type d s = pis Tpre (pis (Tidx ++ [X]) R)).
    { rewrite elim_type_tele, Hname. unfold Tpre, Tidx, X, R. fold p k q. rewrite <- !pis_app, <- !app_assoc. reflexivity. }
    assert (Etype2 : elim_type d s = pis (Tpre ++ Tidx) (Pi X R)).
    { rewrite Etype, !pis_app. reflexivity. }
    assert (HlTpre : length Tpre = length pre) by (unfold Tpre; rewrite Hlpre, !length_app, length_methods; cbn [length]; fold k; lia).
    assert (Hhead : forall H eh, erases [] (Const (Elim D s)) H eh -> eh <> EBox ->
              conv sg H (pis Tpre (pis (Tidx ++ [X]) R)) /\ eh = EPrim D s).
    { intros H eh Hh' Hb'. split.
      - rewrite <- Etype. exact (const_head Sp sg [] _ _ HtyE _ (proj1 (erases_typed Sp sg) _ _ _ _ Hh')).
      - destruct (erases_const_inv sg _ _ _ _ Hh') as [E | [(f & E & _) | [(D' & c' & E & _) | (D' & s' & E & -> & _)]]];
          [contradiction | discriminate E | discriminate E | injection E as <- <-; reflexivity]. }
    assert (Hnoidx : forall l, length l < length pre -> ~ index_position sg (apps (Const (Elim D s)) l)).
    { intros l Hl Hip. destruct (index_position_elim sg _ _ _ _ Ed Hip) as [H2 _]. fold p k in H2. lia. }
    rewrite Etype in Hs0.
    destruct (erases_apps_inv' sg pre [] _ _ _ Tpre _ s0 (EPrim D s) HlTpre He1 He1v He1b Hhead Hnoidx Hs0)
      as (pre' & -> & Hpre & _).
    (* the object, at the family *)
    pose proof (proj1 (erases_typed Sp sg) _ _ _ _ Hf) as HfT.
    rewrite <- Etype, Etype2 in Hs0.
    assert (Hhd2 : forall H, typed [] (Const (Elim D s)) H -> conv sg H (pis (Tpre ++ Tidx) (Pi X R))).
    { intros H HH. rewrite <- Etype2. exact (const_head Sp sg [] _ _ HtyE _ HH). }
    assert (Hl2 : length (Tpre ++ Tidx) = length (pre ++ is)).
    { rewrite !length_app, HlTpre. unfold Tidx. rewrite length_rename_tele. fold q. lia. }
    destruct (apps_inv Sp sg _ [] _ _ _ _ _ Hl2 HfT Hhd2 Hs0) as [_ Hc1].
    cbn [subst] in Hc1. apply pi_inj in Hc1 as [HX _].
    unfold X, pre in HX. rewrite (inst_family D ps P ms is p k q Hlp Hlk Hlq) in HX.
    destruct (sorted _ _ _ Hxt) as [sx Hsx].
    pose proof (X_Conv _ _ _ _ _ _ _ _ Hx Hsx (conv_sym _ _ HX)) as Hx'.
    exists pre', ib', x'. split; [rewrite eapps_app, eapps_snoc; reflexivity | ].
    split; [exact Hlib | split; [exact Hs | split; [exact Hpre | split; [exact Hx' | exact Hx'v]]]].
  Qed.

  (** *** The rule of the constructor, erased structurally in its
      generic context, with the erased arguments of the redex
      substituted *)

  Lemma vars_is_var : forall base n, Forall is_var (vars base n).
  Proof. intros base n. induction n as [|n IH]; constructor; [eexists; reflexivity | exact IH]. Qed.

  Lemma evarsb_is_evar : forall base n, Forall is_evar (evarsb base n).
  Proof. intros base n. induction n as [|n IH]; constructor; [eexists; reflexivity | exact IH]. Qed.

  Lemma rule_erased : forall D s d ps P ms xs i cd m pre' FX,
    sig_ind sg D = Some d -> s <> Prp -> rules_typed Sp sg d s ->
    nth_error (ind_ctors d) i = Some cd -> nth_error ms i = Some m ->
    length ps = length (ind_params d) -> length ms = length (ind_ctors d) -> length xs = length (ctor_fields cd) ->
    eargs sg [] (ind_params d ++ [motive_type d s] ++ methods d) (ps ++ [P] ++ ms) pre' ->
    eargs sg [] (subst_tele (tsub ps) (field_types D (length (ind_params d)) 0 (ctor_fields cd))) xs FX ->
    exists m', nth_error (firstn (length (ind_ctors d)) (skipn (Datatypes.S (length (ind_params d))) pre')) i = Some m' /\
      erases [] (apps m (iota_args D s (ps ++ [P] ++ ms) (rev ps) (ctor_fields cd) xs))
        (apps P (map (subst (tsub (ps ++ xs))) (ctor_indices cd) ++ [apps (Const (Ctor D (ctor_name cd))) (ps ++ xs)]))
        (eapps m' (eiota_args D s pre' (length (ind_indices d)) (map efield_of (ctor_fields cd)) FX)).
  Proof.
    intros D s d ps P ms xs i cd m pre' FX Ed Hs Hrules Ecd Em Hlp Hlk Hlx Hpre HFX.
    pose proof (sig_ind_name _ _ _ Ed) as Hname.
    pose proof (proj2 (sig_ind_closed _ _ _ Ed)) as Hcs. rewrite forallb_forall in Hcs.
    pose proof (Hcs cd (nth_error_In _ _ Ecd)) as Hccl. unfold ctor_closed in Hccl.
    apply andb_prop in Hccl as [Hfcl _].
    assert (Hvs : forall Bs vs, In (FRec Bs vs) (ctor_fields cd) -> length vs = length (ind_indices d))
      by (intros Bs vs H; exact (Hrec _ _ _ _ _ Ed (nth_error_In _ _ Ecd) H)).
    pose proof (eargs_length _ _ _ _ _ Hpre) as Hlpre'.
    pose proof (eargs_length _ _ _ _ _ HFX) as HlFX.
    remember (length (ind_params d)) as p eqn:Ep.
    remember (length (ind_ctors d)) as k eqn:Ek.
    remember (length (ind_indices d)) as q eqn:Eq.
    remember (length (ctor_fields cd)) as n eqn:En.
    set (pre := ps ++ [P] ++ ms) in *.
    assert (Hlpre : length pre = p + Datatypes.S k) by (unfold pre; rewrite !length_app; cbn [length]; lia).
    assert (Hik : i < k) by (subst k; apply nth_error_Some; congruence).
    (* the erased parameters, motive and methods *)
    destruct (eargs_app sg ps [] (ind_params d) ([motive_type d s] ++ methods d) ([P] ++ ms) pre' ltac:(lia) Hpre)
      as [_ Hrest_e].
    pose proof (eargs_length _ _ _ _ _ Hrest_e) as Hlrest. rewrite length_app in Hlrest. cbn [length] in Hlrest.
    set (ps_e := firstn (length ps) pre') in *.
    assert (Epre' : pre' = ps_e ++ skipn (length ps) pre') by (unfold ps_e; symmetry; apply firstn_skipn).
    destruct (skipn (length ps) pre') as [|P_e ms_e] eqn:Es; [cbn [length] in Hlrest; lia | ].
    cbn [length] in Hlrest.
    assert (Hlps_e : length ps_e = p) by (unfold ps_e; rewrite length_firstn; lia).
    assert (Hlms_e : length ms_e = k) by lia.
    clearbody ps_e. subst pre'.
    assert (Emeth : firstn k (skipn (Datatypes.S p) (ps_e ++ P_e :: ms_e)) = ms_e).
    { change (P_e :: ms_e) with ([P_e] ++ ms_e). rewrite app_assoc, skipn_app_exact
        by (rewrite length_app; cbn [length]; lia). apply firstn_all2. lia. }
    rewrite Emeth.
    destruct (nth_error ms_e i) as [m'|] eqn:Em'; [ | apply nth_error_None in Em'; lia].
    exists m'. split; [reflexivity | ].
    (* the rule, typed in its context *)
    assert (Hin : In (iota_rule_of d s i cd) (iota_rules d s)).
    { apply (nth_error_In _ i). unfold iota_rules. exact (rules_from_nth d s _ 0 i cd Ecd). }
    pose proof (Hrules _ Hin) as Hr. unfold iota_rule_of in Hr. cbv zeta in Hr.
    cbn [rule_ctx rule_rhs rule_type] in Hr.
    rewrite Hname, <- Ep, <- Ek, <- En in Hr.
    set (Fs := field_types D p 0 (ctor_fields cd)) in *. fold Fs in Hr.
    set (Fr := rename_tele (Nat.add (Datatypes.S k)) Fs) in *.
    assert (Ectx : rev Fr ++ rev (methods d) ++ [motive_type d s] ++ rev (ind_params d) =
                   rev ((ind_params d ++ [motive_type d s] ++ methods d) ++ Fr)).
    { rewrite !rev_app_distr. cbn [rev app]. rewrite <- !app_assoc. reflexivity. }
    rewrite Ectx in Hr.
    (* its structural erasure *)
    set (pre_v := vars (n + Datatypes.S k) p ++ [Var (n + k)] ++ vars n k) in *.
    assert (Hpv : Forall is_var pre_v).
    { unfold pre_v. apply Forall_app; split; [apply vars_is_var | ].
      apply Forall_app; split; [constructor; [eexists; reflexivity | constructor] | apply vars_is_var]. }
    assert (Hlpv : length pre_v = length (ind_params d) + 1 + length (ind_ctors d)).
    { unfold pre_v. rewrite !length_app, !length_vars. cbn [length]. lia. }
    destruct (eps_iota_args sg D s d Ed Hs (ctor_fields cd) pre_v (rev (vars (n + Datatypes.S k) p)) (vars 0 n)
                Hpv (vars_is_var 0 n) Hlpv (fun Bs vs H => eq_trans (Hvs Bs vs H) Eq)) as [Heps Hgood].
    pose proof (struct_erases sg _ _ _ Hr (good_apps_var sg _ _ Hgood)) as Hgen.
    rewrite eps_apps_var, Heps in Hgen.
    (* the arguments of the redex, erased against the context *)
    assert (Hall : eargs sg [] ((ind_params d ++ [motive_type d s] ++ methods d) ++ Fr) (pre ++ xs)
                     ((ps_e ++ P_e :: ms_e) ++ FX)).
    { apply (eargs_app_join sg pre [] _ _ _ _ _ Hpre). unfold Fr. rewrite subst_tele_rename_tele.
      rewrite (subst_tele_ext _ _ (tsub ps)); [exact HFX | ].
      intros j. unfold pre.
      replace (Datatypes.S k + j) with (length ([P] ++ ms) + j) by (rewrite length_app; cbn [length]; lia).
      apply tsub_app_ge. }
    pose proof (proj1 (erases_subst Sp sg) _ _ _ _ Hgen [] _ _ (W_Nil _ _) (eargs_esub_ok sg _ _ _ Hall)) as Hu.
    set (sb := tsub (pre ++ xs)) in *.
    set (esb := etsub ((ps_e ++ P_e :: ms_e) ++ FX)) in *.
    (* the erased side *)
    rewrite esubst_eapps in Hu. cbn [esubst] in Hu.
    rewrite (esubst_eiota_args D s d _ _ _ _) in Hu.
    2: { unfold pre_v. rewrite !map_app, !eps_vars. cbn [map eps].
         apply Forall_app; split; [apply evarsb_is_evar | ].
         apply Forall_app; split; [constructor; [eexists; reflexivity | constructor] | apply evarsb_is_evar]. }
    2: { rewrite eps_vars. apply evarsb_is_evar. }
    assert (Hesb_m : esb (n + k - 1 - i) = m').
    { unfold esb. replace (n + k - 1 - i) with (length FX + (k - 1 - i)) by lia. rewrite etsub_app_ge.
      change (ps_e ++ P_e :: ms_e) with (ps_e ++ [P_e] ++ ms_e). rewrite app_assoc.
      rewrite etsub_app_lt by lia. unfold etsub.
      rewrite rev_nth by lia. replace (length ms_e - Datatypes.S (k - 1 - i)) with i by lia.
      apply nth_error_nth. exact Em'. }
    assert (Hesb_pre : map (esubst esb) (map (eps sg) pre_v) = ps_e ++ P_e :: ms_e).
    { unfold pre_v. rewrite !map_app, !eps_vars. cbn [map eps esubst].
      assert (E1 : map (esubst esb) (evarsb (n + Datatypes.S k) p) = ps_e).
      { unfold esb.
        replace (n + Datatypes.S k) with (length ([P_e] ++ ms_e ++ FX)) by (rewrite !length_app; cbn [length]; lia).
        rewrite <- Hlps_e. change (P_e :: ms_e) with ([P_e] ++ ms_e). rewrite <- !app_assoc.
        apply map_etsub_evarsb_in with (l0 := []). }
      assert (E2 : esb (n + k) = P_e).
      { unfold esb. replace (n + k) with (length FX + (length ms_e + 0)) by lia.
        rewrite etsub_app_ge. replace (ps_e ++ P_e :: ms_e) with ((ps_e ++ [P_e]) ++ ms_e) by (rewrite <- app_assoc; reflexivity).
        rewrite etsub_app_ge. unfold etsub. rewrite rev_app_distr. reflexivity. }
      assert (E3 : map (esubst esb) (evarsb n k) = ms_e).
      { unfold esb. replace n with (length FX) by lia. replace k with (length ms_e) by lia.
        replace (ps_e ++ P_e :: ms_e) with ((ps_e ++ [P_e]) ++ ms_e) by (rewrite <- app_assoc; reflexivity). rewrite <- app_assoc.
        apply map_etsub_evarsb_in. }
      rewrite E1, E2, E3. reflexivity. }
    assert (Hesb_xs : map (esubst esb) (map (eps sg) (vars 0 n)) = FX).
    { rewrite eps_vars. unfold esb. replace n with (length FX) by lia.
      pose proof (map_etsub_evarsb_in (ps_e ++ P_e :: ms_e) FX []) as H. rewrite app_nil_r in H. exact H. }
    rewrite Hesb_m, Hesb_pre, Hesb_xs, <- Eq in Hu.
    (* the source side, as in [iota_typed] *)
    assert (Hsb_params : map (subst sb) (vars (n + Datatypes.S k) p) = ps).
    { unfold sb, pre. replace (n + Datatypes.S k) with (length ([P] ++ ms ++ xs)) by (rewrite !length_app; cbn [length]; lia).
      replace p with (length ps) by lia. rewrite <- !app_assoc. apply map_tsub_vars_in with (l0 := []). }
    assert (Hsb_P : sb (n + k) = P).
    { unfold sb, pre. replace (n + k) with (length xs + (length ms + 0)) by lia.
      rewrite tsub_app_ge, app_assoc, tsub_app_ge. unfold tsub. rewrite rev_app_distr. reflexivity. }
    assert (Hsb_ms : map (subst sb) (vars n k) = ms).
    { unfold sb, pre. replace n with (length xs) by lia. replace k with (length ms) by lia.
      rewrite <- !app_assoc, (app_assoc ps [P]). apply map_tsub_vars_in. }
    assert (Hsb_xs : map (subst sb) (vars 0 n) = xs).
    { unfold sb. replace n with (length xs) by lia. apply map_tsub_vars_last. }
    assert (Hsb_m : sb (n + k - 1 - i) = m).
    { unfold sb. replace (n + k - 1 - i) with (length xs + (k - 1 - i)) by lia. rewrite tsub_app_ge.
      unfold pre. rewrite (app_assoc ps [P]), tsub_app_lt by lia. unfold tsub.
      rewrite (nth_indep _ _ m) by (rewrite length_rev; lia).
      rewrite rev_nth by lia. replace (length ms - Datatypes.S (k - 1 - i)) with i by lia.
      apply nth_error_nth. exact Em. }
    rewrite subst_apps in Hu. cbn [subst] in Hu. rewrite Hsb_m in Hu.
    rewrite iota_args_subst in Hu by (rewrite length_rev, length_vars; exact Hfcl).
    unfold pre_v in Hu. rewrite !map_app, map_rev, Hsb_params, Hsb_ms, Hsb_xs in Hu. cbn [map subst] in Hu. rewrite Hsb_P in Hu.
    rewrite subst_apps, map_app, map_map in Hu. cbn [subst map] in Hu. rewrite Hsb_P in Hu.
    rewrite subst_apps, map_app, Hsb_params, Hsb_xs in Hu. cbn [subst] in Hu.
    rewrite (map_ext _ (subst (tsub (ps ++ xs)))) in Hu.
    2: { intros v. rewrite subst_rename. apply subst_ext. intros j.
         destruct (Nat.lt_ge_cases j n) as [Hj | Hj].
         - rewrite upn_ren_lt by exact Hj. unfold sb. rewrite !tsub_app_lt by lia. reflexivity.
         - replace j with (n + (j - n)) by lia. rewrite upn_ren_ge. unfold sb.
           replace (n + (Datatypes.S k + (j - n))) with (length xs + (length ([P] ++ ms) + (j - n)))
             by (rewrite length_app; cbn [length]; lia).
           rewrite tsub_app_ge. unfold pre. rewrite tsub_app_ge.
           replace (n + (j - n)) with (length xs + (j - n)) by lia. rewrite tsub_app_ge. reflexivity. }
    exact Hu.
  Qed.

  (** *** The erased ι of each kind *)

  Lemma eelim_iota_data : forall D s d pre' ib' c es' i cd m',
    efind_elim se D s = Some KData -> efind_ind se D = Some (erase_ind d) ->
    length pre' = length (ind_params d) + 1 + length (ind_ctors d) -> length ib' = length (ind_indices d) ->
    find_ctor (ind_ctors d) c = Some (i, cd) ->
    length es' = length (ind_params d) + length (ctor_fields cd) ->
    nth_error (firstn (length (ind_ctors d)) (skipn (Datatypes.S (length (ind_params d))) pre')) i = Some m' ->
    eelim_iota se (eapps (EPrim D s) (pre' ++ ib' ++ [eapps (ECtor D c) es'])) =
      Some (eapps m' (eiota_args D s pre' (length (ind_indices d)) (map efield_of (ctor_fields cd))
                        (skipn (length (ind_params d)) es'))).
  Proof.
    intros D s d pre' ib' c es' i cd m' Hk Hi Hlpre Hlib Ec Hles Hm.
    unfold eelim_iota. rewrite espine_head_eapps. cbn [espine_head]. rewrite Hk, Hi.
    rewrite espine_args_eapps. cbn [espine_args app]. rewrite earity_erase.
    replace (Nat.eqb (length (pre' ++ ib' ++ [eapps (ECtor D c) es'])) (elim_arity d)) with true
      by (symmetry; apply Nat.eqb_eq; unfold elim_arity; rewrite !length_app; cbn [length]; lia).
    cbv zeta.
    change (eind_params (erase_ind d)) with (length (ind_params d)).
    change (eind_indices (erase_ind d)) with (length (ind_indices d)).
    change (eind_ctors (erase_ind d))
      with (map (fun c => mk_ector (ctor_name c) (map efield_of (ctor_fields c))) (ind_ctors d)).
    rewrite length_map.
    rewrite (firstn_app_exact pre' _ (Datatypes.S (length (ind_params d)) + length (ind_ctors d))) by lia.
    rewrite app_assoc, last_last, <- app_assoc.
    rewrite skipn_app. replace (Datatypes.S (length (ind_params d)) - length pre') with 0 by lia. rewrite skipn_O.
    rewrite firstn_app, length_skipn. replace (length (ind_ctors d) - (length pre' - Datatypes.S (length (ind_params d))))
      with 0 by lia. rewrite firstn_O, app_nil_r.
    rewrite espine_head_eapps. cbn [espine_head]. rewrite String.eqb_refl, (efind_ctor_erase _ _ _ _ Ec).
    rewrite espine_args_eapps. cbn [espine_args app ector_fields]. rewrite length_map.
    replace (Nat.eqb (length es') (length (ind_params d) + length (ctor_fields cd))) with true
      by (symmetry; apply Nat.eqb_eq; exact Hles).
    rewrite Hm. reflexivity.
  Qed.

  Lemma eelim_iota_singleton : forall D s d pre' ib' x' cd m',
    efind_elim se D s = Some KSingleton -> efind_ind se D = Some (erase_ind d) -> ind_ctors d = [cd] ->
    length pre' = length (ind_params d) + 1 + 1 -> length ib' = length (ind_indices d) ->
    firstn 1 (skipn (Datatypes.S (length (ind_params d))) pre') = [m'] ->
    eelim_iota se (eapps (EPrim D s) (pre' ++ ib' ++ [x'])) =
      Some (eapps m' (eiota_args D s pre' (length (ind_indices d)) (map efield_of (ctor_fields cd))
                        (repeat EBox (length (ctor_fields cd))))).
  Proof.
    intros D s d pre' ib' x' cd m' Hk Hi Hc Hlpre Hlib Hm.
    unfold eelim_iota. rewrite espine_head_eapps. cbn [espine_head]. rewrite Hk, Hi.
    rewrite espine_args_eapps. cbn [espine_args app]. rewrite earity_erase.
    replace (Nat.eqb (length (pre' ++ ib' ++ [x'])) (elim_arity d)) with true
      by (symmetry; apply Nat.eqb_eq; unfold elim_arity; rewrite Hc, !length_app; cbn [length]; lia).
    cbv zeta.
    change (eind_params (erase_ind d)) with (length (ind_params d)).
    change (eind_indices (erase_ind d)) with (length (ind_indices d)).
    change (eind_ctors (erase_ind d))
      with (map (fun c => mk_ector (ctor_name c) (map efield_of (ctor_fields c))) (ind_ctors d)).
    rewrite Hc. cbn [map length].
    rewrite (firstn_app_exact pre' _ (Datatypes.S (length (ind_params d)) + 1)) by lia.
    rewrite skipn_app. replace (Datatypes.S (length (ind_params d)) - length pre') with 0 by lia. rewrite skipn_O.
    rewrite firstn_app, length_skipn. replace (1 - (length pre' - Datatypes.S (length (ind_params d)))) with 0 by lia.
    rewrite firstn_O, app_nil_r, Hm. cbn [ector_fields]. rewrite length_map. reflexivity.
  Qed.

  (** *** The fields of a singleton proposition are proofs *)

  Lemma singleton_props : forall D d c ps xs, sig_ind sg D = Some d -> ind_sort d = Prp -> ind_elim d = AllSorts ->
    ind_ctors d = [c] -> args_typed Sp sg [] (ind_params d) ps ->
    args_typed Sp sg [] (subst_tele (tsub ps) (field_types D (length (ind_params d)) 0 (ctor_fields c))) xs ->
    args_props sg [] (subst_tele (tsub ps) (field_types D (length (ind_params d)) 0 (ctor_fields c))) xs.
  Proof.
    intros D d c ps xs Hd Hs He Hc Hps Hxs.
    set (Fs := field_types D (length (ind_params d)) 0 (ctor_fields c)) in *.
    pose proof (args_typed_length Sp sg _ _ _ Hps) as Hlp.
    pose proof (args_typed_length Sp sg _ _ _ Hxs) as Hlx. rewrite subst_tele_length in Hlx.
    assert (Hall : args_typed Sp sg [] (ind_params d ++ Fs) (ps ++ xs))
      by (apply (proj2 (args_typed_app Sp sg ps [] _ _ _ Hlp)); split; assumption).
    apply (args_props_of_nth sg); [exact Hxs | ].
    intros j T HT Hj. rewrite nth_error_subst_tele in HT.
    destruct (nth_error Fs j) as [F|] eqn:EF; [ | discriminate HT]. cbn [option_map] in HT. injection HT as <-.
    pose proof (Hsing D d c Hd Hs He Hc j F EF) as HF. fold Fs in HF.
    assert (Hpre : args_typed Sp sg [] (ind_params d ++ firstn j Fs) (ps ++ firstn j xs)).
    { rewrite <- (firstn_skipn j Fs), <- (firstn_skipn j xs), !app_assoc in Hall.
      refine (proj1 (proj1 (args_typed_app Sp sg (ps ++ firstn j xs) [] (ind_params d ++ firstn j Fs) _ _ _) Hall)).
      rewrite !length_app, !length_firstn. lia. }
    rewrite <- (app_nil_r (rev (ind_params d ++ firstn j Fs))) in HF.
    pose proof (typing_tsub Sp sg [] _ _ Hpre _ _ HF) as H1. cbn [subst] in H1.
    rewrite subst_subst. rewrite (subst_ext F _ (tsub (ps ++ firstn j xs))); [exact H1 | ].
    intros i. set (fx := firstn j xs). replace j with (length fx) by (unfold fx; rewrite length_firstn; lia).
    apply tsub_app.
  Qed.

  (** *** ι, simulated *)

  Lemma apps_const_shape : forall g l, (forall u A, apps (Const g) l <> Ann u A) /\
    (forall D s P x bs, apps (Const g) l <> Case D s P x bs).
  Proof.
    intros g l. induction l as [|a l _] using rev_ind;
      split; intros; try discriminate; rewrite apps_snoc; discriminate.
  Qed.

  Lemma kind_data : forall d, ind_sort d <> Prp -> kind_of d = KData.
  Proof.
    intros d H. unfold kind_of. destruct (sort_eqb (ind_sort d) Prp) eqn:E; [ | reflexivity].
    apply sort_eqb_eq in E. contradiction.
  Qed.

  Lemma kind_singleton : forall d c, ind_sort d = Prp -> kind_of d <> KProp -> In c (ind_ctors d) ->
    ind_elim d = AllSorts /\ ind_ctors d = [c] /\ kind_of d = KSingleton.
  Proof.
    intros d c Hs Hk Hin. unfold kind_of in Hk |- *. rewrite Hs in Hk |- *.
    rewrite (proj2 (sort_eqb_eq Prp Prp) eq_refl) in Hk |- *.
    destruct (ind_elim d) eqn:Ee; destruct (ind_ctors d) as [|c0 [|c1 cs]] eqn:Ec; cbn in Hin;
      try contradiction; try (exfalso; apply Hk; reflexivity).
    destruct Hin as [<- | []]. auto.
  Qed.

  Theorem env_iota_sound : forall t u T e, iota sg t = Some u -> erases [] t T e -> evalue e ->
    (exists D s, espine_head e = EPrim D s) ->
    exists e2, eelim_iota se e = Some e2 /\ erases [] u T e2.
  Proof.
    intros t u T e Hi He Hev (D0 & s0 & Hhd).
    assert (Hb : e <> EBox) by (intros ->; discriminate Hhd).
    destruct (iota_inv _ _ _ Hi) as (D & s & A & d & ps & P & ms & is & x & i & cd & c & ps' & xs & m &
      Ee & Ed & Et & Hlp & Hlk & Hlq & Ex & Ec & Hlp' & Hlx & Em & Eu).
    subst t u.
    destruct (Hinst _ _ _ Ee) as (d0 & Hd0 & EA & Hrules). rewrite Ed in Hd0. injection Hd0 as <-. subst A.
    pose proof (proj1 (erases_typed Sp sg) _ _ _ _ He) as Ht.
    destruct (redex_typed Sp sg Htypes [] D s true d ps P ms is x c cd i ps' xs T Ee Ed Hlp Hlk Hlq Ex Ec Hlp' Hlx Ht)
      as (Hpre_t & Hxt & Hpp & Hxs' & (RF & sF & HF) & HcT).
    destruct (redex_erased D s d ps P ms is x T e Ee Ed Hlp Hlk Hlq He Hev Hb Hxt)
      as (pre' & ib' & x' & -> & Hlib & Hs & Hpre & Hx' & Hx'v).
    pose proof (find_ctor_nth_error _ _ _ _ Ec) as Ecd.
    pose proof (find_ctor_name _ _ _ _ Ec) as Ecn.
    destruct (Hkinds D s _ true Hs Ee) as (d1 & Hd1 & Hk & HkP). rewrite Ed in Hd1. injection Hd1 as <-.
    pose proof (Hinds _ _ Ed) as Hind.
    pose proof (eargs_length _ _ _ _ _ Hpre) as Hlpre'. rewrite !length_app in Hlpre'. cbn [length] in Hlpre'.
    assert (Hps_t : args_typed Sp sg [] (ind_params d) ps).
    { exact (proj1 (proj1 (args_typed_app Sp sg ps [] (ind_params d) ([motive_type d s] ++ methods d) ([P] ++ ms)
                             ltac:(lia)) Hpre_t)). }
    destruct (sorted _ _ _ Ht) as [sT HsT].
    assert (HcT' : ctype Sp sg [] (apps P (map (subst (tsub (ps ++ xs))) (ctor_indices cd) ++
                                          [apps (Const (Ctor D (ctor_name cd))) (ps ++ xs)])) T).
    { right. rewrite Ecn. split; [exact HcT | exists sT; exact HsT]. }
    destruct (sort_eqb (ind_sort d) Prp) eqn:Esort.
    - (* a singleton proposition: its fields are proofs, [□] *)
      apply sort_eqb_eq in Esort.
      destruct (kind_singleton d cd Esort HkP (nth_error_In _ _ Ecd)) as (Eel & Ectors & Ekind).
      rewrite Ekind in Hk.
      assert (Ei : i = 0) by (rewrite Ectors in Ecd; destruct i as [|[|i]]; [reflexivity | discriminate Ecd | discriminate Ecd]).
      subst i.
      pose proof (args_props_eargs sg _ _ _ (singleton_props D d cd ps xs Ed Esort Eel Ectors Hps_t Hxs')) as HFX.
      destruct (rule_erased D s d ps P ms xs 0 cd m pre' _ Ed Hs Hrules Ecd Em Hlp Hlk Hlx Hpre HFX)
        as (m' & Hm' & Hu).
      exists (eapps m' (eiota_args D s pre' (length (ind_indices d)) (map efield_of (ctor_fields cd))
                         (repeat EBox (length xs)))).
      split; [ | exact (erases_ctype sg _ _ _ _ _ Hu HcT')].
      rewrite Hlx. apply (eelim_iota_singleton D s d pre' ib' x' cd m' Hk Hind Ectors); [rewrite Ectors in Hlk; cbn [length] in Hlk; lia | lia | ].
      rewrite Ectors in Hm'. cbn [length] in Hm'.
      destruct (firstn 1 (skipn (Datatypes.S (length (ind_params d))) pre')) as [|m0 [|m1 l]] eqn:E1;
        [discriminate Hm' | | ].
      + injection Hm' as <-. reflexivity.
      + exfalso. pose proof (f_equal (@length eterm) E1) as El. rewrite length_firstn in El. cbn [length] in El. lia.
    - (* data: the object is a constructor *)
      assert (Hsort : ind_sort d <> Prp) by (intros E; rewrite E, (proj2 (sort_eqb_eq Prp Prp) eq_refl) in Esort; discriminate Esort).
      rewrite (kind_data d Hsort) in Hk.
      assert (Hx'b : x' <> EBox).
      { intros E. destruct (apps_const_shape (Ctor D c) (ps' ++ xs)) as [Ha Hc'].
        rewrite <- Ex in Ha, Hc'.
        apply (ind_not_erasable sg Hsig [] D d (ps ++ is) Ed Hsort); [rewrite !length_app; lia | ].
        exact (box_erasable sg _ _ _ _ Hx' E Ha Hc'). }
      rewrite Ex in Hx'.
      assert (HtyC : sig_type sg (Ctor D c) = Some (ctor_type d cd)) by (cbn [sig_type]; rewrite Ed, Ec; reflexivity).
      destruct (const_type_typed_t Sp sg Htypes [] _ _ (W_Nil _ _) HtyC) as [sc Hsc].
      rewrite (ctor_type_split _ _ _ cd Ed), <- pis_app in Hsc.
      set (Fs := field_types D (length (ind_params d)) 0 (ctor_fields cd)) in *.
      set (Rc := apps (Const (Ind D)) (vars (length (ctor_fields cd)) (length (ind_params d)) ++ ctor_indices cd)) in *.
      assert (Hhead : forall H eh, erases [] (Const (Ctor D c)) H eh -> eh <> EBox ->
                conv sg H (pis (ind_params d ++ Fs) Rc) /\ eh = ECtor D c).
      { intros H eh Hh Hb'. split.
        - pose proof (const_head Sp sg [] _ _ HtyC _ (proj1 (erases_typed Sp sg) _ _ _ _ Hh)) as Hc1.
          rewrite (ctor_type_split _ _ _ cd Ed), <- pis_app in Hc1. exact Hc1.
        - destruct (erases_const_inv sg _ _ _ _ Hh) as [E | [(f & E & _) | [(D' & c' & E & ->) | (D' & s' & E & _)]]];
            [contradiction | discriminate E | injection E as <- <-; reflexivity | discriminate E]. }
      assert (Hlc : length (ind_params d ++ Fs) = length (ps' ++ xs))
        by (unfold Fs; rewrite !length_app, field_types_length; lia).
      destruct (erases_apps_inv sg (ps' ++ xs) [] _ _ _ _ _ _ _ Hlc Hx' Hx'v Hx'b Hhead (no_index_ctor sg D c) Hsc)
        as (es' & -> & Hargs & _).
      assert (Hlp'' : length (ind_params d) = length ps') by lia.
      destruct (eargs_app sg ps' [] _ _ _ _ Hlp'' Hargs) as [_ Hxs_e].
      pose proof (eargs_conv sg _ _ _ _ Hxs_e _ _ _ (conv_subst_tele_tsub sg _ _ Hpp Fs 0) HF) as HFX.
      destruct (rule_erased D s d ps P ms xs i cd m pre' _ Ed Hs Hrules Ecd Em Hlp Hlk Hlx Hpre HFX)
        as (m' & Hm' & Hu).
      pose proof (eargs_length _ _ _ _ _ Hargs) as Hles. rewrite length_app in Hles.
      exists (eapps m' (eiota_args D s pre' (length (ind_indices d)) (map efield_of (ctor_fields cd))
                         (skipn (length ps') es'))).
      split; [ | exact (erases_ctype sg _ _ _ _ _ Hu HcT')].
      rewrite Hlp'. apply (eelim_iota_data D s d pre' ib' c es' i cd m' Hk Hind); [lia | lia | exact Ec | lia | exact Hm'].
  Qed.
End Iota.

(** ** The erased signature *)

Section Env.
  Variable sg : signature.
  Variable fuel : nat.

  (** Every instance into a sort other than Prop has, in a strict erasure,
      the kind of its family, which computes. *)
  Lemma erase_entries_elims : forall es se, erase_entries Sp sg fuel true es = Ok se ->
    forall D s A act, find_elim es D s = Some (A, act) -> s <> Prp ->
    exists d, sig_ind sg D = Some d /\ efind_elim se D s = Some (kind_of d) /\ kind_of d <> KProp.
  Proof.
    induction es as [|e es IH]; intros se H D s A act Hf Hs; [discriminate Hf | ].
    cbn [erase_entries] in H. apply bind_ok in H as (se' & Hse' & H).
    apply bind_ok in H as (e' & He' & H). injection H as <-.
    destruct e as [d0 | D' s' A' act' | f A' b']; cbn [find_elim] in Hf.
    - cbn in He'. destruct (reserved_name (ind_name d0)); [discriminate He' | ]. injection He' as <-.
      cbn [efind_elim]. exact (IH _ Hse' _ _ _ _ Hf Hs).
    - cbn [erase_entry] in He'. destruct act'; cbn [negb] in He'; [ | discriminate He'].
      destruct (sig_ind sg D') as [d'|] eqn:Hd'; [ | discriminate He'].
      destruct (sort_eqb s' Prp) eqn:Es'.
      + injection He' as <-. cbn [efind_elim].
        destruct (String.eqb D' D && sort_eqb s' s) eqn:Ek.
        * apply andb_prop in Ek as [_ Ek]. apply sort_eqb_eq in Ek, Es'. subst. contradiction.
        * exact (IH _ Hse' _ _ _ _ Hf Hs).
      + assert (Hk : exists k, kind_of d' = k /\ k <> KProp /\ e' = EEElim D' s' k).
        { destruct (kind_of d') eqn:Ek; try (injection He' as <-; eexists; split; [reflexivity | split; [discriminate | reflexivity]]).
          discriminate He'. }
        destruct Hk as (k & Ek & HkP & ->). cbn [efind_elim].
        destruct (String.eqb D' D && sort_eqb s' s) eqn:Em.
        * apply andb_prop in Em as [E1 E2]. apply String.eqb_eq in E1. apply sort_eqb_eq in E2. subst D' s'.
          exists d'. rewrite Ek. auto.
        * exact (IH _ Hse' _ _ _ _ Hf Hs).
    - cbn [erase_entry] in He'. apply bind_ok in He' as (b'' & _ & He'). injection He' as <-.
      cbn [efind_elim]. exact (IH _ Hse' _ _ _ _ Hf Hs).
  Qed.

  Hypothesis Hsig : signature_typed Sp sg.
  Hypothesis Hinst : instances_checked Sp sg.
  Hypothesis Hdist : ctors_distinct sg.
  Hypothesis Hgen : elim_types_generated sg.
  Hypothesis Hrec : rec_ok sg.
  Hypothesis Hsing : singleton_ok sg.

  (** A signature whose declarations are as registration leaves them is
      related to its strict erasure. *)
  Theorem env_related : forall se, erase_env Sp sg fuel = Erased se -> erases_env sg se.
  Proof.
    intros se H. unfold erase_env, to_erase_result in H.
    destruct (erase_env_e Sp sg fuel true) as [se'|[e|st t]] eqn:E; try discriminate H. injection H as ->.
    unfold erase_env_e in E.
    assert (Hinds : forall D d, sig_ind sg D = Some d -> efind_ind se D = Some (erase_ind d))
      by (intros D d Hd; exact (erase_entries_inds Sp sg fuel true _ _ E D d Hd)).
    assert (Hkinds : forall D s A act, s <> Prp -> sig_elim sg D s = Some (A, act) ->
              exists d, sig_ind sg D = Some d /\ efind_elim se D s = Some (kind_of d) /\ kind_of d <> KProp)
      by (intros D s A act Hs He; exact (erase_entries_elims _ _ E D s A act He Hs)).
    constructor.
    - exact Hsig.
    - intros f A b Hf. destruct (erase_entries_defs Sp sg fuel true _ _ E f A b Hf) as (b' & Hb & Hb').
      exists b'. split; [exact Hb' | ].
      assert (Hty : sig_type sg (Def f) = Some A) by (cbn [sig_type]; rewrite Hf; reflexivity).
      assert (Hdl : sig_delta sg (Def f) = Some b) by (cbn [sig_delta]; rewrite Hf; reflexivity).
      exact (erase_sound sg fuel Hsig Hdist Hgen b [] A b' (proj1 (proj2 Hsig) _ _ _ Hty Hdl) Hb).
    - exact Hinds.
    - exact (erase_entries_prims Sp sg fuel true _ _ E prim_unit eq_refl).
    - exact (erase_entries_prims Sp sg fuel true _ _ E prim_bool eq_refl).
    - intros D s A act Hs He. destruct (Hkinds D s A act Hs He) as (d & _ & Hk & _). rewrite Hk. discriminate.
    - intros t u T e Hi Ht Hev Hhd. exact (env_iota_sound sg Hsig Hinst Hrec Hsing se Hinds Hkinds t u T e Hi Ht Hev Hhd).
    - intros D d c ps xs Hd Hs He Hc Hps Hxs. rewrite (sig_ind_name _ _ _ Hd) in Hxs |- *.
      exact (singleton_props sg Hsing D d c ps xs Hd Hs He Hc Hps Hxs).
  Qed.
End Env.

(** ** A checked signature and its erasure *)

Theorem env_related_checked : forall sg fenv se, wf_checked sg -> erase_env Sp sg fenv = Erased se ->
  erases_env sg se.
Proof.
  intros sg fenv se H He. destruct (checked_fields sg H) as (Hinv & Hrec & Hsing).
  exact (env_related sg fenv (inv_typed _ Hinv) (inv_instances Hinv) (checked_ctors_distinct _ H)
           (checked_elim_types _ H) Hrec Hsing se He).
Qed.
