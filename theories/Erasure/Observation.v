(** * The observation of related values

    A value of the source evaluator, related to an erased term at an
    observable type, is observed alike ([observation_src]): the core of
    [erasure_observation] (Contracts.v).  It rests on two facts:
    - an observable type is not erasable: it reduces to Bool, Unit, a
      family of data or a Σ, none of which is convertible to an arity or
      to a type in Prop (Erasure/Simulation.v);
    - the canonical forms of closed values ([value_shape] of
      PTS/Values.v of the kernel): a value whose type reduces to Bool is
      a boolean, to Unit [tt], to a Σ a pair, to a family a constructor
      of it applied to all its arguments, in a type-correct signature
      whose instances have types of the arity of their eliminator
      ([instances_shaped]).  That a checked signature is both is
      [checked_signature_typed] and [checked_instances_shaped] of
      Contracts.v.

    The erased side follows the derivation of the relation: at a type
    that is not erasable no subterm of a constructor spine is erased to
    [□] ([erases_apps_inv_ne]), so the erased value is the erased
    constructor applied to erasures of the arguments, each at its field
    type; the observation recurses into the fields of data. *)

From Stdlib Require Import String List Bool Arith Lia Relations.
Import ListNotations.
From DepTypes.Common Require Import Outcome.
From DepTypes.PTS Require Import Syntax Telescope Spec Signature Reduction SubstLaws Confluence Guard Typing
  TypingSubst Inversion SubjectRed BidirSound EvalSrc Values.
From DepTypes.Configs Require Import Predicative.
From DepTypes.MLTT Require Import Constants Families.
From IndTypes.Data Require Import Lists.
From CIC.Erasure Require Import Target Erase Observe Relation Simulation.

Local Open Scope list_scope.

Local Notation Sp := predicative_prop.


(** ** The observation *)

Fixpoint tsize (t : term) : nat :=
  match t with
  | App f a => S (tsize f + tsize a)
  | Pair a b => S (tsize a + tsize b)
  | _ => 0
  end.

Lemma nth_error_subst_tele : forall Ts sb j,
  nth_error (subst_tele sb Ts) j = option_map (subst (upn j sb)) (nth_error Ts j).
Proof.
  induction Ts as [|T Ts IH]; intros sb [|j]; cbn [subst_tele nth_error]; try reflexivity.
  rewrite IH. destruct (nth_error Ts j); cbn [option_map]; [ | reflexivity].
  f_equal. apply subst_ext. intros n. apply up_sub_upn.
Qed.

Section Observation.
  Variable sg : signature.
  Hypothesis Hsig : signature_typed Sp sg.
  Hypothesis Helim : instances_shaped sg.
  Local Notation typed := (has_type Sp sg).
  Local Notation erases := (erases Sp sg).
  Local Notation "t ≡ u" := (conv sg t u).

  (** An argument erased against a telescope, at its entry instantiated
      by the arguments before it. *)
  Lemma eargs_nth : forall G Ts args es, eargs sg G Ts args es -> forall j T a e,
    nth_error Ts j = Some T -> nth_error args j = Some a -> nth_error es j = Some e ->
    erases G a (subst (tsub (firstn j args)) T) e.
  Proof.
    intros G Ts args es H. induction H as [|T0 Ts a0 args a0' args' Ha Hargs IH]; intros j T a e HT Ha0 He.
    - destruct j; discriminate HT.
    - destruct j as [|j]; cbn [nth_error firstn] in *.
      + injection HT as <-. injection Ha0 as <-. injection He as <-. rewrite subst_tsub_nil. exact Ha.
      + pose proof (IH j (subst (upn j (scons a0 Var)) T) a e ltac:(rewrite nth_error_subst_tele, HT; reflexivity)
                      Ha0 He) as H1.
        assert (Hj : j < length args) by (apply nth_error_Some; congruence).
        rewrite (subst_tsub_cons a0 (firstn j args) j) in H1; [exact H1 | rewrite length_firstn; lia].
  Qed.

  (** At a type that is not erasable, a spine of a head with known
      types and erasures is erased to the erased head applied to
      erasures of its arguments against the telescope of the head. *)
  Theorem erases_apps_inv_ne : forall args G h T e Ts R0 s0 eh0, length Ts = length args ->
    erases G (apps h args) T e -> ~ erasable_at Sp sg G T ->
    (forall H eh, erases G h H eh -> ~ erasable_at Sp sg G H -> H ≡ pis Ts R0 /\ eh = eh0) ->
    (forall l, ~ index_position sg (apps h l)) ->
    typed G (pis Ts R0) (Srt s0) ->
    exists es, e = eapps eh0 es /\ eargs sg G Ts args es /\ subst (tsub args) R0 ≡ T.
  Proof.
    induction args as [|a args IH] using rev_ind; intros G h T e Ts R0 s0 eh0 Hl He Hne Hh Hi HP.
    - destruct Ts; [ | discriminate Hl]. destruct (Hh T e He Hne) as [Hc ->].
      exists []. split; [reflexivity | split; [constructor | ]]. rewrite subst_tsub_nil. apply conv_sym, Hc.
    - assert (HTs : Ts <> []) by (intros ->; rewrite length_app in Hl; cbn in Hl; lia).
      destruct (exists_last HTs) as (Ts' & Tl & ->).
      rewrite !length_app in Hl. cbn [length] in Hl.
      rewrite apps_snoc in He.
      destruct (erases_app_inv sg _ _ _ _ _ He) as [(-> & _ & HE) | (A & B & f' & a' & -> & Hf & Ha & HT)];
        [exfalso; exact (Hne HE) | ].
      destruct Ha as [Ha | (_ & _ & Hip)]; [ | exfalso; exact (Hi _ Hip)].
      assert (Hne' : ~ erasable_at Sp sg G (Pi A B)).
      { intros HE. apply Hne.
        apply (erasable_at_conv sg _ _ _ (erasable_pi_cod sg Hsig _ _ _ _ HE (proj1 (erases_typed Sp sg) _ _ _ _ Ha))).
        exact (ctype_conv_of Sp sg _ _ _ HT). }
      rewrite pis_app in HP. cbn [pis] in HP.
      assert (Hh' : forall H eh, erases G h H eh -> ~ erasable_at Sp sg G H -> H ≡ pis Ts' (Pi Tl R0) /\ eh = eh0).
      { intros H eh H1 H2. destruct (Hh H eh H1 H2) as [Hc Heq]. rewrite pis_app in Hc. split; [exact Hc | exact Heq]. }
      destruct (IH G h (Pi A B) f' Ts' (Pi Tl R0) s0 eh0 ltac:(lia) Hf Hne' Hh' Hi HP) as (es & -> & Hargs & Hc).
      cbn [subst] in Hc. apply pi_inj in Hc as [HcA HcB].
      destruct (typed_pis_inst Sp sg _ _ _ _ _ (eargs_typed sg _ _ _ _ Hargs) HP) as [s' HPi]. cbn [subst] in HPi.
      destruct (inv_pi Sp sg _ _ _ _ HPi) as (s1 & _ & _ & HTl & _ & _ & _).
      pose proof (X_Conv _ _ _ _ _ _ _ _ Ha HTl (conv_sym _ _ HcA)) as Ha'.
      exists (es ++ [a']). split; [rewrite eapps_snoc; reflexivity | split].
      + apply (eargs_app_join sg args G Ts' [Tl] [a] es [a'] Hargs). cbn [subst_tele].
        constructor; [exact Ha' | constructor].
      + rewrite subst_tsub_snoc. eapply conv_trans; [ | exact (ctype_conv_of Sp sg _ _ _ HT)].
        apply conv_subst. exact HcB.
  Qed.

  (** A constructor of data at a type that is not erasable: the erased
      constructor, applied to its arguments erased at their fields. *)
  Lemma ctor_erasure : forall D d c i cd args T w,
    sig_ind sg D = Some d -> find_ctor (ind_ctors d) c = Some (i, cd) ->
    length args = length (ind_params d) + length (ctor_fields cd) ->
    erases [] (apps (Const (Ctor D c)) args) T w -> ~ erasable_at Sp sg [] T ->
    exists es, w = eapps (ECtor D c) es /\
      eargs sg [] (ind_params d ++ field_types (ind_name d) (length (ind_params d)) 0 (ctor_fields cd)) args es /\
      subst (tsub args) (apps (Const (Ind (ind_name d)))
                           (vars (length (ctor_fields cd)) (length (ind_params d)) ++ ctor_indices cd)) ≡ T.
  Proof.
    intros D d c i cd args T w Hd Hc Hl Hw Hne.
    assert (Hty : sig_type sg (Ctor D c) = Some (ctor_type d cd)) by (cbn [sig_type]; rewrite Hd, Hc; reflexivity).
    destruct (const_type_typed Sp sg Hsig [] _ _ (W_Nil _ _) Hty) as [s0 Hs0].
    unfold ctor_type in Hs0. cbv zeta in Hs0.
    apply (erases_apps_inv_ne args [] (Const (Ctor D c)) T w _ _ s0 (ECtor D c)).
    - rewrite length_app, field_types_length. lia.
    - exact Hw.
    - exact Hne.
    - intros H0 eh Hh Hne0.
      destruct (erases_const_inv sg _ _ _ _ Hh) as [-> | [(f0 & E & _) | [(D' & c' & E & ->) | (D' & s' & E & _ & _)]]].
      + exfalso. apply Hne0. apply (box_erasable sg _ _ _ _ Hh eq_refl); intros; discriminate.
      + discriminate E.
      + injection E as <- <-. split; [ | reflexivity].
        exact (const_head Sp sg _ _ _ Hty _ (proj1 (erases_typed Sp sg) _ _ _ _ Hh)).
      + discriminate E.
    - intros l (D' & s' & d' & E & _). rewrite spine_head_apps in E. discriminate E.
    - exact Hs0.
  Qed.

  (** The type of a value at an observable type reduces to a type. *)
  Lemma red_typed_type : forall v T Y k, typed [] v T -> red sg T Y -> shape_of Y = Some k -> k <> SSrt ->
    exists s, typed [] Y (Srt s).
  Proof.
    intros v T Y k H HY Hk Hs. destruct (validity Sp sg Hsig _ _ _ H) as [[s0 ->] | [s0 HT]].
    - exfalso. rewrite (red_fixed sg _ (red1_srt sg s0) _ HY) in Hk. cbn in Hk. injection Hk as <-. apply Hs; reflexivity.
    - exists s0. exact (subject_red Sp sg Hsig _ _ _ _ HT HY).
  Qed.

  Lemma ind_args_typed : forall D d args s, sig_ind sg D = Some d ->
    length (ind_params d ++ ind_indices d) = length args ->
    typed [] (apps (Const (Ind D)) args) (Srt s) -> args_typed Sp sg [] (ind_params d ++ ind_indices d) args.
  Proof.
    intros D d args s Hd Hl H.
    assert (Hty : sig_type sg (Ind D) = Some (ind_type d)) by (cbn [sig_type]; rewrite Hd; reflexivity).
    destruct (const_type_typed Sp sg Hsig [] _ _ (W_Nil _ _) Hty) as [s0 Hs0]. unfold ind_type in Hs0.
    exact (proj1 (apps_inv Sp sg args [] (Const (Ind D)) _ _ _ _ Hl H (const_head Sp sg _ _ _ Hty) Hs0)).
  Qed.

  Lemma not_erasable_red : forall T Y, red sg T Y -> (erasable_at Sp sg [] Y -> False) -> ~ erasable_at Sp sg [] T.
  Proof. intros T Y HY H HE. exact (H (erasable_at_conv sg _ _ _ HE (red_conv _ _ HY))). Qed.

  Theorem observation : forall n v T w, tsize v < n -> vvalue sg v -> Observable sg T ->
    erases [] v T w -> value_observation sg T v w.
  Proof.
    induction n as [|n IHn]; intros v T w Hsz Hv HO Hw; [lia | ].
    pose proof (proj1 (erases_typed Sp sg) _ _ _ _ Hw) as Tv.
    destruct HO as [T HT | T HT | T HT Hnat | T A HT Hlist HA | T A m HT Hvec Hnat HA | T A B HT HA HB
                   | T A B K HT HA Hsyn HK].
    (* Bool *)
    - destruct (value_shape Sp sg Hsig Helim v T Bool SBool Hv Tv HT eq_refl ltac:(discriminate) ltac:(discriminate))
        as [-> | ->].
      + destruct (erases_prim_ctor_inv sg _ _ _ _ Hw (or_intror (or_introl eq_refl)))
          as [(-> & HE) | [(E & _) | [(_ & ->) | (E & _)]]]; [ | discriminate E | | discriminate E].
        * exfalso. exact (not_erasable_red _ _ HT (bool_not_erasable sg Hsig []) HE).
        * apply VO_True. exact HT.
      + destruct (erases_prim_ctor_inv sg _ _ _ _ Hw (or_intror (or_intror eq_refl)))
          as [(-> & HE) | [(E & _) | [(E & _) | (_ & ->)]]]; [ | discriminate E | discriminate E | ].
        * exfalso. exact (not_erasable_red _ _ HT (bool_not_erasable sg Hsig []) HE).
        * apply VO_False. exact HT.
    (* Unit *)
    - pose proof (value_shape Sp sg Hsig Helim v T Unit SUnit Hv Tv HT eq_refl ltac:(discriminate) ltac:(discriminate))
        as ->.
      destruct (erases_prim_ctor_inv sg _ _ _ _ Hw (or_introl eq_refl))
        as [(-> & HE) | [(_ & ->) | [(E & _) | (E & _)]]]; [ | | discriminate E | discriminate E].
      + exfalso. exact (not_erasable_red _ _ HT (unit_not_erasable sg Hsig []) HE).
      + apply VO_Tt. exact HT.
    (* ℕ *)
    - destruct (value_shape Sp sg Hsig Helim v T NatT (SInd "Nat") Hv Tv HT eq_refl ltac:(discriminate) ltac:(discriminate))
        as (c & args & d & i & cd & -> & Hd & Hc & Hl).
      rewrite Hnat in Hd. injection Hd as <-.
      assert (Hne : ~ erasable_at Sp sg [] T)
        by exact (not_erasable_red _ _ HT (ind_not_erasable sg Hsig [] "Nat" nat_desc [] Hnat ltac:(discriminate) eq_refl)).
      destruct (ctor_erasure _ _ _ _ _ _ _ _ Hnat Hc Hl Hw Hne) as (es & -> & Hes & _).
      pose proof (eargs_length sg _ _ _ _ Hes) as Hles.
      unfold nat_desc in Hc. cbn [ind_ctors find_ctor ctor_name] in Hc.
      destruct (String.eqb "zero" c) eqn:E1.
      + apply String.eqb_eq in E1. subst c. injection Hc as <- <-.
        destruct args; [ | discriminate Hl]. destruct es; [ | discriminate Hles].
        apply VO_Zero. exact HT.
      + destruct (String.eqb "succ" c) eqn:E2; [ | discriminate Hc]. apply String.eqb_eq in E2. subst c.
        cbn [option_map fst snd] in Hc. injection Hc as <- <-.
        destruct args as [|k [|]]; try discriminate Hl. destruct es as [|wk [|]]; try discriminate Hles.
        change (eargs sg [] [NatT] [k] [wk]) in Hes.
        pose proof (eargs_nth _ _ _ _ Hes 0 NatT k wk eq_refl eq_refl eq_refl) as Hk. cbn in Hk.
        destruct Hv as (_ & _ & Hvk).
        apply VO_Succ; [exact HT | ].
        apply (IHn k NatT wk); [cbn in Hsz; lia | exact Hvk | apply O_Nat; [apply rt_refl | exact Hnat] | exact Hk].
    (* lists *)
    - destruct (value_shape Sp sg Hsig Helim v T (ListT A) (SInd "List") Hv Tv HT eq_refl ltac:(discriminate) ltac:(discriminate))
        as (c & args & d & i & cd & -> & Hd & Hc & Hl).
      rewrite Hlist in Hd. injection Hd as <-.
      assert (Hne : ~ erasable_at Sp sg [] T)
        by exact (not_erasable_red _ _ HT (ind_not_erasable sg Hsig [] "List" list_desc [A] Hlist ltac:(discriminate) eq_refl)).
      destruct (ctor_erasure _ _ _ _ _ _ _ _ Hlist Hc Hl Hw Hne) as (es & -> & Hes & Hcv).
      pose proof (eargs_length sg _ _ _ _ Hes) as Hles.
      destruct (red_typed_type _ _ _ _ Tv HT eq_refl ltac:(discriminate)) as [sL HL].
      pose proof (ind_args_typed "List" list_desc [A] sL Hlist eq_refl HL) as HAt.
      change (args_typed Sp sg [] [Srt (Univ 0)] [A]) in HAt.
      destruct (args_typed_cons_inv Sp sg _ _ _ _ _ HAt) as [HA0 _].
      unfold list_desc in Hc. cbn [ind_ctors find_ctor ctor_name] in Hc.
      destruct (String.eqb "nil" c) eqn:E1.
      + apply String.eqb_eq in E1. subst c. injection Hc as <- <-.
        destruct args as [|A' [|]]; try discriminate Hl. destruct es as [|wA [|]]; try discriminate Hles.
        eapply VO_Nil. exact HT.
      + destruct (String.eqb "cons" c) eqn:E2; [ | discriminate Hc]. apply String.eqb_eq in E2. subst c.
        cbn [option_map fst snd] in Hc. injection Hc as <- <-.
        destruct args as [|A' [|x [|xs [|]]]]; try discriminate Hl.
        destruct es as [|wA [|wx [|wxs [|]]]]; try discriminate Hles.
        change (eargs sg [] [Srt (Univ 0); Var 0; App (Const (Ind "List")) (Var 1)] [A'; x; xs] [wA; wx; wxs]) in Hes.
        change (App (Const (Ind "List")) A' ≡ T) in Hcv.
        assert (HAA : A' ≡ A).
        { assert (Hc2 : apps (Const (Ind "List")) [A'] ≡ apps (Const (Ind "List")) [A])
            by (eapply conv_trans; [exact Hcv | exact (red_conv _ _ HT)]).
          apply conv_ind_spine in Hc2. inversion Hc2; assumption. }
        pose proof (eargs_nth _ _ _ _ Hes 1 (Var 0) x wx eq_refl eq_refl eq_refl) as Hx. cbn in Hx.
        pose proof (eargs_nth _ _ _ _ Hes 2 (App (Const (Ind "List")) (Var 1)) xs wxs eq_refl eq_refl eq_refl) as Hxs.
        cbn in Hxs.
        destruct Hv as (_ & (_ & _ & Hvx) & Hvxs).
        cbn in Hsz.
        eapply VO_Cons; [exact HT | | ].
        * apply (IHn x A wx); [lia | exact Hvx | exact HA | ].
          exact (X_Conv _ _ _ _ _ _ _ _ Hx HA0 HAA).
        * apply (IHn xs (ListT A) wxs); [lia | exact Hvxs | eapply O_List; [apply rt_refl | exact Hlist | exact HA] | ].
          apply (X_Conv _ _ _ _ _ _ _ _ Hxs HL). apply conv_app_arg. exact HAA.
    (* vectors *)
    - destruct (value_shape Sp sg Hsig Helim v T (VecT A m) (SInd "Vec") Hv Tv HT eq_refl ltac:(discriminate) ltac:(discriminate))
        as (c & args & d & i & cd & -> & Hd & Hc & Hl).
      rewrite Hvec in Hd. injection Hd as <-.
      assert (Hne : ~ erasable_at Sp sg [] T)
        by exact (not_erasable_red _ _ HT (ind_not_erasable sg Hsig [] "Vec" vec_desc [A; m] Hvec ltac:(discriminate) eq_refl)).
      destruct (ctor_erasure _ _ _ _ _ _ _ _ Hvec Hc Hl Hw Hne) as (es & -> & Hes & Hcv).
      pose proof (eargs_length sg _ _ _ _ Hes) as Hles.
      destruct (red_typed_type _ _ _ _ Tv HT eq_refl ltac:(discriminate)) as [sV HV].
      pose proof (ind_args_typed "Vec" vec_desc [A; m] sV Hvec eq_refl HV) as HAt.
      change (args_typed Sp sg [] [Srt (Univ 0); NatT] [A; m]) in HAt.
      destruct (args_typed_cons_inv Sp sg _ _ _ _ _ HAt) as [HA0 _].
      unfold vec_desc in Hc. cbn [ind_ctors find_ctor ctor_name] in Hc.
      destruct (String.eqb "nil" c) eqn:E1.
      + apply String.eqb_eq in E1. subst c. injection Hc as <- <-.
        destruct args as [|A' [|]]; try discriminate Hl. destruct es as [|wA [|]]; try discriminate Hles.
        eapply VO_VNil. exact HT.
      + destruct (String.eqb "cons" c) eqn:E2; [ | discriminate Hc]. apply String.eqb_eq in E2. subst c.
        cbn [option_map fst snd] in Hc. injection Hc as <- <-.
        destruct args as [|A' [|k [|x [|xs [|]]]]]; try discriminate Hl.
        destruct es as [|wA [|wk [|wx [|wxs [|]]]]]; try discriminate Hles.
        change (eargs sg [] [Srt (Univ 0); NatT; Var 1; App (App (Const (Ind "Vec")) (Var 2)) (Var 1)]
                  [A'; k; x; xs] [wA; wk; wx; wxs]) in Hes.
        change (App (App (Const (Ind "Vec")) A') (App (Const (Ctor "Nat" "succ")) k) ≡ T) in Hcv.
        assert (HAA : A' ≡ A).
        { assert (Hc2 : apps (Const (Ind "Vec")) [A'; App (Const (Ctor "Nat" "succ")) k] ≡ apps (Const (Ind "Vec")) [A; m])
            by (eapply conv_trans; [exact Hcv | exact (red_conv _ _ HT)]).
          apply conv_ind_spine in Hc2. inversion Hc2; assumption. }
        pose proof (eargs_nth _ _ _ _ Hes 1 NatT k wk eq_refl eq_refl eq_refl) as Hk. cbn in Hk.
        pose proof (eargs_nth _ _ _ _ Hes 2 (Var 1) x wx eq_refl eq_refl eq_refl) as Hx. cbn in Hx.
        pose proof (eargs_nth _ _ _ _ Hes 3 (App (App (Const (Ind "Vec")) (Var 2)) (Var 1)) xs wxs
                      eq_refl eq_refl eq_refl) as Hxs. cbn in Hxs.
        destruct Hv as (_ & (_ & (_ & _ & Hvk) & Hvx) & Hvxs).
        cbn in Hsz.
        (* the type of the tail *)
        assert (HVk : exists s, typed [] (VecT A k) (Srt s)).
        { assert (Hty : sig_type sg (Ind "Vec") = Some (ind_type vec_desc)) by (cbn [sig_type]; rewrite Hvec; reflexivity).
          pose proof (T_Const Sp sg [] _ _ (W_Nil Sp sg) eq_refl Hty) as HVec.
          change (typed [] (Const (Ind "Vec")) (pis [Srt (Univ 0); NatT] (Srt (Univ 0)))) in HVec.
          assert (Hargs : args_typed Sp sg [] [Srt (Univ 0); NatT] [A; k]).
          { constructor; [exact HA0 | ]. cbn [subst_tele subst]. constructor; [ | constructor].
            exact (proj1 (erases_typed Sp sg) _ _ _ _ Hk). }
          exists (Univ 0). exact (typed_apps Sp sg _ _ _ _ _ Hargs HVec). }
        destruct HVk as [sk HVk].
        eapply VO_VCons; [exact HT | | | ].
        * apply (IHn k NatT wk); [lia | exact Hvk | apply O_Nat; [apply rt_refl | exact Hnat] | exact Hk].
        * apply (IHn x A wx); [lia | exact Hvx | exact HA | ].
          exact (X_Conv _ _ _ _ _ _ _ _ Hx HA0 HAA).
        * apply (IHn xs (VecT A k) wxs); [lia | exact Hvxs | eapply O_Vec; [apply rt_refl | exact Hvec | exact Hnat | exact HA] | ].
          apply (X_Conv _ _ _ _ _ _ _ _ Hxs HVk). apply conv_app; [apply conv_app_arg; exact HAA | apply conv_refl].
    (* pairs of observable components *)
    - destruct (value_shape Sp sg Hsig Helim v T (Sigma A B) SSigma Hv Tv HT eq_refl ltac:(discriminate) ltac:(discriminate))
        as (a & b & ->).
      destruct (erases_pair_inv sg _ _ _ _ _ Hw) as [(-> & HE) | (A' & B' & s & a' & b' & -> & HS & Ha & Hb & Hc)].
      { exfalso. exact (not_erasable_red _ _ HT (sigma_not_erasable sg Hsig [] A B) HE). }
      assert (Hcs : Sigma A' B' ≡ Sigma A B)
        by (eapply conv_trans; [exact (ctype_conv_of Sp sg _ _ _ Hc) | exact (red_conv _ _ HT)]).
      apply sigma_inj in Hcs as [HAA HBB].
      destruct (red_typed_type _ _ _ _ Tv HT eq_refl ltac:(discriminate)) as [sS HS'].
      destruct (inv_sigma Sp sg _ _ _ _ HS') as (s1 & s2 & _ & HA0 & HB0 & _ & _).
      pose proof (X_Conv _ _ _ _ _ _ _ _ Ha HA0 HAA) as Ha'.
      pose proof (typing_subst1 Sp sg _ _ _ _ _ (proj1 (erases_typed Sp sg) _ _ _ _ Ha') HB0) as HBa.
      change (subst1 (Srt s2) a) with (Srt s2) in HBa.
      destruct Hv as [Hva Hvb]. cbn in Hsz.
      eapply VO_Pair; [exact HT | | ].
      + apply (IHn a A a'); [lia | exact Hva | exact HA | exact Ha'].
      + apply (IHn b (subst1 B a) b'); [lia | exact Hvb | exact (HB a) | ].
        apply (X_Conv _ _ _ _ _ _ _ _ Hb HBa). apply conv_subst. exact HBB.
    (* a witness and a proof *)
    - destruct (value_shape Sp sg Hsig Helim v T (Sigma A B) SSigma Hv Tv HT eq_refl ltac:(discriminate) ltac:(discriminate))
        as (a & b & ->).
      destruct (erases_pair_inv sg _ _ _ _ _ Hw) as [(-> & HE) | (A' & B' & s & a' & b' & -> & HS & Ha & Hb & Hc)].
      { exfalso. exact (not_erasable_red _ _ HT (sigma_not_erasable sg Hsig [] A B) HE). }
      assert (Hcs : Sigma A' B' ≡ Sigma A B)
        by (eapply conv_trans; [exact (ctype_conv_of Sp sg _ _ _ Hc) | exact (red_conv _ _ HT)]).
      apply sigma_inj in Hcs as [HAA _].
      destruct (red_typed_type _ _ _ _ Tv HT eq_refl ltac:(discriminate)) as [sS HS'].
      destruct (inv_sigma Sp sg _ _ _ _ HS') as (s1 & s2 & _ & HA0 & _ & _ & _).
      destruct Hv as [Hva _]. cbn in Hsz.
      eapply VO_Witness; [exact HT | exact Hsyn | exact HK | ].
      apply (IHn a A a'); [lia | exact Hva | exact HA | exact (X_Conv _ _ _ _ _ _ _ _ Ha HA0 HAA)].
  Qed.
End Observation.

(** For the evaluator of source programs. *)
Corollary observation_src : forall sg, signature_typed Sp sg -> instances_shaped sg ->
  forall fsrc t T v w, Observable sg T -> eval_src sg fsrc t = CbvValue v -> erases Sp sg [] v T w ->
  value_observation sg T v w.
Proof.
  intros sg Hsig Helim fsrc t T v w HO Hv Hw. rewrite (proj1 (eval_src_nested fsrc) t) in Hv.
  exact (observation sg Hsig Helim (S (tsize v)) v T w (Nat.lt_succ_diag_r _) (eval_nested_vvalue _ _ _ _ Hv) HO Hw).
Qed.
