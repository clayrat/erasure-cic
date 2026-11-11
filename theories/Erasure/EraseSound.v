(** * The function of erasure is sound for its relation

    [erase] of Erase.v, run on a term typed by the declarative rules in
    a type-correct signature, produces an erasure in the relation
    [erases] of Relation.v ([erase_sound]); with the soundness of the
    kernel for the declarative rules, so does it on a checked term
    ([erasure_sound] of Contracts.v).

    The walk passes down types it computed itself: the weak-head forms
    of the types it was given, and the types [infer] synthesizes for
    functions, scrutinees and projected pairs.  The declarative
    derivation gives every subterm some type, perhaps another one; the
    two are related by
    - the injectivity of Π and Σ and of the spines of a family
      (PTS.Confluence, PTS.Inversion);
    - the uniqueness of synthesized types up to conversion: a term that
      synthesizes [A] has only types convertible to [A]
      ([synth_unique] of PTS/BidirSound.v).  A λ synthesizes nothing, so the domain-free λ
      of the kernel, whose types are not unique, never meets it;
    - context conversion, for the body of a λ under the domain read off
      the weak-head form.

    The decision of erasability agrees with the declarative rules
    ([erasable_consistent], the obligation
    [erasure_decision_consistent] of Contracts.v): the sort that
    [sort_of_e] finds structurally is the one every typing gives the
    type ([sort_of_e_sound]).  For a neutral spine it instantiates the
    type of the head, which every other type of the head is convertible
    to: a variable, a constant and a [fix] by their typing rules, any
    other head by [synth_unique]; for a match, by the motive at the
    indices of the type of the scrutinee unfolded to its family.

    Two choices of [erase] serve this proof (Erase.v).  [sort_of_e]
    reads the indices of the scrutinee of a match only off a type that
    unfolds to its family: otherwise relating them to the indices of a
    typing would need the head normalization of the kernel's
    reduction.  And an instance into Prop is erased to [□] outright:
    its type has the sort Prop ([elim_prop_erasable]), while the sort
    [sort_of_e] finds for a type convertible to it is Prop only by the
    uniqueness of the sorts of types up to conversion, not proved. *)

From Stdlib Require Import String List Bool Arith Lia Relations.
Import ListNotations.
From DepTypes.Common Require Import Result Traced.
From DepTypes.PTS Require Import Syntax Telescope Spec Signature Reduction SubstLaws NormalOrder Confluence
  Guard Typing TypingSubst Inversion SubjectRed Bidir BidirSound.
From DepTypes.Configs Require Import Predicative.
From IndTypes Require Import Telescope.
From IndTypes.Elim Require Import Generate.
From IndTypes.Checked Require Import Invariants IotaTyped.
From CIC.Erasure Require Import Target Erase Relation.

Local Open Scope list_scope.

Local Notation Sp := predicative_prop.

Section Sound.
  Variable sg : signature.
  Variable fuel : nat.
  (** A type-correct signature with distinct constructor names, whose
      instances have the generated types: a checked signature
      (Checked/SigTyped.v and Checked/Shaped.v of elim-inductive-types). *)
  Hypothesis Hsig : signature_typed Sp sg.
  Hypothesis Hdist : ctors_distinct sg.
  Hypothesis Hgen : elim_types_generated sg.

  Local Notation typed := (has_type Sp sg).
  Local Notation wf := (wf_ctx Sp sg).
  Local Notation "t ≡ u" := (conv sg t u).
  Local Notation "t ⇝* u" := (red sg t u).

  Lemma Htypes : sig_types_typed Sp sg.
  Proof. exact (proj1 Hsig). Qed.

  (** ** Typing helpers *)

  Local Notation sorted := (type_typed Sp sg Htypes predicative_prop_full).

  Lemma synth_typed : forall G t A, wf G -> synth Sp sg G t A -> typed G t A.
  Proof.
    intros G t A HG H.
    exact (proj1 (bidir_sound Sp sg Hsig (fun _ => predicative_prop_full) Hdist) _ _ _ H HG).
  Qed.

  Lemma red_typed : forall G t T U, typed G t T -> T ⇝* U -> typed G t U.
  Proof.
    intros G t T U H R.
    destruct U; first
      [ exact (typed_red_srt _ _ Hsig _ _ _ _ H R)
      | exact (proj1 (typed_red_type _ _ Hsig _ _ _ _ H R (fun s E => ltac:(discriminate E)))) ].
  Qed.

  Lemma conv_to : forall G t A T e, erases Sp sg G t A e -> typed G t T -> A ≡ T -> erases Sp sg G t T e.
  Proof.
    intros G t A T e H HT Hc. destruct (sorted _ _ _ HT) as [s Hs]. exact (X_Conv _ _ _ _ _ _ _ _ H Hs Hc).
  Qed.

  (** ** The steps of the walk *)

  Lemma as_pi_red : forall t T A B, as_pi_e sg fuel t T = Ok (A, B) -> T ⇝* Pi A B.
  Proof.
    intros t T A B H. unfold as_pi_e in H. apply bind_ok in H as (V & HV & H). apply whnf_e_red in HV.
    destruct V; cbv beta iota in H; try discriminate H. injection H as <- <-. exact HV.
  Qed.

  Lemma as_sigma_red : forall t T A B, as_sigma_e sg fuel t T = Ok (A, B) -> T ⇝* Sigma A B.
  Proof.
    intros t T A B H. unfold as_sigma_e in H. apply bind_ok in H as (V & HV & H). apply whnf_e_red in HV.
    destruct V; cbv beta iota in H; try discriminate H. injection H as <- <-. exact HV.
  Qed.

  Lemma sort_at_red : forall T K s, sort_at sg fuel T K = Ok s -> K ⇝* Srt s.
  Proof.
    intros T K s H. unfold sort_at in H. apply bind_ok in H as (V & HV & H). apply whnf_e_red in HV.
    destruct V; cbv beta iota in H; try discriminate H. injection H as <-. exact HV.
  Qed.

  (** The parameters read off the type of a scrutinee. *)
  Lemma params_e_spec : forall x X D d ps, params_e sg fuel x X D d = Ok ps ->
    exists us, X ⇝* apps (Const (Ind D)) (ps ++ us) /\
      length ps = length (ind_params d) /\ length us = length (ind_indices d).
  Proof.
    intros x X D d ps H. unfold params_e in H. apply bind_ok in H as (V & HV & H). apply whnf_e_red in HV.
    cbv beta zeta in H. revert H.
    destruct (term_eqb (spine_head V) (Const (Ind D)) &&
              Nat.eqb (length (spine_args V)) (length (ind_params d) + length (ind_indices d))) eqn:E;
      intros H; [ | discriminate H].
    injection H as <-. apply andb_prop in E as [E1 E2]. apply term_eqb_eq in E1. apply Nat.eqb_eq in E2.
    exists (skipn (length (ind_params d)) (spine_args V)). rewrite firstn_skipn.
    rewrite <- (apps_spine V), E1 in HV.
    split; [exact HV | split]; [rewrite length_firstn; lia | rewrite length_skipn; lia].
  Qed.

  (** A type of a head is convertible to every other one. *)
  Lemma head_type_uniq : forall G h H, head_type Sp sg fuel G h = Ok H -> forall U, typed G h U -> H ≡ U.
  Proof.
    intros G h H Hh U HU. destruct h; cbn [head_type] in Hh;
      try (apply infer_e_sound in Hh; exact (synth_unique Sp sg _ _ _ Hh _ HU)).
    - revert Hh. destruct (lookup G n) as [A|] eqn:E; intros Hh; [injection Hh as <- | discriminate Hh].
      destruct (inv_var Sp sg _ _ _ HU) as (A' & Hl & Hc). assert (A' = A) by congruence. subst A'.
      exact (ctype_conv_of Sp sg _ _ _ Hc).
    - revert Hh. destruct (sig_type sg g) as [A|] eqn:E; intros Hh; [injection Hh as <- | discriminate Hh].
      exact (conv_sym _ _ (const_head Sp sg _ _ _ E _ HU)).
    - injection Hh as <-. destruct (inv_fix Sp sg _ _ _ _ _ HU) as (s & D & _ & _ & _ & _ & _ & Hc).
      exact (ctype_conv_of Sp sg _ _ _ Hc).
  Qed.

  (** Instantiating a type of the head along the spine reaches a type
      convertible to every type of the spine. *)
  Lemma inst_sound : forall G args h H K U,
    (forall U', typed G h U' -> H ≡ U') -> typed G (apps h args) U ->
    instantiate sg fuel H args = Ok K -> K ≡ U.
  Proof.
    intros G args. induction args as [|a args IH]; intros h H K U Hh Ht Hi; cbn [instantiate] in Hi.
    - injection Hi as <-. exact (Hh U Ht).
    - apply bind_ok in Hi as (V & HV & Hi). apply whnf_e_red in HV.
      destruct V as [| | V1 V2 | | | | | | | | | | | | | | | | | | |]; cbv beta iota in Hi; try discriminate Hi.
      apply (IH (App h a) (subst1 V2 a) K U); [ | exact Ht | exact Hi].
      intros U' HU'. destruct (inv_app Sp sg _ _ _ _ HU') as (A1 & B1 & Hf & _ & Hc).
      assert (Hpi : Pi V1 V2 ≡ Pi A1 B1) by (eapply conv_trans; [apply conv_sym, red_conv, HV | exact (Hh _ Hf)]).
      apply pi_inj in Hpi as [_ HB].
      eapply conv_trans; [unfold subst1; apply conv_subst; exact HB | exact (ctype_conv_of Sp sg _ _ _ Hc)].
  Qed.

  (** ** The sort of a type *)

  (** The last branch of [sort_of_e]: a neutral spine. *)
  Definition spine_sort (G : ctx) (T V : term) : result erase_failure sort :=
    match spine_head V with
    | Const (Ind D) =>
        match sig_ind sg D with Some d => Ok (ind_sort d) | None => Err (Fail (XNotAType T V)) end
    | Case D _ P x _ =>
        match sig_ind sg D with
        | Some d =>
            let* X := infer_e Sp sg fuel G x in
            let* XV := whnf_e sg fuel AtSort X in
            let p := length (ind_params d) in
            let xs := spine_args XV in
            if term_eqb (spine_head XV) (Const (Ind D)) &&
               Nat.eqb (length xs) (p + length (ind_indices d)) then
              let* K := instantiate sg fuel (apps P (skipn p xs ++ [x])) (spine_args V) in
              sort_at sg fuel T K
            else Err (Fail (XShape x XV))
        | None => Err (Fail (XNotAType T V))
        end
    | h =>
        let* H := head_type Sp sg fuel G h in
        let* K := instantiate sg fuel H (spine_args V) in
        sort_at sg fuel T K
    end.

  Lemma generic_sound : forall G T h args s s0, typed G (apps h args) (Srt s0) ->
    (let* H := head_type Sp sg fuel G h in
     let* K := instantiate sg fuel H args in
     sort_at sg fuel T K) = Ok s -> s = s0.
  Proof.
    intros G T h args s s0 HV H. apply bind_ok in H as (Hh & EHh & H). apply bind_ok in H as (K & HK & H).
    pose proof (inst_sound _ _ _ _ _ _ (head_type_uniq _ _ _ EHh) HV HK) as Hc.
    pose proof (sort_at_red _ _ _ H) as R.
    exact (conv_srt_inj sg _ _ (conv_trans _ _ _ (conv_sym _ _ (red_conv _ _ R)) Hc)).
  Qed.

  Lemma spine_sort_sound : forall G T V s s0, typed G V (Srt s0) -> spine_sort G T V = Ok s -> s = s0.
  Proof.
    intros G T V s s0 HV H. rewrite <- (apps_spine V) in HV. unfold spine_sort in H. revert HV H.
    generalize (spine_args V) as args. generalize (spine_head V) as h. intros h args HV H.
    destruct h as [| | | | | | | | | | | | | | | | | | | g | D s1 P x bs |];
      try exact (generic_sound _ _ _ _ _ _ HV H).
    - destruct g as [D | | | ]; try exact (generic_sound _ _ _ _ _ _ HV H).
      cbv beta iota in H. revert H. destruct (sig_ind sg D) as [d|] eqn:Hd; intros H; [ | discriminate H].
      injection H as <-.
      pose proof (sig_type_ind sg _ _ Hd) as Hty.
      destruct (const_type_typed_t Sp sg Htypes G _ _ (typed_wf _ _ _ _ _ HV) Hty) as [sI HI].
      unfold ind_type in HI.
      assert (Hh : forall H, typed G (Const (Ind D)) H -> H ≡ pis (ind_params d ++ ind_indices d) (Srt (ind_sort d)))
        by exact (const_head Sp sg G _ _ Hty).
      pose proof (spine_length Sp sg args G _ _ _ _ _ HV Hh HI) as Hl.
      destruct (apps_inv Sp sg args G (Const (Ind D)) (Srt s0) _ _ _ (eq_sym Hl) HV Hh HI) as [_ Hc].
      cbn [subst] in Hc. exact (conv_srt_inj sg _ _ Hc).
    - cbv beta iota in H. revert H. destruct (sig_ind sg D) as [d|] eqn:Hd; intros H; [ | discriminate H].
      apply bind_ok in H as (X & HX & H). apply bind_ok in H as (XV & HXV & H). cbv beta zeta in H. revert H.
      destruct (term_eqb (spine_head XV) (Const (Ind D)) &&
                Nat.eqb (length (spine_args XV)) (length (ind_params d) + length (ind_indices d))) eqn:E;
        intros H; [ | discriminate H].
      apply bind_ok in H as (K & HK & H).
      apply andb_prop in E as [E1 E2]. apply term_eqb_eq in E1. apply Nat.eqb_eq in E2.
      apply infer_e_sound in HX. apply whnf_e_red in HXV.
      assert (Hu : forall U, typed G (Case D s1 P x bs) U ->
                apps P (skipn (length (ind_params d)) (spine_args XV) ++ [x]) ≡ U).
      { intros U HU. destruct (inv_case Sp sg _ _ _ _ _ _ _ HU)
          as (d0 & ps0 & us0 & _ & Hd0 & _ & Hlp0 & Hlu0 & Hx0 & _ & _ & Hc).
        rewrite Hd in Hd0. injection Hd0 as <-.
        pose proof (synth_unique Sp sg _ _ _ HX _ Hx0) as EX.
        rewrite <- (apps_spine XV), E1 in HXV.
        assert (Hsp : Forall2 (conv sg) (spine_args XV) (ps0 ++ us0)).
        { apply (conv_ind_spine sg D). eapply conv_trans; [apply conv_sym, red_conv, HXV | exact EX]. }
        rewrite <- (firstn_skipn (length (ind_params d)) (spine_args XV)) in Hsp.
        apply forall2_app_split in Hsp as [_ Hus]; [ | rewrite length_firstn; lia].
        eapply conv_trans; [ | exact (ctype_conv_of Sp sg _ _ _ Hc)]. apply conv_apps; [apply conv_refl | ].
        apply Forall2_app; [exact Hus | constructor; [apply conv_refl | constructor]]. }
      pose proof (inst_sound _ _ _ _ _ _ Hu HV HK) as Hc.
      pose proof (sort_at_red _ _ _ H) as R.
      exact (conv_srt_inj sg _ _ (conv_trans _ _ _ (conv_sym _ _ (red_conv _ _ R)) Hc)).
  Qed.

  (** The sort [sort_of_e] finds is the one every typing gives the type. *)
  Theorem sort_of_e_sound : forall n G T s s0, typed G T (Srt s0) ->
    sort_of_e Sp sg fuel n G T = Ok s -> s = s0.
  Proof.
    induction n as [|n IH]; intros G T s s0 HT H; cbn [sort_of_e] in H; [discriminate H | ].
    apply bind_ok in H as (V & HV & H). apply whnf_e_red in HV.
    pose proof (subject_red Sp sg Hsig _ _ _ _ HT HV) as HV'. clear HT HV. cbv beta zeta in H.
    destruct V as [s1 | | A B | | | | | | | | | | | | | A B | | | | | |];
      try exact (spine_sort_sound _ _ _ _ _ HV' H).
    - cbv iota in H. revert H. destruct (spec_axiom Sp s1) as [s'|] eqn:Ha; intros H; [ | discriminate H].
      injection H as <-. destruct (inv_sort Sp sg _ _ _ HV') as (s'' & Ha' & Hc).
      rewrite Ha in Ha'. injection Ha' as <-. exact (conv_srt_inj sg _ _ (ctype_conv_of Sp sg _ _ _ Hc)).
    - cbv iota in H. apply bind_ok in H as (s1 & H1 & H). apply bind_ok in H as (s2 & H2 & H).
      destruct (inv_pi Sp sg _ _ _ _ HV') as (s1' & s2' & s3' & HA & HB & Hr & Hc).
      rewrite (IH _ _ _ _ HA H1), (IH _ _ _ _ HB H2), Hr in H. injection H as <-.
      exact (conv_srt_inj sg _ _ (ctype_conv_of Sp sg _ _ _ Hc)).
    - cbv iota in H. destruct (inv_prim Sp sg _ _ _ HV' (or_introl eq_refl)) as (s1 & Hp & Hc).
      rewrite Hp in H. injection H as <-. exact (conv_srt_inj sg _ _ (ctype_conv_of Sp sg _ _ _ Hc)).
    - cbv iota in H. destruct (inv_prim Sp sg _ _ _ HV' (or_intror (or_introl eq_refl))) as (s1 & Hp & Hc).
      rewrite Hp in H. injection H as <-. exact (conv_srt_inj sg _ _ (ctype_conv_of Sp sg _ _ _ Hc)).
    - cbv iota in H. destruct (inv_prim Sp sg _ _ _ HV' (or_intror (or_intror eq_refl))) as (s1 & Hp & Hc).
      rewrite Hp in H. injection H as <-. exact (conv_srt_inj sg _ _ (ctype_conv_of Sp sg _ _ _ Hc)).
    - cbv iota in H. apply bind_ok in H as (s1 & H1 & H). apply bind_ok in H as (s2 & H2 & H).
      destruct (inv_sigma Sp sg _ _ _ _ HV') as (s1' & s2' & s3' & HA & HB & Hr & Hc).
      rewrite (IH _ _ _ _ HA H1), (IH _ _ _ _ HB H2), Hr in H. injection H as <-.
      exact (conv_srt_inj sg _ _ (ctype_conv_of Sp sg _ _ _ Hc)).
  Qed.

  (** ** The decision of erasability *)

  Theorem erasable_consistent : forall G T, tyok Sp sg G T ->
    erasable Sp sg fuel G T = Ok true -> erasable_at Sp sg G T.
  Proof.
    intros G T HT H. destruct (erasable_spec Sp sg fuel G T H) as [Ha | Hs].
    - exists T. split; [apply conv_refl | left; exact Ha].
    - destruct HT as [[s0 ->] | [s0 HT]].
      + exists (Srt s0). split; [apply conv_refl | left]. apply (Ar_Sort sg _ s0). apply rt_refl.
      + pose proof (sort_of_e_sound _ _ _ _ _ HT Hs) as <-.
        exists T. split; [apply conv_refl | right; exact HT].
  Qed.

  Lemma box : forall G t T, typed G t T -> erasable Sp sg fuel G T = Ok true -> erases Sp sg G t T EBox.
  Proof.
    intros G t T Ht H. apply X_Box; [exact Ht | ].
    exact (erasable_consistent _ _ (validity_t Sp sg Htypes _ _ _ Ht) H).
  Qed.

  (** ** An instance into Prop is a proof *)

  Lemma rule_prp : forall s1 s3, spec_rule Sp s1 Prp = Some s3 -> s3 = Prp.
  Proof. intros [] s3 H; cbn in H; try discriminate H; injection H as <-; reflexivity. Qed.

  (** A telescope ending in a proposition is a proposition. *)
  Lemma pis_sort_prp : forall Ts G R s, typed G (pis Ts R) (Srt s) ->
    (forall s', typed (rev Ts ++ G) R (Srt s') -> s' = Prp) -> s = Prp.
  Proof.
    induction Ts as [|T Ts IH]; intros G R s H HR; cbn [pis] in H.
    - exact (HR s H).
    - destruct (inv_pi Sp sg _ _ _ _ H) as (s1 & s2 & s3 & _ & HB & Hr & Hc).
      assert (E2 : s2 = Prp).
      { apply (IH (T :: G) R s2 HB). intros s' Hs'. apply HR. cbn [rev]. rewrite <- app_assoc. exact Hs'. }
      subst s2. pose proof (rule_prp _ _ Hr) as ->.
      symmetry. exact (conv_srt_inj sg _ _ (ctype_conv_of Sp sg _ _ _ Hc)).
  Qed.

  Lemma rename_pis_srt : forall Ts r k, exists Ts', rename r (pis Ts (Srt k)) = pis Ts' (Srt k) /\
    length Ts' = length Ts.
  Proof.
    induction Ts as [|T Ts IH]; intros r k; [exists []; split; reflexivity | ].
    cbn [pis rename]. destruct (IH (up_ren r) k) as (Ts' & E & El).
    exists (rename r T :: Ts'). rewrite E. split; [reflexivity | cbn [length]; rewrite El; reflexivity].
  Qed.

  (** The generated type of an instance into Prop: [P ū x] at its end
      is a proposition, the motive [P] ending in Prop. *)
  Lemma elim_prop_sort : forall D A act, sig_elim sg D Prp = Some (A, act) -> typed [] A (Srt Prp).
  Proof.
    intros D A act He. destruct (Hgen _ _ _ _ He) as (d & Hd & ->).
    assert (Hty : sig_type sg (Elim D Prp) = Some (elim_type d Prp)) by (cbn [sig_type]; rewrite He; reflexivity).
    destruct (Htypes _ _ Hty) as [sE HE].
    assert (E : sE = Prp); [ | subst sE; exact HE].
    rewrite elim_type_tele in HE. apply (pis_sort_prp _ _ _ _ HE). intros s' Hs'.
    set (p := length (ind_params d)) in *. set (k := length (ind_ctors d)) in *.
    set (q := length (ind_indices d)) in *.
    set (Dty := apps (Const (Ind (ind_name d))) (vars (q + S k) p ++ vars 0 q)) in *.
    set (I' := rename_tele (Nat.add (S k)) (ind_indices d)) in *.
    (* the motive, at [S (k + q)] in the context of the telescope *)
    assert (Hn : nth_error (rev (ind_params d ++ [motive_type d Prp] ++ methods d ++ I' ++ [Dty]) ++ [])
                   (S (k + q)) = Some (motive_type d Prp)).
    { rewrite app_nil_r, !rev_app_distr. cbn [rev app nth_error].
      assert (El : length (rev I' ++ rev (methods d)) = k + q).
      { rewrite length_app, !length_rev, length_methods. unfold I'. rewrite length_rename_tele.
        unfold k, q. lia. }
      rewrite nth_error_app1 by (rewrite length_app, El; cbn [length]; lia).
      rewrite nth_error_app2 by lia. rewrite El, Nat.sub_diag. reflexivity. }
    assert (Hm : exists Ts', lookup (rev (ind_params d ++ [motive_type d Prp] ++ methods d ++ I' ++ [Dty]) ++ [])
                   (S (k + q)) = Some (pis Ts' (Srt Prp)) /\ length Ts' = S q).
    { unfold lookup. rewrite Hn. cbn [option_map].
      assert (Em : motive_type d Prp = pis (ind_indices d ++ [apps (Const (Ind (ind_name d))) (vars q p ++ vars 0 q)])
                     (Srt Prp)) by (unfold motive_type; rewrite pis_app; reflexivity).
      rewrite Em. destruct (rename_pis_srt (ind_indices d ++ [apps (Const (Ind (ind_name d))) (vars q p ++ vars 0 q)])
                              (Nat.add (S (S (k + q)))) Prp) as (Ts' & E & El).
      exists Ts'. unfold lift. rewrite E. split; [reflexivity | ]. rewrite El, length_app. cbn [length]. fold q. lia. }
    destruct Hm as (Ts' & Hl & ElTs).
    pose proof (typed_wf _ _ _ _ _ Hs') as HG.
    destruct (wf_lookup Sp sg _ _ _ HG Hl) as [sM HM].
    assert (Hh : forall H, typed (rev (ind_params d ++ [motive_type d Prp] ++ methods d ++ I' ++ [Dty]) ++ [])
                             (Var (S (k + q))) H -> H ≡ pis Ts' (Srt Prp)).
    { intros H HH. destruct (inv_var Sp sg _ _ _ HH) as (A' & Hl' & Hc). rewrite Hl in Hl'. injection Hl' as <-.
      exact (conv_sym _ _ (ctype_conv_of Sp sg _ _ _ Hc)). }
    assert (Hlen : length Ts' = length (vars 1 q ++ [Var 0]))
      by (rewrite length_app, length_vars; cbn [length]; lia).
    destruct (apps_inv Sp sg _ _ _ _ _ _ _ Hlen Hs' Hh HM) as [_ Hc].
    cbn [subst] in Hc. symmetry. exact (conv_srt_inj sg _ _ Hc).
  Qed.

  Lemma elim_prop_erasable : forall G D T, typed G (Const (Elim D Prp)) T -> erasable_at Sp sg G T.
  Proof.
    intros G D T H. destruct (inv_const Sp sg _ _ _ H) as (A & HG & _ & Hty & Hc).
    assert (Hcl : closed A = true) by exact (sig_type_closed sg _ _ Hty).
    cbn [sig_type] in Hty. revert Hty. destruct (sig_elim sg D Prp) as [[A' act]|] eqn:He; intros Hty;
      cbn in Hty; [injection Hty as -> | discriminate Hty].
    exists A. split; [exact (conv_sym _ _ (ctype_conv_of Sp sg _ _ _ Hc)) | right].
    exact (typed_closed_weaken Sp sg G _ _ (elim_prop_sort _ _ _ He) Hcl eq_refl HG).
  Qed.

  (** ** The branches of a match *)

  Lemma conv_motive : forall D d ps0 ps s, sig_ind sg D = Some d ->
    length ps0 = length (ind_params d) -> length ps = length (ind_params d) ->
    Forall2 (conv sg) ps0 ps -> case_motive_type d ps0 s ≡ case_motive_type d ps s.
  Proof.
    intros D d ps0 ps s Hd Hl0 Hl H.
    rewrite (case_motive_type_tsub sg D d ps0 s Hd Hl0), (case_motive_type_tsub sg D d ps s Hd Hl).
    apply conv_pis.
    - exact (conv_subst_tele_tsub sg _ _ H _ 0).
    - apply conv_pi; [ | apply conv_refl]. apply conv_apps; [apply conv_refl | ].
      apply Forall2_app; [apply forall2_conv_lift, H | apply forall2_conv_refl].
  Qed.

  Lemma conv_branch : forall D d ps0 ps P c, sig_ind sg D = Some d -> In c (ind_ctors d) ->
    length ps0 = length (ind_params d) -> length ps = length (ind_params d) ->
    Forall2 (conv sg) ps0 ps -> case_branch_type d ps0 P c ≡ case_branch_type d ps P c.
  Proof.
    intros D d ps0 ps P c Hd Hin Hl0 Hl H.
    rewrite (case_branch_type_tsub sg D d ps0 P c Hd Hin Hl0), (case_branch_type_tsub sg D d ps P c Hd Hin Hl).
    cbv zeta. apply conv_pis.
    - exact (conv_subst_tele_tsub sg _ _ H _ 0).
    - apply conv_apps; [apply conv_refl | ]. apply Forall2_app.
      + apply forall2_conv_subst_tsub, H.
      + constructor; [ | constructor]. apply conv_apps; [apply conv_refl | ].
        apply Forall2_app; [apply forall2_conv_lift, H | apply forall2_conv_refl].
  Qed.

  Lemma branches_conv : forall G d ps0 ps P cs bs, has_branches Sp sg G d ps0 P cs bs ->
    (forall c, In c cs -> case_branch_type d ps0 P c ≡ case_branch_type d ps P c /\
       exists s, typed G (case_branch_type d ps P c) (Srt s)) ->
    has_branches Sp sg G d ps P cs bs.
  Proof.
    intros G d ps0 ps P cs bs H. induction H as [|G d ps0' P c cs b bs Hb _ IH]; intros Hok; constructor.
    - destruct (Hok c (or_introl eq_refl)) as [Hc [s Hs]]. exact (T_Conv _ _ _ _ _ _ _ Hb Hs Hc).
    - apply IH. intros c' Hc'. exact (Hok c' (or_intror Hc')).
  Qed.

  Lemma branches_sound : forall G d ps P t0 cs bs bs',
    Forall (fun b => forall G T e, typed G b T -> erase Sp sg fuel true G b T = Ok e ->
                                   erases Sp sg G b T e) bs ->
    has_branches Sp sg G d ps P cs bs ->
    erase_each t0 (fun c b => erase Sp sg fuel true G b (case_branch_type d ps P c)) cs bs = Ok bs' ->
    erases_branches Sp sg G d ps P cs bs bs'.
  Proof.
    intros G d ps P t0 cs bs bs' HIH H. revert bs' HIH.
    induction H as [|G d ps P c cs b bs Hb _ IH]; intros bs' HIH He; cbn [erase_each] in He.
    - injection He as <-. constructor.
    - apply bind_ok in He as (b' & Hb' & He). apply bind_ok in He as (r & Hr & He). injection He as <-.
      inversion HIH as [| ? ? IHb IHbs]; subst. constructor.
      + exact (IHb _ _ _ Hb Hb').
      + exact (IH _ IHbs Hr).
  Qed.

  (** Parameters of a family are typed against its parameters. *)
  Lemma ind_args_typed : forall G D d ps us x, sig_ind sg D = Some d -> length ps = length (ind_params d) ->
    length us = length (ind_indices d) -> typed G x (apps (Const (Ind D)) (ps ++ us)) ->
    args_typed Sp sg G (ind_params d) ps.
  Proof.
    intros G D d ps us x Hd Hlp Hlu Hx.
    destruct (sorted _ _ _ Hx) as [sX HX].
    pose proof (sig_type_ind sg _ _ Hd) as Hty.
    destruct (const_type_typed_t Sp sg Htypes G _ _ (typed_wf _ _ _ _ _ Hx) Hty) as [s0 Hs0].
    unfold ind_type in Hs0.
    assert (Hl : length (ind_params d ++ ind_indices d) = length (ps ++ us)) by (rewrite !length_app; lia).
    destruct (apps_inv Sp sg (ps ++ us) G (Const (Ind D)) _ _ _ _ Hl HX (const_head Sp sg _ _ _ Hty) Hs0)
      as [Hargs _].
    exact (proj1 (proj1 (args_typed_app Sp sg ps G _ _ us (eq_sym Hlp)) Hargs)).
  Qed.

  (** ** Soundness *)

  Theorem erase_sound : forall t G T e, typed G t T -> erase Sp sg fuel true G t T = Ok e ->
    erases Sp sg G t T e.
  Proof.
    intros t. induction t as
      [ s | n | A IHA B IHB | b IHb | f IHf a IHa | u IHu A IHA | | C IHC e0 IHe | | | C IHC c IHc u IHu
      | | | | C IHC x IHx y IHy b IHb | A IHA B IHB | a IHa b IHb | q IHq | q IHq | g
      | D s P IHP x IHx bs IHbs | A IHA k b IHb ] using term_ind';
      intros G T e Ht H; pose proof (typed_wf _ _ _ _ _ Ht) as HG;
      cbn [erase] in H; apply bind_ok in H as (er & Her & H); cbv beta in H;
      (destruct er; [injection H as <-; exact (box _ _ _ Ht Her) | cbv iota in H]).
    - (* Srt *) discriminate H.
    - (* Var *) injection H as <-. exact (X_Var _ _ _ _ _ Ht).
    - (* Pi *) discriminate H.
    - (* Lam *)
      apply bind_ok in H as ([A B] & Hp & H). apply bind_ok in H as (b' & Hb & H). injection H as <-.
      cbn [fst snd] in Hb. apply as_pi_red in Hp.
      pose proof (red_typed _ _ _ _ Ht Hp) as HPi.
      destruct (sorted _ _ _ HPi) as [sP HsP].
      destruct (inv_pi Sp sg _ _ _ _ HsP) as (s1 & s2 & s3 & HA & HB & _ & _).
      destruct (inv_lam Sp sg _ _ _ HPi) as (A0 & B0 & s0 & Hb0 & _ & Hc).
      pose proof (ctype_conv_of Sp sg _ _ _ Hc) as Hc'. apply pi_inj in Hc' as [HA0 HB0].
      pose proof (ctx_conv1 Sp sg _ _ _ _ _ _ Hb0 HA HA0) as Hb1.
      pose proof (T_Conv _ _ _ _ _ _ _ Hb1 HB HB0) as Hb2.
      exact (conv_to _ _ _ _ _ (X_Lam _ _ _ _ _ _ _ _ (IHb _ _ _ Hb2 Hb) HsP) Ht (conv_sym _ _ (red_conv _ _ Hp))).
    - (* App *)
      apply bind_ok in H as (Fs & HFs & H). destruct Fs as [|F Fs]; [discriminate H | ].
      apply bind_ok in H as ([A B] & Hp & H).
      apply bind_ok in H as (f' & Hf & H). apply bind_ok in H as (a' & Ha & H). injection H as <-.
      rewrite (erase_spine_erase _ _ _ _ _ _ _ _ HFs) in Hf.
      cbn [fst] in Ha. apply infer_spine_e_sound in HFs as HF. apply as_pi_red in Hp.
      pose proof (synth_typed _ _ _ HG HF) as HfF.
      destruct (inv_app Sp sg _ _ _ _ Ht) as (A0 & B0 & Hf0 & Ha0 & Hc).
      assert (Hpi : Pi A B ≡ Pi A0 B0)
        by (eapply conv_trans; [apply conv_sym, red_conv, Hp | exact (synth_unique Sp sg _ _ _ HF _ Hf0)]).
      apply pi_inj in Hpi as [HA HB].
      pose proof (red_typed _ _ _ _ HfF Hp) as HfP.
      destruct (sorted _ _ _ HfP) as [sP HsP]. destruct (inv_pi Sp sg _ _ _ _ HsP) as (s1 & _ & _ & HA1 & _ & _ & _).
      pose proof (T_Conv _ _ _ _ _ _ _ Ha0 HA1 (conv_sym _ _ HA)) as HaA.
      pose proof (conv_to _ _ _ _ _ (IHf _ _ _ HfF Hf) HfP (red_conv _ _ Hp)) as Ef.
      apply (conv_to _ _ _ _ _ (X_App _ _ _ _ _ _ _ _ _ Ef (IHa _ _ _ HaA Ha)) Ht).
      eapply conv_trans; [unfold subst1; apply conv_subst; exact HB | exact (ctype_conv_of Sp sg _ _ _ Hc)].
    - (* Ann *)
      destruct (inv_ann Sp sg _ _ _ _ Ht) as (s0 & HA & Hu & Hc).
      exact (conv_to _ _ _ _ _ (X_Ann _ _ _ _ _ _ _ HA (IHu _ _ _ Hu H)) Ht (ctype_conv_of Sp sg _ _ _ Hc)).
    - (* Void *) discriminate H.
    - (* ElimVoid *)
      apply bind_ok in H as (e' & He & H). injection H as <-.
      destruct (inv_elim_void Sp sg _ _ _ _ Ht) as (s0 & HC & He0 & Hc).
      exact (conv_to _ _ _ _ _ (X_ElimVoid _ _ _ _ _ _ _ HC (IHe _ _ _ He0 He)) Ht (ctype_conv_of Sp sg _ _ _ Hc)).
    - (* Unit *) discriminate H.
    - (* Tt *) injection H as <-. exact (X_Tt _ _ _ _ Ht).
    - (* ElimUnit *)
      apply bind_ok in H as (c' & Hc' & H). apply bind_ok in H as (u' & Hu' & H). injection H as <-.
      destruct (inv_elim_unit Sp sg _ _ _ _ _ Ht) as (s0 & HC & Hc0 & Hu0 & Hc).
      exact (conv_to _ _ _ _ _ (X_ElimUnit _ _ _ _ _ _ _ _ _ HC (IHc _ _ _ Hc0 Hc') (IHu _ _ _ Hu0 Hu')) Ht
               (ctype_conv_of Sp sg _ _ _ Hc)).
    - (* Bool *) discriminate H.
    - (* True *) injection H as <-. exact (X_True _ _ _ _ Ht).
    - (* False *) injection H as <-. exact (X_False _ _ _ _ Ht).
    - (* ElimBool *)
      apply bind_ok in H as (x' & Hx' & H). apply bind_ok in H as (y' & Hy' & H).
      apply bind_ok in H as (b' & Hb' & H). injection H as <-.
      destruct (inv_elim_bool Sp sg _ _ _ _ _ _ Ht) as (s0 & HC & Hx0 & Hy0 & Hb0 & Hc).
      exact (conv_to _ _ _ _ _ (X_ElimBool _ _ _ _ _ _ _ _ _ _ _ HC (IHx _ _ _ Hx0 Hx') (IHy _ _ _ Hy0 Hy')
                                  (IHb _ _ _ Hb0 Hb')) Ht (ctype_conv_of Sp sg _ _ _ Hc)).
    - (* Sigma *) discriminate H.
    - (* Pair *)
      apply bind_ok in H as ([A B] & Hp & H). apply bind_ok in H as (a' & Ha & H).
      apply bind_ok in H as (b' & Hb & H). injection H as <-.
      cbn [fst snd] in Ha, Hb. apply as_sigma_red in Hp.
      pose proof (red_typed _ _ _ _ Ht Hp) as HS.
      destruct (sorted _ _ _ HS) as [sS HsS].
      destruct (inv_sigma Sp sg _ _ _ _ HsS) as (s1 & s2 & _ & HA & HB & _ & _).
      destruct (inv_pair Sp sg _ _ _ _ HS) as (A0 & B0 & s0 & _ & Ha0 & Hb0 & Hc).
      pose proof (ctype_conv_of Sp sg _ _ _ Hc) as Hc'. apply sigma_inj in Hc' as [HA0 HB0].
      pose proof (T_Conv _ _ _ _ _ _ _ Ha0 HA HA0) as HaA.
      assert (HBa : typed G (subst1 B a) (Srt s2)) by exact (typing_subst1 Sp sg _ _ _ _ _ HaA HB).
      pose proof (T_Conv _ _ _ _ _ _ _ Hb0 HBa (conv_subst (scons a Var) _ _ HB0)) as HbB.
      exact (conv_to _ _ _ _ _ (X_Pair _ _ _ _ _ _ _ _ _ _ HsS (IHa _ _ _ HaA Ha) (IHb _ _ _ HbB Hb)) Ht
               (conv_sym _ _ (red_conv _ _ Hp))).
    - (* Fst *)
      apply bind_ok in H as (Q & HQ & H). apply bind_ok in H as ([A B] & Hp & H).
      apply bind_ok in H as (q' & Hq & H). injection H as <-.
      apply infer_e_sound in HQ. apply as_sigma_red in Hp.
      pose proof (synth_typed _ _ _ HG HQ) as HqQ.
      destruct (inv_fst Sp sg _ _ _ Ht) as (A0 & B0 & Hq0 & Hc).
      assert (Hs : Sigma A B ≡ Sigma A0 B0)
        by (eapply conv_trans; [apply conv_sym, red_conv, Hp | exact (synth_unique Sp sg _ _ _ HQ _ Hq0)]).
      apply sigma_inj in Hs as [HA _].
      pose proof (conv_to _ _ _ _ _ (IHq _ _ _ HqQ Hq) (red_typed _ _ _ _ HqQ Hp) (red_conv _ _ Hp)) as Eq.
      exact (conv_to _ _ _ _ _ (X_Fst _ _ _ _ _ _ _ Eq) Ht (conv_trans _ _ _ HA (ctype_conv_of Sp sg _ _ _ Hc))).
    - (* Snd *)
      apply bind_ok in H as (Q & HQ & H). apply bind_ok in H as ([A B] & Hp & H).
      apply bind_ok in H as (q' & Hq & H). injection H as <-.
      apply infer_e_sound in HQ. apply as_sigma_red in Hp.
      pose proof (synth_typed _ _ _ HG HQ) as HqQ.
      destruct (inv_snd Sp sg _ _ _ Ht) as (A0 & B0 & Hq0 & Hc).
      assert (Hs : Sigma A B ≡ Sigma A0 B0)
        by (eapply conv_trans; [apply conv_sym, red_conv, Hp | exact (synth_unique Sp sg _ _ _ HQ _ Hq0)]).
      apply sigma_inj in Hs as [_ HB].
      pose proof (conv_to _ _ _ _ _ (IHq _ _ _ HqQ Hq) (red_typed _ _ _ _ HqQ Hp) (red_conv _ _ Hp)) as Eq.
      apply (conv_to _ _ _ _ _ (X_Snd _ _ _ _ _ _ _ Eq) Ht).
      eapply conv_trans; [unfold subst1; apply conv_subst; exact HB | exact (ctype_conv_of Sp sg _ _ _ Hc)].
    - (* Const *)
      destruct g as [D | D c | D s0 | f]; cbv iota in H.
      + discriminate H.
      + injection H as <-. exact (X_Ctor _ _ _ _ _ _ Ht).
      + revert H. destruct (sort_eqb s0 Prp) eqn:Es; intros H; injection H as <-.
        * apply sort_eqb_eq in Es. subst s0. exact (X_Box _ _ _ _ _ Ht (elim_prop_erasable _ _ _ Ht)).
        * apply X_Elim; [exact Ht | intros ->]. rewrite (proj2 (sort_eqb_eq Prp Prp) eq_refl) in Es.
          discriminate Es.
      + injection H as <-. exact (X_Def _ _ _ _ _ Ht).
    - (* Case *)
      revert H. destruct (sig_ind sg D) as [d|] eqn:Hd; intros H; [ | discriminate H].
      apply bind_ok in H as (X & HX & H). apply bind_ok in H as (ps & Hps & H).
      apply bind_ok in H as (x' & Hx' & H). apply bind_ok in H as (bs' & Hbs' & H).
      apply infer_e_sound in HX. destruct (params_e_spec _ _ _ _ _ Hps) as (us & HXr & Hlp & Hlu).
      pose proof (synth_typed _ _ _ HG HX) as HxX.
      destruct (inv_case Sp sg _ _ _ _ _ _ _ Ht)
        as (d0 & ps0 & us0 & Hdecl & Hd0 & Hel & Hlp0 & Hlu0 & Hx0 & HP0 & Hbr0 & Hc).
      rewrite Hd in Hd0. injection Hd0 as <-.
      assert (Hsp : Forall2 (conv sg) (ps ++ us) (ps0 ++ us0)).
      { apply (conv_ind_spine sg D).
        eapply conv_trans; [apply conv_sym, red_conv, HXr | exact (synth_unique Sp sg _ _ _ HX _ Hx0)]. }
      apply forall2_app_split in Hsp as [Hpc Hus]; [ | lia].
      pose proof (red_typed _ _ _ _ HxX HXr) as Hxt.
      pose proof (ind_args_typed _ _ _ _ _ _ Hd Hlp Hlu Hxt) as Hpt.
      assert (Hs : spec_sort Sp s = true)
        by (unfold allows_elimination in Hel; apply andb_prop in Hel as [Hs _]; exact Hs).
      destruct (motive_typed Sp sg Hsig predicative_prop_full Hdecl G D d ps s Hd HG Hlp Hpt Hs) as [sm Hm].
      pose proof (T_Conv _ _ _ _ _ _ _ HP0 Hm (conv_motive _ _ _ _ _ Hd Hlp0 Hlp (forall2_conv_sym _ _ _ Hpc)))
        as HPt.
      assert (Hbr : has_branches Sp sg G d ps P (ind_ctors d) bs).
      { apply (branches_conv _ _ _ _ _ _ _ Hbr0). intros c Hin. split.
        - exact (conv_branch _ _ _ _ _ _ Hd Hin Hlp0 Hlp (forall2_conv_sym _ _ _ Hpc)).
        - exact (branch_typed Sp sg Hsig predicative_prop_full Hdecl G D d ps P s c Hd (Hdist D d Hd) Hin Hlp
                   Hpt HPt Hs). }
      pose proof (branches_sound _ _ _ _ _ _ _ _ IHbs Hbr Hbs') as Ebs.
      pose proof (conv_to _ _ _ _ _ (IHx _ _ _ HxX Hx') Hxt (red_conv _ _ HXr)) as Ex.
      assert (HcT : apps P (us ++ [x]) ≡ T).
      { eapply conv_trans; [ | exact (ctype_conv_of Sp sg _ _ _ Hc)]. apply conv_apps; [apply conv_refl | ].
        apply Forall2_app; [exact Hus | constructor; [apply conv_refl | constructor]]. }
      revert H. destruct (sort_eqb (ind_sort d) Prp) eqn:Es; intros H; cbv iota in H.
      + apply sort_eqb_eq in Es.
        revert H. destruct (ind_elim d) eqn:Eel; intros H; cbv iota in H; try discriminate H.
        rewrite <- Eel in Hel.
        revert H Ebs. destruct (ind_ctors d) as [|c [|c2 cs]] eqn:Ec; intros H Ebs;
          destruct bs' as [|b' [|b2' bs2']]; cbv iota in H; try discriminate H; injection H as <-.
        * inversion Ebs; subst.
          exact (conv_to _ _ _ _ _ (X_CaseEmpty _ _ _ _ _ _ _ _ _ _ _ Hdecl Hd Hel Hlp Hlu Es Eel Ec Ex HPt) Ht HcT).
        * inversion Ebs as [| ? ? ? ? ? ? b ? ? ? Eb Erest]; subst. inversion Erest; subst.
          exact (conv_to _ _ _ _ _ (X_CaseSingleton _ _ _ _ _ _ _ _ _ _ _ _ _ Hdecl Hd Hel Hlp Hlu Es Eel Ec Hxt
                                      HPt Eb) Ht HcT).
      + injection H as <-. assert (Hnp : ind_sort d <> Prp).
        { intros E. rewrite E, (proj2 (sort_eqb_eq Prp Prp) eq_refl) in Es. discriminate Es. }
        exact (conv_to _ _ _ _ _ (X_Case _ _ _ _ _ _ _ _ _ _ _ _ _ Hdecl Hd Hel Hlp Hlu Hnp Ex HPt Ebs) Ht HcT).
    - (* Fix *)
      apply bind_ok in H as (b' & Hb & H). injection H as <-.
      destruct (inv_fix Sp sg _ _ _ _ _ Ht) as (s0 & D & HA & Hsa & Hne & Hb0 & Hgd & Hc).
      exact (conv_to _ _ _ _ _ (X_Fix _ _ _ _ _ _ _ _ _ HA Hsa Hne (IHb _ _ _ Hb0 Hb) Hgd) Ht
               (ctype_conv_of Sp sg _ _ _ Hc)).
  Qed.
End Sound.
