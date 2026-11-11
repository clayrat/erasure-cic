(** * The relation of erasure under renaming and substitution

    [erases] commutes with substitution ([erases_subst1]): the erasure
    of [b] with the erasure of [u] substituted for its variable is an
    erasure of [b[u/0]] at [B[u/0]].  This is [erasure_substitution] of
    Contracts.v, the step of the simulation for β and the unfolding of
    [fix], as the substitution lemma of the erasure of MetaCoq.

    The proof follows the one for typing (PTS.TypingSubst of the
    kernel): first renamings that keep the types of the variables, which
    rename the erasure as well ([erases_rename]), and give weakening;
    then substitutions sending each variable to a term with an erasure
    at the substituted type ([erases_subst]), the erased substitution
    giving the erasures.  Every rule of the relation repeats a typing
    rule, so its typing premises follow from the stability of typing,
    and an erasable type stays erasable: arities by the stability of
    reduction, types in Prop by the stability of typing.  Two rules need
    more:
    - a variable may be erased at a type convertible to the one of the
      context: the substituted term is erased at the substituted type of
      the context, then converted;
    - the singleton match applies its branch to boxes, which renaming and
      substitution leave as they are. *)

From Stdlib Require Import String List Bool.
Import ListNotations.
From DepTypes.PTS Require Import Syntax Telescope Spec Signature Reduction SubstLaws Guard Typing
  TypingSubst Inversion.
From CIC.Erasure Require Import Target Erase Relation.

(** ** Renaming and substitution of erased terms *)

Lemma erename_eapps : forall r us h, erename r (eapps h us) = eapps (erename r h) (map (erename r) us).
Proof. intros r us. induction us as [|u us IH]; intros h; [reflexivity | exact (IH (EApp h u))]. Qed.

Lemma esubst_eapps : forall sb us h, esubst sb (eapps h us) = eapps (esubst sb h) (map (esubst sb) us).
Proof. intros sb us. induction us as [|u us IH]; intros h; [reflexivity | exact (IH (EApp h u))]. Qed.

Lemma map_box : forall (f : eterm -> eterm) n, f EBox = EBox -> map f (repeat EBox n) = repeat EBox n.
Proof. intros f n H. induction n as [|n IH]; cbn [repeat map]; [reflexivity | rewrite H, IH; reflexivity]. Qed.

(** ** Erasable types *)

Lemma arity_subst : forall sg T, arity sg T -> forall sb, arity sg (subst sb T).
Proof.
  intros sg T H. induction H as [T s HT | T A B HT _ IH]; intros sb.
  - exact (Ar_Sort sg _ s (red_subst sb _ _ HT)).
  - exact (Ar_Pi sg _ (subst sb A) (subst (up_sub sb) B) (red_subst sb _ _ HT) (IH _)).
Qed.

Lemma arity_rename : forall sg T r, arity sg T -> arity sg (rename r T).
Proof. intros sg T r H. rewrite rename_as_subst. apply arity_subst, H. Qed.

Section ErasureSubst.
  Variable S : spec.
  Variable sg : signature.
  Local Notation typed := (has_type S sg).
  Local Notation wf := (wf_ctx S sg).
  Local Notation erases := (erases S sg).
  Local Notation erases_branches := (erases_branches S sg).

  Let ty_ren := proj1 (proj2 (typing_rename S sg)).
  Let ty_sub := proj1 (proj2 (typing_subst S sg)).

  Lemma erasable_at_rename : forall G G' T r, wf G' -> ren_ok G G' r ->
    erasable_at S sg G T -> erasable_at S sg G' (rename r T).
  Proof.
    intros G G' T r HG Hr (T' & Hc & H). exists (rename r T'). split; [exact (conv_rename r _ _ Hc) | ].
    destruct H as [H | H]; [left; exact (arity_rename _ _ r H) | right].
    exact (ty_ren _ _ _ H _ _ HG Hr).
  Qed.

  Lemma erasable_at_subst : forall G G' T sb, wf G' -> sub_ok S sg G G' sb ->
    erasable_at S sg G T -> erasable_at S sg G' (subst sb T).
  Proof.
    intros G G' T sb HG Hs (T' & Hc & H). exists (subst sb T'). split; [exact (conv_subst sb _ _ Hc) | ].
    destruct H as [H | H]; [left; exact (arity_subst _ _ H sb) | right].
    exact (ty_sub _ _ _ H _ _ HG Hs).
  Qed.

  Lemma index_position_subst : forall f sb, index_position sg f -> index_position sg (subst sb f).
  Proof.
    intros f sb (D & s & d & Eh & Hd & H1 & H2).
    destruct (subst_spine_const f _ sb Eh) as [Eh' Ea]. exists D, s, d.
    rewrite Eh', Ea, length_map. auto.
  Qed.

  Lemma index_position_rename : forall f r, index_position sg f -> index_position sg (rename r f).
  Proof. intros f r H. rewrite rename_as_subst. apply index_position_subst, H. Qed.

  (** ** Renaming *)

  Theorem erases_rename :
    (forall G t T e, erases G t T e -> forall G' r, wf G' -> ren_ok G G' r ->
       erases G' (rename r t) (rename r T) (erename r e)) /\
    (forall G d ps P cs bs bs', erases_branches G d ps P cs bs bs' -> forall G' r, wf G' -> ren_ok G G' r ->
       length ps = length (ind_params d) -> forallb (ctor_closed (length (ind_params d))) cs = true ->
       erases_branches G' d (map (rename r) ps) (rename r P) cs (map (rename r) bs) (map (erename r) bs')).
  Proof.
    apply erases_mutind.
    (* □ and conversion *)
    - intros G t T Ht HT G' r HG Hr. cbn [erename].
      apply X_Box; [exact (ty_ren _ _ _ Ht _ _ HG Hr) | exact (erasable_at_rename _ _ _ _ HG Hr HT)].
    - intros G t A B s e _ IH HB Hc G' r HG Hr.
      eapply X_Conv; [exact (IH _ _ HG Hr) | exact (ty_ren _ _ _ HB _ _ HG Hr) | exact (conv_rename r _ _ Hc)].
    (* variables, λ, application, annotation *)
    - intros G n T Ht G' r HG Hr. cbn [rename erename]. apply X_Var. exact (ty_ren _ _ _ Ht _ _ HG Hr).
    - intros G A B b s b' _ IHb HP G' r HG Hr. cbn [rename erename].
      pose proof (ty_ren _ _ _ HP _ _ HG Hr) as HP'. cbn [rename] in HP'.
      destruct (pi_dom_typed S sg _ _ _ _ HP') as [s1 HA].
      eapply X_Lam; [ | exact HP']. exact (IHb _ _ (W_Cons _ _ _ _ _ HA) (ren_ok_up _ _ _ _ Hr)).
    - intros G f u A B f' u' _ IHf _ IHu G' r HG Hr. rewrite rename_subst1. cbn [rename erename].
      pose proof (IHf G' r HG Hr) as Hf. cbn [rename] in Hf.
      exact (X_App _ _ _ _ _ _ _ _ _ Hf (IHu G' r HG Hr)).
    - intros G f u A B f' _ IHf Hu Hip G' r HG Hr. rewrite rename_subst1. cbn [rename erename].
      pose proof (IHf G' r HG Hr) as Hf. cbn [rename] in Hf.
      exact (X_AppIndex _ _ _ _ _ _ _ _ Hf (ty_ren _ _ _ Hu _ _ HG Hr) (index_position_rename _ r Hip)).
    - intros G t A s e HA _ IHt G' r HG Hr. cbn [rename].
      eapply X_Ann; [exact (ty_ren _ _ _ HA _ _ HG Hr) | exact (IHt G' r HG Hr)].
    (* constants and the constructors of the primitives *)
    - intros G f T Ht G' r HG Hr. cbn [rename erename]. apply X_Def. exact (ty_ren _ _ _ Ht _ _ HG Hr).
    - intros G D c T Ht G' r HG Hr. cbn [rename erename]. apply X_Ctor. exact (ty_ren _ _ _ Ht _ _ HG Hr).
    - intros G D s T Ht Hs G' r HG Hr. cbn [rename erename]. apply X_Elim; [exact (ty_ren _ _ _ Ht _ _ HG Hr) | exact Hs].
    - intros G T Ht G' r HG Hr. cbn [rename erename]. apply X_Tt. exact (ty_ren _ _ _ Ht _ _ HG Hr).
    - intros G T Ht G' r HG Hr. cbn [rename erename]. apply X_True. exact (ty_ren _ _ _ Ht _ _ HG Hr).
    - intros G T Ht G' r HG Hr. cbn [rename erename]. apply X_False. exact (ty_ren _ _ _ Ht _ _ HG Hr).
    (* the eliminators of the primitives *)
    - intros G C e s e' HC _ IHe G' r HG Hr. cbn [rename erename map].
      eapply X_ElimVoid; [exact (ty_ren _ _ _ HC _ _ HG Hr) | exact (IHe G' r HG Hr)].
    - intros G C c u s c' u' HC _ IHc _ IHu G' r HG Hr. cbn [rename erename map].
      eapply X_ElimUnit; [exact (ty_ren _ _ _ HC _ _ HG Hr) | exact (IHc G' r HG Hr) | exact (IHu G' r HG Hr)].
    - intros G C x y b s x' y' b' HC _ IHx _ IHy _ IHb G' r HG Hr. cbn [rename erename map].
      eapply X_ElimBool;
        [exact (ty_ren _ _ _ HC _ _ HG Hr) | exact (IHx G' r HG Hr) | exact (IHy G' r HG Hr) | exact (IHb G' r HG Hr)].
    (* Σ *)
    - intros G A B a b s a' b' HS _ IHa _ IHb G' r HG Hr. cbn [rename erename].
      pose proof (IHb G' r HG Hr) as Hb. rewrite rename_subst1 in Hb.
      eapply X_Pair; [exact (ty_ren _ _ _ HS _ _ HG Hr) | exact (IHa G' r HG Hr) | exact Hb].
    - intros G p A B p' _ IHp G' r HG Hr. cbn [rename erename].
      pose proof (IHp G' r HG Hr) as Hp. cbn [rename] in Hp. exact (X_Fst _ _ _ _ _ _ _ Hp).
    - intros G p A B p' _ IHp G' r HG Hr. rewrite rename_subst1. cbn [rename erename].
      pose proof (IHp G' r HG Hr) as Hp. cbn [rename] in Hp. exact (X_Snd _ _ _ _ _ _ _ Hp).
    (* match on data *)
    - intros G D s P x bs d ps us x' bs' Hdecls Hind Hel Hlp Hlu Hsort _ IHx HP _ IHbs G' r HG Hr.
      destruct (sig_ind_closed _ _ _ Hind) as [Hi Hcs].
      rewrite rename_apps, map_app. cbn [map rename erename].
      pose proof (IHx G' r HG Hr) as Hx. rewrite rename_apps, map_app in Hx. cbn [rename] in Hx.
      pose proof (ty_ren _ _ _ HP _ _ HG Hr) as HP'. rewrite rename_case_motive_type in HP' by (rewrite Hlp; exact Hi).
      apply (X_Case _ _ G' D s (rename r P) (rename r x) (map (rename r) bs) d (map (rename r) ps)
               (map (rename r) us) (erename r x') (map (erename r) bs'));
        [exact Hdecls | exact Hind | exact Hel | rewrite length_map; exact Hlp | rewrite length_map; exact Hlu
        | exact Hsort | exact Hx | exact HP' | exact (IHbs G' r HG Hr Hlp Hcs)].
    (* match on a proposition without constructors *)
    - intros G D s P x d ps us x' Hdecls Hind Hel Hlp Hlu Hsort Helim Hctors _ IHx HP G' r HG Hr.
      destruct (sig_ind_closed _ _ _ Hind) as [Hi _].
      rewrite rename_apps, map_app. cbn [map rename erename].
      pose proof (IHx G' r HG Hr) as Hx. rewrite rename_apps, map_app in Hx. cbn [rename] in Hx.
      pose proof (ty_ren _ _ _ HP _ _ HG Hr) as HP'. rewrite rename_case_motive_type in HP' by (rewrite Hlp; exact Hi).
      apply (X_CaseEmpty _ _ G' D s (rename r P) (rename r x) d (map (rename r) ps) (map (rename r) us)
               (erename r x'));
        [exact Hdecls | exact Hind | exact Hel | rewrite length_map; exact Hlp | rewrite length_map; exact Hlu
        | exact Hsort | exact Helim | exact Hctors | exact Hx | exact HP'].
    (* match on a singleton proposition *)
    - intros G D s P x b d c ps us b' Hdecls Hind Hel Hlp Hlu Hsort Helim Hctors Hx HP _ IHb G' r HG Hr.
      destruct (sig_ind_closed _ _ _ Hind) as [Hi Hcs]. rewrite Hctors in Hcs. cbn [forallb] in Hcs.
      apply andb_prop in Hcs as [Hc _].
      rewrite rename_apps, map_app, erename_eapps, (map_box (erename r)) by reflexivity.
      cbn [map rename].
      pose proof (ty_ren _ _ _ Hx _ _ HG Hr) as Hx'. rewrite rename_apps, map_app in Hx'. cbn [rename] in Hx'.
      pose proof (ty_ren _ _ _ HP _ _ HG Hr) as HP'. rewrite rename_case_motive_type in HP' by (rewrite Hlp; exact Hi).
      pose proof (IHb G' r HG Hr) as Hb. rewrite rename_case_branch_type in Hb by assumption.
      apply (X_CaseSingleton _ _ G' D s (rename r P) (rename r x) (rename r b) d c (map (rename r) ps)
               (map (rename r) us) (erename r b'));
        [exact Hdecls | exact Hind | exact Hel | rewrite length_map; exact Hlp | rewrite length_map; exact Hlu
        | exact Hsort | exact Helim | exact Hctors | exact Hx' | exact HP' | exact Hb].
    (* fix *)
    - intros G A k b s D b' HA Hsa Hne _ IHb Hg G' r HG Hr. cbn [rename erename].
      pose proof (ty_ren _ _ _ HA _ _ HG Hr) as HA'. cbn [rename] in HA'.
      pose proof (IHb _ _ (W_Cons _ _ _ _ _ HA') (ren_ok_up _ _ _ _ Hr)) as Hb. rewrite rename_up_lift1 in Hb.
      eapply X_Fix; [exact HA' | exact (struct_arg_rename _ _ _ _ r Hsa) | exact Hne | exact Hb
                    | exact (fix_guarded_rename _ _ _ r Hg)].
    (* the branches *)
    - intros G d ps P G' r HG Hr Hl Hc. constructor.
    - intros G d ps P c cs b bs b' bs' _ IHb _ IHbs G' r HG Hr Hl Hc.
      cbn [forallb] in Hc. apply andb_prop in Hc as [Hc1 Hc2]. cbn [map].
      constructor; [ | exact (IHbs G' r HG Hr Hl Hc2)].
      pose proof (IHb G' r HG Hr) as Hb. rewrite rename_case_branch_type in Hb by assumption. exact Hb.
  Qed.

  (** Weakening by one well-sorted type. *)
  Corollary erases_weaken1 : forall G t T e B s, erases G t T e -> typed G B (Srt s) ->
    erases (B :: G) (lift 1 t) (lift 1 T) (elift 1 e).
  Proof.
    intros G t T e B s H HB. apply (proj1 erases_rename _ _ _ _ H (B :: G) (Nat.add 1)).
    - exact (W_Cons _ _ _ _ _ HB).
    - intros n A HA. change (Nat.add 1 n) with (Datatypes.S n). rewrite lookup_cons_S, HA. reflexivity.
  Qed.

  (** ** Substitution *)

  (** [sb] sends the context [G] into [G'], every variable to a term with
      an erasure at the substituted type, given by [esb]. *)
  Definition esub_ok (G G' : ctx) (sb : nat -> term) (esb : nat -> eterm) : Prop :=
    forall n A, lookup G n = Some A -> erases G' (sb n) (subst sb A) (esb n).

  Lemma esub_ok_typed : forall G G' sb esb, esub_ok G G' sb esb -> sub_ok S sg G G' sb.
  Proof. intros G G' sb esb H n A HA. exact (proj1 (erases_typed S sg) _ _ _ _ (H n A HA)). Qed.

  Lemma esub_ok_up : forall G G' sb esb A s, esub_ok G G' sb esb -> typed G' (subst sb A) (Srt s) ->
    esub_ok (A :: G) (subst sb A :: G') (up_sub sb) (eup esb).
  Proof.
    intros G G' sb esb A s H HA [|n] B HB.
    - rewrite lookup_cons_0 in HB. injection HB as <-. rewrite subst_up_lift1. cbn [up_sub eup].
      apply X_Var. apply T_Var; [exact (W_Cons _ _ _ _ _ HA) | apply lookup_cons_0].
    - rewrite lookup_cons_S in HB. destruct (lookup G n) as [B'|] eqn:E; [ | discriminate HB].
      injection HB as <-. rewrite subst_up_lift1. cbn [up_sub eup].
      exact (erases_weaken1 _ _ _ _ _ _ (H n B' E) HA).
  Qed.

  Theorem erases_subst :
    (forall G t T e, erases G t T e -> forall G' sb esb, wf G' -> esub_ok G G' sb esb ->
       erases G' (subst sb t) (subst sb T) (esubst esb e)) /\
    (forall G d ps P cs bs bs', erases_branches G d ps P cs bs bs' ->
       forall G' sb esb, wf G' -> esub_ok G G' sb esb ->
       length ps = length (ind_params d) -> forallb (ctor_closed (length (ind_params d))) cs = true ->
       erases_branches G' d (map (subst sb) ps) (subst sb P) cs (map (subst sb) bs) (map (esubst esb) bs')).
  Proof.
    apply erases_mutind.
    (* □ and conversion *)
    - intros G t T Ht HT G' sb esb HG Hs. cbn [esubst]. pose proof (esub_ok_typed _ _ _ _ Hs) as Hs'.
      apply X_Box; [exact (ty_sub _ _ _ Ht _ _ HG Hs') | exact (erasable_at_subst _ _ _ _ HG Hs' HT)].
    - intros G t A B s e _ IH HB Hc G' sb esb HG Hs.
      eapply X_Conv; [exact (IH _ _ _ HG Hs) | exact (ty_sub _ _ _ HB _ _ HG (esub_ok_typed _ _ _ _ Hs))
                     | exact (conv_subst sb _ _ Hc)].
    (* a variable: the term substituted for it, converted *)
    - intros G n T Ht G' sb esb HG Hs. cbn [subst esubst].
      destruct (inv_var S sg _ _ _ Ht) as (A & HA & HAT). pose proof (Hs n A HA) as H1.
      destruct HAT as [<- | [Hc [s HT]]]; [exact H1 | ].
      eapply X_Conv; [exact H1 | exact (ty_sub _ _ _ HT _ _ HG (esub_ok_typed _ _ _ _ Hs))
                     | exact (conv_subst sb _ _ Hc)].
    (* λ, application, annotation *)
    - intros G A B b s b' _ IHb HP G' sb esb HG Hs. cbn [subst esubst].
      pose proof (ty_sub _ _ _ HP _ _ HG (esub_ok_typed _ _ _ _ Hs)) as HP'. cbn [subst] in HP'.
      destruct (pi_dom_typed S sg _ _ _ _ HP') as [s1 HA].
      eapply X_Lam; [ | exact HP']. exact (IHb _ _ _ (W_Cons _ _ _ _ _ HA) (esub_ok_up _ _ _ _ _ _ Hs HA)).
    - intros G f u A B f' u' _ IHf _ IHu G' sb esb HG Hs. rewrite subst_subst1. cbn [subst esubst].
      pose proof (IHf G' sb esb HG Hs) as Hf. cbn [subst] in Hf.
      exact (X_App _ _ _ _ _ _ _ _ _ Hf (IHu G' sb esb HG Hs)).
    - intros G f u A B f' _ IHf Hu Hip G' sb esb HG Hs. rewrite subst_subst1. cbn [subst esubst].
      pose proof (IHf G' sb esb HG Hs) as Hf. cbn [subst] in Hf.
      exact (X_AppIndex _ _ _ _ _ _ _ _ Hf (ty_sub _ _ _ Hu _ _ HG (esub_ok_typed _ _ _ _ Hs))
               (index_position_subst _ sb Hip)).
    - intros G t A s e HA _ IHt G' sb esb HG Hs. cbn [subst].
      eapply X_Ann; [exact (ty_sub _ _ _ HA _ _ HG (esub_ok_typed _ _ _ _ Hs)) | exact (IHt G' sb esb HG Hs)].
    (* constants and the constructors of the primitives *)
    - intros G f T Ht G' sb esb HG Hs. cbn [subst esubst]. apply X_Def.
      exact (ty_sub _ _ _ Ht _ _ HG (esub_ok_typed _ _ _ _ Hs)).
    - intros G D c T Ht G' sb esb HG Hs. cbn [subst esubst]. apply X_Ctor.
      exact (ty_sub _ _ _ Ht _ _ HG (esub_ok_typed _ _ _ _ Hs)).
    - intros G D s T Ht Hp G' sb esb HG Hs. cbn [subst esubst]. apply X_Elim; [ | exact Hp].
      exact (ty_sub _ _ _ Ht _ _ HG (esub_ok_typed _ _ _ _ Hs)).
    - intros G T Ht G' sb esb HG Hs. cbn [subst esubst]. apply X_Tt.
      exact (ty_sub _ _ _ Ht _ _ HG (esub_ok_typed _ _ _ _ Hs)).
    - intros G T Ht G' sb esb HG Hs. cbn [subst esubst]. apply X_True.
      exact (ty_sub _ _ _ Ht _ _ HG (esub_ok_typed _ _ _ _ Hs)).
    - intros G T Ht G' sb esb HG Hs. cbn [subst esubst]. apply X_False.
      exact (ty_sub _ _ _ Ht _ _ HG (esub_ok_typed _ _ _ _ Hs)).
    (* the eliminators of the primitives *)
    - intros G C e s e' HC _ IHe G' sb esb HG Hs. cbn [subst esubst map].
      eapply X_ElimVoid; [exact (ty_sub _ _ _ HC _ _ HG (esub_ok_typed _ _ _ _ Hs)) | exact (IHe G' sb esb HG Hs)].
    - intros G C c u s c' u' HC _ IHc _ IHu G' sb esb HG Hs. cbn [subst esubst map].
      eapply X_ElimUnit; [exact (ty_sub _ _ _ HC _ _ HG (esub_ok_typed _ _ _ _ Hs)) | exact (IHc G' sb esb HG Hs)
                         | exact (IHu G' sb esb HG Hs)].
    - intros G C x y b s x' y' b' HC _ IHx _ IHy _ IHb G' sb esb HG Hs. cbn [subst esubst map].
      eapply X_ElimBool; [exact (ty_sub _ _ _ HC _ _ HG (esub_ok_typed _ _ _ _ Hs)) | exact (IHx G' sb esb HG Hs)
                         | exact (IHy G' sb esb HG Hs) | exact (IHb G' sb esb HG Hs)].
    (* Σ *)
    - intros G A B a b s a' b' HS _ IHa _ IHb G' sb esb HG Hs. cbn [subst esubst].
      pose proof (IHb G' sb esb HG Hs) as Hb. rewrite subst_subst1 in Hb.
      eapply X_Pair; [exact (ty_sub _ _ _ HS _ _ HG (esub_ok_typed _ _ _ _ Hs)) | exact (IHa G' sb esb HG Hs)
                     | exact Hb].
    - intros G p A B p' _ IHp G' sb esb HG Hs. cbn [subst esubst].
      pose proof (IHp G' sb esb HG Hs) as Hp. cbn [subst] in Hp. exact (X_Fst _ _ _ _ _ _ _ Hp).
    - intros G p A B p' _ IHp G' sb esb HG Hs. rewrite subst_subst1. cbn [subst esubst].
      pose proof (IHp G' sb esb HG Hs) as Hp. cbn [subst] in Hp. exact (X_Snd _ _ _ _ _ _ _ Hp).
    (* match on data *)
    - intros G D s P x bs d ps us x' bs' Hdecls Hind Hel Hlp Hlu Hsort _ IHx HP _ IHbs G' sb esb HG Hs.
      destruct (sig_ind_closed _ _ _ Hind) as [Hi Hcs].
      rewrite subst_apps, map_app. cbn [map subst esubst].
      pose proof (IHx G' sb esb HG Hs) as Hx. rewrite subst_apps, map_app in Hx. cbn [subst] in Hx.
      pose proof (ty_sub _ _ _ HP _ _ HG (esub_ok_typed _ _ _ _ Hs)) as HP'.
      rewrite subst_case_motive_type in HP' by (rewrite Hlp; exact Hi).
      apply (X_Case _ _ G' D s (subst sb P) (subst sb x) (map (subst sb) bs) d (map (subst sb) ps)
               (map (subst sb) us) (esubst esb x') (map (esubst esb) bs'));
        [exact Hdecls | exact Hind | exact Hel | rewrite length_map; exact Hlp | rewrite length_map; exact Hlu
        | exact Hsort | exact Hx | exact HP' | exact (IHbs G' sb esb HG Hs Hlp Hcs)].
    (* match on a proposition without constructors *)
    - intros G D s P x d ps us x' Hdecls Hind Hel Hlp Hlu Hsort Helim Hctors _ IHx HP G' sb esb HG Hs.
      destruct (sig_ind_closed _ _ _ Hind) as [Hi _].
      rewrite subst_apps, map_app. cbn [map subst esubst].
      pose proof (IHx G' sb esb HG Hs) as Hx. rewrite subst_apps, map_app in Hx. cbn [subst] in Hx.
      pose proof (ty_sub _ _ _ HP _ _ HG (esub_ok_typed _ _ _ _ Hs)) as HP'.
      rewrite subst_case_motive_type in HP' by (rewrite Hlp; exact Hi).
      apply (X_CaseEmpty _ _ G' D s (subst sb P) (subst sb x) d (map (subst sb) ps) (map (subst sb) us)
               (esubst esb x'));
        [exact Hdecls | exact Hind | exact Hel | rewrite length_map; exact Hlp | rewrite length_map; exact Hlu
        | exact Hsort | exact Helim | exact Hctors | exact Hx | exact HP'].
    (* match on a singleton proposition *)
    - intros G D s P x b d c ps us b' Hdecls Hind Hel Hlp Hlu Hsort Helim Hctors Hx HP _ IHb G' sb esb HG Hs.
      pose proof (esub_ok_typed _ _ _ _ Hs) as Hs'.
      destruct (sig_ind_closed _ _ _ Hind) as [Hi Hcs]. rewrite Hctors in Hcs. cbn [forallb] in Hcs.
      apply andb_prop in Hcs as [Hc _].
      rewrite subst_apps, map_app, esubst_eapps, (map_box (esubst esb)) by reflexivity.
      cbn [map subst].
      pose proof (ty_sub _ _ _ Hx _ _ HG Hs') as Hx'. rewrite subst_apps, map_app in Hx'. cbn [subst] in Hx'.
      pose proof (ty_sub _ _ _ HP _ _ HG Hs') as HP'. rewrite subst_case_motive_type in HP' by (rewrite Hlp; exact Hi).
      pose proof (IHb G' sb esb HG Hs) as Hb. rewrite subst_case_branch_type in Hb by assumption.
      apply (X_CaseSingleton _ _ G' D s (subst sb P) (subst sb x) (subst sb b) d c (map (subst sb) ps)
               (map (subst sb) us) (esubst esb b'));
        [exact Hdecls | exact Hind | exact Hel | rewrite length_map; exact Hlp | rewrite length_map; exact Hlu
        | exact Hsort | exact Helim | exact Hctors | exact Hx' | exact HP' | exact Hb].
    (* fix *)
    - intros G A k b s D b' HA Hsa Hne _ IHb Hg G' sb esb HG Hs. cbn [subst esubst].
      pose proof (ty_sub _ _ _ HA _ _ HG (esub_ok_typed _ _ _ _ Hs)) as HA'. cbn [subst] in HA'.
      pose proof (IHb _ _ _ (W_Cons _ _ _ _ _ HA') (esub_ok_up _ _ _ _ _ _ Hs HA')) as Hb.
      rewrite subst_up_lift1 in Hb.
      eapply X_Fix; [exact HA' | exact (struct_arg_subst _ _ _ _ sb Hsa) | exact Hne | exact Hb
                    | exact (fix_guarded_subst _ _ _ sb Hg)].
    (* the branches *)
    - intros G d ps P G' sb esb HG Hs Hl Hc. constructor.
    - intros G d ps P c cs b bs b' bs' _ IHb _ IHbs G' sb esb HG Hs Hl Hc.
      cbn [forallb] in Hc. apply andb_prop in Hc as [Hc1 Hc2]. cbn [map].
      constructor; [ | exact (IHbs G' sb esb HG Hs Hl Hc2)].
      pose proof (IHb G' sb esb HG Hs) as Hb. rewrite subst_case_branch_type in Hb by assumption. exact Hb.
  Qed.

  (** The substitution lemma for one variable. *)
  Corollary erases_subst1 : forall G A b B u eb eu, erases (A :: G) b B eb -> erases G u A eu ->
    erases G (subst1 b u) (subst1 B u) (esubst1 eb eu).
  Proof.
    intros G A b B u eb eu Hb Hu.
    pose proof (typed_wf S sg _ _ _ (proj1 (erases_typed S sg) _ _ _ _ Hu)) as HG.
    unfold subst1, esubst1.
    apply (proj1 erases_subst _ _ _ _ Hb G (scons u Var) (fun n => match n with 0 => eu | Datatypes.S n' => EVar n' end) HG).
    intros [|n] B' HB'.
    - rewrite lookup_cons_0 in HB'. injection HB' as <-.
      change (erases G u (subst1 (lift 1 A) u) eu). rewrite subst1_lift. exact Hu.
    - rewrite lookup_cons_S in HB'. destruct (lookup G n) as [B''|] eqn:E; [ | discriminate HB'].
      injection HB' as <-. change (erases G (Var n) (subst1 (lift 1 B'') u) (EVar n)). rewrite subst1_lift.
      apply X_Var. apply T_Var; [exact HG | exact E].
  Qed.
End ErasureSubst.
