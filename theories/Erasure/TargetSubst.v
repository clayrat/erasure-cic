(** * Renaming and substitution of erased terms

    The laws of [erename], [elift] and [esubst] of Erasure/Target.v the
    relation of a signature with its erasure needs: renamings compose
    ([erename_erename]), a substitution under [m] binders ([eupn]) lifts
    what it substitutes past them ([eupn_ge]), and the erased arguments
    of a telescope substitute for its variables ([etsub], after [tsub]
    of PTS.Inversion: the argument of the outermost entry, under the
    others, first). *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.
From DepTypes.PTS Require Import Syntax.
From CIC.Erasure Require Import Target.

Local Open Scope list_scope.

(** ** Renaming and substitution of erased terms *)

Lemma erename_ext : forall t r r', (forall n, r n = r' n) -> erename r t = erename r' t.
Proof.
  fix IH 1. intros t r r' H.
  assert (Hup : forall n, up_ren r n = up_ren r' n) by (intros [|n]; cbn [up_ren]; [reflexivity | rewrite H; reflexivity]).
  destruct t as [ | n | b | f a | c | D c | D x bs | k b | a b | p | p | D s ]; cbn [erename]; try reflexivity.
  - rewrite H. reflexivity.
  - f_equal. exact (IH _ _ _ Hup).
  - f_equal; apply IH; exact H.
  - f_equal; [exact (IH _ _ _ H) | ]. induction bs as [|b bs IHbs]; [reflexivity | ].
    cbn [map]. f_equal; [exact (IH _ _ _ H) | exact IHbs].
  - f_equal. exact (IH _ _ _ Hup).
  - f_equal; apply IH; exact H.
  - f_equal. apply IH. exact H.
  - f_equal. apply IH. exact H.
Qed.

Lemma erename_erename : forall t r1 r2, erename r1 (erename r2 t) = erename (fun n => r1 (r2 n)) t.
Proof.
  fix IH 1. intros t r1 r2.
  assert (Hup : forall n, up_ren r1 (up_ren r2 n) = up_ren (fun n => r1 (r2 n)) n) by (intros [|n]; reflexivity).
  destruct t as [ | n | b | f a | c | D c | D x bs | k b | a b | p | p | D s ]; cbn [erename]; try reflexivity.
  - f_equal. rewrite IH. apply erename_ext. exact Hup.
  - f_equal; apply IH.
  - f_equal; [apply IH | ]. induction bs as [|b bs IHbs]; [reflexivity | ].
    cbn [map]. f_equal; [apply IH | exact IHbs].
  - f_equal. rewrite IH. apply erename_ext. exact Hup.
  - f_equal; apply IH.
  - f_equal. apply IH.
  - f_equal. apply IH.
Qed.

Lemma elift_elift : forall m n t, elift m (elift n t) = elift (m + n) t.
Proof.
  intros m n t. unfold elift. rewrite erename_erename. apply erename_ext. intros i. lia.
Qed.

(** [sb] under [m] binders, the innermost first. *)
Fixpoint eupn (m : nat) (sb : nat -> eterm) : nat -> eterm :=
  match m with 0 => sb | S m' => eupn m' (eup sb) end.


(** The identity renaming. *)
Lemma erename_id : forall t, erename (fun n => n) t = t.
Proof.
  fix IH 1. intros t.
  destruct t as [ | n | b | f a | c | D c | D x bs | k b | a b | p | p | D s ]; cbn [erename]; try reflexivity.
  - f_equal. rewrite (erename_ext b (up_ren (fun n => n)) (fun n => n)) by (intros [|n]; reflexivity). apply IH.
  - f_equal; apply IH.
  - f_equal; [apply IH | ]. induction bs as [|b bs IHbs]; [reflexivity | ].
    cbn [map]. f_equal; [apply IH | exact IHbs].
  - f_equal. rewrite (erename_ext b (up_ren (fun n => n)) (fun n => n)) by (intros [|n]; reflexivity). apply IH.
  - f_equal; apply IH.
  - f_equal. apply IH.
  - f_equal. apply IH.
Qed.

Lemma eupn_ge : forall m sb j, eupn m sb (m + j) = elift m (sb j).
Proof.
  induction m as [|m IH]; intros sb j.
  - cbn [eupn]. unfold elift. symmetry. rewrite (erename_ext (sb j) (Nat.add 0) (fun n => n)) by reflexivity.
    apply erename_id.
  - cbn [eupn]. replace (Datatypes.S m + j) with (m + Datatypes.S j) by lia. rewrite IH. cbn [eup].
    rewrite elift_elift. f_equal. lia.
Qed.

Lemma eupn_lt : forall m sb i, i < m -> eupn m sb i = EVar i.
Proof.
  induction m as [|m IH]; intros sb i Hi; [lia | ]. cbn [eupn].
  destruct (Nat.lt_ge_cases i m) as [H | H]; [exact (IH _ _ H) | ].
  replace i with (m + 0) by lia. rewrite eupn_ge. cbn [eup]. unfold elift. cbn [erename]. reflexivity.
Qed.

Lemma esubst_elams : forall m sb b, esubst sb (elams m b) = elams m (esubst (eupn m sb) b).
Proof. induction m as [|m IH]; intros sb b; [reflexivity | ]. cbn [elams esubst eupn]. rewrite IH. reflexivity. Qed.

Lemma esubst_evars : forall m sb, map (esubst (eupn m sb)) (evars m) = evars m.
Proof.
  intros m sb. assert (H : forall n, n <= m -> map (esubst (eupn m sb)) (evars n) = evars n).
  { induction n as [|n IH]; intros Hn; [reflexivity | ]. cbn [evars map esubst].
    rewrite eupn_lt by lia. rewrite IH by lia. reflexivity. }
  apply H. lia.
Qed.

(** ** Substituting erased arguments for the variables of a telescope *)

Definition etsub (es : list eterm) : nat -> eterm :=
  fun i => nth i (rev es) (EVar (i - length es)).

Lemma etsub_app_lt : forall l r i, i < length r -> etsub (l ++ r) i = etsub r i.
Proof.
  intros l r i H. unfold etsub. rewrite rev_app_distr, app_nth1 by (rewrite length_rev; exact H).
  apply nth_indep. rewrite length_rev. exact H.
Qed.

Lemma etsub_app_ge : forall l r j, etsub (l ++ r) (length r + j) = etsub l j.
Proof.
  intros l r j. unfold etsub. rewrite rev_app_distr, app_nth2 by (rewrite length_rev; lia).
  rewrite length_rev. replace (length r + j - length r) with j by lia. rewrite length_app.
  replace (length r + j - (length l + length r)) with (j - length l) by lia. reflexivity.
Qed.

(** The erased variables [EVar (base + n - 1), …, EVar base]. *)
Fixpoint evarsb (base n : nat) : list eterm :=
  match n with 0 => [] | S n' => EVar (base + n') :: evarsb base n' end.

Lemma evarsb_0 : forall n, evarsb 0 n = evars n.
Proof. induction n as [|n IH]; [reflexivity | cbn [evarsb evars]; rewrite IH; reflexivity]. Qed.

Lemma length_evarsb : forall base n, length (evarsb base n) = n.
Proof. intros base n. induction n; cbn; congruence. Qed.

Lemma map_etsub_evarsb : forall l m, map (esubst (etsub (l ++ m))) (evarsb (length m) (length l)) = l.
Proof.
  induction l as [|a l IH]; intros m; [reflexivity | ].
  cbn [length evarsb map esubst]. f_equal.
  - change ((a :: l) ++ m) with ([a] ++ (l ++ m)).
    replace (length m + length l) with (length (l ++ m) + 0) by (rewrite length_app; lia).
    rewrite etsub_app_ge. reflexivity.
  - transitivity (map (esubst (etsub (l ++ m))) (evarsb (length m) (length l))); [ | exact (IH m)].
    apply map_ext_in. intros e He.
    assert (Hv : exists j, e = EVar j /\ length m <= j < length m + length l).
    { clear IH. induction (length l) as [|n IHn]; [destruct He | ].
      destruct He as [<- | He]; [exists (length m + n); split; [reflexivity | lia] | ].
      destruct (IHn He) as (j & -> & Hj). exists j. split; [reflexivity | lia]. }
    destruct Hv as (j & -> & Hj). cbn [esubst].
    change ((a :: l) ++ m) with ([a] ++ (l ++ m)). rewrite etsub_app_lt by (rewrite length_app; lia). reflexivity.
Qed.

Lemma map_etsub_evarsb_in : forall l0 l m,
  map (esubst (etsub (l0 ++ l ++ m))) (evarsb (length m) (length l)) = l.
Proof.
  intros l0 l m. transitivity (map (esubst (etsub (l ++ m))) (evarsb (length m) (length l)));
    [ | exact (map_etsub_evarsb l m)].
  apply map_ext_in. intros e He.
  assert (Hv : exists j, e = EVar j /\ j < length m + length l).
  { clear l0. induction (length l) as [|n IHn]; [destruct He | ].
    destruct He as [<- | He]; [exists (length m + n); split; [reflexivity | lia] | ].
    destruct (IHn He) as (j & -> & Hj). exists j. split; [reflexivity | lia]. }
  destruct Hv as (j & -> & Hj). cbn [esubst]. rewrite etsub_app_lt by (rewrite length_app; lia). reflexivity.
Qed.

Lemma eapps_app : forall h l1 l2, eapps h (l1 ++ l2) = eapps (eapps h l1) l2.
Proof. intros h l1 l2. unfold eapps. apply fold_left_app. Qed.

