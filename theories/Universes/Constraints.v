(** * Constraints between levels and their fragment

    A constraint [ℓ₁ + w ≤ ℓ₂] compares two level expressions, with an
    integer offset [w]: [ℓ₁ ≤ ℓ₂] is [w = 0], [ℓ₁ < ℓ₂] is [w = 1], and
    the constraints of a polymorphic constant keep their offsets when
    levels are substituted for its variables.

    The supported fragment, fixed before the graph:
    - a maximum on the left is exact: [max(aᵢ + kᵢ) + w ≤ ℓ] iff every
      [aᵢ + kᵢ + w ≤ ℓ];
    - on the right one atom with an offset, [b + m]; then each element on
      the left is the edge [(aᵢ, kᵢ + w - m, b)] of the graph, and the
      constraint holds in a valuation iff its edges do
      ([decompose_sound]);
    - a maximum of several atoms on the right is a disjunction, which is
      not an edge.  Such a constraint is never added to the graph; it is
      accepted only when each element on the left is entailed below one
      element on the right, and otherwise refused as outside the
      fragment ([CUnsupported]), not as false.
    Edges that hold in every valuation ([a + w ≤ a] or [0 + w ≤ b] with
    [w ≤ 0]) are dropped.

    [close_context] decides the context of a definition from its
    declared constraints [C] and the requirements [R] its checking
    produced:
    - [Rigid]: the declared constraints are the whole context; each
      requirement must be entailed by them, or is refused with a
      counter-model;
    - [Extensible]: the requirements in the fragment are added, and the
      graph must have no cycle of positive weight.
    In both modes [C] must be in the fragment and consistent.  The answer
    carries a model, and [close_context_sound] proves what it promises. *)

From Stdlib Require Import String List Bool Arith ZArith Lia.
Import ListNotations.
From DepTypes.Common Require Import Result.
From CIC.Universes Require Import Level Graph.

Local Open Scope Z_scope.

Record constr : Type := Constr { c_lhs : level; c_off : Z; c_rhs : level }.

Definition cle (l1 l2 : level) : constr := Constr l1 0 l2.
Definition clt (l1 l2 : level) : constr := Constr l1 1 l2.

Definition csat (v : valuation) (c : constr) : Prop :=
  Z.of_nat (leval v (c_lhs c)) + c_off c <= Z.of_nat (leval v (c_rhs c)).

Definition csubst (σ : lsubst_map) (c : constr) : constr :=
  Constr (lsubst σ (c_lhs c)) (c_off c) (lsubst σ (c_rhs c)).

(** ** Decomposition into edges *)

Definition trivial_edge (e : edge) : bool :=
  (e_w e <=? 0) && (atom_eqb (e_src e) (e_dst e) || atom_eqb (e_src e) LZero).

Lemma trivial_edge_sat : forall v e, trivial_edge e = true -> edge_sat v e.
Proof.
  intros v [[a w] b] H. unfold trivial_edge in H; cbn in H.
  apply andb_prop in H as [Hw H]. apply Z.leb_le in Hw. unfold edge_sat; cbn.
  apply orb_prop in H as [H | H]; apply atom_eqb_eq in H; subst; cbn; lia.
Qed.

Definition edges_to (b : atom) (m : nat) (w : Z) (l : level) : list edge :=
  filter (fun e => negb (trivial_edge e))
    (map (fun x => (fst x, Z.of_nat (snd x) + w - Z.of_nat m, b)) (elems (lnorm l))).

Definition decompose (c : constr) : option (list edge) :=
  match elems (lnorm (c_rhs c)) with
  | [(b, m)] => Some (edges_to b m (c_off c) (c_lhs c))
  | _ => None
  end.

Definition decomposable (c : constr) : bool :=
  match decompose c with Some _ => true | None => false end.

(** A bound on the maximum of a nonempty list is a bound on each
    element. *)
Lemma leval_bound : forall v l w R, l <> [] ->
  (Z.of_nat (leval v l) + w <= R <-> Forall (fun x => Z.of_nat (eval_elem v x) + w <= R) l).
Proof.
  intros v l w R. induction l as [|x l IH]; intros H; [congruence | ].
  change (leval v (x :: l)) with (Nat.max (eval_elem v x) (leval v l)).
  destruct l as [|y l].
  - change (leval v []) with O. split; intros H1.
    + constructor; [lia | constructor].
    + inversion H1; subst. lia.
  - specialize (IH ltac:(discriminate)). split; intros H1.
    + constructor; [lia | apply IH; lia].
    + inversion H1 as [|? ? Hx Hl]; subst. apply IH in Hl. lia.
Qed.

Lemma elems_nonempty : forall l, elems l <> [].
Proof. intros [|x l]; discriminate. Qed.

Lemma leval_norm_elems : forall v l, leval v (elems (lnorm l)) = leval v l.
Proof. intros v l. rewrite leval_elems. apply lnorm_sound. Qed.

Lemma models_filter_trivial : forall v es,
  models v (filter (fun e => negb (trivial_edge e)) es) <-> models v es.
Proof.
  intros v es. unfold models. rewrite !Forall_forall. split.
  - intros H e He. destruct (trivial_edge e) eqn:E; [exact (trivial_edge_sat v e E) | ].
    apply H, filter_In. rewrite E. auto.
  - intros H e He. apply filter_In in He as [He _]. exact (H e He).
Qed.

(** Each element of the left, below the value [R]. *)
Lemma models_edges_to : forall v b m w l,
  models v (edges_to b m w l) <->
  Forall (fun x => Z.of_nat (eval_elem v x) + w <= Z.of_nat (aval v b + m)) (elems (lnorm l)).
Proof.
  intros v b m w l. unfold edges_to. rewrite models_filter_trivial. unfold models.
  rewrite Forall_map, !Forall_forall. split; intros H x Hx; specialize (H x Hx);
    unfold edge_sat, eval_elem in *; cbn [e_src e_w e_dst] in *; lia.
Qed.

Theorem decompose_sound : forall c es, decompose c = Some es ->
  forall v, models v es <-> csat v c.
Proof.
  intros [l1 w l2] es H v. unfold decompose in H; cbn [c_lhs c_off c_rhs] in H.
  destruct (elems (lnorm l2)) as [|[b m] [|y r]] eqn:E2; try discriminate H.
  injection H as <-. unfold csat; cbn [c_lhs c_off c_rhs].
  rewrite models_edges_to, <- (leval_norm_elems v l1), <- (leval_norm_elems v l2), E2.
  rewrite (leval_bound v _ w _ (elems_nonempty _)).
  replace (leval v [(b, m)]) with (aval v b + m)%nat by (cbn; unfold eval_elem; cbn; lia).
  reflexivity.
Qed.

(** ** Graphs of lists of constraints *)

Fixpoint graph_of (cs : list constr) : option (list edge) :=
  match cs with
  | [] => Some []
  | c :: cs' =>
      match decompose c, graph_of cs' with
      | Some es, Some G => Some (es ++ G)
      | _, _ => None
      end
  end.

Theorem graph_of_sound : forall cs G, graph_of cs = Some G ->
  forall v, models v G <-> Forall (csat v) cs.
Proof.
  induction cs as [|c cs IH]; intros G H v; cbn in H.
  - injection H as <-. split; constructor.
  - destruct (decompose c) as [es|] eqn:E1; [ | discriminate H].
    destruct (graph_of cs) as [G'|] eqn:E2; [ | discriminate H]. injection H as <-.
    unfold models. rewrite Forall_app. fold (models v es). fold (models v G').
    rewrite (decompose_sound c es E1 v), (IH G' eq_refl v). split.
    + intros [H1 H2]. constructor; assumption.
    + intros H1. inversion H1; subst. auto.
Qed.

(** ** Entailment of a constraint *)

Definition implied (G : list edge) (c : constr) : bool :=
  match decompose c with
  | Some es => forallb (entailed G) es
  | None =>
      forallb (fun x => existsb (fun y => entailed G (fst x, Z.of_nat (snd x) + c_off c - Z.of_nat (snd y), fst y))
                                (elems (lnorm (c_rhs c))))
              (elems (lnorm (c_lhs c)))
  end.

Theorem implied_sound : forall G c, implied G c = true -> forall v, models v G -> csat v c.
Proof.
  intros G c H v Hv. unfold implied in H. destruct (decompose c) as [es|] eqn:E.
  - apply (decompose_sound c es E v). apply Forall_forall. intros e He.
    rewrite forallb_forall in H. exact (entailed_sound G e (H e He) v Hv).
  - destruct c as [l1 w l2]. unfold csat; cbn [c_lhs c_off c_rhs] in *.
    rewrite <- (leval_norm_elems v l1). apply (leval_bound v _ w _ (elems_nonempty _)).
    apply Forall_forall. intros x Hx. rewrite forallb_forall in H.
    apply H, existsb_exists in Hx as (y & Hy & He).
    pose proof (entailed_sound G _ He v Hv) as Hs. unfold edge_sat in Hs; cbn [e_src e_w e_dst] in Hs.
    pose proof (leval_ge v _ y Hy) as Hge. rewrite leval_norm_elems in Hge.
    unfold eval_elem in *. lia.
Qed.

(** A counter-model of a decomposable constraint, for the message of a
    refusal. *)
Definition refute (G : list edge) (c : constr) : option model :=
  match decompose c with
  | Some es =>
      fold_right (fun e r => match entails G e with Refuted m => Some m | _ => r end) None es
  | None => None
  end.

Lemma refute_found : forall G es m,
  fold_right (fun e r => match entails G e with Refuted m => Some m | _ => r end) None es = Some m ->
  exists e, In e es /\ entails G e = Refuted m.
Proof.
  intros G es m. induction es as [|e es IH]; intros H; cbn in H; [discriminate H | ].
  destruct (entails G e) eqn:Ee;
    [ destruct (IH H) as (f & Hf & Ef); exists f; split; [right; exact Hf | exact Ef]
    | injection H as <-; exists e; split; [left; reflexivity | exact Ee]
    | destruct (IH H) as (f & Hf & Ef); exists f; split; [right; exact Hf | exact Ef] ].
Qed.

Lemma refute_sound : forall G c m, refute G c = Some m -> models (val_of m) G /\ ~ csat (val_of m) c.
Proof.
  intros G c m H. unfold refute in H. destruct (decompose c) as [es|] eqn:E; [ | discriminate H].
  destruct (refute_found G es m H) as (e & He & Ee).
  destruct (entails_refuted _ _ _ Ee) as [HG Hn]. split; [exact HG | ].
  intros Hc. apply Hn. apply (decompose_sound c _ E) in Hc. unfold models in Hc.
  rewrite Forall_forall in Hc. exact (Hc e He).
Qed.

(** ** The context of a definition *)

Inductive mode : Type := Rigid | Extensible.

Inductive cerror : Type :=
| CNotInFragment : constr -> cerror          (** a declared constraint with a max on the right *)
| CCycle : list edge -> cerror               (** a cycle of positive weight *)
| CNotImplied : constr -> option model -> cerror  (** rigid: a requirement not entailed *)
| CUnsupported : constr -> cerror            (** a max on the right, not entailed by an element *)
| CUnknown : cerror.                         (** a certificate that did not check *)

Definition consistent (G : list edge) : result cerror model :=
  match solve G with
  | Consistent m => Ok m
  | Cycle c => Err (CCycle c)
  | Unknown => Err CUnknown
  end.

Lemma consistent_ok : forall G m, consistent G = Ok m -> models (val_of m) G.
Proof.
  intros G m H. unfold consistent in H. destruct (solve G) eqn:E; try discriminate H.
  injection H as <-. exact (solve_consistent _ _ E).
Qed.

Definition close_context (md : mode) (C R : list constr) : result cerror (list constr * model) :=
  match graph_of C with
  | None => Err (match find (fun c => negb (decomposable c)) C with Some c => CNotInFragment c | None => CUnknown end)
  | Some G0 =>
      let* m0 := consistent G0 in
      match md with
      | Rigid =>
          match find (fun r => negb (implied G0 r)) R with
          | Some r => Err (CNotImplied r (refute G0 r))
          | None => Ok (C, m0)
          end
      | Extensible =>
          let D := filter decomposable R in
          match graph_of D with
          | None => Err CUnknown
          | Some GD =>
              let* m := consistent (G0 ++ GD) in
              match find (fun r => negb (implied (G0 ++ GD) r)) R with
              | Some r => Err (CUnsupported r)
              | None => Ok (C ++ D, m)
              end
          end
      end
  end.

Lemma find_none_implied : forall G R, find (fun r => negb (implied G r)) R = None ->
  forall v, models v G -> Forall (csat v) R.
Proof.
  intros G R H v Hv. apply Forall_forall. intros r Hr.
  pose proof (find_none _ _ H r Hr) as E. apply negb_false_iff in E.
  exact (implied_sound G r E v Hv).
Qed.

Theorem close_context_sound : forall md C R ctx m, close_context md C R = Ok (ctx, m) ->
  Forall (csat (val_of m)) ctx /\
  (forall v, Forall (csat v) ctx -> Forall (csat v) C /\ Forall (csat v) R) /\
  (md = Rigid -> ctx = C).
Proof.
  intros md C R ctx m H. unfold close_context in H.
  destruct (graph_of C) as [G0|] eqn:EC; [ | discriminate H].
  destruct (consistent G0) as [m0|] eqn:E0; cbn in H; [ | discriminate H].
  destruct md.
  - destruct (find (fun r => negb (implied G0 r)) R) eqn:EF; [discriminate H | ].
    injection H as <- <-. split; [ | split; [ | reflexivity]].
    + apply (graph_of_sound C G0 EC). exact (consistent_ok _ _ E0).
    + intros v Hv. split; [exact Hv | ]. apply (find_none_implied G0); [exact EF | ].
      apply (graph_of_sound C G0 EC). exact Hv.
  - destruct (graph_of (filter decomposable R)) as [GD|] eqn:ED; [ | discriminate H].
    destruct (consistent (G0 ++ GD)) as [m1|] eqn:E1; cbn in H; [ | discriminate H].
    destruct (find (fun r => negb (implied (G0 ++ GD) r)) R) eqn:EF; [discriminate H | ].
    injection H as <- <-.
    assert (Hm : forall v, Forall (csat v) (C ++ filter decomposable R) -> models v (G0 ++ GD)).
    { intros v Hv. apply Forall_app in Hv as [H1 H2]. unfold models. apply Forall_app. split.
      - apply (graph_of_sound C G0 EC). exact H1.
      - apply (graph_of_sound _ GD ED). exact H2. }
    split; [ | split; [ | discriminate]].
    + pose proof (consistent_ok _ _ E1) as Hc. unfold models in Hc. apply Forall_app in Hc as [H1 H2].
      apply Forall_app. split; [apply (graph_of_sound C G0 EC) | apply (graph_of_sound _ GD ED)]; assumption.
    + intros v Hv. split; [apply Forall_app in Hv as [H1 _]; exact H1 | ].
      apply (find_none_implied (G0 ++ GD)); [exact EF | exact (Hm v Hv)].
Qed.
