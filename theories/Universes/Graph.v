(** * The graph of constraints

    An edge [(a, w, b)] with [w ∈ ℤ] is the difference constraint

      a + w ≤ b

    [u ≤ v] is the edge [(u, 0, v)], [u < v] is [(u, 1, v)]; an edge with
    another weight comes from a constraint with offsets.  A valuation of
    the variables in ℕ is a model of a graph if it satisfies every edge;
    the atom [0] has the value [0], and every atom is at least [0], so
    the base edges [(0, 0, a)] hold in every model.

    A graph has a model iff it has no cycle of positive weight: a cycle
    of non-strict edges ([u ≤ v ≤ u]) has weight [0] and is allowed, a
    cycle with a strict edge ([u < v ≤ u]) has weight [1] and is not.
    [solve] runs Bellman–Ford for the longest paths, from a source at
    distance [0] from every node, with the base edges added:
    - if no edge is violated after [|V|] rounds, the distances relative to
      [0] are a model;
    - otherwise the predecessors of the violated edge lead to a cycle.
    Either answer is a certificate checked before it is returned: the
    model against every edge ([check_model]), the cycle as a closed chain
    of edges of the graph with a positive sum ([cycle_ok]).  Both checks
    are proved sound, so [Consistent] and [Cycle] are proved answers
    whatever the algorithm did; [Unknown], a certificate that does not
    check, is the third answer, and that it never happens is the open
    obligation [graph_solve_complete] of Contracts.v.

    Entailment reduces to it: [a + w ≤ b] holds in every model of [G]
    iff [G] with the negation [b + (1 - w) ≤ a] has no model.  A cycle is
    then a proof of the entailment, a model is a counter-model. *)

From Stdlib Require Import String List Bool Arith ZArith Lia.
Import ListNotations.
From CIC.Universes Require Import Level.

Local Open Scope Z_scope.

Definition edge : Type := (atom * Z * atom)%type.

Definition e_src (e : edge) : atom := let '(a, _, _) := e in a.
Definition e_w (e : edge) : Z := let '(_, w, _) := e in w.
Definition e_dst (e : edge) : atom := let '(_, _, b) := e in b.

Definition edge_eq_dec (e f : edge) : {e = f} + {e <> f}.
Proof.
  destruct e as [[a w] b], f as [[a' w'] b'].
  destruct (atom_eq_dec a a'), (Z.eq_dec w w'), (atom_eq_dec b b'); subst;
  first [left; reflexivity | right; congruence].
Defined.

Definition edge_sat (v : valuation) (e : edge) : Prop :=
  Z.of_nat (aval v (e_src e)) + e_w e <= Z.of_nat (aval v (e_dst e)).

Definition edge_satb (v : valuation) (e : edge) : bool :=
  Z.of_nat (aval v (e_src e)) + e_w e <=? Z.of_nat (aval v (e_dst e)).

Lemma edge_satb_sat : forall v e, edge_satb v e = true <-> edge_sat v e.
Proof. intros v e. unfold edge_satb, edge_sat. apply Z.leb_le. Qed.

Definition models (v : valuation) (G : list edge) : Prop := Forall (edge_sat v) G.

(** ** Nodes and base edges *)

Definition nodes (G : list edge) : list atom :=
  nodup atom_eq_dec (LZero :: flat_map (fun e => [e_src e; e_dst e]) G).

Definition base (G : list edge) : list edge := map (fun x => (LZero, 0, x)) (nodes G).

Definition relaxed (G : list edge) : list edge := base G ++ G.

Lemma aval_zero : forall v, aval v LZero = 0%nat.
Proof. reflexivity. Qed.

Lemma models_relaxed : forall v G, models v G -> models v (relaxed G).
Proof.
  intros v G H. apply Forall_app. split; [ | exact H].
  apply Forall_forall. intros e He. unfold base in He. apply in_map_iff in He as (x & <- & _).
  unfold edge_sat; cbn. lia.
Qed.

(** ** Models *)

Definition model : Type := list (atom * nat).

Definition val_of (m : model) : valuation :=
  fun a => match find (fun p => atom_eqb (fst p) a) m with Some (_, n) => n | None => O end.

Definition check_model (G : list edge) (m : model) : bool := forallb (edge_satb (val_of m)) G.

Lemma check_model_sound : forall G m, check_model G m = true -> models (val_of m) G.
Proof.
  intros G m H. apply Forall_forall. intros e He. unfold check_model in H.
  rewrite forallb_forall in H. apply edge_satb_sat, H, He.
Qed.

(** ** Cycles *)

Fixpoint chain_ok (x : atom) (c : list edge) (y : atom) : bool :=
  match c with
  | [] => atom_eqb x y
  | e :: c' => atom_eqb x (e_src e) && chain_ok (e_dst e) c' y
  end.

Definition weight (c : list edge) : Z := fold_right (fun e z => e_w e + z) 0 c.

Definition mem_edge (G : list edge) (e : edge) : bool :=
  existsb (fun f => if edge_eq_dec e f then true else false) G.

Definition cycle_ok (G : list edge) (c : list edge) : bool :=
  match c with
  | [] => false
  | e :: _ => chain_ok (e_src e) c (e_src e) && (0 <? weight c) && forallb (mem_edge (relaxed G)) c
  end.

Lemma chain_ok_sum : forall v c x y, chain_ok x c y = true -> Forall (edge_sat v) c ->
  Z.of_nat (aval v x) + weight c <= Z.of_nat (aval v y).
Proof.
  intros v c. induction c as [|e c IH]; intros x y H Hs; cbn in H.
  - apply atom_eqb_eq in H. subst. cbn. lia.
  - apply andb_prop in H as [H1 H2]. apply atom_eqb_eq in H1. subst.
    inversion Hs as [|? ? He Hc]; subst. specialize (IH _ _ H2 Hc).
    unfold edge_sat in He. change (weight (e :: c)) with (e_w e + weight c). lia.
Qed.

Theorem cycle_ok_sound : forall G c, cycle_ok G c = true -> forall v, ~ models v G.
Proof.
  intros G c H v Hv. destruct c as [|e c']; [discriminate H | ].
  unfold cycle_ok in H. apply andb_prop in H as [H Hm]. apply andb_prop in H as [Hc Hw].
  apply Z.ltb_lt in Hw.
  assert (Hs : Forall (edge_sat v) (e :: c')).
  { apply Forall_forall. intros f Hf. rewrite forallb_forall in Hm. specialize (Hm f Hf).
    unfold mem_edge in Hm. apply existsb_exists in Hm as (g & Hg & Heq).
    destruct (edge_eq_dec f g) as [-> | ]; [ | discriminate Heq].
    pose proof (models_relaxed v G Hv) as Hr. unfold models in Hr. rewrite Forall_forall in Hr. exact (Hr g Hg). }
  pose proof (chain_ok_sum v _ _ _ Hc Hs). lia.
Qed.

(** ** Bellman–Ford for the longest paths *)

Definition dists : Type := list (atom * Z).
Definition preds : Type := list (atom * edge).

Fixpoint dget (d : dists) (a : atom) : Z :=
  match d with [] => 0 | (b, z) :: d' => if atom_eqb a b then z else dget d' a end.

Fixpoint pget (p : preds) (a : atom) : option edge :=
  match p with [] => None | (b, e) :: p' => if atom_eqb a b then Some e else pget p' a end.

Definition violated (d : dists) (e : edge) : bool := dget d (e_dst e) <? dget d (e_src e) + e_w e.

Definition relax_one (st : dists * preds) (e : edge) : dists * preds :=
  let (d, p) := st in
  if violated d e then ((e_dst e, dget d (e_src e) + e_w e) :: d, (e_dst e, e) :: p) else st.

Fixpoint rounds (n : nat) (es : list edge) (st : dists * preds) : dists * preds :=
  match n with
  | O => st
  | S n' => rounds n' es (fold_left relax_one es st)
  end.

(** [walk] goes [n] steps back along the predecessors; [collect] then
    gathers the cycle through the node reached, in the order of the
    edges. *)
Fixpoint walk (p : preds) (n : nat) (x : atom) : atom :=
  match n with
  | O => x
  | S n' => match pget p x with Some e => walk p n' (e_src e) | None => x end
  end.

Fixpoint collect (p : preds) (n : nat) (x y : atom) (acc : list edge) : option (list edge) :=
  match n with
  | O => None
  | S n' =>
      match pget p y with
      | None => None
      | Some e => if atom_eqb (e_src e) x then Some (e :: acc) else collect p n' x (e_src e) (e :: acc)
      end
  end.

Inductive verdict : Type :=
| Consistent : model -> verdict
| Cycle : list edge -> verdict
| Unknown : verdict.

Definition solve (G : list edge) : verdict :=
  let es := relaxed G in
  let n := length (nodes G) in
  let (d, p) := rounds n es ([], []) in
  match find (violated d) es with
  | None =>
      let m := map (fun x => (x, Z.to_nat (dget d x - dget d LZero))) (nodes G) in
      if check_model G m then Consistent m else Unknown
  | Some e =>
      let p' := (e_dst e, e) :: p in
      let x := walk p' n (e_dst e) in
      match collect p' (S n) x x [] with
      | Some c => if cycle_ok G c then Cycle c else Unknown
      | None => Unknown
      end
  end.

Theorem solve_consistent : forall G m, solve G = Consistent m -> models (val_of m) G.
Proof.
  intros G m H. unfold solve in H.
  destruct (rounds _ _ _) as [d p].
  destruct (find (violated d) (relaxed G)) as [e|].
  - destruct (collect _ _ _ _ _) as [c|]; [ | discriminate H].
    destruct (cycle_ok G c); discriminate H.
  - match type of H with (if check_model G ?m0 then _ else _) = _ => destruct (check_model G m0) eqn:E end;
      [ | discriminate H].
    injection H as <-. exact (check_model_sound _ _ E).
Qed.

Theorem solve_cycle : forall G c, solve G = Cycle c -> forall v, ~ models v G.
Proof.
  intros G c H. unfold solve in H.
  destruct (rounds _ _ _) as [d p].
  destruct (find (violated d) (relaxed G)) as [e|].
  - destruct (collect _ _ _ _ _) as [c'|]; [ | discriminate H].
    destruct (cycle_ok G c') eqn:E; [ | discriminate H].
    injection H as <-. exact (cycle_ok_sound _ _ E).
  - match type of H with (if ?b then _ else _) = _ => destruct b end; discriminate H.
Qed.

(** ** Entailment *)

Definition negate (e : edge) : edge := (e_dst e, 1 - e_w e, e_src e).

Inductive entailment : Type :=
| Entailed : list edge -> entailment   (** the cycle of the graph with the negation *)
| Refuted : model -> entailment        (** a model of the graph violating the edge *)
| EUnknown : entailment.

Definition entails (G : list edge) (e : edge) : entailment :=
  match solve (negate e :: G) with
  | Cycle c => Entailed c
  | Consistent m => Refuted m
  | Unknown => EUnknown
  end.

Definition entailed (G : list edge) (e : edge) : bool :=
  match entails G e with Entailed _ => true | _ => false end.

Theorem entails_entailed : forall G e c, entails G e = Entailed c ->
  forall v, models v G -> edge_sat v e.
Proof.
  intros G e c H v Hv. unfold entails in H.
  destruct (solve (negate e :: G)) eqn:E; try discriminate H.
  pose proof (solve_cycle _ _ E v) as Hn. unfold edge_sat in *.
  destruct (Z_le_gt_dec (Z.of_nat (aval v (e_src e)) + e_w e) (Z.of_nat (aval v (e_dst e)))) as [Hle | Hgt];
    [exact Hle | ].
  exfalso. apply Hn. constructor; [ | exact Hv].
  unfold edge_sat, negate; cbn [e_src e_w e_dst]. lia.
Qed.

Theorem entails_refuted : forall G e m, entails G e = Refuted m ->
  models (val_of m) G /\ ~ edge_sat (val_of m) e.
Proof.
  intros G e m H. unfold entails in H.
  destruct (solve (negate e :: G)) eqn:E; try discriminate H. injection H as <-.
  pose proof (solve_consistent _ _ E) as Hm. inversion Hm as [|? ? Hn HG]; subst.
  split; [exact HG | ]. unfold edge_sat, negate in *; cbn [e_src e_w e_dst] in Hn. lia.
Qed.

Corollary entailed_sound : forall G e, entailed G e = true -> forall v, models v G -> edge_sat v e.
Proof.
  intros G e H. unfold entailed in H. destruct (entails G e) eqn:E; try discriminate H.
  exact (entails_entailed _ _ _ E).
Qed.
