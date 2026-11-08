(** * Levels of universes

    The milestone of universes (stage 7) is a separate mini-checker over
    its own small language (Universes/Term.v); the kernel of the lectures
    keeps its numeric [Type_i] and is not changed.  This file fixes the
    representation of levels before the graph of constraints.

    An atom is the level [0], a level variable [u] named by the user, or
    an instance variable [?n] made fresh for one reference to a
    polymorphic constant.  A level expression is the maximum of a list
    of atoms with offsets:

      ℓ ::= max (a₁ + k₁, …, aₙ + kₙ)      with  kᵢ ∈ ℕ

    and the empty list is [0].  The successor adds one to every offset
    and [max] concatenates, so the levels are closed under the axiom
    [Type ℓ : Type (ℓ+1)] and the rule [Π : Type (max ℓ₁ ℓ₂)].

    [lnorm] keeps the maximal elements in the structural order: [a + k]
    is below [a + k'] for [k ≤ k'], and [0 + k] is below every [a + k']
    with [k ≤ k'].  The normal form has at most one element per atom,
    and an element on [0] only above all the others; [max(u+1, u)] is
    [u+1].  It is proved to keep the value under every valuation.

    The value of a level under a valuation of the variables in ℕ is the
    maximum of its elements, [0] for the empty list. *)

From Stdlib Require Import String List Bool Arith Lia.
Import ListNotations.

Inductive atom : Type :=
| LZero : atom
| LVar : string -> atom
| LInst : nat -> atom.

Definition atom_eq_dec (a b : atom) : {a = b} + {a <> b}.
Proof. decide equality; [apply string_dec | apply Nat.eq_dec]. Defined.

Definition atom_eqb (a b : atom) : bool := if atom_eq_dec a b then true else false.

Lemma atom_eqb_eq : forall a b, atom_eqb a b = true <-> a = b.
Proof. intros a b. unfold atom_eqb. destruct (atom_eq_dec a b); split; congruence. Qed.

Definition level : Type := list (atom * nat).

Definition elem_eq_dec (x y : atom * nat) : {x = y} + {x <> y}.
Proof. decide equality; [apply Nat.eq_dec | apply atom_eq_dec]. Defined.

Definition elem_eqb (x y : atom * nat) : bool := if elem_eq_dec x y then true else false.

Definition lzero : level := [].
Definition lconst (n : nat) : level := match n with O => [] | _ => [(LZero, n)] end.
Definition lvar (u : string) : level := [(LVar u, 0)].
Definition linst (n : nat) : level := [(LInst n, 0)].

(** ** Values *)

Definition valuation : Type := atom -> nat.

Definition aval (v : valuation) (a : atom) : nat := match a with LZero => 0 | _ => v a end.

Definition eval_elem (v : valuation) (x : atom * nat) : nat := aval v (fst x) + snd x.

Definition leval (v : valuation) (l : level) : nat :=
  fold_right (fun x m => Nat.max (eval_elem v x) m) 0 l.

(** [elems] reads the empty list as its value [0 + 0]: the constraints
    decompose over a nonempty list. *)
Definition elems (l : level) : level := match l with [] => [(LZero, 0)] | _ => l end.

(** ** The structural order and the normal form *)

Definition dom (x y : atom * nat) : bool :=
  (atom_eqb (fst x) (fst y) || atom_eqb (fst x) LZero) && (snd x <=? snd y).

Definition maximal_in (l : level) (x : atom * nat) : bool :=
  forallb (fun y => implb (dom x y) (dom y x)) l.

Definition lnorm (l : level) : level :=
  let l1 := filter (fun x => negb (elem_eqb x (LZero, 0))) l in
  nodup elem_eq_dec (filter (maximal_in l1) l1).

Definition lplus (l : level) (n : nat) : level :=
  lnorm (map (fun x => (fst x, snd x + n)) (elems l)).
Definition lsucc (l : level) : level := lplus l 1.
Definition lmax (l1 l2 : level) : level := lnorm (l1 ++ l2).

(** Syntactic comparisons of normal forms: every element of the first
    is below an element of the second.  They are only shortcuts: a
    comparison they do not settle becomes a constraint. *)
Definition lle_syn (l1 l2 : level) : bool :=
  forallb (fun x => existsb (dom x) (lnorm l2)) (lnorm l1).
Definition lsame (l1 l2 : level) : bool := lle_syn l1 l2 && lle_syn l2 l1.

(** ** Laws *)

Lemma dom_sound : forall v x y, dom x y = true -> eval_elem v x <= eval_elem v y.
Proof.
  intros v [a k] [b m] H. unfold dom in H; cbn in H. apply andb_prop in H as [H1 H2].
  apply Nat.leb_le in H2. unfold eval_elem; cbn.
  apply orb_prop in H1 as [H1 | H1]; apply atom_eqb_eq in H1; subst; cbn; lia.
Qed.

Lemma dom_refl : forall x, dom x x = true.
Proof.
  intros [a k]. unfold dom; cbn. unfold atom_eqb. destruct (atom_eq_dec a a); [ | congruence].
  cbn. apply Nat.leb_le. lia.
Qed.

Lemma dom_trans : forall x y z, dom x y = true -> dom y z = true -> dom x z = true.
Proof.
  intros [a k] [b m] [c n] H1 H2. unfold dom in *; cbn in *.
  apply andb_prop in H1 as [A1 K1]. apply andb_prop in H2 as [A2 K2].
  apply Nat.leb_le in K1, K2. apply andb_true_intro; split; [ | apply Nat.leb_le; lia].
  apply orb_prop in A1 as [A1 | A1]; apply atom_eqb_eq in A1; subst;
  [ exact A2 | apply orb_true_intro; right; apply atom_eqb_eq; reflexivity ].
Qed.

Lemma leval_ge : forall v l x, In x l -> eval_elem v x <= leval v l.
Proof.
  intros v l x. induction l as [|y l IH]; intros H; [destruct H | ].
  change (leval v (y :: l)) with (Nat.max (eval_elem v y) (leval v l)).
  destruct H as [<- | H]; [lia | specialize (IH H); lia].
Qed.

Lemma leval_le : forall v l n, (forall x, In x l -> eval_elem v x <= n) -> leval v l <= n.
Proof.
  intros v l n. induction l as [|y l IH]; intros H; [cbn; lia | ].
  change (leval v (y :: l)) with (Nat.max (eval_elem v y) (leval v l)).
  apply Nat.max_lub; [apply H; left; reflexivity | apply IH; intros x Hx; apply H; right; exact Hx].
Qed.

Lemma leval_elems : forall v l, leval v (elems l) = leval v l.
Proof. intros v [|x l]; reflexivity. Qed.

Lemma leval_app : forall v l1 l2, leval v (l1 ++ l2) = Nat.max (leval v l1) (leval v l2).
Proof.
  intros v l1 l2. induction l1 as [|x l1 IH]; [change (leval v l2 = Nat.max 0 (leval v l2)); lia | ].
  change (Nat.max (eval_elem v x) (leval v (l1 ++ l2)) = Nat.max (Nat.max (eval_elem v x) (leval v l1)) (leval v l2)).
  rewrite IH; lia.
Qed.

(** Every element has a maximal element above it. *)
Lemma maximal_above : forall l x, exists y,
  In y (x :: l) /\ dom x y = true /\ forall z, In z (x :: l) -> dom y z = true -> dom z y = true.
Proof.
  induction l as [|h l IH]; intros x.
  - exists x. split; [left; reflexivity | split; [apply dom_refl | ]].
    intros z [<- | []] _. apply dom_refl.
  - destruct (dom x h) eqn:Exh.
    + destruct (IH h) as (y & Hy & Hhy & Hmax). exists y. split; [right; exact Hy | split].
      * exact (dom_trans _ _ _ Exh Hhy).
      * intros z [<- | Hz] Hyz; [ | exact (Hmax z Hz Hyz)].
        exact (dom_trans _ _ _ Exh Hhy).
    + destruct (IH x) as (y & Hy & Hxy & Hmax). exists y. split.
      { destruct Hy as [<- | Hy]; [left; reflexivity | right; right; exact Hy]. }
      split; [exact Hxy | ].
      intros z [<- | [<- | Hz]] Hyz.
      * apply Hmax; [left; reflexivity | exact Hyz].
      * rewrite (dom_trans _ _ _ Hxy Hyz) in Exh. discriminate.
      * apply Hmax; [right; exact Hz | exact Hyz].
Qed.

Theorem lnorm_sound : forall v l, leval v (lnorm l) = leval v l.
Proof.
  intros v l. unfold lnorm.
  set (l1 := filter (fun x => negb (elem_eqb x (LZero, 0))) l).
  apply Nat.le_antisymm.
  - apply leval_le. intros x Hx. apply nodup_In in Hx. apply filter_In in Hx as [Hx _].
    unfold l1 in Hx. apply filter_In in Hx as [Hx _]. exact (leval_ge v l x Hx).
  - apply leval_le. intros x Hx.
    destruct (elem_eqb x (LZero, 0)) eqn:Ez.
    { unfold elem_eqb in Ez. destruct (elem_eq_dec x (LZero, 0)) as [-> | ]; [ | discriminate].
      unfold eval_elem; cbn. lia. }
    assert (Hx1 : In x l1) by (apply filter_In; rewrite Ez; auto).
    destruct (maximal_above l1 x) as (y & Hy & Hxy & Hmax).
    assert (Hy1 : In y l1) by (destruct Hy as [<- | Hy]; auto).
    assert (Hm : maximal_in l1 y = true).
    { apply forallb_forall. intros z Hz. destruct (dom y z) eqn:E; [ | reflexivity].
      cbn. apply Hmax; [right; exact Hz | exact E]. }
    eapply Nat.le_trans; [exact (dom_sound v _ _ Hxy) | ].
    apply leval_ge. apply nodup_In. apply filter_In. auto.
Qed.

Lemma leval_shift : forall v l n, l <> [] ->
  leval v (map (fun x => (fst x, snd x + n)) l) = leval v l + n.
Proof.
  intros v l n. induction l as [|x l IH]; intros H; [congruence | ].
  destruct l as [|y l].
  - cbn. unfold eval_elem; cbn. lia.
  - change (Nat.max (eval_elem v (fst x, snd x + n)) (leval v (map (fun x => (fst x, snd x + n)) (y :: l)))
            = Nat.max (eval_elem v x) (leval v (y :: l)) + n).
    rewrite IH by discriminate. unfold eval_elem; cbn. lia.
Qed.

Theorem lplus_sound : forall v l n, leval v (lplus l n) = leval v l + n.
Proof.
  intros v l n. unfold lplus. rewrite lnorm_sound, leval_shift by (destruct l; discriminate).
  rewrite leval_elems. reflexivity.
Qed.

Corollary lsucc_sound : forall v l, leval v (lsucc l) = S (leval v l).
Proof. intros v l. unfold lsucc. rewrite lplus_sound. lia. Qed.

Theorem lmax_sound : forall v l1 l2, leval v (lmax l1 l2) = Nat.max (leval v l1) (leval v l2).
Proof. intros v l1 l2. unfold lmax. rewrite lnorm_sound. apply leval_app. Qed.

Theorem lle_syn_sound : forall v l1 l2, lle_syn l1 l2 = true -> leval v l1 <= leval v l2.
Proof.
  intros v l1 l2 H. rewrite <- (lnorm_sound v l1), <- (lnorm_sound v l2).
  apply leval_le. intros x Hx. unfold lle_syn in H. rewrite forallb_forall in H.
  apply H, existsb_exists in Hx as (y & Hy & Hxy).
  eapply Nat.le_trans; [exact (dom_sound v _ _ Hxy) | exact (leval_ge v _ y Hy)].
Qed.

(** ** Substitution of levels for atoms

    [σ] maps the variables of a polymorphic constant to the levels of an
    instance; the atoms it does not mention stay. *)
Definition lsubst_map : Type := list (atom * level).

Fixpoint lookup_atom (σ : lsubst_map) (a : atom) : option level :=
  match σ with
  | [] => None
  | (b, l) :: σ' => if atom_eqb a b then Some l else lookup_atom σ' a
  end.

Definition lsubst (σ : lsubst_map) (l : level) : level :=
  lnorm (flat_map (fun x => match lookup_atom σ (fst x) with
                            | Some l' => map (fun y => (fst y, snd y + snd x)) (elems l')
                            | None => [x]
                            end) l).

Definition atoms_of (l : level) : list atom := map fst l.
