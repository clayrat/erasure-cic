(** * Observable results

    The contract of erasure compares the result of a source program with
    the result of its erasure at an observable type, an explicit class of
    first-order data:
    - Bool and Unit of the minimal MLTT;
    - ℕ, lists and vectors of the lectures, with their declarations, ℕ
      among them for vectors, whose lengths are observed;
    - pairs of observable components, and pairs of an observable witness
      and a proof in Prop.
    Functions, arbitrary families and W-trees with functional fields are
    used inside programs, but their results are not compared.

    [value_observation T v w] relates a source value [v] of type [T] and
    an erased value [w]: the constructors are the same, the fields of
    data are related at their types, and the parameters of a list or a
    vector and the proof of a witness pair are ignored, where [w] may
    have anything, [□] included.  [□] is accepted nowhere else.

    [observes] decides the relation for a budget, and is sound for it. *)

From Stdlib Require Import String List Bool Arith Relations.
Import ListNotations.
From DepTypes.Common Require Import Result Traced.
From DepTypes.PTS Require Import Syntax Spec Signature Reduction NormalOrder Eval Bidir Check CheckSound.
From DepTypes.Configs Require Import Predicative.
From DepTypes.MLTT Require Import Constants Families.
From IndTypes.Data Require Import Lists.
From CIC.Erasure Require Import Target.

Local Open Scope string_scope.

Definition NatT : term := Const (Ind "Nat").
Definition ListT (A : term) : term := App (Const (Ind "List")) A.
Definition VecT (A n : term) : term := App (App (Const (Ind "Vec")) A) n.

Section Observe.
  Variable sg : signature.
  Local Notation "t ⇝* u" := (red sg t u).

  Inductive Observable : term -> Prop :=
  | O_Bool : forall T, T ⇝* Bool -> Observable T
  | O_Unit : forall T, T ⇝* Unit -> Observable T
  | O_Nat : forall T, T ⇝* NatT -> sig_ind sg "Nat" = Some nat_desc -> Observable T
  | O_List : forall T A, T ⇝* ListT A -> sig_ind sg "List" = Some list_desc -> Observable A -> Observable T
  | O_Vec : forall T A n, T ⇝* VecT A n -> sig_ind sg "Vec" = Some vec_desc -> sig_ind sg "Nat" = Some nat_desc ->
      Observable A -> Observable T
  | O_Pair : forall T A B, T ⇝* Sigma A B -> Observable A -> (forall a, Observable (subst1 B a)) -> Observable T
  | O_Witness : forall T A B K, T ⇝* Sigma A B -> Observable A ->
      synth predicative_prop sg [A] B K -> K ⇝* Srt Prp -> Observable T.

  Inductive value_observation : term -> term -> eterm -> Prop :=
  | VO_True : forall T, T ⇝* Bool -> value_observation T BTrue (ECtor prim_bool "true")
  | VO_False : forall T, T ⇝* Bool -> value_observation T BFalse (ECtor prim_bool "false")
  | VO_Tt : forall T, T ⇝* Unit -> value_observation T Tt (ECtor prim_unit "tt")
  | VO_Zero : forall T, T ⇝* NatT ->
      value_observation T (Const (Ctor "Nat" "zero")) (ECtor "Nat" "zero")
  | VO_Succ : forall T v w, T ⇝* NatT -> value_observation NatT v w ->
      value_observation T (App (Const (Ctor "Nat" "succ")) v) (EApp (ECtor "Nat" "succ") w)
  | VO_Nil : forall T A A' wA, T ⇝* ListT A ->
      value_observation T (App (Const (Ctor "List" "nil")) A') (EApp (ECtor "List" "nil") wA)
  | VO_Cons : forall T A A' wA x wx xs wxs, T ⇝* ListT A ->
      value_observation A x wx -> value_observation (ListT A) xs wxs ->
      value_observation T (apps (Const (Ctor "List" "cons")) [A'; x; xs])
                          (eapps (ECtor "List" "cons") [wA; wx; wxs])
  | VO_VNil : forall T A n A' wA, T ⇝* VecT A n ->
      value_observation T (App (Const (Ctor "Vec" "nil")) A') (EApp (ECtor "Vec" "nil") wA)
  | VO_VCons : forall T A n A' wA k wk x wx xs wxs, T ⇝* VecT A n ->
      value_observation NatT k wk -> value_observation A x wx -> value_observation (VecT A k) xs wxs ->
      value_observation T (apps (Const (Ctor "Vec" "cons")) [A'; k; x; xs])
                          (eapps (ECtor "Vec" "cons") [wA; wk; wx; wxs])
  | VO_Pair : forall T A B a wa b wb, T ⇝* Sigma A B ->
      value_observation A a wa -> value_observation (subst1 B a) b wb ->
      value_observation T (Pair a b) (EPair wa wb)
  | VO_Witness : forall T A B K a wa p wp, T ⇝* Sigma A B ->
      synth predicative_prop sg [A] B K -> K ⇝* Srt Prp ->
      value_observation A a wa -> value_observation T (Pair a p) (EPair wa wp).

  (** ** A decision for a budget *)

  Variable fuel : nat.

  Definition tag (D c : string) : term := Const (Ctor D c).

  (** [B] is a family of propositions over [A]. *)
  Definition prop_family (A B : term) : option term :=
    match snd (run_infer predicative_prop sg fuel [A] B) with
    | Accepted K => match whnf sg fuel K with HeadForm (Srt Prp) => Some K | _ => None end
    | _ => None
    end.

  (** The shapes of the observable types. *)
  Inductive tshape : Type :=
  | TBool | TUnit | TNat | TList (A : term) | TVec (A n : term) | TSigma (A B : term) | TOther.

  Definition classify_type (V : term) : tshape :=
    match V with
    | Bool => TBool
    | Unit => TUnit
    | Sigma A B => TSigma A B
    | Const (Ind D) => if String.eqb D "Nat" then TNat else TOther
    | App (Const (Ind D)) A => if String.eqb D "List" then TList A else TOther
    | App (App (Const (Ind D)) A) n => if String.eqb D "Vec" then TVec A n else TOther
    | _ => TOther
    end.

  Definition is_tag (D c : string) (D' c' : string) : bool := String.eqb D' D && String.eqb c' c.

  Fixpoint observes (n : nat) (T v : term) (w : eterm) : bool :=
    match n with
    | O => false
    | S n' =>
        match whnf sg fuel T with
        | HeadOutOfFuel _ => false
        | HeadForm V =>
            match classify_type V, v, w with
            | TBool, BTrue, ECtor D c => is_tag prim_bool "true" D c
            | TBool, BFalse, ECtor D c => is_tag prim_bool "false" D c
            | TUnit, Tt, ECtor D c => is_tag prim_unit "tt" D c
            | TNat, Const (Ctor D c), ECtor D' c' => is_tag "Nat" "zero" D c && is_tag "Nat" "zero" D' c'
            | TNat, App (Const (Ctor D c)) k, EApp (ECtor D' c') wk =>
                is_tag "Nat" "succ" D c && is_tag "Nat" "succ" D' c' && observes n' NatT k wk
            | TList _, App (Const (Ctor D c)) _, EApp (ECtor D' c') _ =>
                is_tag "List" "nil" D c && is_tag "List" "nil" D' c'
            | TList A, App (App (App (Const (Ctor D c)) _) x) xs, EApp (EApp (EApp (ECtor D' c') _) wx) wxs =>
                is_tag "List" "cons" D c && is_tag "List" "cons" D' c' &&
                observes n' A x wx && observes n' (ListT A) xs wxs
            | TVec _ _, App (Const (Ctor D c)) _, EApp (ECtor D' c') _ =>
                is_tag "Vec" "nil" D c && is_tag "Vec" "nil" D' c'
            | TVec A _, App (App (App (App (Const (Ctor D c)) _) k) x) xs,
              EApp (EApp (EApp (EApp (ECtor D' c') _) wk) wx) wxs =>
                is_tag "Vec" "cons" D c && is_tag "Vec" "cons" D' c' &&
                observes n' NatT k wk && observes n' A x wx && observes n' (VecT A k) xs wxs
            | TSigma A B, Pair a b, EPair wa wb =>
                observes n' A a wa &&
                match prop_family A B with
                | Some _ => true
                | None => observes n' (subst1 B a) b wb
                end
            | _, _, _ => false
            end
        end
    end.

  (** ** Soundness *)

  Lemma prop_family_sound : forall A B K, prop_family A B = Some K ->
    synth predicative_prop sg [A] B K /\ K ⇝* Srt Prp.
  Proof.
    intros A B K H. unfold prop_family in H.
    destruct (snd (run_infer predicative_prop sg fuel [A] B)) as [K'| |] eqn:E; try discriminate H.
    destruct (whnf sg fuel K') as [V|] eqn:W; try discriminate H.
    destruct V; try discriminate H. destruct s; try discriminate H. injection H as <-.
    split; [exact (proj2 (run_infer_sound _ _ _ _ _ _ E)) | exact (whnf_red sg fuel _ _ W)].
  Qed.

  Lemma classify_type_spec : forall V,
    match classify_type V with
    | TBool => V = Bool
    | TUnit => V = Unit
    | TNat => V = NatT
    | TList A => V = ListT A
    | TVec A n => V = VecT A n
    | TSigma A B => V = Sigma A B
    | TOther => True
    end.
  Proof.
    intros V. destruct V; cbn; try reflexivity; try exact I.
    - destruct V1; try exact I.
      + destruct V1_1; try exact I. destruct g; try exact I.
        destruct (String.eqb s "Vec") eqn:E; [apply String.eqb_eq in E; subst; reflexivity | exact I].
      + destruct g; try exact I.
        destruct (String.eqb s "List") eqn:E; [apply String.eqb_eq in E; subst; reflexivity | exact I].
    - destruct g; try exact I.
      destruct (String.eqb s "Nat") eqn:E; [apply String.eqb_eq in E; subst; reflexivity | exact I].
  Qed.

  Lemma is_tag_eq : forall D c D' c', is_tag D c D' c' = true -> D' = D /\ c' = c.
  Proof.
    intros D c D' c' H. unfold is_tag in H. apply andb_prop in H as [H1 H2].
    apply String.eqb_eq in H1. apply String.eqb_eq in H2. auto.
  Qed.

  Theorem observes_sound : forall n T v w, observes n T v w = true -> value_observation T v w.
  Proof.
    induction n as [|n IH]; intros T v w H; [discriminate H | ]. cbn [observes] in H.
    destruct (whnf sg fuel T) as [V|] eqn:W; [ | discriminate H].
    apply (whnf_red sg fuel) in W. pose proof (classify_type_spec V) as Hs.
    destruct (classify_type V) as [ | | | A | A m | A B | ]; try subst V.
    all: repeat match type of H with
         | match ?x with _ => _ end = true => destruct x; try discriminate H
         end.
    all: repeat match goal with
         | H : _ && _ = true |- _ => apply andb_prop in H as [? ?]
         | H : is_tag _ _ _ _ = true |- _ => apply is_tag_eq in H as [? ?]; subst
         end.
    all: try discriminate.
    all: try match goal with
         | H0 : match prop_family ?A ?B with _ => _ end = true |- _ =>
             let E := fresh "E" in destruct (prop_family A B) eqn:E
         end.
    all: first
      [ solve [constructor; exact W]
      | apply VO_Succ; [exact W | apply IH; assumption]
      | eapply VO_Cons; [exact W | apply IH; assumption | apply IH; assumption]
      | eapply VO_VCons; [exact W | apply IH; assumption | apply IH; assumption | apply IH; assumption]
      | eapply VO_Nil; exact W
      | eapply VO_VNil; exact W
      | match goal with
        | E : prop_family _ _ = Some _ |- _ =>
            destruct (prop_family_sound _ _ _ E) as [Hk Hp];
            eapply VO_Witness; [exact W | exact Hk | exact Hp | apply IH; assumption]
        end
      | eapply VO_Pair; [exact W | apply IH; assumption | apply IH; assumption] ].
  Qed.
End Observe.
