(** * The language of the milestone

    A small language with sorts [Type ℓ] at level expressions, enough for
    the checks of the plan and nothing more:
    - Π, unannotated λ, application, annotation, de Bruijn variables;
    - global δ-constants with an instance of levels, [c@{ℓ₁ … ℓₙ}];
    - ℕ with [zero], [succ] and the eliminator [elimNat@{ℓ}] into
      [Type ℓ], the history of [isEven] of lecture 7 needing it;
    - Unit with [tt] in [Type 0];
    - Σ with pairs and projections.
    Prop is not in this fragment: the milestone is about the levels of
    [Type].

    A polymorphic constant is stored with its universe context: the
    variables it is abstracted over and its constraints.  An instance
    substitutes levels for the variables, in its type, its body and its
    constraints.

    Reduction is weak head: β, δ (unfolding a constant at its instance),
    ι of [elimNat] on [zero] and [succ], projections of a pair, and the
    annotation dropped.  Fuel bounds it; [None] is running out. *)

From Stdlib Require Import String List Bool Arith.
Import ListNotations.
From CIC.Universes Require Import Level Constraints.

Inductive uterm : Type :=
| UVar : nat -> uterm
| USort : level -> uterm
| UPi : uterm -> uterm -> uterm
| ULam : uterm -> uterm
| UApp : uterm -> uterm -> uterm
| UAnn : uterm -> uterm -> uterm
| UConst : string -> list level -> uterm
| UNat : uterm
| UZero : uterm
| USucc : uterm
| UElimNat : level -> uterm
| UUnit : uterm
| UTt : uterm
| USigma : uterm -> uterm -> uterm
| UPair : uterm -> uterm -> uterm
| UFst : uterm -> uterm
| USnd : uterm -> uterm.

(** ** De Bruijn *)

Fixpoint ulift (d k : nat) (t : uterm) : uterm :=
  match t with
  | UVar n => if n <? k then UVar n else UVar (n + d)
  | UPi A B => UPi (ulift d k A) (ulift d (S k) B)
  | ULam b => ULam (ulift d (S k) b)
  | UApp f a => UApp (ulift d k f) (ulift d k a)
  | UAnn t A => UAnn (ulift d k t) (ulift d k A)
  | USigma A B => USigma (ulift d k A) (ulift d (S k) B)
  | UPair a b => UPair (ulift d k a) (ulift d k b)
  | UFst p => UFst (ulift d k p)
  | USnd p => USnd (ulift d k p)
  | t => t
  end.

Fixpoint usubst (k : nat) (u t : uterm) : uterm :=
  match t with
  | UVar n => if n =? k then ulift k 0 u else if k <? n then UVar (pred n) else UVar n
  | UPi A B => UPi (usubst k u A) (usubst (S k) u B)
  | ULam b => ULam (usubst (S k) u b)
  | UApp f a => UApp (usubst k u f) (usubst k u a)
  | UAnn t A => UAnn (usubst k u t) (usubst k u A)
  | USigma A B => USigma (usubst k u A) (usubst (S k) u B)
  | UPair a b => UPair (usubst k u a) (usubst k u b)
  | UFst p => UFst (usubst k u p)
  | USnd p => USnd (usubst k u p)
  | t => t
  end.

Definition usubst1 (b u : uterm) : uterm := usubst 0 u b.

Definition arrow (A B : uterm) : uterm := UPi A (ulift 1 0 B).

Fixpoint uapps (f : uterm) (args : list uterm) : uterm :=
  match args with [] => f | a :: args' => uapps (UApp f a) args' end.

(** ** Levels in terms *)

Fixpoint ulsubst (σ : lsubst_map) (t : uterm) : uterm :=
  match t with
  | USort l => USort (lsubst σ l)
  | UElimNat l => UElimNat (lsubst σ l)
  | UConst c inst => UConst c (map (lsubst σ) inst)
  | UPi A B => UPi (ulsubst σ A) (ulsubst σ B)
  | ULam b => ULam (ulsubst σ b)
  | UApp f a => UApp (ulsubst σ f) (ulsubst σ a)
  | UAnn t A => UAnn (ulsubst σ t) (ulsubst σ A)
  | USigma A B => USigma (ulsubst σ A) (ulsubst σ B)
  | UPair a b => UPair (ulsubst σ a) (ulsubst σ b)
  | UFst p => UFst (ulsubst σ p)
  | USnd p => USnd (ulsubst σ p)
  | t => t
  end.

(** The type of [elimNat@{ℓ}]:
    Π(P : ℕ → Type ℓ). P 0 → (Π n. P n → P (succ n)) → Π n. P n. *)
Definition elimnat_type (l : level) : uterm :=
  UPi (UPi UNat (USort l))
    (UPi (UApp (UVar 0) UZero)
      (UPi (UPi UNat (UPi (UApp (UVar 2) (UVar 0)) (UApp (UVar 3) (UApp USucc (UVar 1)))))
        (UPi UNat (UApp (UVar 3) (UVar 0))))).

(** ** Polymorphic constants *)

Record udef : Type := UDef {
  ud_name : string;
  ud_univs : list atom;          (** the variables of the context *)
  ud_cstrs : list constr;        (** the constraints of the context *)
  ud_type : uterm;
  ud_body : uterm;
}.

Definition usig : Type := list udef.

Fixpoint ulookup (sg : usig) (c : string) : option udef :=
  match sg with
  | [] => None
  | d :: sg' => if String.eqb (ud_name d) c then Some d else ulookup sg' c
  end.

Definition inst_map (d : udef) (inst : list level) : lsubst_map := combine (ud_univs d) inst.

Definition unfold_const (sg : usig) (c : string) (inst : list level) : option uterm :=
  match ulookup sg c with
  | Some d => if length inst =? length (ud_univs d) then Some (ulsubst (inst_map d inst) (ud_body d)) else None
  | None => None
  end.

(** ** Weak head reduction *)

Section Whnf.
  Variable sg : usig.

  Fixpoint whnf (fuel : nat) (t : uterm) : option uterm :=
    match fuel with
    | O => None
    | S f =>
        match t with
        | UApp g a =>
            match whnf f g with
            | None => None
            | Some (ULam b) => whnf f (usubst1 b a)
            | Some (UApp (UApp (UApp (UElimNat l) P) z) s as g') =>
                match whnf f a with
                | None => None
                | Some UZero => whnf f z
                | Some (UApp USucc n) => whnf f (UApp (UApp s n) (UApp g' n))
                | Some a' => Some (UApp g' a')
                end
            | Some g' => Some (UApp g' a)
            end
        | UAnn t' _ => whnf f t'
        | UConst c inst =>
            match unfold_const sg c inst with Some b => whnf f b | None => Some t end
        | UFst p =>
            match whnf f p with
            | None => None
            | Some (UPair a _) => whnf f a
            | Some p' => Some (UFst p')
            end
        | USnd p =>
            match whnf f p with
            | None => None
            | Some (UPair _ b) => whnf f b
            | Some p' => Some (USnd p')
            end
        | _ => Some t
        end
    end.
End Whnf.
