(** * The relation of erasure

    [erases S sg Γ t T e]: in the context [Γ], the term [t] of type [T]
    erases to [e].  It is the relation against which the function
    [erase] of Erase.v is to be proved sound, and the one the simulation
    is stated for, after the relation [erases] of MetaCoq
    ([MetaCoq 2020], Contracts.v): a relation is closed under
    substitution and reduction where the function is not.  [erase] asks
    the checker for the type of every function it meets, so it fails on
    the reducts of a checked program, which need not check
    (Contracts.v, [annotated_preservation_fails]).

    The relation differs from that of MetaCoq in two ways.
    - It is directed by the type, as [erase] is.  A λ of the kernel
      carries no domain, and one λ may be a function on data and a
      function on proofs: [λx. x] has the type [Bool → Bool] and the type
      [P → P] for a proposition [P].  Whether its variable is erasable
      depends on the type it is used at.
    - Every rule repeats a typing rule of PTS.Typing, with [has_type] for
      the subterms that disappear (types, motives, the domains of
      binders) and [erases] for the others, so that a derivation of
      [erases] is a typing derivation of [t] at [T] with an erasure for
      every computational subterm ([erases_typed]).  One λ is thus used
      at one type throughout a derivation, the type of the application
      that consumes it.

    The rules:
    - [□] for a term whose type is erasable ([erasable_at]): convertible
      to an arity, or to a type in Prop.  Erasability is taken up to
      conversion because the sort of a type is not known to be unique
      (a λ carries no domain), so that [□] survives the conversions of a
      derivation.  As in MetaCoq, the other rules apply to erasable
      terms too: a derivation may keep the structure of a proof or of a
      type, as long as it types;
    - a conversion of the type, as [T_Conv];
    - variables, the constants of the signature (δ-constants,
      constructors, eliminator instances) and the constructors of the
      primitives, at their typing.  An instance into Prop is a proof,
      erased by [□] only: the erased evaluator does not compute it;
    - λ at a Π, an application at the codomain instantiated by the
      argument, an annotation dropped, pairs, projections;
    - an argument of an eliminator instance at the position of an index
      erased to [□], whatever its type: the erased ι passes [□] for the
      indices in the hypotheses of recursive fields, since the erased
      description does not keep them, and never reads an index;
    - the eliminators of Unit, Bool and Void as matches on the
      primitives of the target;
    - a match on data, a match on a proposition without constructors
      (kept, without branches), and a match on a singleton proposition
      eliminated into any sort: its only branch applied to [□] for each
      field, the scrutinee dropped.  A proposition eliminated into Prop
      only has no informative match: such a match is a proof, erased
      by [□];
    - a [fix] without its type. *)

From Stdlib Require Import String List.
Import ListNotations.
From DepTypes.Common Require Import Result.
From DepTypes.PTS Require Import Syntax Spec Signature Reduction Guard Typing.
From CIC.Erasure Require Import Target Erase.

Section Relation.
  Variable S : spec.
  Variable sg : signature.
  Local Notation "t ≡ u" := (conv sg t u).
  Local Notation typed := (has_type S sg).

  (** A term of type [T] in [Γ] is a type or a family of types ([T] an
      arity), or a proof ([T] in Prop), up to conversion of [T]. *)
  Definition erasable_at (G : ctx) (T : term) : Prop :=
    exists T', T ≡ T' /\ (arity sg T' \/ typed G T' (Srt Prp)).

  (** [f] is an eliminator instance applied up to an index: past its
      parameters, motive and methods, before its object. *)
  Definition index_position (f : term) : Prop :=
    exists D s d, spine_head f = Const (Elim D s) /\ sig_ind sg D = Some d /\
      length (ind_params d) + 1 + length (ind_ctors d) <= length (spine_args f) /\
      length (spine_args f) < length (ind_params d) + 1 + length (ind_ctors d) + length (ind_indices d).

  Inductive erases : ctx -> term -> term -> eterm -> Prop :=
  | X_Box : forall G t T,
      typed G t T -> erasable_at G T ->
      erases G t T EBox
  | X_Conv : forall G t A B s e,
      erases G t A e -> typed G B (Srt s) -> A ≡ B ->
      erases G t B e
  | X_Var : forall G n T,
      typed G (Var n) T ->
      erases G (Var n) T (EVar n)
  | X_Lam : forall G A B b s b',
      erases (A :: G) b B b' -> typed G (Pi A B) (Srt s) ->
      erases G (Lam b) (Pi A B) (ELam b')
  | X_App : forall G f u A B f' u',
      erases G f (Pi A B) f' -> erases G u A u' ->
      erases G (App f u) (subst1 B u) (EApp f' u')
  | X_AppIndex : forall G f u A B f',
      erases G f (Pi A B) f' -> typed G u A -> index_position f ->
      erases G (App f u) (subst1 B u) (EApp f' EBox)
  | X_Ann : forall G t A s e,
      typed G A (Srt s) -> erases G t A e ->
      erases G (Ann t A) A e
  | X_Def : forall G f T,
      typed G (Const (Def f)) T ->
      erases G (Const (Def f)) T (EConst f)
  | X_Ctor : forall G D c T,
      typed G (Const (Ctor D c)) T ->
      erases G (Const (Ctor D c)) T (ECtor D c)
  | X_Elim : forall G D s T,
      typed G (Const (Elim D s)) T -> s <> Prp ->
      erases G (Const (Elim D s)) T (EPrim D s)
  | X_Tt : forall G T,
      typed G Tt T ->
      erases G Tt T (ECtor prim_unit "tt")
  | X_True : forall G T,
      typed G BTrue T ->
      erases G BTrue T (ECtor prim_bool "true")
  | X_False : forall G T,
      typed G BFalse T ->
      erases G BFalse T (ECtor prim_bool "false")
  | X_ElimVoid : forall G C e s e',
      typed G C (Pi Void (Srt s)) -> erases G e Void e' ->
      erases G (ElimVoid C e) (App C e) (ECase prim_void e' [])
  | X_ElimUnit : forall G C c u s c' u',
      typed G C (Pi Unit (Srt s)) -> erases G c (App C Tt) c' -> erases G u Unit u' ->
      erases G (ElimUnit C c u) (App C u) (ECase prim_unit u' [c'])
  | X_ElimBool : forall G C x y b s x' y' b',
      typed G C (Pi Bool (Srt s)) ->
      erases G x (App C BTrue) x' -> erases G y (App C BFalse) y' -> erases G b Bool b' ->
      erases G (ElimBool C x y b) (App C b) (ECase prim_bool b' [x'; y'])
  | X_Pair : forall G A B a b s a' b',
      typed G (Sigma A B) (Srt s) -> erases G a A a' -> erases G b (subst1 B a) b' ->
      erases G (Pair a b) (Sigma A B) (EPair a' b')
  | X_Fst : forall G p A B p',
      erases G p (Sigma A B) p' ->
      erases G (Fst p) A (EFst p')
  | X_Snd : forall G p A B p',
      erases G p (Sigma A B) p' ->
      erases G (Snd p) (subst1 B (Fst p)) (ESnd p')
  | X_Case : forall G D s P x bs d ps us x' bs',
      spec_decls S = true -> sig_ind sg D = Some d ->
      allows_elimination S (ind_elim d) s = true ->
      length ps = length (ind_params d) -> length us = length (ind_indices d) ->
      ind_sort d <> Prp ->
      erases G x (apps (Const (Ind D)) (ps ++ us)) x' ->
      typed G P (case_motive_type d ps s) ->
      erases_branches G d ps P (ind_ctors d) bs bs' ->
      erases G (Case D s P x bs) (apps P (us ++ [x])) (ECase D x' bs')
  | X_CaseEmpty : forall G D s P x d ps us x',
      spec_decls S = true -> sig_ind sg D = Some d ->
      allows_elimination S (ind_elim d) s = true ->
      length ps = length (ind_params d) -> length us = length (ind_indices d) ->
      ind_sort d = Prp -> ind_elim d = AllSorts -> ind_ctors d = [] ->
      erases G x (apps (Const (Ind D)) (ps ++ us)) x' ->
      typed G P (case_motive_type d ps s) ->
      erases G (Case D s P x []) (apps P (us ++ [x])) (ECase D x' [])
  | X_CaseSingleton : forall G D s P x b d c ps us b',
      spec_decls S = true -> sig_ind sg D = Some d ->
      allows_elimination S (ind_elim d) s = true ->
      length ps = length (ind_params d) -> length us = length (ind_indices d) ->
      ind_sort d = Prp -> ind_elim d = AllSorts -> ind_ctors d = [c] ->
      typed G x (apps (Const (Ind D)) (ps ++ us)) ->
      typed G P (case_motive_type d ps s) ->
      erases G b (case_branch_type d ps P c) b' ->
      erases G (Case D s P x [b]) (apps P (us ++ [x]))
        (eapps b' (repeat EBox (length (ctor_fields c))))
  | X_Fix : forall G A k b s D b',
      typed G A (Srt s) -> struct_arg sg A k D -> sig_ind sg D <> None ->
      erases (A :: G) b (lift 1 A) b' -> fix_guarded sg k b ->
      erases G (Fix A k b) A (EFix k b')

  (** The branches of a match, one per constructor, in order. *)
  with erases_branches : ctx -> ind_desc -> list term -> term -> list ctor_desc -> list term ->
                         list eterm -> Prop :=
  | XB_Nil : forall G d ps P, erases_branches G d ps P [] [] []
  | XB_Cons : forall G d ps P c cs b bs b' bs',
      erases G b (case_branch_type d ps P c) b' ->
      erases_branches G d ps P cs bs bs' ->
      erases_branches G d ps P (c :: cs) (b :: bs) (b' :: bs').

  Scheme erases_mut := Induction for erases Sort Prop
    with erases_branches_mut := Induction for erases_branches Sort Prop.
  Combined Scheme erases_mutind from erases_mut, erases_branches_mut.

  (** ** A derivation of erasure is a typing derivation *)

  Theorem erases_typed :
    (forall G t T e, erases G t T e -> typed G t T) /\
    (forall G d ps P cs bs bs', erases_branches G d ps P cs bs bs' -> has_branches S sg G d ps P cs bs).
  Proof.
    apply erases_mutind; intros; try assumption.
    all: try solve [econstructor; eassumption].
    (* the empty and the singleton match: their branches, by the constructors *)
    all: eapply T_Case; try eassumption;
      match goal with H : ind_ctors _ = _ |- _ => rewrite H end;
      repeat constructor; assumption.
  Qed.
End Relation.

(** A successful entry point of erasure is a successful erasure. *)
Lemma erase_term_erased : forall S sg fuel G t T e,
  erase_term S sg fuel G t T = Erased e -> erase S sg fuel true G t T = Ok e.
Proof.
  intros S sg fuel G t T e H. unfold erase_term, to_erase_result in H.
  destruct (erase S sg fuel true G t T) as [e' | [err | st u]]; congruence.
Qed.
