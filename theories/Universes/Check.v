(** * Checking with levels and cumulativity

    A bidirectional checker over the language of Universes/Term.v.  It
    does not decide comparisons of levels itself: every comparison it
    cannot settle syntactically becomes a requirement, a constraint
    collected in its state, and the requirements are decided at the end,
    against the context of the definition, by Constraints.close_context.

    Cumulativity is its own directed check, [cumul T A] for [T ≤ A]:
    - [Type ℓ₁ ≤ Type ℓ₂] requires [ℓ₁ ≤ ℓ₂];
    - [Π x:A. B ≤ Π x:A'. B'] requires [A ≡ A'] and [B ≤ B'];
    - everything else, Σ included, requires conversion.
    Conversion [conv] is symmetric: at sorts it requires [ℓ₁ = ℓ₂], two
    constraints, and it is never weakened to [≤].  The checking rule uses
    [cumul] from the inferred type to the expected one; with the switch
    [cumulative] off it uses [conv], the kernel of lecture 7 without
    cumulativity.

    A reference to a polymorphic constant [c@{ℓ₁ … ℓₙ}] substitutes the
    levels for its variables in its type and in its constraints, which
    become requirements of the referring term.  A reference without an
    instance, [c] alone, gets fresh instance variables [?i] before the
    check ([freshen]); they are variables of the new definition, so
    every reference has its own instance.  In a [Rigid] declaration a
    fresh instance is refused: all its variables are named.

    [check_decl] checks a declaration [c@{u₁ … uₙ | C} : T := b]:
    - [T] is a type and [b : T], with the levels of the variables named
      in the declaration and of the fresh instances;
    - its requirements are entailed by [C] ([Rigid]), or added to [C]
      with no cycle of positive weight ([Extensible]).
    The stored constant is abstracted over all its variables, with the
    context decided by close_context. *)

From Stdlib Require Import String List Bool Arith ZArith.
Import ListNotations.
From DepTypes.Common Require Import Result.
From CIC.Universes Require Import Level Graph Constraints Term.

Inductive uerror : Type :=
| UUnbound : nat -> uerror
| UUnknownConst : string -> uerror
| UBadInstance : string -> uerror          (** an instance of the wrong length *)
| UNeedsInstance : string -> uerror        (** rigid: a reference without an instance *)
| UUnboundLevel : atom -> uerror           (** a level variable not of the context *)
| UNotASort : uterm -> uterm -> uerror
| UNotAPi : uterm -> uterm -> uerror
| UNotASigma : uterm -> uterm -> uerror
| UMismatch : uterm -> uterm -> uerror     (** heads that no constraint can reconcile *)
| UCannotInfer : uterm -> uerror
| UDuplicate : string -> uerror
| ULevels : cerror -> uerror               (** the requirements against the context *)
| UOutOfFuel : uerror.

(** ** Collecting requirements *)

Definition M (A : Type) : Type := list constr -> result uerror (A * list constr).

Definition ret {A} (a : A) : M A := fun cs => Ok (a, cs).
Definition mbind {A B} (m : M A) (k : A -> M B) : M B :=
  fun cs => match m cs with Ok (a, cs') => k a cs' | Err e => Err e end.
Definition fail {A} (e : uerror) : M A := fun _ => Err e.
Definition emit (c : constr) : M unit := fun cs => Ok (tt, cs ++ [c]).

Notation "'let+' x ':=' m 'in' k" := (mbind m (fun x => k))
  (at level 200, x name, m at level 100, k at level 200).

Fixpoint emit_all (cs : list constr) : M unit :=
  match cs with [] => ret tt | c :: cs' => let+ _ := emit c in emit_all cs' end.

Definition req_le (l1 l2 : level) : M unit := if lle_syn l1 l2 then ret tt else emit (cle l1 l2).
Definition req_eq (l1 l2 : level) : M unit :=
  if lsame l1 l2 then ret tt else let+ _ := emit (cle l1 l2) in emit (cle l2 l1).

Fixpoint req_eqs (c : string) (l1 l2 : list level) : M unit :=
  match l1, l2 with
  | [], [] => ret tt
  | a :: r1, b :: r2 => let+ _ := req_eq a b in req_eqs c r1 r2
  | _, _ => fail (UBadInstance c)
  end.

(** ** Fresh instances *)

Section Freshen.
  Variable sg : usig.
  Variable md : mode.

  Fixpoint freshen (n : nat) (t : uterm) : result uerror (uterm * nat) :=
    let two (k : uterm -> uterm -> uterm) (a b : uterm) :=
      let* p := freshen n a in
      let* q := freshen (snd p) b in
      Ok (k (fst p) (fst q), snd q) in
    let one (k : uterm -> uterm) (a : uterm) :=
      let* p := freshen n a in Ok (k (fst p), snd p) in
    match t with
    | UConst c [] =>
        match ulookup sg c with
        | Some d =>
            match ud_univs d, md with
            | [], _ => Ok (t, n)
            | _, Rigid => Err (UNeedsInstance c)
            | us, Extensible => Ok (UConst c (map linst (seq n (length us))), n + length us)
            end
        | None => Ok (t, n)
        end
    | UPi A B => two UPi A B
    | USigma A B => two USigma A B
    | UApp f a => two UApp f a
    | UAnn u A => two UAnn u A
    | UPair a b => two UPair a b
    | ULam b => one ULam b
    | UFst p => one UFst p
    | USnd p => one USnd p
    | _ => Ok (t, n)
    end.
End Freshen.

(** ** Conversion, cumulativity and typing *)

Section Check.
  Variable sg : usig.
  Variable univs : list atom.
  Variable cumulative : bool.

  Definition bound_level (l : level) : M unit :=
    match find (fun x => match fst x with LZero => false | a => negb (existsb (atom_eqb a) univs) end) l with
    | Some x => fail (UUnboundLevel (fst x))
    | None => ret tt
    end.

  Fixpoint bound_levels (ls : list level) : M unit :=
    match ls with [] => ret tt | l :: ls' => let+ _ := bound_level l in bound_levels ls' end.

  Fixpoint conv (fuel : nat) (t u : uterm) : M unit :=
    match fuel with
    | O => fail UOutOfFuel
    | S f =>
        match whnf sg f t, whnf sg f u with
        | Some t', Some u' =>
            match t', u' with
            | USort l1, USort l2 => req_eq l1 l2
            | UVar n, UVar m => if n =? m then ret tt else fail (UMismatch t' u')
            | UPi A B, UPi A' B' | USigma A B, USigma A' B'
            | UApp A B, UApp A' B' | UPair A B, UPair A' B' =>
                let+ _ := conv f A A' in conv f B B'
            | ULam b, ULam b' | UFst b, UFst b' | USnd b, USnd b' => conv f b b'
            | UConst c i, UConst c' i' =>
                if String.eqb c c' then req_eqs c i i' else fail (UMismatch t' u')
            | UElimNat l, UElimNat l' => req_eq l l'
            | UNat, UNat | UZero, UZero | USucc, USucc | UUnit, UUnit | UTt, UTt => ret tt
            | _, _ => fail (UMismatch t' u')
            end
        | _, _ => fail UOutOfFuel
        end
    end.

  Fixpoint cumul (fuel : nat) (t u : uterm) : M unit :=
    match fuel with
    | O => fail UOutOfFuel
    | S f =>
        match whnf sg f t, whnf sg f u with
        | Some (USort l1), Some (USort l2) => req_le l1 l2
        | Some (UPi A B), Some (UPi A' B') => let+ _ := conv f A A' in cumul f B B'
        | Some t', Some u' => conv f t' u'
        | _, _ => fail UOutOfFuel
        end
    end.

  Definition subsumes (fuel : nat) (T A : uterm) : M unit :=
    if cumulative then cumul fuel T A else conv fuel T A.

  Definition as_sort (fuel : nat) (A T : uterm) : M level :=
    match whnf sg fuel T with
    | Some (USort l) => ret l
    | Some T' => fail (UNotASort A T')
    | None => fail UOutOfFuel
    end.

  Fixpoint infer (fuel : nat) (G : list uterm) (t : uterm) {struct fuel} : M uterm :=
    match fuel with
    | O => fail UOutOfFuel
    | S f =>
        match t with
        | UVar n => match nth_error G n with Some A => ret (ulift (S n) 0 A) | None => fail (UUnbound n) end
        | USort l => let+ _ := bound_level l in ret (USort (lsucc l))
        | UPi A B | USigma A B =>
            let+ TA := infer f G A in let+ l1 := as_sort f A TA in
            let+ TB := infer f (A :: G) B in let+ l2 := as_sort f B TB in
            ret (USort (lmax l1 l2))
        | UApp g a =>
            let+ T := infer f G g in
            match whnf sg f T with
            | Some (UPi A B) => let+ _ := check f G a A in ret (usubst1 B a)
            | Some T' => fail (UNotAPi g T')
            | None => fail UOutOfFuel
            end
        | UAnn u A =>
            let+ TA := infer f G A in let+ _ := as_sort f A TA in
            let+ _ := check f G u A in ret A
        | UConst c inst =>
            match ulookup sg c with
            | None => fail (UUnknownConst c)
            | Some d =>
                if length inst =? length (ud_univs d) then
                  let+ _ := bound_levels inst in
                  let+ _ := emit_all (map (csubst (inst_map d inst)) (ud_cstrs d)) in
                  ret (ulsubst (inst_map d inst) (ud_type d))
                else fail (UBadInstance c)
            end
        | UNat | UUnit => ret (USort lzero)
        | UZero => ret UNat
        | USucc => ret (arrow UNat UNat)
        | UTt => ret UUnit
        | UElimNat l => let+ _ := bound_level l in ret (elimnat_type l)
        | UFst p =>
            let+ T := infer f G p in
            match whnf sg f T with
            | Some (USigma A _) => ret A
            | Some T' => fail (UNotASigma p T')
            | None => fail UOutOfFuel
            end
        | USnd p =>
            let+ T := infer f G p in
            match whnf sg f T with
            | Some (USigma _ B) => ret (usubst1 B (UFst p))
            | Some T' => fail (UNotASigma p T')
            | None => fail UOutOfFuel
            end
        | ULam _ | UPair _ _ => fail (UCannotInfer t)
        end
    end
  with check (fuel : nat) (G : list uterm) (t A : uterm) {struct fuel} : M unit :=
    match fuel with
    | O => fail UOutOfFuel
    | S f =>
        match t with
        | ULam b =>
            match whnf sg f A with
            | Some (UPi A1 B1) => check f (A1 :: G) b B1
            | Some A' => fail (UNotAPi t A')
            | None => fail UOutOfFuel
            end
        | UPair a b =>
            match whnf sg f A with
            | Some (USigma A1 B1) => let+ _ := check f G a A1 in check f G b (usubst1 B1 a)
            | Some A' => fail (UNotASigma t A')
            | None => fail UOutOfFuel
            end
        | _ => let+ T := infer f G t in subsumes f T A
        end
    end.
End Check.

(** ** Declarations *)

Record udecl : Type := UDecl {
  dc_name : string;
  dc_univs : list string;
  dc_cstrs : list constr;
  dc_mode : mode;
  dc_type : uterm;
  dc_body : uterm;
}.

Definition run {A} (m : M A) : result uerror (A * list constr) := m [].

Definition declared_atoms (us : list string) : list atom := map LVar us.

Definition check_cstrs_bound (univs : list atom) (C : list constr) : result uerror unit :=
  let* r := run (bound_levels univs (flat_map (fun c => [c_lhs c; c_rhs c]) C)) in Ok (fst r).

(** The type and the body of a declaration, after its fresh instances,
    with the variables of its context. *)
Definition prepare (sg : usig) (md : mode) (us : list string) (T b : uterm)
  : result uerror (uterm * uterm * list atom) :=
  let* p := freshen sg md 0 T in
  let* q := freshen sg md (snd p) b in
  Ok (fst p, fst q, declared_atoms us ++ map LInst (seq 0 (snd q))).

Definition check_decl (cumulative : bool) (sg : usig) (fuel : nat) (dc : udecl) : result uerror (udef * model) :=
  match ulookup sg (dc_name dc) with
  | Some _ => Err (UDuplicate (dc_name dc))
  | None =>
      let* _ := check_cstrs_bound (declared_atoms (dc_univs dc)) (dc_cstrs dc) in
      let* p := prepare sg (dc_mode dc) (dc_univs dc) (dc_type dc) (dc_body dc) in
      let '(T, b, univs) := p in
      let* r := run (let+ TT := infer sg univs cumulative fuel [] T in
                     let+ _ := as_sort sg fuel T TT in
                     check sg univs cumulative fuel [] b T) in
      let* cm := map_err ULevels (close_context (dc_mode dc) (dc_cstrs dc) (snd r)) in
      Ok ({| ud_name := dc_name dc; ud_univs := univs; ud_cstrs := fst cm;
             ud_type := T; ud_body := b |}, snd cm)
  end.

Definition declare (cumulative : bool) (fuel : nat) (sg : usig) (dc : udecl) : result uerror usig :=
  let* r := check_decl cumulative sg fuel dc in Ok (sg ++ [fst r]).

Fixpoint declare_all (cumulative : bool) (fuel : nat) (sg : usig) (dcs : list udecl) : result uerror usig :=
  match dcs with
  | [] => Ok sg
  | dc :: dcs' => let* sg' := declare cumulative fuel sg dc in declare_all cumulative fuel sg' dcs'
  end.

(** A term outside a declaration: its type is inferred, or it is checked
    against a type, in a context of named variables with constraints. *)
Definition infer_term (cumulative : bool) (sg : usig) (fuel : nat) (us : list string) (C : list constr)
  (md : mode) (t : uterm) : result uerror (uterm * list constr * model) :=
  let* _ := check_cstrs_bound (declared_atoms us) C in
  let* p := prepare sg md us UUnit t in
  let '(_, t', univs) := p in
  let* r := run (infer sg univs cumulative fuel [] t') in
  let* cm := map_err ULevels (close_context md C (snd r)) in
  Ok (fst r, fst cm, snd cm).

Definition check_term (cumulative : bool) (sg : usig) (fuel : nat) (us : list string) (C : list constr)
  (md : mode) (t A : uterm) : result uerror (list constr * model) :=
  let* _ := check_cstrs_bound (declared_atoms us) C in
  let* p := prepare sg md us A t in
  let '(A', t', univs) := p in
  let* r := run (let+ TA := infer sg univs cumulative fuel [] A' in
                 let+ _ := as_sort sg fuel A' TA in
                 check sg univs cumulative fuel [] t' A') in
  map_err ULevels (close_context md C (snd r)).

(** ** Instances at closed levels

    The levels of a valuation, for the open obligation that every
    instance of an accepted constant satisfying its context is accepted
    at closed levels (Contracts.instances_accepted). *)
Definition closed_map (v : valuation) (d : udef) : lsubst_map :=
  map (fun a => (a, lconst (aval v a))) (ud_univs d).
