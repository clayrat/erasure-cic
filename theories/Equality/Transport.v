(** * Equality and transport

    [eq (A : Type₀) (a : A) : A → Prop] with [refl : eq A a a], declared
    by algorithm 1 of lecture 7 (Data/Logic.v of elim-inductive-types),
    over the signature of vectors of that lecture ([sg_vec] of
    Programs/Append.v): [A] and the left side [a] are parameters, the
    right side an index.  With no fields its only constructor is a
    singleton, so its category is [AllSorts]: it eliminates into Type.

    Transport along an equality of indices, written two ways:
    - [cast A n m (p : eq ℕ n m) (v : Vec A n) : Vec A m], a [match] on
      [p] into [Type₀], registered as a δ-constant;
    - the same through the instance [elimeq[0]], Rocq's [eq_rect] with the
      dependency on the proof, registered with its ι-rules.
    Both satisfy [cast A n n (refl ℕ n) v ≡ v].  [sym], a [match] on the
    proof into Prop, turns an equality around.

    Every entry is registered through the kernel's checker: the
    declaration and its instances by algorithm 1, the δ-constants by
    [define], whose body checks against its type in the signature before
    it. *)

From Stdlib Require Import String List Bool.
Import ListNotations.
From DepTypes.Common Require Import Result Traced.
From DepTypes.PTS Require Import Syntax Named Spec Signature Eval EvalSrc Check.
From DepTypes.Configs Require Import Predicative.
From DepTypes.SystemU Require Import Looping.
From DepTypes.MLTT Require Import Choose Constants Families.
From IndTypes.Elim Require Import Decl Generate Declare.
From IndTypes.Data Require Import Nat Lists Logic.
From IndTypes.Programs Require Import Direct Append.

Open Scope string_scope.
Open Scope nterm_scope.

Definition eq_fuel : nat := 1000.

Definition sym : nterm := NConst (Def "sym").
Definition cast : nterm := NConst (Def "cast").
Definition cast_rect : nterm := NConst (Def "cast_rect").
Definition elim_eq0 : nterm := NConst (Elim "eq" (Univ 0)).

Definition sym_ty : nterm :=
  Π "A" : Type@ 0, Π "x" : "A", Π "y" : "A", Eq "A" "x" "y" ~> Eq "A" "y" "x".

(** [match p in eq _ _ z return eq A z x with refl ⇒ refl A x]. *)
Definition sym_body : nterm :=
  λ "A", λ "x", λ "y", λ "p", NCase "eq" Prp (λ "z", λ "_", Eq "A" "z" "x") "p" [refl "A" "x"].

Definition cast_ty : nterm :=
  Π "A" : Type@ 0, Π "n" : Nat, Π "m" : Nat, Eq Nat "n" "m" ~> Vec "A" "n" ~> Vec "A" "m".

(** [match p in eq _ _ y return Vec A y with refl ⇒ v]: singleton
    elimination into [Type₀]. *)
Definition cast_body : nterm :=
  λ "A", λ "n", λ "m", λ "p", λ "v", NCase "eq" (Univ 0) (λ "y", λ "_", Vec "A" "y") "p" [NVar "v"].

(** The same with the instance [elimeq[0]] of the eliminator. *)
Definition cast_rect_body : nterm :=
  λ "A", λ "n", λ "m", λ "p", λ "v", elim_eq0 Nat "n" (λ "y", λ "_", Vec "A" "y") "v" "m" "p".

Definition transport_run : list (stage * list event) * registration :=
  run_registration (
    let! s1 := declare predicative_prop eq_fuel sg_vec raw_eq [Prp; Univ 0] in
    let! s2 := define predicative_prop eq_fuel s1 "sym" (build [] sym_ty) (build [] sym_body) in
    let! s3 := define predicative_prop eq_fuel s2 "cast" (build [] cast_ty) (build [] cast_body) in
    define predicative_prop eq_fuel s3 "cast_rect" (build [] cast_ty) (build [] cast_rect_body)).

Definition sg_transport : signature := sg_of transport_run.

Example transport_stages :
  map fst (fst transport_run) =
  [AtIndType "eq"; AtCtorType "eq" "refl";
   AtElimType "eq" Prp; AtRuleLhs "eq" Prp "refl"; AtRuleRhs "eq" Prp "refl";
   AtElimType "eq" (Univ 0); AtRuleLhs "eq" (Univ 0) "refl"; AtRuleRhs "eq" (Univ 0) "refl";
   AtDefType "sym"; AtDefBody "sym"; AtDefType "cast"; AtDefBody "cast";
   AtDefType "cast_rect"; AtDefBody "cast_rect"] /\
  option_map ind_elim (sig_ind sg_transport "eq") = Some AllSorts.
Proof. split; vm_compute; reflexivity. Qed.

(** Transport along [refl] is the identity, by ι of the match and by ι
    of the instance; [sym] of [refl] is [refl]. *)
Example transport_equations :
  converts sg_transport ["A"; "n"; "v"] (cast "A" "n" "n" (refl Nat "n") "v") "v" &&
  converts sg_transport ["A"; "n"; "v"] (cast_rect "A" "n" "n" (refl Nat "n") "v") "v" &&
  converts sg_transport ["A"; "x"] (sym "A" "x" "x" (refl "A" "x")) (refl "A" "x") = true.
Proof. vm_compute. reflexivity. Qed.

(** On a free proof both are neutral, and different: a match on one
    side, a spine of [elimeq[0]] on the other. *)
Definition open_ctx : list (string * nterm) :=
  [("v", Vec "A" "n"); ("p", Eq Nat "n" "m"); ("m", Nat); ("n", Nat); ("A", Type@ 0)].

Example transport_open :
  match normalize sg_transport eq_fuel (term_in open_ctx (cast "A" "n" "m" "p" "v")) with
  | NormalForm (Case "eq" _ _ (Var 1) _) => true
  | _ => false
  end &&
  match normalize sg_transport eq_fuel (term_in open_ctx (cast_rect "A" "n" "m" "p" "v")) with
  | NormalForm t => match spine_head t with Const (Elim "eq" (Univ 0)) => true | _ => false end
  | _ => false
  end &&
  negb (converts sg_transport ["A"; "n"; "m"; "p"; "v"] (cast "A" "n" "m" "p" "v") (cast_rect "A" "n" "m" "p" "v"))
  = true.
Proof. vm_compute. reflexivity. Qed.
