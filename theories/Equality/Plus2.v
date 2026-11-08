(** * plus2 0 m = m, and the transport of a vector

    The end-to-end example of lecture 8.  [plus2] is addition by
    recursion on its second argument, written with [fix] and [match]:

      plus2 n zero     = n
      plus2 n (succ k) = succ (plus2 n k)

    so [plus2 0 m] does not compute on a free [m], and lecture 7 refused
    the branch [nil] of [append] with [plus2] (Programs/Append.v): there
    [ys : Vec A m] is expected at [Vec A (plus2 0 m)].

    The proof [plus2_zero : Πm:ℕ. eq ℕ (plus2 0 m) m] is a [fix] on [m]
    with [match … return eq ℕ (plus2 0 m) m]: in the branch of [zero]
    [refl], in that of [succ k] the congruence of [succ], written as a
    [match] on the hypothesis [plus2_zero k].  It passes the guard and the
    checker; on a concrete [m] it computes to [refl], and the transport
    of a vector along it to the vector itself; on a free [m] the
    transport stays neutral.

    Transported backwards with [sym], the proof makes the branch [nil]
    check.  The branch [cons] needs [plus2 (succ k) m = succ (plus2 k m)]
    as well, [plus2_succ], proved the same way; with both, [append2] with
    [plus2] in its type is registered and computes, the transports
    vanishing on concrete vectors. *)

From Stdlib Require Import String List Bool.
Import ListNotations.
From DepTypes.Common Require Import Result Traced.
From DepTypes.PTS Require Import Syntax Named Spec Signature Eval EvalSrc Guard Check.
From DepTypes.Configs Require Import Predicative.
From DepTypes.SystemU Require Import Looping.
From DepTypes.MLTT Require Import Choose Constants Families.
From IndTypes.Elim Require Import Declare.
From IndTypes.Data Require Import Nat Lists Logic.
From IndTypes.Programs Require Import Direct Append.
From CIC.Equality Require Import Transport.

Open Scope string_scope.
Open Scope nterm_scope.

Definition plus2_zero : nterm := NConst (Def "plus2_zero").
Definition plus2_succ : nterm := NConst (Def "plus2_succ").
Definition append2 : nterm := NConst (Def "append2").

(** ** Definitions *)

Definition plus2_body : nterm :=
  NFix "p" (Nat ~> Nat ~> Nat) 1
    (λ "n", λ "m", NCase "Nat" (Univ 0) (λ "_", Nat) "m" [NVar "n"; λ "k", succ ("p" "n" "k")]).

Definition plus2_zero_ty : nterm := Π "m" : Nat, Eq Nat (plus2 zero "m") "m".

(** [fix pf m := match m return eq ℕ (plus2 0 m) m with
      | zero ⇒ refl ℕ zero
      | succ k ⇒ match pf k in eq _ _ y return eq ℕ (succ (plus2 0 k)) (succ y)
                 with refl ⇒ refl ℕ (succ (plus2 0 k)) end end]. *)
Definition plus2_zero_body : nterm :=
  NFix "pf" plus2_zero_ty 0
    (λ "m", NCase "Nat" Prp (λ "m'", Eq Nat (plus2 zero "m'") "m'") "m"
       [refl Nat zero;
        λ "k", NCase "eq" Prp (λ "y", λ "_", Eq Nat (succ (plus2 zero "k")) (succ "y")) ("pf" "k")
                 [refl Nat (succ (plus2 zero "k"))]]).

Definition plus2_succ_ty : nterm :=
  Π "k" : Nat, Π "m" : Nat, Eq Nat (plus2 (succ "k") "m") (succ (plus2 "k" "m")).

Definition plus2_succ_body : nterm :=
  NFix "ps" plus2_succ_ty 1
    (λ "k", λ "m", NCase "Nat" Prp (λ "m'", Eq Nat (plus2 (succ "k") "m'") (succ (plus2 "k" "m'"))) "m"
       [refl Nat (succ "k");
        λ "j", NCase "eq" Prp (λ "y", λ "_", Eq Nat (succ (plus2 (succ "k") "j")) (succ "y")) ("ps" "k" "j")
                 [refl Nat (succ (plus2 (succ "k") "j"))]]).

(** The branch [nil], with [ys] transported backwards. *)
Definition nil_branch : nterm :=
  cast "A" "m" (plus2 zero "m") (sym Nat (plus2 zero "m") "m" (plus2_zero "m")) "ys".

Definition append2_ty : nterm :=
  Π "A" : Type@ 0, Π "n" : Nat, Π "m" : Nat, Vec "A" "n" ~> Vec "A" "m" ~> Vec "A" (plus2 "n" "m").

Definition append2_body : nterm :=
  NFix "app" append2_ty 3
    (λ "A", λ "n", λ "m", λ "xs", λ "ys",
       NCase "Vec" (Univ 0) (λ "k", λ "_", Vec "A" (plus2 "k" "m")) "xs"
         [nil_branch;
          λ "k", λ "x", λ "xs'",
            cast "A" (succ (plus2 "k" "m")) (plus2 (succ "k") "m")
              (sym Nat (plus2 (succ "k") "m") (succ (plus2 "k" "m")) (plus2_succ "k" "m"))
              (vcons "A" (plus2 "k" "m") "x" ("app" "A" "k" "m" "xs'" "ys"))]).

Definition plus2_run : list (stage * list event) * registration :=
  run_registration (
    let! s1 := define predicative_prop eq_fuel sg_transport "plus2" (build [] (Nat ~> Nat ~> Nat))
                 (build [] plus2_body) in
    let! s2 := define predicative_prop eq_fuel s1 "plus2_zero" (build [] plus2_zero_ty)
                 (build [] plus2_zero_body) in
    let! s3 := define predicative_prop eq_fuel s2 "plus2_succ" (build [] plus2_succ_ty)
                 (build [] plus2_succ_body) in
    define predicative_prop eq_fuel s3 "append2" (build [] append2_ty) (build [] append2_body)).

Definition sg_plus2 : signature := sg_of plus2_run.

(** Every definition is accepted: types, bodies and the guard of each
    [fix]. *)
Example plus2_stages :
  map fst (fst plus2_run) =
  [AtDefType "plus2"; AtDefBody "plus2"; AtDefType "plus2_zero"; AtDefBody "plus2_zero";
   AtDefType "plus2_succ"; AtDefBody "plus2_succ"; AtDefType "append2"; AtDefBody "append2"] /\
  registered plus2_run <> None.
Proof. split; vm_compute; [reflexivity | discriminate]. Qed.

(** The guard of the proof: the call [pf k] on the field of [succ]. *)
Example plus2_zero_guarded :
  match build [] plus2_zero_body with
  | Fix _ k b => guard_fix sg_plus2 k b
  | _ => Err (GPartialCall (Var 0))
  end = Ok tt.
Proof. vm_compute. reflexivity. Qed.

(** The type of the proof is a proposition: a product into Prop. *)
Example plus2_zero_prop :
  snd (run_infer predicative_prop sg_plus2 eq_fuel [] (build [] plus2_zero_ty)) = Accepted (Srt Prp).
Proof. vm_compute. reflexivity. Qed.

(** ** Computation *)

(** On a concrete [m] the proof computes to [refl], and the transport of
    a vector along it to the vector itself. *)
Definition two : nterm := num 2.
Definition two_vec : nterm := vcons NBool (num 1) NTrue (vcons NBool zero NFalse (vnil NBool)).

Example proof_computes :
  map (fun n => normalize sg_plus2 eq_fuel (build [] (plus2_zero (num n)))) [0; 1; 3]
  = map (fun n => NormalForm (build [] (refl Nat (num n)))) [0; 1; 3].
Proof. vm_compute. reflexivity. Qed.

Example transport_computes :
  snd (run_check predicative_prop sg_plus2 eq_fuel []
         (build [] (cast NBool (plus2 zero two) two (plus2_zero two) two_vec)) (build [] (Vec NBool two)))
  = Accepted tt /\
  normalize sg_plus2 eq_fuel (build [] (cast NBool (plus2 zero two) two (plus2_zero two) two_vec))
  = NormalForm (build [] two_vec) /\
  eval_src sg_plus2 eq_fuel (build [] (cast NBool (plus2 zero two) two (plus2_zero two) two_vec))
  = CbvValue (build [] two_vec).
Proof. vm_compute. repeat split. Qed.

(** On a free [m] the transport is neutral: a match on the proof, itself
    a fix on [m] that does not unfold. *)
Definition free_ctx : list (string * nterm) :=
  [("v", Vec "A" (plus2 zero "m")); ("m", Nat); ("A", Type@ 0)].

Example transport_neutral :
  match normalize sg_plus2 eq_fuel (term_in free_ctx (cast "A" (plus2 zero "m") "m" (plus2_zero "m") "v")) with
  | NormalForm (Case "eq" _ _ x _) =>
      match spine_head x with Fix _ _ _ => true | _ => false end
  | _ => false
  end = true.
Proof. vm_compute. reflexivity. Qed.

(** ** The branch nil *)

(** In the context of the branch, [ys] alone is refused at
    [Vec A (plus2 0 m)], as in lecture 7; transported backwards it is
    accepted. *)
Definition nil_ctx : list (string * nterm) := [("ys", Vec "A" "m"); ("m", Nat); ("A", Type@ 0)].

Example nil_branch_checks :
  match snd (run_check predicative_prop sg_plus2 eq_fuel (in_ctx nil_ctx) (term_in nil_ctx "ys")
               (term_in nil_ctx (Vec "A" (plus2 zero "m")))) with
  | Rejected (EMismatch _ _ _) => true
  | _ => false
  end = true /\
  snd (run_check predicative_prop sg_plus2 eq_fuel (in_ctx nil_ctx) (term_in nil_ctx nil_branch)
         (term_in nil_ctx (Vec "A" (plus2 zero "m"))))
  = Accepted tt.
Proof. vm_compute. split; reflexivity. Qed.

(** ** append with plus2 *)

Example append2_computes :
  normalize sg_plus2 eq_fuel (build [] (append2 Nat (num 1) (num 2) (vec [7]) (vec [8; 9])))
  = NormalForm (build [] (vec [7; 8; 9])) /\
  normalize sg_plus2 eq_fuel (build [] (append2 Nat zero (num 1) (vnil Nat) (vec [5])))
  = NormalForm (build [] (vec [5])) /\
  eval_src sg_plus2 eq_fuel (build [] (append2 Nat (num 1) (num 2) (vec [7]) (vec [8; 9])))
  = CbvValue (build [] (vec [7; 8; 9])).
Proof. vm_compute. repeat split. Qed.

(** Its equations hold up to the transports, which stay on free indices:
    the branch [nil] is [ys] transported along [sym (plus2_zero m)]. *)
Example append2_nil_equation :
  converts sg_plus2 ["A"; "m"; "ys"] (append2 "A" zero "m" (vnil "A") "ys") nil_branch = true.
Proof. vm_compute. reflexivity. Qed.
