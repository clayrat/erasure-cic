(** * Erasure on examples

    The checks of stage 6 on one signature: the vectors, [plus] and the
    equality of stage 5, with the propositions of lecture 7 ([True],
    [False], [and], [ex], [AccP]) and a few definitions:
    - [strip (p : True) {struct p} := match p with I ⇒ 0 end], a [fix]
      structural on a proof: the target unfolds it on [□];
    - [depth n x (a : AccP A R x) {struct a}], the recursion on the
      functional field [g] of a proof, its depth given by [n], and the
      same through the instance [elimAccP[0]], whose singleton rule
      builds the hypotheses of the recursive field on [□];
    - [append] and [append_eq], the same with an extra proof of the
      length: different arities after erasure, one vector computed;
    - the transport of stage 5 and [append2] with [plus2].
    Every closed observable program is run on both sides, and its results
    compared by [observes]. *)

From Stdlib Require Import String List Bool Arith Relations.
Import ListNotations.
From DepTypes.Common Require Import Result Traced.
From DepTypes.PTS Require Import Syntax Named Spec Signature Eval EvalSrc Check.
From DepTypes.Configs Require Import Predicative.
From DepTypes.SystemU Require Import Looping.
From DepTypes.MLTT Require Import Choose Constants Families.
From IndTypes.Elim Require Import Declare.
From IndTypes.Data Require Import Nat Lists Logic.
From IndTypes.Programs Require Import Direct Append.
From CIC.Equality Require Import Transport Plus2.
From CIC.Erasure Require Import Target Erase Observe Checked.
From IndTypes.Recursion Require Import CaseTree Compile.

Open Scope string_scope.
Open Scope nterm_scope.

Definition erase_fuel : nat := 1000.

(** ** The signature *)

Definition nat_case (x z s : nterm) : nterm := NCase "Nat" (Univ 0) (λ "_", Nat) x [z; s].

Definition strip_ty : nterm := True_ ~> Nat.
Definition strip_body : nterm :=
  NFix "strip" strip_ty 0 (λ "p", NCase "True" (Univ 0) (λ "_", Nat) "p" [zero]).

Definition depth_ty : nterm :=
  Π "A" : NProp, Π "R" : ("A" ~> "A" ~> NProp), Π "next" : ("A" ~> "A"),
  Π "step" : (Π "x" : "A", "R" ("next" "x") "x"), Π "n" : Nat, Π "x" : "A", AccP "A" "R" "x" ~> Nat.

(** [depth 0 x a = 0], [depth (succ k) x (introP x₀ g) =
    succ (depth k (next x₀) (g (next x₀) (step x₀)))]. *)
Definition depth_body : nterm :=
  NFix "depth" depth_ty 6
    (λ "A", λ "R", λ "next", λ "step", λ "n", λ "x", λ "a",
       nat_case "n" zero
         (λ "k", NCase "AccP" (Univ 0) (λ "x'", λ "_", Nat) "a"
                   [λ "x0", λ "g", succ ("depth" "A" "R" "next" "step" "k" ("next" "x0")
                                           ("g" ("next" "x0") ("step" "x0")))])).

(** The same through [elimAccP[0]], the motive [λ_ _. ℕ → ℕ]. *)
Definition depth_elim_body : nterm :=
  λ "A", λ "R", λ "next", λ "step", λ "n", λ "x", λ "a",
    NConst (Elim "AccP" (Univ 0)) "A" "R" (λ "x'", λ "_", Nat ~> Nat)
      (λ "x0", λ "g", λ "ih", λ "m", nat_case "m" zero (λ "k", succ ("ih" ("next" "x0") ("step" "x0") "k")))
      "x" "a" "n".

Definition append_ty : nterm :=
  Π "A" : Type@ 0, Π "n" : Nat, Π "m" : Nat, Vec "A" "n" ~> Vec "A" "m" ~> Vec "A" (plus "n" "m").

Definition append_body : nterm :=
  NFix "app" append_ty 3
    (λ "A", λ "n", λ "m", λ "xs", λ "ys",
       NCase "Vec" (Univ 0) (λ "k", λ "_", Vec "A" (plus "k" "m")) "xs"
         [NVar "ys"; λ "k", λ "x", λ "xs'", vcons "A" (plus "k" "m") "x" ("app" "A" "k" "m" "xs'" "ys")]).

Definition appendD : nterm := NConst (Def "append").
Definition append_eq : nterm := NConst (Def "append_eq").

(** [append] with an extra proof of its length. *)
Definition append_eq_ty : nterm :=
  Π "A" : Type@ 0, Π "n" : Nat, Π "m" : Nat, Π "k" : Nat, Eq Nat (plus "n" "m") "k" ~>
  Vec "A" "n" ~> Vec "A" "m" ~> Vec "A" "k".

Definition append_eq_body : nterm :=
  λ "A", λ "n", λ "m", λ "k", λ "e", λ "xs", λ "ys",
    cast "A" (plus "n" "m") "k" "e" (appendD "A" "n" "m" "xs" "ys").

Definition demo_run : list (stage * list event) * registration :=
  run_registration (
    let! s1 := declare predicative_prop erase_fuel sg_plus2 raw_true [Prp; Univ 0] in
    let! s2 := declare predicative_prop erase_fuel s1 raw_false [Prp; Univ 0] in
    let! s3 := declare predicative_prop erase_fuel s2 raw_and [Prp; Univ 0] in
    let! s4 := declare predicative_prop erase_fuel s3 raw_ex [Prp] in
    let! s5 := declare predicative_prop erase_fuel s4 raw_accp [Prp; Univ 0] in
    let! s6 := define predicative_prop erase_fuel s5 "strip" (build [] strip_ty) (build [] strip_body) in
    let! s7 := define predicative_prop erase_fuel s6 "depth" (build [] depth_ty) (build [] depth_body) in
    let! s8 := define predicative_prop erase_fuel s7 "depth_elim" (build [] depth_ty) (build [] depth_elim_body) in
    let! s9 := define predicative_prop erase_fuel s8 "append" (build [] append_ty) (build [] append_body) in
    let! s10 := define predicative_prop erase_fuel s9 "append_eq" (build [] append_eq_ty) (build [] append_eq_body) in
    define predicative_prop erase_fuel s10 "Fam" (build [] (Type@ 1)) (build [] (Nat ~> Type@ 0))).

Definition sg_demo : signature := sg_of demo_run.


Example demo_registered : registered demo_run <> None.
Proof. vm_compute. discriminate. Qed.

(** ** The erased signature *)

Definition se_demo : esignature :=
  match erase_env predicative_prop sg_demo erase_fuel with Erased se => se | _ => [] end.

Fixpoint enum (n : nat) : eterm :=
  match n with O => ECtor "Nat" "zero" | S n' => EApp (ECtor "Nat" "succ") (enum n') end.

(** The proofs and the types are [□]; [strip] keeps its [fix] and the
    branch of the singleton match; the transport is the identity on its
    last argument. *)
Example erased_definitions :
  match erase_env predicative_prop sg_demo erase_fuel with Erased _ => true | _ => false end = true /\
  map (efind_def se_demo) ["plus2_zero"; "sym"; "Fam"; "strip"; "cast"]
  = [Some EBox; Some EBox; Some EBox; Some (EFix 0 (ELam (ECtor "Nat" "zero"))); Some (elams 5 (EVar 0))].
Proof. vm_compute. split; reflexivity. Qed.

Definition erase_closed (t T : nterm) : erase_result eterm :=
  erase_term predicative_prop sg_demo erase_fuel [] (build [] t) (build [] T).

(** ** Known types *)

(** λ and pairs are erased at their expected types, nested binders keep
    their indices; the polymorphic identity, whose codomain is a
    variable, is not erased whole. *)
Example erase_lambdas :
  erase_closed (λ "x", λ "y", "x") (Nat ~> NBool ~> Nat) = Erased (ELam (ELam (EVar 1))) /\
  erase_closed ⟨ num 1, NTrue ⟩ (Nat ⨯ NBool) = Erased (EPair (enum 1) (ECtor prim_bool "true")) /\
  erase_closed (λ "A", λ "x", "x") (Π "A" : Type@ 0, "A" ~> "A") = Erased (ELam (ELam (EVar 0))).
Proof. vm_compute. repeat split. Qed.

(** A family is erased by its arity, also when the arity shows only
    after δ ([Fam]) or β. *)
Definition takes_family (F : nterm) : nterm := ((λ "P", zero) ∷ (F ~> Nat)) (λ "_", Nat).

Example erase_families :
  erase_closed (takes_family (Nat ~> Type@ 0)) Nat = Erased (EApp (ELam (ECtor "Nat" "zero")) EBox) /\
  erase_closed (takes_family (NConst (Def "Fam"))) Nat = Erased (EApp (ELam (ECtor "Nat" "zero")) EBox) /\
  erase_closed (takes_family (((λ "X", "X") ∷ (Type@ 1 ~> Type@ 1)) (Nat ~> Type@ 0))) Nat
  = Erased (EApp (ELam (ECtor "Nat" "zero")) EBox).
Proof. vm_compute. repeat split. Qed.

(** The family [B] of a W-type is a type parameter: [□]. *)
Example erase_w_family :
  erase_term predicative_prop sg_families erase_fuel [] (build [] (succ_w zero_w)) (build [] nat_w)
  = Erased (eapps (ECtor "W" "sup") [EBox; EBox; ECtor prim_bool "true";
                                     ELam (eapps (ECtor "W" "sup")
                                                 [EBox; EBox; ECtor prim_bool "false";
                                                  ELam (ECase prim_void (EVar 0) [])])]).
Proof. vm_compute. reflexivity. Qed.

(** Without fuel nothing is decided. *)
Example erase_undecided :
  match erase_term predicative_prop sg_demo 0 [] (build [] zero) (build [] Nat) with
  | UndecidedAt AtArity _ => true
  | _ => false
  end &&
  match erase_term predicative_prop sg_demo 1 [] (build [] (takes_family (((λ "X", "X") ∷ (Type@ 1 ~> Type@ 1)) (Nat ~> Type@ 0))))
          (build [] Nat) with
  | UndecidedAt _ _ => true
  | _ => false
  end = true.
Proof. vm_compute. reflexivity. Qed.

(** ** Proofs, pairs and choices *)

Definition witness : nterm := ⟨ num 2, refl Nat (num 2) ⟩.
Definition witness_ty : nterm := Σ "x" : Nat, Eq Nat "x" "x".
Definition ex_proof : nterm := NConst (Ctor "ex" "ex_intro") Nat (λ "x", Eq Nat "x" "x") (num 2) (refl Nat (num 2)).

Example erase_proofs :
  erase_closed witness witness_ty = Erased (EPair (enum 2) EBox) /\
  erase_closed (NFst (witness ∷ witness_ty)) Nat = Erased (EFst (EPair (enum 2) EBox)) /\
  erase_closed ex_proof (NConst (Ind "ex") Nat (λ "x", Eq Nat "x" "x")) = Erased EBox /\
  erase_term predicative_prop sg_demo erase_fuel (in_ctx types_ctx) (term_in types_ctx choose)
    (term_in types_ctx choose_ty)
  = Erased (ELam (ELam (ELam (ECase prim_bool (EVar 2) [EVar 1; EVar 0])))).
Proof. vm_compute. repeat split. Qed.

(** ** strip and depth *)

Definition strip : nterm := NConst (Def "strip").
Definition depth : nterm := NConst (Def "depth").

Example strip_runs :
  erase_closed (strip I_) Nat = Erased (EApp (EConst "strip") EBox) /\
  eval_src sg_demo erase_fuel (build [] (strip I_)) = CbvValue (build [] zero) /\
  eval_erased se_demo erase_fuel (EApp (EConst "strip") EBox) = CbvValue (enum 0).
Proof. vm_compute. repeat split. Qed.

(** No closed proof of [AccP] exists for a total [step]; the erased
    [depth] runs with [□] for every proof and type: the [fix] unfolds on
    [□], and [elimAccP[0]] takes its only method on [□], with the
    hypothesis of [g] built from the description. *)
Definition depth_args (n : nat) : list eterm := [EBox; EBox; EBox; EBox; enum n; EBox; EBox].

Example depth_runs :
  map (fun n => eval_erased se_demo erase_fuel (eapps (EConst "depth") (depth_args n))) [0; 3]
  = [CbvValue (enum 0); CbvValue (enum 3)] /\
  map (fun n => eval_erased se_demo erase_fuel (eapps (EConst "depth_elim") (depth_args n))) [0; 3]
  = [CbvValue (enum 0); CbvValue (enum 3)].
Proof. vm_compute. split; reflexivity. Qed.

(** ** Matches *)

(** [and] with two fields: the branch applied to [□] twice. *)
Definition and_case : nterm :=
  ((λ "p", NCase "and" (Univ 0) (λ "_", Nat) "p" [λ "a", λ "b", num 1]) ∷ (And True_ True_ ~> Nat))
    (NConst (Ctor "and" "conj") True_ True_ I_ I_).

(** An empty match in a function on [False]: no closed proof of [False]
    is made, the erased function applied to [□] gets stuck. *)
Definition from_false : nterm := (λ "f", NCase "False" (Univ 0) (λ "_", Nat) "f" []) ∷ (False_ ~> Nat).

Example erase_matches :
  erase_closed and_case Nat
  = Erased (EApp (ELam (EApp (EApp (ELam (ELam (enum 1))) EBox) EBox)) EBox) /\
  eval_erased se_demo erase_fuel (match erase_closed and_case Nat with Erased e => e | _ => EBox end)
  = CbvValue (enum 1) /\
  erase_closed from_false (False_ ~> Nat) = Erased (ELam (ECase "False" EBox [])) /\
  eval_erased se_demo erase_fuel (EApp (ELam (ECase "False" EBox [])) EBox) = CbvStuck (ECase "False" EBox []) /\
  eval_erased se_demo erase_fuel (ECase "Nat" EBox [enum 0; ELam (EVar 0)]) = CbvStuck (ECase "Nat" EBox [enum 0; ELam (EVar 0)]).
Proof. vm_compute. repeat split. Qed.

(** A [fix] short of its structural argument is a value. *)
Example fix_unsaturated :
  match eval_erased se_demo erase_fuel (EApp (EConst "plus2") (enum 1)) with
  | CbvValue (EApp (EFix 1 _) _) => true
  | _ => false
  end = true.
Proof. vm_compute. reflexivity. Qed.

(** ** The eliminators of lecture 7 *)

Definition elim_true_two : nterm := NConst (Elim "True" (Univ 0)) (λ "_", Nat) (num 2) I_.
Definition elim_true_partial : nterm :=
  ((λ "f", "f" I_) ∷ ((True_ ~> Nat) ~> Nat)) (NConst (Elim "True" (Univ 0)) (λ "_", Nat) (num 2)).

Example erase_primitives :
  erase_closed elim_true_two Nat = Erased (eapps (EPrim "True" (Univ 0)) [EBox; enum 2; EBox]) /\
  eval_erased se_demo erase_fuel (eapps (EPrim "True" (Univ 0)) [EBox; enum 2; EBox]) = CbvValue (enum 2) /\
  eval_erased se_demo erase_fuel (match erase_closed elim_true_partial Nat with Erased e => e | _ => EBox end)
  = CbvValue (enum 2) /\
  eval_erased se_demo erase_fuel (eapps (EPrim "False" (Univ 0)) [EBox; EBox])
  = CbvStuck (eapps (EPrim "False" (Univ 0)) [EBox; EBox]) /\
  eval_erased se_demo erase_fuel (eapps (EPrim "Nat" (Univ 0)) [EBox; enum 0; ELam (ELam (EVar 0)); EBox])
  = CbvStuck (eapps (EPrim "Nat" (Univ 0)) [EBox; enum 0; ELam (ELam (EVar 0)); EBox]).
Proof. vm_compute. repeat split. Qed.

(** ** The contract on examples

    Each closed program is accepted by the checker at an observable
    type, erased, run on both sides, and its results are related. *)

Definition contract_on (t T : nterm) : bool :=
  match snd (run_check predicative_prop sg_demo erase_fuel [] (build [] t) (build [] T)),
        erase_closed t T, eval_src sg_demo erase_fuel (build [] t) with
  | Accepted _, Erased e, CbvValue v =>
      match eval_erased se_demo erase_fuel e with
      | CbvValue w => observes sg_demo erase_fuel erase_fuel (build [] T) v w
      | _ => false
      end
  | _, _, _ => false
  end.

Definition bool_case : nterm := ((λ "b", NElimBool ((λ "_", Nat) ∷ (NBool ~> Type@ 0)) (num 1) zero "b") ∷ (NBool ~> Nat)) NTrue.
Definition two_vec : nterm := vcons NBool (num 1) NTrue (vcons NBool zero NFalse (vnil NBool)).

Example contract_examples :
  forallb (fun '(t, T) => contract_on t T)
    [(plus (num 2) (num 3), Nat);
     (strip I_, Nat);
     (and_case, Nat);
     (elim_true_two, Nat);
     (elim_true_partial, Nat);
     (bool_case, Nat);
     (witness, witness_ty);
     (appendD Nat (num 1) (num 2) (vec [7]) (vec [8; 9]), Vec Nat (plus (num 1) (num 2)));
     (append_eq Nat (num 1) (num 2) (num 3) (refl Nat (num 3)) (vec [7]) (vec [8; 9]), Vec Nat (num 3));
     (append2 Nat (num 1) (num 2) (vec [7]) (vec [8; 9]), Vec Nat (plus2 (num 1) (num 2)));
     (append2 Nat zero (num 1) (vnil Nat) (vec [5]), Vec Nat (plus2 zero (num 1)));
     (cast NBool (plus2 zero (num 2)) (num 2) (plus2_zero (num 2)) two_vec, Vec NBool (num 2));
     (cast_rect NBool (num 2) (num 2) (refl Nat (num 2)) two_vec, Vec NBool (num 2))] = true.
Proof. vm_compute. reflexivity. Qed.

(** [append] and [append_eq] keep their arities: [append_eq] takes the
    length and the proof, [□], as well, and on the corresponding
    arguments computes the same vector. *)
Definition evec (xs : list nat) : eterm :=
  match erase_closed (vec xs) (Vec Nat (num (length xs))) with Erased e => e | _ => EBox end.

Example append_arities :
  match efind_def se_demo "append", efind_def se_demo "append_eq" with
  | Some (EFix 3 (ELam (ELam (ELam (ELam (ELam _)))))),
    Some (ELam (ELam (ELam (ELam (ELam (ELam (ELam _))))))) => true
  | _, _ => false
  end = true /\
  eval_erased se_demo erase_fuel (eapps (EConst "append") [EBox; enum 1; enum 2; evec [7]; evec [8; 9]])
  = eval_erased se_demo erase_fuel (eapps (EConst "append_eq") [EBox; enum 1; enum 2; enum 3; EBox; evec [7]; evec [8; 9]]) /\
  eval_erased se_demo erase_fuel (eapps (EConst "append") [EBox; enum 1; enum 2; evec [7]; evec [8; 9]])
  = CbvValue (evec [7; 8; 9]).
Proof. vm_compute. repeat split. Qed.

(** ** BypassElim

    The signature of stage 2 with [elimBoolP[0]] registered by the
    bypass: erasure proper refuses it; its demonstration keeps the
    elimination as one on data, which gets stuck on the erased proof,
    while the source returned data. *)
Example bypass :
  erase_env predicative_prop sg_bypass erase_fuel = NotErasable (XIllegalElim "BoolP" (Univ 0)) /\
  eval_src sg_bypass erase_fuel (build [] (observe_proof trueP)) = CbvValue BTrue /\
  match erase_env_bypassing predicative_prop sg_bypass erase_fuel,
        erase_term_bypassing predicative_prop sg_bypass erase_fuel [] (build [] (observe_proof trueP)) (build [] NBool) with
  | Erased se, Erased e =>
      match eval_erased se erase_fuel e with CbvStuck _ => true | _ => false end
  | _, _ => false
  end = true.
Proof. vm_compute. repeat split. Qed.

(** ** The premises of the contract hold

    The signature is checked: the same entries come out of 23 checked
    steps, lecture 7 (ℕ, [plus], [pow], [f], vectors), stage 5 and the
    declarations and definitions above.  [Vec ℕ 3] is observable. *)
Definition demo_steps : list step :=
  [StDeclare predicative reg_fuel raw_nat [Univ 0];
   StCompile predicative prog_fuel [plus_fn; pow_fn; f_fn];
   StDeclare predicative 300 raw_vec [Univ 0];
   StDeclare predicative_prop eq_fuel raw_eq [Prp; Univ 0];
   StDefine predicative_prop eq_fuel "sym" (build [] sym_ty) (build [] sym_body);
   StDefine predicative_prop eq_fuel "cast" (build [] cast_ty) (build [] cast_body);
   StDefine predicative_prop eq_fuel "cast_rect" (build [] cast_ty) (build [] cast_rect_body);
   StDefine predicative_prop eq_fuel "plus2" (build [] (Nat ~> Nat ~> Nat)) (build [] plus2_body);
   StDefine predicative_prop eq_fuel "plus2_zero" (build [] plus2_zero_ty) (build [] plus2_zero_body);
   StDefine predicative_prop eq_fuel "plus2_succ" (build [] plus2_succ_ty) (build [] plus2_succ_body);
   StDefine predicative_prop eq_fuel "append2" (build [] append2_ty) (build [] append2_body);
   StDeclare predicative_prop erase_fuel raw_true [Prp; Univ 0];
   StDeclare predicative_prop erase_fuel raw_false [Prp; Univ 0];
   StDeclare predicative_prop erase_fuel raw_and [Prp; Univ 0];
   StDeclare predicative_prop erase_fuel raw_ex [Prp];
   StDeclare predicative_prop erase_fuel raw_accp [Prp; Univ 0];
   StDefine predicative_prop erase_fuel "strip" (build [] strip_ty) (build [] strip_body);
   StDefine predicative_prop erase_fuel "depth" (build [] depth_ty) (build [] depth_body);
   StDefine predicative_prop erase_fuel "depth_elim" (build [] depth_ty) (build [] depth_elim_body);
   StDefine predicative_prop erase_fuel "append" (build [] append_ty) (build [] append_body);
   StDefine predicative_prop erase_fuel "append_eq" (build [] append_eq_ty) (build [] append_eq_body);
   StDefine predicative_prop erase_fuel "Fam" (build [] (Type@ 1)) (build [] (Nat ~> Type@ 0))].

Definition sg_steps : signature := match run_steps ∅ demo_steps with Some sg => sg | None => ∅ end.

Theorem demo_checked : wf_checked sg_demo.
Proof.
  apply (wf_checked_entries sg_steps).
  - apply (steps_checked demo_steps ∅); [exact wf_checked_empty | repeat constructor | vm_compute; reflexivity].
  - vm_compute. reflexivity.
Qed.

Example vector_observable : Observable sg_demo (VecT NatT (build [] (num 3))).
Proof.
  eapply O_Vec; [apply rt_refl | vm_compute; reflexivity | ].
  eapply O_Nat; [apply rt_refl | vm_compute; reflexivity].
Qed.
