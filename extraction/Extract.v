(** * Extraction driver

    Exports into generated/deptypes.ml the kernel (checker, evaluators,
    [match], [fix] and the guard), the declarations of lectures 7 and 8,
    the examples of this project (the tables, the CoC gist, the paired
    programs, the equality of stage 5) and erasure with its target
    evaluator; and into generated/universes.ml the separate checker of
    the milestone of universes, whose modules [Check], [Term] and their
    [whnf] and [infer] would clash with the kernel's in one file.  The
    extract keeps the kernel's module name, so the printers of both
    submodules (extraction/pretty.ml of the kernel and
    extraction/pretty_ind.ml of the declarations, which make copies next
    to it) compile against it unchanged.  Natural numbers are OCaml ints,
    integers of the graph of levels OCaml ints, booleans OCaml bools and
    names OCaml strings. *)

From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlNativeString ExtrOcamlZInt.
From DepTypes.PTS Require Import Syntax Named Spec Signature Eval EvalSrc Guard Check.
From DepTypes.Configs Require Import Finite Predicative.
From DepTypes.SystemU Require Import Looping Encodings.
From DepTypes.MLTT Require Import Choose Constants Families.
From IndTypes.Elim Require Import Decl Generate Declare.
From IndTypes.Data Require Import Nat Lists Tree W Primitives Positivity Logic.
From IndTypes.Recursion Require Import Below CaseTree Compile.
From IndTypes.Programs Require Import Direct Half Append Rejected Copy.
From DepTypes.CIC Require Match Guard.
From CIC.Examples Require Tables CoCGist Paired.
From CIC.Equality Require Transport Plus2.
From CIC.Erasure Require Import Target Erase Observe Checked.
From CIC.Erasure Require Examples.
From CIC.Universes Require Level Graph Constraints Term Check Examples.

(** Unique names for examples whose names other modules use too. *)
Definition guard_half := Guard.half.
Definition gist_zero := CoCGist.zero.
Definition gist_succ := CoCGist.succ.
Definition gist_add := CoCGist.add.
Definition paired_plus_fix := Paired.plus_fix.

Extraction Language OCaml.
Set Extraction Output Directory "generated".

(** Arithmetic on de Bruijn indices and levels, natively. *)
Extract Inlined Constant Init.Nat.add => "(+)".
Extract Inlined Constant Init.Nat.max => "max".
Extract Inlined Constant Init.Nat.eqb => "(=)".
Extract Inlined Constant Init.Nat.ltb => "(<)".
Extract Inlined Constant PeanoNat.Nat.add => "(+)".
Extract Inlined Constant PeanoNat.Nat.max => "max".
Extract Inlined Constant PeanoNat.Nat.eqb => "(=)".
Extract Inlined Constant PeanoNat.Nat.ltb => "(<)".

Extraction "deptypes.ml"
  (* the kernel *)
  term_eqb sort_eqb gref_eqb rename lift subst subst1 arrow times free_in map_sorts lookup
  apps spine_head spine_args pis lams vars
  sig_empty sig_add sig_type sig_delta sig_ind sig_def ind_type ctor_type field_type elim_arity elim_view full_elim iota
  allows_elimination
  case_iota inst_params inst_tele case_motive_type case_branch_type fix_view full_fix fix_unfold
  full_spine spine_iota has_lams spine_value eval_src
  mark_at entry_marks field_mark sub_arg origin branch_fields peel call_ok guard guard_entry guard_fix
  resolve resolve_ctx build in_ctx term_in
  lambda_star system_u system_u_minus predicative pure_predicative predicative_prop coc u_to_univ
  classify normalize_trace normalize whnf convert
  infer check run_infer run_check
  observe
  nat_desc elim_nat_ty vec_desc w_desc sg_nat sg_families nat_w zero_w succ_w types_ctx choose choose_ty
  Match.match_fuel Match.nat_rect_ty Match.nat_rect Match.rect_ctx Match.plus_fix Match.sg_match Match.numeral
  Match.append Match.copy Match.boolp_desc Match.sg_boolp Match.loop
  guard_half Guard.size Guard.under_binders Guard.g_pred Guard.partial Guard.bare Guard.nested Guard.shadowed
  Guard.guard_of Guard.nonrec_field Guard.half_position
  (* the declarations of lectures 7 and 8 *)
  classify_decl sort_class sort_level motive_type method_type elim_type iota_rules
  within elim_class_of
  declare declare_elim define declare_checked declare_bypassing declare_bypassing_elim define_checked
  run_registration registered refusal unit_at
  raw_nat raw_list list_desc raw_vec raw_w
  logic_fuel raw_true raw_false raw_eq raw_and raw_or raw_ex raw_ex1 raw_accp raw_boolp raw_sigT0
  logic_run sg_logic category sg_ex1 boolp_bypassed sg_bypass observe_proof trueP falseP
  compile_checked compile_all named_equations
  prog_fuel num plus_fn sg_direct half_fn sg_half append_fn plus2_fn sg_vec sg_append pred_fn g_fn copy_fn sg_copy
  (* the examples of this project *)
  Tables.tables Tables.tables_fuel Tables.infer_all Tables.u_to_prop Tables.id_ty Tables.id
  CoCGist.gist_fuel CoCGist.n_ty gist_zero gist_succ CoCGist.one CoCGist.two CoCGist.three CoCGist.four
  CoCGist.add_ty gist_add CoCGist.convertible CoCGist.pair_ty CoCGist.pair
  CoCGist.vect_ctx CoCGist.vect_one CoCGist.vect_three CoCGist.vect_four CoCGist.in_vect
  Paired.accepted Paired.same_result Paired.half_fix paired_plus_fix Paired.append_fix Paired.copy_fix
  Paired.sg_pred Paired.g_fix
  Transport.eq_fuel Transport.sym_ty Transport.sym_body Transport.cast_ty Transport.cast_body
  Transport.cast_rect_body Transport.transport_run Transport.sg_transport
  Plus2.plus2_body Plus2.plus2_zero_ty Plus2.plus2_zero_body Plus2.plus2_succ_ty Plus2.plus2_succ_body
  Plus2.nil_branch Plus2.append2_ty Plus2.append2_body Plus2.plus2_run Plus2.sg_plus2
  Plus2.free_ctx Plus2.nil_ctx
  (* erasure *)
  eterm_eqb erename elift esubst esubst1 eapps espine_head espine_args elams evars
  prim_unit prim_bool prim_void prim_entries efind_ind efind_elim efind_def efind_ctor
  ecase_iota earity ehyp eiota_args eelim_iota eelim_partial eval_erased
  kind_of efield_of erase_ind erase_term erase_env erase_term_bypassing erase_env_bypassing
  NatT ListT VecT observes run_steps
  Examples.erase_fuel Examples.strip_ty Examples.strip_body Examples.depth_ty Examples.depth_body
  Examples.depth_elim_body Examples.append_ty Examples.append_body Examples.append_eq_ty Examples.append_eq_body
  Examples.demo_run Examples.sg_demo Examples.se_demo Examples.enum Examples.erase_closed
  Examples.takes_family Examples.witness Examples.witness_ty Examples.ex_proof Examples.depth_args
  Examples.and_case Examples.from_false Examples.elim_true_two Examples.elim_true_partial
  Examples.contract_on Examples.bool_case Examples.two_vec Examples.evec Examples.demo_steps Examples.sg_steps.

Extraction "universes.ml"
  Level.lnorm Level.lplus Level.lsucc Level.lmax Level.lle_syn Level.lsame Level.lsubst Level.atoms_of
  Graph.solve Graph.entails Graph.check_model Graph.cycle_ok Graph.nodes
  Constraints.decompose Constraints.graph_of Constraints.implied Constraints.refute Constraints.close_context
  Constraints.cle Constraints.clt Constraints.csubst
  Term.ulift Term.usubst Term.arrow Term.uapps Term.ulsubst Term.elimnat_type Term.ulookup Term.whnf
  Check.conv Check.cumul Check.check_decl Check.declare Check.declare_all Check.infer_term Check.check_term
  Universes.Examples.u Universes.Examples.v Universes.Examples.w Universes.Examples.l1 Universes.Examples.l2
  Universes.Examples.fuel Universes.Examples.below_type Universes.Examples.below_body Universes.Examples.below_decl
  Universes.Examples.sg_below Universes.Examples.const_nat Universes.Examples.id_type Universes.Examples.id_decl
  Universes.Examples.sg_id Universes.Examples.self_app Universes.Examples.idid_decl Universes.Examples.sg_idid
  Universes.Examples.lift_decl Universes.Examples.lower_decl Universes.Examples.sg_lift
  Universes.Examples.fam0 Universes.Examples.fun0 Universes.Examples.pair0 Universes.Examples.coerce_max.
