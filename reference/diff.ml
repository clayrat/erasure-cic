(* The differential test of the native erasure, target evaluator and
   guard against the extract.

   Every case runs both implementations on the same input and compares
   their complete answers, converted to the extract's syntax:
   - erasure of terms: the examples of stage 6 with known types, the
     families, the W-type, proofs, pairs and choices, the matches and
     eliminators, the thirteen programs of the contract, refusals (a term
     that is not a type, a sort at a type, an unbound variable, a term of
     another shape, an elimination forbidden by its category) and the
     demonstration of BypassElim; each also for every fuel from 0 to 40,
     so that UndecidedAt agrees with its stage and its term;
   - erasure of signatures: those of the lecture, strict and bypassing,
     and the signature of the demonstrations for every fuel up to 30; a
     declaration under the name of each primitive of the target, alone
     and after the demonstrations for every fuel up to 30, refused
     (Examples.shadow_refused);
   - the target evaluator: the erased programs of the contract, with
     every fuel up to 60 and one large budget, values, stuck terms, □
     taking the place of proofs and types, and the positions of
     arguments kept by erasure (append against append_eq);
   - the guard: the bodies of every fix of the lecture, accepted and
     refused.
   It shows that two implementations agree on these inputs, not that they
   are equivalent in general. *)

module X = Deptypes
module N = Pts_native
module T = Eval_erased_native
module E = Erase_native

open Extracted
open Conversions_erased

let checks = ref 0
let failures = ref 0

let compare name native extracted =
  incr checks;
  if native <> extracted then begin
    incr failures;
    Printf.printf "FAIL %s\n" name
  end

let sg_of = function _, X.Registered sg -> sg | _ -> failwith "not registered"

(* The kinds of answers the cases met, so that a run shows what it
   compared: each kind is counted once per comparison. *)
let seen = Hashtbl.create 16
let saw kind = Hashtbl.replace seen kind (1 + Option.value ~default:0 (Hashtbl.find_opt seen kind))

let stage_name = function X.AtArity -> "arity" | X.AtSort -> "sort" | X.AtUnfold -> "unfold" | X.AtType -> "type"

let saw_erasure = function
  | X.Erased _ -> saw "erased"
  | X.NotErasable (X.XIllTyped _) -> saw "not erasable: ill-typed"
  | X.NotErasable (X.XNotAType _) -> saw "not erasable: not a type"
  | X.NotErasable (X.XShape _) -> saw "not erasable: shape"
  | X.NotErasable (X.XIllegalElim _) -> saw "not erasable: illegal elimination"
  | X.NotErasable (X.XUnsupported _) -> saw "not erasable: unsupported"
  | X.NotErasable (X.XInactive _) -> saw "not erasable: inactive"
  | X.NotErasable (X.XReserved _) -> saw "not erasable: reserved name"
  | X.UndecidedAt (st, _) -> saw ("undecided at " ^ stage_name st)

let saw_eval = function
  | X.CbvValue _ -> saw "evaluated: value"
  | X.CbvStuck _ -> saw "evaluated: stuck"
  | X.CbvOutOfFuel -> saw "evaluated: out of fuel"

(* ── builders ── *)

let nat = X.NConst (X.Ind "Nat")
let zero = X.NConst (X.Ctor ("Nat", "zero"))
let succ n = X.NApp (X.NConst (X.Ctor ("Nat", "succ")), n)
let rec numn k = if k = 0 then zero else succ (numn (k - 1))
let napps f args = List.fold_left (fun t a -> X.NApp (t, a)) f args
let def f args = napps (X.NConst (X.Def f)) args
let vec_t a n = napps (X.NConst (X.Ind "Vec")) [ a; n ]
let vnil_t a = X.NApp (X.NConst (X.Ctor ("Vec", "nil")), a)
let vcons_t a n x xs = napps (X.NConst (X.Ctor ("Vec", "cons"))) [ a; n; x; xs ]
let vec_of a xs = fst (List.fold_right (fun x (w, k) -> (vcons_t a (numn k) x w, k + 1)) xs (vnil_t a, 0))
let nvec xs = vec_of nat (List.map numn xs)
let bvec = vec_of X.NBool [ X.NTrue; X.NFalse ]
let i_proof = X.NConst (X.Ctor ("True", "I"))
let refl a x = napps (X.NConst (X.Ctor ("eq", "refl"))) [ a; x ]
let lam x b = X.NLam (x, b)
let arrow a b = X.NArrow (a, b)

(* ── erasure ── *)

let spec_x = X.predicative_prop
let spec_n = N.predicative_prop

(* [sg] extracted, [g] a context of names, innermost first. *)
let erase_both ?(strict = true) name sg fuel g t ty =
  let ctx = X.in_ctx g and t' = X.term_in g t and ty' = X.term_in g ty in
  let extracted =
    if strict then X.erase_term spec_x sg fuel ctx t' ty' else X.erase_term_bypassing spec_x sg fuel ctx t' ty'
  in
  let native =
    E.erase_term ~strict spec_n (signature_of_extracted sg) fuel (List.map term_of_extracted ctx) (term_of_extracted t')
      (term_of_extracted ty')
  in
  saw_erasure extracted;
  compare name (erase_result_to_extracted eterm_to_extracted native) extracted

(* The same on terms of de Bruijn syntax, closed. *)
let erase_raw name sg fuel t ty =
  let extracted = X.erase_term spec_x sg fuel [] t ty in
  saw_erasure extracted;
  compare name
    (erase_result_to_extracted eterm_to_extracted (E.erase_term spec_n (signature_of_extracted sg) fuel [] (term_of_extracted t) (term_of_extracted ty)))
    extracted

let sg_demo = X.sg_demo

let term_cases =
  let takes_family = X.takes_family in
  let plus2 a b = def "plus2" [ a; b ] in
  [ ("λx y. x", sg_demo, [], lam "x" (lam "y" (X.NVar "x")), arrow nat (arrow X.NBool nat));
    ("⟨1, true⟩", sg_demo, [], X.NPair (numn 1, X.NTrue), X.NTimes (nat, X.NBool));
    ("the polymorphic identity", sg_demo, [], lam "A" (lam "x" (X.NVar "x")),
     X.NPi ("A", X.NSrt (X.Univ 0), arrow (X.NVar "A") (X.NVar "A")));
    ("a family", sg_demo, [], takes_family (arrow nat (X.NSrt (X.Univ 0))), nat);
    ("a family after δ", sg_demo, [], takes_family (X.NConst (X.Def "Fam")), nat);
    ("a family after β", sg_demo, [],
     takes_family (X.NApp (X.NAnn (lam "X" (X.NVar "X"), arrow (X.NSrt (X.Univ 1)) (X.NSrt (X.Univ 1))), arrow nat (X.NSrt (X.Univ 0)))),
     nat);
    ("the W-type", X.sg_families, [], X.succ_w X.zero_w, X.nat_w);
    ("a witness", sg_demo, [], X.witness, X.witness_ty);
    ("fst of a witness", sg_demo, [], X.NFst (X.NAnn (X.witness, X.witness_ty)), nat);
    ("ex", sg_demo, [], X.ex_proof,
     napps (X.NConst (X.Ind "ex")) [ nat; lam "x" (napps (X.NConst (X.Ind "eq")) [ nat; X.NVar "x"; X.NVar "x" ]) ]);
    ("choose", sg_demo, X.types_ctx, X.choose, X.choose_ty);
    ("and", sg_demo, [], X.and_case, nat);
    ("from False", sg_demo, [], X.from_false, arrow (X.NConst (X.Ind "False")) nat);
    ("elimTrue[0]", sg_demo, [], X.elim_true_two, nat);
    ("elimTrue[0] partial", sg_demo, [], X.elim_true_partial, nat);
    ("elimBool", sg_demo, [], X.bool_case, nat);
    ("plus 2 3", sg_demo, [], def "plus" [ numn 2; numn 3 ], nat);
    ("strip I", sg_demo, [], def "strip" [ i_proof ], nat);
    ("append", sg_demo, [], def "append" [ nat; numn 1; numn 2; nvec [ 7 ]; nvec [ 8; 9 ] ],
     vec_t nat (def "plus" [ numn 1; numn 2 ]));
    ("append_eq", sg_demo, [], def "append_eq" [ nat; numn 1; numn 2; numn 3; refl nat (numn 3); nvec [ 7 ]; nvec [ 8; 9 ] ],
     vec_t nat (numn 3));
    ("append2", sg_demo, [], def "append2" [ nat; numn 1; numn 2; nvec [ 7 ]; nvec [ 8; 9 ] ], vec_t nat (plus2 (numn 1) (numn 2)));
    ("append2 nil", sg_demo, [], def "append2" [ nat; zero; numn 1; vnil_t nat; nvec [ 5 ] ], vec_t nat (plus2 zero (numn 1)));
    ("cast", sg_demo, [], def "cast" [ X.NBool; plus2 zero (numn 2); numn 2; def "plus2_zero" [ numn 2 ]; bvec ],
     vec_t X.NBool (numn 2));
    ("cast_rect", sg_demo, [], def "cast_rect" [ X.NBool; numn 2; numn 2; refl nat (numn 2); bvec ], vec_t X.NBool (numn 2));
    ("the transport on a free m", X.sg_plus2, X.free_ctx,
     def "cast" [ X.NVar "A"; plus2 zero (X.NVar "m"); X.NVar "m"; def "plus2_zero" [ X.NVar "m" ]; X.NVar "v" ],
     vec_t (X.NVar "A") (X.NVar "m"));
    ("the branch nil", X.sg_plus2, X.nil_ctx, X.nil_branch, vec_t (X.NVar "A") (plus2 zero (X.NVar "m")));
    ("a proof of plus2 0 m = m", X.sg_plus2, [ ("m", nat) ], def "plus2_zero" [ X.NVar "m" ],
     napps (X.NConst (X.Ind "eq")) [ nat; plus2 zero (X.NVar "m"); X.NVar "m" ]);
    (* refusals *)
    ("a term that is not a type", sg_demo, [], zero, zero);
    ("a sort at a type", sg_demo, [], X.NSrt (X.Univ 0), nat);
    ("a function at another shape", sg_demo, [], lam "x" (X.NVar "x"), nat) ]

let raw_cases =
  [ ("an unbound variable", X.App (X.Var 3, X.Const (X.Ctor ("Nat", "zero"))), X.Const (X.Ind "Nat"));
    ("an application of a non-function", X.App (X.Const (X.Ctor ("Nat", "zero")), X.Const (X.Ctor ("Nat", "zero"))),
     X.Const (X.Ind "Nat")) ]

let () =
  List.iter (fun (name, sg, g, t, ty) -> erase_both name sg 1000 g t ty) term_cases;
  List.iter (fun (name, sg, g, t, ty) ->
      for fuel = 0 to 40 do erase_both (Printf.sprintf "%s, fuel %d" name fuel) sg fuel g t ty done)
    term_cases;
  List.iter (fun (name, t, ty) -> erase_raw name sg_demo 1000 t ty) raw_cases;
  (* BypassElim *)
  let observe p = X.observe_proof p in
  List.iter
    (fun (name, p) ->
      erase_both ~strict:false ("bypassing, " ^ name) X.sg_bypass 1000 [] (observe p) X.NBool;
      erase_both ("strict, " ^ name) X.sg_bypass 1000 [] (observe p) X.NBool)
    [ ("trueP", X.trueP); ("falseP", X.falseP) ]

(* ── signatures ── *)

let env_both ?(strict = true) name sg fuel =
  let extracted = if strict then X.erase_env spec_x sg fuel else X.erase_env_bypassing spec_x sg fuel in
  let native = E.erase_env ~strict spec_n (signature_of_extracted sg) fuel in
  saw_erasure extracted;
  compare name (erase_result_to_extracted esignature_to_extracted native) extracted

let () =
  List.iter
    (fun (name, sg) -> env_both name sg 1000)
    [ ("the demonstrations", sg_demo); ("plus2", X.sg_plus2); ("the transport", X.sg_transport);
      ("the families", X.sg_families); ("match", X.sg_match); ("ℕ", X.sg_nat); ("the propositions", sg_of X.logic_run);
      ("half", X.sg_half); ("append", X.sg_append); ("copy", X.sg_copy); ("BypassElim", X.sg_bypass) ];
  env_both ~strict:false "BypassElim, bypassing" X.sg_bypass 1000;
  for fuel = 0 to 30 do env_both (Printf.sprintf "the demonstrations, fuel %d" fuel) sg_demo fuel done

(* A declaration under the name of a primitive of the target, the empty
   type of Examples.raw_shadow: accepted by the registration, refused by
   erasure.  After the demonstrations, whose entries are erased first, a
   small fuel stops earlier. *)
let () =
  List.iter
    (fun prim ->
      let raw = { X.raw_shadow with X.rd_name = prim } in
      let alone = sg_of (X.declare_checked spec_x 100 X.sig_empty raw []) in
      let after = sg_of (X.declare_checked spec_x 100 sg_demo raw []) in
      env_both ("a declaration " ^ prim) alone 1000;
      env_both ~strict:false ("a declaration " ^ prim ^ ", bypassing") alone 1000;
      for fuel = 0 to 30 do
        env_both (Printf.sprintf "a declaration %s after the demonstrations, fuel %d" prim fuel) after fuel
      done)
    [ X.prim_unit; X.prim_bool; X.prim_void ]

(* ── the target evaluator ── *)

let se_demo = X.se_demo
let se_native = esignature_of_extracted se_demo

let eval_both name se_x se_n fuel e =
  let extracted = X.eval_erased se_x fuel e in
  saw_eval extracted;
  compare name (ecbv_to_extracted (T.eval se_n fuel (eterm_of_extracted e))) extracted

let () =
  let programs =
    List.filter_map
      (fun (name, sg, g, t, ty) ->
        if sg == sg_demo && g = [] then
          match X.erase_closed t ty with X.Erased e -> Some (name, e) | _ -> None
        else None)
      term_cases
  in
  List.iter
    (fun (name, e) ->
      eval_both name se_demo se_native 1000 e;
      for fuel = 0 to 60 do eval_both (Printf.sprintf "%s, fuel %d" name fuel) se_demo se_native fuel e done)
    programs;
  let open X in
  let cases =
    [ ("strip □", EApp (EConst "strip", EBox));
      ("depth on □", eapps (EConst "depth") (depth_args 3));
      ("depth_elim on □", eapps (EConst "depth_elim") (depth_args 3));
      ("append", eapps (EConst "append") [ EBox; enum 1; enum 2; evec [ 7 ]; evec [ 8; 9 ] ]);
      ("append_eq, two more positions", eapps (EConst "append_eq") [ EBox; enum 1; enum 2; enum 3; EBox; evec [ 7 ]; evec [ 8; 9 ] ]);
      ("append_eq without the proof: positions shifted", eapps (EConst "append_eq") [ EBox; enum 1; enum 2; enum 3; evec [ 7 ]; evec [ 8; 9 ] ]);
      ("a match on □", ECase ("Nat", EBox, [ enum 0; ELam (EVar 0) ]));
      ("an empty match", EApp (ELam (ECase ("False", EBox, [])), EBox));
      ("an empty eliminator", eapps (EPrim ("False", Univ 0)) [ EBox; EBox ]);
      ("a data eliminator on □", eapps (EPrim ("Nat", Univ 0)) [ EBox; enum 0; ELam (ELam (EVar 0)); EBox ]);
      ("a singleton eliminator", eapps (EPrim ("True", Univ 0)) [ EBox; enum 2; EBox ]);
      ("a partial eliminator", eapps (EPrim ("True", Univ 0)) [ EBox; enum 2 ]);
      ("□ applied", eapps EBox [ enum 1; enum 2 ]);
      ("a fix short of its argument", EApp (EConst "plus2", enum 1));
      ("a fix applied to too many", eapps (EFix (0, ELam (EVar 0))) [ enum 1; enum 2 ]);
      ("a free variable", EApp (EVar 0, EBox));
      ("an unknown constant", EConst "nowhere");
      ("a projection of a non-pair", EFst (enum 1));
      ("a pair", EPair (EApp (EConst "strip", EBox), ESnd (EPair (EBox, enum 2)))) ]
  in
  List.iter
    (fun (name, e) ->
      eval_both name se_demo se_native 1000 e;
      for fuel = 0 to 40 do eval_both (Printf.sprintf "%s, fuel %d" name fuel) se_demo se_native fuel e done)
    cases;
  (* the bypassing signature: the elimination kept on data, stuck on □ *)
  match (X.erase_env_bypassing spec_x X.sg_bypass 1000,
         X.erase_term_bypassing spec_x X.sg_bypass 1000 [] (X.build [] (X.observe_proof X.trueP)) X.Bool) with
  | X.Erased se, X.Erased e -> eval_both "BypassElim on □" se (esignature_of_extracted se) 1000 e
  | _ -> compare "BypassElim erased" "no" "yes"

(* ── the guard ── *)

let guard_raw name sg k b =
  let extracted = X.guard_fix sg k b in
  saw
    (match extracted with
    | X.Ok () -> "guarded"
    | X.Err (X.GPartialCall _) -> "guard: partial call"
    | X.Err (X.GNotSubterm _) -> "guard: not a subterm"
    | X.Err (X.GShortBody _) -> "guard: short body");
  compare name (guard_result_to_extracted (N.guard_fix (signature_of_extracted sg) k (term_of_extracted b))) extracted

let guard_both name sg t =
  match X.build [] t with
  | X.Fix (_, k, b) -> guard_raw name sg k b
  | _ -> compare name "not a fix" ""

(* bodies short of their k + 1 leading λ, which no checked fix has *)
let () =
  guard_raw "a body without its λ" X.sig_empty 0 (X.Var 0);
  guard_raw "a body short of its second λ" X.sg_nat 1 (X.Lam (X.Var 0))

let () =
  List.iter
    (fun (name, sg, t) -> guard_both name sg t)
    [ ("half", X.sg_nat, X.guard_half); ("size", X.sg_match, X.size); ("under binders", X.sg_nat, X.under_binders);
      ("g pred", X.sg_nat, X.g_pred); ("partial", X.sg_nat, X.partial); ("bare", X.sg_nat, X.bare);
      ("nested", X.sg_nat, X.nested); ("shadowed", X.sg_nat, X.shadowed); ("a non-recursive field", X.sg_match, X.nonrec_field);
      ("half a position", X.sg_match, X.half_position); ("nat_rect", X.sg_nat, X.nat_rect 0); ("plus", X.sg_nat, X.plus_fix);
      ("append", X.sg_match, X.append); ("copy", X.sg_match, X.copy); ("loop", X.sg_nat, X.loop);
      ("half paired", X.sg_half, X.half_fix); ("plus paired", X.sg_direct, X.paired_plus_fix);
      ("append paired", X.sg_append, X.append_fix); ("copy paired", X.sg_copy, X.copy_fix); ("g of lecture 7", X.sg_pred, X.g_fix);
      ("strip", sg_demo, X.strip_body); ("depth", sg_demo, X.depth_body); ("append of stage 6", sg_demo, X.append_body);
      ("plus2", X.sg_plus2, X.plus2_body); ("plus2_zero", X.sg_plus2, X.plus2_zero_body);
      ("plus2_succ", X.sg_plus2, X.plus2_succ_body) ]

let () =
  List.iter (fun (kind, n) -> Printf.printf "  %s: %d\n" kind n)
    (List.sort Stdlib.compare (Hashtbl.fold (fun k n acc -> (k, n) :: acc) seen []));
  Printf.printf "diff: %d comparisons, %d differences\n" !checks !failures;
  if !failures > 0 then exit 1
