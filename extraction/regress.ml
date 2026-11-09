(* Regression tests of the extract: the answers the demos print, and the
   checks of the plan that the examples prove in Rocq, now on the
   extracted programs — the four tables, the gist, the categories and the
   refusals, nat_rect and the guard, plus2 and the transport, erasure and
   both evaluators, and the milestone of universes.  Two more checks have
   no Rocq counterpart: on the thirteen programs of the contract the
   erased program reaches exactly the erasure of the source value (the
   obligation erasure_first_order of Contracts.v, tested), and the
   answers of erasure for every fuel from 0 up are Undecided until they
   are the answer with enough fuel (fuel is monotone on these inputs). *)
open Deptypes
open Pretty
open Pretty_ind
open Pretty_cic

let failures = ref 0
let checks = ref 0

let expect name actual expected =
  incr checks;
  if actual <> expected then begin
    incr failures;
    Printf.printf "FAIL %s\n  expected: %s\n  actual:   %s\n" name expected actual
  end

let expect_true name b = expect name (string_of_bool b) "true"

let fuel = 300
let sg_of = function _, Registered sg -> sg | _ -> failwith "not registered"
let nat = NConst (Ind "Nat")
let zero = NConst (Ctor ("Nat", "zero"))
let succ n = NApp (NConst (Ctor ("Nat", "succ")), n)
let rec numn k = if k = 0 then zero else succ (numn (k - 1))
let napps f args = List.fold_left (fun t a -> NApp (t, a)) f args
let def f args = napps (NConst (Def f)) args
let vec_t a n = napps (NConst (Ind "Vec")) [ a; n ]
let vnil_t a = NApp (NConst (Ctor ("Vec", "nil")), a)
let vcons_t a n x xs = napps (NConst (Ctor ("Vec", "cons"))) [ a; n; x; xs ]
let vec_of a xs = fst (List.fold_right (fun x (w, k) -> (vcons_t a (numn k) x w, k + 1)) xs (vnil_t a, 0))
let nvec xs = vec_of nat (List.map numn xs)
let bvec = vec_of NBool [ NTrue; NFalse ]
let v x = NVar x
let i_proof = NConst (Ctor ("True", "I"))
let infer_in spec sg g t = snd (run_infer spec sg fuel (in_ctx g) (term_in g t))
let check_in spec sg g t a = snd (run_check spec sg fuel (in_ctx g) (term_in g t) (term_in g a))
let src sg t = pc (eval_src sg fuel (build [] t))
let erun e = pec (eval_erased se_demo fuel e)
let erased t a = per (erase_closed t a)

(* The thirteen programs of the contract on examples (Erasure/Examples.v). *)
let contract_programs =
  let plus2 a b = def "plus2" [ a; b ] in
  [ (def "plus" [ numn 2; numn 3 ], nat);
    (def "strip" [ i_proof ], nat);
    (and_case, nat);
    (elim_true_two, nat);
    (elim_true_partial, nat);
    (bool_case, nat);
    (witness, witness_ty);
    (def "append" [ nat; numn 1; numn 2; nvec [ 7 ]; nvec [ 8; 9 ] ], vec_t nat (def "plus" [ numn 1; numn 2 ]));
    (def "append_eq" [ nat; numn 1; numn 2; numn 3; napps (NConst (Ctor ("eq", "refl"))) [ nat; numn 3 ]; nvec [ 7 ]; nvec [ 8; 9 ] ],
     vec_t nat (numn 3));
    (def "append2" [ nat; numn 1; numn 2; nvec [ 7 ]; nvec [ 8; 9 ] ], vec_t nat (plus2 (numn 1) (numn 2)));
    (def "append2" [ nat; zero; numn 1; vnil_t nat; nvec [ 5 ] ], vec_t nat (plus2 zero (numn 1)));
    (def "cast" [ NBool; plus2 zero (numn 2); numn 2; def "plus2_zero" [ numn 2 ]; bvec ], vec_t NBool (numn 2));
    (def "cast_rect" [ NBool; numn 2; numn 2; napps (NConst (Ctor ("eq", "refl"))) [ nat; numn 2 ]; bvec ],
     vec_t NBool (numn 2)) ]

let () =
  (* the four tables *)
  let tables ?(names = []) g t = String.concat "; " (List.map (pa ~names) (infer_all g t)) in
  expect "tables id_ty" (tables [] (build [] id_ty)) "accepted: ∗; accepted: ∗; accepted: Type₁; accepted: Prop";
  expect "tables id id_ty id" (tables [] (build [] (napps id [ id_ty; id ])))
    "accepted: ΠA:∗. A → A; accepted: ΠA:∗. A → A; rejected: ΠA:Type₀. A → A has type Type₁, expected Type₀; accepted: ΠA:Prop. A → A";
  expect "tables family" (tables ~names:[ "A" ] [ Srt Star ] (build [ "A" ] (NArrow (v "A", NSrt Star))))
    "rejected: no rule (∗, □, _) for A → ∗; accepted: □; accepted: Type₁; accepted: Type₁";
  expect "tables box" (tables [] (Srt Box))
    "accepted: △; rejected: the sort □ has no type; accepted: Type₂; accepted: Type₂";

  (* the gist *)
  let known = List.map (fun (t, n) -> (build [] t, n)) [ (four, "four"); (one, "one"); (n_ty, "Nat") ] in
  expect "gist four" (pa ~known (snd (run_infer coc sig_empty gist_fuel [] (build [] four)))) "accepted: Nat";
  expect "gist add equations"
    (String.concat " " (List.map (fun (t, u) -> string_of_bool (convertible t u))
       [ (napps gist_add [ gist_zero; gist_zero ], gist_zero); (napps gist_add [ three; one ], four);
         (napps gist_add [ three; one ], three) ]))
    "true true false";
  let names = List.map fst vect_ctx in
  expect "gist zip refused"
    (pa ~names ~known (snd (run_infer coc sig_empty gist_fuel (in_ctx vect_ctx)
       (in_vect (napps (v "zip") [ four; v "item_ty"; v "item_ty"; vect_one; vect_four ])))))
    "rejected: replicate one item_ty item has type Vect one item_ty, expected Vect four item_ty";
  expect "gist concat checks"
    (pa_unit (snd (run_check coc sig_empty gist_fuel (in_ctx vect_ctx) (in_vect vect_four)
       (in_vect (napps (v "Vect") [ four; v "item_ty" ])))))
    "accepted";

  (* Prop *)
  let logic_sg = sg_of logic_run in
  expect "categories"
    (String.concat " " (List.map (fun d -> match category logic_sg d with Some AllSorts -> "all" | Some PropOnly -> "prop" | None -> "-")
       [ "True"; "False"; "eq"; "and"; "AccP"; "or"; "ex" ]))
    "all all all all all prop prop";
  expect "or refused" (pp_registration (snd (run_registration (declare_elim predicative_prop logic_fuel logic_sg "or" (Univ 0)))))
    "refused: elimor[0]: the category of elimination of or does not allow motives in Type₀";
  expect "BoolP refused" (pp_registration (snd (declare_checked predicative_prop logic_fuel sig_empty raw_boolp [ Prp; Univ 0 ])))
    "refused: elimBoolP[0]: the category of elimination of BoolP does not allow motives in Type₀";
  expect "bypass source" (String.concat ", " (List.map (fun p -> src sg_bypass (observe_proof p)) [ trueP; falseP ]))
    "value true, value false";
  expect "bypass refused by erasure"
    (match erase_env predicative_prop sg_bypass fuel with NotErasable (XIllegalElim (d, Univ 0)) -> d | _ -> "?") "BoolP";
  expect "bypass stuck after erasure"
    (match (erase_env_bypassing predicative_prop sg_bypass fuel,
            erase_term_bypassing predicative_prop sg_bypass fuel [] (build [] (observe_proof trueP)) Bool) with
     | Erased se, Erased e -> pec (eval_erased se fuel e)
     | _ -> "?")
    "stuck at elimBoolP[0] □ true false □";
  expect "witness erased" (erased witness witness_ty) "erased: ⟨2, □⟩";
  expect "ex erased" (erased ex_proof (napps (NConst (Ind "ex")) [ nat; NLam ("x", napps (NConst (Ind "eq")) [ nat; v "x"; v "x" ]) ]))
    "erased: □";

  (* nat_rect, the guard, the pairs *)
  expect "nat_rect levels"
    (String.concat "; " (List.map (fun j -> pa (infer_in predicative sg_nat [] (nat_rect j))) [ 0; 1; 2 ]))
    (String.concat "; " (List.map (fun j -> "accepted: " ^ pt (build [] (nat_rect_ty j))) [ 0; 1; 2 ]));
  let step = NLam ("n", NLam ("ih", succ (succ (v "ih")))) and motive = NLam ("_", nat) in
  expect "double 3" (String.concat ", " (List.map (fun f -> src sg_nat (napps f [ motive; zero; step; numn 3 ])) [ nat_rect 0; elim_nat ]))
    "value 6, value 6";
  let trace, _ = normalize_trace sg_nat fuel (term_in (rect_ctx 0) (napps (nat_rect 0) [ v "P"; v "z"; v "s"; succ (v "n") ])) in
  expect "nat_rect succ redexes" (pp_redexes (cic_redexes sg_nat trace)) "fix · β ×4 · ι matchNat · β";
  expect "half 5" (src sg_nat (NApp (guard_half, numn 5))) "value 2";
  expect "copy guarded" (match guard_of sg_match copy with Ok () -> "ok" | Err e -> pp_guard_error e) "ok";
  expect "g refused" (pa (infer_in predicative sg_pred [] g_fix))
    "rejected: the guard refuses the call #2 (pred #0): pred #0 is not a strict subterm of the structural argument";
  expect "partial refused" (pa (infer_in predicative sg_nat [] partial))
    "rejected: the guard refuses the partial call #3 #2: the structural argument is missing";
  expect "bare refused" (pa (infer_in predicative sg_nat [] bare))
    "rejected: the guard refuses the partial call #2: the structural argument is missing";
  expect_true "half paired"
    (List.for_all (fun k -> same_result sg_half (NApp (half_fix, numn k)) (NApp (half, numn k))) [ 0; 1; 2; 3; 4; 5; 6; 7 ]);
  expect_true "append paired"
    (same_result sg_append (napps append_fix [ nat; numn 1; numn 2; nvec [ 7 ]; nvec [ 8; 9 ] ])
       (def "append" [ nat; numn 1; numn 2; nvec [ 7 ]; nvec [ 8; 9 ] ]));

  (* plus2 and the transport *)
  let moved = def "cast" [ NBool; def "plus2" [ zero; numn 2 ]; numn 2; def "plus2_zero" [ numn 2 ]; bvec ] in
  expect "plus2_zero 2" (pe (normalize sg_plus2 fuel (build [] (def "plus2_zero" [ numn 2 ])))) "normal form refl Nat 2";
  expect "transport" (src sg_plus2 moved) "value cons Bool 1 true (cons Bool 0 false (nil Bool))";
  let trace, _ = normalize_trace sg_plus2 fuel (build [] moved) in
  expect "transport redexes" (pp_redexes (cic_redexes sg_plus2 trace))
    "δ cast · β ×5 · δ plus2_zero · fix · β · ι matchNat · β · fix · β · ι matchNat · β · fix · β · ι matchNat · ι matcheq ×3";
  expect "nil branch"
    (pa_unit (check_in predicative_prop sg_plus2 nil_ctx nil_branch (vec_t (v "A") (def "plus2" [ zero; v "m" ]))))
    "accepted";
  expect "ys refused"
    (match check_in predicative_prop sg_plus2 nil_ctx (v "ys") (vec_t (v "A") (def "plus2" [ zero; v "m" ])) with
     | Rejected (EMismatch _) -> "mismatch" | _ -> "?")
    "mismatch";
  expect "append2" (src sg_plus2 (def "append2" [ nat; numn 1; numn 2; nvec [ 7 ]; nvec [ 8; 9 ] ]))
    "value cons Nat 2 7 (cons Nat 1 8 (cons Nat 0 9 (nil Nat)))";

  (* erasure *)
  let edef f = match efind_def se_demo f with Some b -> pet b | None -> "absent" in
  expect "erased append" (edef "append")
    "fix f {struct 3} := λx. λy. λz. λu. λv. match u with v | λw. λx'. λy'. cons □ (plus w z) x' (f □ w z y' v) end";
  expect "erased append_eq" (edef "append_eq") "λx. λy. λz. λu. λv. λw. λx'. cast □ (plus y z) u □ (append □ y z w x')";
  expect "erased cast" (edef "cast") "λx. λy. λz. λu. λv. v";
  expect "erased proofs and families" (String.concat ", " (List.map edef [ "sym"; "plus2_zero"; "Fam" ])) "□, □, □";
  expect "erased strip" (edef "strip") "fix f {struct 0} := λx. 0";
  expect "append arities"
    (erun (eapps (EConst "append_eq") [ EBox; enum 1; enum 2; enum 3; EBox; evec [ 7 ]; evec [ 8; 9 ] ]))
    (erun (eapps (EConst "append") [ EBox; enum 1; enum 2; evec [ 7 ]; evec [ 8; 9 ] ]));
  expect "choose erased"
    (per (erase_term predicative_prop sg_demo fuel (in_ctx types_ctx) (term_in types_ctx choose) (term_in types_ctx choose_ty)))
    "erased: λx. λy. λz. match x with y | z end";
  expect "strip □" (erun (EApp (EConst "strip", EBox))) "value 0";
  expect "depth □" (String.concat ", " (List.map (fun f -> erun (eapps (EConst f) (depth_args 3))) [ "depth"; "depth_elim" ]))
    "value 3, value 3";
  expect "match on □" (erun (ECase ("Nat", EBox, [ enum 0; ELam (EVar 0) ]))) "stuck at match □ with 0 | λx. x end";
  expect "empty eliminator" (erun (eapps (EPrim ("False", Univ 0)) [ EBox; EBox ])) "stuck at elimFalse[0] □ □";
  expect "undecided without fuel"
    (match erase_term predicative_prop sg_demo 0 [] (build [] zero) (build [] nat) with UndecidedAt (AtArity, _) -> "ok" | _ -> "?")
    "ok";
  expect "the demonstration signature is replayed from checked steps"
    (match run_steps sig_empty demo_steps with Some sg -> string_of_bool (sg = sg_demo) | None -> "none")
    "true";

  (* the contract on examples, and the first-order obligation tested *)
  List.iteri
    (fun i (t, a) ->
      let name = Printf.sprintf "contract %d" i in
      expect_true name (contract_on t a);
      match (eval_src sg_demo 1000 (build [] t), erase_closed t a) with
      | CbvValue value, Erased e -> (
          match (eval_erased se_demo 1000 e, erase_term predicative_prop sg_demo 1000 [] value (build [] a)) with
          | CbvValue w, Erased w' -> expect (name ^ ": the erasure of the value") (pet w) (pet w')
          | r, r' -> expect (name ^ ": the erasure of the value") (pec r) (per r'))
      | _ -> expect name "no value or no erasure" "")
    contract_programs;

  (* fuel: undecided, then the answer *)
  List.iteri
    (fun i (t, a) ->
      let final = per (erase_closed t a) in
      let rec sweep n seen_final =
        if n > 60 then ()
        else
          let r = erase_term predicative_prop sg_demo n [] (build [] t) (build [] a) in
          match r with
          | UndecidedAt _ when not seen_final -> sweep (n + 1) false
          | UndecidedAt _ -> expect (Printf.sprintf "fuel %d monotone at %d" i n) (per r) final
          | _ -> expect (Printf.sprintf "fuel %d at %d" i n) (per r) final; sweep (n + 1) true
      in
      sweep 0 false)
    contract_programs;

  (* the milestone of universes *)
  let open Universes in
  let open Pretty_univ in
  let decl = function Ok (d, _) -> "accepted: " ^ pp_constrs d.ud_cstrs | Err e -> "refused: " ^ pp_uerror e in
  let chk = function Ok (cs, _) -> "accepted: " ^ pp_constrs cs | Err e -> "refused: " ^ pp_uerror e in
  let inf = function Ok ((t, cs), _) -> pp_uterm t ^ " with " ^ pp_constrs cs | Err e -> "refused: " ^ pp_uerror e in
  expect "Below" (decl (check_decl true [] fuel below_decl)) "accepted: none";
  expect "Below without cumulativity" (decl (check_decl false [] fuel below_decl))
    "refused: 1 ≤ 0 is not implied; counter-model every level 0";
  expect "Π at u" (inf (infer_term true [] fuel [ "u" ] [] Rigid (id_type u))) "Type (u+1) with none";
  expect "id at 0" (inf (infer_term true sg_id fuel [] [] Rigid (uapps (UConst ("id", [ lzero ])) [ UNat; UZero ]))) "ℕ with none";
  expect "id at 1" (inf (infer_term true sg_id fuel [] [] Rigid (uapps (UConst ("id", [ l1 ])) [ USort lzero; UNat ])))
    "Type₀ with none";
  expect "id one instance" (inf (infer_term true sg_id fuel [ "u" ] [] Extensible (self_app [ u ])))
    "refused: the cycle u < u of positive weight";
  expect "id fresh instance" (inf (infer_term true sg_id fuel [ "u" ] [] Extensible (self_app [])))
    "ΠA:Type u. A → A with u+1 ≤ ?0";
  expect "idid@{1 1}" (inf (infer_term true sg_idid fuel [] [] Rigid (UConst ("idid", [ l1; l1 ]))))
    "refused: 2 ≤ 1 is not implied; counter-model every level 0";
  expect "Type u : Type u" (chk (check_term true [] fuel [ "u" ] [] Extensible (USort u) (USort u)))
    "refused: the cycle u < u of positive weight";
  expect "u ≤ v ≤ u" (decl (check_decl true [] fuel (lower_decl Rigid [ cle u v; cle v u ]))) "accepted: u ≤ v, v ≤ u";
  expect "u < v ≤ u" (decl (check_decl true [] fuel (lower_decl Rigid [ clt u v; cle v u ])))
    "refused: the cycle u < v ≤ u of positive weight";
  expect "lowering" (decl (check_decl true [] fuel (lower_decl Rigid [ cle u v ])))
    "refused: v ≤ u is not implied; counter-model u = 0, v = 1";

  Printf.printf "regress: %d checks, %d failures\n" !checks !failures;
  if !failures > 0 then exit 1
