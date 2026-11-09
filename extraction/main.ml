(* Lecture demonstrations, in the order of the plan of stage 8:
   - the four tables on one checker, and the examples of the CoC gist on λC;
   - Prop: Σ with its witness and proof against ex, the categories of
     elimination, the refused large elimination of BoolP and what the
     mode BypassElim does with it, in the source and after erasure;
   - nat_rect by fix and match, the equations of both implementations and
     the closed results of elimNat; the programs of lecture 7 paired;
   - the guard: half directly, copy with its call under λ, and the refusals;
   - plus2 0 m = m, the transport of a vector along it and its computation;
   - erasure: append with and without a proof, the transport, choose,
     strip and depth on □, and both evaluators on closed programs;
   - the milestone of universes: Unit at two levels, id@{u}, and the
     refusal of Type u : Type u.

   Traces of normal order list their redexes: δ with the name of the
   constant it unfolds, a separate step; ι of an eliminator, ι of a match
   (ι matchD) and the unfolding of a fix (fix) apart.  The evaluators by
   value have no trace: their answers are printed.  Closed numerals print
   as digits, the Church numerals of the gist and nat_rect by their
   names.  Terms deeper than the bound print as "…"; in events, #k is the
   free variable of de Bruijn index k.  No evaluation here diverges. *)
open Deptypes
open Pretty
open Pretty_ind
open Pretty_cic

let fuel = 300
let depth = 12

let header title =
  print_newline ();
  print_endline ("== " ^ title)

let line s = print_endline ("  " ^ s)
let sg_of = function _, Registered sg -> sg | _ -> failwith "not registered"

(* Builders over the names of the declarations. *)
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
let lam x b = NLam (x, b)
let v x = NVar x
let i_proof = NConst (Ctor ("True", "I"))

let infer_in spec sg g t = snd (run_infer spec sg fuel (in_ctx g) (term_in g t))
let check_in spec sg g t a = snd (run_check spec sg fuel (in_ctx g) (term_in g t) (term_in g a))
let names_of g = List.map fst g
let src sg t = pc ~depth (eval_src sg fuel (build [] t))

(* A term under normal order: its redexes and its normal form; with
   [terms] the terms of the trace as well. *)
let show_normal ?(terms = false) ?(names = []) ?(known = []) sg label t =
  let trace, result = normalize_trace sg fuel t in
  let rs = cic_redexes sg trace in
  (match rs with
   | [] -> line (label ^ ": normal")
   | _ -> line (label ^ ", " ^ plural (List.length rs) "step" ^ ": " ^ pp_redexes rs));
  if terms && rs <> [] then begin
    line ("  " ^ pt ~depth ~names ~known t);
    List.iter2 (fun r u -> line ("  ⇝ " ^ r ^ ":  " ^ pt ~depth ~names ~known u)) rs (List.tl trace)
  end;
  line ("  " ^ pe ~depth ~names ~known result)

(* An equation by conversion, each side under normal order. *)
let show_equation ?(known = []) sg g l r =
  let names = names_of g in
  line (pt ~depth ~names ~known (term_in g l) ^ " ≡ " ^ pt ~depth ~names ~known (term_in g r));
  let side label t =
    let trace, result = normalize_trace sg fuel (term_in g t) in
    let rs = cic_redexes sg trace in
    (match rs with
     | [] -> line ("  " ^ label ^ ": normal")
     | _ -> line ("  " ^ label ^ ", " ^ plural (List.length rs) "step" ^ ": " ^ pp_redexes rs));
    result
  in
  let a = side "left" l and b = side "right" r in
  match (a, b) with
  | NormalForm a, NormalForm b when term_eqb a b -> line ("  both reach " ^ pt ~depth ~names ~known a)
  | _ -> line ("  different: " ^ pe ~depth ~names ~known a ^ " and " ^ pe ~depth ~names ~known b)

let show_def sg f =
  match sig_def sg f with
  | Some (a, b) ->
      line (f ^ " : " ^ pt ~depth a);
      line ("  := " ^ pt ~depth:20 b)
  | None -> line (f ^ ": not defined")

(* ── 1. Four tables on one checker ─────────────────────────────────── *)

let table_names = [ "U⁻"; "λC"; "predicative"; "predicative with Prop" ]

let show_tables label names g t =
  line label;
  List.iter2 (fun name a -> line ("  " ^ name ^ ": " ^ pa ~depth ~names a)) table_names (infer_all g (build names t))

let gist_known =
  List.map (fun (t, n) -> (build [] t, n))
    [ (four, "four"); (three, "three"); (two, "two"); (one, "one"); (gist_zero, "zero"); (gist_succ, "succ");
      (gist_add, "add"); (pair, "Pair"); (n_ty, "Nat") ]

let demo_tables () =
  print_endline "Four tables on one checker: U⁻, λC, the predicative hierarchy, the same with Prop.";
  print_endline "The terms are written in ∗ and □; each table reads them in its own sorts.";
  header "The same terms under the four tables";
  show_tables "⊢ ΠA:∗. A → A" [] [] id_ty;
  show_tables "⊢ id (ΠA:∗. A → A) id, with id := λA x. x : ΠA:∗. A → A" [] [] (napps id [ id_ty; id ]);
  show_tables "A : ∗ ⊢ A → ∗, a family indexed by the terms of A" [ "A" ] [ Srt Star ] (NArrow (v "A", NSrt Star));
  show_tables "⊢ ΠA:∗. ∗, a type operator" [] [] (NPi ("A", NSrt Star, NSrt Star));
  show_tables "⊢ □" [] [] (NSrt Box);
  header "The CoC gist on λC: Church numerals, add and pairs (Nat := ΠA:∗. (A → A) → A → A)";
  let known = gist_known in
  List.iter
    (fun (name, t) ->
      let body = match build [] t with Ann (u, _) -> u | u -> u in
      line (name ^ " := " ^ pt ~depth ~known:(List.tl (List.tl known)) body);
      line ("  " ^ pa ~depth ~known (snd (run_infer coc sig_empty gist_fuel [] (build [] t)))))
    [ ("zero", gist_zero); ("succ", gist_succ); ("add", gist_add); ("Pair", pair) ];
  line ("four := " ^ pt ~depth ~known:(List.tl known) (build [] four) ^ ": "
        ^ pa ~depth ~known (snd (run_infer coc sig_empty gist_fuel [] (build [] four))));
  List.iter
    (fun (t, u) ->
      line (Printf.sprintf "%s ≡ %s: %b" (pt ~depth ~known (build [] t)) (pt ~depth ~known (build [] u)) (convertible t u)))
    [ (napps gist_add [ gist_zero; one ], one);
      (napps gist_add [ three; one ], four);
      (napps gist_add [ three; one ], three) ];
  header "The CoC gist: vectors by assumption, concat computes its length, zip of different lengths";
  let names = names_of vect_ctx in
  let infer_v t = snd (run_infer coc sig_empty gist_fuel (in_ctx vect_ctx) (in_vect t)) in
  line ("context: " ^ pp_named_ctx ~depth ~known vect_ctx);
  line ("v₁ := " ^ pt ~depth ~names ~known (in_vect vect_one) ^ ", v₃ := " ^ pt ~depth ~names ~known (in_vect vect_three));
  line ("concat one three item_ty v₁ v₃: " ^ pa ~depth ~names ~known (infer_v vect_four));
  line ("  against Vect four item_ty: "
        ^ pa_unit
            (snd (run_check coc sig_empty gist_fuel (in_ctx vect_ctx) (in_vect vect_four)
                    (in_vect (napps (v "Vect") [ four; v "item_ty" ])))));
  line ("zip four item_ty item_ty v₁ v₄: "
        ^ pa ~depth ~names ~known (infer_v (napps (v "zip") [ four; v "item_ty"; v "item_ty"; vect_one; vect_four ])));
  line ("the same context in U⁻: "
        ^ pa ~depth ~known (snd (run_infer system_u_minus sig_empty gist_fuel (in_ctx vect_ctx) (in_vect vect_one))))

(* ── 2. Prop ───────────────────────────────────────────────────────── *)

let demo_prop () =
  print_newline ();
  print_endline "Prop: proofs beside data, the categories of elimination, and what erasure keeps.";
  header "Σ(x:ℕ). x = x keeps its witness; ex ℕ (λx. x = x) is a proposition";
  let ex_ty = napps (NConst (Ind "ex")) [ nat; lam "x" (napps (NConst (Ind "eq")) [ nat; v "x"; v "x" ]) ] in
  List.iter
    (fun (t, a) ->
      line (pt ~depth (build [] t) ^ " : " ^ pt ~depth (build [] a));
      line ("  " ^ pa_unit (check_in predicative_prop sg_demo [] t a)
            ^ ", the type in " ^ (match infer_in predicative_prop sg_demo [] a with
                                 | Accepted s -> pt s | r -> pa r));
      line ("  " ^ per ~depth (erase_closed t a)))
    [ (witness, witness_ty); (ex_proof, ex_ty) ];
  let first = NFst (NAnn (witness, witness_ty)) in
  line (pt ~depth (build [] first) ^ " : ℕ, " ^ per ~depth (erase_closed first nat) ^ ", "
        ^ (match erase_closed first nat with Erased e -> pec (eval_erased se_demo fuel e) | _ -> ""));
  header "The categories of elimination on the hierarchy with Prop";
  let logic_sg = sg_of logic_run in
  List.iter
    (fun d -> line (d ^ ": " ^ match category logic_sg d with Some c -> pp_elim_class c | None -> "not declared"))
    [ "True"; "False"; "eq"; "and"; "AccP"; "or"; "ex" ];
  header "Large elimination refused where a proof would be observed";
  let refused run = line (pp_registration ~depth (snd run)) in
  refused (run_registration (declare_elim predicative_prop logic_fuel logic_sg "or" (Univ 0)));
  refused (run_registration (declare_elim predicative_prop logic_fuel logic_sg "ex" (Univ 0)));
  refused (declare_checked predicative_prop logic_fuel sig_empty raw_boolp [ Prp; Univ 0 ]);
  header "BypassElim: elimBoolP[0] registered anyway, two proofs of BoolP told apart by the source";
  line (pp_registration ~depth (snd boolp_bypassed));
  List.iter (fun p -> let t = observe_proof p in line (pt ~depth (build [] t) ^ " ⇓ " ^ src sg_bypass t)) [ trueP; falseP ];
  header "BypassElim after erasure: refused by erasure proper; kept in its demonstration, stuck on □";
  line ("erase_env: " ^ match erase_env predicative_prop sg_bypass fuel with
                        | Erased _ -> "erased"
                        | NotErasable e -> per (NotErasable e)
                        | UndecidedAt (s, t) -> per (UndecidedAt (s, t)));
  List.iter
    (fun p ->
      let t = build [] (observe_proof p) in
      match
        ( erase_env_bypassing predicative_prop sg_bypass fuel,
          erase_term_bypassing predicative_prop sg_bypass fuel [] t Bool )
      with
      | Erased se, Erased e -> line (pet ~depth e ^ ": " ^ pec ~depth (eval_erased se fuel e))
      | Erased _, r -> line (per ~depth r)
      | NotErasable e, _ -> line (per ~depth (NotErasable e))
      | UndecidedAt (s, u), _ -> line (per ~depth (UndecidedAt (s, u))))
    [ trueP; falseP ]

(* ── 3. nat_rect by fix and match ──────────────────────────────────── *)

let demo_nat_rect () =
  print_newline ();
  print_endline "match and fix in the kernel: nat_rect, its equations, and the programs of lecture 7.";
  header "nat_rect j := fix F P z s n {struct n} := match n return P n with zero ⇒ z | succ m ⇒ s m (F P z s m)";
  line ("nat_rect 0 := " ^ pt ~depth:20 (build [] (nat_rect 0)));
  List.iter
    (fun j -> line (Printf.sprintf "nat_rect %d: %s" j (pa ~depth (infer_in predicative sg_nat [] (nat_rect j)))))
    [ 0; 1; 2 ];
  header "The ι-equations of both implementations, on open terms";
  let known = [ (build [] (nat_rect 0), "nat_rect₀") ] in
  let g = rect_ctx 0 in
  let p, z, s, n = (v "P", v "z", v "s", v "n") in
  line ("context: " ^ pp_named_ctx ~depth g);
  show_equation ~known sg_nat g (napps (nat_rect 0) [ p; z; s; zero ]) z;
  show_equation ~known sg_nat g (napps (nat_rect 0) [ p; z; s; succ n ]) (napps s [ n; napps (nat_rect 0) [ p; z; s; n ] ]);
  show_equation sg_nat g (napps elim_nat [ p; z; s; zero ]) z;
  show_equation sg_nat g (napps elim_nat [ p; z; s; succ n ]) (napps s [ n; napps elim_nat [ p; z; s; n ] ]);
  header "Closed results: double 3 by nat_rect 0 and by elimNat[0], motive λ_. ℕ, step λn ih. succ (succ ih)";
  let motive = lam "_" nat and step = lam "n" (lam "ih" (succ (succ (v "ih")))) in
  List.iter
    (fun (label, f) ->
      let t = napps f [ motive; zero; step; numn 3 ] in
      line (label ^ " … 3 ⇓ " ^ src sg_nat t);
      show_normal ~known sg_nat ("  " ^ label ^ " … 3 under normal order") (build [] t))
    [ ("nat_rect₀", nat_rect 0); ("elimNat[0]", elim_nat) ];
  header "fix and match against the compiler of lecture 7: the same closed results";
  List.iter
    (fun (label, ok) -> line (label ^ ": " ^ string_of_bool ok))
    [ ("half by fix and half through the history, on 0 … 7",
       List.for_all (fun k -> same_result sg_half (NApp (half_fix, numn k)) (NApp (half, numn k))) [ 0; 1; 2; 3; 4; 5; 6; 7 ]);
      ("plus by fix and plus compiled directly, 2 + 3",
       same_result sg_direct (napps paired_plus_fix [ numn 2; numn 3 ]) (def "plus" [ numn 2; numn 3 ]));
      ("append by fix and append through the history, [7] ++ [8; 9]",
       same_result sg_append (napps append_fix [ nat; numn 1; numn 2; nvec [ 7 ]; nvec [ 8; 9 ] ])
         (def "append" [ nat; numn 1; numn 2; nvec [ 7 ]; nvec [ 8; 9 ] ])) ]

(* ── 4. The guard ──────────────────────────────────────────────────── *)

let demo_guard () =
  print_newline ();
  print_endline "The guard of fix: every recursive call on a strict subterm of the structural argument.";
  header "half directly: its call is two fields down, where lecture 7 needed the history";
  let events, answer = run_infer predicative sg_nat fuel [] (build [] guard_half) in
  List.iter (fun ev -> line (pp_event ~depth:8 ev)) events;
  line (pa ~depth answer);
  line ("half 5 ⇓ " ^ src sg_nat (NApp (guard_half, numn 5)));
  header "copy on W: the call on f b, a child under the λ of its position";
  line ("copy := " ^ pt ~depth:20 (build [] copy));
  line ("guard: " ^ match guard_of sg_match copy with Ok () -> "every call guarded" | Err e -> pp_guard_error ~depth e);
  line (pa ~depth (infer_in predicative sg_match [] copy));
  header "Refused: g (succ k) = g (pred k), pred k is no strict subterm";
  line ("g := " ^ pt ~depth:20 (build [] g_pred));
  line (pa ~depth (infer_in predicative sg_nat [] g_pred));
  line ("the same g with pred compiled by lecture 7: " ^ pa ~depth (infer_in predicative sg_pred [] g_fix));
  header "Refused: incomplete self-reference, a call without its structural argument";
  List.iter
    (fun (label, t) ->
      line (label ^ " := " ^ pt ~depth:20 (build [] t));
      line ("  " ^ pa ~depth (infer_in predicative sg_nat [] t)))
    [ ("partial", partial); ("bare", bare) ];
  header "Refused: a valid call around an invalid one";
  line ("nested := " ^ pt ~depth:20 (build [] nested));
  line ("  " ^ pa ~depth (infer_in predicative sg_nat [] nested))

(* ── 5. plus2 0 m = m and the transport ───────────────────────────── *)

let demo_plus2 () =
  print_newline ();
  print_endline "Equality: plus2 0 m = m by fix and match, and the transport of a vector along it.";
  let sg = sg_plus2 in
  header "plus2, by recursion on its second argument, and plus2_zero";
  show_def sg "plus2";
  show_def sg "plus2_zero";
  line ("the type of plus2_zero is in " ^ (match infer_in predicative_prop sg [] plus2_zero_ty with Accepted s -> pt s | r -> pa r));
  header "plus2_zero 2 computes to refl";
  show_normal sg "plus2_zero 2" (build [] (def "plus2_zero" [ numn 2 ]));
  line ("plus2_zero 2 ⇓ " ^ src sg (def "plus2_zero" [ numn 2 ]));
  header "cast Bool (plus2 0 2) 2 (plus2_zero 2) [true; false] computes to the vector";
  let moved = def "cast" [ NBool; def "plus2" [ zero; numn 2 ]; numn 2; def "plus2_zero" [ numn 2 ]; bvec ] in
  line (pa_unit (check_in predicative_prop sg [] moved (vec_t NBool (numn 2))));
  show_normal sg "transport" (build [] moved);
  line ("transport ⇓ " ^ src sg moved);
  header "On a free m the transport stays neutral: a match on a fix that does not unfold";
  let names = names_of free_ctx in
  let open_moved = def "cast" [ v "A"; def "plus2" [ zero; v "m" ]; v "m"; def "plus2_zero" [ v "m" ]; v "v" ] in
  line ("context: " ^ pp_named_ctx ~depth free_ctx);
  line (pt ~depth ~names (term_in free_ctx open_moved));
  line ("  " ^ pe ~depth:6 ~names (normalize sg fuel (term_in free_ctx open_moved)));
  header "The branch nil of append with plus2, refused in lecture 7, checks after the backward transport";
  let names = names_of nil_ctx in
  let expected = vec_t (v "A") (def "plus2" [ zero; v "m" ]) in
  line ("context: " ^ pp_named_ctx ~depth nil_ctx ^ "; expected " ^ pt ~depth ~names (term_in nil_ctx expected));
  line ("ys: " ^ pa_unit ~depth ~names (check_in predicative_prop sg nil_ctx (v "ys") expected));
  line (pt ~depth ~names (term_in nil_ctx nil_branch) ^ ": " ^ pa_unit (check_in predicative_prop sg nil_ctx nil_branch expected));
  header "append2 with plus2 in its type, registered and computing";
  line ("append2 : " ^ pt ~depth (build [] append2_ty));
  line ("append2 ℕ 1 2 [7] [8; 9] ⇓ " ^ src sg (def "append2" [ nat; numn 1; numn 2; nvec [ 7 ]; nvec [ 8; 9 ] ]))

(* ── 6. Erasure ────────────────────────────────────────────────────── *)

let erased_def f =
  match efind_def se_demo f with Some b -> line (f ^ " ⇒ " ^ pet ~depth:20 b) | None -> line (f ^ ": absent")

let erun e = pec ~depth (eval_erased se_demo fuel e)

let erase_and_run label t a =
  match erase_closed t a with
  | Erased e ->
      line (label ^ " ⇒ " ^ pet ~depth e);
      line ("  " ^ erun e)
  | r -> line (label ^ ": " ^ per ~depth r)

let demo_erasure () =
  print_newline ();
  print_endline "Erasure: types and proofs become □, the positions of arguments stay.";
  header "The erased signature: declarations and instances by their kind";
  List.iter
    (fun e -> line (Pretty_erased.pp_eentry ~depth e))
    (List.rev
       (List.filter
          (function
            | Deptypes.EEInd d -> List.mem d.eind_name [ "Nat"; "Vec"; "eq"; "True"; "False"; "and"; "ex"; "AccP" ]
            | EEElim (d, _, _) -> List.mem d [ "Vec"; "eq"; "True"; "False"; "and"; "AccP" ]
            | _ -> false)
          se_demo));
  header "append and append_eq, with an extra proof of the length: the λ and □ that remain";
  erased_def "append";
  erased_def "append_eq";
  List.iter
    (fun e -> line (pet ~depth e); line ("  " ^ erun e))
    [ eapps (EConst "append") [ EBox; enum 1; enum 2; evec [ 7 ]; evec [ 8; 9 ] ];
      eapps (EConst "append_eq") [ EBox; enum 1; enum 2; enum 3; EBox; evec [ 7 ]; evec [ 8; 9 ] ] ];
  header "The transport is the identity on its last argument; proofs and families are □";
  List.iter erased_def [ "cast"; "cast_rect"; "sym"; "plus2_zero"; "Fam" ];
  erase_and_run "cast Bool (plus2 0 2) 2 (plus2_zero 2) [true; false]"
    (def "cast" [ NBool; def "plus2" [ zero; numn 2 ]; numn 2; def "plus2_zero" [ numn 2 ]; bvec ])
    (vec_t NBool (numn 2));
  header "choose : Πb:Bool. A → B → (if b then A else B), its type by a large elimination";
  line ("choose ⇒ "
        ^ per ~depth
            (erase_term predicative_prop sg_demo fuel (in_ctx types_ctx) (term_in types_ctx choose)
               (term_in types_ctx choose_ty)));
  header "strip (p : True) {struct p} := match p with I ⇒ 0 end, a fix on a proof";
  erased_def "strip";
  show_normal ~terms:true sg_demo "strip I under normal order" (build [] (def "strip" [ i_proof ]));
  line ("strip I ⇓ " ^ src sg_demo (def "strip" [ i_proof ]));
  erase_and_run "strip I" (def "strip" [ i_proof ]) nat;
  header "depth on AccP: no closed proof exists, the erased program runs on □";
  erased_def "depth";
  List.iter
    (fun f -> List.iter (fun k -> let e = eapps (EConst f) (depth_args k) in line (pet e ^ ": " ^ erun e)) [ 0; 3 ])
    [ "depth"; "depth_elim" ];
  header "Stuck: a match on □, the empty match, an empty eliminator";
  List.iter
    (fun e -> line (pet ~depth e ^ ": " ^ erun e))
    [ ECase ("Nat", EBox, [ enum 0; ELam (EVar 0) ]);
      EApp (ELam (ECase ("False", EBox, [])), EBox);
      eapps (EPrim ("False", Univ 0)) [ EBox; EBox ] ];
  header "Both evaluators on closed programs at observable types";
  List.iter
    (fun (t, a) ->
      line (pt ~depth (build [] t) ^ " : " ^ pt ~depth (build [] a));
      line ("  source: " ^ src sg_demo t);
      (match erase_closed t a with
       | Erased e -> line ("  erased: " ^ erun e)
       | r -> line ("  " ^ per ~depth r));
      line ("  related by the observation: " ^ string_of_bool (contract_on t a)))
    [ (def "plus" [ numn 2; numn 3 ], nat);
      (and_case, nat);
      (witness, witness_ty);
      (def "append" [ nat; numn 1; numn 2; nvec [ 7 ]; nvec [ 8; 9 ] ], vec_t nat (def "plus" [ numn 1; numn 2 ]));
      (def "append2" [ nat; numn 1; numn 2; nvec [ 7 ]; nvec [ 8; 9 ] ], vec_t nat (def "plus2" [ numn 1; numn 2 ])) ]

(* ── 7. Universes ─────────────────────────────────────────────────── *)

let demo_universes () =
  let open Universes in
  let open Pretty_univ in
  print_newline ();
  print_endline "The milestone of universes: level variables, constraints, cumulativity (a separate checker).";
  let model m = match pp_model m with "every level 0" -> "" | s -> "; model " ^ s in
  let ok_term = function
    | Ok ((t, []), m) -> "accepted: " ^ pp_uterm t ^ model m
    | Ok ((t, cs), m) -> "accepted: " ^ pp_uterm t ^ ", with " ^ pp_constrs cs ^ model m
    | Err e -> "refused: " ^ pp_uerror e
  in
  let ok_check = function
    | Ok ([], m) -> "accepted" ^ model m
    | Ok (cs, m) -> "accepted, with " ^ pp_constrs cs ^ model m
    | Err e -> "refused: " ^ pp_uerror e
  in
  let ok_decl = function
    | Ok (d, m) -> "accepted; its context: " ^ pp_constrs d.ud_cstrs ^ model m
    | Err e -> "refused: " ^ pp_uerror e
  in
  header "Unit at two levels: Below with Unit : Type₀ where lecture 7 needed Unit_1";
  line ("Below : " ^ pp_uterm below_type);
  line ("  := " ^ pp_uterm below_body);
  line ("with cumulativity: " ^ ok_decl (check_decl true [] fuel below_decl));
  line ("without it, as in lecture 7: " ^ ok_decl (check_decl false [] fuel below_decl));
  let below k = uapps (UConst ("Below", [])) [ const_nat; k ] in
  line ("tt : Below (λ_. ℕ) zero: " ^ ok_check (check_term true sg_below fuel [] [] Rigid UTt (below UZero)));
  line ("⟨zero, tt⟩ : Below (λ_. ℕ) (succ zero): "
        ^ ok_check (check_term true sg_below fuel [] [] Rigid (UPair (UZero, UTt)) (below (UApp (USucc, UZero)))));
  line ("ℕ : Type₁: " ^ ok_check (check_term true [] fuel [] [] Rigid UNat (USort l1)));
  line ("Type₁ : Type₁: " ^ ok_check (check_term true [] fuel [] [] Rigid (USort l1) (USort l1)));
  header "ΠA:Type u. A → A : Type (u+1)";
  line (ok_term (infer_term true [] fuel [ "u" ] [] Rigid (id_type u)));
  header "id@{u} : ΠA:Type u. A → A at two levels, and applied to itself";
  line ("id@{0} ℕ zero: " ^ ok_term (infer_term true sg_id fuel [] [] Rigid (uapps (UConst ("id", [ lzero ])) [ UNat; UZero ])));
  line ("id@{1} Type₀ ℕ: " ^ ok_term (infer_term true sg_id fuel [] [] Rigid (uapps (UConst ("id", [ l1 ])) [ USort lzero; UNat ])));
  line ("id@{u} (ΠA:Type u. A → A) id@{u}: " ^ ok_term (infer_term true sg_id fuel [ "u" ] [] Extensible (self_app [ u ])));
  line ("id (ΠA:Type u. A → A) id@{u}, a fresh instance ?0: "
        ^ ok_term (infer_term true sg_id fuel [ "u" ] [] Extensible (self_app [])));
  line ("idid := that term, with u < ?0 in its context; idid@{0 1}: "
        ^ ok_term (infer_term true sg_idid fuel [] [] Rigid (UConst ("idid", [ lzero; l1 ]))));
  line ("idid@{1 1}: " ^ ok_term (infer_term true sg_idid fuel [] [] Rigid (UConst ("idid", [ l1; l1 ]))));
  header "Type u : Type u";
  line ("in an extensible context: " ^ ok_check (check_term true [] fuel [ "u" ] [] Extensible (USort u) (USort u)));
  line ("in a rigid one: " ^ ok_check (check_term true [] fuel [ "u" ] [] Rigid (USort u) (USort u)));
  line ("Type u : Type (u+1): " ^ ok_check (check_term true [] fuel [ "u" ] [] Rigid (USort u) (USort (lsucc u))));
  header "Cycles: u ≤ v ≤ u accepted, u < v ≤ u refused; lifting does not allow lowering";
  line ("lower@{u v | u ≤ v, v ≤ u} : Type v → Type u: " ^ ok_decl (check_decl true [] fuel (lower_decl Rigid [ cle u v; cle v u ])));
  line ("lower@{u v | u < v, v ≤ u}: " ^ ok_decl (check_decl true [] fuel (lower_decl Rigid [ clt u v; cle v u ])));
  line ("lift@{u v | u ≤ v} : Type u → Type v: " ^ ok_decl (check_decl true [] fuel lift_decl));
  line ("lower@{u v | u ≤ v} : Type v → Type u: " ^ ok_decl (check_decl true [] fuel (lower_decl Rigid [ cle u v ])))

let () =
  demo_tables ();
  demo_prop ();
  demo_nat_rect ();
  demo_guard ();
  demo_plus2 ();
  demo_erasure ();
  demo_universes ()
