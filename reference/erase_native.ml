(* Erasure with known types, by hand, after Erasure/Erase.v, on the
   kernel's native reference.

   At every subterm, first the decision: the type unfolds to an arity (a
   sort, or a Π whose codomain is an arity), or its sort is Prop; then
   the term is □.  Otherwise the walk follows the shape of the term,
   passing known types down: a λ at a Π, a pair at a Σ, an application by
   the type of its function, a match by the types of its branches, a fix
   by its own type.  A match on a proposition is a singleton (its branch
   applied to □ for each field) or empty (no branches); any other
   elimination of a proposition into a type is refused, or kept on data in
   the demonstration of BypassElim.  The sort of a type is found from its
   weak-head form, without inferring its subterms.  Running out of fuel
   on the way is UndecidedAt with the stage it happened in, not a guess.

   The types of subterms come from the kernel's [infer], in a context
   taken as checked ([run_infer_open]), as in Rocq. *)

open Pts_native
module T = Eval_erased_native

type stage = AtArity | AtSort | AtUnfold | AtType

type error =
  | XIllTyped of term * Pts_native.error
  | XNotAType of term * term
  | XShape of term * term
  | XIllegalElim of string * sort
  | XUnsupported of term
  | XInactive of string * sort

type 'a erase_result = Erased of 'a | NotErasable of error | UndecidedAt of stage * term

type failure = Fail of error | Short of stage * term

let ( let* ) = Result.bind
let fail e = Error (Fail e)

let kind_of d =
  if d.ind_sort = Prp then
    match (d.ind_elim, d.ind_ctors) with
    | AllSorts, [] -> T.KEmpty
    | AllSorts, [ _ ] -> T.KSingleton
    | _ -> T.KProp
  else T.KData

let efield_of = function FArg _ -> T.ENonRec | FRec (domains, _) -> T.ERec (List.length domains)

let erase_ind d =
  { T.eind_name = d.ind_name;
    eind_params = List.length d.ind_params;
    eind_indices = List.length d.ind_indices;
    eind_ctors = List.map (fun c -> { T.ector_name = c.ctor_name; ector_fields = List.map efield_of c.ctor_fields }) d.ind_ctors;
    eind_kind = kind_of d }

(* The type of a variable, lifted to the context: [lookup] of Syntax.v. *)
let lookup_ctx g n = match List.nth_opt g n with Some a -> Some (lift (n + 1) a) | None -> None

let erasure spec sg fuel strict =
  let infer g t =
    match snd (run_infer_open ~sg spec fuel g t) with
    | Accepted a -> Ok a
    | Rejected e -> fail (XIllTyped (t, e))
    | Undecided u -> Error (Short (AtType, u))
  in
  let whnf st t = match whnf ~sg fuel t with HeadForm v -> Ok v | HeadOutOfFuel u -> Error (Short (st, u)) in
  let rec is_arity n t =
    if n = 0 then Error (Short (AtArity, t))
    else
      let* v = whnf AtArity t in
      match v with Srt _ -> Ok true | Pi (_, b) -> is_arity (n - 1) b | _ -> Ok false
  in
  let head_type g h =
    match h with
    | Var n -> ( match lookup_ctx g n with Some a -> Ok a | None -> fail (XIllTyped (h, EUnboundVar n)))
    | Const r -> ( match sig_type sg r with Some a -> Ok a | None -> fail (XIllTyped (h, EUnknownConst r)))
    | Fix (a, _, _) -> Ok a
    | _ -> infer g h
  in
  (* [h] applied to [args]: its Π peeled, each codomain instantiated. *)
  let rec instantiate h = function
    | [] -> Ok h
    | a :: args -> (
        let* v = whnf AtSort h in
        match v with Pi (_, b) -> instantiate (subst1 b a) args | _ -> fail (XShape (a, v)))
  in
  let sort_at t k =
    let* v = whnf AtSort k in
    match v with Srt s -> Ok s | _ -> fail (XNotAType (t, v))
  in
  let rec sort_of n g t =
    if n = 0 then Error (Short (AtSort, t))
    else
      let* v = whnf AtSort t in
      let bad = fail (XNotAType (t, v)) in
      let rule of_rule a b =
        let* s1 = sort_of (n - 1) g a in
        let* s2 = sort_of (n - 1) (a :: g) b in
        match of_rule s1 s2 with Some s3 -> Ok s3 | None -> bad
      in
      match v with
      | Srt s -> ( match spec.axiom s with Some s' -> Ok s' | None -> bad)
      | Pi (a, b) -> rule spec.product a b
      | Sigma (a, b) -> rule spec.sigma a b
      | Void | Unit | Bool -> ( match spec.primitive_sort with Some s0 -> Ok s0 | None -> bad)
      | _ -> (
          let head, args = spine v in
          match head with
          | Const (Ind d) -> ( match find_ind sg d with Some i -> Ok i.ind_sort | None -> bad)
          | Case (d, _, p, x, _) -> (
              match find_ind sg d with
              | Some i ->
                  let* xt = infer g x in
                  let* xv = whnf AtSort xt in
                  let us = drop (List.length i.ind_params) (snd (spine xv)) in
                  let* k = instantiate (apps p (us @ [ x ])) args in
                  sort_at t k
              | None -> bad)
          | h ->
              let* ht = head_type g h in
              let* k = instantiate ht args in
              sort_at t k)
  in
  let erasable g t =
    let* a = is_arity fuel t in
    if a then Ok true
    else
      let* s = sort_of fuel g t in
      Ok (s = Prp)
  in
  let as_pi t ty = let* v = whnf AtUnfold ty in match v with Pi (a, b) -> Ok (a, b) | _ -> fail (XShape (t, v)) in
  let as_sigma t ty = let* v = whnf AtUnfold ty in match v with Sigma (a, b) -> Ok (a, b) | _ -> fail (XShape (t, v)) in
  let params x xt d i =
    let* v = whnf AtUnfold xt in
    let p = List.length i.ind_params in
    let head, args = spine v in
    if head = Const (Ind d) && List.length args = p + List.length i.ind_indices then Ok (take p args)
    else fail (XShape (x, v))
  in
  let rec erase_each t f cs bs =
    match (cs, bs) with
    | c :: cs', b :: bs' ->
        let* b' = f c b in
        let* rest = erase_each t f cs' bs' in
        Ok (b' :: rest)
    | [], [] -> Ok []
    | _ -> fail (XUnsupported t)
  in
  let rec erase g t ty =
    let* er = erasable g ty in
    if er then Ok T.EBox
    else
      match t with
      | Var n -> Ok (T.EVar n)
      | Lam b ->
          let* a, bt = as_pi t ty in
          let* b' = erase (a :: g) b bt in
          Ok (T.ELam b')
      | App (f, a) ->
          let* ft = infer g f in
          let* dom, _ = as_pi f ft in
          let* f' = erase g f ft in
          let* a' = erase g a dom in
          Ok (T.EApp (f', a'))
      | Ann (u, a) -> erase g u a
      | Const (Def f) -> Ok (T.EConst f)
      | Const (Ctor (d, c)) -> Ok (T.ECtor (d, c))
      | Const (Elim (d, s)) -> Ok (T.EPrim (d, s))
      | Tt -> Ok (T.ECtor (T.prim_unit, "tt"))
      | BTrue -> Ok (T.ECtor (T.prim_bool, "true"))
      | BFalse -> Ok (T.ECtor (T.prim_bool, "false"))
      | ElimUnit (c, m, u) ->
          let* m' = erase g m (App (c, Tt)) in
          let* u' = erase g u Unit in
          Ok (T.ECase (T.prim_unit, u', [ m' ]))
      | ElimBool (c, x, y, b) ->
          let* x' = erase g x (App (c, BTrue)) in
          let* y' = erase g y (App (c, BFalse)) in
          let* b' = erase g b Bool in
          Ok (T.ECase (T.prim_bool, b', [ x'; y' ]))
      | ElimVoid (_, e) ->
          let* e' = erase g e Void in
          Ok (T.ECase (T.prim_void, e', []))
      | Pair (a, b) ->
          let* ta, tb = as_sigma t ty in
          let* a' = erase g a ta in
          let* b' = erase g b (subst1 tb a) in
          Ok (T.EPair (a', b'))
      | Fst q ->
          let* qt = infer g q in
          let* _ = as_sigma q qt in
          let* q' = erase g q qt in
          Ok (T.EFst q')
      | Snd q ->
          let* qt = infer g q in
          let* _ = as_sigma q qt in
          let* q' = erase g q qt in
          Ok (T.ESnd q')
      | Case (d, s, p, x, bs) -> (
          match find_ind sg d with
          | None -> fail (XUnsupported t)
          | Some i ->
              let* xt = infer g x in
              let* ps = params x xt d i in
              let* x' = erase g x xt in
              let* bs' = erase_each t (fun c b -> erase g b (case_branch_type i ps p c)) i.ind_ctors bs in
              if i.ind_sort = Prp then
                match (i.ind_elim, i.ind_ctors, bs') with
                | AllSorts, [], [] -> Ok (T.ECase (d, x', []))
                | AllSorts, [ c ], [ b' ] -> Ok (T.apps b' (List.map (fun _ -> T.EBox) c.ctor_fields))
                | _ -> if strict then fail (XIllegalElim (d, s)) else Ok (T.ECase (d, x', bs'))
              else Ok (T.ECase (d, x', bs')))
      | Fix (a, k, b) ->
          let* b' = erase (a :: g) b (lift 1 a) in
          Ok (T.EFix (k, b'))
      | Srt _ | Pi _ | Sigma _ | Void | Unit | Bool | Const (Ind _) -> fail (XUnsupported t)
  in
  let erase_entry = function
    | EInd d -> Ok (T.EEInd (erase_ind d))
    | EElim (d, s, _, active) -> (
        if not active then fail (XInactive (d, s))
        else
          match find_ind sg d with
          | None -> fail (XUnsupported (Const (Elim (d, s))))
          | Some i -> (
              if s = Prp then Ok (T.EEElim (d, s, T.KProp))
              else
                match kind_of i with
                | T.KProp -> if strict then fail (XIllegalElim (d, s)) else Ok (T.EEElim (d, s, T.KData))
                | k -> Ok (T.EEElim (d, s, k))))
    | EDef (f, a, b) ->
        let* b' = erase [] b a in
        Ok (T.EEDef (f, b'))
  in
  (* Oldest entry first: the signature is newest first. *)
  let rec erase_entries = function
    | [] -> Ok T.prim_entries
    | e :: es ->
        let* se = erase_entries es in
        let* e' = erase_entry e in
        Ok (e' :: se)
  in
  (erase, erase_entries)

let to_result = function
  | Ok a -> Erased a
  | Error (Fail e) -> NotErasable e
  | Error (Short (st, t)) -> UndecidedAt (st, t)

let erase_term ?(strict = true) spec sg fuel g t ty =
  let erase, _ = erasure spec sg fuel strict in
  to_result (erase g t ty)

let erase_env ?(strict = true) spec sg fuel =
  let _, entries = erasure spec sg fuel strict in
  to_result (entries sg)
