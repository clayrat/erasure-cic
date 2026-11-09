(* Printing for the lecture on CIC, over pretty.ml of the kernel and
   pretty_ind.ml of the declarations.

   - Closed numerals of ℕ print as digits, in source terms (zero, succ …)
     and in erased ones; [known] closed terms, such as the Church
     numerals of the gist or nat_rect, print by a name.  Both only
     abbreviate the printing: the terms themselves are those of the
     extract.
   - A context given by names prints with them, outermost entry first.
   - The redexes of normal order are those of pretty_ind.ml, with ι of a
     match on a constructor (ι matchD) and the unfolding of a fix (fix)
     named apart; δ names its constant. *)
open Deptypes
open Pretty
open Pretty_ind

let rec nat_value = function
  | Const (Ctor ("Nat", "zero")) -> Some 0
  | App (Const (Ctor ("Nat", "succ")), n) -> Option.map (fun k -> k + 1) (nat_value n)
  | _ -> None

let map_sub f t =
  match t with
  | Srt _ | Var _ | Void | Unit | Tt | Bool | BTrue | BFalse | Const _ -> t
  | Pi (a, b) -> Pi (f a, f b)
  | Lam b -> Lam (f b)
  | App (g, a) -> App (f g, f a)
  | Ann (u, a) -> Ann (f u, f a)
  | ElimVoid (c, e) -> ElimVoid (f c, f e)
  | ElimUnit (c, x, u) -> ElimUnit (f c, f x, f u)
  | ElimBool (c, x, y, b) -> ElimBool (f c, f x, f y, f b)
  | Sigma (a, b) -> Sigma (f a, f b)
  | Pair (a, b) -> Pair (f a, f b)
  | Fst p -> Fst (f p)
  | Snd p -> Snd (f p)
  | Case (d, s, p, x, bs) -> Case (d, s, f p, f x, List.map f bs)
  | Fix (a, k, b) -> Fix (f a, k, f b)

let rec abbrev ?(known = []) t =
  match List.find_opt (fun (u, _) -> term_eqb t u) known with
  | Some (_, name) -> Const (Def name)
  | None -> (
      match nat_value t with
      | Some k -> Const (Def (string_of_int k))
      | None -> map_sub (abbrev ~known) t)

let abbrev_guard ?(known = []) = function
  | GPartialCall c -> GPartialCall (abbrev ~known c)
  | GNotSubterm (c, a) -> GNotSubterm (abbrev ~known c, abbrev ~known a)

let abbrev_error ?(known = []) e =
  let ab = abbrev ~known in
  match e with
  | ENoRule (t, s1, s2) -> ENoRule (ab t, s1, s2)
  | ENotASort (t, a) -> ENotASort (ab t, ab a)
  | ENotAPi (t, a) -> ENotAPi (ab t, ab a)
  | EMismatch (t, x, y) -> EMismatch (ab t, ab x, ab y)
  | EStuckType (t, x, y) -> EStuckType (ab t, ab x, ab y)
  | ECannotInfer t -> ECannotInfer (ab t)
  | ENoPrimitives t -> ENoPrimitives (ab t)
  | EBadFamily (c, x, y) -> EBadFamily (ab c, ab x, ab y)
  | ENoSigmaRule (t, s1, s2) -> ENoSigmaRule (ab t, s1, s2)
  | ENotASigma (t, a) -> ENotASigma (ab t, ab a)
  | ENoDecls t -> ENoDecls (ab t)
  | ENotInductive (x, d, a) -> ENotInductive (ab x, d, ab a)
  | EBranchCount (t, k, n) -> EBranchCount (ab t, k, n)
  | ENoStructArg (t, k, a) -> ENoStructArg (ab t, k, ab a)
  | EStructNotInductive (t, k, a) -> EStructNotInductive (ab t, k, ab a)
  | EFixBody (t, k) -> EFixBody (ab t, k)
  | ENotGuarded (t, g) -> ENotGuarded (ab t, abbrev_guard ~known g)
  | EUnboundVar _ | ENotInSystem _ | ETopSort _ | EUnknownConst _ | EElimSort _ -> e

(* Printers of terms, answers and results with the abbreviations. *)
let pt ?(depth = max_int) ?(names = []) ?(known = []) t = pp_term ~depth ~names (abbrev ~known t)

let pa ?(depth = max_int) ?(names = []) ?(known = []) = function
  | Accepted t -> "accepted: " ^ pt ~depth ~names ~known t
  | Rejected e -> "rejected: " ^ pp_error ~depth ~names (abbrev_error ~known e)
  | Undecided t -> "undecided: out of fuel while typing " ^ pt ~depth ~names ~known t

let pa_unit ?(depth = max_int) ?(names = []) ?(known = []) = function
  | Accepted () -> "accepted"
  | Rejected e -> "rejected: " ^ pp_error ~depth ~names (abbrev_error ~known e)
  | Undecided t -> "undecided: out of fuel while typing " ^ pt ~depth ~names ~known t

let pc ?(depth = max_int) ?(names = []) = function
  | CbvValue t -> "value " ^ pt ~depth ~names t
  | CbvStuck t -> "stuck at " ^ pt ~depth ~names t
  | CbvOutOfFuel -> "out of fuel"

let pe ?(depth = max_int) ?(names = []) ?(known = []) = function
  | NormalForm t -> "normal form " ^ pt ~depth ~names ~known t
  | StuckTerm t -> "stuck at " ^ pt ~depth ~names ~known t
  | OutOfFuel t -> "out of fuel at " ^ pt ~depth ~names ~known t

(* A context given by names, innermost entry first, printed outermost
   first. *)
let pp_named_ctx ?(depth = max_int) ?(known = []) g =
  let rec go = function
    | [] -> []
    | (x, a) :: rest -> go rest @ [ x ^ " : " ^ pt ~depth ~names:(List.map fst rest) ~known (term_in rest a) ]
  in
  match go g with [] -> "·" | es -> String.concat ", " es

(* ── Erased terms ── *)

let rec enat_value = function
  | ECtor ("Nat", "zero") -> Some 0
  | EApp (ECtor ("Nat", "succ"), n) -> Option.map (fun k -> k + 1) (enat_value n)
  | _ -> None

let rec eabbrev t =
  match enat_value t with
  | Some k -> EConst (string_of_int k)
  | None -> (
      match t with
      | EBox | EVar _ | EConst _ | ECtor _ | EPrim _ -> t
      | ELam b -> ELam (eabbrev b)
      | EApp (f, a) -> EApp (eabbrev f, eabbrev a)
      | ECase (d, x, bs) -> ECase (d, eabbrev x, List.map eabbrev bs)
      | EFix (k, b) -> EFix (k, eabbrev b)
      | EPair (a, b) -> EPair (eabbrev a, eabbrev b)
      | EFst p -> EFst (eabbrev p)
      | ESnd p -> ESnd (eabbrev p))

let pet ?(depth = max_int) t = Pretty_erased.pp_eterm ~depth (eabbrev t)

let pec ?(depth = max_int) = function
  | CbvValue t -> "value " ^ pet ~depth t
  | CbvStuck t -> "stuck at " ^ pet ~depth t
  | CbvOutOfFuel -> "out of fuel"

let per ?(depth = max_int) ?(names = []) = function
  | Erased e -> "erased: " ^ pet ~depth e
  | NotErasable e -> "not erasable: " ^ Pretty_erased.pp_erase_error ~depth ~names e
  | UndecidedAt (st, t) ->
      "undecided: out of fuel " ^ Pretty_erased.pp_stage st ^ " at " ^ pt ~depth ~names t

(* ── Redexes of normal order, with match and fix ── *)

let cic_redex sg t =
  match t with
  | Case (d, _, _, _, _) when case_iota sg t <> None -> Some ("ι match" ^ d)
  | App _ -> (
      match redex sg t with
      | Some r -> Some r
      | None -> if fix_unfold t <> None then Some "fix" else None)
  | _ -> redex sg t

let cic_components t t' =
  match (t, t') with
  | Case (_, _, p, x, bs), Case (_, _, p', x', bs') when List.length bs = List.length bs' ->
      (p, p') :: (x, x') :: List.combine bs bs'
  | Fix (a, _, b), Fix (a', _, b') -> [ (a, a'); (b, b') ]
  | _ -> components t t'

let rec cic_step sg t t' =
  match cic_redex sg t with
  | Some r -> r
  | None -> (
      match List.filter (fun (a, b) -> not (term_eqb a b)) (cic_components t t') with
      | [ (a, b) ] -> cic_step sg a b
      | _ -> "?")

let rec cic_redexes sg = function
  | a :: (b :: _ as rest) -> cic_step sg a b :: cic_redexes sg rest
  | _ -> []
