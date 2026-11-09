(* Printing for the milestone of universes (Universes/ of this project).

   A level is the maximum of atoms with offsets: 0, a named variable u,
   a fresh instance variable ?i; u+1 is the successor, max(u, v+1) a
   maximum, a closed level its number.  A constraint l + k ≤ r prints as
   l ≤ r for k = 0 and l < r for k = 1.  An edge a + w ≤ b of the graph
   prints the same way, a cycle as the chain of its edges.  Terms name
   their binders as pretty.ml: A, B, … for a domain that is a sort, x, y,
   … otherwise; a Π whose body does not use its variable is an arrow. *)
open Universes

let subscript = Pretty.subscript

let pp_atom = function LZero -> "0" | LVar u -> u | LInst i -> "?" ^ string_of_int i

let pp_elem (a, k) =
  match a with
  | LZero -> string_of_int k
  | _ -> if k = 0 then pp_atom a else pp_atom a ^ "+" ^ string_of_int k

let pp_level = function
  | [] -> "0"
  | [ x ] -> pp_elem x
  | xs -> "max(" ^ String.concat ", " (List.map pp_elem xs) ^ ")"

let pp_sort_level l =
  match l with
  | [] -> "Type" ^ subscript 0
  | [ (LZero, k) ] -> "Type" ^ subscript k
  | [ (_, 0) ] -> "Type " ^ pp_level l
  | _ -> "Type (" ^ pp_level l ^ ")"

let pp_le lhs off rhs =
  if off = 0 then lhs ^ " ≤ " ^ rhs
  else if off = 1 then lhs ^ " < " ^ rhs
  else lhs ^ " + " ^ string_of_int off ^ " ≤ " ^ rhs

let pp_constr c = pp_le (pp_level c.c_lhs) c.c_off (pp_level c.c_rhs)
let pp_constrs = function [] -> "none" | cs -> String.concat ", " (List.map pp_constr cs)
let pp_edge ((a, w), b) = pp_le (pp_atom a) w (pp_atom b)

(* A cycle a₀ ≤ a₁ < a₂ … ≤ a₀ as one chain. *)
let pp_cycle = function
  | [] -> "the empty cycle"
  | ((a, _), _) :: _ as es ->
      List.fold_left
        (fun s ((_, w), b) -> s ^ (if w = 0 then " ≤ " else if w = 1 then " < " else " +" ^ string_of_int w ^ " ≤ ") ^ pp_atom b)
        (pp_atom a) es

let pp_model m =
  match List.filter (fun (a, _) -> a <> LZero) m with
  | [] -> "every level 0"
  | m' -> String.concat ", " (List.map (fun (a, n) -> pp_atom a ^ " = " ^ string_of_int n) m')

let pp_cerror = function
  | CNotInFragment c -> pp_constr c ^ " is outside the supported fragment"
  | CCycle es -> "the cycle " ^ pp_cycle es ^ " of positive weight"
  | CNotImplied (c, Some m) -> pp_constr c ^ " is not implied; counter-model " ^ pp_model m
  | CNotImplied (c, None) -> pp_constr c ^ " is not implied"
  | CUnsupported c -> pp_constr c ^ ": a maximum on the right, outside the fragment"
  | CUnknown -> "the graph gives no verdict"

let rec occurs k = function
  | UVar n -> n = k
  | UPi (a, b) | USigma (a, b) -> occurs k a || occurs (k + 1) b
  | ULam b -> occurs (k + 1) b
  | UApp (f, a) | UAnn (f, a) | UPair (f, a) -> occurs k f || occurs k a
  | UFst p | USnd p -> occurs k p
  | _ -> false

let rec pp_u names level t =
  let paren wanted s = if level > wanted then "(" ^ s ^ ")" else s in
  let binder a = match a with USort _ -> Pretty.fresh Pretty.type_names names | _ -> Pretty.fresh Pretty.term_names names in
  match t with
  | UVar n -> Pretty.lookup_name names n
  | USort l -> paren 1 (pp_sort_level l)
  | UPi (a, b) when not (occurs 0 b) -> paren 0 (pp_u names 1 a ^ " → " ^ pp_u ("_" :: names) 0 b)
  | UPi (a, b) ->
      let x = binder a in
      paren 0 ("Π" ^ x ^ ":" ^ pp_u names 0 a ^ ". " ^ pp_u (x :: names) 0 b)
  | ULam b ->
      let x = Pretty.fresh Pretty.term_names names in
      paren 0 ("λ" ^ x ^ ". " ^ pp_u (x :: names) 0 b)
  | UApp (f, a) -> paren 1 (pp_u names 1 f ^ " " ^ pp_u names 2 a)
  | UAnn (u, a) -> "(" ^ pp_u names 1 u ^ " : " ^ pp_u names 0 a ^ ")"
  | UConst (c, []) -> c
  | UConst (c, inst) -> c ^ "@{" ^ String.concat " " (List.map pp_level inst) ^ "}"
  | UNat -> "ℕ"
  | UZero -> "zero"
  | USucc -> "succ"
  | UElimNat l -> "elimNat@{" ^ pp_level l ^ "}"
  | UUnit -> "Unit"
  | UTt -> "tt"
  | USigma (a, b) when not (occurs 0 b) -> paren 0 (pp_u names 1 a ^ " × " ^ pp_u ("_" :: names) 1 b)
  | USigma (a, b) ->
      let x = binder a in
      paren 0 ("Σ" ^ x ^ ":" ^ pp_u names 0 a ^ ". " ^ pp_u (x :: names) 0 b)
  | UPair (a, b) -> "⟨" ^ pp_u names 0 a ^ ", " ^ pp_u names 0 b ^ "⟩"
  | UFst p -> paren 1 ("fst " ^ pp_u names 2 p)
  | USnd p -> paren 1 ("snd " ^ pp_u names 2 p)

let pp_uterm ?(names = []) t = pp_u names 0 t

let pp_uerror = function
  | UUnbound n -> "unbound variable #" ^ string_of_int n
  | UUnknownConst c -> "unknown constant " ^ c
  | UBadInstance c -> c ^ ": an instance of the wrong length"
  | UNeedsInstance c -> c ^ " needs an instance: a rigid context takes no fresh level"
  | UUnboundLevel a -> "the level " ^ pp_atom a ^ " is not in the context"
  | UNotASort (t, a) -> pp_uterm t ^ " has type " ^ pp_uterm a ^ ", not a sort"
  | UNotAPi (t, a) -> pp_uterm t ^ " has type " ^ pp_uterm a ^ ", not a Π-type"
  | UNotASigma (t, a) -> pp_uterm t ^ " has type " ^ pp_uterm a ^ ", not a Σ-type"
  | UMismatch (a, b) -> pp_uterm a ^ " is not " ^ pp_uterm b
  | UCannotInfer t -> "cannot infer the type of " ^ pp_uterm t
  | UDuplicate c -> c ^ " is declared twice"
  | ULevels e -> pp_cerror e
  | UOutOfFuel -> "out of fuel"
