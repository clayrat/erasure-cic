(* Printing for erasure and its target.

   Erased terms have no types: a λ is named x, y, z, … whatever its
   domain was, a fix f, g, h.  [□] is the erased type or proof.  A
   constructor is printed by its name, the constructors of the primitives
   prim.Unit and prim.Bool as tt, true and false; an eliminator instance
   kept as a primitive as elimD[j], as in the source; a match without a
   motive as match x with b₁ | … end, its branches in the order of the
   constructors.  [depth] bounds the printed nesting as in pretty.ml. *)
open Deptypes
open Pretty

let eatomic = function EBox | EVar _ | EConst _ | ECtor _ | EPrim _ -> true | _ -> false

let rec pp_eat depth names level t =
  let paren wanted s = if level > wanted then "(" ^ s ^ ")" else s in
  if depth <= 1 && not (eatomic t) then "…"
  else
    let pp = pp_eat (depth - 1) in
    match t with
    | EBox -> "□"
    | EVar n -> lookup_name names n
    | ELam b ->
        let x = fresh term_names names in
        paren 0 ("λ" ^ x ^ ". " ^ pp (x :: names) 0 b)
    | EApp (f, a) -> paren 1 (pp names 1 f ^ " " ^ pp names 2 a)
    | EConst f -> f
    | ECtor (_, c) -> c
    | ECase (_, x, []) -> paren 0 ("match " ^ pp names 1 x ^ " with end")
    | ECase (_, x, bs) ->
        paren 0 ("match " ^ pp names 1 x ^ " with " ^ String.concat " | " (List.map (pp names 0) bs) ^ " end")
    | EFix (k, b) ->
        let f = fresh fix_names names in
        paren 0 ("fix " ^ f ^ " {struct " ^ string_of_int k ^ "} := " ^ pp (f :: names) 0 b)
    | EPair (a, b) -> "⟨" ^ pp names 0 a ^ ", " ^ pp names 0 b ^ "⟩"
    | EFst p -> paren 1 ("fst " ^ pp names 2 p)
    | ESnd p -> paren 1 ("snd " ^ pp names 2 p)
    | EPrim (d, s) -> pp_gref (Elim (d, s))

let pp_eterm ?(depth = max_int) ?(names = []) t = pp_eat depth names 0 t

let pp_ecbv ?(depth = max_int) = function
  | CbvValue t -> "value " ^ pp_eterm ~depth t
  | CbvStuck t -> "stuck at " ^ pp_eterm ~depth t
  | CbvOutOfFuel -> "out of fuel"

let pp_stage = function
  | AtArity -> "recognizing an arity"
  | AtSort -> "finding the sort of a type"
  | AtUnfold -> "unfolding a type"
  | AtType -> "inferring a type"

let pp_erase_error ?(depth = max_int) ?(names = []) e =
  let pp = pp_term ~depth ~names in
  match e with
  | XIllTyped (t, err) -> "the kernel rejects " ^ pp t ^ ": " ^ pp_error ~depth ~names err
  | XNotAType (t, k) -> pp t ^ " has type " ^ pp k ^ ", not a sort"
  | XShape (t, ty) -> pp t ^ " has type " ^ pp ty ^ ", of another shape"
  | XIllegalElim (d, s) ->
      "the elimination of " ^ d ^ " into " ^ pp_sort s ^ " is forbidden by its category"
  | XUnsupported t -> "erasure does not expect " ^ pp t
  | XInactive (d, s) -> "the instance " ^ pp_gref (Elim (d, s)) ^ " has no active rules"

let pp_erase_result ?(depth = max_int) ?(names = []) pp_value = function
  | Erased a -> "erased: " ^ pp_value a
  | NotErasable e -> "not erasable: " ^ pp_erase_error ~depth ~names e
  | UndecidedAt (st, t) -> "undecided: out of fuel " ^ pp_stage st ^ " at " ^ pp_term ~depth ~names t

let pp_kind = function
  | KData -> "data, on a constructor"
  | KSingleton -> "a singleton proposition, on anything"
  | KEmpty -> "an empty proposition, never"
  | KProp -> "into Prop only, never"

let pp_efield = function ENonRec -> "_" | ERec 0 -> "rec" | ERec m -> "rec/" ^ string_of_int m

let pp_eentry ?(depth = max_int) = function
  | EEInd d ->
      let count n one many = string_of_int n ^ " " ^ if n = 1 then one else many in
      let ctors =
        match d.eind_ctors with
        | [] -> "no constructors"
        | cs ->
            String.concat " | "
              (List.map
                 (fun c ->
                   match c.ector_fields with
                   | [] -> c.ector_name
                   | fs -> c.ector_name ^ " " ^ String.concat " " (List.map pp_efield fs))
                 cs)
      in
      Printf.sprintf "%s, %s, %s: %s; %s" d.eind_name (count d.eind_params "parameter" "parameters")
        (count d.eind_indices "index" "indices") ctors (pp_kind d.eind_kind)
  | EEElim (d, s, k) -> pp_gref (Elim (d, s)) ^ ": " ^ pp_kind k
  | EEDef (f, b) -> f ^ " := " ^ pp_eterm ~depth b
