(* The target of erasure and its evaluator, by hand, after Erasure/Target.v.

   Erased terms have no types: variables, λ, application, □, δ-constants,
   constructors, a match without its motive, a fix without its type,
   pairs, and the eliminator instances of lecture 7 kept as primitives.
   A declaration keeps what computation needs of it: the number of its
   parameters and indices, its constructors with the shape of their
   fields, and how it computes when eliminated into a type.

   The evaluator is weak and by value, as eval_src of the kernel: a value
   is a λ, □, a constructor applied to values, a pair of values, a fix or
   an eliminator short of its arguments.  □ applied to a value is □; a
   match on □ is stuck; a fix unfolds as soon as it has k + 1 arguments,
   □ included; a saturated eliminator computes by the kind of its
   declaration — on a constructor for data, on anything for a singleton
   proposition with □ for the fields, never for an empty one.  The budget
   bounds the depth of the evaluation, as in Rocq. *)

type sort = Pts_native.sort

type eterm =
  | EBox
  | EVar of int
  | ELam of eterm
  | EApp of eterm * eterm
  | EConst of string
  | ECtor of string * string
  | ECase of string * eterm * eterm list
  | EFix of int * eterm
  | EPair of eterm * eterm
  | EFst of eterm
  | ESnd of eterm
  | EPrim of string * sort

type efield = ENonRec | ERec of int
type ector = { ector_name : string; ector_fields : efield list }
type elim_kind = KData | KSingleton | KEmpty | KProp

type eind = {
  eind_name : string;
  eind_params : int;
  eind_indices : int;
  eind_ctors : ector list;
  eind_kind : elim_kind;
}

type eentry = EEInd of eind | EEElim of string * sort * elim_kind | EEDef of string * eterm
type esignature = eentry list (* newest first *)

let prim_unit = "prim.Unit"
let prim_bool = "prim.Bool"
let prim_void = "prim.Void"

let prim_entries =
  [ EEInd { eind_name = prim_unit; eind_params = 0; eind_indices = 0;
            eind_ctors = [ { ector_name = "tt"; ector_fields = [] } ]; eind_kind = KData };
    EEInd { eind_name = prim_bool; eind_params = 0; eind_indices = 0;
            eind_ctors = [ { ector_name = "true"; ector_fields = [] }; { ector_name = "false"; ector_fields = [] } ];
            eind_kind = KData };
    EEInd { eind_name = prim_void; eind_params = 0; eind_indices = 0; eind_ctors = []; eind_kind = KData } ]

(* ** Renaming and substitution *)

let rec rename r = function
  | EVar n -> EVar (r n)
  | ELam b -> ELam (rename (up r) b)
  | EApp (f, a) -> EApp (rename r f, rename r a)
  | ECase (d, x, bs) -> ECase (d, rename r x, List.map (rename r) bs)
  | EFix (k, b) -> EFix (k, rename (up r) b)
  | EPair (a, b) -> EPair (rename r a, rename r b)
  | EFst p -> EFst (rename r p)
  | ESnd p -> ESnd (rename r p)
  | (EBox | EConst _ | ECtor _ | EPrim _) as t -> t

and up r n = if n = 0 then 0 else r (n - 1) + 1

let lift k t = rename (fun n -> n + k) t

let rec subst sb = function
  | EVar n -> sb n
  | ELam b -> ELam (subst (up_subst sb) b)
  | EApp (f, a) -> EApp (subst sb f, subst sb a)
  | ECase (d, x, bs) -> ECase (d, subst sb x, List.map (subst sb) bs)
  | EFix (k, b) -> EFix (k, subst (up_subst sb) b)
  | EPair (a, b) -> EPair (subst sb a, subst sb b)
  | EFst p -> EFst (subst sb p)
  | ESnd p -> ESnd (subst sb p)
  | (EBox | EConst _ | ECtor _ | EPrim _) as t -> t

and up_subst sb n = if n = 0 then EVar 0 else lift 1 (sb (n - 1))

let subst1 body u = subst (fun n -> if n = 0 then u else EVar (n - 1)) body
let apps head args = List.fold_left (fun f a -> EApp (f, a)) head args

let spine t =
  let rec go t args = match t with EApp (f, a) -> go f (a :: args) | head -> (head, args) in
  go t []

let rec lams n b = if n = 0 then b else ELam (lams (n - 1) b)
let vars n = List.init n (fun i -> EVar (n - 1 - i))

let rec take n = function x :: l when n > 0 -> x :: take (n - 1) l | _ -> []
let rec drop n l = if n <= 0 then l else match l with [] -> [] | _ :: l' -> drop (n - 1) l'

(* ** The signature *)

let find_ind se d = List.find_map (function EEInd i when i.eind_name = d -> Some i | _ -> None) se
let find_elim se d s = List.find_map (function EEElim (d', s', k) when d' = d && s' = s -> Some k | _ -> None) se
let find_def se f = List.find_map (function EEDef (f', b) when f' = f -> Some b | _ -> None) se

let find_ctor cs c =
  let rec go i = function [] -> None | cd :: cs -> if cd.ector_name = c then Some (i, cd) else go (i + 1) cs in
  go 0 cs

(* ** ι *)

(* A match on a constructor of its declaration: the branch applied to the
   fields, the parameters skipped. *)
let case_iota se d v bs =
  match spine v with
  | ECtor (d', c), args when d' = d -> (
      match find_ind se d with
      | Some i -> (
          match find_ctor i.eind_ctors c with
          | Some (k, cd) when List.length args = i.eind_params + List.length cd.ector_fields ->
              Option.map (fun b -> apps b (drop i.eind_params args)) (List.nth_opt bs k)
          | _ -> None)
      | None -> None)
  | _ -> None

(* Parameters, motive, methods, indices, object. *)
let arity i = i.eind_params + 1 + List.length i.eind_ctors + i.eind_indices + 1

(* The hypothesis of a recursive field a with m positions:
   λȳ. elim_D[s] pre □… (a ȳ), the indices □. *)
let hyp d s pre q m a =
  lams m (apps (EPrim (d, s)) (List.map (lift m) pre @ List.init q (fun _ -> EBox) @ [ apps (lift m a) (vars m) ]))

let rec iota_args d s pre q fields xs =
  match (fields, xs) with
  | ENonRec :: fields', a :: xs' -> a :: iota_args d s pre q fields' xs'
  | ERec m :: fields', a :: xs' -> a :: hyp d s pre q m a :: iota_args d s pre q fields' xs'
  | _ -> []

(* A saturated spine of an eliminator, by the kind of its declaration. *)
let elim_iota se t =
  match spine t with
  | EPrim (d, s), args -> (
      match (find_elim se d s, find_ind se d) with
      | Some kind, Some i when List.length args = arity i -> (
          let p = i.eind_params and k = List.length i.eind_ctors and q = i.eind_indices in
          let pre = take (p + 1 + k) args in
          let methods = take k (drop (p + 1) args) in
          match kind with
          | KData -> (
              match spine (List.nth args (List.length args - 1)) with
              | ECtor (d', c), xa when d' = d -> (
                  match find_ctor i.eind_ctors c with
                  | Some (j, cd) when List.length xa = p + List.length cd.ector_fields ->
                      Option.map (fun m -> apps m (iota_args d s pre q cd.ector_fields (drop p xa))) (List.nth_opt methods j)
                  | _ -> None)
              | _ -> None)
          | KSingleton -> (
              match (i.eind_ctors, methods) with
              | [ cd ], [ m ] ->
                  let n = List.length cd.ector_fields in
                  Some (apps m (iota_args d s pre q cd.ector_fields (List.init n (fun _ -> EBox))))
              | _ -> None)
          | KEmpty | KProp -> None)
      | _ -> None)
  | _ -> None

let elim_partial se t =
  match spine t with
  | EPrim (d, s), args -> (
      match (find_elim se d s, find_ind se d) with
      | Some _, Some i -> List.length args < arity i
      | _ -> false)
  | _ -> false

(* ** Evaluation *)

type cbv_result = CbvValue of eterm | CbvStuck of eterm | CbvOutOfFuel

let rec eval se fuel t =
  if fuel = 0 then CbvOutOfFuel
  else
    let fuel = fuel - 1 in
    match t with
    | EBox | ELam _ | EFix _ | ECtor _ | EPrim _ -> CbvValue t
    | EVar _ -> CbvStuck t
    | EConst f -> ( match find_def se f with Some b -> eval se fuel b | None -> CbvStuck t)
    | EApp (g, a) -> (
        match eval se fuel g with
        | CbvValue vg -> (
            match eval se fuel a with
            | CbvValue va -> apply se fuel vg va
            | r -> r)
        | r -> r)
    | EPair (a, b) -> (
        match eval se fuel a with
        | CbvValue va -> ( match eval se fuel b with CbvValue vb -> CbvValue (EPair (va, vb)) | r -> r)
        | r -> r)
    | EFst p -> (
        match eval se fuel p with
        | CbvValue (EPair (a, _)) -> CbvValue a
        | CbvValue v -> CbvStuck (EFst v)
        | r -> r)
    | ESnd p -> (
        match eval se fuel p with
        | CbvValue (EPair (_, b)) -> CbvValue b
        | CbvValue v -> CbvStuck (ESnd v)
        | r -> r)
    | ECase (d, x, bs) -> (
        match eval se fuel x with
        | CbvValue v -> ( match case_iota se d v bs with Some r -> eval se fuel r | None -> CbvStuck (ECase (d, v, bs)))
        | r -> r)

(* A value applied to a value: β, □, a fix with its arguments, an
   eliminator, a constructor; anything else is stuck. *)
and apply se fuel vg va =
  match vg with
  | ELam b -> eval se fuel (subst1 b va)
  | EBox -> CbvValue EBox
  | _ -> (
      let u = EApp (vg, va) in
      match spine u with
      | EFix (k, b), args ->
          let n = List.length args in
          if n = k + 1 then eval se fuel (apps (subst1 b (EFix (k, b))) args)
          else if n < k + 1 then CbvValue u
          else CbvStuck u
      | EPrim _, _ -> (
          match elim_iota se u with
          | Some r -> eval se fuel r
          | None -> if elim_partial se u then CbvValue u else CbvStuck u)
      | ECtor _, _ -> CbvValue u
      | _ -> CbvStuck u)
