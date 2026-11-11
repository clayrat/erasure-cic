(* Conversions between the native erasure and the extract, for the
   differential test: signatures of the kernel from the extract (the
   lecture's signatures are built by the extracted registration), erased
   terms, signatures and results both ways where a comparison needs them.
   The kernel's terms, sorts, errors and guard results convert by the
   kernel's [Extracted]. *)

module X = Deptypes
module N = Pts_native
module T = Eval_erased_native
module E = Erase_native

open Extracted

(* ** Signatures of the kernel, from the extract *)

let elim_class_of_extracted = function X.PropOnly -> N.PropOnly | X.AllSorts -> N.AllSorts

let field_of_extracted = function
  | X.FArg a -> N.FArg (term_of_extracted a)
  | X.FRec (domains, indices) -> N.FRec (List.map term_of_extracted domains, List.map term_of_extracted indices)

let ctor_of_extracted c =
  { N.ctor_name = c.X.ctor_name;
    ctor_fields = List.map field_of_extracted c.X.ctor_fields;
    ctor_indices = List.map term_of_extracted c.X.ctor_indices }

let desc_of_extracted d =
  { N.ind_name = d.X.ind_name;
    ind_params = List.map term_of_extracted d.X.ind_params;
    ind_indices = List.map term_of_extracted d.X.ind_indices;
    ind_sort = sort_of_extracted d.X.ind_sort;
    ind_elim = elim_class_of_extracted d.X.ind_elim;
    ind_ctors = List.map ctor_of_extracted d.X.ind_ctors }

let entry_of_extracted = function
  | X.EInd d -> N.EInd (desc_of_extracted d)
  | X.EElim (d, s, ty, active) -> N.EElim (d, sort_of_extracted s, term_of_extracted ty, active)
  | X.EDef (f, ty, body) -> N.EDef (f, term_of_extracted ty, term_of_extracted body)

(* The extracted signature is its list of entries, newest first, like the
   native one. *)
let signature_of_extracted (sg : X.signature) : N.signature = List.map entry_of_extracted sg

(* ** Erased terms and signatures *)

let rec eterm_to_extracted = function
  | T.EBox -> X.EBox
  | T.EVar n -> X.EVar n
  | T.ELam b -> X.ELam (eterm_to_extracted b)
  | T.EApp (f, a) -> X.EApp (eterm_to_extracted f, eterm_to_extracted a)
  | T.EConst f -> X.EConst f
  | T.ECtor (d, c) -> X.ECtor (d, c)
  | T.ECase (d, x, bs) -> X.ECase (d, eterm_to_extracted x, List.map eterm_to_extracted bs)
  | T.EFix (k, b) -> X.EFix (k, eterm_to_extracted b)
  | T.EPair (a, b) -> X.EPair (eterm_to_extracted a, eterm_to_extracted b)
  | T.EFst p -> X.EFst (eterm_to_extracted p)
  | T.ESnd p -> X.ESnd (eterm_to_extracted p)
  | T.EPrim (d, s) -> X.EPrim (d, sort_to_extracted s)

let rec eterm_of_extracted = function
  | X.EBox -> T.EBox
  | X.EVar n -> T.EVar n
  | X.ELam b -> T.ELam (eterm_of_extracted b)
  | X.EApp (f, a) -> T.EApp (eterm_of_extracted f, eterm_of_extracted a)
  | X.EConst f -> T.EConst f
  | X.ECtor (d, c) -> T.ECtor (d, c)
  | X.ECase (d, x, bs) -> T.ECase (d, eterm_of_extracted x, List.map eterm_of_extracted bs)
  | X.EFix (k, b) -> T.EFix (k, eterm_of_extracted b)
  | X.EPair (a, b) -> T.EPair (eterm_of_extracted a, eterm_of_extracted b)
  | X.EFst p -> T.EFst (eterm_of_extracted p)
  | X.ESnd p -> T.ESnd (eterm_of_extracted p)
  | X.EPrim (d, s) -> T.EPrim (d, sort_of_extracted s)

let efield_to_extracted = function T.ENonRec -> X.ENonRec | T.ERec m -> X.ERec m
let efield_of_extracted = function X.ENonRec -> T.ENonRec | X.ERec m -> T.ERec m
let kind_to_extracted = function T.KData -> X.KData | T.KSingleton -> X.KSingleton | T.KEmpty -> X.KEmpty | T.KProp -> X.KProp
let kind_of_extracted = function X.KData -> T.KData | X.KSingleton -> T.KSingleton | X.KEmpty -> T.KEmpty | X.KProp -> T.KProp

let eind_to_extracted i =
  { X.eind_name = i.T.eind_name;
    eind_params = i.T.eind_params;
    eind_indices = i.T.eind_indices;
    eind_ctors =
      List.map (fun c -> { X.ector_name = c.T.ector_name; ector_fields = List.map efield_to_extracted c.T.ector_fields })
        i.T.eind_ctors;
    eind_kind = kind_to_extracted i.T.eind_kind }

let eind_of_extracted i =
  { T.eind_name = i.X.eind_name;
    eind_params = i.X.eind_params;
    eind_indices = i.X.eind_indices;
    eind_ctors =
      List.map (fun c -> { T.ector_name = c.X.ector_name; ector_fields = List.map efield_of_extracted c.X.ector_fields })
        i.X.eind_ctors;
    eind_kind = kind_of_extracted i.X.eind_kind }

let eentry_to_extracted = function
  | T.EEInd i -> X.EEInd (eind_to_extracted i)
  | T.EEElim (d, s, k) -> X.EEElim (d, sort_to_extracted s, kind_to_extracted k)
  | T.EEDef (f, b) -> X.EEDef (f, eterm_to_extracted b)

let eentry_of_extracted = function
  | X.EEInd i -> T.EEInd (eind_of_extracted i)
  | X.EEElim (d, s, k) -> T.EEElim (d, sort_of_extracted s, kind_of_extracted k)
  | X.EEDef (f, b) -> T.EEDef (f, eterm_of_extracted b)

let esignature_to_extracted = List.map eentry_to_extracted
let esignature_of_extracted = List.map eentry_of_extracted

(* ** Results *)

let stage_to_extracted = function
  | E.AtArity -> X.AtArity | E.AtSort -> X.AtSort | E.AtUnfold -> X.AtUnfold | E.AtType -> X.AtType

let erase_error_to_extracted = function
  | E.XIllTyped (t, e) -> X.XIllTyped (term_to_extracted t, error_to_extracted e)
  | E.XNotAType (t, k) -> X.XNotAType (term_to_extracted t, term_to_extracted k)
  | E.XShape (t, ty) -> X.XShape (term_to_extracted t, term_to_extracted ty)
  | E.XIllegalElim (d, s) -> X.XIllegalElim (d, sort_to_extracted s)
  | E.XUnsupported t -> X.XUnsupported (term_to_extracted t)
  | E.XInactive (d, s) -> X.XInactive (d, sort_to_extracted s)
  | E.XReserved d -> X.XReserved d

let erase_result_to_extracted value = function
  | E.Erased a -> X.Erased (value a)
  | E.NotErasable e -> X.NotErasable (erase_error_to_extracted e)
  | E.UndecidedAt (st, t) -> X.UndecidedAt (stage_to_extracted st, term_to_extracted t)

let ecbv_to_extracted = function
  | T.CbvValue t -> X.CbvValue (eterm_to_extracted t)
  | T.CbvStuck t -> X.CbvStuck (eterm_to_extracted t)
  | T.CbvOutOfFuel -> X.CbvOutOfFuel
