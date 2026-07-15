open Ast
open AstSurface

let rec translate expr = match expr with
  | EValS v -> EVal (translate_value v)
  | EOpS (op, args) -> EOp (op, List.map translate_value args)
  | EAppS (v1, v2) -> EApp (translate_value v1, translate_value v2)
  | EEffAppS (v, e) -> EEffApp (translate_value v, translate_syneff e)
  | ELetS (x, m1, m2) -> ELet (x, translate m1, translate m2)
  | EIfS (v, m1, m2) -> EIf (translate_value v, translate m1, translate m2)
  | ETensorS (v1, v2) -> ETensor (translate_value v1, translate_value v2)
  | EMatchS (v, branches) ->
    let translated_branches = List.map (fun (p, m) -> (translate_pattern p, translate m)) branches in
    EMatch (translate_value v, translated_branches)

and translate_value v = match v with
  | VVarS x -> VVar x
  | VConstS c -> VConst (translate_const c)
  | VLamS (x, ty, m) -> VLam (x, translate_val_ty ty, translate m)
  | VEffLamS (e, m) -> VEffLam (e, translate m)
  | VTyLamS (ty, m) -> VTyLam (translate_val_ty ty, translate m)
  | VConstructorS (name, args) -> failwith "Translation for sum type constructors is not implemented yet."
and translate_pattern p = match p with
  | PWildcardS -> PWildcard
  | PVarS x -> PVar x
  | PConstructorS (name, args) -> PConstructor (name, List.map translate_pattern args)
and translate_const c = match c with
  | CUnitS -> CUnit
  | CIntS n -> CInt n
  | CBoolS b -> CBool b
and translate_val_ty ty = match ty with
  | TVBaseS b -> TVBase (translate_base_ty b)
  | TVVarS x -> TVVar x
  | TVArrowS (t, c) -> TVArrow (translate_val_ty t, translate_comp_ty c)
  | TVEffForallS (e, c) -> TVEffForall (e, translate_comp_ty c)
  | TVTyForallS (t, c) -> TVTyForall (t, translate_comp_ty c)
  | TVRecS (x, t) -> TVRec (x, translate_val_ty t)
  | TVSumS constructors -> failwith "Translation for sum types is not implemented yet."
  | TVNamedS name -> failwith "Translation for named types is not implemented yet."
and translate_comp_ty c = { ct_val = translate_val_ty c.ct_valS; ct_eff = translate_syneff c.ct_effS }
and translate_syneff e = match e with
  | SEEmptyS -> SEEmpty
  | SEVarS x -> SEVar x
  | SEJoinS (e1, e2) -> SEJoin (translate_syneff e1, translate_syneff e2)
  | SESeqS (e1, e2) -> SESeq (translate_syneff e1, translate_syneff e2)
  | SELabelS l -> SELabel l

and translate_base_ty b = match b with
  | TUnitS -> TUnit
  | TBoolS -> TBool
  | TIntS -> TInt 