(* open Ast
open AstSurface



let rec infer_later = function
  | VConstructorS (name, args) -> failwith "TODO: infer_later: sum type constructors are not supported yet."
  | _ -> failwith "TODO: infer_later: only sum type constructors are supported for later inference."


  and trans_expr (env : adt_env) (e : exprS) : expr =
  match e with
  | EValS v -> EVal (trans_value env v)
  | EOpS (op, args) -> EOp (op, List.map (trans_value env) args)
  | EAppS (v1, v2) -> EApp (trans_value env v1, trans_value env v2)
  | EEffAppS (v, eff) -> EEffApp (trans_value env v, trans_syneff eff)
  | ELetS (x, e1, e2) -> ELet (x, trans_expr env e1, trans_expr env e2)
  | EIfS (v, e1, e2) -> EIf (trans_value env v, trans_expr env e1, trans_expr env e2)
  | ETensorS (v1, v2) -> ETensor (trans_value env v1, trans_value env v2)

let rec translate_value (env : adt_env) (v : valueS) : value =
  match v with
  | VVarS x -> VVar x
  | VConstS c -> VConst (trans_const c)
  | VLamS (x, t, body) -> VLam (x, trans_val_ty env [] t, trans_expr env body)
  | VTyLamS (a, body) -> VTyLam (a, trans_expr env body)
  | VEffLamS (x, body) -> VEffLam (x, trans_expr env body)
  | VConstructorS (cname, args) -> (*TODO*)trans_ctor_value env cname (List.map (trans_value env) args)

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
  | TVSumS constructors -> failwith "TODO: Translation for sum types is not implemented yet."
  | TVNamedS name -> failwith "TODO: Translation for named types is not implemented yet."
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
  | TIntS -> TInt  *)