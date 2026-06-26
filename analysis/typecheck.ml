(* Bidirectional Type Checking for the Language of 
   "Algebraic Temporal Effects" (Sekiyama & Unno, POPL 2025) *)

(* 
  - Values are checked bidirectionally:  infer_val / check_val.
  - Expressions are always inferred: infer_expr.
*)


open Ast
exception TypeError of string

let error msg = raise (TypeError msg)

let errorf fmt = Printf.ksprintf error fmt



(* -------------------------------------------------------------------------- *)
(* Type Inference *)


(** Infer the type of a value
    (* @param penv The type environment *)
    @param ctx The typing context
    @param v The value to infer
    @return The inferred type
*)

(* Context helpers *)
let ctx_find_var (ctx: ctx) (x: var) : val_ty =
  match List.find_opt (function CEVar (y, _) when y = x -> true | _ -> false) ctx with
  | Some (CEVar (_, t)) -> t
  | _ -> errorf "unbound variable: %s" x

let ctx_add_var (ctx: ctx) (x: var) (t: val_ty) : ctx =
  let rec aux acc = function
    | [] -> (CEVar (x, t) :: acc)
    | CEVar (y, _) :: rest when y = x -> aux (CEVar (x, t) :: acc) rest (* shadowing *)
    | entry :: rest -> aux (entry :: acc) rest
  in aux [] ctx

let infer_const (c: const) : val_ty =
  match c with
  | CUnit -> TVBase TUnit
  | CInt _ -> TVBase TInt
  | CBool _ -> TVBase TBool

let rec infer_expr (prim: prim_env) (ctx: ctx) (e: expr) : val_ty =
  match e with
  | EVal v -> infer_val prim ctx v
  | EOp (op, args) -> error "TODO"
  | EApp (v1, v2) -> error "TODO"
  | EEffApp (v, eff) -> error "TODO"
  | EUnfold v -> error "TODO"
  | ELet (x, e1, e2) -> error "TODO"
  | EIf (v, e1, e2) -> error "TODO"
  | ENext e -> error "TODO"
  | ETensor (v1, v2) -> error "TODO"
  | EPrev v -> error "TODO"
and infer_val (prim: prim_env) (ctx: ctx) (v: value) : val_ty =
  match v with
  (* T_Var *)
  | VVar x ->  ctx_find_var ctx x           (* x          — variable               *)
  (* T_Const *)
  | VConst c -> infer_const c              (* c          — constant               *)
  (* T_Abs 
     Γ, x:T ⊢ M : C
     ─────────────────────────────
     Γ ⊢ λ(x:T).M : T → C         *)
  | VLam  (v, val_ty , body) -> infer_expr prim (ctx_add_var ctx v val_ty) body (* λx. M      — term abstraction - annotated*)
  | VBigLam (effvar, body) -> error "TODO" (* ΛX. M      — effect abstraction      *)
  | VFold (value, value_ty) -> error "TODO" (* fold V     — recursive type intro - annotated   *)
  | VNext value -> error "TODO" (* next V     — later computation results      *)

(* -------------------------------------------------------------------------- *)
(* Type Checking *)

(* Check a value against a type *)
(* let rec check_val penv ctx v t = *)
