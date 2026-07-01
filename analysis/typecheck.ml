(* Bidirectional Type Checking for the Language of 
   "Algebraic Temporal Effects" (Sekiyama & Unno, POPL 2025) *)

(* 
  - Values are checked bidirectionally:  infer_val / check_val.
  - Expressions are always inferred: infer_expr.
*)


open Ast
open Helpers
exception TypeError of string

let error msg = raise (TypeError msg)

let errorf fmt = Printf.ksprintf error fmt


(* -------------------------------------------------------------------------- *)
(* Context helpers *)
let ctx_find_var (ctx: ctx) (x: var) : val_ty =
  match List.find_opt (function CEVar (y, _) when y = x -> true | _ -> false) ctx with
  | Some (CEVar (_, t)) -> t
  | _ -> errorf "unbound variable: %s" x

let ctx_add_entry (ctx: ctx) (entry: ctx_entry) : ctx=
  match entry with
  | CEVar (x, t) -> 
    (List.map (
        function
        | CEVar (y, _) when y = x -> CEVar (x, t) (* shadowing *)
        | e -> e) ctx)
  | e -> e::ctx



(* -------------------------------------------------------------------------- *)
(* Type Substitution *)
let rec subst_val_ty (x: tvar) (s: val_ty) (t: val_ty) : val_ty =
  match t with
  | TVBase _ -> t
  | TVVar y -> if x = y then s else t
  | TVArrow (t1, c) -> TVArrow (subst_val_ty x s t1, subst_comp_ty x s c)
  | TVForall (y, c) -> if x = y then t else TVForall (y, subst_comp_ty x s c)
  | TVRec (y, t') -> if x = y then t else TVRec (y, subst_val_ty x s t')
  | TVLater t' -> TVLater (subst_val_ty x s t')
  | TVSum constructors -> 
    let new_constructors = List.map (fun (name, args) -> (*TODO double check*)
        let new_args = List.map (subst_val_ty x s) args in
        (name, new_args)
      ) constructors in
    TVSum new_constructors
  | TVNamed name -> TVNamed name
and subst_comp_ty (x: tvar) (s: val_ty) (c: comp_ty) : comp_ty =
  { ct_val = subst_val_ty x s c.ct_val; ct_eff = subst_eff_ty x s c.ct_eff }
and subst_eff_ty (x: tvar) (s: val_ty) (e: syneff) : syneff =
  match e with
  | SEEmpty -> SEEmpty
  | SEVar _ -> e
  | SEJoin (e1, e2) -> SEJoin (subst_eff_ty x s e1, subst_eff_ty x s e2)
  | SESeq (e1, e2) -> SESeq (subst_eff_ty x s e1, subst_eff_ty x s e2)
  | SENext e' -> SENext (subst_eff_ty x s e')
  | SELabel _ -> e

(* -------------------------------------------------------------------------- *)
(* Typing specific conditions *)

let rec wf_ty (ctx: ctx) (t: val_ty) : bool =
  match t with
  | TVBase _ -> true
  | TVVar x -> List.exists (function CETVar y when y = x -> true | _ -> false) ctx
  | TVArrow (t1, c) -> wf_ty ctx t1 && wf_comp ctx c
  | TVForall (x, c) -> wf_comp (CEEffVar x :: ctx) c
  | TVRec (x, t) -> wf_ty (CETVar x :: ctx) t
  | TVLater t -> wf_ty ctx t
  | TVSum constructors -> List.for_all (fun (_, args) -> List.for_all (wf_ty ctx) args) constructors
  | TVNamed _ -> true (* Assuming named types are well-formed by definition *)

and wf_comp (ctx: ctx) (c: comp_ty) : bool =
  wf_ty ctx c.ct_val
(* -------------------------------------------------------------------------- *)
(* Type Inference *)


(** [infer_expr (penv: prim_env) (ctx: ctx) (e: expr) : comp_ty]

    Infers the type of an expression
    @param penv The type environment
    @param ctx The typing context
    @param e The expression to infer
    @return The inferred type
 **)

let rec infer_expr (penv: prim_env) (ctx: ctx) (e: expr) : comp_ty =
  match e with
  | EVal v -> {ct_val = infer_val penv ctx v; ct_eff = SEEmpty} (* V                           *)
  | EOp (op, args) -> error "TODO"
  | EApp (v1, v2) -> error "TODO"
  | EEffApp (v, eff) -> error "TODO"
  | EUnfold v -> error "TODO"
  | ELet (x, e1, e2) -> error "TODO"
  | EIf (v, e1, e2) -> error "TODO"
  | ENext e -> error "TODO"
  | ETensor (v1, v2) -> error "TODO"
  | EPrev v -> error "TODO"
  | EMatch (v, cases) -> error "TODO"




(** [infer_val (penv: prim_env) (ctx: ctx) (v: value) : val_ty]
    Infers the type of a value
    @param penv The type environment
    @param ctx The typing context
    @param v The value to infer
    @return The inferred type
 **)
and infer_val (penv: prim_env) (ctx: ctx) (v: value) : val_ty =
  match v with
  (* T_Var *)
  | VVar x ->  ctx_find_var ctx x           (* x          — variable               *)
  (* T_Const *)
  | VConst c -> penv.pe_const c           (* c          — constant               *)
  | VLam  (v, val_ty , body) -> (* λx. M      — term abstraction - annotated*)
    (* T_Abs 
       Γ, x:T ⊢ M : C
       ─────────────────────────────
       Γ ⊢ λ(x:T).M : T → C         *)
    if not (wf_ty ctx val_ty) then errorf "ill-formed type: %s" (string_of_val_ty val_ty);
    let ctx' = ctx_add_entry ctx (CEVar (v, val_ty)) in
    let body_ty = infer_expr penv ctx' body in
    TVArrow (val_ty, body_ty)
  | VBigLam (tvar, body) -> (* ΛX. M      — effect abstraction      *)
    (* T_EAbs  — ΛX.M
       Γ, X ⊢ M : C
       ───────────────────────
       Γ ⊢ ΛX.M : ∀X.C         *)
    let ctx' = ctx_add_entry ctx  (CEEffVar tvar) in
    TVForall (tvar, infer_expr penv ctx' body) 
  | VFold (value, value_ty) -> (* fold V     — recursive type intro - annotated   *)
    (* T_Fold  — fold V as rec α.T
       The target type [ann] must be of the form rec α.T.
       Γ ⊢ V : T[rec α.T/α]
       ────────────────────────────
       Γ ⊢ fold V : rec α.T         *)
    infer_val penv ctx value (*TODO*)
  | VNext value -> error "TODO" (* next V     — later computation results      *)
  (* T_NextV  — next V
     Γ ⊢ V : T
     ────────────────
     Γ ⊢ next V : ▶T   (pure effect — NOT ▶e) *)

  | VConstructor (name, args) -> error "TODO" (* C(V1, V2, ..., Vn) — sum type constructor with named type*)
(* T_Constructor  — C(V1, V2, ..., Vn)
   Γ ⊢ Vi : Ti for each i
   ────────────────────────────────
   Γ ⊢ C(V1, V2, ..., Vn) : T�      
   where T is the sum type that contains the constructor C with argument types T1, T2, ..., Tn *)
(* For now, we will assume that the type of the constructor is known and can be retrieved from the context or a global environment. *)

(* -------------------------------------------------------------------------- *)
(* Type Checking *)

(* Check a value against a type *)
(* let rec check_val penv ctx v t = *)
