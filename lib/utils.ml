open Ast

let rec string_of_syneff = function
  | SEEmpty -> "ε"
  | SEVar x -> x
  | SEJoin (e1, e2) -> Printf.sprintf "(%s ∨ %s)" (string_of_syneff e1) (string_of_syneff e2)
  | SESeq (e1, e2) -> Printf.sprintf "(%s ⊵ %s)" (string_of_syneff e1) (string_of_syneff e2)
  | SENext e -> Printf.sprintf "▶%s" (string_of_syneff e)
  | SELabel l -> l

let rec string_of_val_ty = function
  | TVBase TUnit -> "unit"
  | TVBase TBool -> "bool"
  | TVBase TInt -> "int"
  | TVVar a -> a
  | TVArrow (t, c) -> Printf.sprintf "(%s -> %s)" (string_of_val_ty t) (string_of_comp_ty c)
  | TVEffForall (x, c) -> Printf.sprintf "(∀%s. %s)" x (string_of_comp_ty c)
  | TVRec (a, t) -> Printf.sprintf "(rec %s. %s)" a (string_of_val_ty t)
  | TVLater t -> Printf.sprintf "▶%s" (string_of_val_ty t)
  | TVTyForall (a, c) -> Printf.sprintf "(∀%s. %s)" a (string_of_comp_ty c)

and string_of_comp_ty c =
  Printf.sprintf "%s & %s" (string_of_val_ty c.ct_val) (string_of_syneff c.ct_eff)

let string_of_const = function
  | CUnit -> "()"
  | CInt n -> string_of_int n
  | CBool b -> string_of_bool b

let rec string_of_value = function
  | VVar x -> x
  | VConst c -> string_of_const c
  | VLam (x, t, e) -> Printf.sprintf "(λ%s:%s. %s)" x (string_of_val_ty t) (string_of_expr e)
  | VEffLam (x, e) -> Printf.sprintf "(Λ%s. %s)" x (string_of_expr e)
  | VFold (v, t) -> Printf.sprintf "(fold[%s] %s)" (string_of_val_ty t) (string_of_value v)
  | VNext v -> Printf.sprintf "(next %s)" (string_of_value v)
  | VTyLam (a, e) -> Printf.sprintf "(Λ%s. %s)" a (string_of_expr e)

and string_of_expr = function
  | EVal v -> string_of_value v
  | EOp (op, vs) -> Printf.sprintf "%s(%s)" op (String.concat ", " (List.map string_of_value vs))
  | EApp (v1, v2) -> Printf.sprintf "(%s %s)" (string_of_value v1) (string_of_value v2)
  | EEffApp (v, e) -> Printf.sprintf "(%s %s)" (string_of_value v) (string_of_syneff e)
  | ETyApp (v, t) -> Printf.sprintf "(%s [%s])" (string_of_value v) (string_of_val_ty t)
  | EUnfold v -> Printf.sprintf "(unfold %s)" (string_of_value v)
  | ELet (x, e1, e2) ->
    Printf.sprintf "(let %s = %s in\n  %s)" x (string_of_expr e1) (string_of_expr e2)
  | EIf (v, e1, e2) ->
    Printf.sprintf "(if %s then %s else %s)" (string_of_value v) (string_of_expr e1)
      (string_of_expr e2)
  | ENext e -> Printf.sprintf "(next %s)" (string_of_expr e)
  | ETensor (v1, v2) -> Printf.sprintf "(%s ⊗ %s)" (string_of_value v1) (string_of_value v2)
  | EPrev v -> Printf.sprintf "(prev %s)" (string_of_value v)
  | EMatch (v, brs) ->
    let string_of_pat = function
      | PWildcard -> "_"
      | PVar x -> x
      | PConstructor (c, _) -> Printf.sprintf "%s(..)" c
    in
    let brs' =
      List.map (fun (p, e) -> Printf.sprintf "%s -> %s" (string_of_pat p) (string_of_expr e)) brs
    in
    Printf.sprintf "(match %s with %s)" (string_of_value v) (String.concat " | " brs')