open Ast


let rec string_of_comp_ty (c: comp_ty) : string =
  Printf.sprintf "%s ! %s" (string_of_val_ty c.ct_val) (string_of_eff_ty c.ct_eff)

and string_of_eff_ty (e: syneff) : string =  match e with
  | SEEmpty -> "ε"
  | SEVar x -> x
  | SEJoin (e1, e2) -> Printf.sprintf "(%s ∨ %s)" (string_of_eff_ty e1) (string_of_eff_ty e2  )
  | SESeq (e1, e2) -> Printf.sprintf "(%s ⊵ %s)" (string_of_eff_ty e1) (string_of_eff_ty e2)
  | SENext e -> Printf.sprintf "▶%s" (string_of_eff_ty e)
  | SELabel l -> l

and string_of_base_ty (b: base_ty) : string =
  match b with
  | TUnit -> "unit"
  | TBool -> "bool"   
  | TInt -> "int"

and string_of_val_ty (t: val_ty) : string =
  match t with
  | TVBase b -> string_of_base_ty b
  | TVVar x -> x
  | TVArrow (t1, c) -> Printf.sprintf "(%s -> %s)" (string_of_val_ty t1) (string_of_comp_ty c)
  | TVForall (x, c) -> Printf.sprintf "forall %s. %s" x (string_of_comp_ty c)
  | TVRec (x, t) -> Printf.sprintf "mu %s. %s" x (string_of_val_ty t)
  | TVLater t -> Printf.sprintf "later %s" (string_of_val_ty t)
  | TVSum constructors -> 
    let constructor_strings = List.map (fun (name, args) ->
        let args_str = String.concat ", " (List.map string_of_val_ty args) in
        Printf.sprintf "%s(%s)" name args_str
      ) constructors in
    String.concat " + " constructor_strings
  | TVNamed name -> name