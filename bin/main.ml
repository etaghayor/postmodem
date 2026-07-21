open Ast
open AstSurface
open TranslatorAI
open Utils


(* ── ADT ──────────────────────────────────────────────────────── *)
let penv = default_prim;;

let list_adt = {adt_name = "List"; adt_variants = [("Nil", []); ("Cons", [TVBaseS TIntS; TVNamedS "List"])]}
let tree_adt = {adt_name = "Tree"; adt_variants = [("Leaf", []); ("Node", [TVNamedS "Tree"; TVNamedS "Tree"])]}
let option_adt = {adt_name = "Option"; adt_variants = [("None", []); ("Some", [TVBaseS TIntS])]}
let decl_env = [list_adt; tree_adt; option_adt]



let () =
  print_endline "Let's get into it";
  (* handler_val_ty "list" list_adt.adt_variants |> string_of_val_ty |> print_endline; *)
  TVNamedS "List" |> trans_val_ty decl_env [] |> string_of_val_ty |> print_endline;
  (* TVNamedS "Option" |> trans_val_ty decl_env [] |> string_of_val_ty |> print_endline; *)


