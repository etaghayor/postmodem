open Ast
open AstSurface
open TranslatorAI
(* open Utils *)
open Pp
open Tests

(* ── ADT ──────────────────────────────────────────────────────── *)
let penv = default_prim;;

let list_decl = {adt_name = "List"; adt_variants = [("Nil", []); ("Cons", [TVBaseS TIntS; TVNamedS "List"])]; adt_guarded = true}
let tree_decl = {adt_name = "Tree"; adt_variants = [("Leaf", []); ("Node", [TVNamedS "Tree"; TVNamedS "Tree"])]; adt_guarded = true}
let option_decl = {adt_name = "Option"; adt_variants = [("None", []); ("Some", [TVBaseS TIntS])]; adt_guarded = true}

let proc_decl : adt_declS =
  { adt_name = "Proc";
    adt_variants =
      [ ("Halt", []);
        ("Cont", [ TVArrowS (TVBaseS TUnitS,
                             { ct_valS = TVNamedS "Proc"; ct_effS = SEEmptyS }) ]) ];
    adt_guarded = true }
let decl_env = [list_decl; tree_decl; option_decl; proc_decl]



let () =
  print_endline "Let's get into it";
  (* trans_value decl_env m2_closure |> pp_value ~compact:false Format.std_formatter; *)
  (* EValS (VConstructorS ("Cont", [ m2_closure ])) |> trans_expr decl_env penv None |> pp_expr ~compact:false Format.std_formatter; *)
  (* trans_expr decl_env penv None minf_expr|> pp_expr ~compact:true Format.std_formatter; *)
  (* trans_expr decl_env penv None mres |> pp_expr ~compact:true Format.std_formatter;
  Format.print_flush ();
  print_endline "\n";
  eff_of_program {prog_decls= decl_env; prog_main = mres} |> string_of_eff_val |> print_endline;
  print_endline "\n";
  eff_of_program example2 |> string_of_eff_val |> print_endline;
  print_endline "\n";
  eff_of_program exampleB |> string_of_eff_val |> print_endline;
  print_endline "\n";
  eff_of_program example4 |> string_of_eff_val |> print_endline;
  print_endline "\n";

  trans_program example4 |> pp_expr ~compact:true Format.std_formatter; *)
  
  eff_of_program exampleB |> string_of_eff_val |> print_endline;
  print_endline "\n";


  Format.print_flush ();
  print_endline "\n";
  (* ----- EValS (VConstructorS ("Cont", [ m2_closure ])) ----- *)

  (* Proc = (rec __rec_Proc.
          (∀__alpha_Proc.
            ((∀__e_5. __alpha_Proc & __e_5) ->
              ((∀__e_5. ((unit -> Later (__rec_Proc & __e_5)) -> (__alpha_Proc & ε)) ) ->
                __alpha_Proc & ε) ))) *)

  (*(fold[(rec __rec_Proc.
         (∀__alpha_Proc.
           ((∀__e_5. __alpha_Proc & __e_5) ->
             ((∀__e_5. ((unit -> __rec_Proc & ε) -> __alpha_Proc & ε) & __e_5) ->
               __alpha_Proc & ε) & ε) & ε))]
    (Λ__alpha_Proc.
     (λ__h_1:__alpha_Proc.
       (λ__h_2:((unit -> __rec_Proc & ε) -> __alpha_Proc & ε).
         let __af_3 =
           __h_2
         in
         let __aa_4 =
           (λ_:unit. let _ =
                       print("seen ")
                     in
                     (minf ()))
         in
         (__af_3 __aa_4))))) *)