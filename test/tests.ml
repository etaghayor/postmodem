open Ast
open AstSurface
open TranslatorAI
open Utils


let m2_closure : valueS =
  VLamS
    ( "_",
      TVBaseS TUnitS,
      ELetS
        ( "_",
          EOpS ("print", [VConstS (CStringS "seen ")]),
          EAppS (VVarS "minf", VConstS CUnitS) ) )


(* let rec minf = Cont (fun () -> print_string "seen "; minf) *)
let minf_expr : exprS =
  ELetRecValS
    ( "minf", TVNamedS "Proc",
      EValS
        (VConstructorS
           ( "Cont",
             [ VLamS
                 ( "_", TVBaseS TUnitS,
                   ELetS
                     ( "_", EOpS ("print", [ VConstS (CStringS "seen ") ]),
                       EValS (VVarS "minf") ) )
             ] )),
      EValS (VVarS "minf") )

(* let rec mtake x = match x with
     | Halt -> print_string "unseen"
     | Cont f -> mtake (f ()) *)
let mres : exprS =
  ELetRecS
    ( "mtake", "x", TVNamedS "Proc",
      { ct_valS = TVBaseS TUnitS; ct_effS = SEEmptyS },
      EMatchS
        ( VVarS "x",
          TVBaseS TUnitS,
          [ ( PConstructorS ("Halt", []),
              EOpS ("print", [ VConstS (CStringS "unseen") ]) );
            ( PConstructorS ("Cont", [ PVarS "f" ]),
              ELetS
                ( "y", EAppS (VVarS "f", VConstS CUnitS),
                  EAppS (VVarS "mtake", VVarS "y") ) )
          ] ),
      ELetS ("minf", minf_expr,EAppS (VVarS "mtake", VVarS "minf")))
(* let mres : exprS = 
   ELetS ("minf", minf_expr, 
         ELetS ("mtake", mtake_expr,
                EAppS (VVarS "mtake", VVarS "minf"))) *)