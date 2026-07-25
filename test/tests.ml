open Ast
open AstSurface
open TranslatorAI
open Utils





(* -------------------------------------------------- *)
(* ---------------------Test 1----------------------- *)
(* -------------------------------------------------- *)
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
let mtake_expr : exprS =
  ELetRecS
    ( "mtake", "x", TVNamedS "Proc",
      { ct_valS = TVBaseS TUnitS; ct_effS = SELabelS "print" },
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
      EValS (VVarS "mtake") )

let mres : exprS = 
  ELetS ("minf", minf_expr, 
         ELetS ("mtake", mtake_expr,
                EAppS (VVarS "mtake", VVarS "minf")))



(* -------------------------------------------------- *)
(* ---------------------Test 2----------------------- *)
(* -------------------------------------------------- *)

let comb_decl : adt_declS =
  { adt_name = "Comb";
    adt_variants =
      [ ("MkComb",
         [ TVArrowS (TVNamedS "Comb", { ct_valS = TVBaseS TUnitS; ct_effS = SEVarS "e" }) ]) ];
    adt_guarded = true }

let run_def (cont : exprS) : exprS =
  ELetRecS
    ( "run", "p", TVNamedS "Comb",
      { ct_valS = TVBaseS TUnitS; ct_effS = SEVarS "e" },
      EMatchS ( VVarS "p", TVNamedS "Comb",
                [ (PConstructorS ("MkComb", [ PVarS "k" ]), EAppS (VVarS "k", VVarS "p")) ] ),
      cont )

let f_def (cont : exprS) : exprS =
  ELetRecValS
    ( "f", TVNamedS "Comb",
      EValS (VConstructorS ( "MkComb",
                             [ VLamS ( "self", TVNamedS "Comb",
                                       ELetS ("_", EOpS ("a", []), EAppS (VVarS "run", VVarS "self")) ) ] )),
      cont )

let example2 : programS =
  { prog_decls = [ comb_decl ];
    prog_main = run_def (f_def (EAppS (VVarS "run", VVarS "f"))) }


(* -------------------------------------------------- *)
(* ---------------------Test 3----------------------- *)
(* -------------------------------------------------- *)
(* type brec = B1 of (int -> brec -> int) | B2 of brec

   let rec binf = B1 (fun n b -> print_string "Bseen "; n);;

   let rec btake x = match x with
   | B1 f -> let _ = (f 0 x) in btake x
   | B2 b -> print_string "Bunseen" *)

let brec_decl : adt_declS =
  { adt_name = "Brec";
    adt_variants =
      [ ("B1", [ TVArrowS (TVBaseS TIntS,
                           { ct_valS = TVArrowS (TVNamedS "Brec", { ct_valS = TVBaseS TIntS; ct_effS = SEEmptyS });
                             ct_effS = SEEmptyS }) ]);
        ("B2", [ TVNamedS "Brec" ]) ];
    adt_guarded = true }

let binf_expr : exprS =
  ELetRecValS
    ( "binf", TVNamedS "Brec",
      EValS
        (VConstructorS
           ( "B1",
             [ VLamS
                 ( "n", TVBaseS TIntS,
                   EValS
                     (VLamS
                        ( "b", TVNamedS "Brec",
                          ELetS
                            ( "_", EOpS ("print", [ VConstS (CStringS "Bseen ") ]),
                              EValS (VVarS "n") ) )) )
             ] )),
      EValS (VVarS "binf") )

let btake_expr : exprS =
  ELetRecS
    ( "btake", "x", TVNamedS "Brec",
      { ct_valS = TVBaseS TUnitS; ct_effS = SELabelS "print" },
      EMatchS
        ( VVarS "x",
          TVBaseS TUnitS,
          [ ( PConstructorS ("B1", [ PVarS "f" ]),
              ELetS
                ( "_",
                  ELetS
                    ( "t1", EAppS (VVarS "f", VConstS (CIntS 0)),
                      EAppS (VVarS "t1", VVarS "x") ),
                  EAppS (VVarS "btake", VVarS "x") ) );
            ( PConstructorS ("B2", [ PVarS "b" ]),
              EOpS ("print", [ VConstS (CStringS "Bunseen") ]) )
          ] ),
      EValS (VVarS "btake") )

let bres : exprS = 
  ELetS ("binf", binf_expr, 
         ELetS ("btake", btake_expr,
                EAppS (VVarS "btake", VVarS "binf")))
let exampleB : programS =
  { prog_decls = [ brec_decl ];
    prog_main = bres }


(* -------------------------------------------------- *)
(* ---------------------Test 3----------------------- *)
(* -------------------------------------------------- *)
(* type crec = C1 | C2 of (unit -> crec)

   let rec cinf = C2 (fun () -> print_string "Cseen "; cinf);;

   let rec ctake x = match x with
   | C1 -> print_string "Cunseen"
   | C2 f -> iter f
   and iter f = let _ = f () in iter f *)


let crec_decl : adt_declS =
  { adt_name = "Crec";
    adt_variants =
      [ ("C1", []);
        ("C2", [ TVArrowS (TVBaseS TUnitS, { ct_valS = TVNamedS "Crec"; ct_effS = SEEmptyS }) ]) ];
    adt_guarded = true }

let cinf_expr : exprS =
  ELetRecValS
    ( "cinf", TVNamedS "Crec",
      EValS
        (VConstructorS
           ( "C2",
             [ VLamS
                 ( "_", TVBaseS TUnitS,
                   ELetS
                     ( "_", EOpS ("print", [ VConstS (CStringS "Cseen ") ]),
                       EValS (VVarS "cinf") ) )
             ] )),
      EValS (VVarS "cinf") )

let ctake_expr : exprS =
  ELetRecS
    ( "iter", "f",
      TVArrowS (TVBaseS TUnitS, { ct_valS = TVNamedS "Crec"; ct_effS = SEEmptyS }),
      { ct_valS = TVBaseS TUnitS; ct_effS = SELabelS "print" },
      ELetS ("_", EAppS (VVarS "f", VConstS CUnitS), EAppS (VVarS "iter", VVarS "f")),
      ELetRecS
        ( "ctake", "x", TVNamedS "Crec",
          { ct_valS = TVBaseS TUnitS; ct_effS = SELabelS "print" },
          EMatchS
            ( VVarS "x",
              TVBaseS TUnitS,
              [ ( PConstructorS ("C1", []),
                  EOpS ("print", [ VConstS (CStringS "Cunseen") ]) );
                ( PConstructorS ("C2", [ PVarS "f" ]),
                  EAppS (VVarS "iter", VVarS "f") )
              ] ),
          EValS (VVarS "ctake") ) )

let example4 : programS =
  { prog_decls = [ crec_decl ];
    prog_main =
      ELetS ("cinf", cinf_expr,
             ELetS ("ctake", ctake_expr,
                    EAppS (VVarS "ctake", VVarS "cinf"))) }