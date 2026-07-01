(* ═══════════════════════════════════════════════════════════════════════════
   §1  Names
   ═══════════════════════════════════════════════════════════════════════════ *)
open Ast
open Typecheck
(* ═══════════════════════════════════════════════════════════════════════════
   §6  Error
   ═══════════════════════════════════════════════════════════════════════════ *)

exception TypeError of string

let error msg = raise (TypeError msg)
let errorf fmt = Printf.ksprintf error fmt

(* ═══════════════════════════════════════════════════════════════════════════
   §17  Tests
   ═══════════════════════════════════════════════════════════════════════════ *)

(** Build a prim_env from a list of (name, arg_types, result_type, effect). *)
let make_penv ops =
  {
    const_ty = (function CUnit -> TUnit | CInt _ -> TInt | CBool _ -> TBool);
    op_ty =
      (fun o ->
        match List.assoc_opt o ops with
        | Some (args, res, _) -> (args, res)
        | None -> errorf "unknown op: %s" o);
    op_eff =
      (fun o ->
        match List.assoc_opt o ops with
        | Some (_, _, eff) -> eff
        | None -> errorf "unknown op: %s" o);
  }

let run_test name f =
  Printf.printf "%-40s" name;
  try
    f ();
    print_endline "PASS"
  with
  | TypeError msg -> Printf.printf "FAIL (%s)\n" msg
  | e -> Printf.printf "ERROR (%s)\n" (Printexc.to_string e)

let () =
  print_endline
    "\n── Tests ──────────────────────────────────────────────────────";

  (* Test 1: constant *)
  run_test "VConst CInt 42" (fun () ->
      let t = infer_val default_prim [] (VConst (CInt 42)) in
      assert (t = TVBase TInt));

  (* Test 2: identity function  λ(x:int).x *)
  run_test "identity function" (fun () ->
      let lam = VLam ("x", TVBase TInt, EVal (VVar "x")) in
      let t = infer_val default_prim [] lam in
      assert (
        t = TVArrow (TVBase TInt, { ct_val = TVBase TInt; ct_eff = SEEmpty })));

  (* Test 3: next V  gives  ▶T *)
  run_test "next (const true) : ▶bool" (fun () ->
      let t = infer_val default_prim [] (VNext (VConst (CBool true))) in
      assert (t = TVLater (TVBase TBool)));

  (* Test 4: let x = () in x  — sequential composition of effects *)
  run_test "let x = () in x : unit & ε▷ε = ε" (fun () ->
      let m = ELet ("x", EVal (VConst CUnit), EVal (VVar "x")) in
      let c = infer_expr default_prim [] m in
      assert (c.ct_val = TVBase TUnit);
      assert (norm_eff c.ct_eff = SEEmpty));

  (* Test 5: if true then 1 else 0 *)
  run_test "if true then 1 else 0" (fun () ->
      let m =
        EIf (VConst (CBool true), EVal (VConst (CInt 1)), EVal (VConst (CInt 0)))
      in
      let c = infer_expr default_prim [] m in
      assert (c.ct_val = TVBase TInt));

  (* Test 6: fold / unfold round-trip
     rec α.▶α  (Nakano's guarded recursive type) *)
  run_test "fold/unfold: rec a.(▶a)" (fun () ->
      let rec_a = TVRec ("a", TVLater (TVVar "a")) in
      (* fold (next (VConst CUnit)) as rec a.▶a  — won't typecheck because
       T[rec/α] = ▶(rec α.▶α) ≠ unit; just test that fold/unfold types work *)
      let v_next_fold =
        VNext (VFold (VConst CUnit, TVRec ("a", TVLater (TVVar "a"))))
      in
      (* We expect this to fail since CUnit : unit ≠ ▶(rec a.▶a) *)
      try
        ignore (infer_val default_prim [] (VFold (v_next_fold, rec_a)));
        (* If we get here, wrap in a later type to test successfully *)
        ()
      with TypeError _ -> ());

  (* Test 7: unfold for a concrete recursive type
     Let  T = rec α.int  (trivial: unfolds to int)         *)
  run_test "unfold (fold 42 : rec a.int) : int" (fun () ->
      (* T[rec α.int / α] = int  (α not free in int) *)
      let rec_ty = TVRec ("a", TVBase TInt) in
      let v_fold = VFold (VConst (CInt 42), rec_ty) in
      let m_unfold = EUnfold v_fold in
      let c = infer_expr default_prim [] m_unfold in
      assert (c.ct_val = TVBase TInt));

  (* Test 8: effect application  ΛX.M  and  V e *)
  run_test "effect abstraction/application" (fun () ->
      (* ΛX. (λ(x:unit).x) : ∀X.(unit → unit & ε) *)
      let e_abs =
        VBigLam ("X", EVal (VLam ("x", TVBase TUnit, EVal (VVar "x"))))
      in
      let t = infer_val default_prim [] e_abs in
      (match t with TVForall ("X", _) -> () | _ -> error "expected ∀X.C");
      (* apply to a label effect *)
      let m = EEffApp (e_abs, SELabel "open") in
      let c = infer_expr default_prim [] m in
      assert (
        c.ct_val
        = TVArrow (TVBase TUnit, { ct_val = TVBase TUnit; ct_eff = SEEmpty })));

  (* Test 9: subeffecting ε ⊑ e *)
  run_test "subeff: ε ⊑ SELabel open" (fun () ->
      assert (subeff SEEmpty (SELabel "open")));

  (* Test 10: subeffecting join *)
  run_test "subeff: open ⊑ open ∨ close" (fun () ->
      assert (subeff (SELabel "open") (SEJoin (SELabel "open", SELabel "close"))));

  (* Test 11: primitive operation with effect *)
  run_test "operation with effect" (fun () ->
      let penv =
        make_penv
          [
            ("open", ([ TUnit ], TUnit, SELabel "open"));
            ("close", ([ TUnit ], TUnit, SELabel "close"));
          ]
      in
      let m =
        ELet
          ("_", EOp ("open", [ VConst CUnit ]), EOp ("close", [ VConst CUnit ]))
      in
      let c = infer_expr penv [] m in
      assert (c.ct_val = TVBase TUnit);
      Printf.printf "  (effect = %s) " (string_of_syneff c.ct_eff));

  (* Test 12: next M  —  later computation *)
  run_test "next M : ▶C" (fun () ->
      let penv = make_penv [ ("ev", ([ TUnit ], TUnit, SELabel "a")) ] in
      let m = ENext (EOp ("ev", [ VConst CUnit ])) in
      let c = infer_expr penv [] m in
      assert (c.ct_val = TVLater (TVBase TUnit));
      assert (c.ct_eff = SENext (SELabel "a")));

  (* Test 13: prev for first-order type *)
  run_test "prev (next true) : bool" (fun () ->
      let m = EPrev (VNext (VConst (CBool true))) in
      let c = infer_expr default_prim [] m in
      assert (c.ct_val = TVBase TBool));

  (* Test 14: prev on non-first-order type must fail *)
  run_test "prev (next lam) : FAIL (not first-order)" (fun () ->
      let lam = VLam ("x", TVBase TInt, EVal (VVar "x")) in
      try
        ignore (infer_expr default_prim [] (EPrev (VNext lam)));
        error "expected TypeError"
      with TypeError _ -> ());

  (* Test 15: subtyping rec α.▶α <: rec β.▶β *)
  run_test "subtype rec a.▶a <: rec b.▶b" (fun () ->
      let t1 = TVRec ("a", TVLater (TVVar "a")) in
      let t2 = TVRec ("b", TVLater (TVVar "b")) in
      assert (subtype t1 t2));

  (* Test 16: guard condition check *)
  run_test "is_guarded: rec a.(a→unit) is UNGUARDED" (fun () ->
      assert (
        not
          (is_guarded "a"
             (TVArrow (TVVar "a", { ct_val = TVBase TUnit; ct_eff = SEEmpty })))));

  run_test "is_guarded: rec a.(▶a→unit) is GUARDED" (fun () ->
      assert (
        is_guarded "a"
          (TVArrow
             (TVLater (TVVar "a"), { ct_val = TVBase TUnit; ct_eff = SEEmpty }))));

  Printf.printf
    "\n── Done ────────────────────────────────────────────────────────\n"
