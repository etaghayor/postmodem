open Ast

(* Readable rendering of core terms produced by translator.ml.

   Two things make raw translator output hard to read: (1) every type
   annotation on a Church-encoded ADT spells out its full
   rec/forall/arrow expansion in place, over and over; (2) everything
   comes out as one unbroken line. This fixes both:

   - translator.ml names an ADT `X`'s recursion variable "__rec_X"
     and its answer-type variable "__ans_X" (deterministically, see
     rec_var_for/alpha_for there) - so we can recognize those names on
     the way back out and print "List" instead of expanding
     `rec __rec_List. ∀__ans_List. ...` at every single occurrence.
     The full expansion is still shown once, up front, as a legend.
   - Printing goes through Format so lets/lambdas/types indent and
     wrap instead of running off in one line.

   Pass ~compact:false to string_of_expr to disable the abbreviation
   and see everything spelled out in full, if you want that instead. *)

let adt_prefix = "__rec_"

let strip_prefix (p : string) (s : string) : string option =
  let lp = String.length p in
  if String.length s >= lp && String.sub s 0 lp = p then Some (String.sub s lp (String.length s - lp))
  else None

(* ── legend: collect every distinct ADT rec-type mentioned, with its
   full definition, so we can print it once ──────────────────────── *)

let legend : (string, val_ty) Hashtbl.t = Hashtbl.create 16

let rec collect_val_ty (t : val_ty) : unit =
  match t with
  | TVBase _ | TVVar _ -> ()
  | TVArrow (t1, c) -> collect_val_ty t1; collect_comp_ty c
  | TVEffForall (_, c) -> collect_comp_ty c
  | TVTyForall (_, c) -> collect_comp_ty c
  | TVLater t1 -> collect_val_ty t1
  | TVRec (rv, body) ->
    (match strip_prefix adt_prefix rv with
     | Some name -> if not (Hashtbl.mem legend name) then Hashtbl.add legend name t
     | None -> ());
    collect_val_ty body

and collect_comp_ty (c : comp_ty) : unit = collect_val_ty c.ct_val

let rec collect_value (v : value) : unit =
  match v with
  | VVar _ | VConst _ -> ()
  | VLam (_, t, e) -> collect_val_ty t; collect_expr e
  | VEffLam (_, e) -> collect_expr e
  | VFold (v1, t) -> collect_value v1; collect_val_ty t
  | VNext v1 -> collect_value v1
  | VTyLam (_, e) -> collect_expr e

and collect_expr (e : expr) : unit =
  match e with
  | EVal v -> collect_value v
  | EOp (_, vs) -> List.iter collect_value vs
  | EApp (v1, v2) -> collect_value v1; collect_value v2
  | EEffApp (v, _) -> collect_value v
  | ETyApp (v, t) -> collect_value v; collect_val_ty t
  | EUnfold v -> collect_value v
  | ELet (_, e1, e2) -> collect_expr e1; collect_expr e2
  | EIf (v, e1, e2) -> collect_value v; collect_expr e1; collect_expr e2
  | ENext e1 -> collect_expr e1
  | ETensor (v1, v2) -> collect_value v1; collect_value v2
  | EPrev v -> collect_value v

(* ── printers ──────────────────────────────────────────────────────── *)

let rec pp_syneff fmt (e : syneff) =
  match e with
  | SEEmpty -> Format.fprintf fmt "ε"
  | SEVar x -> Format.fprintf fmt "%s" x
  | SEJoin (e1, e2) -> Format.fprintf fmt "@[<hov 1>(%a@ ∨ %a)@]" pp_syneff e1 pp_syneff e2
  | SESeq (e1, e2) -> Format.fprintf fmt "@[<hov 1>(%a@ \xe2\x8a\xb5 %a)@]" pp_syneff e1 pp_syneff e2
  | SENext e1 -> Format.fprintf fmt "\xe2\x96\xb6%a" pp_syneff e1
  | SELabel l -> Format.fprintf fmt "%s" l

let rec pp_val_ty ~compact fmt (t : val_ty) =
  match t with
  | TVBase TUnit -> Format.fprintf fmt "unit"
  | TVBase TBool -> Format.fprintf fmt "bool"
  | TVBase TInt -> Format.fprintf fmt "int"
  | TVBase TString -> Format.fprintf fmt "string"
  | TVVar a -> (
    match (if compact then strip_prefix adt_prefix a else None) with
    | Some name -> Format.fprintf fmt "%s" name (* self-reference inside its own decl *)
    | None -> Format.fprintf fmt "%s" a)
  | TVArrow (t1, c) ->
    Format.fprintf fmt "@[<hov 2>(%a ->@ %a)@]" (pp_val_ty ~compact) t1 (pp_comp_ty ~compact) c
  | TVEffForall (x, c) -> Format.fprintf fmt "@[<hov 2>(\xe2\x88\x80%s.@ %a)@]" x (pp_comp_ty ~compact) c
  | TVTyForall (a, c) -> Format.fprintf fmt "@[<hov 2>(\xe2\x88\x80%s.@ %a)@]" a (pp_comp_ty ~compact) c
  | TVLater t1 -> Format.fprintf fmt "\xe2\x96\xb6%a" (pp_val_ty ~compact) t1
  | TVRec (rv, body) -> (
    match (if compact then strip_prefix adt_prefix rv else None) with
    | Some name -> Format.fprintf fmt "%s" name
    | None -> Format.fprintf fmt "@[<hov 2>(rec %s.@ %a)@]" rv (pp_val_ty ~compact) body)

and pp_comp_ty ~compact fmt (c : comp_ty) =
  Format.fprintf fmt "%a & %a" (pp_val_ty ~compact) c.ct_val pp_syneff c.ct_eff

let pp_const fmt (c : const) =
  match c with
  | CUnit -> Format.fprintf fmt "()"
  | CInt n -> Format.fprintf fmt "%d" n
  | CBool b -> Format.fprintf fmt "%b" b
  | CString s -> Format.fprintf fmt "\"%s\"" s

let pp_sep_comma fmt () = Format.fprintf fmt ",@ "

let rec pp_value ~compact fmt (v : value) =
  match v with
  | VVar x -> Format.fprintf fmt "%s" x
  | VConst c -> pp_const fmt c
  | VLam (x, t, e) ->
    Format.fprintf fmt "@[<hov 2>(\xce\xbb%s:%a.@ %a)@]" x (pp_val_ty ~compact) t (pp_expr ~compact) e
  | VEffLam (x, e) -> Format.fprintf fmt "@[<hov 2>(\xce\x9b%s.@ %a)@]" x (pp_expr ~compact) e
  | VFold (v1, t) ->
    Format.fprintf fmt "@[<hov 2>(fold[%a]@ %a)@]" (pp_val_ty ~compact) t (pp_value ~compact) v1
  | VNext v1 -> Format.fprintf fmt "(next %a)" (pp_value ~compact) v1
  | VTyLam (a, e) -> Format.fprintf fmt "@[<hov 2>(\xce\x9b%s.@ %a)@]" a (pp_expr ~compact) e

and pp_expr ~compact fmt (e : expr) =
  match e with
  | EVal v -> pp_value ~compact fmt v
  | EOp (op, vs) ->
    Format.fprintf fmt "@[<hov 2>%s(%a)@]" op
      (Format.pp_print_list ~pp_sep:pp_sep_comma (pp_value ~compact))
      vs
  | EApp (v1, v2) -> Format.fprintf fmt "@[<hov 2>(%a@ %a)@]" (pp_value ~compact) v1 (pp_value ~compact) v2
  | EEffApp (v, e1) -> Format.fprintf fmt "@[<hov 2>(%a@ %a)@]" (pp_value ~compact) v pp_syneff e1
  | ETyApp (v, t) -> Format.fprintf fmt "@[<hov 2>(%a@ [%a])@]" (pp_value ~compact) v (pp_val_ty ~compact) t
  | EUnfold v -> Format.fprintf fmt "(unfold %a)" (pp_value ~compact) v
  | ELet (x, e1, e2) ->
    Format.fprintf fmt "@[<v>let %s =@;<1 2>@[%a@]@ in@ %a@]" x (pp_expr ~compact) e1 (pp_expr ~compact) e2
  | EIf (v, e1, e2) ->
    Format.fprintf fmt "@[<v>if %a then@;<1 2>@[%a@]@ else@;<1 2>@[%a@]@]" (pp_value ~compact) v
      (pp_expr ~compact) e1 (pp_expr ~compact) e2
  | ENext e1 -> Format.fprintf fmt "(next %a)" (pp_expr ~compact) e1
  | ETensor (v1, v2) -> Format.fprintf fmt "(%a \xe2\x8a\x97 %a)" (pp_value ~compact) v1 (pp_value ~compact) v2
  | EPrev v -> Format.fprintf fmt "(prev %a)" (pp_value ~compact) v


(* ── semantic effects (φ, ι) ──────────────────────────────────────── *)

let rec pp_trace fmt (t : trace) =
  match t with
  | TEps -> Format.fprintf fmt "ε"
  | TVar x -> Format.fprintf fmt "%s" x
  | TLabel l -> Format.fprintf fmt "%s" l
  | TSeq (t1, t2) -> Format.fprintf fmt "@[<hov 2>%a@ \xe2\x8a\xb5 %a@]" pp_trace t1 pp_trace t2
  | TJoin (t1, t2) -> Format.fprintf fmt "@[<hov 2>%a@ \xe2\x88\xa8 %a@]" pp_trace t1 pp_trace t2
  | TStar t1 -> Format.fprintf fmt "(%a)*" pp_trace t1

let pp_eff_val fmt (e : eff_val) =
  let pp_inf fmt = function
    | None -> Format.fprintf fmt "\xe2\x8a\xa5"
    | Some loop -> Format.fprintf fmt "%a^\xcf\x89" pp_trace loop
  in
  Format.fprintf fmt "@[<hov 1>(%a,@ %a)@]" pp_trace e.fin pp_inf e.inf

let string_of_eff_val (e : eff_val) : string =
  let buf = Buffer.create 64 in
  let fmt = Format.formatter_of_buffer buf in
  Format.fprintf fmt "@[%a@]@." pp_eff_val e;
  Format.pp_print_flush fmt ();
  Buffer.contents buf

(* ── entry points ──────────────────────────────────────────────────── *)

let string_of_expr ?(compact = true) ?(margin = 100) (e : expr) : string =
  Hashtbl.reset legend;
  if compact then collect_expr e;
  let buf = Buffer.create 1024 in
  let fmt = Format.formatter_of_buffer buf in
  Format.pp_set_margin fmt margin;
  if compact && Hashtbl.length legend > 0 then begin
    Format.fprintf fmt "@[<v>(* ADT types, spelled out once: *)@ ";
    Hashtbl.iter
      (fun name t -> Format.fprintf fmt "@[<hov 2>(*   %s =@ %a *)@]@ " name (pp_val_ty ~compact:false) t)
      legend;
    Format.fprintf fmt "@]@,@,"
  end;
  Format.fprintf fmt "@[%a@]@." (pp_expr ~compact) e;
  Format.pp_print_flush fmt ();
  Buffer.contents buf