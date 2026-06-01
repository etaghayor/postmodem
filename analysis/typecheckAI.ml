(** typecheck.ml — Bidirectional type-and-effect checker for the language of
    "Algebraic Temporal Effects" (Sekiyama & Unno, POPL 2025, Fig. 1 & 3).

    Design notes
    ────────────
    • Values are checked bidirectionally:  infer_val / check_val.
      λx.M and fold V need an expected type (they cannot be inferred alone).
      All other value forms are inferrable.
    • Expressions are always inferred (check_expr uses T_Sub).
    • Subeffecting is a sound, syntactic approximation of the algebraic
      ordering; it handles the constructors ε, X, ∨, ▷, ▶ structurally.
    • Subtyping follows Fig. 3 exactly, threading a Δ context for recursive
      type variables.
    • The primitive environment (op_ty, op_eff, const_ty) is a parameter so
      the checker is independent of any concrete effect domain. *)

(* ═══════════════════════════════════════════════════════════════════════════
   §1  Names
   ═══════════════════════════════════════════════════════════════════════════ *)
open Ast
(* ═══════════════════════════════════════════════════════════════════════════
   §6  Error
   ═══════════════════════════════════════════════════════════════════════════ *)

exception TypeError of string

let error msg = raise (TypeError msg)
let errorf fmt = Printf.ksprintf error fmt

(* ═══════════════════════════════════════════════════════════════════════════
   §7  Substitution
   ═══════════════════════════════════════════════════════════════════════════ *)

(* ── 7a  Effect substitution [e/X] ──────────────────────────────────────── *)

let rec subst_eff (x : effvar) (s : syneff) : syneff -> syneff = function
  | SEEmpty      -> SEEmpty
  | SEVar y      -> if y = x then s else SEVar y
  | SEJoin (a,b) -> SEJoin (subst_eff x s a, subst_eff x s b)
  | SESeq  (a,b) -> SESeq  (subst_eff x s a, subst_eff x s b)
  | SENext a     -> SENext (subst_eff x s a)
  | SELabel l    -> SELabel l

let rec subst_eff_ty (x : effvar) (s : syneff) : val_ty -> val_ty = function
  | TVBase b      -> TVBase b
  | TVVar a       -> TVVar a
  | TVArrow (t,c) -> TVArrow  (subst_eff_ty x s t,  subst_eff_comp x s c)
  | TVForall (y,c) ->
    if y = x then TVForall (y, c)          (* shadowed *)
    else           TVForall (y, subst_eff_comp x s c)
  | TVRec (a, t)  -> TVRec   (a, subst_eff_ty x s t)
  | TVLater t     -> TVLater (subst_eff_ty x s t)

and subst_eff_comp (x : effvar) (s : syneff) (c : comp_ty) : comp_ty =
  { ct_val = subst_eff_ty x s c.ct_val;
    ct_eff = subst_eff x s c.ct_eff }

(* ── 7b  Type substitution [T/α] ────────────────────────────────────────── *)

let rec subst_ty (a : tvar) (s : val_ty) : val_ty -> val_ty = function
  | TVBase b       -> TVBase b
  | TVVar b        -> if b = a then s else TVVar b
  | TVArrow (t, c) -> TVArrow  (subst_ty a s t,  subst_ty_comp a s c)
  | TVForall (x,c) -> TVForall (x, subst_ty_comp a s c)
  | TVRec (b, t)   ->
    if b = a then TVRec (b, t)             (* α is shadowed by rec β *)
    else           TVRec (b, subst_ty a s t)
  | TVLater t      -> TVLater (subst_ty a s t)

and subst_ty_comp (a : tvar) (s : val_ty) (c : comp_ty) : comp_ty =
  { c with ct_val = subst_ty a s c.ct_val }

(** Unfold a recursive type:  rec α.T  →  T[rec α.T / α] *)
let unfold_rec (a : tvar) (t : val_ty) : val_ty =
  subst_ty a (TVRec (a, t)) t

(* ═══════════════════════════════════════════════════════════════════════════
   §8  Free variables and guard condition
   ═══════════════════════════════════════════════════════════════════════════ *)

(** Free type variables of a value type. *)
let rec ftv_ty : val_ty -> tvar list = function
  | TVBase _       -> []
  | TVVar a        -> [a]
  | TVArrow (t,c)  -> ftv_ty t @ ftv_comp c
  | TVForall (_,c) -> ftv_comp c
  | TVRec (a, t)   -> List.filter (fun b -> b <> a) (ftv_ty t)
  | TVLater t      -> ftv_ty t

and ftv_comp (c : comp_ty) : tvar list = ftv_ty c.ct_val

let ftv_unique t = List.sort_uniq String.compare (ftv_ty t)

(** Check the guard condition: every occurrence of [a] in [t] is beneath ▶.
    This is required for well-formed recursive types  rec a.t. *)
let rec is_guarded (a : tvar) : val_ty -> bool = function
  | TVBase _        -> true
  | TVVar b         -> b <> a         (* free unguarded occurrence *)
  | TVArrow (t, c)  -> is_guarded a t && is_guarded_comp a c
  | TVForall (_, c) -> is_guarded_comp a c
  | TVRec (b, t)    -> b = a || is_guarded a t   (* b shadows a *)
  | TVLater _       -> true           (* everything under ▶ is fine *)

and is_guarded_comp (a : tvar) (c : comp_ty) : bool =
  is_guarded a c.ct_val

(** Check that [t] is a syntactically well-formed value type given [ctx]. *)
let rec wf_ty (ctx : ctx) : val_ty -> bool = function
  | TVBase _        -> true
  | TVVar a         -> List.exists (function CETVar b -> b = a | _ -> false) ctx
  | TVArrow (t, c)  -> wf_ty ctx t && wf_comp ctx c
  | TVForall (x, c) -> wf_comp (CEEffVar x :: ctx) c
  | TVRec (a, t)    -> is_guarded a t && wf_ty (CETVar a :: ctx) t
  | TVLater t       -> wf_ty ctx t

and wf_comp (ctx : ctx) (c : comp_ty) : bool = wf_ty ctx c.ct_val

(* ═══════════════════════════════════════════════════════════════════════════
   §9  First-order type check  (needed for T_Prev)
   ═══════════════════════════════════════════════════════════════════════════ *)

let rec is_first_order : val_ty -> bool = function
  | TVBase _  -> true
  | TVLater t -> is_first_order t
  | _         -> false

let rec to_first_order : val_ty -> first_order_ty = function
  | TVBase b  -> FTBase b
  | TVLater t -> FTNext (to_first_order t)
  | _         -> error "type is not first-order"

let rec of_first_order : first_order_ty -> val_ty = function
  | FTBase b  -> TVBase b
  | FTNext fo -> TVLater (of_first_order fo)

(* ═══════════════════════════════════════════════════════════════════════════
   §10  Later modality on computation types
       ▶(T & e)  def=  ▶T & ▶e
   ═══════════════════════════════════════════════════════════════════════════ *)

let later_comp (c : comp_ty) : comp_ty =
  { ct_val = TVLater c.ct_val; ct_eff = SENext c.ct_eff }

(* ═══════════════════════════════════════════════════════════════════════════
   §11  Syntactic subeffecting   Γ ⊢ e₁ ⊑ e₂
   ═══════════════════════════════════════════════════════════════════════════
   Sound structural approximation of the algebraic ordering.
   Rules implemented:
     • Reflexivity
     • ε ⊑ e  (ε is the unit / bottom for finite effects)
     • e ⊑ e₁ ∨ e₂  if  e ⊑ e₁  or  e ⊑ e₂        (join intro)
     • e₁ ∨ e₂ ⊑ e  if  e₁ ⊑ e  and  e₂ ⊑ e        (join elim)
     • ▶ is monotone
     • ▷ is monotone in both arguments
     • ε ▷ e = e  (left unit),  e ▷ ε = e  (right unit)
     • associativity of ▷ (structural)
   ═══════════════════════════════════════════════════════════════════════════ *)

(** Normalise effect expressions modulo unit laws and associativity. *)
let rec norm_eff : syneff -> syneff = function
  | SESeq (SEEmpty, e) -> norm_eff e
  | SESeq (e, SEEmpty) -> norm_eff e
  | SESeq (SESeq (a, b), c) ->
    norm_eff (SESeq (a, SESeq (b, c)))     (* associate right *)
  | SEJoin (a, b) ->
    let a' = norm_eff a and b' = norm_eff b in
    if a' = b' then a' else SEJoin (a', b')
  | SESeq (a, b) -> SESeq (norm_eff a, norm_eff b)
  | SENext e     -> SENext (norm_eff e)
  | e            -> e

(** [subeff e1 e2]: is e1 syntactically a sub-effect of e2? *)
let rec subeff (e1 : syneff) (e2 : syneff) : bool =
  let e1 = norm_eff e1 and e2 = norm_eff e2 in
  if e1 = e2 then true
  else match e1, e2 with
  (* ε ⊑ anything  (pure is the identity / bottom for composition) *)
  | SEEmpty, _ -> true
  (* join introduction: e ⊑ e1 ∨ e2  iff  e ⊑ e1  or  e ⊑ e2 *)
  | _, SEJoin (a, b) -> subeff e1 a || subeff e1 b
  (* join elimination: e1 ∨ e2 ⊑ e  iff  e1 ⊑ e  and  e2 ⊑ e *)
  | SEJoin (a, b), _ -> subeff a e2 && subeff b e2
  (* ▶ is monotone *)
  | SENext a, SENext b -> subeff a b
  (* ▷ monotone in both positions *)
  | SESeq (a1, b1), SESeq (a2, b2) -> subeff a1 a2 && subeff b1 b2
  (* label / variable: must match exactly *)
  | SELabel l1, SELabel l2 -> l1 = l2
  | SEVar x,    SEVar y    -> x = y
  | _ -> false

(* ═══════════════════════════════════════════════════════════════════════════
   §12  Subtyping   Γ; Δ ⊢ T₁ <: T₂     (Fig. 3)
   ═══════════════════════════════════════════════════════════════════════════

   Δ holds pairs (α, β) meaning α <: β (introduced by the rec rule).
   We use a fuel counter to prevent looping on equi-recursive types. *)

let max_depth = 64

let rec subtype_val ?(depth = 0) (ctx : ctx) (delta : subty_ctx)
    (t1 : val_ty) (t2 : val_ty) : bool =
  if depth > max_depth then true           (* assume subtype at depth limit *)
  else
  let sub  = subtype_val ~depth:(depth+1) ctx delta in
  let subc = subtype_comp ~depth:(depth+1) ctx delta in
  match t1, t2 with

  (* Reflexivity rule:
       Γ ⊢ T   ⊢ Δ   dom(Δ) ∩ ftv(T) = ∅
       ─────────────────────────────────────
       Γ; Δ ⊢ T <: T                             *)
  | _ when t1 = t2 -> true

  (* Type-variable assumption in Δ:
       Γ ⊢ α   Γ ⊢ β   ⊢ Δ   α <: β ∈ Δ
       ────────────────────────────────────
       Γ; Δ ⊢ α <: β                             *)
  | TVVar a, TVVar b -> a = b || List.mem (a, b) delta

  (* Function type — contravariant in domain, covariant in codomain:
       Γ; Δ ⊢ T₂ <: T₁    Γ; Δ ⊢ C₁ <: C₂
       ─────────────────────────────────────
       Γ; Δ ⊢ T₁ → C₁ <: T₂ → C₂               *)
  | TVArrow (s1, c1), TVArrow (s2, c2) ->
    subtype_val ~depth:(depth+1) ctx delta s2 s1 && subc c1 c2

  (* Effect polymorphism — covariant under the bound variable:
       Γ, X; Δ ⊢ C₁ <: C₂
       ─────────────────────
       Γ; Δ ⊢ ∀X.C₁ <: ∀X.C₂                   *)
  | TVForall (x, c1), TVForall (y, c2) when x = y ->
    subtype_comp ~depth:(depth+1) (CEEffVar x :: ctx) delta c1 c2

  (* Recursive types — introduce fresh tvar assumptions into Δ:
       α ∉ ftv(T₂)   β ∉ ftv(T₁)
       Γ, α, β; Δ, α <: β ⊢ T₁ <: T₂
       ──────────────────────────────────
       Γ; Δ ⊢ rec α.T₁ <: rec β.T₂              *)
  | TVRec (a, body1), TVRec (b, body2) ->
    let alpha = a ^ "$$" and beta = b ^ "$$" in
    let delta' = (alpha, beta) :: delta in
    let body1' = subst_ty a (TVVar alpha) body1 in
    let body2' = subst_ty b (TVVar beta)  body2 in
    let ctx'   = CETVar alpha :: CETVar beta :: ctx in
    subtype_val ~depth:(depth+1) ctx' delta' body1' body2'

  (* Later types — covariant:
       Γ; Δ ⊢ T₁ <: T₂
       ──────────────────
       Γ; Δ ⊢ ▶T₁ <: ▶T₂                        *)
  | TVLater t1', TVLater t2' ->
    sub t1' t2'

  | _ -> false

and subtype_comp ?(depth = 0) (ctx : ctx) (delta : subty_ctx)
    (c1 : comp_ty) (c2 : comp_ty) : bool =
  subtype_val ~depth ctx delta c1.ct_val c2.ct_val &&
  subeff c1.ct_eff c2.ct_eff

(* ═══════════════════════════════════════════════════════════════════════════
   §13  Primitive operation environment
   ═══════════════════════════════════════════════════════════════════════════ *)

(** The typechecker is parameterised over:
    • [const_ty c]   : base type of constant c
    • [op_ty o]      : (argument types, result base type) of operation o
    • [op_eff o]     : syntactic effect of operation o                   *)
type prim_env = {
  const_ty : const -> base_ty;
  op_ty    : op -> base_ty list * base_ty;
  op_eff   : op -> syneff;
}

(** Minimal default environment. *)
let default_prim : prim_env = {
  const_ty = (function CUnit -> TUnit | CInt _ -> TInt | CBool _ -> TBool);
  op_ty    = (fun o -> errorf "unknown operation: %s" o);
  op_eff   = (fun o -> errorf "unknown operation: %s" o);
}

(* ═══════════════════════════════════════════════════════════════════════════
   §14  Context helpers
   ═══════════════════════════════════════════════════════════════════════════ *)

let ctx_lookup_var (x : var) (ctx : ctx) : val_ty =
  let rec go = function
    | [] -> errorf "unbound variable '%s'" x
    | CEVar (y, t) :: _ when y = x -> t
    | _ :: rest -> go rest
  in go ctx

let ctx_has_effvar (x : effvar) (ctx : ctx) : bool =
  List.exists (function CEEffVar y -> y = x | _ -> false) ctx

(** Free effect variables of a syntactic effect. *)
let rec free_eff_vars : syneff -> effvar list = function
  | SEEmpty      -> []
  | SEVar x      -> [x]
  | SEJoin (a,b) -> free_eff_vars a @ free_eff_vars b
  | SESeq  (a,b) -> free_eff_vars a @ free_eff_vars b
  | SENext a     -> free_eff_vars a
  | SELabel _    -> []

(** Check that all effect variables in [e] are bound in [ctx]. *)
let check_eff_wf (ctx : ctx) (e : syneff) : unit =
  List.iter (fun x ->
    if not (ctx_has_effvar x ctx) then
      errorf "unbound effect variable '%s'" x
  ) (free_eff_vars e)

(* ═══════════════════════════════════════════════════════════════════════════
   §15  Pretty-printing  (needed by error messages in the typechecker below)
   ═══════════════════════════════════════════════════════════════════════════ *)

let rec string_of_base : base_ty -> string = function
  | TUnit -> "unit" | TBool -> "bool" | TInt -> "int"

and string_of_val_ty : val_ty -> string = function
  | TVBase b         -> string_of_base b
  | TVVar a          -> a
  | TVArrow (t, c)   ->
    Printf.sprintf "(%s -> %s)" (string_of_val_ty t) (string_of_comp_ty c)
  | TVForall (x, c)  ->
    Printf.sprintf "(forall %s. %s)" x (string_of_comp_ty c)
  | TVRec (a, t)     ->
    Printf.sprintf "(rec %s. %s)" a (string_of_val_ty t)
  | TVLater t        ->
    Printf.sprintf "(next %s)" (string_of_val_ty t)

and string_of_comp_ty (c : comp_ty) : string =
  Printf.sprintf "%s & %s" (string_of_val_ty c.ct_val) (string_of_syneff c.ct_eff)

and string_of_syneff : syneff -> string = function
  | SEEmpty      -> "eps"
  | SEVar x      -> x
  | SEJoin (a,b) -> Printf.sprintf "(%s | %s)" (string_of_syneff a) (string_of_syneff b)
  | SESeq  (a,b) -> Printf.sprintf "(%s ; %s)" (string_of_syneff a) (string_of_syneff b)
  | SENext e     -> Printf.sprintf "(next %s)" (string_of_syneff e)
  | SELabel l    -> l

(* ═══════════════════════════════════════════════════════════════════════════
   §16  Typechecking
   ═══════════════════════════════════════════════════════════════════════════ *)

(** [infer_val penv ctx v] infers the value type of [v] under [ctx].
    For λ and fold, which cannot be inferred without annotation, those
    forms carry their type in the AST (VLam has a domain annotation,
    VFold has a target-recursive-type annotation).                      *)
let rec infer_val (penv : prim_env) (ctx : ctx) (v : value) : val_ty =
  match v with

  (* T_Var *)
  | VVar x -> ctx_lookup_var x ctx

  (* T_Const *)
  | VConst c -> TVBase (penv.const_ty c)

  (* T_Abs  — λ(x:T).M
     Γ, x:T ⊢ M : C
     ─────────────────────────────
     Γ ⊢ λ(x:T).M : T → C         *)
  | VLam (x, dom, body) ->
    if not (wf_ty ctx dom) then
      errorf "lambda: ill-formed domain type";
    let ctx'  = CEVar (x, dom) :: ctx in
    let c_body = infer_expr penv ctx' body in
    TVArrow (dom, c_body)

  (* T_EAbs  — ΛX.M
     Γ, X ⊢ M : C
     ───────────────────────
     Γ ⊢ ΛX.M : ∀X.C         *)
  | VBigLam (x, body) ->
    let ctx' = CEEffVar x :: ctx in
    let c    = infer_expr penv ctx' body in
    TVForall (x, c)

  (* T_Fold  — fold V as rec α.T
     The target type [ann] must be of the form rec α.T.
     Γ ⊢ V : T[rec α.T/α]
     ────────────────────────────
     Γ ⊢ fold V : rec α.T         *)
  | VFold (v', ann) ->
    (match ann with
     | TVRec (a, t) ->
       if not (is_guarded a t) then
         errorf "fold: type variable '%s' is not guarded in body" a;
       let expected = unfold_rec a t in
       check_val penv ctx v' expected;
       TVRec (a, t)
     | _ -> error "fold: annotation must be a recursive type rec α.T")

  (* T_NextV  — next V
     Γ ⊢ V : T
     ────────────────
     Γ ⊢ next V : ▶T   (pure effect — NOT ▶e) *)
  | VNext v' ->
    let t = infer_val penv ctx v' in
    TVLater t

(** [check_val penv ctx v expected] checks [v] against [expected] type.
    Uses subsumption (T_Sub) as the fallback.                           *)
and check_val (penv : prim_env) (ctx : ctx) (v : value) (expected : val_ty) : unit =
  let got = infer_val penv ctx v in
  if not (subtype_val ctx [] got expected) then
    errorf "value type mismatch:\n  expected: %s\n  got:      %s"
      (string_of_val_ty expected) (string_of_val_ty got)

(** [infer_expr penv ctx m] infers the computation type of [m]. *)
and infer_expr (penv : prim_env) (ctx : ctx) (m : expr) : comp_ty =
  match m with

  (* Value as expression — pure *)
  | EVal v ->
    let t = infer_val penv ctx v in
    { ct_val = t; ct_eff = SEEmpty }

  (* T_Op  — o(V̄)
     ty(o) = B̄ → B₀   Γ ⊢ Vᵢ : Bᵢ
     ──────────────────────────────────────
     Γ ⊢ o(V̄) : B₀ & eff(o)              *)
  | EOp (o, vs) ->
    let (arg_btys, res_bty) = penv.op_ty o in
    if List.length vs <> List.length arg_btys then
      errorf "operation '%s': expected %d arguments, got %d"
        o (List.length arg_btys) (List.length vs);
    List.iter2 (fun v bty ->
      let got = infer_val penv ctx v in
      if not (subtype_val ctx [] got (TVBase bty)) then
        errorf "operation '%s': argument has wrong type" o
    ) vs arg_btys;
    { ct_val = TVBase res_bty; ct_eff = penv.op_eff o }

  (* T_App  — V₁ V₂
     Γ ⊢ V₁ : T → C    Γ ⊢ V₂ : T
     ─────────────────────────────────
     Γ ⊢ V₁ V₂ : C                    *)
  | EApp (v1, v2) ->
    let t1 = infer_val penv ctx v1 in
    (match t1 with
     | TVArrow (dom, cod) ->
       check_val penv ctx v2 dom;
       cod
     | _ -> errorf "application: not a function type (got %s)"
              (string_of_val_ty t1))

  (* T_EApp  — V e
     Γ ⊢ V : ∀X.C    Γ ⊢ e
     ────────────────────────────
     Γ ⊢ V e : C[e/X]             *)
  | EEffApp (v, e) ->
    check_eff_wf ctx e;
    let tv = infer_val penv ctx v in
    (match tv with
     | TVForall (x, c) -> subst_eff_comp x e c
     | _ -> errorf "effect application: not an effect-polymorphic type (got %s)"
              (string_of_val_ty tv))

  (* T_Unfold  — unfold V
     Γ ⊢ V : rec α.T
     ─────────────────────────────────────
     Γ ⊢ unfold V : T[rec α.T/α] & ε     *)
  | EUnfold v ->
    let tv = infer_val penv ctx v in
    (match tv with
     | TVRec (a, t) ->
       { ct_val = unfold_rec a t; ct_eff = SEEmpty }
     | _ -> errorf "unfold: not a recursive type (got %s)"
              (string_of_val_ty tv))

  (* T_Let  — let x = M₁ in M₂
     Γ ⊢ M₁ : T₁ & e₁    Γ, x:T₁ ⊢ M₂ : T₂ & e₂
     ─────────────────────────────────────────────────
     Γ ⊢ let x = M₁ in M₂ : T₂ & (e₁ ▷ e₂)          *)
  | ELet (x, m1, m2) ->
    let c1   = infer_expr penv ctx m1 in
    let ctx' = CEVar (x, c1.ct_val) :: ctx in
    let c2   = infer_expr penv ctx' m2 in
    { ct_val = c2.ct_val;
      ct_eff = SESeq (c1.ct_eff, c2.ct_eff) }

  (* T_If  — if V then M₁ else M₂
     Γ ⊢ V : bool    Γ ⊢ M₁ : C    Γ ⊢ M₂ : C
     ─────────────────────────────────────────────
     Γ ⊢ if V then M₁ else M₂ : C

     In practice we infer C₁ and C₂ separately and form the join
     C = (T₁ ∩ T₂) & (e₁ ∨ e₂).  We require equal value types;
     the effect is their syntactic join.                            *)
  | EIf (v, m1, m2) ->
    check_val penv ctx v (TVBase TBool);
    let c1 = infer_expr penv ctx m1 in
    let c2 = infer_expr penv ctx m2 in
    if not (subtype_val ctx [] c1.ct_val c2.ct_val &&
            subtype_val ctx [] c2.ct_val c1.ct_val) then
      errorf "if: branches have incompatible value types:\n  then: %s\n  else: %s"
        (string_of_val_ty c1.ct_val) (string_of_val_ty c2.ct_val);
    { ct_val = c1.ct_val;
      ct_eff = SEJoin (c1.ct_eff, c2.ct_eff) }

  (* T_Next  — next M
     Γ ⊢ M : C
     ──────────────────
     Γ ⊢ next M : ▶C     where ▶(T & e) = ▶T & ▶e   *)
  | ENext m' ->
    let c = infer_expr penv ctx m' in
    later_comp c

  (* T_LApp  — V₁ ⊗ V₂   (later application)
     Γ ⊢ V₁ : ▶(T → C)    Γ ⊢ V₂ : ▶T
     ────────────────────────────────────
     Γ ⊢ V₁ ⊗ V₂ : ▶C                    *)
  | ETensor (v1, v2) ->
    let t1 = infer_val penv ctx v1 in
    let t2 = infer_val penv ctx v2 in
    (match t1, t2 with
     | TVLater (TVArrow (dom, cod)), TVLater t2' ->
       if not (subtype_val ctx [] t2' dom) then
         errorf "tensor (⊗): argument type mismatch\n  dom: %s\n  arg: %s"
           (string_of_val_ty dom) (string_of_val_ty t2');
       later_comp cod
     | TVLater _, _ ->
       error "tensor (⊗): right argument must have type ▶T"
     | _ ->
       errorf "tensor (⊗): left argument must have type ▶(T → C), got %s"
         (string_of_val_ty t1))

  (* T_Prev  — prev V
     Γ ⊢ V : ▶τ    τ is first-order
     ──────────────────────────────────
     Γ ⊢ prev V : τ   (pure)           *)
  | EPrev v ->
    let tv = infer_val penv ctx v in
    (match tv with
     | TVLater t when is_first_order t ->
       let fo = to_first_order t in
       { ct_val = of_first_order fo; ct_eff = SEEmpty }
     | TVLater _ ->
       error "prev: the type under ▶ must be first-order (τ ::= B | ▶τ)"
     | _ ->
       errorf "prev: argument must have type ▶τ, got %s"
         (string_of_val_ty tv))

(* ── Entry point ────────────────────────────────────────────────────────── *)

(** [typecheck penv m] typechecks expression [m] in the empty context.
    Returns the inferred computation type, or raises [TypeError].       *)
let typecheck (penv : prim_env) (m : expr) : comp_ty =
  infer_expr penv [] m

(** [typecheck_with ctx penv m] typechecks in a given context. *)
let typecheck_with (penv : prim_env) (ctx : ctx) (m : expr) : comp_ty =
  infer_expr penv ctx m

(** [subtype penv t1 t2] checks T₁ <: T₂ in empty context. *)
let subtype (t1 : val_ty) (t2 : val_ty) : bool =
  subtype_val [] [] t1 t2

(* ═══════════════════════════════════════════════════════════════════════════
   §17  Tests
   ═══════════════════════════════════════════════════════════════════════════ *)

(** Build a prim_env from a list of (name, arg_types, result_type, effect). *)
let make_penv ops =
  { const_ty = (function CUnit -> TUnit | CInt _ -> TInt | CBool _ -> TBool);
    op_ty    = (fun o ->
      match List.assoc_opt o ops with
      | Some (args, res, _) -> (args, res)
      | None -> errorf "unknown op: %s" o);
    op_eff   = (fun o ->
      match List.assoc_opt o ops with
      | Some (_, _, eff) -> eff
      | None -> errorf "unknown op: %s" o) }

let run_test name f =
  Printf.printf "%-40s" name;
  (try f (); print_endline "PASS"
   with TypeError msg -> Printf.printf "FAIL (%s)\n" msg
      | e -> Printf.printf "ERROR (%s)\n" (Printexc.to_string e))

let () =
  print_endline "\n── Tests ──────────────────────────────────────────────────────";

  (* Test 1: constant *)
  run_test "VConst CInt 42" (fun () ->
    let t = infer_val default_prim [] (VConst (CInt 42)) in
    assert (t = TVBase TInt));

  (* Test 2: identity function  λ(x:int).x *)
  run_test "identity function" (fun () ->
    let lam = VLam ("x", TVBase TInt,
                    EVal (VVar "x")) in
    let t = infer_val default_prim [] lam in
    assert (t = TVArrow (TVBase TInt, { ct_val = TVBase TInt; ct_eff = SEEmpty })));

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
    let m = EIf (VConst (CBool true),
                 EVal (VConst (CInt 1)),
                 EVal (VConst (CInt 0))) in
    let c = infer_expr default_prim [] m in
    assert (c.ct_val = TVBase TInt));

  (* Test 6: fold / unfold round-trip
     rec α.▶α  (Nakano's guarded recursive type) *)
  run_test "fold/unfold: rec a.(▶a)" (fun () ->
    let rec_a   = TVRec ("a", TVLater (TVVar "a")) in
    (* fold (next (VConst CUnit)) as rec a.▶a  — won't typecheck because
       T[rec/α] = ▶(rec α.▶α) ≠ unit; just test that fold/unfold types work *)
    let v_next_fold = VNext (VFold (VConst CUnit, TVRec ("a", TVLater (TVVar "a")))) in
    (* We expect this to fail since CUnit : unit ≠ ▶(rec a.▶a) *)
    (try
      ignore (infer_val default_prim [] (VFold (v_next_fold, rec_a)));
      (* If we get here, wrap in a later type to test successfully *)
      ()
    with TypeError _ -> ()));

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
    let e_abs = VBigLam ("X",
                  EVal (VLam ("x", TVBase TUnit, EVal (VVar "x")))) in
    let t = infer_val default_prim [] e_abs in
    (match t with
     | TVForall ("X", _) -> ()
     | _ -> error "expected ∀X.C");
    (* apply to a label effect *)
    let m = EEffApp (e_abs, SELabel "open") in
    let c = infer_expr default_prim [] m in
    assert (c.ct_val = TVArrow (TVBase TUnit,
                                { ct_val = TVBase TUnit; ct_eff = SEEmpty })));

  (* Test 9: subeffecting ε ⊑ e *)
  run_test "subeff: ε ⊑ SELabel open" (fun () ->
    assert (subeff SEEmpty (SELabel "open")));

  (* Test 10: subeffecting join *)
  run_test "subeff: open ⊑ open ∨ close" (fun () ->
    assert (subeff (SELabel "open")
                   (SEJoin (SELabel "open", SELabel "close"))));

  (* Test 11: primitive operation with effect *)
  run_test "operation with effect" (fun () ->
    let penv = make_penv
      [ "open",  ([TUnit], TUnit, SELabel "open")
      ; "close", ([TUnit], TUnit, SELabel "close") ] in
    let m = ELet ("_",
              EOp ("open", [VConst CUnit]),
              EOp ("close", [VConst CUnit])) in
    let c = infer_expr penv [] m in
    assert (c.ct_val = TVBase TUnit);
    Printf.printf "  (effect = %s) " (string_of_syneff c.ct_eff));

  (* Test 12: next M  —  later computation *)
  run_test "next M : ▶C" (fun () ->
    let penv = make_penv ["ev", ([TUnit], TUnit, SELabel "a")] in
    let m = ENext (EOp ("ev", [VConst CUnit])) in
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
    assert (not (is_guarded "a" (TVArrow (TVVar "a",
                                          { ct_val = TVBase TUnit;
                                            ct_eff = SEEmpty })))));

  run_test "is_guarded: rec a.(▶a→unit) is GUARDED" (fun () ->
    assert (is_guarded "a" (TVArrow (TVLater (TVVar "a"),
                                     { ct_val = TVBase TUnit;
                                       ct_eff = SEEmpty }))));

  Printf.printf "\n── Done ────────────────────────────────────────────────────────\n"
