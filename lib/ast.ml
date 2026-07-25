(* ── Names ─────────────────────────────────────────────────────────── *)

type var = string (* x, y, z, f  — term variables          *)
type tvar = string (* α            — type variables          *)
type effvar = string (* X            — effect variables        *)
type label = string (* concrete effect labels (bold e)        *)
type op = string (* primitive operation names              *)

(* ── Base types  B ──────────────────────────────────────────────────
   B ::= unit | bool | int | ···
   ──────────────────────────────────────────────────────────────────── *)

type base_ty = TUnit | TBool | TInt | TString

(* ── Syntactic effects  e ───────────────────────────────────────────
   e ::= ε | X | e₁ ∨ e₂ | e₁ ⊵ e₂ | ▶e | e
   ──────────────────────────────────────────────────────────────────── *)

type syneff =
  | SEEmpty (* ε          — empty / pure          *)
  | SEVar of effvar (* X          — effect variable        *)
  | SEJoin of syneff * syneff (* e₁ ∨ e₂   — join           *)
  | SESeq of syneff * syneff (* e₁ ⊵ e₂   — sequential composition *)
  | SENext of syneff (* ▶e         — effect-level later       *)
  | SELabel of label (* e          — effect constructor  *)

(* ── Computation types  C ───────────────────────────────────────────
   C ::= T & e
   ──────────────────────────────────────────────────────────────────── *)
and comp_ty = {
  ct_val : val_ty; (* the return type T   *)
  ct_eff : syneff; (* the effect     e    *)
}

(* ── Value types  T ─────────────────────────────────────────────────
   T ::= B | α | T → C | ∀X.C | rec α.T | ▶T
   ──────────────────────────────────────────────────────────────────── *)
and val_ty =
  | TVBase of base_ty (* B              — base type          *)
  | TVVar of tvar (* α              — type variable       *)
  | TVArrow of val_ty * comp_ty (* T → C          — function type      *)
  | TVEffForall of effvar * comp_ty (* ∀X. C          — effect polymorphism *)
  | TVTyForall of tvar * comp_ty (* ∀T. C          — type polymorphism *)
  | TVRec of tvar * val_ty (* rec α. T       — recursive type      *)
  | TVLater of val_ty (* ▶T             — later / guarded     *)

(* ── First-order types  τ ───────────────────────────────────────────
   τ ::= B | ▶τ
   ──────────────────────────────────────────────────────────────────── *)

type first_order_ty =
  | FTBase of base_ty (* B    *)
  | FTNext of first_order_ty (* ▶τ   *)



(** Δ ::= ∅ | Δ, α <: β  — used in subtyping for recursive type variables *)
type subty_ctx = (tvar * tvar) list

(* ── Constants ─────────────────────────────────────────────────────── *)

type const = CUnit | CInt of int | CBool of bool | CString of string

(* ── Values  V ──────────────────────────────────────────────────────
   V ::= x | c | λx.M | ΛX.M | fold V | next V
   ──────────────────────────────────────────────────────────────────── *)

type value =
  | VVar of var (* x          — variable               *)
  | VConst of const (* c          — constant               *)
  | VLam of var * val_ty * expr (* λx. M      — term abstraction - annotated*)
  | VEffLam of effvar * expr (* ΛX. M      — effect abstraction      *)
  | VTyLam of tvar * expr (* ΛT. M      — Type abstraction      *)
  | VFold of value* val_ty (* fold V     — recursive type intro - annotated   *)
  | VNext of value (* next V     — later computation results      *)

(* ── Expressions  M ─────────────────────────────────────────────────
   M ::= V | o(V̄) | V₁ V₂ | V e | unfold V | let x = M₁ in M₂
       | if V then M₁ else M₂ | next M | V₁ ⊗ V₂ | prev V
   ──────────────────────────────────────────────────────────────────── *)
and expr =
  | EVal of value (* V                           *)
  | EOp of op * value list (* o(V̄)   — primitive op call  *)
  | EApp of value * value (* V₁ V₂  — term application   *)
  | EEffApp of value * syneff (* V e    — effect application  *)
  | ETyApp of value * val_ty (* V T    — type application*)
  | EUnfold of value (* unfold V                    *)
  | ELet of var * expr * expr (* let x = M₁ in M₂            *)
  | EIf of value * expr * expr (* if V then M₁ else M₂        *)
  | ENext of expr (* next M  — later computations        *)
  | ETensor of value * value (* V₁ ⊗ V₂ — lator applications       *)
  | EPrev of value (* prev V  — later type destructor  *)


(** ── Primitive operations and constants environment ────────────────
    It contains the types of constants, primitive operations, 
    and their associated effects.
 **)

type prim_env = {
  pe_const : const -> val_ty; (* type of constants *)
  pe_op : op -> val_ty list * val_ty; (* type of primitive operations *)
  pe_op_eff : op -> syneff (* effect of primitive operations *)
}

let default_prim : prim_env =
  {
    pe_const =
      (function
        | CUnit -> TVBase TUnit
        | CInt _ -> TVBase TInt
        | CBool _ -> TVBase TBool
        | CString _ -> TVBase TString);
    pe_op =
      (function
        | "add" ->  [ TVBase TInt; TVBase TInt ], TVBase TInt
        | _ -> failwith "unknown primitive operation");
    pe_op_eff =
      (function
        | "add" ->
          SEEmpty (* pure operations *)
        | _ -> failwith "unknown primitive operation");
  }

(* ── Typing contexts  Γ ─────────────────────────────────────────────
   Γ ::= ∅ | Γ, x : T | Γ, X | Γ, α
   ──────────────────────────────────────────────────────────────────── *)

type ctx_entry =
  | CEVar of var * val_ty (* x : T   — term variable binding    *)
  | CEEffVar of effvar (* X       — effect variable           *)
  | CETVar of tvar (* α       — type variable             *)

type ctx = ctx_entry list

(* ══════════════════════════════════════════════════════════════════
   Semantic effects: (φ, ι) pairs.
   φ (fin) : guaranteed finite prefix.
   ι (inf) : None if the effect terminates after φ; Some loop if,
             after φ, it repeats `loop` forever (ι = loop^ω).
   This is the value domain effect inference computes INTO - distinct
   from `syneff` above, which is the syntax effects are WRITTEN in.
   ══════════════════════════════════════════════════════════════════ *)

type trace =
  | TEps
  | TVar of string
  | TLabel of string
  | TSeq of trace * trace
  | TJoin of trace * trace
  | TStar of trace  (* zero or more repetitions - finitely many, still a finite trace *)

type eff_val = { fin : trace; inf : trace option }

let tseq (a : trace) (b : trace) : trace =
  match (a, b) with TEps, t | t, TEps -> t | _ -> TSeq (a, b)

let tjoin (a : trace) (b : trace) : trace =
  if a = b then a else TJoin (a, b)

let tstar (t : trace) : trace = match t with TEps -> TEps | TStar _ -> t | _ -> TStar t

let bottom : eff_val = { fin = TEps; inf = None }
let of_label (l : string) : eff_val = { fin = TLabel l; inf = None }
let of_var (x : string) : eff_val = { fin = TVar x; inf = None }
let diverge (loop : trace) : eff_val = { fin = TEps; inf = Some loop }

(* join (finite/infinite parts). If either side can diverge, that
   possibility survives into the join. *)
let join (e1 : eff_val) (e2 : eff_val) : eff_val =
  {
    fin = tjoin e1.fin e2.fin;
    inf =
      (match (e1.inf, e2.inf) with
       | None, None -> None
       | Some l, None | None, Some l -> Some l
       | Some l1, Some l2 -> Some (tjoin l1 l2));
  }

(* sequential composition ("add e2 after e1") - where the infinite
   part is actually generated: if e1 already diverges, e2 is
   unreachable and the composition's infinite part is just e1's;
   otherwise e1 terminates, so only THEN can e2's infinite part (if
   any) take over. *)
let seq (e1 : eff_val) (e2 : eff_val) : eff_val =
  match e1.inf with
  | Some loop -> { fin = e1.fin; inf = Some loop }
  | None -> { fin = tseq e1.fin e2.fin; inf = e2.inf }

(* modify: substitute effect variable x by `repl` throughout e. *)
let rec subst_trace (x : string) (repl : eff_val) (t : trace) : eff_val =
  match t with
  | TEps -> bottom
  | TVar y -> if y = x then repl else of_var y
  | TLabel l -> of_label l
  | TSeq (t1, t2) -> seq (subst_trace x repl t1) (subst_trace x repl t2)
  | TJoin (t1, t2) -> join (subst_trace x repl t1) (subst_trace x repl t2)
  | TStar t1 -> (
      let v = subst_trace x repl t1 in
      match v.inf with
      | Some l -> diverge l (* repeating something that itself never returns just IS that divergence *)
      | None -> { fin = tstar v.fin; inf = None })

let subst (x : string) (repl : eff_val) (e : eff_val) : eff_val =
  let via_fin = subst_trace x repl e.fin in
  match e.inf with
  | None -> via_fin
  | Some loop -> (
      (* x also occurs in the repeated loop body; if repl itself
         diverges, the loop can never get back around to repeating -
         it collapses into repl's own infinite behavior instead. *)
      let loop_val = subst_trace x repl loop in
      match loop_val.inf with
      | Some l -> seq via_fin (diverge l)
      | None -> seq via_fin (diverge loop_val.fin))