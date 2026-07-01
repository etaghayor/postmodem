(* ── Names ─────────────────────────────────────────────────────────── *)

type var = string (* x, y, z, f  — term variables          *)
type tvar = string (* α            — type variables          *)
type effvar = string (* X            — effect variables        *)
type label = string (* concrete effect labels (bold e)        *)
type op = string (* primitive operation names              *)

(* ── Base types  B ──────────────────────────────────────────────────
   B ::= unit | bool | int | ···
   ──────────────────────────────────────────────────────────────────── *)

type base_ty = TUnit | TBool | TInt

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
  | TVForall of effvar * comp_ty (* ∀X. C          — effect polymorphism *)
  | TVRec of tvar * val_ty (* rec α. T       — recursive type      *)
  | TVLater of val_ty (* ▶T             — later / guarded     *)
  | TVSum of (string * val_ty list) list (* T₁ + T₂ + ... + Tn — sum type *) (*val_ty list for individual pattern matching*)
  | TVNamed of string (* instance of sum type *)

(* ── First-order types  τ ───────────────────────────────────────────
   τ ::= B | ▶τ
   ──────────────────────────────────────────────────────────────────── *)

type first_order_ty =
  | FTBase of base_ty (* B    *)
  | FTNext of first_order_ty (* ▶τ   *)

type pattern =
  | PWildcard (* _ *)
  | PVar of var (* x *)
  | PConstructor of string * pattern list (* C(p1, p2, ..., pn) *)


(** Δ ::= ∅ | Δ, α <: β  — used in subtyping for recursive type variables *)
type subty_ctx = (tvar * tvar) list

(* ── Constants ─────────────────────────────────────────────────────── *)

type const = CUnit | CInt of int | CBool of bool

(* ── Values  V ──────────────────────────────────────────────────────
   V ::= x | c | λx.M | ΛX.M | fold V | next V
   ──────────────────────────────────────────────────────────────────── *)

type value =
  | VVar of var (* x          — variable               *)
  | VConst of const (* c          — constant               *)
  | VLam of var * val_ty * expr (* λx. M      — term abstraction - annotated*)
  | VBigLam of effvar * expr (* ΛX. M      — effect abstraction      *)
  | VFold of value* val_ty (* fold V     — recursive type intro - annotated   *)
  | VNext of value (* next V     — later computation results      *)
  | VConstructor of string * value list (* C(V1, V2, ..., Vn) — sum type constructor with named type*)

(* ── Expressions  M ─────────────────────────────────────────────────
   M ::= V | o(V̄) | V₁ V₂ | V e | unfold V | let x = M₁ in M₂
       | if V then M₁ else M₂ | next M | V₁ ⊗ V₂ | prev V
   ──────────────────────────────────────────────────────────────────── *)
and expr =
  | EVal of value (* V                           *)
  | EOp of op * value list (* o(V̄)   — primitive op call  *)
  | EApp of value * value (* V₁ V₂  — term application   *)
  | EEffApp of value * syneff (* V e    — effect application  *)
  | EUnfold of value (* unfold V                    *)
  | ELet of var * expr * expr (* let x = M₁ in M₂            *)
  | EIf of value * expr * expr (* if V then M₁ else M₂        *)
  | ENext of expr (* next M  — later computations        *)
  | ETensor of value * value (* V₁ ⊗ V₂ — lator applications       *)
  | EPrev of value (* prev V  — later type destructor  *)
  | EMatch of value * (pattern * expr) list (* match V with p1 -> M1 | ... | pn -> Mn *)


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
        | CBool _ -> TVBase TBool);
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
