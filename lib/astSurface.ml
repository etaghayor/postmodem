(* ── Names ─────────────────────────────────────────────────────────── *)

type varS = string (* x, y, z, f  — term variables          *)
type tvarS = string (* α            — type variables          *)
type effvarS = string (* X            — effect variables        *)
type labelS = string (* concrete effect labels (bold e)        *)
type opS = string (* primitive operation names              *)

(* ── Base types  B ──────────────────────────────────────────────────
   B ::= unit | bool | int | ···
   ──────────────────────────────────────────────────────────────────── *)

type base_tyS = TUnitS | TBoolS | TIntS

(* ── Syntactic effects  e ───────────────────────────────────────────
   e ::= ε | X | e₁ ∨ e₂ | e₁ ⊵ e₂ | ▶e | e
   ──────────────────────────────────────────────────────────────────── *)

type syneffS =
  | SEEmptyS (* ε          — empty / pure          *)
  | SEVarS of effvarS (* X          — effect variable        *)
  | SEJoinS of syneffS * syneffS   (* e₁ ∨ e₂   — join           *)
  | SESeqS of syneffS * syneffS   (* e₁ ⊵ e₂   — sequential composition *)
  | SELabelS of labelS  (* e          — effect constructor  *)

(* ── Computation types  C ───────────────────────────────────────────
   C ::= T & e
   ──────────────────────────────────────────────────────────────────── *)
and comp_tyS = {
  ct_valS : val_tyS; (* the return type T   *)
  ct_effS : syneffS; (* the effect     e    *)
}

(* ── valueS types  T ─────────────────────────────────────────────────
   T ::= B | α | T → C | ∀X.C | rec α.T | ▶T
   ──────────────────────────────────────────────────────────────────── *)
and val_tyS =
  | TVBaseS of base_tyS (* B              — base type          *)
  | TVVarS of tvarS (* α              — type variable       *)
  | TVArrowS of val_tyS * comp_tyS (* T → C          — function type      *)
  | TVForallS of effvarS  * comp_tyS (* ∀X. C          — effect polymorphism *)
  | TVRecS of tvarS* val_tyS(* rec α. T       — recursive type      *)
  | TVSumS of (string * val_tyS list) list (* T₁ + T₂ + ... + Tn — sum type *) (*val_tySlist for individual pattern matching*)
  | TVNamedS of string (* instance of sum type *)

(* ── First-order types  τ ───────────────────────────────────────────
   τ ::= B | ▶τ
   ──────────────────────────────────────────────────────────────────── *)

type first_order_tyS =
  | FTBaseS of base_tyS(* B    *)

type patternS =
  | PWildcardS (* _ *)
  | PvarS of varS (* x *)
  | PConstructorS of string * patternS list (* C(p1, p2, ..., pn) *)


(** Δ ::= ∅ | Δ, α <: β  — used in subtyping for recursive type variables *)
type subty_ctxS = (tvarS * tvarS) list

(* ── Constants ─────────────────────────────────────────────────────── *)

type constS = CUnitS | CIntS of int | CBoolS of bool

(* ── valueSs  V ──────────────────────────────────────────────────────
   V ::= x | c | λx.M | ΛX.M 
   ──────────────────────────────────────────────────────────────────── *)

type valueS =
  | VvarS of varS (* x          — variable               *)
  | VConstS of constS (* c          — constant               *)
  | VLamS of varS * val_tyS * exprS (* λx. M      — term abstraction - annotated*)
  | VBigLam of effvarS  * exprS (* ΛX. M      — effect abstraction      *)
  | VConstSructor of string * valueS list (* C(V1, V2, ..., Vn) — sum type constructor with named type*)

(* ── exprSessions  M ─────────────────────────────────────────────────
   M ::= V | o(V̄) | V₁ V₂ | V e | let x = M₁ in M₂
       | if V then M₁ else M₂ | V₁ ⊗ V₂
   ──────────────────────────────────────────────────────────────────── *)
and exprS =
  | EValS of valueS (* V                           *)
  | EopS of opS * valueS list (* o(V̄)   — primitive opS call  *)
  | EAppS of valueS * valueS (* V₁ V₂  — term application   *)
  | EEffAppS of valueS * syneffS   (* V e    — effect application  *)
  | ELetS of varS * exprS * exprS (* let x = M₁ in M₂            *)
  | EIfS of valueS * exprS * exprS (* if V then M₁ else M₂        *)
  | ETensorS of valueS * valueS (* V₁ ⊗ V₂ — lator applications       *)
  | EMatchS of valueS * (patternS * exprS) list (* match V with p1 -> M1 | ... | pn -> Mn *)


(** ── Primitive operations and constants environment ────────────────
    It contains the types of constants, primitive operations, 
    and their associated effects.
 **)

type prim_envS = {
  pe_constS : constS -> val_tyS; (* type of constants *)
  pe_opS : opS -> val_tyS list * val_tyS ; (* type of primitive operations *)
  pe_op_effS : opS -> syneffS   (* effect of primitive operations *)
}

let default_prim : prim_envS =
  {
    pe_constS =
      (function
        | CUnitS -> TVBaseS TUnitS
        | CIntS _ -> TVBaseS TIntS
        | CBoolS _ -> TVBaseS TBoolS);
    pe_opS =
      (function
        | "add" ->  [ TVBaseS TIntS; TVBaseS TIntS ], TVBaseS TIntS
        | _ -> failwith "unknown primitive operation");
    pe_op_effS =
      (function
        | "add" ->
          SEEmptyS (* pure operations *)
        | _ -> failwith "unknown primitive operation");
  }

(* ── Typing contexts  Γ ─────────────────────────────────────────────
   Γ ::= ∅ | Γ, x : T | Γ, X | Γ, α
   ──────────────────────────────────────────────────────────────────── *)

type ctx_entryS =
  | CEvarS of varS * val_tyS(* x : T   — term variable binding    *)
  | CEeffvarS  of effvarS  (* X       — effect variable           *)
  | CEtvarS of tvarS (* α       — type variable             *)

type ctxS = ctx_entryS list
