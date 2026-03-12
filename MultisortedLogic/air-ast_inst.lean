import MultisortedLogic.Semantics

namespace MSFirstOrder

namespace MSLanguage

open MSLanguage

universe u

inductive AirSorts where
  | Bool
  | Int
  | Fun
  | Named (name: String)
  | BitVec (width: UInt32)
deriving Repr, Inhabited, DecidableEq, Hashable

abbrev Poly := AirSorts.Named "Poly"

-- Type in air
abbrev TYPE := AirSorts.Named "TYPE"

variable {α : AirSorts → Type*}

open AirSorts

inductive airFunc : List AirSorts → AirSorts → Type
  -- air-ast :: Const
  | True : airFunc [] Bool
  | False : airFunc [] Bool
  | Nat : (i : String) → airFunc [] Poly
  | BitVector : (bits : List Nat) → (width: UInt32) → airFunc [] (BitVec width)

  -- air-ast :: Binop
  | Implies : airFunc [Bool, Bool] Bool
  | Eq : airFunc [Int, Int] Bool
  | Le : airFunc [Int, Int] Bool
  | Ge : airFunc [Int, Int] Bool
  | Lt : airFunc [Int, Int] Bool
  | Gt : airFunc [Int, Int] Bool
  | EuclideanDiv : airFunc [Int, Int] Int
  | EuclideanMod : airFunc [Int, Int] Int
  -- | Relation (rel: Relation) (idx: UInt64)
  -- | BitXor
  -- | BitAnd
  -- | BitOr
  -- | BitAdd
  -- | BitSub
  -- | BitMul
  -- | BitUDiv
  -- | BitUMod
  | BitShr : airFunc [Poly, Poly] Int
  | Bitshl : airFunc [Poly, Poly] Int
  -- | BitConcat : (w w': UInt32) → airFunc [BitVec w, BitVec w'] (BitVec (w+w'))
  --| FieldUpdate (ident: String)

  -- air-ast :: UnaryOp
  | Not : airFunc [Bool] Bool
  | BitNot : airFunc [Poly] Int
  -- | BitExtract (high: UInt32) (low: UInt32)
  -- | BitZeroExtend (fr: UInt32)
  -- | BitSignExtend (fr: UInt32)

  -- air-ast :: MultiOp
  | And : (n : Nat) → airFunc (List.replicate n Bool) Bool
  | Or : (n : Nat) → airFunc (List.replicate n Bool) Bool
  | Xor : (n : Nat) → airFunc (List.replicate n Bool) Bool
  | Add : airFunc [Int, Int] Int
  | Sub : airFunc [Int, Int] Int
  | Mul : airFunc [Int, Int] Int
  -- | Distinct

  -- Functions in air examples:

  -- 1. Related to hastype:
  | BOOL : airFunc [] TYPE
  | INT : airFunc [] TYPE
  | NAT : airFunc [] TYPE
  | CHAR : airFunc [] TYPE
  | USIZE : airFunc [] TYPE
  | ISIZE : airFunc [] TYPE
  | UINT : airFunc [Int] TYPE
  | SINT : airFunc [Int] TYPE
  | FLOAT : airFunc [Int] TYPE
  | CONST_INT : airFunc [Int] TYPE
  | CONST_BOOL : airFunc [Bool] TYPE

  -- 2. array
  -- (declare-fun ARRAY (Dcr Type Dcr Type) Type)
  | ARRAY : airFunc [TYPE, TYPE] TYPE

  -- 3. convert to/from POLY
  | ofI : airFunc [Int] Poly   -- I
  | ofB : airFunc [Bool] Poly  -- B
  | toI : airFunc [Poly] Int   -- %I
  | toB : airFunc [Poly] Bool  -- %B


def air_ast : MSLanguage AirSorts := {
  Functions := airFunc
  Relations := fun _ => Empty
}

open airFunc

abbrev addZFunc : air_ast.Functions [Int, Int] Int := Add
abbrev subZFunc : air_ast.Functions [Int, Int] Int := Sub
abbrev mulZFunc : air_ast.Functions [Int, Int] Int := Mul
abbrev divZFunc : air_ast.Functions [Int, Int] Int := EuclideanDiv
abbrev modZFunc : air_ast.Functions [Int, Int] Int := EuclideanMod

abbrev andBFunc (n : Nat) : air_ast.Functions (List.replicate n Bool) Bool := And n

instance {α : AirSorts → Type*} : Add (MSLanguage.air_ast.Term α Int) :=
{ add := addZFunc.apply₂ }

theorem addZ_def (α : AirSorts → Type*) (t₁ t₂ : MSLanguage.air_ast.Term α Int) :
    t₁ + t₂ = addZFunc.apply₂ t₁ t₂ := rfl

instance {α : AirSorts → Type*} : Sub (MSLanguage.air_ast.Term α Int) :=
{ sub := subZFunc.apply₂ }

theorem subZ_def (α : AirSorts → Type*) (t₁ t₂ : MSLanguage.air_ast.Term α Int) :
    t₁ - t₂ = subZFunc.apply₂ t₁ t₂ := rfl

instance {α : AirSorts → Type*} : Mul (MSLanguage.air_ast.Term α Int) :=
{ mul := mulZFunc.apply₂ }

theorem mulZ_def (α : AirSorts → Type*) (t₁ t₂ : MSLanguage.air_ast.Term α Int) :
    t₁ * t₂ = mulZFunc.apply₂ t₁ t₂ := rfl

instance {α : AirSorts → Type*} : Div (MSLanguage.air_ast.Term α Int) :=
{ div := divZFunc.apply₂ }

theorem divZ_def (α : AirSorts → Type*) (t₁ t₂ : MSLanguage.air_ast.Term α Int) :
    t₁ / t₂ = divZFunc.apply₂ t₁ t₂ := rfl

instance {α : AirSorts → Type*} : Mod (MSLanguage.air_ast.Term α Int) :=
{ mod := modZFunc.apply₂ }

theorem modZ_def (α : AirSorts → Type*) (t₁ t₂ : MSLanguage.air_ast.Term α Int) :
    t₁ % t₂ = modZFunc.apply₂ t₁ t₂ := rfl

instance {α : AirSorts → Type*} : AndOp (MSLanguage.air_ast.Term α Bool) :=
{ and := (andBFunc 2).apply₂ }

-- theorem andB_def (α : AirSorts → Type*) (n : Nat) (t₁ t₂ : MSLanguage.air_ast.Term α Bool) :
--     (andBFunc n).apply₂ t₁ t₂ = := rfl

/-- Making this an abbrev instead of a def makes Lean automatically unfold this,
which helps with typeclass inference -/
abbrev AirMod (B I F P T BV : Type u) : AirSorts → Type _
  | AirSorts.Bool => B
  | AirSorts.Int => I
  | AirSorts.Fun => F
  | AirSorts.Named "Poly" => P
  | AirSorts.Named "Type" => T
  | AirSorts.BitVec w => BV
  | _ => sorry

/-!
## Carrier type assignment

We interpret:
- `AirSorts.Bool` as Lean's `Bool`
- `AirSorts.Int`  as Lean's `Int`
- `AirSorts.Fun`  as `Unit` (placeholder)
- `AirSorts.Named _` (including `Poly`, `TYPE`) as `Int`
  (We encode Poly values and TYPE tags uniformly as integers.
   For TYPE, each type-tag like BOOL, INT, NAT, etc. gets a distinct Int code.)
- `AirSorts.BitVec w` as `Fin (2 ^ w.toNat)`
-/
abbrev AirCarrier : AirSorts → Type
  | AirSorts.Bool      => Bool
  | AirSorts.Int       => Int
  | AirSorts.Named _   => Int     -- Poly and TYPE both carried by Int
  | AirSorts.Fun       => Unit
  | AirSorts.BitVec w  => Fin (2 ^ w.toNat)

/-!
## Helper: fold a SortedTuple of Bools

For the n-ary `And`, `Or`, `Xor` we need to fold over a `SortedTuple` whose
signature is `List.replicate n Bool`. We extract elements via `toMap` and fold.
-/

open SortedTuple
-- TODO
--/-- Fold a binary Boolean operation over a SortedTuple of n Bools. -/
-- def foldBools (op : Bool → Bool → Bool) (init : Bool)
--     {n : Nat} (xs : SortedTuple (List.replicate n AirSorts.Bool) AirCarrier) : Bool :=
--   let len := (List.replicate n AirSorts.Bool).length
--   -- Each element has type `AirCarrier ((List.replicate n Bool).get i) = AirCarrier Bool = Bool`
--   -- We fold over `Fin len` using the map.
--   Fin.foldl len (fun acc i =>
--     have h : (List.replicate n AirSorts.Bool).get (Fin.cast (by simp; sorry) i) = AirSorts.Bool := by
--       simp
--     op acc (h ▸ xs.toMap (Fin.cast (by simp) i))
--   ) init


/-!
## The MSStructure instance

We define `funMap` for every constructor of `airFunc`.
For constants (empty input), the SortedTuple argument is `default` (the unique
element of `SortedTuple [] AirCarrier`), so we just return a value.
For functions with inputs, we extract arguments using `eval₁`, `eval₂₁`, `eval₂₂`.
-/

open SortedTuple airFunc in
instance airStructure : air_ast.MSStructure AirCarrier where
  funMap := fun {σ t} f xs =>
    match σ, t, f with
    -- ══════════════════════════════════════
    -- Constants (empty input)
    -- ══════════════════════════════════════
    | [], AirSorts.Bool, airFunc.True   => true
    | [], AirSorts.Bool, airFunc.False  => false

    -- Nat literal: parse the string as an integer, default to 0
    | [], _, airFunc.Nat i =>
        (i.toInt?.getD 0 : Int)

    -- TODO
    -- BitVector literal
    -- | [], AirSorts.BitVec w, airFunc.BitVector bits _ =>
    --     let val := bitsToInt bits
    --     -- Wrap into Fin (2^w)
    --     ⟨val.toNat % (2 ^ w.toNat), Nat.mod_lt _ (Nat.pos_of_ne_zero (by
    --       intro h; simp [Nat.pow_eq_zero] at h))⟩

    -- TODO: this relies on interpreting Poly as Int.
    -- TYPE constants: assign distinct integer codes
    | [], _, airFunc.BOOL  => (0 : Int)
    | [], _, airFunc.INT   => (1 : Int)
    | [], _, airFunc.NAT   => (2 : Int)
    | [], _, airFunc.CHAR  => (3 : Int)
    | [], _, airFunc.USIZE => (4 : Int)
    | [], _, airFunc.ISIZE => (5 : Int)

    -- ══════════════════════════════════════
    -- Unary functions (one input)
    -- ══════════════════════════════════════

    -- Boolean negation
    | [AirSorts.Bool], AirSorts.Bool, airFunc.Not =>
        !xs.eval₁

    -- TODO
    -- BitNot : Poly → Int
    -- We interpret Poly as Int; bitwise NOT on integers
    -- | [_], AirSorts.Int, airFunc.BitNot =>
    --     let v : Int := xs.eval₁
    --     Int.complement v   -- Lean 4's bitwise complement on Int

    -- ofI : Int → Poly (identity embedding, both carried by Int)
    | [AirSorts.Int], _, airFunc.ofI =>
        xs.eval₁

    -- ofB : Bool → Poly (embed Bool into Int: true ↦ 1, false ↦ 0)
    | [AirSorts.Bool], _, airFunc.ofB =>
        if xs.eval₁ then (1 : Int) else (0 : Int)

    -- toI : Poly → Int (identity, both are Int)
    | [_], AirSorts.Int, airFunc.toI =>
        xs.eval₁

    -- toB : Poly → Bool (0 ↦ false, nonzero ↦ true)
    | [_], AirSorts.Bool, airFunc.toB =>
        xs.eval₁ != (0 : Int)

    -- UINT, SINT, FLOAT : Int → TYPE
    -- We encode as: 100 + n, 200 + n, 300 + n
    | [AirSorts.Int], _, airFunc.UINT =>
        (100 + xs.eval₁ : Int)
    | [AirSorts.Int], _, airFunc.SINT =>
        (200 + xs.eval₁ : Int)
    | [AirSorts.Int], _, airFunc.FLOAT =>
        (300 + xs.eval₁ : Int)

    -- CONST_INT : Int → TYPE
    | [AirSorts.Int], _, airFunc.CONST_INT =>
        (400 + xs.eval₁ : Int)

    -- CONST_BOOL : Bool → TYPE
    | [AirSorts.Bool], _, airFunc.CONST_BOOL =>
        if xs.eval₁ then (501 : Int) else (500 : Int)

    -- ══════════════════════════════════════
    -- Binary functions (two inputs)
    -- ══════════════════════════════════════

    -- Bool × Bool → Bool
    | [AirSorts.Bool, AirSorts.Bool], AirSorts.Bool, airFunc.Implies =>
        !xs.eval₂₁ || xs.eval₂₂

    -- Int × Int → Bool  (comparison operators)
    | [AirSorts.Int, AirSorts.Int], AirSorts.Bool, airFunc.Eq =>
        decide (xs.eval₂₁ = xs.eval₂₂)
    | [AirSorts.Int, AirSorts.Int], AirSorts.Bool, airFunc.Le =>
        decide (xs.eval₂₁ ≤ xs.eval₂₂)
    | [AirSorts.Int, AirSorts.Int], AirSorts.Bool, airFunc.Ge =>
        decide (xs.eval₂₁ ≥ xs.eval₂₂)
    | [AirSorts.Int, AirSorts.Int], AirSorts.Bool, airFunc.Lt =>
        decide (xs.eval₂₁ < xs.eval₂₂)
    | [AirSorts.Int, AirSorts.Int], AirSorts.Bool, airFunc.Gt =>
        decide (xs.eval₂₁ > xs.eval₂₂)

    -- Int × Int → Int  (arithmetic)
    | [AirSorts.Int, AirSorts.Int], AirSorts.Int, airFunc.Add =>
        xs.eval₂₁ + xs.eval₂₂
    | [AirSorts.Int, AirSorts.Int], AirSorts.Int, airFunc.Sub =>
        xs.eval₂₁ - xs.eval₂₂
    | [AirSorts.Int, AirSorts.Int], AirSorts.Int, airFunc.Mul =>
        xs.eval₂₁ * xs.eval₂₂
    | [AirSorts.Int, AirSorts.Int], AirSorts.Int, airFunc.EuclideanDiv =>
        xs.eval₂₁ / xs.eval₂₂
    | [AirSorts.Int, AirSorts.Int], AirSorts.Int, airFunc.EuclideanMod =>
        xs.eval₂₁ % xs.eval₂₂

    -- Poly × Poly → Int  (bit shift operations)
    -- Interpret Poly values as Int, perform shift
    | [_, _], AirSorts.Int, airFunc.BitShr =>
        let a : Int := xs.eval₂₁
        let b : Int := xs.eval₂₂
        a / (2 ^ b.toNat)   -- arithmetic right shift
    | [_, _], AirSorts.Int, airFunc.Bitshl =>
        let a : Int := xs.eval₂₁
        let b : Int := xs.eval₂₂
        a * (2 ^ b.toNat)   -- left shift

    -- ARRAY : TYPE × TYPE → TYPE
    -- Encode as a pairing function on the integer codes
    | [_, _], _, airFunc.ARRAY =>
        let a : Int := xs.eval₂₁
        let b : Int := xs.eval₂₂
        (1000 + a * 100 + b : Int)  -- simple injective encoding

    -- TODO
    -- ══════════════════════════════════════
    -- N-ary Boolean operations
    -- ══════════════════════════════════════
    -- | _, AirSorts.Bool, airFunc.And n =>
    --     foldBools (· && ·) true xs
    -- | _, AirSorts.Bool, airFunc.Or n =>
    --     foldBools (· || ·) false xs
    -- | _, AirSorts.Bool, airFunc.Xor n =>
    --     foldBools (· ^^ ·) false xs

    |  _, _, _ => sorry

    -- No relations in air_ast
  RelMap := fun r => Empty.elim r

end MSLanguage

end MSFirstOrder
