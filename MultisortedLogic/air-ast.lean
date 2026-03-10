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
  -- TODO
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


end MSLanguage

end MSFirstOrder
