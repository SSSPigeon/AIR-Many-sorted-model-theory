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
