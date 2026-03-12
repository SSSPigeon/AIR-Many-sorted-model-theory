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
  | Nat : (i : String) → airFunc [] Int
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
abbrev AirCarrier (P T F : Type) : AirSorts → Type
  | AirSorts.Bool      => Bool
  | AirSorts.Int       => Int
  | AirSorts.Named "Poly"   => P
  | AirSorts.Named "TYPE"   => T
  | AirSorts.Fun       => F
  | AirSorts.BitVec w  => Fin (2 ^ w.toNat)
  | _ => sorry

/-!
## Helper: fold a SortedTuple of Bools

For the n-ary `And`, `Or`, `Xor` we need to fold over a `SortedTuple` whose
signature is `List.replicate n Bool`. We extract elements via `toMap` and fold.
-/

open SortedTuple airFunc

variable {P T F : Type}

variable [S : air_ast.MSStructure (AirCarrier P T F)]
-- TODO
/-- Fold a binary Boolean operation over a SortedTuple of n Bools. -/
def foldBools (op : Bool → Bool → Bool) (init : Bool)
    {n : Nat} (xs : SortedTuple (List.replicate n AirSorts.Bool) (AirCarrier P T F)) : Bool :=
  List.foldl op init <| List.ofFn fun (i : Fin n) =>
    let i' : Fin (List.replicate n AirSorts.Bool).length := ⟨i.val, by simp⟩
    have h : (List.replicate n AirSorts.Bool).get i' = AirSorts.Bool := by simp
    cast (congrArg (AirCarrier P T F) h) (xs.toMap i')

class CompatibleAir (P T F : Type) extends air_ast.MSStructure (AirCarrier P T F) where
  -- Pin down the Bool/Int operations:
  funMap_true  : ∀ xs, funMap airFunc.True xs = true
  funMap_false : ∀ xs, funMap airFunc.False xs = false
  funMap_nat   : ∀ (i : String) xs, funMap (airFunc.Nat i) xs = i.toInt?.getD 0
  --TODO: funMap_bitvec

  funMap_implies : ∀ xs, funMap airFunc.Implies xs = (!xs.eval₂₁ || xs.eval₂₂)
  funMap_not   : ∀ xs, funMap airFunc.Not xs = !xs.eval₁

  funMap_eq    : ∀ xs, funMap airFunc.Eq xs = decide (xs.eval₂₁ = xs.eval₂₂)
  funMap_le    : ∀ xs, funMap airFunc.Le xs = decide (xs.eval₂₁ ≤ xs.eval₂₂)
  funMap_ge    : ∀ xs, funMap airFunc.Ge xs = decide (xs.eval₂₁ ≥ xs.eval₂₂)
  funMap_lt    : ∀ xs, funMap airFunc.Lt xs = decide (xs.eval₂₁ < xs.eval₂₂)
  funMap_gt    : ∀ xs, funMap airFunc.Gt xs = decide (xs.eval₂₁ > xs.eval₂₂)
  funMap_euclideanDiv : ∀ xs, funMap airFunc.EuclideanDiv xs = xs.eval₂₁ / xs.eval₂₂
  funMap_euclideanMod : ∀ xs, funMap airFunc.EuclideanMod xs = xs.eval₂₁ % xs.eval₂₂


  funMap_add   : ∀ xs, funMap airFunc.Add xs = xs.eval₂₁ + xs.eval₂₂
  funMap_sub   : ∀ xs, funMap airFunc.Sub xs = xs.eval₂₁ - xs.eval₂₂
  funMap_mul   : ∀ xs, funMap airFunc.Mul xs = xs.eval₂₁ * xs.eval₂₂

  funMap_and   : ∀ (n : Nat) xs, funMap (airFunc.And n) xs = foldBools (· && ·) true xs
  funMap_or    : ∀ (n : Nat) xs, funMap (airFunc.Or n) xs = foldBools (· || ·) false xs
  funMap_xor   : ∀ (n : Nat) xs, funMap (airFunc.Xor n) xs = foldBools (· ^^ ·) false xs

  -- Leave Poly/TYPE/Fun operations abstract — axioms constrain them

-- /--
-- ``Soundness``
-- Choice 1: for any sort s, and e1 e2: s, prove that ∀ v, Term.realize v e1 = Term.realize v e2.
-- theorem my_thm
--     {P T F : Type}
--     [CompatibleAir P T F]
--     (hAxioms : AirCarrier P T F ⊨ myAxioms)
--     : ∀ v, Term.realize v e1 = Term.realize v e2 := by
--   sorry

-- Choice 2: Prove that myAxioms ⊢ e1 = e2.
-- -/
variable (myAxioms : air_ast.Theory)


end MSLanguage

end MSFirstOrder
