import ProdExpr.Signature
import ProdExpr.Fam

/-!
## Main Definitions

- Given a type `S`, a map `α : S → Type*` and a list `σ : Signature S`,
  a `α [^] σ` is a `List (Sigma α)` with first projection equal to `σ`
- `Sortedtuple.ofList'` converts a `List (Sigma α)` to a Interpret, notation `!ₛ[ ... ]`
- `Interpret.toMap` converts a `α [^] σ ` to a dependent map
  `(i : Fin σ.length) → α (σ.get i)`
- `Interpret.toFMap` converts a `α [^] σ ` to a map fibered over `S`: an object of type
  `(s : S) → { (i : Fin σ.length) // σ.get i = s } →  α s`
- `Interpret.append` appends two Interprets, similar to appending lists
- `Interpret.map` maps a dependent function over a Interpret,
  similar to List.map. Notation `<$>ₛ`


## Main theorems

- Equivalence between sorted tuples and dependent maps
  in `Interpret.toMap_fromMap` and `Interpret.fromMap_toMap`
- Equivalence between sorted tuples and maps fibered over a base `S`
  in `Interpret.toFMap_fromFMap` and `Interpret.fromFmap_toFmap`
- various helper theorems on appending,
  casting over equality of the parametrizing list `σ`, and mapping over Interprets
-/

universe u v w z

variable {S : Type u}
namespace MSFirstOrder

namespace Signature
namespace Interpret

open Signature

variable {α : S → Type v} {β : S → Type w}

/-! ## Basic Instances and Properties -/

instance nilUnique : Unique (Interpret β ⦃⦄) :=
  inferInstanceAs (Unique PUnit)

@[simp]
lemma reduce_nil (a : Interpret α ⦃⦄) : a = default := rfl

abbrev mk_default (α : S → Type v) : Interpret α ⦃⦄ := default

instance IdxNilEmpty {s : S} : IsEmpty (Idx ⦃⦄ s) := by
  constructor
  intro a
  cases a

instance IdxofInhabited {s : S} : Inhabited (Idx ⦃s⦄ s) := by
  constructor
  case default =>
    exact Idx.var

instance IdxofUnique {s : S} : Unique (Idx ⦃s⦄ s) := by
  constructor
  · intro a
    cases a
    case var => rfl


/-! ## Core Operations -/

/-! ### Element Access -/

/-- Takes an `Idx σ` as an index for a Sorted Tuple xs and returns
    the value at that position.
-/
def get {σ : Signature S} (xs : α [^] σ) : (σ.Idx) →ₛ α :=
  match σ with
  | .nil => fun s => fun v => isEmptyElim v
  | .of t => fun s => fun v => by
    cases v
    exact xs
  | .prod σ τ => fun s => fun v =>
    match v with
    | Idx.left w => get xs.1 s w
    | Idx.right w => get xs.2 s w

open Idx

@[simp]
theorem get_of (s : S) (xs : ⦃s⦄.Interpret α) : xs.get _ var = xs := rfl

@[simp]
theorem get_left {s : S} {σ τ : Signature S} {v : σ.Idx s} (xs : (σ.prod τ).Interpret α)
  : get xs _ (left v) = get xs.1 _ v  := rfl

@[simp]
theorem get_right {s : S} {σ τ : Signature S} {v : σ.Idx s} (xs : (τ.prod σ).Interpret α)
  : get xs _ (right v) = get xs.2 _ v  := rfl

def fromGet {σ : Signature S} (v : (Idx σ) →ₛ α) : α [^] σ :=
  match σ with
  | .nil =>  (default : PUnit)
  | .of t => v t var
  | .prod _ _  =>  ⟨fromGet (fun s => fun w => v s (left w)),
                  fromGet (fun s => fun w => v s (right w))⟩

@[simp]
theorem get_fromGet {σ : Signature S} (xs : α [^] σ) : fromGet (get xs) = xs := by
  induction σ
  case nil => simp
  case of t => rfl
  case prod σ τ => simp_all only [fromGet, get, Prod.mk.eta]

@[simp]
theorem fromGet_get {σ : Signature S} (v : (Idx σ) →ₛ α) : get (fromGet v) = v := by
  ext s x
  induction σ
  case nil => exact isEmptyElim x
  case of t =>
    have h : α t = α [^] ⦃t⦄ := by rfl
    change get (h ▸ (v t var)) s x = v s x
    cases x
    case var =>
    simp_all only
    rfl
  case prod σ τ =>
    rw[fromGet, get]
    simp_all only
    split
    next v_1 w => simp_all only
    next v_1 w => simp_all only

/-- Decomposition lemma for `fromGet` on product signatures.
    Useful for simplifying contexts in ultraproduct proofs.
    Not marked @[simp] to avoid interfering with `comap` proofs. -/
theorem fromGet_prod {σ τ : Signature S} (v : (Idx (σ ⨯ τ)) →ₛ α) :
    fromGet v = ⟨fromGet (fun s w => v s (Idx.left w)),
                 fromGet (fun s w => v s (Idx.right w))⟩ := rfl

/-! ## Conversion Functions -/

/-! ### List Conversion -/

/-- Forget the tree shape and just view it as a list of elements with their sorts. -/
def toList {σ : Signature S} (t : α [^] σ) : List (Sigma α) :=
  match σ with
  | ⦃⦄  => []
  | of s          => [⟨s, t⟩]
  | prod _ _      => toList t.fst ++ toList t.snd

/-! ### Finset Conversion -/

/--
Turn a Sorted Tuple into a Finset of ⟨s, a : α s⟩ pairs
-/
def toFinset {σ : Signature S} (t : α [^] σ)
    [DecidableEq S] [∀ t, DecidableEq (α t)] : Finset (Sigma α) :=
  match σ with
  | nil            => ∅
  | of s         => {⟨s, t⟩}
  | prod _ _      => toFinset t.fst ∪ toFinset t.snd

@[simp] lemma toList_nil :
   toList (mk_default α) = [] := rfl

@[simp] lemma toList_of (s : S) (a : α s) :
    toList (σ := ⦃s⦄) a = [⟨s, a⟩] := rfl

@[simp] lemma toList_prod {σ τ : Signature S} (xs : α [^] σ) (ys : τ.Interpret α) :
    toList (σ := σ.prod τ) ⟨xs,  ys⟩ = toList xs ++ toList ys := rfl

@[simp] lemma toList_prod' {σ τ : Signature S} (xs : (σ.prod τ).Interpret α) :
    toList (σ := σ.prod τ) xs = toList xs.1 ++ toList xs.2 := rfl

/-! ### Length Properties -/

lemma toList_length {σ : Signature S} {xs ys : α [^] σ} :
  (toList xs).length = (toList ys).length := by
  induction σ
  case of => simp
  case nil => simp
  case prod σ τ ih₁ ih₂ => simp[ih₁ (xs := xs.1) (ys := ys.1), ih₂ (xs := xs.2) (ys := ys.2)]

variable {α : S → Type v} {β : S → Type w} {γ : S → Type z}
variable {σ ξ η : Signature S} {s : S} {x : α s}
variable {l : List (Sigma α)} {xs : α [^] σ}

open List

@[simp]
theorem length_eq (xs : α [^] σ) : (toList xs).length = σ.length := by
  induction σ
  case nil => rfl
  case of =>
    simp[Signature.length]
  case prod =>
    simp_all[Signature.length]

theorem length_eq_List (xs : α [^] σ) : (toList xs).length = σ.toList.length := by
  induction σ
  case nil =>
    simp[Signature.toList]
  case of =>
    simp[Signature.toList]
  case prod _ _ ih₁ ih₂ =>
    simp_all[Signature.toList, ih₁ (xs := xs.1), ih₂ (xs := xs.2)]

/-! ## Mapping Operations -/

section maps

/-- Map a dependent function over a Interpret, similar to List.map. -/
def map (f : α →ₛ β) {σ : Signature S} (xs : α [^] σ) : β [^] σ :=
  match f , σ , xs with
  | _ , .nil  , _      =>  default
  | f , .of s , xs      =>  f s xs
  | f , .prod _ _ , xs => ⟨map f xs.1 , map f xs.2⟩

/--A sorted tuple is comparable to a "dependent functor",
  so we borrow this notation for "Functor.map". -/
infixr:100 " <$>ₛ " => Interpret.map

@[simp]
theorem map_id (xs : α [^] σ) : (fun _ => id) <$>ₛ xs = xs := by
  induction σ
  case nil => simp[map]
  case of => simp [map, id_eq]
  case prod τ η ih₁ ih₂ => simp only [map, ih₁, ih₂, Prod.mk.eta]

@[simp]
theorem map_id' (xs : α [^] σ) : (fun _ t => t) <$>ₛ xs = xs := by
  have : (fun _ t => t : α →ₛ α) = fun _ => id := rfl
  simp [this]

theorem comp_map (φ : α →ₛ β) (ψ : β →ₛ γ)
    (xs : α [^] σ) : ((ψ ∘ₛ φ) <$>ₛ  xs) = ψ <$>ₛ (φ <$>ₛ  xs) := by
  induction σ
  case nil => simp only [map]
  case of => simp [map]
  case prod τ η ih₁ ih₂ => simp only [map, ih₁, ih₂]

@[simp]
theorem get_map (xs : α [^] σ) (f : α →ₛ β) : Interpret.get (f <$>ₛ xs) =
    fun s => f s ∘ (get xs s) := by
  induction σ with
  | nil => funext s x; exact isEmptyElim x
  | of s =>
    funext s₁ a
    cases a
    rw [Function.comp_apply, get_of]
    rfl
  | prod σ₁ σ₂ ih₁ ih₂ =>
    funext s a
    obtain ⟨x₁, x₂⟩ := xs
    rw [map]
    cases a with
    | left v => simp only [ih₁, Function.comp_apply, get]
    | right w => simp only [ih₂, Function.comp_apply, get]

@[simp]
theorem map_prod {σ₁ σ₂ : Signature S} {f : α →ₛ β} (x₁ : σ₁.Interpret α) (x₂ : σ₂.Interpret α) :
    (f <$>ₛ (x₁, x₂) : (σ₁.prod σ₂).Interpret β)
    = ((f <$>ₛ x₁, f <$>ₛ x₂) : (σ₁.prod σ₂).Interpret β) := rfl

end maps

/-! ## Type Class Instances -/

section instances

@[simp]
theorem default_toList {S : Type u} {α : S → Type*} :
  toList (default : nil.Interpret α ) = [] := rfl

@[simp]
theorem map_default {S : Type u} {α β : S → Type*} {f : α →ₛ β} :
  f <$>ₛ (default : nil.Interpret α) = default := rfl

/-- Decidability instance for Interpret equality.
    Uses structural recursion on the Signature shape. -/
def decidableEq
    [∀ s, DecidableEq (α s)] :
    ∀ {σ : Signature S}, DecidableEq (α [^] σ)
| .nil =>
    by intro a b; cases a; cases b; exact isTrue rfl
| .of s =>
    by
    aesop
| .prod σ τ =>
    by
    simp only [Interpret]
    intro a b
    rcases a with ⟨a1, a2⟩
    rcases b with ⟨b1 , b2⟩
    have h1 : Decidable (a1 = b1) :=
      Interpret.decidableEq (σ := σ) a1 b1
    have h2 : Decidable (a2 = b2) :=
      Interpret.decidableEq (σ := τ) a2 b2
    have h3:= (inferInstance : Decidable (a1 = b1 ∧ a2 = b2))
    aesop

instance instDecidableEq
    [∀ s, DecidableEq (α s)] :
    DecidableEq (α [^] σ) :=
  Interpret.decidableEq (σ := σ)


open Signature

/-- "Flat" argument tuples: one entry per position in the arity `σ`. -/
def SortedMap (α : S → Type v) (σ : Signature S) :=
  (i : Fin σ.length) → α (σ.getIdx i).1

/-- Coercion instance from Interpret to a dependent object over Sorts -/
instance instCoeFam : Coe (σ.Interpret α) (σ.Idx →ₛ α) where
  coe := get

@[ext]
lemma ext {xs ys : σ.Interpret α} (h : ∀ (s : S) (v : σ.Idx s),
        xs.get s v = ys.get s v) : xs = ys := by
  induction σ
  case nil => simp_all only [reduce_nil, PUnit.default_eq_unit, implies_true]
  case of s  =>
    have conc := h s (Idx.var)
    simp only [get, id_eq] at conc
    exact conc
  case prod σ τ ihσ ihτ =>
    rcases xs with ⟨xsσ, xsτ⟩
    rcases ys with ⟨ysσ, ysτ⟩
    rw[Prod.mk.injEq]
    constructor
    case left =>
      apply ihσ
      intro s v
      have h' := h s (v.left)
      simp only [get] at h'
      exact h'
    case right =>
      apply ihτ
      intro s v
      have h' := h s (v.right)
      simp only [get] at h'
      exact h'

end instances

section quotients

open Fam
/--
If the underlying family `α` carries a many-sorted setoid, then each interpretation
`α [^] σ` inherits a setoid by transporting the pointwise setoid on maps
`σ.Idx →ₛ α` along `SortedTuple.get`.
-/
instance instSetoidInterpret [MSSetoid α] : Setoid (α [^] σ) :=
  Setoid.comap Interpret.get
    (inferInstance : Setoid (σ.Idx →ₛ α))

instance instMSSetoidInterpret [Fam.MSSetoid α] : MSSetoid (fun s => σ.Idx s → α s) := {
    toSetoid := fun _ => inferInstance
}

variable (R : MSSetoid α)

@[simp]
lemma interpret_equiv_iff (xs ys : α [^] σ) :
    xs ≈ ys ↔ ∀ (s : S) (v : σ.Idx s), xs.get s v ≈ ys.get s v :=
  Iff.rfl

@[simp]
lemma interpret_equiv_iff' (xs ys : σ.Idx →ₛ α) :
  xs ≈ ys ↔ fromGet xs ≈ fromGet ys := by
  simp_all only [interpret_equiv_iff, fromGet_get]
  rfl

local instance : Fam.MSSetoid α := R

/-- Map an interpretation into the componentwise-quotiented interpretation
  (componentwise `Quotient.mk`). -/
def toQuot {σ : Signature S} (xs : α [^] σ) : (MSQuotient R) [^] σ:=
  (Fam.MSQuotient.mk (M := α) R) <$>ₛ xs

@[simp]
lemma get_toQuot {σ : Signature S} (xs : α [^] σ) (s : S) (v : σ.Idx s) :
    (toQuot (σ := σ) (α := α) R xs).get s v
      = Quotient.mk (s := (R.toSetoid s)) (xs.get s v) := by
  simp only [toQuot, get_map, MSQuotient.mk, Function.comp_apply]

/--
Multisorted analogue of Mathlib's `Quotient.finChoice`:
turn a *tuple of quotients* into a *single quotient of representative tuples*.

Noncomputable: chooses representatives via `Quotient.out`.
-/
noncomputable def choice {σ : Signature S} (xs : (α /ₛ R) [^] σ) :
    Quotient (α := α [^] σ) instSetoidInterpret :=
  ⟦fromGet (fun s v => (xs.get s v).out)⟧

/-- `choice` inverts `toQuot` up to quotient equivalence. -/
theorem choice_toQuot {σ : Signature S} (xs : α [^] σ) :
    choice R (toQuot R xs) = ⟦xs⟧ := by
  apply Quotient.sound
  simp only [interpret_equiv_iff, fromGet_get, get_toQuot]
  intro s v
  exact Quotient.exact (Quotient.out_eq _)

/-- The representative from `choice` maps back to the original tuple of quotients. -/
@[simp]
theorem toQuot_out_choice {σ : Signature S} (xs : (α /ₛ R) [^] σ) :
    toQuot R (choice R xs).out = xs := by
  ext s v
  have hrepr : (choice R xs).out ≈
      fromGet (σ := σ) (α := α) (fun s v => (xs.get s v).out) := by
    exact
      Quotient.exact (by simp [choice])
  have hcomp : (choice R xs).out.get s v ≈ (xs.get s v).out := by
    have hpoint :=
      (interpret_equiv_iff R
          (choice R xs).out
          (fromGet (fun s v => (xs.get s v).out))).1
        hrepr
    simp_all only [interpret_equiv_iff, fromGet_get, implies_true]
  calc
    (toQuot R (choice R xs).out).get s v
        = Quotient.mk (s := (R.toSetoid s)) ((choice R xs).out.get s v) := by
          simp
    _ = Quotient.mk (s := (R.toSetoid s)) ((xs.get s v).out) :=
          Quotient.sound hcomp
    _ = xs.get s v := by
          simp

end quotients

end Interpret

/-! ## Advanced Equivalences -/

section interpret_equivalences
/-!
This section elaborates on how Interpret.get interacts with maps of Idxs,
which will be needed in semantics.
-/

open Interpret

/-- The map of interpretations induced by a SigMap on signatures. -/
def Interpret.comap
    {X : S → Type v} {σ τ : Signature S} (f : SigMap σ τ) :
    Interpret X τ → Interpret X σ :=
  fun xs =>
    Interpret.fromGet
      (fun s w => Interpret.get xs s (f s w))

@[simp]
lemma get_comap
     {X : S → Type _} {σ τ : Signature S}
    (xs : Interpret X τ) (f : SigMap σ τ) :
  Interpret.get (xs.comap f) = fun s w => Interpret.get xs s (f s w) := by
  ext s w
  simp [Interpret.comap]

@[simp] lemma get_comap_incl_left
     {X : S → Type _} {σ τ : Signature S} (xs : Interpret X (σ ⨯ τ)) :
  Interpret.get (xs.comap (SigMap.incl_left : SigMap σ (σ ⨯ τ)))
    = fun s w => Interpret.get xs s (Idx.left w) := by
  simp [get_comap]

@[simp] lemma get_comap_incl_right
     {X : S → Type _} {σ τ : Signature S} (xs : Interpret X (τ ⨯ σ)) :
  Interpret.get (xs.comap (SigMap.incl_right : SigMap σ (τ ⨯ σ)))
    = fun s w => Interpret.get xs s (Idx.right w) := by
  simp [get_comap]

/-- The equivalence on interpretations induced by a `SigEquiv` on signatures. -/
def Interpret.EquivfromSigEquiv
    {X : S → Type v} {σ τ : Signature S} (e : SigEquiv σ τ) :
    Interpret X σ ≃ Interpret X τ :=
{ toFun    := fun xs => xs.comap e.invFun
  , invFun := fun ys => ys.comap e.toFun
  , left_inv := by
      intro xs
      simp [Interpret.comap]
  , right_inv := by
      intro ys
      simp [Interpret.comap] }

/-- Needed to simp away the messiness needed for quantification over "of s" -/
@[simp]
theorem nilLeft_symm_apply (s : S) :
    (Fam.MSEquiv.symm (Signature.SigEquiv.nilLeft ⦃s⦄)).toFun s .var = .right .var := by
  rfl

/-- Needed to simplify the "get" statement after using nilLeft_symm_apply -/
@[simp]
theorem get_right_var {X : S → Type v} {s : S} {u : PUnit} {x : X s} :
    Interpret.get ((u, x) : (nil.prod ⦃s⦄).Interpret X) s (.right .var) = x := by
  simp [Interpret.get]

end interpret_equivalences
end Signature

/-! ## DepSet tuple coercions -/

namespace Fam

open Signature
open Signature.Interpret

section dep_set_tuples

variable {Sorts : Type u} {M : Sorts → Type v}

instance (S : DepSet M) {σ : Signature Sorts} : CoeTC (S.Subtype [^] σ) (M [^] σ) :=
  ⟨fun xs => (S.subtype) <$>ₛ xs⟩

end dep_set_tuples

end Fam

end MSFirstOrder
