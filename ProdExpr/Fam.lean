import Mathlib.Data.FunLike.Basic
import Mathlib.Logic.Embedding.Basic
import Mathlib.Data.Setoid.Basic
import Mathlib.Data.SetLike.Basic

/- Wrapper code for working with families of objects with type `base → Type u'
    Similar to sigma types, but base is fixed -/
universe u v w z u' v' w'

namespace MSFirstOrder

namespace Fam
variable {base : Type u} (α : base → Type v) (β : base → Type w) (γ : base → Type z)

/-- A map between two families over the same base -/
abbrev famMap (α : base → Type v) (β : base → Type w) :=
  (s : base) → (α s → β s)

/-- Notation for famMap -/
notation:25 A  " →ₛ " B  => famMap A B

/- The following is useful notation for pointwise composition of maps which are
parametrized by a Sort type. -/
notation:80 f " ∘ₛ " g => fun t => f t ∘ g t

/-- Notation for dependent disjoint union of types -/
notation:30 f " ⊕ₛ " g => fun s => (f s) ⊕ (g s)

@[simp]
protected def id : famMap α α := fun _ => id

@[simp]
theorem famId {δ : base → Type u} : Fam.id δ = (fun d => @id (δ d)) := rfl

abbrev EmptyFam : base → Type := fun _ => Empty

abbrev PEmptyFam : base → Type u := fun _ => PEmpty

section dependent_sets

variable {base : Type u} {M : base → Type v}

open Set

/-- A dependent family of sets over a fixed base. -/
structure DepSet (M : base → Type v) where
  carrier : ∀ s, Set (M s)

instance : CoeFun (DepSet M) (fun _ => ∀ s, Set (M s)) :=
  ⟨DepSet.carrier⟩

/-- Two dependent sets are equal if they agree on every sort. -/
@[ext]
theorem DepSet.ext {S T : DepSet M} (h : ∀ s x, x ∈ S s ↔ x ∈ T s) : S = T := by
  cases S with
  | mk Scarrier =>
    cases T with
    | mk Tcarrier =>
      have hcarrier : Scarrier = Tcarrier := by
        funext s
        apply Set.ext
        intro x
        exact h s x
      cases hcarrier
      rfl

/-- The underlying family of subtypes of a dependent set. -/
abbrev DepSet.Subtype (S : DepSet M) : base → Type v :=
  fun s => { x : M s // x ∈ S s }

instance : CoeTC (DepSet M) (base → Type _) :=
  ⟨DepSet.Subtype⟩

/-- The pointwise coercion map from a dependent subtype family to the ambient family. -/
abbrev DepSet.subtype (S : DepSet M) : S.Subtype →ₛ M :=
  fun _ x => x.1

/-- The sigma-type of elements of a dependent set. -/
abbrev DepSubtype (S : DepSet M) : Type _ :=
  Σ s, { x : M s // x ∈ S s }

/-- View a dependent set as a set on `Sigma M`. -/
def DepSet.toSigma (S : DepSet M) : Set (Sigma M) :=
  fun x => S x.1 x.2

/-- View a set on `Sigma M` as a dependent set. -/
def DepSet.ofSigma (S : Set (Sigma M)) : DepSet M :=
  ⟨fun s x => S ⟨s, x⟩⟩

-- Allow `x ∈ S` for `x : Sigma M`.
instance : Membership (Sigma M) (DepSet M) :=
  ⟨fun S x => S x.1 x.2⟩

instance : HasSubset (DepSet M) :=
  ⟨fun S T => ∀ s, S s ⊆ T s⟩

@[simp]
theorem DepSet.mem_sigma {S : DepSet M} {s : base} {x : M s} :
    (⟨s, x⟩ : Sigma M) ∈ S ↔ x ∈ S s :=
  Iff.rfl

theorem DepSet.subset_iff {S T : DepSet M} :
    S ⊆ T ↔ ∀ s, S s ⊆ T s := by
  rfl

instance instLE : LE (DepSet M) :=
  ⟨fun S T => ∀ s, S s ⊆ T s⟩

theorem DepSet.le_def {S T : DepSet M} : S ≤ T ↔ ∀ s, S s ⊆ T s :=
  Iff.rfl

instance instPartialOrder : PartialOrder (DepSet M) where
  le := (· ≤ ·)
  le_refl S := by
    intro s x hx
    exact hx
  le_trans S T U hST hTU := by
    intro s x hx
    exact hTU s (hST s hx)
  le_antisymm S T hST hTS := by
    apply DepSet.ext
    intro s x
    exact ⟨fun hx => hST s hx, fun hx => hTS s hx⟩

instance instBot : Bot (DepSet M) :=
  ⟨⟨fun _ => ∅⟩⟩

instance instTop : Top (DepSet M) :=
  ⟨⟨fun _ => univ⟩⟩

instance instInhabited : Inhabited (DepSet M) :=
  ⟨⊥⟩

@[simp]
theorem DepSet.mem_bot {s : base} {x : M s} : x ∈ (⊥ : DepSet M) s ↔ False :=
  Iff.rfl

@[simp]
theorem DepSet.mem_top {s : base} {x : M s} : x ∈ (⊤ : DepSet M) s :=
  mem_univ x

instance instInf : Min (DepSet M) :=
  ⟨fun S T => ⟨fun s => S s ∩ T s⟩⟩

instance instSup : Max (DepSet M) :=
  ⟨fun S T => ⟨fun s => S s ∪ T s⟩⟩

@[simp]
theorem DepSet.inf_apply (S T : DepSet M) (s : base) :
    (S ⊓ T) s = S s ∩ T s :=
  rfl

@[simp]
theorem DepSet.sup_apply (S T : DepSet M) (s : base) :
    (S ⊔ T) s = S s ∪ T s :=
  rfl

@[simp]
theorem DepSet.mem_inf {S T : DepSet M} {s : base} {x : M s} :
    x ∈ (S ⊓ T) s ↔ x ∈ S s ∧ x ∈ T s :=
  Iff.rfl

@[simp]
theorem DepSet.mem_sup {S T : DepSet M} {s : base} {x : M s} :
    x ∈ (S ⊔ T) s ↔ x ∈ S s ∨ x ∈ T s :=
  Iff.rfl

@[simp]
theorem DepSet.toSigma_ofSigma (S : Set (Sigma M)) :
    DepSet.toSigma (DepSet.ofSigma (M := M) S) = S := by
  rfl

@[simp]
theorem DepSet.ofSigma_toSigma (S : DepSet M) :
    DepSet.ofSigma (M := M) (DepSet.toSigma S) = S := by
  apply DepSet.ext
  intro s x
  rfl

end dependent_sets

section dep_setlike

/-!
### `DepSetLike` — a typeclass for types that behave like dependent families of sets

This mirrors Mathlib's `SetLike` but for the many-sorted setting. The canonical coercion
is `F → DepSet M`, analogous to `SetLike.coe : A → Set B`. All derived operations
(`Subtype`, `subtype`, `ext`, coercion to `base → Type _`) route through `DepSet`'s
existing API.
-/

/-- A typeclass for types that behave like dependent families of sets over `M`.
    The canonical data is a coercion to `DepSet M`, which must be injective.
    This mirrors `SetLike` from Mathlib. -/
class DepSetLike (F : Type*) {base : outParam (Type*)} (M : outParam (base → Type*)) where
  /-- The coercion from `F` to `DepSet M`. -/
  protected toDepSet : F → DepSet M
  /-- The coercion is injective. -/
  protected toDepSet_injective : Function.Injective toDepSet

attribute [coe] DepSetLike.toDepSet

namespace DepSetLike

variable {base : Type*} {M : base → Type*} {F : Type*} [DepSetLike F M]

instance instCoeDepSet : CoeTC F (DepSet M) where
  coe := DepSetLike.toDepSet

instance (priority := 100) instCoeSortedTypes : CoeTC F (base → Type _) :=
  ⟨fun S => (DepSetLike.toDepSet S).Subtype⟩

/-- Access the carrier of a `DepSetLike` element at a given sort. -/
def carrier (S : F) : ∀ s, Set (M s) :=
  (DepSetLike.toDepSet S).carrier

@[simp]
theorem carrier_toDepSet (S : F) : (DepSetLike.toDepSet S).carrier = carrier S := rfl

/-- The subtype family, routed through `DepSet.Subtype`. -/
def toSortedTypes (S : F) : base → Type _ :=
  (DepSetLike.toDepSet S).Subtype

@[simp]
theorem toSortedTypes_apply (S : F) (s : base) :
    toSortedTypes S s = { x : M s // x ∈ carrier S s } := rfl

/-- The pointwise `Subtype.val` map, routed through `DepSet.subtype`. -/
def subtypeVal (S : F) : toSortedTypes S →ₛ M :=
  (DepSetLike.toDepSet S).subtype

@[simp]
theorem subtypeVal_apply (S : F) (s : base) (x : toSortedTypes S s) :
    subtypeVal S s x = x.1 := rfl

/-- Two elements of a `DepSetLike` type are equal iff they have the same members everywhere. -/
theorem ext {S T : F} (h : ∀ s x, x ∈ carrier S s ↔ x ∈ carrier T s) : S = T :=
  DepSetLike.toDepSet_injective (DepSet.ext h)

end DepSetLike

end dep_setlike

section many_sorted_setoids

/-
This section introduces dependent families of setoids and their quotients.
It mirrors the structure of standard `Quotient`, `Quotient.lift`, and `Quotient.map`
but applied sort-wise.
-/

variable {Sorts : Type u} {M : Sorts → Type v} {N : Sorts → Type w}

/-- A many-sorted setoid is a family of setoids, one for each sort. -/
structure MSSetoid (M : Sorts → Type v) where
  /-- The family of setoid structures. -/
  toSetoid : ∀ s, Setoid (M s)

attribute [class] MSSetoid

instance [S : MSSetoid M] (s : Sorts) : Setoid (M s) := S.toSetoid s

instance : CoeFun (MSSetoid M) (fun _ => ∀ s, Setoid (M s)) where
  coe := MSSetoid.toSetoid

instance MSSetoid.piSetoid (S : MSSetoid M) : Setoid ((s : Sorts) → M s) := inferInstance

instance MSSetoid.instFam (S : MSSetoid M) {α : Sorts → Type*} :
    MSSetoid (fun s => α s → M s) :=
  MSSetoid.mk fun s : Sorts => (inferInstance : Setoid (α s → M s))

def MSQuotient (S : MSSetoid M) : Sorts → Type _ :=
  fun s => Quotient (S.toSetoid s)

/-- Notation for Many-Sorted Quotient. Input `\sdiv` for the slash. -/
notation:35 M " /ₛ " S => @MSQuotient _ M S

/-- The canonical projection map from the family to its quotient. -/
def MSQuotient.mk (S : MSSetoid M) : M →ₛ (M /ₛ S) :=
  fun s => Quotient.mk (S.toSetoid s)

/--
Lift a map `f : M →ₛ N` to `(M /ₛ S) →ₛ N`.
Requires proof that `f` respects the relation `S` at every sort.
-/
def MSQuotient.lift {S : MSSetoid M} (f : M →ₛ N)
    (respects : ∀ s (x y : M s), @Setoid.r _ (S.toSetoid s) x y → f s x = f s y) :
    (M /ₛ S) →ₛ N :=
  fun s => Quotient.lift (f s) (respects s)

@[simp]
theorem MSQuotient.lift_comp_mk {S : MSSetoid M} (f : M →ₛ N) (h) :
    (MSQuotient.lift f h ∘ₛ MSQuotient.mk S) = f := by
  funext s x
  rfl

/--
Map between quotients: if `f : M →ₛ N` sends related elements in `S` to related elements in `R`,
it descends to a map between quotients.
-/
def MSQuotient.map {S : MSSetoid M} {R : MSSetoid N} (f : M →ₛ N)
    (h : ∀ s (x y : M s), x ≈ y → f s x ≈ f s y) :
    (M /ₛ S) →ₛ (N /ₛ R) :=
  fun s => Quotient.map (f s) (h s)

@[simp]
theorem MSQuotient.map_comp_mk {S : MSSetoid M} {R : MSSetoid N} (f : M →ₛ N) (h) :
    (MSQuotient.map f h ∘ₛ MSQuotient.mk S) = (MSQuotient.mk R) ∘ₛ f := by
  funext s x
  rfl

/-- The kernel of a many-sorted map `f` is the family of setoids defined by `x ≈ y ↔ f x = f y`. -/
def famMap.ker (f : M →ₛ N) : MSSetoid M where
  toSetoid := fun s => Setoid.ker (f s)

/--
Given xs : N →ₛ (M /ₛ S), choose representatives to get N →ₛ M, but return it
modulo the induced pointwise setoid `S.instFam.piSetoid : Setoid (N →ₛ M)`
-/
noncomputable def MSSetoid.choice (S : MSSetoid M) (xs : N →ₛ (M /ₛ S)) :
 Quotient (α := N →ₛ M)
          --S.instFam is an `MSSetoid (fun s => N s → M s)`
          --S.instFam.piSetoid is the corresponding piSetoid `Setoid (N →ₛ M)`
          (S.instFam.piSetoid : Setoid (N →ₛ M)) :=
  Quotient.choice (fun s => Quotient.choice (xs s))

@[simp] theorem MSSetoid.choice_eq
  {Sorts : Type u} {M : Sorts → Type v} {N : Sorts → Type w}
  (S : Fam.MSSetoid M) (f : N →ₛ M) :
  S.choice (MSQuotient.mk S ∘ₛ f)
    = (⟦f⟧ : Quotient S.instFam.piSetoid) := by
    have h :
      (fun s =>
        Quotient.choice (MSQuotient.mk S s ∘ f s))
        =
      (fun s =>
        (⟦f s⟧ : Quotient ((S.instFam (α := N)).toSetoid s))) := by
      funext s
      simp [MSQuotient.mk, Function.comp_def]
      rfl
    simp_all [instFam, choice, Function.comp_def]
    rfl

end many_sorted_setoids

section aux

variable {S : Type*} {α : S → Type*} {β : S → Type*} {σ : List S} {l : List (Sigma α)}

def inl : α →ₛ α ⊕ₛ β := fun _s a => Sum.inl a

def inr : β →ₛ α ⊕ₛ β := fun _s b => Sum.inr b

/-- Dependent analogue of Sum.Elim -/
abbrev sumElim {γ : S → Type*} (f : α →ₛ γ) (g : β →ₛ γ) : (α ⊕ₛ β) →ₛ γ :=
  fun s => Sum.elim (f s) (g s)

@[simp]
theorem sumElim_inl {γ : S → Type*} (f : α →ₛ γ) (g : β →ₛ γ) :
    (fun s => sumElim f g s ∘ Sum.inl) = f := by
  funext s x
  rfl

@[simp]
theorem sumElim_inr {γ : S → Type*} (f : α →ₛ γ) (g : β →ₛ γ) :
    (fun s => sumElim f g s ∘ Sum.inr) = g := by
  funext s x
  rfl

--@[simp]
theorem sumComp_elim {γ : S → Type*} {δ : S → Type*} (f : γ →ₛ δ) (g : α →ₛ γ) (h : β →ₛ γ) :
    (f ∘ₛ (sumElim g h)) = sumElim (f ∘ₛ g) (f ∘ₛ h) := by
  funext s x
  simp_all only [Function.comp_apply]
  cases x <;> rfl

/-- Distributing pointwise evaluation over `sumElim`.
    Useful in ultraproduct proofs where we evaluate at a specific index `a`. -/
@[simp]
theorem sumElim_apply {γ : S → Type*} {I : Type*}
    (f : α →ₛ (fun s => I → γ s)) (g : β →ₛ (fun s => I → γ s)) (a : I) :
    (fun s b => sumElim f g s b a) = sumElim (fun s x => f s x a) (fun s x => g s x a) := by
  funext s x
  cases x <;> rfl

abbrev sumMap {γ : S → Type*} {δ : S → Type*}
    (f : α →ₛ γ) (g : β →ₛ δ) : (α ⊕ₛ β) →ₛ (γ ⊕ₛ δ) :=
  fun s => Sum.map (f s) (g s)

end aux

section manySortedEmbeddings

/-
This section introduces classes for the many-sorted analogues of embeddings and equivalences.
It provides dependent versions of Mathlib.Logic.Equiv and Mathlib.Logic.Embedding to mimic the
development of the one-sorted case.
-/
variable {Sorts : Type*} (M : Sorts → Type w) (N : Sorts → Type w')

/-- A many-sorted embedding is a family of functions that are all injective. -/
--Think about whether this can wrap ergular Embedding via sigma types.
@[ext]
structure MSEmbedding (M : Sorts → Type*) (N : Sorts → Type*) where
  /-- The family of underlying functions. -/
  toFun : M →ₛ N
  /-- The proof that each function in the family is injective. -/
  inj' : ∀ t, Function.Injective (toFun t)

notation:25 A  " ↪ₛ " B  => MSEmbedding A B

instance : CoeFun (M ↪ₛ N) (fun _ => M →ₛ N) where
  coe := MSEmbedding.toFun

instance : DFunLike (M ↪ₛ N) Sorts (fun t => M t → N t) where
  coe := MSEmbedding.toFun
  coe_injective' :=
   by
    rintro ⟨f, hf⟩ ⟨g, hg⟩ h
    have : f = g := by
      funext t x
      exact congrFun (congrArg (fun φ => φ t) h) x
    cases this
    have : hf = hg := Subsingleton.elim _ _
    cases this
    rfl

def MSEmbedding.comp' {A B C : Sorts → Type*} (g : MSEmbedding B C) (f : MSEmbedding A B) :
    MSEmbedding A C :=
  {toFun := g ∘ₛ f,
    inj' := by simp only [g.inj', Function.Injective.of_comp_iff, f.inj', implies_true]
  }

/-- Constructs an embedding from a family of bundled embeddings. -/
def MSEmbedding.fromEmbeddings {M : Sorts → Type w} {N : Sorts → Type w'}
    (f : ∀ t, (M t) ↪ (N t)) : M ↪ₛ N :=
  ⟨ (fun t => (f t : M t → N t)) , (fun t => (f t).inj') ⟩

/-- A many-sorted equivalence is a family of bijections, one for each sort. -/
structure MSEquiv (M : Sorts → Type*) (N : Sorts → Type*) where
  /-- The family of forward functions. -/
  toFun : M →ₛ N
  /-- The family of inverse functions. -/
  invFun : N →ₛ M
  /-- The proof that `invFun` is a left inverse to `toFun` for each sort. -/
  left_inv' : ∀ t, Function.LeftInverse (invFun t) (toFun t)
  /-- The proof that `invFun` is a right inverse to `toFun` for each sort. -/
  right_inv' : ∀ t, Function.RightInverse (invFun t) (toFun t)

notation:25 A  " ≃ₛ " B  => MSEquiv A B

/-- Constructs an MSEquiv from a family of Equivs -/
def MSEquiv.fromEquivs {M : Sorts → Type w} {N : Sorts → Type w'}
    (f : ∀ t, (M t) ≃ (N t)) : M ≃ₛ N :=
 ⟨ (fun t => (f t : M t → N t)),
  (fun t => ((f t).symm : N t → M t)),
  (fun t => (f t).left_inv),
  (fun t => (f t).right_inv) ⟩

/-- Function coercion for MSEquiv -/
instance : CoeFun (M ≃ₛ N) (fun _ => M →ₛ N) where
  coe := MSEquiv.toFun

instance : DFunLike (M ≃ₛ N) Sorts (fun t => M t → N t) where
  coe := MSEquiv.toFun
  coe_injective' :=
   by
    rintro ⟨f, g, L, R⟩ ⟨f', g', L', R'⟩ h
    have : f = f' := by
      funext t x
      exact congrFun (congrArg (fun φ => φ t) h) x
    have : g = g' := by
      funext t y
      have hF_t : f t = f' t := congrArg (fun φ => φ t) this
      have L_t : Function.LeftInverse (g t) (f t) := L t
      have R'_t : Function.RightInverse (g' t) (f' t) := R' t
      calc
        g t y
            = g t (f' t (g' t y)) := by
                rw [← (R'_t y).symm]
        _   = g' t y := by
                simpa [hF_t] using L_t (g' t y)
    cases this; cases this
    have : L = L' := Subsingleton.elim _ _
    have : R = R' := Subsingleton.elim _ _
    cases this; cases this
    rfl

@[ext]
theorem MSEquiv.ext {M N : Sorts → Type*}
    {e₁ e₂ : M ≃ₛ N}
    (h : ∀ t, e₁.toFun t = e₂.toFun t) : e₁ = e₂ := by
  cases e₁ with
  | mk to₁ inv₁ left₁ right₁ =>
    cases e₂ with
    | mk to₂ inv₂ left₂ right₂ =>
      have hF : to₁ = to₂ := by
        funext t; exact h t
      have hI : inv₁ = inv₂ := by
        funext t y
        have hF_t : to₁ t = to₂ t := congrArg (fun φ => φ t) hF
        have L₁ : Function.LeftInverse (inv₁ t) (to₁ t) := left₁ t
        have R₂ : Function.RightInverse (inv₂ t) (to₂ t) := right₂ t
        calc
          inv₁ t y
              = inv₁ t (to₂ t (inv₂ t y)) := by
                  rw [← (R₂ y).symm]
          _   = inv₂ t y := by
                  simpa [hF_t] using L₁ (inv₂ t y)
      cases hF; cases hI
      have : left₁ = left₂ := Subsingleton.elim _ _
      have : right₁ = right₂ := Subsingleton.elim _ _
      cases this; cases this
      rfl

variable {M N}
/-- Inverse of an equivalence `e : α ≃ β`. -/
@[symm]
protected def MSEquiv.symm (e : M ≃ₛ N) : MSEquiv N M :=
  ⟨e.invFun, e.toFun, e.right_inv', e.left_inv'⟩

namespace MSEquiv

def refl {M : Sorts → Type*} : MSEquiv M M where
  toFun     := fun _ => id
  invFun    := fun _ => id
  left_inv' := by intro t x; rfl
  right_inv' := by intro t x; rfl

def toEquiv (e : MSEquiv M N) (s : Sorts) : M s ≃ N s :=
  {
    toFun := e.toFun s
    invFun := e.invFun s
    left_inv := e.left_inv' s
    right_inv := e.right_inv' s
  }

/-- Composition of many-sorted equivalences. -/
def trans {K} (e₁ : MSEquiv M N) (e₂ : MSEquiv N K) : MSEquiv M K :=
  MSEquiv.fromEquivs (fun s => Equiv.trans (e₁.toEquiv s) (e₂.toEquiv s))

lemma trans_is_comp {K} (e₁ : MSEquiv M N) (e₂ : MSEquiv N K) :
  ∀ {s : Sorts}, e₁.trans e₂ s = (e₂ ∘ₛ e₁) s := by
  intro s
  simp_all only
  rfl

/-- Helper simp lemma for applying MSEquiv inverse on left -/
@[simp] lemma inv_to (e : M ≃ₛ N) (t : Sorts) (x : M t) :
    e.invFun t (e.toFun t x) = x :=
  (e.left_inv' t) x

/-- Helper simp lemma for applying MSEquiv inverse on right -/
@[simp] lemma to_inv (e : M ≃ₛ N) (t : Sorts) (y : N t) :
    e.toFun t (e.invFun t y) = y :=
  (e.right_inv' t) y

@[simp] lemma inv_comp (e : M ≃ₛ N) (t : Sorts) :
    e.invFun t ∘ e.toFun t = id := by ext x; exact e.inv_to t x

@[simp] lemma to_comp (e : M ≃ₛ N) (t : Sorts) :
    e.toFun t ∘ e.invFun t = id := by ext y; exact e.to_inv t y

def sumCongr {α₁ : Sorts → Type*} {α₂ : Sorts → Type*}
    {β₁ : Sorts → Type*} {β₂ : Sorts → Type*}
    (ea : α₁ ≃ₛ α₂) (eb : β₁ ≃ₛ β₂) : (α₁ ⊕ₛ β₁) ≃ₛ (α₂ ⊕ₛ β₂) :=
  MSEquiv.fromEquivs (fun s => (ea.toEquiv s).sumCongr (eb.toEquiv s))

end MSEquiv

end manySortedEmbeddings

/-- A class for dependent families of injective functions. -/
class InjectivePerSort
    {Sorts : Type _} {M N : Sorts → Type _} (F : Type*)
    [DFunLike F Sorts (fun t => M t → N t)] where
    (inj' : ∀ (f : F) t, Function.Injective (f t))

instance {Sorts : Type _} {M N : Sorts → Type _} : InjectivePerSort (M ↪ₛ N) where
  inj' := MSEmbedding.inj'

/-- Per-sort analogue of `EquivLike`: an element of `F` is a family of bijections,
one for each sort. -/
class PerSortEquivLike
    {Sorts : Type _} (F : Type*) (M N : Sorts → Type _)
    [DFunLike F Sorts (fun t => M t → N t)] where
  inv : F → (N →ₛ M)
  left_inv : ∀ f t, Function.LeftInverse (inv f t) (f t)
  right_inv : ∀ f t, Function.RightInverse (inv f t) (f t)

instance {Sorts : Type _} {M N : Sorts → Type _} : PerSortEquivLike (M ≃ₛ N) M N where
  inv := MSEquiv.invFun
  left_inv := MSEquiv.left_inv'
  right_inv := MSEquiv.right_inv'

/-- Turn an element of a type `F` satisfying `PerSortEquivLike F α β` into an actual
`Equiv`. This is declared as the default coercion from `F` to `α ≃ β`. -/
@[coe]
def PerSortEquivLike.toEquiv {Sorts : Type _} {F}
    {M N : Sorts → Type _}
    [DFunLike F Sorts (fun t => M t → N t)]
    [PerSortEquivLike F M N] (f : F) : M ≃ₛ N where
  toFun := f
  invFun := PerSortEquivLike.inv f
  left_inv' := PerSortEquivLike.left_inv f
  right_inv' := PerSortEquivLike.right_inv f

namespace PerSortEquivLike

variable {Sorts : Type*} {F : Type*} {M N : Sorts → Type*}
  [DFunLike F Sorts (fun t => M t → N t)] [PerSortEquivLike F M N]

@[simp]
theorem apply_inv_apply (g : F) (s : Sorts) (x : N s) : g s (inv g s x) = x := right_inv _ _ _

@[simp]
theorem inv_apply_apply (g : F) (s : Sorts) (x : M s) : (inv g) s (g s x) = x := left_inv _ _ _

theorem apply_inv_apply_fun (g : F) :
    (fun s => g s ∘ (inv g s)) = fun _ => id := by
  funext
  simp only [Function.comp_apply, apply_inv_apply, id_eq]

theorem inv_apply_apply_fun (g : F) :
    (fun s => inv g s ∘ (g s)) = fun _ => id := by
  funext
  simp only [Function.comp_apply, inv_apply_apply, id_eq]

end PerSortEquivLike
end Fam
end MSFirstOrder
