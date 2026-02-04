import ProdExpr.LanguageMap
import ProdExpr.SortedTuple

/-
Based on the corresponding Mathlib file Mathlib\ModelTheory\Syntax.lean
which was authored by 2021 Aaron Anderson, Jesse Michael Han, Floris van Doorn,
and is released under the Apache 2.0 license.

For the Flypitch project:
- [J. Han, F. van Doorn, A formal proof of the independence of the continuum hypothesis]
  [flypitch_cpp]
- [J. Han, F. van Doorn, A formalization of forcing and the unprovability of
  the continuum hypothesis][flypitch_itp]
-/

universe u v w z u' v' w'

namespace MSFirstOrder

namespace MSLanguage

variable {Sorts : Type z} {L : MSLanguage.{u, v, z} Sorts} {L' : MSLanguage Sorts}
variable {M : Sorts → Type w} {α : Sorts → Type u'} {γ : Sorts → Type*}

open MSFirstOrder MSStructure Fin Fam Signature
open Interpret

/-- A term on `α` is either a variable indexed by an element of `α`,
    a function symbol applied to simpler terms, or a product of terms.
-/
inductive Term (L : MSLanguage.{u, v, z} Sorts) (α : Sorts → Type u') :
    Signature Sorts → Type max z u' u where
| var (s : Sorts) : α s → L.Term α (of s)
| func {σ : Signature Sorts} {t : Sorts} (f : L.Functions σ t) (r : L.Term α σ) : L.Term α (.of t)
| prod {σ τ : Signature Sorts} : L.Term α σ → L.Term α τ → L.Term α (σ ⨯ τ)
| nil : L.Term α .nil

/-- A term of a single sort `s`. Shorthand for `L.Term α (of s)`. -/
abbrev Term₁ (L : MSLanguage.{u, v, z} Sorts) (α : Sorts → Type u') (s : Sorts) :=
  L.Term α ⦃s⦄

/--
Needed in some cases to show termination for recursion on terms
-/
def Term.size : {σ : Signature Sorts} → L.Term α σ → Nat
    | _, .nil            => 2
    | _, .var _ _        => 1
    | _, .func _ ts      => 2 + ts.size
    | _, .prod t₁ t₂     => 1 + Term.size t₁ + Term.size t₂

namespace Term

/-- Recursive helper for establishing `DecidableEq` on terms: -/
def decEqTerm
  [DecidableEq Sorts]
  [∀ s, DecidableEq (α s)]
  [∀ σ t, DecidableEq (L.Functions σ t)] :
  {σ : Signature Sorts} → (t₁ t₂ : L.Term α σ) → Decidable (t₁ = t₂)
| .nil, .nil, .nil =>
    isTrue rfl
| .of s, .var _ x₁, .var _ x₂ =>
    match decEq x₁ x₂ with
    | isTrue h  => isTrue (by cases h; rfl)
    | isFalse h => isFalse (by intro hEq; cases hEq; exact h rfl)
| .of s, .var _ _, .func _ _ =>
    isFalse (by intro hEq; cases hEq)
| .of s, .func _ _, .var _ _ =>
    isFalse (by intro hEq; cases hEq)
| .of s,
    .func (σ := σ₁) (t := _) f₁ r₁,
    .func (σ := σ₂) (t := _) f₂ r₂ =>
    match decEq σ₁ σ₂ with
    | isFalse hσ =>
        isFalse (by intro hEq; cases hEq; exact hσ rfl)
    | isTrue hσ =>
        by
          cases hσ
          match decEq f₁ f₂ with
          | isFalse hf =>
              exact isFalse (by intro hEq; cases hEq; exact hf rfl)
          | isTrue hf =>
              cases hf
              match decEqTerm (σ := σ₁) r₁ r₂ with
              | isTrue hr  => exact isTrue (by cases hr; rfl)
              | isFalse hr => exact isFalse (by intro hEq; cases hEq; exact hr rfl)
| .prod σ τ, .prod t₁₁ t₁₂, .prod t₂₁ t₂₂ =>
    match decEqTerm (σ := σ) t₁₁ t₂₁ with
    | isFalse h1 =>
        isFalse (by intro hEq; cases hEq; exact h1 rfl)
    | isTrue h1 =>
        match decEqTerm (σ := τ) t₁₂ t₂₂ with
        | isFalse h2 =>
            isFalse (by intro hEq; cases hEq; exact h2 rfl)
        | isTrue h2 =>
            isTrue (by cases h1; cases h2; rfl)

instance instDecidableEq
  [DecidableEq Sorts]
  [∀ s, DecidableEq (α s)]
  [∀ σ t, DecidableEq (L.Functions σ t)] :
  ∀ σ, DecidableEq (L.Term α σ) :=
by
  intro σ t₁ t₂
  exact decEqTerm t₁ t₂

section term_monad
/-We can think of Terms as dependent monad-like structures over their variables, with
  `Term.var` functioning as `pure` and `Term.bind` defined in this section.-/

/-- Binds a term assignment to variables in a term -/
@[simp]
def bind {β : Sorts → Type _} {σ} : L.Term α σ → (α →ₛ L.Term₁ β) → L.Term β σ
  | nil , _     => nil
  | var t a, tf => tf t a
  | func f ts, tf => func f (ts.bind tf)
  | prod t₁ t₂, tf => prod (t₁.bind tf) (t₂.bind tf)


/-- Relabels a term's variables along a particular function -/
@[simp]
def mapVars {β : Sorts → Type _} {σ : Signature Sorts} (g : α →ₛ β) : L.Term α σ → L.Term β σ :=
  fun t => t.bind (fun s a => .var s (g s a))

variable {β : Sorts → Type*} {t : Sorts} {σ : Signature Sorts}

def varOf (g : α →ₛ β) : ∀ s, α s → L.Term₁ β s :=
  fun s a => Term.var s (g s a)

/-- Associativity of bind -/
@[simp]
theorem bind_bind (t : Term L α σ)
    (f : α →ₛ L.Term₁ β)
    (g : β →ₛ L.Term₁ γ) :
    (t.bind f).bind g = t.bind (fun s a => (f s a).bind g) := by
  induction t <;> simp only [bind, *]

theorem bind_id {f : α →ₛ L.Term₁ α}
  (t : Term L α σ) (h : ∀ s a, f s a = var s a) : t.bind f = t := by
  induction t  <;> simp_all only [bind]

/-- Applying bind on the variable map is the identity (right monad law) -/
@[simp]
theorem bind_var (t : Term L α σ) :
    t.bind (fun s a => var s a) = t := by
  induction t <;> simp only [bind, *]

/-- Applying bind to a variable (left monad identity) -/
@[simp]
theorem var_bind (s : Sorts) (a : α s) (f : α →ₛ L.Term₁ β) :
    (var s a).bind f = f s a := rfl

theorem mapVars_id {f : L.Term α σ} : mapVars (Fam.id α) f = f := by
  simp only [mapVars, Fam.id, id_eq, bind_var]

@[simp]
theorem mapVars_id_eq_id : (mapVars (fun s => @id (α s)) : L.Term α σ → L.Term α σ) = id := by
  ext a; simp only [mapVars, id_eq, bind_var]

@[simp]
theorem mapVars_mapVars (f : α →ₛ β) (g : β →ₛ γ) (t : L.Term α σ) :
    mapVars g (mapVars f t) = mapVars (g ∘ₛ f) t := by
  induction t with
  | var => rfl
  | func _ _ ih => simp_all only [mapVars, Function.comp_apply, bind]
  | prod t₁ t₂ ih₁ ih₂ => simp_all only [mapVars, Function.comp_apply, bind]
  | nil => rfl

@[simp]
theorem mapVars_comp_mapVars (f : α →ₛ β) (g : β →ₛ γ) :
    (mapVars g ∘ mapVars f : L.Term α σ → L.Term γ σ) = mapVars (g ∘ₛ f) :=
  funext (mapVars_mapVars f g)

/-- Relabels a term's variables along a bijection. -/
@[simps]
def mapVarsEquiv (g : α ≃ₛ β) : L.Term α σ ≃ L.Term β σ :=
  ⟨mapVars (fun s => g s),
   mapVars (fun s => (g.toEquiv s).symm),
  fun _ => by simp only [mapVars, MSEquiv.toEquiv, Equiv.coe_fn_symm_mk, bind_bind, bind,
    MSEquiv.inv_to, bind_var]
    , fun _ => by  simp only [mapVars, MSEquiv.toEquiv, Equiv.coe_fn_symm_mk, bind_bind, bind,
      MSEquiv.to_inv, bind_var]⟩

@[simp]
lemma mapVars_size {β σ} (g : α →ₛ β) (t : L.Term α σ) : (t.mapVars g).size = t.size := by
  induction t <;> simp_all only [mapVars, bind, size]

end term_monad

section renaming_and_reindexing

variable {β δ : Sorts → Type*} {t : Sorts} {σ ξ τ η : Signature Sorts}


/-- Relabel the sum type variables along a map of left summands -/
def rename {β : Sorts → Type _} {σ : Signature Sorts} (g : α →ₛ β) :
    L.Term (α ⊕ₛ γ) σ → L.Term (β ⊕ₛ γ) σ :=
  mapVars (fun s => Sum.map (g s) id)

def reindex {τ η σ : Signature Sorts} (g : SigMap τ η) :
    L.Term (α ⊕ₛ τ.Idx) σ → L.Term (α ⊕ₛ η.Idx) σ :=
  mapVars (fun s => Sum.map id (g s))

@[simp]
theorem rename_id (t : L.Term (α ⊕ₛ γ) σ) : t.rename (Fam.id α) = t := by
  simp only [rename, mapVars, Fam.id, Sum.map_id_id, id_eq, bind_var]

@[simp]
theorem rename_rename (t : L.Term (α ⊕ₛ γ) σ) (f : α →ₛ β) (g : β →ₛ δ) :
  (t.rename f).rename g = t.rename (g ∘ₛ f) := by
  simp only [rename, mapVars, bind_bind, bind, Sum.map_map, CompTriple.comp_eq]

@[simp]
theorem reindex_id (t : L.Term (α ⊕ₛ σ.Idx) τ) : t.reindex SigMap.Id = t := by
  simp only [reindex, mapVars, SigMap.Id, Fam.id, Sum.map_id_id, id_eq, bind_var]

@[simp]
theorem reindex_reindex (t : L.Term (α ⊕ₛ σ.Idx) ξ) (f : SigMap σ τ) (g : SigMap τ η) :
  (t.reindex f).reindex g = t.reindex (g ∘ₛ f) := by
  simp only [reindex, mapVars, bind_bind, bind, Sum.map_map, CompTriple.comp_eq]

variable {τ : Signature Sorts}

@[simp] theorem reindex_var_inl (s : Sorts) (a : α s) (g : SigMap σ τ) :
  (var s (Sum.inl a) : Term L (α ⊕ₛ σ.Idx) (of s)).reindex g
    = var s (Sum.inl a) := by
  rfl

@[simp] theorem reindex_var_inr (s : Sorts) (v : σ.Idx s) (g : SigMap σ τ) :
  (var s (Sum.inr v) : Term L (α ⊕ₛ σ.Idx) (of s)).reindex g
    = var s (Sum.inr (g s v)) := by
  rfl

@[simp] theorem reindex_func {ρ : Signature Sorts} {t : Sorts}
  (F : L.Functions ρ t) (ts : Term L (α ⊕ₛ σ.Idx) ρ) (g : SigMap σ τ) :
  (func F ts).reindex g = func F (ts.reindex g) := by
  simp only [reindex, mapVars, bind]

@[simp] theorem reindex_prod {ρ η : Signature Sorts}
  (t₁ : Term L (α ⊕ₛ σ.Idx) ρ) (t₂ : Term L (α ⊕ₛ σ.Idx) η) (g : SigMap σ τ) :
  (prod t₁ t₂).reindex g = prod (t₁.reindex g) (t₂.reindex g) := by
  simp only [reindex, mapVars, bind]

@[simp] theorem reindex_nil (g : SigMap σ τ) :
  (nil : Term L (α ⊕ₛ σ.Idx) .nil).reindex g = nil := by
  simp only [reindex, mapVars, bind]

@[simp]
theorem rename_var_inl (s : Sorts) (a : α s) (f : α →ₛ β) :
    (var s (Sum.inl a) : Term L (α ⊕ₛ σ.Idx) (of s)).rename f = var s (Sum.inl (f s a)) := by
  simp only [rename, mapVars, bind, Sum.map_inl]

@[simp]
theorem rename_var_inr (s : Sorts) (v : σ.Idx s) (f : α →ₛ β) :
    (var s (Sum.inr v) : Term L (α ⊕ₛ σ.Idx) (of s)).rename f = var s (Sum.inr v) := by
  simp only [rename, mapVars, bind, Sum.map_inr, id_eq]

@[simp]
theorem rename_func {τ : Signature Sorts} {t : Sorts}
    (g : L.Functions τ t) (ts : Term L (α ⊕ₛ σ.Idx) τ) (f : α →ₛ β) :
    (func g ts).rename f = func g (ts.rename f) := by
  simp only [rename, mapVars, bind]

@[simp]
theorem rename_prod {τ η : Signature Sorts}
    (t₁ : Term L (α ⊕ₛ σ.Idx) τ) (t₂ : Term L (α ⊕ₛ σ.Idx) η) (f : α →ₛ β) :
    (prod t₁ t₂).rename f = prod (t₁.rename f) (t₂.rename f) := by
  simp only [rename, mapVars, bind]

@[simp]
theorem rename_nil (f : α →ₛ β) :
    (nil : L.Term (α ⊕ₛ γ) .nil).rename f = nil := by
    simp only [rename, mapVars, bind]

@[simp]
lemma reindex_rename {β : Sorts → Type _} {σ τ ξ : Signature Sorts}
    (g : SigMap σ τ)
    (t : L.Term (α ⊕ₛ σ.Idx) ξ)
    (f : α →ₛ β) :
    (t.rename f).reindex g = (t.reindex g).rename f := by
    simp only [reindex, mapVars, rename, bind_bind, bind, Sum.map_map, CompTriple.comp_eq]


end renaming_and_reindexing

end Term

section term_constructors

def Term.varTerm : ∀ σ : Signature Sorts, Term L (Idx σ) σ
  | .nil =>
      .nil
  | .of s =>
      .var s Idx.var
  | .prod σ τ =>
      let leftTerm  : L.Term (Idx (σ ⨯ τ)) σ :=
        mapVars (fun s v => Idx.left (σ := σ) (τ := τ) (s := s) v)
          (varTerm σ)
      let rightTerm : L.Term (Idx (σ ⨯ τ)) τ :=
        mapVars (fun s v => Idx.right (σ := σ) (τ := τ) (s := s) v)
          (varTerm τ)
      .prod leftTerm rightTerm

/--
Given (t: Term α σ) and (v : σ.Idx s), we want to recover the term in t at position v.
  This is the direct analogue of `get` for SortedTuples on the semantic side.
-/
def Term.getLeafTerm {σ : Signature Sorts} (t : L.Term α σ) : σ.Idx →ₛ L.Term₁ α
  | s, v =>
  match t with
  | nil => isEmptyElim v
  | var s t =>
      match v with
      | Idx.var => var s t
  | func f r =>
      match v with
      | Idx.var => func f r
  | prod t₁ t₂ =>
    match v with
    | Idx.left w => getLeafTerm t₁ s w
    | Idx.right w => getLeafTerm t₂ s w


variable {s₁ s₂ : Sorts} {t : Sorts}
open Term Signature

/-- The representation of a constant symbol as a term. -/
def Constants.term (c : L.Constants t) : L.Term₁ α t :=
  func c nil

/-- Applies a unary function to a term. -/
def Functions.apply₁ (f : L.Functions ⦃s₁⦄ s₂) (t : L.Term₁ α s₁) : L.Term₁ α s₂ :=
  func f t

/-- Applies a binary function to two terms. -/
def Functions.apply₂ {s₁ s₂ : Sorts} (f : L.Functions (⦃s₁⦄ ⨯ ⦃s₂⦄) t)
   (g₁ : L.Term₁ α s₁) (g₂ : L.Term₁ α s₂) : L.Term₁ α t :=
   func f (prod g₁ g₂)

/- The representation of a function symbol as a term, on fresh variables indexed by `Idx σ` -/
def Functions.term {σ : Signature Sorts} {t : Sorts} (f : L.Functions σ t) : L.Term₁ (Idx σ) t
   := func f (varTerm σ)

end term_constructors

namespace Term

instance IdxNilEmpty {s : Sorts} : IsEmpty (Idx .nil s) := by
  constructor
  intro a
  cases a

instance IdxofInhabited {s : Sorts} : Inhabited (Idx (of s) s) := by
  constructor
  case default =>
    exact Idx.var

instance IdxofUnique {s : Sorts} : Unique (Idx (of s) s) := by
  constructor
  · intro a
    cases a
    case var => rfl

/-- Sends a term with constants to a term with extra variables. -/
@[simp]
def constantsToVars {σ : Signature Sorts} : L[[γ]].Term α σ → L.Term (γ ⊕ₛ α) σ
  | var t a => var t (Sum.inr a)
  | func (σ := σ) (t := t) f ts =>
    Sum.casesOn f
      (fun f => func f ts.constantsToVars)
      fun c => by
        cases σ
        case nil => exact var t (Sum.inl c)
        case of => exact isEmptyElim c
        case prod => exact isEmptyElim c
  | nil => nil
  | prod t₁ t₂ => prod (t₁.constantsToVars) (t₂.constantsToVars)


/-- Sends a term with extra variables to a term with constants. -/
@[simp]
def varsToConstants {σ : Signature Sorts}
 : L.Term (γ ⊕ₛ α) σ → L[[γ]].Term α σ
  | var t (Sum.inr a : (γ ⊕ₛ α) t)  => var t a
  | var _t (Sum.inl a : (γ ⊕ₛ α) _t) => Constants.term (Sum.inr a)
  | func (t := t) f ts => func (Sum.inl f) ts.varsToConstants
  | nil => nil
  | prod t₁ t₂ => prod (t₁.varsToConstants) (t₂.varsToConstants)

/-- A bijection between terms with constants and terms with extra variables. -/
@[simps]
def constantsVarsEquiv {τ : Signature Sorts} : L[[γ]].Term α τ ≃ L.Term (γ ⊕ₛ α) τ :=
  ⟨constantsToVars,
  varsToConstants,
  (by
    intro t
    induction t
    case var s t => simp_all only [constantsToVars, varsToConstants]
    case func σ t f ts ih =>
      match f with
      | Sum.inl f => simp_all only [constantsToVars, varsToConstants, constantsOn_Functions,
        constantsOnFunc]
      | Sum.inr c =>
          cases σ <;> cases ts
          · simp_all only [constantsToVars, varsToConstants, constantsOn_Functions,
              constantsOnFunc.eq_1]
            rfl
          · exact isEmptyElim c
          · exact isEmptyElim c
          · exact isEmptyElim c
    case nil => simp_all only [constantsToVars, varsToConstants]
    case prod t₁ t₂ => simp_all only [constantsToVars, varsToConstants]
  ),
  (by
    intro t
    induction t
    case var s t =>
      cases t with
      | inl val =>
        simp_all only [varsToConstants, constantsOn_Functions, constantsOnFunc]
        rfl
      | inr val_1 => simp_all only [varsToConstants, constantsToVars]
    case func σ t f ts ih =>
        simp_all only [varsToConstants, constantsOn_Functions, constantsOnFunc, constantsToVars]
    case nil => simp_all only [constantsToVars, varsToConstants]
    case prod t₁ t₂ => simp_all only [constantsToVars, varsToConstants]
  ) ⟩

variable {σ τ : Signature Sorts} {t : Sorts}

/-- A bijection between terms with constants and terms with extra variables. -/
def constantsVarsEquivLeft {β : Sorts → Type _} :
    L[[γ]].Term (α ⊕ₛ β) σ ≃ L.Term ((γ ⊕ₛ α) ⊕ₛ β ) σ :=
  (constantsVarsEquiv).trans (mapVarsEquiv (MSEquiv.fromEquivs fun _ => Equiv.sumAssoc _ _ _)).symm

@[simp]
theorem constantsVarsEquivLeft_apply {β : Sorts → Type _} (g : L[[γ]].Term (α ⊕ₛ β) σ) :
    constantsVarsEquivLeft g =
    (constantsToVars g).mapVars (fun _ => (Equiv.sumAssoc _ _ _).invFun) := rfl

@[simp]
theorem constantsVarsEquivLeft_symm_apply {β : Sorts → Type _} (g : L.Term ((γ ⊕ₛ α) ⊕ₛ β) σ) :
    (constantsVarsEquivLeft).symm g = varsToConstants (g.mapVars (fun _ => Equiv.sumAssoc _ _ _)) :=
  rfl

instance inhabitedOfVar [Inhabited (α t)] : Inhabited (L.Term₁ α t) :=
  ⟨var t default⟩


instance inhabitedOfConstant [Inhabited (L.Constants t)] : Inhabited (L.Term₁ α t) :=
  ⟨Constants.term (L := L) (α := α) (t := t) (default : L.Constants t)⟩


section substitution

variable {β : Sorts → Type*} {σ : Signature Sorts}


/-- Substitution of named variables via an assignment from names to terms. -/
def subst {β : Sorts → Type _} {σ : Signature Sorts} {τ : Signature Sorts}
  (t : L.Term (α ⊕ₛ σ.Idx) τ)
  (f : α →ₛ L.Term₁ (β ⊕ₛ σ.Idx)) :
  L.Term (β ⊕ₛ σ.Idx) τ:=
  t.bind (Fam.sumElim f (varOf Fam.inr))

@[simp]
theorem subst_id (t : Term L (α ⊕ₛ σ.Idx) τ) :
    t.subst (fun s a => var s (Sum.inl a)) = t := by
  induction t <;> simp_all only [subst, bind]
  rename_i a
  cases a with
  | inl val => simp_all only [Sum.elim_inl]
  | inr val_1 =>
    simp_all only [Sum.elim_inr]
    rfl

@[simp]
theorem subst_var_inl (s : Sorts) (a : α s)
    (f : α →ₛ L.Term₁ (β ⊕ₛ σ.Idx)) :
    (var s (Sum.inl a)).subst f = f s a := by
  simp only [subst, bind, Sum.elim_inl]

/--
Substituting a bound/context variable `inr v` leaves it unchanged.
-/
@[simp]
theorem subst_var_inr (s : Sorts) (v : σ.Idx s)
    (f : α →ₛ L.Term₁ (β ⊕ₛ σ.Idx)) :
    (var s (Sum.inr v)).subst f = var s (Sum.inr v) := by
  rfl

/--
Substitution pushes through function applications.
-/
@[simp]
theorem subst_func {τ : Signature Sorts} {t : Sorts}
    (g : L.Functions τ t) (ts : Term L (α ⊕ₛ σ.Idx) τ)
    (f : α →ₛ L.Term₁ (β ⊕ₛ σ.Idx)) :
    (func g ts).subst f = func g (ts.subst f) := by
  simp only [subst, bind]

/--
Substitution pushes through product terms.
-/
@[simp]
theorem subst_prod {τ η : Signature Sorts}
    (t₁ : Term L (α ⊕ₛ σ.Idx) τ) (t₂ : Term L (α ⊕ₛ σ.Idx) η)
    (f : α →ₛ L.Term₁ (β ⊕ₛ σ.Idx)) :
    (prod t₁ t₂).subst f = prod (t₁.subst f) (t₂.subst f) := by
  simp only [subst, bind]

/--
Opens bound variables in a term by splitting the rightmost block of bound variables.

Transforms a term `L.Term (α ⊕ₛ (η ⨯ τ).Idx) σ` into `L.Term ((α ⊕ₛ τ.Idx) ⊕ₛ η.Idx) σ`
by replacing `(η ⨯ τ).Idx` variables with a sum where:
- Variables from `η` (left block) become free variables on the right: `Sum.inr`
- Variables from `τ` (right block) become bound variables on the left: `Sum.inl (Sum.inr ...)`
- Original free variables `α` remain as `Sum.inl (Sum.inl ...)`

This is used to "open" a block of quantified variables, making them available as free variables.
The inverse operation is `instantiate` which substitutes terms back in.

⨯⨯Example use case⨯⨯: Opening the innermost quantifier block in nested quantifications.
-/
def openVars {τ η : Signature Sorts} {σ} :
              L.Term (α ⊕ₛ (η ⨯ τ).Idx) σ →
               L.Term ((α ⊕ₛ τ.Idx) ⊕ₛ η.Idx) σ :=
  let f : (α ⊕ₛ (η ⨯ τ).Idx) →ₛ
          (fun s => L.Term ((α ⊕ₛ τ.Idx) ⊕ₛ η.Idx) (of s)) :=
    Fam.sumElim
        (varOf
          (Fam.inl (α:= α ⊕ₛ τ.Idx) ∘ₛ Fam.inl (α:= α))
        )
        (fun s (v : (η ⨯ τ).Idx s) =>
          match v with
          | .left w => .var s (Sum.inr w)
          | .right w => .var s (Sum.inl (Sum.inr w))
        )
  fun ts =>
    ts.bind (L := L) f




/--
Substitutes the block of bound variables `η` (the rightmost factor of the prodExpr)
with the `η`-shaped term `u`.
-/
def instantiate {η : Signature Sorts} {ρ : Signature Sorts}
    (t : L.Term (α ⊕ₛ (σ ⨯ η).Idx) ρ)
    (u : L.Term (α ⊕ₛ σ.Idx) η) :
      L.Term (α ⊕ₛ σ.Idx) ρ :=
  t.bind (β := (α ⊕ₛ σ.Idx))
    (Fam.sumElim
      (varOf Fam.inl)
      (fun s (v : (σ ⨯ η).Idx s) =>
          match v with
          | Signature.Idx.left w =>
              Term.var s (Sum.inr w)
          | Signature.Idx.right w =>
              u.getLeafTerm s w))

/--
`getLeafTerm` commutes with `bind`: extracting a leaf from a substituted term
is the same as substituting into the extracted leaf.
-/
@[simp]
lemma getLeafTerm_bind {σ : Signature Sorts}
    (t : L.Term α σ) (f : α →ₛ L.Term₁ β)
    (s : Sorts) (w : σ.Idx s) :
    (t.bind f).getLeafTerm s w = (t.getLeafTerm s w).bind f := by
  induction t generalizing s with
  | nil => exact isEmptyElim w
  | var s' x =>
    cases w
    simp[getLeafTerm]
    cases f s' x  <;> simp[getLeafTerm]
  | func _ _ ih =>
    cases w
    simp only [bind, getLeafTerm]
  | prod t₁ t₂ ih₁ ih₂ =>
    cases w with
    | left w => simp only [bind, getLeafTerm, ih₁ s w]
    | right w => simp only [bind, getLeafTerm, ih₂ s w]

/--
Extracting a leaf from `varTerm σ` yields the corresponding variable.
-/
@[simp]
lemma getLeafTerm_varTerm (σ : Signature Sorts) (s : Sorts) (w : σ.Idx s) :
    (varTerm (L := L) σ).getLeafTerm s w = .var s w := by
  induction σ with
  | nil => exact isEmptyElim w
  | of s' => cases w; simp only [varTerm, getLeafTerm]
  | prod σ₁ σ₂ ih₁ ih₂ =>
    cases w with
    | left w =>
      simp_all only [varTerm, getLeafTerm, mapVars, getLeafTerm_bind, bind]
    | right w =>
      simp_all only [varTerm, getLeafTerm, bind, getLeafTerm_bind, mapVars, getLeafTerm_bind, bind]
/--
Commuting `reindex` and `getLeafTerm`.
Reindexing a term `u` and then extracting leaf `w` is the same as
extracting the leaf first and then reindexing it.
-/
@[simp]
lemma reindex_getLeafTerm {σ σ' η : Signature Sorts}
    (g : SigMap σ σ')
    (u : L.Term (α ⊕ₛ σ.Idx) η)
    (s : Sorts)
    (w : η.Idx s) :
    (u.reindex g).getLeafTerm s w = (u.getLeafTerm s w).reindex g := by
  induction u generalizing s with
  | nil =>
      exact isEmptyElim w
  | var s' a =>
      cases w
      simp only [reindex, mapVars, bind, getLeafTerm]
  | func f ts ih =>
      cases w
      simp only [reindex, mapVars, bind, getLeafTerm]
  | prod t₁ t₂ ih₁ ih₂ =>
      cases w with
      | left w_l =>
          simp only [reindex, mapVars, bind, getLeafTerm]
          exact ih₁ _ w_l
      | right w_r =>
          simp only [reindex, mapVars, bind, getLeafTerm]
          exact ih₂ _ w_r

/-- Commuting `reindex` and `instantiate`. Basically equates:

    - Swapping the variables in block `η` with a term `u`, then
      reindexing the result along `g`.

    - Reindexing the original term along `g` (extended to cover `η`), then
      swapping the block `η` with the reindexed term `u`.
-/
@[simp]
lemma instantiate_reindex_extend_right {σ' η τ}
  (g : SigMap σ σ')
  (u : L.Term (α ⊕ₛ σ.Idx) η)
  (t : L.Term (α ⊕ₛ (σ ⨯ η).Idx) τ) :
  (t.reindex (SigMap.extend_right g)).instantiate (u.reindex g)
    =
  (t.instantiate u).reindex g := by
  induction t with
  | nil =>
      rfl
  | var t a =>
      cases a with
      | inl a =>
          rfl
      | inr v =>
          cases v with
          | left w =>
              rfl
          | right w =>
              simp only [instantiate, reindex_getLeafTerm, bind]; rfl
  | func f r ih =>
      simp only [Term.reindex, Term.mapVars, Term.instantiate, Term.bind] at *
      rw [ih]
  | prod t₁ t₂ ih₁ ih₂ =>
      simp only [Term.reindex, Term.mapVars, Term.instantiate, Term.bind] at *
      rw [ih₁, ih₂]

/-- `getLeafTerm` is monotone nonincreasing in size. It isn't strictly decreasing
    at vars as it fixes them, but is strictly decreasing on func and prod terms. -/
lemma getLeafTerm_size_le
  {σ : Signature Sorts} {t : L.Term α σ} {s : Sorts} {v : σ.Idx s} :
    (t.getLeafTerm s v).size <= t.size := by
    revert s v
    induction t with
    | nil => intro s v; cases v
    | var s' x => intro s v; cases v; simp only [getLeafTerm, le_refl]
    | func f r ih => intro s v; cases v; simp only [getLeafTerm, le_refl]
    | @prod σ₁ σ₂ t₁ t₂ ih₁ ih₂ =>
      intro s v; cases v
      case left w =>
        have h:= ih₁ (v:= w)
        simp only [getLeafTerm, size]
        linarith
      case right w =>
        have h:= ih₂ (v:= w)
        simp only [getLeafTerm, size]
        linarith

lemma getLeafTerm_size_lt_func
  {σ : Signature Sorts} {ts : L.Term α σ} {s : Sorts} {v : σ.Idx s} {f : L.Functions σ t} :
    (ts.getLeafTerm s v).size < (func f ts).size := by
  simp only[size]
  let h := getLeafTerm_size_le (t := ts) (v := v)
  linarith

lemma getLeafTerm_size_lt_prod_l
  {σ τ : Signature Sorts} {t₁ : L.Term α σ} {t₂ : L.Term α τ} :
    t₁.size < (prod t₁ t₂).size := by
  simp only [size]
  linarith

lemma getLeafTerm_size_lt_prod_r
  {σ τ : Signature Sorts} {t₁ : L.Term α σ} {t₂ : L.Term α τ} :
    t₂.size < (prod t₁ t₂).size := by
  simp only [size, lt_add_iff_pos_left, add_pos_iff, _root_.zero_lt_one, true_or]

/--
Substitutes function symbols in a term with term templates.

Given a term in language `L` and a mapping from `L`-function symbols to `L'`-term templates,
replaces each function application `func f ts` with the template `tf σ t f`, binding the
template's variables to the leaf terms extracted from `ts`.

⨯⨯Parameters:⨯⨯
- Term in language `L` with variables `α`
- Template map `tf : ∀ σ t, L.Functions σ t → L'.Term σ.Idx ⦃t⦄` that assigns
  a term template (with variables indexed by `σ.Idx`) to each function symbol

⨯⨯Example use case⨯⨯: Translating between languages or replacing function symbols with
their definitions. For instance, replacing a binary function `f(x,y)` with a template
like `g(x) + h(y)`.

The binding preserves the structure: leaf terms from the original arguments are substituted
into the corresponding positions in the template.
-/
@[simp]
def bindFunc {σ : Signature Sorts} :
  L.Term α σ →
  (∀ σ t, L.Functions σ t → L'.Term σ.Idx ⦃t⦄) →
  L'.Term α σ
  | nil, _  => nil
  | var t a, _ => var t a
  | func (σ := σ) (t := t) f ts, tf =>
      (tf σ t f).bind (fun s => fun v => (ts.getLeafTerm s v).bindFunc tf)
  | prod t₁ t₂, tf => prod (t₁.bindFunc tf) (t₂.bindFunc tf)
termination_by
  t _ => t.size
decreasing_by
  -- The recursive call in the `func` case
  · -- goal is: (ts.getLeafTerm s v).size < (func f ts).size
    simp only [getLeafTerm_size_lt_func (σ := σ) (ts := ts) (s := s) (v := v) (f := f)]
  -- The recursive call on `t₁` in the `prod` case
  · -- goal is: t₁.size < (prod t₁ t₂).size
    simp only [getLeafTerm_size_lt_prod_l (t₁ := t₁) (t₂ := t₂)]
  -- The recursive call on `t₂` in the `prod` case
  · -- goal: t₂.size < (prod t₁ t₂).size
    simp only [getLeafTerm_size_lt_prod_r (t₁ := t₁) (t₂ := t₂)]

@[simp]
lemma mapVars_bind {β : Sorts → Type _} {σ : Signature Sorts}
  (ρ : α →ₛ β)
  (t : L.Term α σ)
  (f : β →ₛ L.Term₁ γ) :
  (mapVars ρ t).bind f =
    t.bind (fun s v => f s (ρ s v)) := by
  induction t <;> simp_all only [mapVars, bind, var_bind]

@[simp]
theorem rename_subst (t : Term L (α ⊕ₛ σ.Idx) τ)
    (f : α →ₛ β)
    (g : β →ₛ L.Term₁ (γ ⊕ₛ σ.Idx)) :
    (t.rename f).subst g = t.subst (fun s a => g s (f s a)) := by
  induction t <;> simp_all only [subst, rename, mapVars, bind]
  case var a =>
  cases a with
  | inl val => simp_all only [Sum.map_inl, Sum.elim_inl]
  | inr val_1 => simp_all only [Sum.map_inr, id_eq, Sum.elim_inr]

@[simp]
theorem subst_rename (t : Term L (α ⊕ₛ σ.Idx) τ)
    (f : α →ₛ L.Term₁ (β ⊕ₛ σ.Idx))
    (g : β →ₛ γ) :
    (t.subst f).rename g = t.subst (fun s a => (f s a).rename g) := by
  induction t with
  | var _ a =>
    cases a with
    | inl val => rfl
    | inr val => rfl
  | func F t' ih =>
      simp only [subst_func, rename_func, ih]
  | prod =>
      simp_all only [subst_prod, rename_prod]
  | nil =>
      rfl

/- 4. Subst then Subst (Composition)
 This is the hardest one, usually requiring the `bind_bind` lemma I mentioned in the previous turn.
It says (t[f])[g] = t[x ↦ f(x)[g]] -/
@[simp]
theorem subst_subst (t : Term L (α ⊕ₛ σ.Idx) τ)
    (f : α →ₛ L.Term₁ (β ⊕ₛ σ.Idx))
    (g : β →ₛ L.Term₁ (γ ⊕ₛ σ.Idx)) :
    (t.subst f).subst g = t.subst (fun s a => (f s a).subst g) := by
    induction t with
  | var _ a =>
    cases a with
    | inl val => rfl
    | inr val => rfl
  | func F t' ih =>
      simp only [subst_func, ih]
  | prod =>
      simp_all only [subst_prod]
  | nil =>
      rfl


/--
Substituting leaf terms into varTerm returns the original term:
-/
@[simp]
lemma IdxTerm_subst_getLeaf
  (σ : Signature Sorts) (ts : L.Term α σ) :
  (varTerm σ).bind (fun s v => ts.getLeafTerm s v) = ts := by
  induction σ with
  | nil =>
      cases ts
      simp only [varTerm, bind]
  | of s =>
      cases ts with
      | var s' a =>
          simp only [varTerm, getLeafTerm, bind]
      | func f' ts' =>
          simp only [varTerm, getLeafTerm, bind]
  | prod σ₁ σ₂ ih₁ ih₂ =>
      cases ts with
      | prod t₁ t₂ =>
          unfold varTerm
          simp only [bind, mapVars, getLeafTerm, bind_bind, ih₁ t₁, ih₂ t₂]

/--
Substituting leaf terms of ts into the generic function term for f returns `func f ts`:
-/
@[simp] lemma Functions.term_subst_getLeaf
  (σ : Signature Sorts) (t : Sorts)
  (f : L.Functions σ t) (ts : L.Term α σ) :
  (Functions.term f).bind (fun s v => ts.getLeafTerm s v) = func f ts := by
  simp only [Functions.term, bind, IdxTerm_subst_getLeaf]

/--
Helper lemma for bindFunc_term: since bindFunc's recursive call on `func` terms is actually
on `ts.getLeafTerm s v` rather than `ts`, it's helpful to prove this special case separately.
-/
lemma bindFunc_getLeafTerm {s : Sorts} {σ : Signature Sorts} {v : σ.Idx s} {g : L.Term α σ} :
  ((g.getLeafTerm s v).bindFunc (@Functions.term _ _)) = g.getLeafTerm s v := by
  revert s v
  induction g with
  | var s x =>
    intro s' v; cases v
    case var => simp only [getLeafTerm, bindFunc]
  | func f r ih =>
    intro s v; cases v
    case var => simp only [getLeafTerm, bindFunc, ih, Functions.term_subst_getLeaf]
  | prod t₁ t₂ ih₁ ih₂ =>
    intro s v; cases v
    case left => simp_all only [getLeafTerm]
    case right => simp_all only [getLeafTerm]
  | nil => simp

@[simp]
theorem bindFunc_term
 (g : L.Term α σ) :
  g.bindFunc (@Functions.term _ _) = g := by
  induction g
  case nil =>
    simp_all only [bindFunc]
  case var =>
    simp_all only [bindFunc]
  case func f ts h =>
    have h' : (fun s v ↦ (ts.getLeafTerm s v).bindFunc (@Functions.term Sorts L))
              = fun s v ↦ (ts.getLeafTerm s v):= by
      ext s v; exact bindFunc_getLeafTerm (s:= s) (v:= v)
    unfold bindFunc; rw[h']
    simp
  case prod t₁ t₂ ih₁ ih₂ =>
    simp_all only [bindFunc]

lemma reindex_subst {β : Sorts → Type _} {σ τ ξ : Signature Sorts}
    (g : SigMap σ τ)
    (t : L.Term (α ⊕ₛ σ.Idx) ξ)
    (f : α →ₛ L.Term₁ (β ⊕ₛ σ.Idx)) :
    (t.subst f).reindex g =
    (t.reindex g).subst (fun s a => (f s a).reindex g) := by
    unfold reindex subst
    simp_all only [mapVars, bind_bind, bind]
    apply congr
    · rfl
    · ext s a
      cases a with
      | inl val => simp_all only [Sum.elim_inl, Sum.map_inl, id_eq]
      | inr val_1 =>
        simp_all only [Sum.elim_inr, Sum.map_inr]
        rfl


syntax "reduce_term_to_bind" : tactic

macro_rules
  | `(tactic| reduce_term_to_bind) =>
      `(tactic|
        simp (config := { zeta := true }) only [
          MSFirstOrder.MSLanguage.Term.subst,
          MSFirstOrder.MSLanguage.Term.rename,
          MSFirstOrder.MSLanguage.Term.reindex,
          MSFirstOrder.MSLanguage.Term.openVars,
          MSFirstOrder.MSLanguage.Term.instantiate,
          MSFirstOrder.MSLanguage.Term.mapVars,
          MSFirstOrder.MSLanguage.Term.bind,
          MSFirstOrder.MSLanguage.Term.varOf,
          MSFirstOrder.Fam.sumElim
        ];
        repeat simp only [MSFirstOrder.MSLanguage.Term.bind_bind]
      )

end substitution

section variable_finsets
/-! ### Variable Finsets

This section defines operations for collecting the free variables used in a term
into finite sets. This is used for scope analysis and variable restriction.
-/

open Finset

/-- The `Finset` of variables used in a given term (now multi-sorted). -/
@[simp]
def varFinset {σ : Signature Sorts} {α : Sorts → Type u'}
    [DecidableEq Sorts] [∀ t, DecidableEq (α t)] : L.Term α σ →  Finset (Σ t, α t)
  | var t i => {⟨_,i⟩}
  | func _ args => args.varFinset
  | prod t₁ t₂ => t₁.varFinset ∪ t₂.varFinset
  | nil => ∅

lemma varFinset_prod_subset_left {σ₁ σ₂ : Signature Sorts} {α : Sorts → Type u'}
    {t₁ : L.Term α σ₁} {t₂ : L.Term α σ₂}
    [DecidableEq Sorts] [∀ t, DecidableEq (α t)] : varFinset t₁ ⊆ varFinset (prod t₁ t₂) := by
    exact union_subset_left fun ⦃a⦄ a_1 ↦ a_1

lemma varFinset_prod_subset_right {σ₁ σ₂ : Signature Sorts} {α : Sorts → Type u'}
    {t₁ : L.Term α σ₁} {t₂ : L.Term α σ₂}
    [DecidableEq Sorts] [∀ t, DecidableEq (α t)] : varFinset t₂ ⊆ varFinset (prod t₁ t₂) := by
    exact union_subset_right fun ⦃a⦄ a_1 ↦ a_1

/-- The `Finset` of variables from the left side of a sum used in a given term. -/
@[simp]
def varFinsetLeft {β : Sorts → Type _} {σ : Signature Sorts}
  [DecidableEq Sorts] [∀ t, DecidableEq (α t)] :
    L.Term (α ⊕ₛ β) σ → Finset (Σ t, α t)
  | var _ (Sum.inl i) => {⟨_,i⟩}
  | var _ (Sum.inr _i) => ∅
  | func _ args => args.varFinsetLeft
  | prod t₁ t₂ => t₁.varFinsetLeft ∪ t₂.varFinsetLeft
  | nil => ∅

end variable_finsets

section variable_restriction
/-! ### Variable Restriction

This section defines operations for restricting terms to use only a specified
subset of their free variables. Used for scope management and variable elimination.
-/

open Finset
variable {β : Sorts → Type v'}


/-- Restricts a term to use only a set of the given variables. -/
def restrictVar
  [DecidableEq Sorts]
  [∀ s, DecidableEq (α s)]
  : ∀ {σ : Signature Sorts} (t : L.Term α σ)
      (_f : ∀ {s}, {x : α s // ⟨s, x⟩ ∈ varFinset t} → β s),
      L.Term β σ
| _ , var t a, g =>
    let x : {x : α t // ⟨t, x⟩ ∈ varFinset (var t a) } :=
      { val := a,
        property := by simp only [varFinset, mem_singleton] }
    var t (@g t x)
| _, func f ts, g =>
    func f (restrictVar ts g)
| _, prod t₁ t₂, g =>
    prod (restrictVar t₁ (fun x => g ⟨x.val, by
          simp_all only [varFinset, mem_union]
          obtain ⟨val, property⟩ := x
          simp_all only [true_or]⟩ ))
        (restrictVar t₂ (fun x => g ⟨x.val, by
          simp_all only [varFinset, mem_union]
          obtain ⟨val, property⟩ := x
          simp_all only [or_true]⟩))
  | _, nil, _ => nil

/-- Restricts a term to use only a set of the given variables on the left side of a sum. -/
def restrictVarLeft {β : Sorts → Type _} [DecidableEq Sorts] {γ : Sorts → Type*}
  [∀ t, DecidableEq (α t)]
  : ∀ {σ : Signature Sorts} (f : L.Term (α ⊕ₛ γ) σ)
      (_ : ∀ {s}, {x : α s // ⟨s, x⟩ ∈ varFinsetLeft f } → β s),
    L.Term (β ⊕ₛ γ) σ
| _, var t (Sum.inl a), g =>
  let x : {x : α t // ⟨t, x⟩ ∈ varFinsetLeft (var t (Sum.inl a)) } :=
      { val := a,
        property := by simp only [varFinsetLeft, mem_singleton] }
  var t (Sum.inl (@g t x))
| _, var t (Sum.inr a), _ => var t (Sum.inr a)
| _, func t ts, g =>
  func t (restrictVarLeft ts g)
| _, prod t₁ t₂, g =>
    prod
        (restrictVarLeft t₁ (fun x => g ⟨x.val, by
          simp_all only [varFinsetLeft, mem_union]
          obtain ⟨val, property⟩ := x
          simp_all only [true_or]⟩ ))
        (restrictVarLeft t₂ (fun x => g ⟨x.val, by
          simp_all only [varFinsetLeft, mem_union]
          obtain ⟨val, property⟩ := x
          simp_all only [or_true]⟩))
| _, nil, _ => nil

end variable_restriction

open Idx
variable {σ ξ τ η : Signature Sorts}

/-- The term-level identity needed for `BoundedFormula.openVars_closeVars` when `closeVars` is
defined via `relabel` + `SigEquiv.comm`.
  Shows that opening vars then closing them is the identity. -/
@[simp]
lemma openVars_close_id
  (t : L.Term (α ⊕ₛ (σ ⨯ τ).Idx) ξ) :
  Term.reindex (SigEquiv.comm (σ := τ) (τ := σ)).toFun
      ((Term.reindex (SigMap.incl_right : SigMap σ (τ ⨯ σ)) t.openVars).subst
        (Fam.sumElim
          (varOf Fam.inl)
          (varOf (Fam.inr ∘ₛ (fun s => @Idx.left _ _ _ s)))))
    = t := by
  induction t with
  | nil =>
      simp only [reindex, mapVars, subst, openVars, bind]
  | func f ts ih =>
      simp_all only [openVars, bind, reindex_func, subst_func]
  | prod t₁ t₂ ih₁ ih₂ =>
      simp_all only [openVars, bind, reindex_prod, subst_prod]
  | var s a =>
      cases a with
      | inl b => rfl
      | inr v =>
          cases v with
          | left w => rfl
          | right w => rfl

/--
General version: closing variables with `f: X → τ.Idx` then opening them is
equivalent to renaming the variables from `X` to `τ.Idx` via `f`.
-/
lemma close_openVars
  {σ τ : Signature Sorts} {ξ : Signature Sorts} {X : Sorts → Type*}
  (f : X →ₛ τ.Idx)
  (t : L.Term ((α ⊕ₛ X) ⊕ₛ σ.Idx) ξ) :
  openVars (L := L) (α := α) (η := σ) (τ := τ)
    (reindex (SigEquiv.comm (σ := τ) (τ := σ)).toFun
      ((t.reindex
          (SigMap.incl_right : SigMap σ (τ ⨯ σ))
       ).subst
          (Fam.sumElim
            (varOf Fam.inl)
            (fun s x => var s (Sum.inr (Signature.Idx.left (f s x))))
        )
      )
    )
  = (t.rename (Fam.sumElim (fun _ a => Sum.inl a) (fun s x => Sum.inr (f s x)))) := by
  induction t with
  | nil =>
      simp only [openVars, reindex, mapVars, subst, bind, rename]
  | func g ts ih =>
      simp only [openVars, reindex, mapVars, subst, bind_bind, bind,
        rename_func] at *
      rw [ih]
  | prod t₁ t₂ ih₁ ih₂ =>
      simp only [openVars, reindex, mapVars, subst, bind_bind, bind,
        rename_prod] at *
      rw [ih₁, ih₂]
  | var s a =>
      simp_all only
      cases a with
      | inl val =>
        cases val with
        | inl val_1 =>
          simp_all only [reindex_var_inl, subst_var_inl, Sum.elim_inl, rename_var_inl]
          rfl
        | inr
          val_2 =>
          simp_all only [reindex_var_inl, subst_var_inl, Sum.elim_inr,
            reindex_var_inr, rename_var_inl]
          rfl
      | inr val_1 =>
        simp_all only [reindex_var_inr, subst_var_inr, rename_var_inr]
        rfl

/-- Specialized version of `close_openVars` with `X := τ.Idx` and `f := id`,
so the overall effect is the identity. -/
@[simp]
lemma close_openVars_id_id
  {σ τ : Signature Sorts} {ξ : Signature Sorts}
  (t : L.Term ((α ⊕ₛ τ.Idx) ⊕ₛ σ.Idx) ξ) :
  openVars (L := L) (α := α) (η := σ) (τ := τ)
    (reindex (SigEquiv.comm (σ := τ) (τ := σ)).toFun
      ((t.reindex
          (SigMap.incl_right : SigMap σ (τ ⨯ σ))
       ).subst
          (Fam.sumElim
            (varOf Fam.inl)
            (fun s x => var s (Sum.inr x.left))
        )
      )
    )
  = t := by
  have h := @close_openVars _ _ _ σ τ ξ (τ.Idx) (fun s (x : τ.Idx s) => x) t
  rw [h]
  have eq_id : (Fam.sumElim (fun _ (a : α _) => Sum.inl a) (fun s (x : τ.Idx s) => Sum.inr x) :
          (α ⊕ₛ τ.Idx) →ₛ (α ⊕ₛ τ.Idx)) = Fam.id (α ⊕ₛ τ.Idx) := by
    funext s x
    cases x with
    | inl a => rfl
    | inr x => rfl
  rw [eq_id]
  exact rename_id t

end Term

namespace LHom

variable {σ : Signature Sorts}

open Term

/-- Maps a term's symbols along a language map. -/
@[simp]
def onTerm {σ : Signature Sorts} (φ : L →ᴸ L') : L.Term α σ → L'.Term α σ
  | .nil => nil
  | var t a => var t a
  | func f ts => func (φ.onFunction f) (φ.onTerm ts)
  | Term.prod t₁ t₂ => (φ.onTerm t₁).prod (φ.onTerm t₂)

@[simp]
theorem id_onTerm : ((LHom.id L).onTerm : L.Term α σ → L.Term α σ) = id := by
  ext t
  induction t with
  | nil => simp only [onTerm, id_eq]
  | var => rfl
  | func _ _ ih => simp only [onTerm, id_onFunction, id_eq, ih]
  | prod t₁ t₂ ih₁ ih₂ => simp only [onTerm, ih₁, id_eq, ih₂]


@[simp]
theorem comp_onTerm {L'' : MSLanguage Sorts} (φ : L' →ᴸ L'') (ψ : L →ᴸ L') :
    ((φ.comp ψ).onTerm : L.Term α σ → L''.Term α σ) = φ.onTerm ∘ ψ.onTerm := by
  ext t
  induction t with
  | nil => simp only [onTerm, Function.comp_apply]
  | var => rfl
  | func _ _ ih => simp_rw [onTerm, ih]; rfl
  | prod t₁ t₂ ih₁ ih₂ => simp only [onTerm, ih₁, Function.comp_apply, ih₂]

end LHom

/-- Maps a term's symbols along a language equivalence. -/
@[simps]
def LEquiv.onTerm {σ : Signature Sorts} (φ : L ≃ᴸ L') : L.Term α σ ≃ L'.Term α σ where
  toFun := φ.toLHom.onTerm
  invFun := φ.invLHom.onTerm
  left_inv := by
    rw [Function.leftInverse_iff_comp, ← LHom.comp_onTerm, φ.left_inv, LHom.id_onTerm]
  right_inv := by
    rw [Function.rightInverse_iff_comp, ← LHom.comp_onTerm, φ.right_inv, LHom.id_onTerm]

variable (L : MSLanguage.{u, v, z} Sorts)


/-- A bounded formula for a many-sorted language `L`, with free variables in `α`. -/
inductive BoundedFormula (α : Sorts → Type u') : Signature Sorts → Type (max u v z u')
  | falsum {σ} : BoundedFormula α σ
  | equal {σ τ}
    -- note: only terms with the exact same signatures can be set equal to eachother
      (t₁ t₂ : L.Term (α ⊕ₛ σ.Idx) τ) :
      BoundedFormula α σ
  | rel {σ σ'}
      (R : L.Relations σ')
      (ts : (L.Term (α ⊕ₛ σ.Idx) σ')) :
      BoundedFormula α σ
  /-- The logical implication of two bounded formulas-/
  | imp {σ}
      (f₁ f₂ : BoundedFormula α σ) :
      BoundedFormula α σ
  /-- Adds a universal quantifier to a bounded formula-/
  | all {σ} (τ)
      (f : BoundedFormula α (σ ⨯ τ)) :
      BoundedFormula α σ



/-- Size of a bounded formula, useful for proving termination of recursion. -/
def BoundedFormula.size : {σ : Signature Sorts} → L.BoundedFormula α σ → Nat
    | _, .falsum            => 1
    | _, .equal _ _        => 1
    | _, .rel _ ts  => 1 + ts.size
    | _, .imp f₁ f₂     => 1 + BoundedFormula.size f₁ + BoundedFormula.size f₂
    | _, all _ f => 1 + BoundedFormula.size f

attribute [simp] BoundedFormula.size

abbrev Formula (L : MSLanguage.{u, v, z} Sorts) (α : Sorts → Type u') := BoundedFormula L α nil


/-- A sentence is a formula with no free variables. -/
abbrev Sentence (L : MSLanguage.{u, v, z} Sorts) :=
  Formula L Fam.EmptyFam

/-- A theory is a set of sentences. -/
abbrev Theory :=
  Set L.Sentence

open Finsupp

variable {L : MSLanguage.{u, v, z} Sorts} {α : Sorts → Type u'} {β : Sorts → Type v'}
  {σ ξ τ η : Signature Sorts} {s s₁ s₂ : Sorts}

/-! ### Relation and Equality Constructors -/

/-- Applies a relation to terms as a bounded formula. -/
def Relations.boundedFormula {ξ : Signature Sorts} (R : L.Relations σ)
    (ts : L.Term (α ⊕ₛ ξ.Idx) σ) : L.BoundedFormula α ξ :=
  BoundedFormula.rel R ts

/-- Applies a unary relation to a term as a bounded formula. -/
def Relations.boundedFormula₁ (r : L.Relations (of s)) (t : L.Term (α ⊕ₛ σ.Idx) (of s)) :
    L.BoundedFormula α σ := r.boundedFormula t

/-- Applies a binary relation to two terms as a bounded formula. -/
def Relations.boundedFormula₂ (r : L.Relations (⦃s₁⦄ ⨯ ⦃s₂⦄)) (t₁ : L.Term (α ⊕ₛ σ.Idx) ⦃s₁⦄)
    (t₂ : L.Term (α ⊕ₛ σ.Idx) ⦃s₂⦄) :
    L.BoundedFormula α σ := r.boundedFormula (t₁.prod t₂)

/-- The equality of two tuples of terms as a bounded formula. -/
def Term.bdEqual (t₁ t₂ : L.Term (α ⊕ₛ σ.Idx) ξ) : L.BoundedFormula α σ :=
  BoundedFormula.equal t₁ t₂

/-- Applies a relation to terms as a formula. -/
def Relations.formula (R : L.Relations σ) (ts : L.Term α σ) : L.Formula α :=
  R.boundedFormula (ts.mapVars (fun _ => Sum.inl))
/-- Applies a unary relation to a term as a formula. -/
def Relations.formula₁ (r : L.Relations (of s)) (t : L.Term α (of s)) : L.Formula α :=
  Relations.formula r t

/-- Applies a binary relation to two terms as a formula. -/
def Relations.formula₂ (r : L.Relations (⦃s₁⦄ ⨯ ⦃s₂⦄)) (t₁ : L.Term₁ α s₁) (t₂ : L.Term₁ α s₂) :
    L.Formula α := Relations.formula r (t₁.prod t₂)

/-- The equality of two terms as a first-order formula. -/
def Term.equal (t₁ t₂ : L.Term α σ) : L.Formula α :=
  (mapVars (fun _ => Sum.inl) t₁).bdEqual (mapVars (fun _ => Sum.inl) t₂)

namespace BoundedFormula

/-! ### Basic Instances -/

instance : Inhabited (L.BoundedFormula α σ) :=
  ⟨falsum⟩

instance : Bot (L.BoundedFormula α σ) :=
  ⟨falsum⟩

/-! ### Logical Connectives and Quantifiers -/

/-- The negation of a bounded formula is also a bounded formula. -/
@[match_pattern]
protected def not (φ : L.BoundedFormula α σ) : L.BoundedFormula α σ :=
  φ.imp ⊥

/-- Puts an `∃` quantifier on a bounded formula. -/
@[match_pattern]
protected def ex (ξ : Signature Sorts) (φ : L.BoundedFormula α (σ ⨯ ξ)) : L.BoundedFormula α σ :=
  φ.not.all.not

/-- Takes the logical disjunction of two bounded formulas. -/
@[match_pattern]
protected def or (φ ψ : L.BoundedFormula α σ) : L.BoundedFormula α σ :=
  φ.not.imp ψ

/-- Takes the logical conjunction of two bounded formulas. -/
@[match_pattern]
protected def and (φ ψ : L.BoundedFormula α σ) : L.BoundedFormula α σ :=
  (φ.not.or ψ.not).not

/-! ### Typeclass Instances for Lattice Operations -/

instance : Top (L.BoundedFormula α σ) :=
  ⟨BoundedFormula.not ⊥⟩

instance : Min (L.BoundedFormula α σ) :=
  ⟨fun f g => (f.imp g.not).not⟩

instance : Max (L.BoundedFormula α σ) :=
  ⟨fun f g => f.not.imp g⟩

/-- The biimplication between two bounded formulas. -/
protected def iff (φ ψ : L.BoundedFormula α σ) :=
  φ.imp ψ ⊓ ψ.imp φ

/-! ### Free Variables -/

open Finset
open Finsupp

/-- The `Finset` of variables used in a given formula. -/
@[simp]
def freeVarFinset [DecidableEq Sorts] [∀ s, DecidableEq (α s)] :
    ∀ {σ}, L.BoundedFormula α σ → Finset (Σ s, α s)
  | _n, falsum => ∅
  | _n, equal t₁ t₂ => t₁.varFinsetLeft ∪ t₂.varFinsetLeft
  | _n, rel _R ts =>  ts.varFinsetLeft
  | _n, imp f₁ f₂ => f₁.freeVarFinset ∪ f₂.freeVarFinset
  | _n, all _ f => f.freeVarFinset

/-! ### Variable Reindexing -/

open Signature
open SigMap

/-- Reindexes `L.BoundedFormula α σ` as `L.BoundedFormula α τ`, given a dependent family of
embeddings `σ.Idx → τ.Idx`.

This could be a SigEmbed if we want it to model the original idea of "Moving some variables right"
-/
@[simp]
def reindex : ∀ {σ τ : Signature Sorts} (_ : SigMap σ τ ),
     L.BoundedFormula α σ → L.BoundedFormula α τ
  | _, _, _, falsum => falsum
  | _, _, h, equal t₁ t₂ =>
    equal (t₁.reindex h) (t₂.reindex h)
  | _, _, h, rel R ts => rel R (ts.reindex h)
  | _, _, h, imp f₁ f₂ => (f₁.reindex h).imp (f₂.reindex h)
  | _, _, h, all _ f => (f.reindex (h.extend_right)).all


@[simp]
lemma reindex_size {τ : Signature Sorts} (g : SigMap σ τ) (φ : L.BoundedFormula α σ) :
  (φ.reindex g).size = φ.size := by
  induction φ generalizing τ with
  | falsum => simp only [reindex, size]
  | equal t₁ t₂ => simp only [reindex, size]
  | rel r t =>
    unfold reindex Term.reindex size
    rw[Term.mapVars_size]
  | imp φ₁ φ₂ ih₁ ih₂ => simp only [reindex, size, ih₁, ih₂]
  | all τ φ ih => simp_all only [reindex, size]

@[simp]
theorem reindex_id {σ : Signature Sorts} (φ : L.BoundedFormula α σ) :
  φ.reindex SigMap.Id = φ := by
  induction φ with
  | falsum =>
      simp only [reindex]
  | @equal σ τ t₁ t₂ =>
      change equal (t₁.reindex SigMap.Id) (t₂.reindex SigMap.Id) = equal t₁ t₂
      simp_all only [Term.reindex_id]
  | @rel σ τ R ts =>
      change rel R (ts.reindex SigMap.Id) = rel R ts
      simp_all only [Term.reindex_id]
  | imp φ₁ φ₂ ih₁ ih₂ =>
      simp_all only [reindex]
  | all _ φ ih =>
      rw [BoundedFormula.reindex]
      rw[SigMap.idExtend]
      simp_all only

@[simp]
theorem reindex_reindex : ∀ {σ τ η : Signature Sorts} (hστ : SigMap σ τ) (hτη : SigMap τ η)
                         (φ : L.BoundedFormula α σ),
    (φ.reindex hστ).reindex hτη = φ.reindex (hτη ∘ₛ hστ) := by
  intro σ τ η hστ hτη φ
  revert τ η
  induction φ with
  | falsum => intros; rfl
  | equal =>
    intro τ_1 η hστ hτη; simp_all only [reindex, Term.reindex_reindex]
  | rel =>
    intros; simp_all only [reindex, Term.reindex_reindex]
  | imp _ _ ih1 ih2 => simp only [reindex, ih1, ih2, implies_true]
  | all _ φ ih => simp only [reindex, ih, extend_right_comp, implies_true]

@[simp]
theorem reindex_comp_reindex {σ τ η : Signature Sorts} (hστ : SigMap σ τ) (hτη : SigMap τ η) :
    (reindex hτη ∘ reindex hστ :
        L.BoundedFormula α σ → L.BoundedFormula α η) =
      BoundedFormula.reindex (hτη ∘ₛ hστ) :=
  funext (reindex_reindex hστ hτη)

/-! ### Quantifier Operations -/

/-- Places universal quantifiers on all extra variables of a bounded formula. -/
def alls : ∀ {σ}, L.BoundedFormula α σ → L.Formula α
  | .nil , φ => φ
  --We change the shape (of s) to nil ⨯ ⦃s⦄ to prepare it for universal quantification:
  | .of s , φ => (reindex (L := L) (α:= α ) (SigEquiv.nilLeft (of s)).symm φ).all
  | .prod _ _  , φ => φ.all.alls

/-- Places existential quantifiers on all extra variables of a bounded formula. -/
def exs : ∀ {σ}, L.BoundedFormula α σ → L.Formula α
  | .nil , φ => φ
  --We change the shape (of s) to nil ⨯ ⦃s⦄ to prepare it for existential quantification:
  | .of s , φ => (reindex (L := L) (α:= α ) (SigEquiv.nilLeft (of s)).symm φ).ex
  | .prod _ _  , φ => φ.ex.exs

/-! ### Free Variable Restriction -/

abbrev freeVarType [DecidableEq Sorts] [∀ s, DecidableEq (α s)] (φ : L.BoundedFormula α σ) :=
  fun s => {x : α s // ⟨s, x⟩ ∈ freeVarFinset φ }

/-- The freeVarType of a formula is finite when the Sigma type over all free variables is finite. -/
instance freeVarType_finite [DecidableEq Sorts] [∀ s, DecidableEq (α s)]
    (φ : L.BoundedFormula α σ) : Finite (Sigma φ.freeVarType) := by
  -- freeVarType s = {x : α s // ⟨s, x⟩ ∈ freeVarFinset φ}
  -- So Sigma freeVarType ≃ {p : Σ s, α s // p ∈ freeVarFinset φ}
  -- which is finite since freeVarFinset φ is a Finset
  have h : (Sigma φ.freeVarType) ≃ ↑(freeVarFinset φ) := {
    toFun := fun ⟨s, x, hx⟩ => ⟨⟨s, x⟩, hx⟩
    invFun := fun ⟨⟨s, x⟩, hx⟩ => ⟨s, x, hx⟩
    left_inv := fun ⟨s, x, hx⟩ => rfl
    right_inv := fun ⟨⟨s, x⟩, hx⟩ => rfl
  }
  exact Finite.of_equiv _ h.symm

/-- Restricts a bounded formula to only use a particular set of free variables. -/
def restrictFreeVar {β : Sorts → Type _} [DecidableEq Sorts] [∀ s, DecidableEq (α s)] :
    ∀ {σ : Signature Sorts} (φ : L.BoundedFormula α σ)
    (_f : φ.freeVarType →ₛ β), L.BoundedFormula β σ
  | _, falsum, _ => falsum
  | _, equal t₁ t₂, f =>
    equal (t₁.restrictVarLeft (fun {t} => fun x => f t ⟨x.1, Finset.mem_union.mpr (Or.inl x.2)⟩))
          (t₂.restrictVarLeft (fun {t} => fun x => f t ⟨x.1, Finset.mem_union.mpr (Or.inr x.2)⟩))
  | _, rel R ts, f => rel R (ts.restrictVarLeft (fun {t} => f t))
  | _, imp φ₁ φ₂, f => by
    exact
      (φ₁.restrictFreeVar (fun {t} => fun x => f t  ⟨x.1, Finset.mem_union.mpr (Or.inl x.2)⟩)).imp
      (φ₂.restrictFreeVar (fun {t} => fun x => f t  ⟨x.1, Finset.mem_union.mpr (Or.inr x.2)⟩))
  | _, all _ φ, f => (φ.restrictFreeVar f).all

/-! ### Mapping Operations -/

/-- Maps bounded formulas along a map of terms and a map of relations.
  TODO: This lemma is currently more restrictive than its one-sorted cousin,
  as it assumes that arity of formulas is preserved and sorts are literally the same
  on both sides -/
def mapTermRel {β : Sorts → Type _} {g : Signature Sorts → Signature Sorts}
    (ft : ∀ σ ξ : Signature Sorts, L.Term (α ⊕ₛ σ.Idx) ξ →  L'.Term (β ⊕ₛ (g σ).Idx) ξ)
    (fr : ∀ σ, L.Relations σ → L'.Relations σ)
    (h : ∀ σ τ, L'.BoundedFormula β (g (σ ⨯ τ)) → L'.BoundedFormula β ((g σ) ⨯ τ)) :
    ∀ {σ}, L.BoundedFormula α σ → L'.BoundedFormula β (g σ)
  | _σ, falsum => falsum
  | _σ, equal t₁ t₂ => equal (ft _ _ t₁) (ft _ _ t₂)
  | _σ, rel R ts => rel (fr _ R) (ft _ _ ts)
  | _σ, imp φ₁ φ₂ => (φ₁.mapTermRel ft fr h).imp (φ₂.mapTermRel ft fr h)
  | _σ, all ξ φ => (h _ _ (φ.mapTermRel ft fr h)).all ξ

@[simp]
theorem mapTermRel_mapTermRel {β : Sorts → Type _} {L'' : MSLanguage Sorts}
    (ft : ∀ (σ τ : Signature Sorts), L.Term (α ⊕ₛ σ.Idx) τ → L'.Term (β ⊕ₛ σ.Idx) τ)
    (fr : ∀ σ, L.Relations σ → L'.Relations σ)
    (ft' : ∀ (σ τ : Signature Sorts), L'.Term (β ⊕ₛ σ.Idx) τ → L''.Term (γ ⊕ₛ σ.Idx) τ)
    (fr' : ∀ σ, L'.Relations σ → L''.Relations σ) {σ} (φ : L.BoundedFormula α σ) :
    ((φ.mapTermRel ft fr fun _ _ => id).mapTermRel ft' fr' fun _ _ => id) =
    φ.mapTermRel (fun _ _ => ft' _ _ ∘ ft _ _) (fun _ => fr' _ ∘ fr _ ) (fun _ _ => id)
      := by
  induction φ with
  | falsum => rfl
  | equal => simp only [mapTermRel, Function.comp_apply]
  | rel => simp only [mapTermRel, Function.comp_apply]
  | imp _ _ ih1 ih2 => simp only [mapTermRel, ih1, ih2]
  | all _ _ ih3 => simp only [mapTermRel, id_eq, ih3]

@[simp]
theorem mapTermRel_id_id_id {σ} (φ : L.BoundedFormula α σ) :
    (φ.mapTermRel (fun _ _ => id) (fun _ => id) fun _ _=> id) = φ := by
  induction φ with
  | falsum => rfl
  | equal => simp only [mapTermRel, id_eq]
  | rel => simp only [mapTermRel, id_eq]
  | imp _ _ ih1 ih2 => simp only [mapTermRel, ih1, ih2]
  | all _ _ ih3 => simp only [mapTermRel, ih3, id_eq]

/-- An equivalence of bounded formulas given by an equivalence of terms and an equivalence of
relations. -/
@[simps!]
def mapTermRelEquiv
    {β : Sorts → Type*}
    (ft : ∀ (σ τ : Signature Sorts),
      L.Term (α ⊕ₛ σ.Idx) τ ≃ L'.Term (β ⊕ₛ σ.Idx) τ)
    (fr : ∀ σ, L.Relations σ ≃ L'.Relations σ) {σ} :
    L.BoundedFormula α σ ≃ L'.BoundedFormula β σ :=
  ⟨
    mapTermRel (fun σ τ => ft σ τ) (fun σ => fr σ) fun _ _ => id,
    mapTermRel (fun σ τ => (ft σ τ).symm) (fun σ => (fr σ).symm) fun _ _ => id,
    fun φ => by simp,
    fun φ => by simp
  ⟩


/-! ### Variable Renaming -/

variable {β : Sorts → Type*}

/--
Renames the named free variables in a bounded formula.
-/
def rename (f : α →ₛ β) :
    L.BoundedFormula α σ → L.BoundedFormula β σ :=
  mapTermRel
    -- Apply Term.rename (formerly relabel_left) to terms
    (fun _ _ t => t.rename f)
    -- Relations stay the same
    (fun _ R => R)
    -- Quantifiers are the same as before
    (fun _ _ φ => φ)

@[simp]
lemma rename_rel {β : Sorts → Type _} {η : Signature Sorts}
    {g : α →ₛ β}
    {r : L.Relations σ}
    {t : L.Term (α ⊕ₛ η.Idx) σ} :
    (rel r t).rename g = rel r (Term.rename g t) := by
    rfl

@[simp]
lemma rename_equal {β : Sorts → Type _} {η : Signature Sorts}
    {g : α →ₛ β}
    {t₁ t₂ : L.Term (α ⊕ₛ η.Idx) σ} :
    (equal t₁ t₂).rename g = equal (t₁.rename g) (t₂.rename g) := by
    rfl

/-- Renaming with Id is the identity map. -/
@[simp]
theorem rename_id (φ : BoundedFormula L α σ) :
    φ.rename (Fam.id α) = φ := by
  induction φ <;> simp_all only [rename, mapTermRel, Term.rename, Term.mapVars, Fam.id,
    Sum.map_id_id, id_eq, Term.bind_var]

/-- Iterating rename. -/
@[simp]
theorem rename_rename (φ : BoundedFormula L α σ) (f : α →ₛ β) (g : β →ₛ γ) :
    (φ.rename f).rename g = φ.rename (g ∘ₛ f) := by
  induction φ <;> simp_all only [rename, mapTermRel, Term.rename_rename]

@[simp]
lemma reindex_rename {τ : Signature Sorts}
    (g : SigMap σ τ)
    (φ : L.BoundedFormula α σ)
    (f : α →ₛ β) :
    (φ.rename f).reindex g = (φ.reindex g).rename f := by
  induction φ generalizing τ with
  | falsum =>
      simp only [rename, mapTermRel, reindex]
  | equal t₁ t₂ =>
      simp only [rename, mapTermRel, reindex, Term.reindex_rename]
  | rel R ts =>
      simp only [rename, mapTermRel, reindex, Term.reindex_rename]
  | imp φ₁ φ₂ ih₁ ih₂ =>
      simp only [rename, mapTermRel, reindex, imp.injEq]
      apply And.intro
      · apply @ih₁
      · apply @ih₂
  | all η φ ih =>
      simpa [BoundedFormula.rename, BoundedFormula.reindex, BoundedFormula.mapTermRel] using
        congrArg (fun x => (BoundedFormula.all η x)) (ih (g.extend_right))

/-! ### Substitution -/

/--
Substitutes the free variables in a given formula with terms.

Note: `f` provides terms that may contain bound variables from `σ`.
This gives an avenue to passing named variables across to indexed
variables in a bounded formula, namely by having `f` map some `α s`
names to terms of the form `Term.var (Sum.inl v)` where `v : σ.Idx s`.
-/
def subst {σ : Signature Sorts}
    (φ : L.BoundedFormula α σ)
    (f : α →ₛ L.Term₁ (β ⊕ₛ σ.Idx)) :
    L.BoundedFormula β σ :=
  match φ with
  | falsum => falsum
  | equal t₁ t₂ =>
      equal (t₁.subst f) (t₂.subst f)
  | rel R ts =>
      rel R (ts.subst f)
  | imp φ₁ φ₂ =>
      (φ₁.subst f).imp (φ₂.subst f)
  | all τ φ =>
      let f' : α →ₛ L.Term₁ (β ⊕ₛ (σ ⨯ τ).Idx) :=
        fun s a => (f s a).reindex SigMap.incl_left
      (φ.subst f').all

/-! ### Substitution Lemmas -/

open Term

/-- Substitutes the variables with terms given an assignment only on those variables
    occurring in the formula. -/
def substFreeVars [DecidableEq Sorts] [∀ s, DecidableEq (α s)]
    {σ : Signature Sorts}
    (φ : L.BoundedFormula α σ)
    (f : φ.freeVarType →ₛ L.Term₁ (β ⊕ₛ σ.Idx)) :
    L.BoundedFormula β σ :=
    (φ.restrictFreeVar (Fam.id φ.freeVarType)).subst f

@[simp]
theorem subst_falsum (f : α →ₛ L.Term₁ (β ⊕ₛ σ.Idx)) :
    (falsum : BoundedFormula L α σ).subst f = falsum := rfl

@[simp]
theorem subst_equal {τ : Signature Sorts} (t₁ t₂ : L.Term (α ⊕ₛ σ.Idx) τ)
    (f : α →ₛ L.Term₁ (β ⊕ₛ σ.Idx)) :
    (equal t₁ t₂).subst f = equal (t₁.subst f) (t₂.subst f) := rfl

@[simp]
theorem subst_rel {τ : Signature Sorts} (R : L.Relations τ) (ts : L.Term (α ⊕ₛ σ.Idx) τ)
    (f : α →ₛ L.Term₁ (β ⊕ₛ σ.Idx)) :
    (rel R ts).subst f = rel R (ts.subst f) := rfl

@[simp]
theorem subst_imp (φ₁ φ₂ : BoundedFormula L α σ)
    (f : α →ₛ L.Term₁ (β ⊕ₛ σ.Idx)) :
    (φ₁.imp φ₂).subst f = (φ₁.subst f).imp (φ₂.subst f) := rfl

@[simp]
theorem subst_not (φ : BoundedFormula L α σ)
    (f : α →ₛ L.Term₁ (β ⊕ₛ σ.Idx)) :
    (φ.not).subst f = (φ.subst f).not := rfl

/--
Push substitution through the universal quantifier.
Note: The substitution function `f` must be reindexed to account for the new bound variables in `τ`.
-/
@[simp]
theorem subst_all (τ : Signature Sorts) (φ : BoundedFormula L α (σ ⨯ τ))
    (f : α →ₛ L.Term₁ (β ⊕ₛ σ.Idx)) :
    (φ.all).subst f = (φ.subst (fun s a => (f s a).reindex SigMap.incl_left)).all := rfl

-- Derived Connectives (And, Or, Ex, Iff)

@[simp]
theorem subst_or (φ ψ : BoundedFormula L α σ) (f : α →ₛ L.Term₁ (β ⊕ₛ σ.Idx)) :
    (φ.or ψ).subst f = (φ.subst f).or (ψ.subst f) := by
  simp only [BoundedFormula.or, subst_imp, subst_not]

@[simp]
theorem subst_and (φ ψ : BoundedFormula L α σ) (f : α →ₛ L.Term₁ (β ⊕ₛ σ.Idx)) :
    (φ.and ψ).subst f = (φ.subst f).and (ψ.subst f) := by
  simp only [BoundedFormula.and, subst_not, subst_or]

@[simp]
theorem subst_iff (φ ψ : BoundedFormula L α σ) (f : α →ₛ L.Term₁ (β ⊕ₛ σ.Idx)) :
    (φ.iff ψ).subst f = (φ.subst f).iff (ψ.subst f) := by
  simp only [BoundedFormula.iff]
  rfl

@[simp]
theorem subst_ex (τ : Signature Sorts) (φ : BoundedFormula L α (σ ⨯ τ))
    (f : α →ₛ L.Term₁ (β ⊕ₛ σ.Idx)) :
    (φ.ex).subst f = (φ.subst (fun s a => (f s a).reindex SigMap.incl_left)).ex := by
  -- `ex` is defined as `(all not).not`
  simp only [BoundedFormula.ex, subst_not, subst_all]

/-! ### Reindex Interaction Lemmas -/

@[simp]
theorem reindex_not (φ : BoundedFormula L α σ) (g : SigMap σ τ) :
    (φ.not).reindex g = (φ.reindex g).not := by
  simp only [reindex, BoundedFormula.not, imp.injEq, true_and]
  rfl

@[simp]
theorem reindex_or (φ ψ : BoundedFormula L α σ) (g : SigMap σ τ) :
    (φ.or ψ).reindex g = (φ.reindex g).or (ψ.reindex g) := by
  simp only [reindex, BoundedFormula.or, imp.injEq, and_true]
  rfl
@[simp]
theorem reindex_and (φ ψ : BoundedFormula L α σ) (g : SigMap σ τ) :
    (φ.and ψ).reindex g = (φ.reindex g).and (ψ.reindex g) := by
  simp only [reindex, BoundedFormula.and]
  rfl

@[simp]
theorem reindex_iff (φ ψ : BoundedFormula L α σ) (g : SigMap σ τ) :
    (φ.iff ψ).reindex g = (φ.reindex g).iff (ψ.reindex g) := by
  simp only [BoundedFormula.iff, reindex]
  rfl

@[simp]
theorem reindex_ex (ξ : Signature Sorts) (φ : BoundedFormula L α (σ ⨯ ξ)) (g : SigMap σ τ) :
    (φ.ex).reindex g = (φ.reindex (g.extend_right)).ex := by
  simp only [reindex, BoundedFormula.ex]
  rfl

/-! ### Relabeling -/

/--
Redefines the old `relabel` with new API:
1. Widens `σ` to `τ ⨯ σ` in `φ` with `reindex` and the mapping `σ → τ ⨯ σ`
2. Substitutes the original free variable names `α` into `β ⊕ τ`.
-/
def relabel {β : Sorts → Type _} {τ : Signature Sorts}
    (g : α →ₛ β ⊕ₛ τ.Idx)
    (φ : L.BoundedFormula α σ) :
    L.BoundedFormula β (τ ⨯ σ) :=
  ((φ.reindex
      SigMap.incl_right --pushes the `σ`-variables of `φ` rightward
    ).rename g -- relabels the `α`-variables by `g` to be `β ⊕ₛ τ.Idx` ones.
   ).subst
      (Fam.sumElim
        (varOf Fam.inl) --leaves the `β`-variables alone
        (fun s v => Term.var s (Sum.inr (.left v))) --pushes the `τ`-vars to the indexed product
      )


--TODO: resolve Equiv namespace conflicts between MSLanguage and _root_
--because at present we have to write _root_.Equiv to refer to regular Equiv namespace.
def relabelEquiv (e : α ≃ₛ β) {σ : Signature Sorts} :
    L.BoundedFormula α σ ≃ L.BoundedFormula β σ :=
  mapTermRelEquiv
    (fun σ _ =>
      Term.mapVarsEquiv (α := α ⊕ₛ σ.Idx) (β := β ⊕ₛ σ.Idx)
        (MSEquiv.sumCongr e MSEquiv.refl))
    (fun _ => _root_.Equiv.refl (L.Relations _))

  /-
  (ft :=
      fun σ _ =>
        Term.mapVarsEquiv (α := α ⊕ₛ σ.Idx) (β := β ⊕ₛ σ.Idx)
          (MSEquiv.sumCongr e MSEquiv.refl)
  )
  (fr := fun _σ => _root_.Equiv.refl _)
  -/
@[simp]
theorem relabel_falsum {β : Sorts → Type _} {τ : Signature Sorts}
    {g : α →ₛ β ⊕ₛ τ.Idx} {σ : Signature Sorts} :
    (falsum : L.BoundedFormula α σ).relabel (τ := τ) g = falsum :=
  rfl

@[simp]
theorem relabel_bot {β : Sorts → Type _} {τ : Signature Sorts}
    {g : α →ₛ β ⊕ₛ τ.Idx} {σ : Signature Sorts} :
    (⊥ : L.BoundedFormula α σ).relabel (τ := τ) g = ⊥ :=
  rfl

@[simp]
theorem relabel_imp {β : Sorts → Type _} {τ : Signature Sorts}
    {g : α →ₛ β ⊕ₛ τ.Idx} {σ : Signature Sorts} (φ ψ : L.BoundedFormula α σ) :
    (φ.imp ψ).relabel (τ := τ) g =
      (φ.relabel (τ := τ) g).imp (ψ.relabel (τ := τ) g) :=
  rfl

@[simp]
theorem relabel_not {β : Sorts → Type _} {τ : Signature Sorts}
    {g : α →ₛ β ⊕ₛ τ.Idx} {σ : Signature Sorts} (φ : L.BoundedFormula α σ) :
    (φ.not).relabel (τ := τ) g =
      (φ.relabel (τ := τ) g).not := by
  simp only [BoundedFormula.not, relabel_imp, relabel_bot]

/--
Commutation of reindexing and substitution.
Reindexing a formula by `g` and then substituting is the same as
substituting first (with reindexed terms) and then reindexing the result.
-/
@[simp]
lemma reindex_subst {β : Sorts → Type _} {σ τ : Signature Sorts}
    (g : SigMap σ τ)
    (φ : L.BoundedFormula α σ)
    (f : α →ₛ L.Term₁ (β ⊕ₛ σ.Idx)) :
    (φ.subst f).reindex g =
    (φ.reindex g).subst (fun s a => (f s a).reindex g) := by
  induction φ generalizing τ with
  | falsum => simp only [subst, reindex, subst_falsum]
  | equal t₁ t₂ =>
      simp only [subst, reindex, Term.reindex_subst]
  | rel R ts =>
      simp only [subst, reindex, Term.reindex_subst]
  | imp φ₁ φ₂ ih₁ ih₂ =>
      simp only [subst, reindex, ih₁, ih₂, subst_imp]
  | all η φ ih =>
      simp only [subst, reindex]
      rw [ih (g.extend_right)]
      congr
      funext s a
      simp_all  [Term.reindex_reindex]
      rfl

/--
This lemma is only true up to associativity, so we have to apply prodAssocR to generalize it.
-/
@[simp]
theorem relabel_all {β : Sorts → Type _}
    (τ : Signature Sorts) (g : α →ₛ (β ⊕ₛ τ.Idx))
    {σ ξ : Signature Sorts}
    (φ : L.BoundedFormula α (σ ⨯ ξ)) :
    (φ.all).relabel g =
      ((φ.relabel g).reindex (SigMap.assocR τ σ ξ )).all
:= by
  unfold BoundedFormula.relabel
  simp only [BoundedFormula.reindex, reindex_subst]
  -- incl_right for inner formula: SigMap (σ ⨯ ξ) (τ ⨯ (σ ⨯ ξ))
  -- assocR τ σ ξ : SigMap (τ ⨯ (σ ⨯ ξ)) ((τ ⨯ σ) ⨯ ξ)
  -- incl_right.extend_right for outer: SigMap (σ ⨯ ξ) ((τ ⨯ σ) ⨯ ξ)
  have hreindex : (fun t => SigMap.assocR τ σ ξ t ∘ SigMap.incl_right (σ := σ ⨯ ξ) (τ := τ) t) =
      (SigMap.incl_right (σ := σ) (τ := τ)).extend_right (η := ξ) := by
    funext t v
    cases v with
    | left w => rfl
    | right w => rfl
  rw [reindex_rename (τ := (τ ⨯ σ) ⨯ ξ), reindex_reindex, hreindex]
  simp only [rename, mapTermRel, subst_all]
  congr 2
  ext x y : 2
  cases y with
  | inl val =>
    simp_all only [Sum.elim_inl]
    rfl
  | inr val_1 =>
    simp_all only [Sum.elim_inr, reindex_var_inr, var.injEq, Sum.inr.injEq]
    rfl


syntax "reduce_formula" : tactic

macro_rules
  | `(tactic| reduce_formula) =>
      `(tactic|
        simp (config := { zeta := true }) only [
          MSFirstOrder.MSLanguage.BoundedFormula.rename,
          MSFirstOrder.MSLanguage.BoundedFormula.relabel,
          MSFirstOrder.MSLanguage.BoundedFormula.subst,
          MSFirstOrder.MSLanguage.BoundedFormula.reindex,
          MSFirstOrder.MSLanguage.BoundedFormula.mapTermRel_id_id_id
        ];
        repeat simp only [MSFirstOrder.MSLanguage.BoundedFormula.mapTermRel_mapTermRel]
      )

/-! ### Block Swapping for Variable Rearrangement -/

/--
Swaps the middle and right blocks in a three-way product: `(σ·τ)·η ≃ (σ·η)·τ`.

This equivalence rearranges bound variables by swapping the positions of `τ` and `η`
while keeping `σ` fixed in the leftmost position. Implemented as a composition of
associativity and commutativity transformations:
1. Reassociate: `((σ·τ)·η) ≃ (σ·(τ·η))`
2. Swap right pair: `(σ·(τ·η)) ≃ (σ·(η·τ))`
3. Reassociate back: `(σ·(η·τ)) ≃ ((σ·η)·τ)`

⨯⨯Use case⨯⨯: Variable rearrangement during quantifier manipulation, particularly when
reordering nested quantifiers or when preparing formulas for normal forms.
-/
def block_swap {σ τ η : Signature Sorts} :
  SigEquiv ((σ ⨯ τ) ⨯ η) ((σ ⨯ η) ⨯ τ) :=
          SigEquiv.trans
            (SigEquiv.trans
              (SigEquiv.assocL σ τ η) -- ((σ ⨯ τ) ⨯ η) ≃ (σ ⨯ (τ ⨯ η))
              (SigEquiv.prod_congr SigEquiv.Id SigEquiv.comm) -- (σ ⨯ (τ ⨯ η)) ≃  (σ ⨯ (η ⨯ τ))
            )
            (SigEquiv.assocR σ η τ)

@[simp] lemma block_swap_left_left {σ τ η : Signature Sorts} {s : Sorts}
    (v : σ.Idx s) :
    block_swap (σ := σ) (τ := τ) (η := η) s (.left (.left v)) = (.left (.left v)) := by
  rfl

@[simp] lemma block_swap_left_right {σ τ η : Signature Sorts} {s : Sorts}
    (v : τ.Idx s) :
    block_swap (σ := σ) (τ := τ) (η := η) s (.left (.right v)) = (.right v) := by
  rfl

@[simp] lemma block_swap_right {σ τ η : Signature Sorts} {s : Sorts}
    (v : η.Idx s) :
    block_swap (σ := σ) (τ := τ) (η := η) s (.right v) = (.left (.right v)) := by
  rfl

@[simp] lemma block_swap_symm_left_left {σ τ η : Signature Sorts} {s : Sorts}
    (v : σ.Idx s) :
    (block_swap (σ := σ) (τ := τ) (η := η)).symm s (.left (.left v)) = (.left (.left v)) := by
  rfl

@[simp] lemma block_swap_symm_right {σ τ η : Signature Sorts} {s : Sorts}
    (v : τ.Idx s) :
    (block_swap (σ := σ) (τ := τ) (η := η)).symm s (.right v) = (.left (.right v)) := by
  rfl

@[simp] lemma block_swap_symm_left_right {σ τ η : Signature Sorts} {s : Sorts}
    (v : η.Idx s) :
    (block_swap (σ := σ) (τ := τ) (η := η)).symm s (.left (.right v)) = (.right v) := by
  rfl

@[simp] lemma block_swap_block_swap {σ τ η : Signature Sorts} {s : Sorts}
    (x : ((σ ⨯ τ) ⨯ η).Idx s) :
    block_swap (σ := σ) (τ := η) (η := τ) s (block_swap (σ := σ) (τ := τ) (η := η) s x) = x := by
  cases x with
  | left x =>
      cases x with
      | left v  => simp
      | right v => simp
  | right v =>
      simp

/-! ### Opening and Closing Variables -/

/--
Opens bound variables in a formula by splitting the rightmost block of quantified variables.

Transforms a bounded formula `L.BoundedFormula α (σ ⨯ τ)` into
`L.BoundedFormula (α ⊕ₛ τ.Idx) σ` by converting the `τ` block of bound variables into free
variables. This is the formula-level equivalent of `Term.openVars`.

⨯⨯Transformation:⨯⨯
- Free variables `α` remain free
- Bound variables from `τ` (rightmost block) become free variables: `α ⊕ₛ τ.Idx`
- Bound variables from `σ` (leftmost block) remain bound

⨯⨯Use case⨯⨯: Opening quantifiers for substitution. For example, to substitute into
`∀ x ∀ y. φ(x,y)`,
first open the `y` quantifier to get `∀ x. φ(x, y_free)`, then substitute for `y_free`.

This operation is inverted by `closeVars` or `instantiate`.
-/
def openVars {σ τ : Signature Sorts} :
    L.BoundedFormula α (σ ⨯ τ) → L.BoundedFormula (α ⊕ₛ τ.Idx) σ
  | .falsum => .falsum
  | .imp φ₁ φ₂ => .imp (openVars φ₁) (openVars φ₂)
  | .equal t₁ t₂ => .equal t₁.openVars t₂.openVars
  | .rel R ts => .rel R ts.openVars
  | .all η φ =>
      let φ' := (φ.reindex block_swap).openVars
      φ'.all η
termination_by
  φ => φ.size

/-- Inverse for openVars along a map from a right free variable factor back to Idxs. -/
def closeVars {σ τ : Signature Sorts} {X : Sorts → Type*}
  (f : X →ₛ τ.Idx) :
  L.BoundedFormula (α ⊕ₛ X) σ → L.BoundedFormula α (σ ⨯ τ)
| φ =>
    let g : (α ⊕ₛ X) →ₛ (α ⊕ₛ τ.Idx) :=
      Fam.sumElim (fun _ a => Sum.inl a) (fun s x => Sum.inr (f s x))
    (φ.relabel g).reindex SigEquiv.comm

@[simp]
lemma closeVars_falsum {σ τ : Signature Sorts} {X : Sorts → Type*} (f : X →ₛ τ.Idx) :
  (falsum : L.BoundedFormula (α ⊕ₛ X) σ).closeVars f = falsum := by
  simp only [closeVars, relabel_falsum, reindex]

@[simp]
lemma closeVars_imp {σ τ : Signature Sorts} {X : Sorts → Type*} (f : X →ₛ τ.Idx)
    {φ₁ φ₂ : L.BoundedFormula (α ⊕ₛ X) σ} :
  (φ₁.imp φ₂).closeVars f = (φ₁.closeVars f).imp (φ₂.closeVars f) := by
  simp only [closeVars, relabel_imp, reindex]

@[simp]
lemma closeVars_all {σ τ η : Signature Sorts} {X : Sorts → Type*} (f : X →ₛ τ.Idx)
    {φ : L.BoundedFormula (α ⊕ₛ X) (σ ⨯ η)} :
  (φ.all).closeVars f = ((φ.closeVars f).reindex block_swap).all η := by
  simp only [closeVars, relabel_all, reindex, reindex_reindex, all.injEq, heq_eq_eq, true_and]
  congr
  ext s a
  match a with
  | .left v => simp_all only [Function.comp_apply, extend_right]; rfl
  | .right v =>
    match v with
    | .left w => simp_all only [Function.comp_apply, extend_right]; rfl
    | .right w => simp_all only [Function.comp_apply, extend_right]; rfl

def inductionOn_size {τ : Signature Sorts}
    {C : ∀ {α : Sorts → Type u'} {σ τ : Signature Sorts},
        L.BoundedFormula α (σ ⨯ τ) → Prop}
    {α_inner : Sorts → Type u'} {σ_inner : Signature Sorts}
    (φ : L.BoundedFormula α_inner (σ_inner ⨯ τ))
    (h :
      ∀ {α τ} {σ : Signature Sorts} (φ : L.BoundedFormula α (σ ⨯ τ)),
        (∀ {α'} {σ' τ' : Signature Sorts} (ψ : L.BoundedFormula α' (σ' ⨯ τ')),
          ψ.size < φ.size → C ψ) → C φ) :
    C φ :=
  h φ (fun {α' σ' τ'} ψ _ => inductionOn_size ψ h)
termination_by φ.size


lemma openVars_closeVars {σ τ : Signature Sorts} (φ : L.BoundedFormula α (σ ⨯ τ)) :
  φ.openVars.closeVars (Fam.id τ.Idx) = φ := by
  -- generalizing α is crucial here because the recursive step changes the type of α
  apply inductionOn_size φ
  intro α σ τ φ ih
  cases φ with
  | falsum =>
      simp_all only [closeVars, openVars, size, Nat.lt_one_iff, famId]
      rfl
  | imp φ₁ φ₂ =>
    have h₁ := ih φ₁ (by simp only [size]; linarith)
    have h₂ := ih φ₂ (by
      simp only [size, lt_add_iff_pos_left, add_pos_iff, _root_.zero_lt_one, true_or])
    simp only [openVars, closeVars_imp, h₁, h₂]
  | equal t₁ t₂ =>
    simp only [closeVars, relabel, rename, Fam.id, id_eq, openVars, reindex, mapTermRel,
      subst_equal, rename_subst, Sum.elim_inl_inr, equal.injEq, heq_eq_eq, true_and]
    simp only [Term.reindex, Term.subst, Term.openVars, Term.bind_bind, mapVars]
    constructor <;>
      { apply Term.bind_id _
        intro s a;
        simp_all only [size, Nat.lt_one_iff, famId];
        cases a with
        | inl val =>
          simp_all only [Sum.elim_inl]
          rfl
        | inr val_1 =>
          simp_all only [Sum.elim_inr]
          split
          next v w =>
            simp_all only [Term.bind, Sum.map_inr, Sum.elim_inr]
            rfl
          next v
            w =>
            simp_all only [Term.bind, Sum.map_inl, id_eq, Sum.elim_inl, Sum.elim_inr, Sum.map_inr,
              var.injEq, Sum.inr.injEq]
            rfl}
  | rel R ts =>
    simp only [closeVars, relabel, Fam.id, id_eq, openVars, reindex, rename_rel, subst_rel,
      rename_subst, Sum.elim_inl_inr, rel.injEq, heq_eq_eq, true_and]
    reduce_term_to_bind
    apply Term.bind_id
    intro s a
    unfold varOf
    cases a
    · reduce_term_to_bind ; rfl
    · simp only [Function.comp_apply, Sum.elim_inr]
      split <;> reduce_term_to_bind <;> rfl
  | all η φ =>
    rw [openVars]
    simp only [famId, closeVars_all, all.injEq, heq_eq_eq, true_and]
    have ih' := ih (reindex block_swap.toFun φ) (by simp)
    change
      reindex block_swap.toFun
          (closeVars (Fam.id σ.Idx) (reindex block_swap.toFun φ).openVars) = φ
    rw[ih', reindex_reindex]
    let F : (t : Sorts) → ((τ ⨯ σ) ⨯ η).Idx t → ((τ ⨯ σ) ⨯ η).Idx t :=
      fun t ↦ block_swap.toFun t ∘ block_swap.toFun t
    have F_id : F = SigMap.Id := by
      ext t a; simp only [Function.comp_apply, block_swap_block_swap, Id_apply, F]
    change reindex F φ = φ
    rw [F_id]; simp only [reindex_id]

/--
General version: `closeVars` followed by `openVars` is syntactically just renaming the free
variables `α ⊕ₛ X` into `α ⊕ₛ τ.Idx` by sending `X` along `f`.

This is the main rewriting lemma used to prove `realize_closeVars` cleanly.
-/
lemma closeVars_openVars {σ τ : Signature Sorts} {X : Sorts → Type*}
    (f : X →ₛ τ.Idx)
    (φ : L.BoundedFormula (α ⊕ₛ X) σ) :
    (φ.closeVars (α := α) (σ := σ) (τ := τ) f).openVars
      =
    φ.rename (Fam.sumElim (fun _ a => Sum.inl a) (fun s x => Sum.inr (f s x))) := by
  induction φ with
  | falsum =>
      simp only [closeVars_falsum, openVars, rename, mapTermRel]
  | imp φ₁ φ₂ ih₁ ih₂ =>
      simp only [closeVars_imp, openVars]
      rw [ih₁, ih₂]
      simp only [rename, mapTermRel]
  | @equal σ₀ ξ t₁ t₂ =>
      unfold closeVars openVars
      reduce_formula
      simp only [mapTermRel, subst_equal, reindex, equal.injEq, heq_eq_eq,
        true_and]
      reduce_term_to_bind
      constructor <;>
      { congr 2
        ext x y
        cases y
        · case inl w =>
          cases w
          · simp_all only [Sum.map_inl, Sum.elim_inl]; rfl
          · simp_all only [Sum.map_inl, Sum.elim_inr, Sum.elim_inl, Term.bind]; rfl
        · case inr =>
        simp_all only [Term.bind, Sum.map_inr, id_eq, Sum.elim_inr]
        rfl;
      }
  | @rel σ' τ' R ts =>
      simp only [closeVars, relabel, rename, reindex, mapTermRel, subst_rel, rename_subst, openVars,
        rel.injEq, heq_eq_eq, true_and]
      reduce_term_to_bind
      congr 2
      ext x y : 2
      cases y with
      | inl v =>
        cases v with
        | inl w => simp_all only [Sum.map_inl, id_eq, Sum.elim_inl]; rfl
        | inr w =>
          simp_all only [Sum.map_inl, id_eq, Sum.elim_inl, Sum.elim_inr, Term.bind, Sum.map_inr]
          rfl
      | inr v =>
        simp_all only [Sum.map_inr, id_eq]; rfl
  | all η ψ ih =>
    simp only [closeVars, relabel_all, reindex, reindex_reindex] at *
    simp only [rename, openVars, reindex_reindex, mapTermRel, all.injEq, heq_eq_eq, true_and] at *
    rw[← ih]
    congr
    ext s x; cases x
    case left v => simp_all only [Function.comp_apply, extend_right]; rfl
    case right v => cases v <;> simp_all only [Function.comp_apply, extend_right] <;> rfl

@[simp]
lemma closeVars_openVars_id {σ τ : Signature Sorts}
    (φ : L.BoundedFormula (α ⊕ₛ τ.Idx) σ) :
    (φ.closeVars (α := α) (σ := σ) (τ := τ) (Fam.id τ.Idx)).openVars
      =
    φ := by
  rw [closeVars_openVars (f := Fam.id τ.Idx)]
  have :
      (Fam.sumElim
          (fun _ (a : α _) => Sum.inl a)
          (fun s (x : τ.Idx s) => Sum.inr (Fam.id τ.Idx s x)) :
        (α ⊕ₛ τ.Idx) →ₛ (α ⊕ₛ τ.Idx)) = Fam.id (α ⊕ₛ τ.Idx) := by
    funext s x
    cases x with
    | inl a => rfl
    | inr x => rfl
  rw [this, rename_id]

/-! ### Instantiation and Witnesses -/

/--
Substitute a term `u` of shape `τ` into the `τ` variables of `φ`:
-/
def instantiate {σ τ : Signature Sorts} :
    L.BoundedFormula α (σ ⨯ τ)
    → L.Term (α ⊕ₛ σ.Idx) τ →
       L.BoundedFormula α σ :=
    fun φ t =>
      φ.openVars.subst (Fam.sumElim (varOf Fam.inl) (fun s a => t.getLeafTerm s a))

/--
An unqualified version of instantiate that completely eliminates all bound variables to
return a Formula.
-/
def fully_instantiate {τ : Signature Sorts} :
    L.BoundedFormula α τ
    → L.Term (α ⊕ₛ nil.Idx) τ →
       L.Formula α :=
    fun φ t =>
     (φ.reindex SigMap.nil_left_inv).instantiate t

def has_witness (T : L.Theory) (φ : L.BoundedFormula Fam.EmptyFam (of s)) : Prop :=
      ∃ c : L.Constants s,
        φ.fully_instantiate c.term ∈ T ↔ φ.exs ∈ T

/-! ### Constants and Variables Equivalence -/

section constants_vars_equiv

variable {γ : Sorts → Type u'}

/-- A bijection sending formulas with constants to formulas with extra variables. -/
def constantsVarsEquiv {σ : Signature Sorts} {γ : Sorts → Type*} :
    (L[[γ]]).BoundedFormula α σ ≃ L.BoundedFormula (γ ⊕ₛ α) σ :=
  BoundedFormula.mapTermRelEquiv
    (L := L[[γ]]) (L' := L)
    (α := α) (β := γ ⊕ₛ α)
    (ft := fun σ' _ => Term.constantsVarsEquivLeft (β := σ'.Idx))
    (fr := fun _ => Equiv.sumEmpty _ _)

end constants_vars_equiv

/-! ### Finite Meets and Joins -/

/-- Take the disjunction of a finite set of formulas.

Note that this is an arbitrary formula defined using the axiom of choice. It is only well-defined up
to equivalence of formulas. -/
noncomputable def iSup {X} [Finite X] (f : X → L.BoundedFormula α σ) : L.BoundedFormula α σ :=
  let _ := Fintype.ofFinite X
  ((Finset.univ : Finset X).toList.map f).foldr (· ⊔ ·) ⊥

/-- Take the conjunction of a finite set of formulas.

Note that this is an arbitrary formula defined using the axiom of choice. It is only well-defined up
to equivalence of formulas. -/
noncomputable def iInf {X} [Finite X] (f : X → L.BoundedFormula α σ) : L.BoundedFormula α σ :=
  let _ := Fintype.ofFinite X
  ((Finset.univ : Finset X).toList.map f).foldr (· ⊓ ·) ⊤

/--
Indexed AND `⋀ [φ₁, φ₂, ...]` from a list
-/
def bigAnd (l : List (L.BoundedFormula α σ)) : L.BoundedFormula α σ :=
  l.foldr (· ⊓ ·) ⊤

/--
Indexed OR `⋁ [φ₁, φ₂, ...]` from a list
-/
def bigOr (l : List (L.BoundedFormula α σ)) : L.BoundedFormula α σ :=
  l.foldr (· ⊔ ·) ⊥

-- Notation
prefix:110 "⋀ " => bigAnd
prefix:110 "⋁ " => bigOr

/-! ### Localization of Formulas -/

section localize_formula

variable [DecidableEq Sorts] [∀ s, DecidableEq (α s)]

/-- A localization of a bounded formula: a signature `τ` together with an equivalence
between the formula's free-variable family and `τ.Idx`. This packages the data needed
to replace named free variables with signature-indexed ones. -/
structure LocalForm {σ : Signature Sorts} (φ : L.BoundedFormula α σ) where
  τ : Signature Sorts
  e : φ.freeVarType ≃ₛ τ.Idx

namespace LocalForm

variable {σ : Signature Sorts} {φ : L.BoundedFormula α σ} (lf : φ.LocalForm)

/-- The localized bounded formula: free variables replaced by `τ.Idx`. -/
def toFormula : L.BoundedFormula lf.τ.Idx σ :=
  φ.restrictFreeVar lf.e

/-- The derived closed bounded formula: free variables become bound in signature `τ`.
    Only available when `σ = nil` (i.e. for `Formula`). -/
def toBoundedFormula {φ : L.Formula α} (lf : φ.LocalForm) : L.BoundedFormula Fam.EmptyFam lf.τ :=
  let φ_restricted : L.BoundedFormula φ.freeVarType Signature.nil :=
    φ.restrictFreeVar (fun _ x => x)
  let φ_renamed : L.BoundedFormula lf.τ.Idx Signature.nil :=
    φ_restricted.rename lf.e.toFun
  let φ_sum : L.BoundedFormula (Fam.EmptyFam ⊕ₛ lf.τ.Idx) Signature.nil :=
    φ_renamed.rename (fun _ => Sum.inr)
  (φ_sum.closeVars (Fam.id lf.τ.Idx)).reindex (SigEquiv.nilLeft lf.τ)

end LocalForm

/-- Canonical localization via `famToSignature`. -/
noncomputable def localize (φ : L.BoundedFormula α σ) : φ.LocalForm :=
  ⟨(Signature.famToSignature φ.freeVarType).1,
   (Signature.famToSignature φ.freeVarType).2⟩

/-- Manual localization from a user-supplied equivalence. -/
def localizeBy (φ : L.BoundedFormula α σ) (τ : Signature Sorts)
    (e : φ.freeVarType ≃ₛ τ.Idx) : φ.LocalForm :=
  ⟨τ, e⟩

end localize_formula

end BoundedFormula

namespace Formula

variable [DecidableEq Sorts] [∀ s, DecidableEq (α s)]

/-- A localization of a formula. Specializes `BoundedFormula.LocalForm` at `σ = nil`. -/
abbrev LocalForm (φ : L.Formula α) := BoundedFormula.LocalForm φ

/-- Canonical localization of a formula via `famToSignature`. -/
noncomputable abbrev localize (φ : L.Formula α) := BoundedFormula.localize φ

/-- Manual localization of a formula from a user-supplied equivalence. -/
abbrev localizeBy (φ : L.Formula α) := BoundedFormula.localizeBy φ

end Formula

/-! ## Language Homomorphisms and Equivalences -/

namespace LHom

open BoundedFormula

/-- Maps a bounded formula's symbols along a language map. -/
@[simp]
def onBoundedFormula (g : L →ᴸ L') :
    ∀ {ξ : Signature Sorts}, L.BoundedFormula α ξ → L'.BoundedFormula α ξ
  | _ξ, falsum => falsum
  | _ξ, BoundedFormula.equal t₁ t₂ => (g.onTerm t₁).bdEqual (g.onTerm t₂)
  | _ξ, rel R ts => (g.onRelation R).boundedFormula (g.onTerm ts)
  | _ξ, imp f₁ f₂ => (onBoundedFormula g f₁).imp (onBoundedFormula g f₂)
  | _ξ, all η f => all η (onBoundedFormula g f)

@[simp]
theorem id_onBoundedFormula :
    ((LHom.id L).onBoundedFormula : L.BoundedFormula α σ  → L.BoundedFormula α σ) = id := by
  ext f
  induction f with
  | falsum => rfl
  | equal => rw [onBoundedFormula, LHom.id_onTerm, id, id, id, Term.bdEqual]
  | rel => simp only [onBoundedFormula, LHom.id_onTerm,id_onRelation,
    id, Relations.boundedFormula]
  | imp _ _ ih1 ih2 => rw [onBoundedFormula, ih1, ih2, id, id, id]
  | all _ _ ih3 => rw [onBoundedFormula, ih3, id, id]

@[simp]
theorem comp_onBoundedFormula {L'' : MSLanguage Sorts} (φ : L' →ᴸ L'') (ψ : L →ᴸ L') :
    ((φ.comp ψ).onBoundedFormula : L.BoundedFormula α σ → L''.BoundedFormula α σ) =
      φ.onBoundedFormula ∘ ψ.onBoundedFormula := by
  ext f
  induction f with
  | falsum => rfl
  | equal => simp only [onBoundedFormula, Term.bdEqual, comp_onTerm, Function.comp_apply]
  | rel => simp only [onBoundedFormula, Relations.boundedFormula, comp_onRelation, comp_onTerm,
    Function.comp_apply]
  | imp _ _ ih1 ih2 =>
    simp only [onBoundedFormula, Function.comp_apply, ih1, ih2]
  | all _ _ ih3 => simp only [ih3, onBoundedFormula, Function.comp_apply]

/-- Maps a formula's symbols along a language map. -/
def onFormula (g : L →ᴸ L') : L.Formula α → L'.Formula α :=
  g.onBoundedFormula

/-- Maps a sentence's symbols along a language map. -/
def onSentence (g : L →ᴸ L') : L.Sentence → L'.Sentence :=
  g.onFormula

/-- Maps a theory's symbols along a language map. -/
def onTheory (g : L →ᴸ L') (T : L.Theory) : L'.Theory :=
  g.onSentence '' T

@[simp]
theorem mem_onTheory {g : L →ᴸ L'} {T : L.Theory} {φ : L'.Sentence} :
    φ ∈ g.onTheory T ↔ ∃ φ₀, φ₀ ∈ T ∧ g.onSentence φ₀ = φ :=
  Set.mem_image _ _ _

end LHom

namespace LEquiv

/-- Maps a bounded formula's symbols along a language equivalence. -/
@[simps]
def onBoundedFormula (φ : L ≃ᴸ L') : L.BoundedFormula α σ ≃ L'.BoundedFormula α σ where
  toFun := φ.toLHom.onBoundedFormula
  invFun := φ.invLHom.onBoundedFormula
  left_inv := by
    rw [Function.leftInverse_iff_comp, ← LHom.comp_onBoundedFormula, φ.left_inv,
      LHom.id_onBoundedFormula]
  right_inv := by
    rw [Function.rightInverse_iff_comp, ← LHom.comp_onBoundedFormula, φ.right_inv,
      LHom.id_onBoundedFormula]

theorem onBoundedFormula_symm (φ : L ≃ᴸ L') :
    (φ.onBoundedFormula.symm : L'.BoundedFormula α σ ≃ L.BoundedFormula α σ) =
      φ.symm.onBoundedFormula :=
  rfl

/-- Maps a formula's symbols along a language equivalence. -/
def onFormula (φ : L ≃ᴸ L') : L.BoundedFormula α σ ≃ L'.BoundedFormula α σ :=
  φ.onBoundedFormula

@[simp]
theorem onFormula_apply (φ : L ≃ᴸ L') :
    (φ.onFormula : L.Formula α → L'.Formula α) = φ.toLHom.onFormula :=
  rfl

@[simp]
theorem onFormula_symm (φ : L ≃ᴸ L') :
    (φ.onFormula.symm : L'.BoundedFormula α σ ≃ L.BoundedFormula α σ) = φ.symm.onFormula :=
  rfl

/-- Maps a sentence's symbols along a language equivalence. -/
@[simps!]
def onSentence (φ : L ≃ᴸ L') : L.Sentence ≃ L'.Sentence :=
  φ.onFormula

end LEquiv

@[inherit_doc] scoped[MSFirstOrder] infixl:88 " =' " => MSFirstOrder.MSLanguage.Term.bdEqual
-- input \~- or \simeq

@[inherit_doc] scoped[MSFirstOrder] infixr:62 " ⟹ " => MSFirstOrder.MSLanguage.BoundedFormula.imp
-- input \==>

--@[inherit_doc] scoped[MSFirstOrder] prefix:110 "∀'" => MSFirstOrder.MSLanguage.BoundedFormula.all
-- input \forall'

/-! ## Notation -/

variable (l : List ℕ)

@[inherit_doc] scoped[MSFirstOrder] prefix:arg "∼" => MSFirstOrder.MSLanguage.BoundedFormula.not
-- input \~, the ASCII character ~ has too low precedence

@[inherit_doc] scoped[MSFirstOrder] infixl:61 " ⇔ " => MSFirstOrder.MSLanguage.BoundedFormula.iff
-- input \<=>

--@[inherit_doc] scoped[MSFirstOrder] prefix:110 "∃'" => MSFirstOrder.MSLanguage.BoundedFormula.ex
-- input \ex'

/-! ## Formula Operations -/

namespace Formula

/-- Relabels a formula's variables along a particular function.
    Much simpler to define via `BoundedFormula.rename` rather than
    the previous one with `relabel`.
-/
def rename {β : Sorts → Type _} (g : α →ₛ β) : L.Formula α → L.Formula β :=
  BoundedFormula.rename g

/-- The graph of a function as a first-order formula. -/
def graph (f : L.Functions σ s) : L.Formula (σ ⨯ ⦃s⦄).Idx :=
  Term.equal (.var s (.right .var)) (.func f ((Term.varTerm σ).mapVars (fun _ v => .left v)))

/-- The negation of a formula. -/
protected nonrec abbrev not (φ : L.Formula α) : L.Formula α :=
  φ.not

/-- The implication between formulas, as a formula. -/
protected abbrev imp : L.Formula α → L.Formula α → L.Formula α :=
  BoundedFormula.imp

open Signature Term

/-! ### Indexed Quantification over Free Variables -/

section free_var_quantification

variable (β) in
/-- `iAlls φ` turns `L.Formula (α ⊕ₛ X)` into `L.Formula α`
by universally quantifying all `Sum.inr _` variables. -/
noncomputable def iAlls [Finite (Sigma β)]
    (φ : L.Formula (α ⊕ₛ β)) : L.Formula α :=
by
  rcases famToSignature β with ⟨σ, e⟩
  exact
    (φ.relabel
        (fun s a => Sum.map id (e s) a)).alls

variable (β) in
/-- `iExs f φ` transforms a `L.Formula (α ⊕ β)` into a `L.Formula α` by existentially
quantifying over all variables `Sum.inr _`. -/
noncomputable def iExs [Finite (Sigma β)]
    (φ : L.Formula (α ⊕ₛ β)) : L.Formula α :=
by
  rcases famToSignature β with ⟨σ, e⟩
  exact
    (φ.relabel
        (fun s a => Sum.map id (e s) a)).exs

variable (β) in
/-- `iExsUnique f φ` transforms a `L.Formula (α ⊕ β)` into a `L.Formula α` by existentially
quantifying over all variables `Sum.inr _` and asserting that the solution should be unique -/
noncomputable def iExsUnique [Finite (Sigma β)] (φ : L.Formula (α ⊕ₛ β)) : L.Formula α :=
by
  classical
  -- interpret the β-variables of φ as the right β-block in ((α ⊕ β) ⊕ β)
  let shiftβ : (α ⊕ₛ β) →ₛ ((α ⊕ₛ β) ⊕ₛ β) :=
    fun s =>
      Sum.elim
        (fun a => Sum.inl (Sum.inl a))  -- α ↦ inl (inl a)
        (fun x => Sum.inr x)            -- β ↦ inr x  (the challenger block)

  -- conjunction asserting “witness β = challenger β” (pointwise over the finite Sigma β)
  let eqWitness : L.Formula ((α ⊕ₛ β) ⊕ₛ β) :=
    BoundedFormula.iInf (L := L) (X := Sigma β)
      (fun ⟨s, x⟩ =>
        Term.equal (L := L) (α := ((α ⊕ₛ β) ⊕ₛ β))
          (Term.var s (Sum.inl (Sum.inr x)))  -- witness β  (the left of (α ⊕ β))
          (Term.var s (Sum.inr x))            -- challenger β
      )
  -- uniqueness condition: ∀ challenger β, (φ[challenger] → challenger = witness)
  let uniq : L.Formula (α ⊕ₛ β) :=
    Formula.iAlls (L := L) (α := (α ⊕ₛ β)) (β := β)
      ((BoundedFormula.rename (L := L) (σ := Signature.nil) shiftβ φ).imp eqWitness)
  -- ∃ witness β, (φ ∧ uniq)
  exact Formula.iExs (L := L) (α := α) (β := β) (φ ⊓ uniq)

end free_var_quantification

/-! ### Additional Formula Operations -/

protected nonrec abbrev iff (φ ψ : L.Formula α) : L.Formula α :=
  φ.iff ψ

/-- Take the disjunction of finitely many formulas.

Note that this is an arbitrary formula defined using the axiom of choice. It is only well-defined up
to equivalence of formulas. -/
noncomputable def iSup {β} {X : Type _} [Finite X] (f : X → L.Formula β) : L.Formula β :=
  BoundedFormula.iSup f

/-- Take the conjunction of finitely many formulas.

Note that this is an arbitrary formula defined using the axiom of choice. It is only well-defined up
to equivalence of formulas. -/
noncomputable def iInf {β} {X : Type _} [Finite X] (f : X → L.Formula β) : L.Formula β :=
  BoundedFormula.iInf f

/-! ### Formula-Sentence Equivalence -/

/-- A bijection sending formulas to sentences with constants. -/
def equivSentence : L.Formula α ≃ L[[α]].Sentence :=
  (BoundedFormula.constantsVarsEquiv.trans
    (BoundedFormula.relabelEquiv
      (MSEquiv.fromEquivs
        (fun _ => Equiv.sumEmpty _ _))
    )
  ).symm

theorem equivSentence_not (φ : L.Formula α) : equivSentence φ.not = (equivSentence φ).not :=
  by
    simp [equivSentence, BoundedFormula.constantsVarsEquiv, BoundedFormula.relabelEquiv,
      BoundedFormula.mapTermRelEquiv, BoundedFormula.mapTermRel, BoundedFormula.not]
    rfl
theorem equivSentence_inf (φ ψ : L.Formula α) :
    equivSentence (φ ⊓ ψ) = equivSentence φ ⊓ equivSentence ψ :=
  by
    simp [equivSentence, BoundedFormula.constantsVarsEquiv, BoundedFormula.relabelEquiv,
      BoundedFormula.mapTermRelEquiv, BoundedFormula.mapTermRel]
    rfl

end Formula

variable {T : L.Theory}

/-! ## Cardinality -/

section Cardinality

/-! ### Helper Definitions -/

def mkVar'' {σ : Signature Sorts} (i : Fin σ.length) :
    (Σ s : Sorts, L.Term (α ⊕ₛ σ.Idx) (of s)) := by
  let sv := σ.getIdx i
  exact ⟨sv.fst, .var sv.fst (Sum.inr sv.snd)⟩

open Signature
variable (L)

/-- Helper: `fromListAux acc (replicate n s)` preserves `OneSort s` when `acc` is already
`OneSort s`. -/
private def oneSort_fromListAux_replicate {S} (s : S) :
    ∀ (acc : Signature S), OneSort s acc → ∀ n : ℕ,
      OneSort s (Signature.fromListAux acc (List.replicate n s)) := by
  intro acc hacc n
  induction n generalizing acc with
  | zero =>
      simpa [Signature.fromListAux] using hacc
  | succ n ih =>
      -- replicate (n+1) s = s :: replicate n s
      simp only [List.replicate_succ, fromListAux]
      -- unfold the accumulator update in fromListAux
      cases acc with
      | nil =>
          -- acc' := of s
          simpa using (ih (acc := of s) (hacc := OneSort.of))
      | of t =>
          -- This case can only happen if `t` is definitionally `s`
          -- (since `hacc : OneSort s (.of t)`).
          cases hacc
          -- now acc = of s
          have hacc' : OneSort s ((of s) ⨯ ⦃s⦄) :=
            OneSort.prod OneSort.of OneSort.of
          simpa using (ih (acc :=  (of s) ⨯ ⦃s⦄) (hacc := hacc'))
      | prod σ τ =>
          have hacc' : OneSort s ((σ ⨯ τ) ⨯ ⦃s⦄) :=
            OneSort.prod hacc OneSort.of
          simpa using (ih (acc := (σ ⨯ τ) ⨯ ⦃s⦄) (hacc := hacc'))

/-- Helper: `fromList (replicate n s)` is `OneSort s`. -/
private def oneSort_fromList_replicate {S} (s : S) (n : ℕ) :
    OneSort s (Signature.fromList (List.replicate n s)) := by
  simpa [Signature.fromList] using
    (oneSort_fromListAux_replicate (s := s) (acc := (Signature.nil : Signature S)) OneSort.nil n)

/-- `repeat n s` is the `Signature` consisting of `n` copies of `.of s`, multiplied on the right. -/
def _root_.MSFirstOrder.Signature.repeat (n : ℕ) (s : Sorts) : Signature Sorts :=
  match n with
  | .zero => .nil
  | .succ n => (Signature.repeat n s) ⨯ ⦃s⦄

@[simp]
lemma _root_.MSFirstOrder.Signature.repeat_length (n : ℕ) (s : Sorts) :
  (Signature.repeat n s).length = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [Signature.repeat, length_prod, ih, length_of]

@[simp] lemma _root_.MSFirstOrder.Signature.repeat_zero (s : Sorts) :
    Signature.repeat (Sorts := Sorts) 0 s = .nil := by
  simp only [Signature.repeat]

/-- Successor rule for `repeat`: appending one more copy of `s` corresponds to multiplying by
`.of s` on the right. -/
@[simp] lemma _root_.MSFirstOrder.Signature.repeat_succ (n : ℕ) (s : Sorts) :
    Signature.repeat (Sorts := Sorts) (n + 1) s =
      ((Signature.repeat (Sorts := Sorts) n s) ⨯ ⦃s⦄) := by
  simp only [Signature.repeat]

/-- `repeat n s` is a one-sorted `Signature` (all entries are `s`). -/
def _root_.MSFirstOrder.Signature.oneSort_repeat (s : Sorts) (n : ℕ) :
    OneSort s (Signature.repeat (Sorts := Sorts) n s) := by
  induction n with
  | zero =>
    simp_all only [Signature.repeat_zero]
    apply OneSort.nil
  | succ n ih =>
      rw [Signature.repeat]
      apply OneSort.prod ih
      apply OneSort.of


/-! ### Cardinality Sentences and Theories -/

/-
### Distinctness over repeated blocks
-/

open Term Signature

/-- In context `σ ⨯ ⦃s⦄`, asserts that the rightmost variable of sort `s`
    is distinct from every variable in the left `σ` block (assumed to be one-sorted). -/
protected def BoundedFormula.distinct_from
    (s : Sorts) : (σ : Signature Sorts)→ (hσ : OneSort s σ) →
    L.BoundedFormula α (σ ⨯ ⦃s⦄)
    |  .nil,  h =>  ⊤
    |  .of t,  h => by
        cases h with
        | of => exact
          ((var s (Sum.inr (Idx.left .var))).bdEqual
                        (var s (Sum.inr (Idx.right  (.var (s:= s)) )))).not
    |  (.prod σ τ), h => by
      cases h with
      | prod hσ hτ =>
        -- embed (σ ⨯ ⦃s⦄) into ((σ ⨯ τ) ⨯ ⦃s⦄)
        let gσ :
            SigMap (σ ⨯ ⦃s⦄) ((σ ⨯ τ) ⨯ ⦃s⦄) :=
          (SigMap.incl_left (σ := σ) (τ := τ)).extend_right (η := ⦃s⦄)
        -- embed (τ ⨯ ⦃s⦄) into ((σ ⨯ τ) ⨯ ⦃s⦄)
        let gτ :
            SigMap (τ ⨯ ⦃s⦄) ((σ ⨯ τ) ⨯ ⦃s⦄) :=
          (SigMap.incl_right (σ := τ) (τ := σ)).extend_right (η := ⦃s⦄)
        exact
          ((BoundedFormula.distinct_from s σ hσ).reindex gσ) ⊓
          ((BoundedFormula.distinct_from s τ hτ).reindex gτ)

/-- `distinct s n` asserts that the `n` bound variables of sort `s` in `Signature.repeat n s`
    are pairwise distinct. Defined inductively on `n`.

    The successor case is: old distinctness (reindexed into the left block) and
    the new last variable is distinct from all earlier ones. -/
protected def BoundedFormula.distinct (s : Sorts) :
    ∀ n : ℕ, L.BoundedFormula α (Signature.repeat n s)
  | 0 => ⊤
  | n + 1 =>
    ((BoundedFormula.distinct s n).reindex (SigMap.incl_left)) ⊓
    (BoundedFormula.distinct_from L s (Signature.repeat n s) (Signature.oneSort_repeat s n))

/-- A sentence indicating that a structure has at least `n` distinct elements of sort `s`. -/
protected def Sentence.cardGe (s : Sorts) (n : ℕ) : L.Sentence :=
  (BoundedFormula.distinct L s n).exs

/-- A theory indicating that a structure is infinite at a sort. -/
def infiniteTheory (s : Sorts) : L.Theory :=
  Set.range (Sentence.cardGe L s)

/-- A theory that indicates a structure is nonempty. -/
def nonemptyTheory (s : Sorts) : L.Theory :=
  {Sentence.cardGe L s 1}

/-- A theory indicating that each of a set of constants (all of one fixed sort) is distinct. -/
def distinctConstantsTheory (t : Sorts) (s : Set (α t)) : L[[α]].Theory :=
  (fun ab : α t × α t =>
      (Term.equal
        (Constants.term (Sum.inr ab.1) : L[[α]].Term Fam.EmptyFam (.of t))
        (Constants.term (Sum.inr ab.2))).not) ''
    (s ×ˢ s ∩ (Set.diagonal (α t))ᶜ)

/-! ### Properties of distinctConstantsTheory -/

variable {L}

open Set

theorem distinctConstantsTheory_mono {t : Sorts} {s₁ s₂ : Set (α t)} (h : s₁ ⊆ s₂) :
    L.distinctConstantsTheory t s₁ ⊆ L.distinctConstantsTheory t s₂ := by
  unfold distinctConstantsTheory; gcongr

theorem monotone_distinctConstantsTheory (t : Sorts) :
    Monotone (L.distinctConstantsTheory (t := t) : Set (α t) → L[[α]].Theory) :=
  fun _s _t st => L.distinctConstantsTheory_mono (t := t) st

theorem directed_distinctConstantsTheory (t : Sorts) :
    Directed (· ⊆ ·) (L.distinctConstantsTheory (t := t) : Set (α t) → L[[α]].Theory) :=
  Monotone.directed_le (monotone_distinctConstantsTheory (L := L) (α := α) t)

theorem distinctConstantsTheory_eq_iUnion {t : Sorts} (s : Set (α t)) :
    L.distinctConstantsTheory t s =
      ⋃ u : Finset s,
        L.distinctConstantsTheory t (u.map (Function.Embedding.subtype fun x => x ∈ s)) := by
  classical
  simp only [distinctConstantsTheory]
  rw [← image_iUnion, ← iUnion_inter]
  refine congr(_ '' ($(?_) ∩ _))
  ext ⟨i, j⟩
  simp only [prodMk_mem_set_prod_eq, Finset.coe_map, Function.Embedding.coe_subtype, mem_iUnion,
    mem_image, Finset.mem_coe, Subtype.exists, exists_and_right, exists_eq_right]
  refine ⟨fun h => ⟨{⟨i, h.1⟩, ⟨j, h.2⟩}, ⟨h.1, ?_⟩, ⟨h.2, ?_⟩⟩, ?_⟩
  · simp
  · simp
  · rintro ⟨u, ⟨is, _⟩, ⟨js, _⟩⟩
    exact ⟨is, js⟩

end Cardinality

/-! ## Experimental Definitions

NOTE: The following definitions are experimental and may be moved or removed in future versions.
-/

section Experimental

abbrev FinGet {S} (σ : Signature S) : (i : Fin σ.length) → Sigma σ.Idx :=
  match σ with
  | .nil => elim0
  | .of s => fun _ => ⟨s, .var⟩
  | .prod σ₁ σ₂ => Fin.append
    (fun i => ⟨(FinGet σ₁ i).1, .left (FinGet σ₁ i).2⟩)
    (fun j => ⟨(FinGet σ₂ j).1, .right (FinGet σ₂ j).2⟩)

end Experimental


end MSLanguage

end MSFirstOrder
