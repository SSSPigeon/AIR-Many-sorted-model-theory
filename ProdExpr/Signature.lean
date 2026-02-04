import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic
import Lean
import ProdExpr.Fam
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Arithmetic

universe u v

namespace MSFirstOrder

/--
Non-associative product expressions as recommended by Adam Topaz in zulip chat:
-/
inductive Signature (S : Type u) where
  | nil  : Signature S
  | of   : S → Signature S
  | prod : Signature S → Signature S → Signature S
deriving Repr, DecidableEq

infixl:70 " ⨯ " => Signature.prod

/-- Notation for single-sort signatures: `⦃s⦄` means `Signature.of s`. -/
notation "⦃" s "⦄" => Signature.of s

/-- Notation for the empty/nil signature: `⦃⦄` means `⦃⦄`. -/
notation "⦃⦄" => Signature.nil

@[reducible]
instance instSigZero {S} : Zero (Signature S) :=
  {zero := ⦃⦄}

/-- Mapping suggested by Adam Topaz: -/
@[reducible]
def Signature.Interpret {S : Type u} (X : S → Type v) : Signature S → Type v
  | 0       => PUnit
  | .of s      => X s
  | prod a b  => Interpret X a × Interpret X b

/-
--TODO?
instance : Coe S (Signature S) where
  coe := Signature.of
-/

/--
Notation for Signature.Interpret.
`M[[^]]σ = Signature.Interpret M σ`
-/
notation:80 X " [^] " σ:81 => MSFirstOrder.Signature.Interpret X σ

/-
@[reducible]
instance instInterpretHPow {S : Type u} : HPow (S → Type v) (Signature S) (Type v) :=
  {hPow := Signature.Interpret}
-/

lemma Signature.Interpret.hpow_eq {S : Type u} {σ : Signature S}
    {X : S → Type v} : σ.Interpret X = X [^] σ := rfl

@[reducible]
instance nilExpInhabited {S : Type u} {X : S → Type v} : Inhabited (X[^]⦃⦄) :=
  by
    rw [←Signature.Interpret.hpow_eq, Signature.Interpret]
    apply inferInstance

namespace Signature

/--
An alternative inductive version of `toFam`. The idea is to construct, for each `σ : Signature S`,
and each `s : S`, a canonical type `Idx σ s` representing the collection of `s`-type variables
occuring in `σ`. While we can do this with `Fin`, this approach avoids the use of indices and
preserves the non-associative positional data of `σ`.
-/
inductive Idx {S : Type u} : Signature S → S → Type u where
  | var {s : S} : Idx ⦃s⦄ s
  | left {σ τ : Signature S} {s : S} (v : Idx σ s) : Idx (σ ⨯ τ) s
  | right {σ τ : Signature S} {s : S} (v : Idx τ s) : Idx (σ ⨯ τ) s
deriving Repr

variable {S : Type u}

section defs

def length : Signature S → ℕ
  | .nil => 0
  | .of _     => 1
  | .prod a b  => a.length + b.length

@[simp] lemma length_nil : (⦃⦄ : Signature S).length = 0 := by rfl

@[simp] lemma length_of (s : S) : ⦃s⦄.length = 1 := by rfl

@[simp] lemma length_prod (σ τ : Signature S) :
  (σ ⨯ τ).length = σ.length + τ.length := by rfl

/-- `Idx` for a product splits as a sum of `Idx` for the factors. -/
def Idx_as_prod (σ τ : Signature S) :
    (σ ⨯ τ).Idx ≃ₛ σ.Idx ⊕ₛ τ.Idx :=
{ toFun := fun s v =>
    match v with
    | Signature.Idx.left  vσ => Sum.inl vσ
    | Signature.Idx.right vτ => Sum.inr vτ
  , invFun := fun s v =>
    match v with
    | Sum.inl vσ => Signature.Idx.left vσ
    | Sum.inr vτ => Signature.Idx.right vτ
  , left_inv' := by
      intro s v
      cases v with
      | left vσ  => rfl
      | right vτ => rfl
  , right_inv' := by
      intro s v
      cases v with
      | inl vσ => rfl
      | inr vτ => rfl }

end defs

section to_list

/-- Flatten a `Signature` to a list of sorts. -/
def toList : Signature S → List S
  | .nil       => []
  | .of s      => [s]
  | .prod a b  => a.toList ++ b.toList

/--
Given acc, and an input list L we want to insert L into acc
so that acc comes before L and the resulting item is normalized.
This is done by injesting head to tail, taking each head s and inserting
it as the left factor.
-/
def fromListAux (acc : Signature S) : List S → Signature S
  | []      => acc
  | s :: L  =>
      let acc' :=
        match acc with
        | .nil   => .of s --If accumulating on nil, just replace with ⦃s⦄
        | acc    => acc ⨯ ⦃s⦄ --Otherwise we make ⦃s⦄ the new left product
      fromListAux acc' L

/-- Fold a list of `S` into a left-associated `Signature S`. -/
def fromList (L : List S) : Signature S :=
  fromListAux ⦃⦄ L

lemma toList_fromListAux (acc : Signature S) (l : List S) :
    (fromListAux acc l).toList = acc.toList ++ l := by
  induction l generalizing acc with
  | nil =>
      simp [fromListAux]
  | cons s l ih =>
      simp_all only [fromListAux]
      cases acc <;> simp [toList]

lemma toList_fromList (l : List S) :
    (fromList l).toList = l := by
  induction l with
  | nil => rfl
  | cons a as ih => rw [fromList, toList_fromListAux]; rfl

lemma toList_length (a : Signature S) : a.length = a.toList.length := by
  induction a with
  | of => simp only [length, toList, List.length_cons, List.length_nil, zero_add]
  | prod _ _ ih₁ ih₂ => simp only [length, ih₁, ih₂, toList, List.length_append]
  | nil => simp only [length, toList, List.length_nil]

lemma fromList_length {l : List S} : (fromList l).length = l.length := by
  simp only [toList_length, toList_fromList]

end to_list

section equivalences
/- This section defines the equivalence relation on `Signature S` expressing when
`σ` and `τ` are equivalent up to associativity. It also defines a canonical normalized
representative for each class which trims out all `nil` factors from products and
associates to the right.
-/

/--
Inductive type indexing the basic generating types of associative product equivalences
-/
inductive PEquiv : Signature S → Signature S → Type u where
  | refl  {σ} :
      PEquiv σ σ
  | symm  {σ₁ σ₂} :
      PEquiv σ₁ σ₂ → PEquiv σ₂ σ₁
  | trans {σ₁ σ₂ σ₃} :
      PEquiv σ₁ σ₂ → PEquiv σ₂ σ₃ → PEquiv σ₁ σ₃
  | assocL (a b c) :
      PEquiv (.prod (.prod a b) c) (.prod a (.prod b c))
  | assocR (a b c) :
      PEquiv (.prod a (.prod b c)) (.prod (.prod a b) c)
  | nil_left  (a) :
      PEquiv (.prod .nil a) a
  | nil_right (a) :
      PEquiv (.prod a .nil) a
  | prod_congr_left  {a a' b} :
      PEquiv a a' → PEquiv (.prod a b) (.prod a' b)
  | prod_congr_right {a b b'} :
      PEquiv b b' → PEquiv (.prod a b) (.prod a b')

def PEquiv.prod_congr {a a' b b' : Signature S}
    (h₁ : PEquiv a a') (h₂ : PEquiv b b') :
    PEquiv (.prod a b) (.prod a' b') :=
  PEquiv.trans (PEquiv.prod_congr_left h₁) (PEquiv.prod_congr_right h₂)

open PEquiv

/--
Constructs a PEquiv on an intermediate state of the fromList construction:
-/
def PEquiv_fromListAux (acc : Signature S) (l : List S) :
  PEquiv (.prod acc (fromList l)) (fromListAux acc l) := by
  induction l generalizing acc with
  | nil =>
      rw [fromList, fromListAux, fromListAux]
      exact PEquiv.nil_right acc
  | cons s l ih =>
      cases acc with
      | nil => rw [fromList, fromListAux]; apply PEquiv.nil_left
      | of t =>
          rw [fromList, fromListAux, fromListAux]
          · apply PEquiv.trans _ (ih (⦃t⦄ ⨯ ⦃s⦄))
            let h := PEquiv.assocR (S := S) ⦃t⦄ ⦃s⦄ (nil.fromListAux l)
            apply PEquiv.trans _ h
            apply PEquiv.prod_congr_right
            apply PEquiv.trans _ (ih ⦃s⦄).symm
            exact PEquiv.refl
          · simp only [reduceCtorEq, imp_self]
      | prod a b =>
          rw [fromList, fromListAux]
          have h1 : PEquiv (⦃s⦄ ⨯ fromList l) (fromListAux ⦃s⦄ l) :=
            ih ⦃s⦄
          have h2 := ih ((a ⨯ b) ⨯ ⦃s⦄)
          have h1' := PEquiv.symm h1
          have h_left :
            PEquiv ((a ⨯ b) ⨯ fromListAux ⦃s⦄ l)
                    ((a ⨯ b) ⨯ (⦃s⦄ ⨯ fromList l)) :=
            PEquiv.prod_congr_right h1'
          have h_assoc := PEquiv.assocR (a ⨯ b) ⦃s⦄ (fromList l)
          exact PEquiv.trans h_left (PEquiv.trans h_assoc h2)

lemma fromListAux_append (acc : Signature S) (l₁ l₂ : List S) :
  fromListAux acc (l₁ ++ l₂) =
    fromListAux (fromListAux acc l₁) l₂ := by
  induction l₁ generalizing acc with
  | nil =>
      simp [fromListAux]
  | cons s l ih =>
      cases acc with
      | nil =>
          simp [fromListAux, List.cons_append, ih]
      | of t =>
          simp [fromListAux, List.cons_append, ih]
      | prod a b =>
          simp [fromListAux, List.cons_append, ih]

lemma fromList_append_eq_fromListAux (l₁ l₂ : List S) :
  fromList (l₁ ++ l₂) = fromListAux (fromList l₁) l₂ := by
  unfold fromList
  simpa [fromList] using
    fromListAux_append (acc := ⦃⦄) (l₁ := l₁) (l₂ := l₂)

/--
Helper for showing that `σ ≃ fromList (toList σ)`
-/
def fromList_app (l₁ l₂ : List S) :
  PEquiv (.prod (fromList l₁) (fromList l₂)) (fromList (l₁ ++ l₂)) := by
  have h_eq : fromList (l₁ ++ l₂) = fromListAux (fromList l₁) l₂ :=
    fromList_append_eq_fromListAux (S := S) l₁ l₂
  have h :=
    PEquiv_fromListAux (S := S) (acc := fromList l₁) (l := l₂)
  simpa [h_eq] using h

/--
The PEquiv witnessing the equivalence between `σ` and `(fromList (toList σ))`
-/
def equivToFromList : (σ : Signature S) → PEquiv σ (fromList (toList σ))
  | .nil =>
      PEquiv.refl
  | .of a => by
    rw [fromList, toList, fromListAux]
    exact PEquiv.refl
  | .prod a b => by
      let ha := equivToFromList a
      let hb := equivToFromList b
      let h₁ : PEquiv (.prod a b)
                       (.prod (fromList (toList a)) b) :=
        PEquiv.prod_congr_left ha
      let h₂ : PEquiv (.prod (fromList (toList a)) b)
                       (.prod (fromList (toList a)) (fromList (toList b))) :=
        PEquiv.prod_congr_right hb
      let h₃ : PEquiv (.prod (fromList (toList a)) (fromList (toList b)))
                       (fromList (toList a ++ toList b)) :=
        fromList_app (toList a) (toList b)
      unfold toList
      exact PEquiv.trans (PEquiv.trans h₁ h₂) h₃

end equivalences

section normalization

def leftAppend {S} : Signature S → Signature S → Signature S
  | acc, .nil        => acc ⨯ ⦃⦄
  | acc, .of s       => acc ⨯ ⦃s⦄
  | acc, .prod σ τ   =>
      let acc' := leftAppend acc σ
      leftAppend acc' τ

/-- Left-associate a `Signature` without trimming `nil`s. -/
def leftAssoc : Signature S → Signature S
  | .nil      => .nil
  | .of s     => ⦃s⦄
  | .prod σ τ => leftAppend (leftAssoc σ) τ

def trimNil : Signature S → Signature S
  | .nil      => .nil
  | .of s     => ⦃s⦄
  | .prod σ τ =>
      match trimNil σ, trimNil τ with
      | .nil, .nil => .nil
      | .nil, τ'   => τ'
      | σ',  .nil  => σ'
      | σ',  τ'    => .prod σ' τ'

lemma toList_leftAppend (acc σ : Signature S) :
  (leftAppend acc σ).toList = acc.toList ++ σ.toList := by
  induction σ generalizing acc with
  | nil =>
      simp [leftAppend, toList]
  | of s =>
      simp [leftAppend, toList]
  | prod σ τ ihσ ihτ =>
      simp [leftAppend, toList, ihσ, ihτ, List.append_assoc]

lemma toList_leftAssoc (σ : Signature S) :
  (leftAssoc σ).toList = σ.toList := by
  induction σ with
  | nil =>
      simp [leftAssoc, toList]
  | of s =>
      simp [leftAssoc, toList]
  | prod σ τ ihσ ihτ =>
      simp [leftAssoc, toList, toList_leftAppend, ihσ]

def normalize (σ : Signature S) : Signature S := trimNil (leftAssoc σ)

/-- The normalization bundled with a proof of equivalence -/
@[simp]
def normalize_list (σ : Signature S) : Σ σ' : Signature S, PEquiv σ σ' :=
  ⟨fromList (toList σ), equivToFromList σ⟩

variable {S : Type u}

lemma trimNil_prod_of (acc : Signature S) (s : S) :
    trimNil (acc ⨯ ⦃s⦄) = match trimNil acc with
      | .nil => ⦃s⦄
      | a => a ⨯ ⦃s⦄ := by
  simp only [trimNil]
  split
  next x x_1 heq heq_1 => simp_all [reduceCtorEq]
  next x x_1 heq x_2 => simp_all only [reduceCtorEq, implies_true]
  next x x_1 heq x_2 x_3 => simp_all only [reduceCtorEq]
  next x x_1 x_2 x_3 x_4 => simp_all only [imp_false, reduceCtorEq, implies_true]

lemma fromListAux_eq_trimNil_leftAppend (acc : Signature S) (σ : Signature S) :
    fromListAux (trimNil acc) (toList σ) = trimNil (leftAppend acc σ) := by
  induction σ generalizing acc with
  | nil =>
      simp [toList, fromListAux, leftAppend, trimNil]
      split <;> simp_all
  | of s =>
      simp only [toList, fromListAux, leftAppend, trimNil_prod_of]
  | prod x y ihx ihy =>
      rw [toList, leftAppend, fromListAux_append]
      simp_all only

lemma normalize_unique (σ : Signature S) : normalize σ = (fromList (toList σ)) := by
  unfold normalize
  induction σ with
  | nil =>
      rfl
  | of s =>
      rfl
  | prod x y ih_x ih_y =>
      simp only [fromList, toList]
      rw [fromListAux_append]
      have h_fold_x : trimNil (leftAssoc x) = fromListAux ⦃⦄ (toList x) := ih_x
      rw [←h_fold_x]
      rw [fromListAux_eq_trimNil_leftAppend (leftAssoc x) y]
      rfl

open Equiv

def interpretEquiv (X : S → Type v) :
    {σ₁ σ₂ : Signature S} → PEquiv σ₁ σ₂ → Interpret X σ₁ ≃ Interpret X σ₂
  | _, _, .refl      => Equiv.refl _
  | _, _, .symm h    => (interpretEquiv X h).symm
  | _, _, .trans h₁ h₂ =>
      (interpretEquiv X h₁).trans (interpretEquiv X h₂)
  | _, _, .assocL _ _ _ =>
      prodAssoc _ _ _
  | _, _, .assocR _ _ _ =>
      (prodAssoc _ _ _).symm
  | _, _, .nil_left _ =>
      punitProd _
  | _, _, .nil_right _ =>
      prodPUnit _
  | _, _, .prod_congr_left h =>
      prodCongrLeft (fun _ => (interpretEquiv X h))
  | _, _, .prod_congr_right h =>
      prodCongrRight (fun _ => (interpretEquiv X h))

def interpretToInterpretNormalizedEquiv (X : S → Type v) (σ : Signature S) :
    σ.Interpret X ≃ (normalize σ).Interpret X := by
    rw [normalize_unique]
    exact interpretEquiv _ (equivToFromList σ)

end normalization

section finite_family_conversion
/-! ## Finite Family to Signature Conversion

This section provides machinery to convert a finite family `X : S → Type*`
into a `Signature S` with an equivalence. Used in Syntax.lean for
quantification over finite families (iAlls, iExs, iExsUnique).

### Algorithm
1. Use classical choice to get `Sigma X ≃ Fin n`
2. Build a list of sorts by enumerating `Fin n`
3. Convert to `Signature` via `fromList`
4. Build sort-respecting equivalence `X ≃ₛ σ.Idx`

### Public API
- `getIdx`: Get i-th variable with sort info
- `getIdx_fst`: Relates to `toList`
- `Idx.toFin`: Inverse direction
- `FinIndSigEquiv`: Explicit bijection
- `famToSignature`: Main construction (noncomputable)
-/

variable {σ : Signature S}

private lemma nat_lt_lemma {n m k : ℕ} (hink : m < n + k) (hni : n ≤ m) : m - n < k := by
   have h := Nat.sub_lt_sub_right (a := m) (c:= n) (b := n + k)
   simp_all only [add_tsub_cancel_left, forall_const]

/-- Left injection for product indices -/
private def injLeft (σ τ : Signature S) (i : Fin σ.length) :
    Fin (σ ⨯ τ).length :=
  ⟨i,
    by
      -- `i < σ.length ≤ σ.length + τ.length`
      have hi : (i : Nat) < σ.length := i.is_lt
      exact Nat.lt_of_lt_of_le hi (Nat.le_add_right _ _)⟩

lemma injLeft_Injective {σ τ : Signature S} :
  Function.Injective (injLeft σ τ) := by
  intro v w h
  cases v ;cases w ; simp_all only [Fin.mk.injEq, injLeft]

/-- Right injection for product indices -/
private def injRight (σ τ : Signature S) (j : Fin τ.length) :
    Fin (σ ⨯ τ).length :=
  ⟨σ.length + j,
    by
      have hj : (j : Nat) < τ.length := j.is_lt
      have : σ.length + (j : Nat) < σ.length + τ.length :=
        Nat.add_lt_add_left hj σ.length
      simp [Signature.length]⟩

lemma injRight_Injective {σ τ : Signature S} :
  Function.Injective (injRight σ τ) := by
  intro v w h
  cases v ; cases w ; simp_all only [injRight, Fin.mk.injEq, Nat.add_left_cancel_iff]

/-- List out the associated variables to a given σ -/
def IdxList : (σ : Signature S) → List (Sigma σ.Idx)
  | nil => []
  | of s => [⟨s, Idx.var⟩]
  | prod σ τ => σ.IdxList.map (fun ⟨s, v⟩ => ⟨s, Idx.left v⟩) ++
                τ.IdxList.map (fun ⟨s, v⟩ => ⟨s, Idx.right v⟩)

@[simp]
lemma IdxList_length : (IdxList σ).length = σ.length := by
  induction σ
  case nil => simp only [IdxList, List.length_nil, length_nil]
  case of => simp only [IdxList, List.length_cons, List.length_nil, zero_add, length_of]
  case prod => simp_all only [IdxList, List.length_append, List.length_map]; rfl

lemma IdxList_map_fst (σ : Signature S) :
  (σ.IdxList.map (fun p => p.1)) = σ.toList := by
  induction σ with
  | nil =>
      simp only [IdxList, List.map_nil, toList]
  | of s =>
      simp only [IdxList, List.map_cons, List.map_nil, toList]
  | prod σ τ ihσ ihτ =>
      have hσ : σ.IdxList.map
        ((fun p : Sigma (σ ⨯ τ).Idx ↦ p.fst) ∘ fun x ↦ ⟨x.fst, x.snd.left⟩) = σ.toList
        := by exact ihσ
      have hτ : τ.IdxList.map
        ((fun p : Sigma (σ ⨯ τ).Idx ↦ p.fst) ∘ fun x ↦ ⟨x.fst, x.snd.right⟩) = τ.toList
        := by exact ihτ
      rw [toList, ←hσ, ←hτ]
      simp only [IdxList, List.map_append, List.map_map]

def getIdx (σ : Signature S) : Fin σ.length → Sigma σ.Idx :=
  fun i => σ.IdxList.get (Fin.cast IdxList_length.symm i)

@[simp] private lemma getIdx_prod_left
  {σ τ : Signature S} (i : Fin (σ ⨯ τ).length) (h : (i : Nat) < σ.length) :
  getIdx (σ ⨯ τ) i
    =
    ⟨(getIdx σ ⟨(i : Nat), h⟩).1,
      Signature.Idx.left (getIdx σ ⟨(i : Nat), h⟩).2⟩ := by
  let j : Fin σ.length := ⟨(i : Nat), h⟩
  have hij : σ.injLeft τ j = i := by
    ext; rfl
  simp only [getIdx, IdxList]
  simp_all only [List.get_eq_getElem, Fin.coe_cast, List.length_map, IdxList_length,
    List.getElem_append_left, List.getElem_map, Fin.cast_mk, j]

@[simp] private lemma getIdx_prod_right
  {σ τ : Signature S} (i : Fin (σ ⨯ τ).length) (h : σ.length ≤ (i : Nat)) :
  getIdx (σ ⨯ τ) i
    =
    ⟨(getIdx τ
        ⟨(i : Nat) - σ.length,
          nat_lt_lemma (n := σ.length) (m := (i : Nat)) (k := τ.length) i.is_lt h⟩).1,
      Signature.Idx.right
        (getIdx τ
          ⟨(i : Nat) - σ.length,
            nat_lt_lemma (n := σ.length) (m := (i : Nat)) (k := τ.length) i.is_lt h⟩).2⟩ := by
  let k : Fin τ.length :=
    ⟨(i : Nat) - σ.length,
      nat_lt_lemma (n := σ.length) (m := (i : Nat)) (k := τ.length) i.is_lt h⟩
  have hik : Signature.injRight σ τ k = i := by
    ext
    simp [Signature.injRight, k, Nat.add_sub_of_le h]
  simp only [getIdx, IdxList]
  simp_all only [List.get_eq_getElem, Fin.coe_cast, List.length_map,
    IdxList_length, List.getElem_append_right, List.getElem_map, Fin.cast_mk, k]

def Idx.toFin : ∀ {σ : Signature S} {s : S}, σ.Idx s → Fin σ.length
  | .of _, _, .var      => ⟨0, by simp [Signature.length]⟩
  | .prod σ τ, _, .left v  => Signature.injLeft  σ τ (Idx.toFin v)
  | .prod σ τ, _, .right v => Signature.injRight σ τ (Idx.toFin v)

def Idx.toFin_inj {σ : Signature S} {s : S} :
    Function.Injective (toFin (σ := σ) (s := s)) := by
  intro v w h
  induction σ with
  | nil => cases v
  | of s => cases v; cases w; simp only
  | prod η τ ihη ihτ =>
    cases v
    case left v' =>
      cases w
      case left w' =>
        rw [left.injEq]
        apply ihη
        simp_all only [toFin]
        exact injLeft_Injective h
      case right w' =>
        simp_all only [toFin, injLeft, injRight, Fin.mk.injEq, reduceCtorEq]
        let hv' := v'.toFin.2
        let hw' := w'.toFin.2
        linarith
    case right v' =>
      cases w
      case left w' =>
        simp_all only [toFin, injRight, injLeft, Fin.mk.injEq, reduceCtorEq]
        let hv' := v'.toFin.2
        let hw' := w'.toFin.2
        linarith
      case right w' =>
        rw [right.injEq]
        apply ihτ
        simp_all only [toFin]
        exact injRight_Injective h

/-- Inverse direction: `Σ s, σ.Idx s → Fin σ.length`. -/
private def getIdxInv (σ : Signature S) : Sigma σ.Idx → Fin σ.length
  | ⟨_, v⟩ => Idx.toFin v

@[simp] private lemma getIdx_toFin {σ : Signature S} {s : S} (v : σ.Idx s) :
  getIdx σ (Idx.toFin v) = ⟨s, v⟩ := by
  induction σ with
  | nil => cases v
  | of s =>
    cases v
    case of =>
      simp [getIdx, IdxList]
  | prod σ τ ih₁ ih₂ =>
    cases v
    case left w =>
      simp only [getIdx, IdxList, Idx.toFin, injLeft, Fin.cast_mk, List.get_eq_getElem,
        List.length_map, IdxList_length, Fin.is_lt, List.getElem_append_left, List.getElem_map,
        Sigma.mk.injEq]
      have h₁ := ih₁ w
      simp only [getIdx, List.get_eq_getElem, Fin.coe_cast] at h₁
      rw [h₁]
      simp only [heq_eq_eq, and_self]
    case right w =>
      have h₂ := ih₂ w
      simp only [getIdx, IdxList, Idx.toFin, injRight, Fin.cast_mk, List.get_eq_getElem,
        List.length_map, IdxList_length, le_add_iff_nonneg_right, zero_le,
        List.getElem_append_right, add_tsub_cancel_left, List.getElem_map, Sigma.mk.injEq]
      simp only [getIdx, List.get_eq_getElem, Fin.coe_cast] at h₂
      apply And.intro
      · simp_all only
      · rw [h₂]


@[simp] private lemma getIdxInv_getIdx {σ : Signature S} (i : Fin σ.length) :
  σ.getIdxInv (getIdx σ i) = i := by
  induction σ with
  | nil =>
    cases i
    case mk j h =>
      rw [Signature.length] at h
      simp_all only [not_lt_zero']
  | of s => ext; simp_all only [Fin.val_eq_zero]
  | prod σ τ ih₁ ih₂ =>
    by_cases h : ↑i < σ.length
    case pos =>
      have h₁ := ih₁ ⟨↑i, h⟩
      simp [getIdx_prod_left i h]
      simp [getIdxInv, Idx.toFin] at *
      simp [h₁, injLeft]
    case neg =>
      let j := ↑i - σ.length
      have hi : ↑i < σ.length + τ.length := by
          rcases i with ⟨i, hi⟩
          simp_all only [not_lt]
          exact hi
      have hj : j < τ.length := by
        change ↑i - σ.length < τ.length
        simp_all only [not_lt]
        exact nat_lt_lemma hi h
      have h₂ := ih₂ ⟨j, hj⟩
      simp only [getIdx_prod_right i (by simp_all only [not_lt, j])]
      unfold j at *
      simp only [getIdxInv, Idx.toFin] at *
      simp [h₂, injRight]
      rcases i with ⟨i', hi'⟩
      have hh : σ.length + (i' - σ.length) = i' := by
        simp_all only [not_lt, add_tsub_cancel_of_le]
      simp_all only

/-- Explicit equivalence between `Fin σ.length` and `Sigma (σ.Idx)` -/
def FinIndSigEquiv (σ : Signature S) : Fin σ.length ≃ Sigma (σ.Idx) :=
{ toFun    := getIdx σ
  invFun   := getIdxInv (σ := σ)
  left_inv := by
    intro i; simp only [getIdxInv_getIdx]
  right_inv := by
    intro x
    rcases x with ⟨s, v⟩
    simp only [getIdxInv, getIdx_toFin v]
}

instance instSigmaSigFinite {σ : Signature S} : Finite (Sigma (σ.Idx)) := by
  exact Finite.of_equiv (Fin σ.length) (FinIndSigEquiv (σ := σ))

-- σ.Idx s is finite, since it injects into that finite sigma type
instance instSigAtSortFinite {σ : Signature S} {s : S} : Finite (σ.Idx s) := by
  refine Finite.of_injective
    (fun v : σ.Idx s => (⟨s, v⟩ : Sigma (σ.Idx))) ?_
  intro v w h
  cases h
  rfl

lemma getIdx_fst (σ : Signature S) (i : Fin σ.length) :
  (getIdx σ i).1 = σ.toList.get (Fin.cast (toList_length σ) i) := by
  simp only [List.get_eq_getElem, ← IdxList_map_fst σ, Fin.coe_cast, List.getElem_map]
  rfl

private lemma cast_fin_app {σ : Signature S} {T : Type*} {n : Nat}
    (h : σ.length = n) (g : Fin σ.length → T) (i : Fin n) :
    (h ▸ g) i = g (Fin.cast h.symm i) := by
  cases h
  rfl

@[simp]
private lemma cast_getIdx {σ : Signature S} {n : Nat}
    (h : σ.length = n) (i : Fin n) :
    (h ▸ σ.getIdx) i = σ.getIdx (Fin.cast h.symm i) := by
  cases h
  rfl

@[simp]
lemma cast_FinIndSigEquiv_apply {σ : Signature S} {n : Nat}
    (h : σ.length = n) (i : Fin n) :
    (h ▸ FinIndSigEquiv σ) i = (FinIndSigEquiv σ) (Fin.cast h.symm i) := by
  cases h
  rfl

variable (X : S → Type*) [Finite (Sigma X)]
/-- Equivalence between a finite family over `S` to the Idxs of a `Signature S` -/
noncomputable def famToSignature : Σ σ : Signature S, X ≃ₛ σ.Idx := by
  classical
  let n : Nat := Classical.choose (Finite.exists_equiv_fin (Sigma X))
  let e : (Sigma X) ≃ Fin n :=
    Classical.choice (Classical.choose_spec (Finite.exists_equiv_fin (Sigma X)))
  let l := (List.ofFn (fun i : Fin n => (e.symm i)))
  let σ := Signature.fromList (l.map (fun p => p.1))
  have hlσ : l.map (fun p => p.1) = σ.toList := by
    have h : Signature.toList (Signature.fromList (l.map (fun p => p.1))) = σ.toList := by
      simp_all only [List.map_ofFn, l, n, e, σ]
    simp only [toList_fromList] at h
    exact h
  have hl : l.length = n := by
    simp_all only [List.length_ofFn, l, n, e]
  have hσ : σ.length = n := by
    simp only [fromList_length, List.length_map, hl, σ]
  refine ⟨σ, ?_⟩
  let f := e.trans (hσ ▸ FinIndSigEquiv σ)
  have hfst : ∀ p : Sigma X, (f p).1 = p.1 := by
    intro p
    rcases p with ⟨s, x⟩
    set i : Fin n := e ⟨s, x⟩
    set i' : Fin σ.length := Fin.cast hσ.symm i
    have :
      (f ⟨s, x⟩).1 = σ.toList.get (Fin.cast (toList_length σ) i') := by
      rw [←getIdx_fst]
      have : (f ⟨s, x⟩).1 = (σ.getIdx i').fst := by
        simp only [Equiv.trans_apply, cast_FinIndSigEquiv_apply, f]
        change (σ.FinIndSigEquiv i').fst = (σ.getIdx i').fst
        simp_all only [List.map_ofFn, List.length_ofFn, l, n, e, σ, i', i]
        rfl
      simp_all only [List.map_ofFn, List.length_ofFn, Equiv.trans_apply, cast_FinIndSigEquiv_apply,
              l, n, e, σ, f, i', i]
    rw [this]
    simp [←hlσ]
    simp_all only [List.length_ofFn, Fin.cast_cast, List.get_eq_getElem, Fin.coe_cast,
      List.getElem_ofFn, Fin.eta, Equiv.symm_apply_apply, l, i', i]
  have hfsymm_fst : ∀ v : Sigma (σ.Idx), (f.symm v).1 = v.1 := by
    intro v
    rcases v with ⟨s, v⟩
    have : (f (f.symm ⟨s, v⟩)).1 = s := by simp
    exact (hfst (f.symm ⟨s, v⟩)).symm.trans this
  let toFun : X →ₛ σ.Idx := fun (s : S) (x : X s) =>
      (by simp [hfst ⟨s, x⟩] : (f ⟨s, x⟩).fst = s) ▸ (f ⟨s, x⟩).2
  let invFun : σ.Idx →ₛ X := fun s v =>
      (by simp [hfsymm_fst ⟨s, v⟩] : (f.symm ⟨s, v⟩).1 = s) ▸ (f.symm ⟨s, v⟩).2
  have h_map : ∀ (s : S) (x : X s), ⟨s, toFun s x⟩ = f ⟨s, x⟩ := by
    intro s x
    simp only [toFun]
    refine Sigma.ext (by simp [hfst] : _) ?_
    simp_all only [List.map_ofFn, List.length_ofFn, Equiv.trans_apply,
                   eqRec_heq_iff_heq, heq_eq_eq, l, n, e, σ, f]
  have h_inv : ∀ (s : S) (v : σ.Idx s), ⟨s, invFun s v⟩ = f.symm ⟨s, v⟩ := by
    intro s x
    simp only [invFun]
    refine Sigma.ext (by simp [hfsymm_fst] : _) ?_
    simp_all only [List.map_ofFn, List.length_ofFn, Equiv.trans_apply,
                  cast_FinIndSigEquiv_apply, eqRec_heq_iff_heq, heq_eq_eq, l, n, e, σ, f]
  exact
  { toFun := toFun

    invFun := invFun

    left_inv' := by
      intro s x
      have h : ⟨s, invFun s (toFun s x)⟩ = (⟨s, x⟩ : Sigma X) := by
        rw [h_inv]
        rw [h_map]
        simp only [Equiv.symm_apply_apply]
      have hx : HEq (invFun s (toFun s x)) x := by
        exact (Sigma.mk.inj h).2
      exact eq_of_heq hx
    right_inv' := by
      intro s v
      have h : ⟨s, toFun s (invFun s v)⟩ = (⟨s, v⟩ : Sigma σ.Idx) := by
        rw [h_map]
        rw [h_inv]
        simp only [Equiv.apply_symm_apply]
      have hv : HEq (toFun s (invFun s v)) v := by
        exact (Sigma.mk.inj h).2
      exact eq_of_heq hv
  }

end finite_family_conversion

section variable_maps
/-! ## Variable Mappings

This section defines variable transformations between Signature structures:

### Type Hierarchy
- `SigMap σ τ`: General variable maps (type alias for `σ.Idx →ₛ τ.Idx`)
- `SigEmbed σ τ`: Injective variable maps (type alias for `MSEmbedding σ.Idx τ.Idx`)
- `SigEquiv σ τ`: Bijective variable maps (type alias for `MSEquiv σ.Idx τ.Idx`)

### Relationship to PEquiv
While `PEquiv` describes associative equivalences between Signatures,
`SigEquiv` describes equivalences between variable families up to associative and commutative
equivalence. The function `fromPEquiv : PEquiv σ τ → SigEquiv σ τ`
(defined in the `var_equivs` section) connects these two notions.

### Core Operations
Identity and Extensions:
- `SigMap.Id`, `SigEmbed.Id`, `SigEquiv.Id`: Identity transformations
- `extend_right`: Extend map by identity on right: `(σ → τ) ⇒ (σ ⨯ η → τ ⨯ η)`
- `extend_left`: Extend map by identity on left: `(σ → τ) ⇒ (η ⨯ σ → η ⨯ τ)`
- `incl_left`: Inject left: `σ → σ ⨯ τ`
- `incl_right`: Inject right: `σ → τ ⨯ σ`

Structural Transformations:
- `comm`: Swap factors: `σ ⨯ τ ≃ τ ⨯ σ`
- `assocL`: Left-associate: `((σ ⨯ τ) ⨯ η) ≃ (σ ⨯ (τ ⨯ η))`
- `assocR`: Right-associate: `(σ ⨯ (τ ⨯ η)) ≃ ((σ ⨯ τ) ⨯ η)`
- `nilLeft`: Cancel nil on left: `nil ⨯ σ ≃ σ`
- `nilRight`: Cancel nil on right: `σ ⨯ nil ≃ σ`

### Usage Patterns
- ⨯⨯Syntax.lean⨯⨯: `reindex` operations for terms and formulas, `block_swap` for variable swapping
- ⨯⨯SyntaxClasses.lean⨯⨯: Quantifier casting (e.g., `nilLeft` for `∀' s` notation)
- ⨯⨯Semantics.lean⨯⨯: Structural transformations in realization proofs
-/

/-- A type for dependent mappings on bound variable sets -/
abbrev SigMap (σ τ : Signature S) := σ.Idx →ₛ τ.Idx

/-- Injective SigMaps -/
abbrev SigEmbed (σ τ : Signature S) := Fam.MSEmbedding σ.Idx τ.Idx

/-- SigMaps which are Equivs -/
abbrev SigEquiv (σ τ : Signature S) := Fam.MSEquiv σ.Idx τ.Idx

/-- SigEmbeds are determined by their toFun. -/
@[ext]
lemma varEmbed_ext {σ τ : Signature S} {h h' : SigEmbed σ τ}
    (heq : h.toFun = h'.toFun) : h = h' := by
  ext x x_1 : 3
  simp_all only

/-- SigEquivs are determined by their toFun. -/
@[ext]
lemma varEquiv_ext {σ τ : Signature S} {h h' : SigEquiv σ τ}
    (heq : h.toFun = h'.toFun) : h = h' := by
  ext x x_1 : 3
  simp_all only

/-- Identity variable map -/
def SigMap.Id {σ : Signature S} : SigMap σ σ := Fam.id (α := σ.Idx)

/-- Identity variable embedding -/
@[simp] def SigEmbed.Id {σ : Signature S} : SigEmbed σ σ :=
 { toFun := SigMap.Id,
   inj' := by
     intro t h a₂ a
     subst a
     simp_all only [Fam.id, SigMap.Id, id_eq] }

/-- Identity variable equivalence -/
@[simp] def SigEquiv.Id {σ : Signature S} : SigEquiv σ σ :=
 { toFun := SigMap.Id,
   invFun := SigMap.Id,
   left_inv' := by intro s h; simp [SigMap.Id],
   right_inv' := by intro s h; simp [SigMap.Id] }

@[simp] lemma SigMap.Id_apply {σ : Signature S} (s : S) (v : σ.Idx s) :
  (SigMap.Id s) v = v := rfl

@[simp] lemma SigEmbed.Id_apply {σ : Signature S} (s : S) (v : σ.Idx s) :
  (SigEmbed.Id s) v = v := rfl

instance (σ τ : Signature S) : CoeFun (SigEmbed σ τ) (fun _ => σ.Idx →ₛ τ.Idx) where
  coe := (fun h => h.toFun)

instance (σ τ : Signature S) : CoeFun (SigEquiv σ τ) (fun _ => σ.Idx →ₛ τ.Idx) where
  coe := (fun h => h.toFun)

/-- If we have a varMap from `σ` to `τ`, it can naturally be extended to products
    with `η` by applying the identity on `η`-variables. -/
@[simp]
def SigMap.extend_right {σ τ η : Signature S} (h : SigMap σ τ)
  : SigMap (σ ⨯ η) (τ ⨯ η) :=
   fun s => fun v =>
      match v with
      | .left w =>
          Idx.left ((h s) w)
      | .right w =>
          Idx.right w

@[simp] lemma SigMap.extend_right_left {σ τ η : Signature S} (h : SigMap σ τ)
    {s : S} (w : σ.Idx s) :
    SigMap.extend_right (η := η) h s (Idx.left w) = Idx.left (h s w) := rfl

@[simp] lemma SigMap.extend_right_right {σ τ η : Signature S} (h : SigMap σ τ)
    {s : S} (w : η.Idx s) :
    SigMap.extend_right (η := η) h s (Idx.right w) = Idx.right w := rfl

def SigMap.extend_left {σ τ η : Signature S} (h : SigMap σ τ)
  : SigMap (η ⨯ σ) (η ⨯ τ) :=
   fun s => fun v =>
      match v with
      | .left w  =>
          Idx.left w
      | .right w =>
          Idx.right ((h s) w)

@[simp] lemma SigMap.extend_left_left {σ τ η : Signature S} (h : SigMap σ τ)
    {s : S} (w : η.Idx s) :
    SigMap.extend_left (η := η) h s (Idx.left w) = Idx.left w := rfl

@[simp] lemma SigMap.extend_left_right {σ τ η : Signature S} (h : SigMap σ τ)
    {s : S} (w : σ.Idx s) :
    SigMap.extend_left (η := η) h s (Idx.right w) = Idx.right (h s w) := rfl

/-- Canonical Extension of SigEmbeds by adding a factor on the right.
    The mapping maps variables on the left by h and variables on the
    right embed in the same position, relative to the right factor. -/
def SigEmbed.extend_right {σ τ η : Signature S} (h : SigEmbed σ τ)
  : SigEmbed (σ ⨯ η) (τ ⨯ η) :=
  { toFun := SigMap.extend_right h
  , inj' := by
      intro s x y hxy
      cases x <;> cases y <;>
        simp only [SigMap.extend_right, Idx.left.injEq, reduceCtorEq, Idx.right.injEq ] at hxy
      case left =>
        apply h.inj' at hxy
        simp [hxy];
      case right => simp [hxy]
  }

/-- Canonical Extension of SigEquivs by adding a factor on the right.
    The mapping maps variables on the left by h and variables on the
    right embed in the same position, relative to the right factor. -/
def SigEquiv.extend_right {σ τ η : Signature S} (h : SigEquiv σ τ)
  : SigEquiv (σ ⨯ η) (τ ⨯ η) :=
  { toFun := SigMap.extend_right h,
    invFun := fun s => fun v =>
      match v with
      |.left w => Idx.left (h.invFun s w)
      |.right w => Idx.right w,
    left_inv' := by
      intro s v
      match v with
      |.left w => simp [SigMap.extend_right]
      |.right w => rfl
    right_inv' := by
      intro s v
      match v with
      |.left w => simp [SigMap.extend_right]
      |.right w => rfl
  }

/-- Canonical Extension of SigEquivs by adding a factor on the left.
    The mapping maps variables on the right by h and variables on the
    left embed in the same position, relative to the right factor. -/
def SigEquiv.extend_left {σ τ η : Signature S} (h : SigEquiv σ τ)
  : SigEquiv (η ⨯ σ) (η ⨯ τ) :=
  { toFun := SigMap.extend_left h,
    invFun := fun s => fun v =>
      match v with
      |.left w => Idx.left w
      |.right w => Idx.right (h.invFun s w),
    left_inv' := by
      intro s v
      match v with
      |.left w => rfl
      |.right w => simp [SigMap.extend_left]
    right_inv' := by
      intro s v
      match v with
      |.left w => rfl
      |.right w => simp [SigMap.extend_left]
  }

/-- The Inclusion map `σ.Idx → (σ ⨯ τ).Idx` -/
abbrev SigMap.incl_left {σ τ : Signature S} : SigMap σ (σ ⨯ τ) :=
  fun _ => fun v => Idx.left v

/-- The Inclusion map `σ.Idx → (τ ⨯ σ).Idx` -/
abbrev SigMap.incl_right {σ τ : Signature S} : SigMap σ (τ ⨯ σ) :=
  fun _ => fun v => Idx.right v

@[simp] lemma SigMap.incl_left_apply {σ τ : Signature S} {s : S} (w : σ.Idx s) :
    SigMap.incl_left (σ := σ) (τ := τ) s w = Idx.left w := rfl

@[simp] lemma SigMap.incl_right_apply {σ τ : Signature S} {s : S} (w : σ.Idx s) :
    SigMap.incl_right (σ := σ) (τ := τ) s w = Idx.right w := rfl

/-- The Inclusion embedding `σ.Idx → (σ ⨯ τ).Idx` -/
abbrev SigEmbed.incl_left {σ τ : Signature S} : SigEmbed σ (σ ⨯ τ) :=
  {toFun := SigMap.incl_left,
    inj' := by
    intro t v w h
    cases v <;> cases w <;> simp_all only [Idx.left.injEq, Idx.right.injEq]
  }

/-- The Inclusion map `σ.Idx → (τ ⨯ σ).Idx` -/
abbrev SigEmbed.incl_right {σ τ : Signature S} : SigEmbed σ (τ ⨯ σ) :=
  {toFun := SigMap.incl_right,
    inj' := by
    intro t v w h
    cases v <;> cases w <;> simp_all only [Idx.right.injEq, Idx.left.injEq]
  }

@[simp]
lemma SigMap.idExtend {σ : Signature S} (η : Signature S) :
  (Id (σ := σ)).extend_right = Id (σ := σ ⨯ η) := by
  ext
  simp_all only [extend_right, Id, Fam.id, id_eq]
  split
  next v vσ => simp_all only
  next v vη => simp_all only

@[simp]
lemma SigEmbed.idExtend {σ : Signature S} (η : Signature S) :
  (Id (σ := σ)).extend_right = Id (σ := σ ⨯ η) := by
  ext; unfold Id extend_right SigMap.extend_right; simp only [SigMap.Id_apply]
  split
  next v vσ => simp_all only
  next v vη => simp_all only

@[simp]
lemma SigEquiv.idExtend {σ : Signature S} (η : Signature S) :
  (Id (σ := σ)).extend_right = Id (σ := σ ⨯ η) := by
  ext; unfold Id extend_right SigMap.extend_right; simp only [SigMap.Id_apply]
  split
  next v vσ => simp_all only
  next v vη => simp_all only

@[simp]
lemma SigMap.extend_right_comp
  {σ τ η ξ : Signature S}
  (hστ : SigMap σ τ) (hτη : SigMap τ η) :
  ∀ s : S,
    SigMap.extend_right (η := ξ) hτη s ∘ (SigMap.extend_right hστ s)
      = SigMap.extend_right (hτη ∘ₛ hστ) s := by
  intro s
  ext v
  cases v with
  | left w => simp [SigMap.extend_right]
  | right w => simp [SigMap.extend_right]

@[simp]
lemma SigMap.extend_left_comp
  {σ τ η ξ : Signature S}
  (hστ : SigMap σ τ) (hτη : SigMap τ η) :
  ∀ s : S,
    SigMap.extend_left (η := ξ) hτη s ∘ (SigMap.extend_left hστ s)
      = SigMap.extend_left (hτη ∘ₛ hστ) s := by
  intro s
  ext v
  cases v with
  | left w => simp [SigMap.extend_left]
  | right w => simp [SigMap.extend_left]

/-- Rotate Idxs of shape `τ ⨯ σ` to those of `σ ⨯ τ` -/
def SigMap.comm {σ τ : Signature S} :
    SigMap (τ ⨯ σ) (σ ⨯ τ) :=
fun _ v =>
  match v with
  | Idx.left w  => Idx.right w
  | Idx.right w => Idx.left w

@[simp] lemma SigMap.comm_comm {s : S}
  {σ τ : Signature S} {v : (σ ⨯ τ).Idx s} :
  (comm (σ := σ) (τ := τ) s) (comm (σ := τ) (τ := σ) s v) = v := by
  cases v
  case left => rfl
  case right => rfl

@[simp] lemma SigMap.comm_apply_left
  (σ τ : Signature S) {s} (w : τ.Idx s) :
  comm (σ := σ) (τ := τ) s (Idx.left w) = Idx.right w := rfl

@[simp] lemma SigMap.comm_apply_right
  (σ τ : Signature S) {s} (w : σ.Idx s) :
  comm (σ := σ) (τ := τ) s (Idx.right w) = Idx.left w := rfl

lemma var_eq {s : S} {v : ⦃s⦄.Idx s} : v = Idx.var := by
  cases v
  case var => rfl

end variable_maps

section var_equivs
/- This section builds a large class of SigMaps based on equivalences of Signature's.
  The goal is to develop a general mapping from any `PEquiv σ τ` to a `SigEquiv σ τ`,
  which will allow us to associate signatures of formulas and terms somewhat painlessly.

  This section is just recapitulating all of the patterns we needed to build up PEquiv.
  Maybe there is a less verbose way to do this...
-/
namespace SigMap

open Signature

/--
Associate a product from left to write
-/
def assocL (σ τ η : Signature S) : SigMap ((σ ⨯ τ) ⨯ η) (σ ⨯ (τ ⨯ η)) :=
  fun _ v =>
    match v with
    | Idx.left (Idx.left  vσ) =>
        Idx.left vσ
    | Idx.left (Idx.right vτ) =>
        Idx.right (Idx.left vτ)
    | Idx.right vη =>
        Idx.right (Idx.right vη)

/--
Associate a product from right to left
-/
def assocR (σ τ η : Signature S) : SigMap (σ ⨯ (τ ⨯ η)) ((σ ⨯ τ) ⨯ η) :=
  fun _ v =>
    match v with
    | Idx.left vσ =>
        Idx.left (Idx.left vσ)
    | Idx.right (Idx.left vτ) =>
        Idx.left (Idx.right vτ)
    | Idx.right (Idx.right vη) =>
        Idx.right vη

lemma assocL_assocR_left_inv (σ τ η : Signature S) :
    ∀ s (v : Idx ((σ ⨯ τ) ⨯ η) s),
      assocR (S := S) σ τ η s (assocL (S := S) σ τ η s v) = v :=
by
  intro s v; cases v with
  | left w =>
      cases w with
      | left vσ   => rfl
      | right vτ  => rfl
  | right w    => rfl

lemma assocL_assocR_right_inv (σ τ η : Signature S) :
    ∀ s (v : Idx (σ ⨯ (τ ⨯ η)) s),
      assocL (S := S) σ τ η s (assocR (S := S) σ τ η s v) = v :=
by
  intro s v; cases v with
  | left w => rfl
  | right w =>
      cases w with
      | left vτ  => rfl
      | right vη => rfl

/-
These are a very tedious set of nil-cancelling maps, needed for completeness to construct
our general map `PEquiv → SigEquiv`.

It may be potentially less messy to just in-line these proofs into the eventual defintions
of their associated SigEquivs?
-/

/-- Cancel off nil factors. -/
def nil_left {σ : Signature S} :
    SigMap (⦃⦄ ⨯ σ) σ :=
  fun _ v =>
    match v with
    | Idx.right vσ => vσ

/-- `nil.Idx.right` gives a mapping to add nil factors -/
def nil_left_inv {σ : Signature S} :
    SigMap σ (⦃⦄ ⨯ σ) :=
  fun _ v => Idx.right v

lemma nil_left_left_inv {σ : Signature S} :
    ∀ s (v : Idx (⦃⦄ ⨯ σ) s),
      nil_left_inv (S := S) s (nil_left (S := S) s v) = v :=
by
  intro s v
  cases v with
  | right vσ => rfl
  | left vτ => cases vτ

lemma nil_left_right_inv {σ : Signature S} :
    ∀ s (v : Idx σ s),
      nil_left (S := S) s (nil_left_inv (S := S) s v) = v :=
by
  intro s v; rfl

def nil_right {σ : Signature S} :
    SigMap (σ ⨯ ⦃⦄) σ :=
  fun _ v =>
    match v with
    | Idx.left vσ => vσ

def nil_right_inv {σ : Signature S} :
    SigMap σ (σ ⨯ ⦃⦄) :=
  fun _ v => Idx.left v

lemma nil_right_left_inv {σ : Signature S} :
    ∀ s (v : Idx (σ ⨯ ⦃⦄) s),
      nil_right_inv (S := S) s (nil_right (S := S) s v) = v :=
by
  intro s v
  cases v with
  | left vσ => rfl
  | right vτ => cases vτ

lemma nil_right_right_inv {σ : Signature S} :
    ∀ s (v : Idx σ s),
      nil_right (S := S) s (nil_right_inv (S := S) s v) = v :=
by
  intro s v; rfl

end SigMap

namespace SigEquiv

variable {σ τ : Signature S}

open Signature SigMap

/-- Lifting SigMap.assocL to a SigEquiv. -/
def assocL (σ τ η : Signature S) :
    SigEquiv ((σ ⨯ τ) ⨯ η) (σ ⨯ (τ ⨯ η)) :=
{ toFun     := SigMap.assocL σ τ η
  , invFun  := SigMap.assocR σ τ η
  , left_inv'  := SigMap.assocL_assocR_left_inv  σ τ η
  , right_inv' := SigMap.assocL_assocR_right_inv σ τ η }

/-- Lifting SigMap.assocR to a SigEquiv. -/
def assocR (σ τ η : Signature S) :
    SigEquiv (σ ⨯ (τ ⨯ η)) ((σ ⨯ τ) ⨯ η) :=
{ toFun     := SigMap.assocR σ τ η
  , invFun  := SigMap.assocL σ τ η
  , left_inv'  := SigMap.assocL_assocR_right_inv σ τ η
  , right_inv' := SigMap.assocL_assocR_left_inv  σ τ η }

/-- Alias for SigEquiv.Id -/
@[simp]
abbrev refl (σ : Signature S) : SigEquiv σ σ := SigEquiv.Id

/-- Symmetry of SigEquivs -/
@[simp]
def symm (e : SigEquiv σ τ) : SigEquiv τ σ :=
  Fam.MSEquiv.symm e

/-- Rotate Idxs of shape `τ ⨯ σ` to those of `σ ⨯ τ` -/
def comm {σ τ : Signature S} :
    SigEquiv (σ ⨯ τ) (τ ⨯ σ) :=
  { toFun     := SigMap.comm
  , invFun  := SigMap.comm
  , left_inv'  := fun _ _ => SigMap.comm_comm
  , right_inv' := fun _ _ => SigMap.comm_comm}

/-- SigEquivs are closed under composition -/
@[simp]
def trans {σ τ η : Signature S} (e₁ : SigEquiv σ τ) (e₂ : SigEquiv τ η) : SigEquiv σ η :=
  Fam.MSEquiv.trans e₁ e₂

/-- SigEquiv for `nil ⨯ σ ≃ σ`. -/
def nilLeft (σ : Signature S) :
    SigEquiv (nil ⨯ σ) σ :=
{ toFun     := nil_left
  , invFun  := nil_left_inv
  , left_inv'  := nil_left_left_inv
  , right_inv' := nil_left_right_inv  }

/-- SigEquiv for `σ ⨯ nil ≃ σ`. -/
def nilRight (σ : Signature S) :
    SigEquiv (σ ⨯ nil) σ :=
{ toFun     := nil_right
  , invFun  := nil_right_inv
  , left_inv'  := nil_right_left_inv
  , right_inv' := nil_right_right_inv }

/-- Canonical mapping from any PEquiv to a SigEquiv -/
def fromPEquiv {S : Type u} :
    {σ τ : Signature S} → PEquiv σ τ → SigEquiv σ τ
  | _, _, (@PEquiv.refl _ σ )  =>
      SigEquiv.refl (σ := σ)
  | _, _, PEquiv.symm e =>
      (SigEquiv.fromPEquiv e).symm
  | _, _, PEquiv.trans e₁ e₂ =>
      (SigEquiv.fromPEquiv e₁).trans (SigEquiv.fromPEquiv e₂)
  | _, _, PEquiv.assocL σ τ η =>
      SigEquiv.assocL σ τ η
  | _, _, PEquiv.assocR σ τ η =>
      SigEquiv.assocR σ τ η
  | _, _, PEquiv.nil_left σ =>
      SigEquiv.nilLeft σ
  | _, _, PEquiv.nil_right σ =>
      SigEquiv.nilRight σ
  | _, _, PEquiv.prod_congr_left e =>
      SigEquiv.extend_right (SigEquiv.fromPEquiv e)
  | _, _, PEquiv.prod_congr_right e =>
      SigEquiv.extend_left (SigEquiv.fromPEquiv e)

end SigEquiv
end var_equivs

open Idx

section one_sort
/-! ## OneSort Signatures

A `OneSort s σ` is a witness that the signature `σ` contains only variables of sort `s`.
This is useful for working with single-sorted fragments within a multi-sorted logic,
allowing us to treat multi-sorted signatures as if they were single-sorted when all
variables happen to share the same sort.

### Key Results
- `OneSort.getIdx_sort`: Any variable index in a OneSort signature has the designated sort
- `OneSort.oneSort_iff_toList`: Characterization via the flattened list of sorts
- `OneSort.SigEquivFin`: For OneSort `σ`, we have `σ.Idx s ≃ Fin σ.length`
- `OneSort.fibredMapEquiv`: Fibered maps `σ.Idx →ₛ α` are equivalent to simple maps `σ.Idx s → α s`

### Typical Use Cases
- Quantifying over a block of same-sort variables (e.g., `∀ x₁ x₂ ... xₙ`)
- Simplifying proofs when all bound variables have the same sort
- Converting between multi-sorted and single-sorted representations
-/

/-- A witness that signature `σ` contains only variables of sort `s`. -/
inductive OneSort (s : S) : Signature S → Type _
  | nil : OneSort s .nil
  | of  : OneSort s ⦃s⦄
  | prod {σ τ : Signature S} (hσ : OneSort s σ) (hτ : OneSort s τ) : OneSort s (σ ⨯ τ)

namespace OneSort

variable {s : S}

/-- Helper: If a signature is OneSort s, its list representation only contains s. -/
lemma toList_mem {σ : Signature S} (h : OneSort s σ) :
    ∀ x ∈ σ.toList, x = s := by
  induction h with
  | nil => simp only [toList, List.not_mem_nil, IsEmpty.forall_iff, implies_true]
  | of => simp only [toList, List.mem_cons, List.not_mem_nil, or_false, imp_self, implies_true]
  | prod _ _ ihσ ihτ =>
    intro x hx
    simp only [Signature.toList, List.mem_append] at hx
    cases hx
    · apply ihσ; simp_all only
    · apply ihτ; simp_all only

/-- Any variable in a OneSort signature has sort s. -/
theorem getIdx_sort {σ : Signature S} (h : OneSort s σ) (i : Fin σ.length) :
    (σ.getIdx i).1 = s := by
  rw [Signature.getIdx_fst]
  apply toList_mem h
  apply List.get_mem

/-- Characterization: `σ` is OneSort iff every sort in `toList σ` equals `s`. -/
lemma oneSort_iff_toList {s : S} {σ : Signature S} :
  Nonempty (OneSort s σ) ↔ (∀ t ∈ σ.toList, t = s) := by
  induction σ with
  | nil =>
    simp only [toList, List.not_mem_nil, IsEmpty.forall_iff, implies_true, iff_true]
    constructor
    apply OneSort.nil
  | of a =>
    rw [toList]
    constructor
    · intro h
      cases h
      case intro v =>
      cases v
      simp
    · intro h
      simp only [List.mem_cons, List.not_mem_nil, or_false, h]
      constructor
      exact OneSort.of
  | prod σ τ hσ hτ =>
    constructor
    case mp =>
      intro h t ht
      simp only [toList, List.mem_append] at ht
      cases ht
      case inl ht =>
        cases h
        case intro v =>
          cases v
          case prod v₁ v₂ =>
          exact hσ.mp (by constructor; exact v₁) t ht
      case inr ht =>
        cases h
        case intro v =>
          cases v
          case prod v₁ v₂ =>
          exact hτ.mp (by constructor; exact v₂) t ht
    case mpr =>
      intro h
      constructor
      apply OneSort.prod
      case hσ =>
        apply Nonempty.some
        apply hσ.mpr
        intro t ht
        apply h
        simp only [toList, List.mem_append, ht, true_or]
      case hτ =>
        apply Nonempty.some
        apply hτ.mpr
        intro t ht
        apply h
        simp only [toList, List.mem_append, ht, or_true]

noncomputable
def oneSort_of_toList {s : S} {σ : Signature S}
  (h : ∀ t ∈ σ.toList, t = s) : OneSort s σ :=
  ((oneSort_iff_toList (s := s) (σ := σ)).2 h).some

lemma toList_all_eq_of_oneSort {s : S} {σ : Signature S} (h : OneSort s σ) :
  ∀ t ∈ σ.toList, t = s :=
  (oneSort_iff_toList (s := s) (σ := σ)).1 (.intro h)

/-- A signature built from `n` copies of sort `s` is trivially OneSort. -/
noncomputable
def oneSort_fromList_replicate (s : S) (n : ℕ) :
    OneSort s (Signature.fromList (List.replicate n s)) := by
  apply oneSort_of_toList (s := s) (σ := Signature.fromList (List.replicate n s))
  intro t ht
  simpa [Signature.toList_fromList] using
    (List.eq_of_mem_replicate (by simpa [Signature.toList_fromList] using ht))

/-- Enumerate all variables in a OneSort signature as a list of `σ.Idx s`. -/
def OneSortIdxList {σ} : (OneSort s σ) → List (σ.Idx s) :=
fun h =>
  match h with
  | nil => []
  | of => [Idx.var]
  | prod hσ hτ => (OneSortIdxList hσ).map left ++ (OneSortIdxList hτ).map right

/-- In a OneSort signature, every variable must have sort `s`. -/
@[simp]
lemma sort_is_s {t : S} {σ : Signature S} (h : OneSort s σ) (v : σ.Idx t) : t = s := by
  induction σ
  case nil => cases v
  case of s' =>
    cases h ; cases v ; simp_all only
  case prod σ τ ihσ ihτ =>
    cases h
    case prod hσ hτ =>
      cases v
      case left w =>
        exact ihσ hσ w
      case right w =>
        exact ihτ hτ w

/-- Inverse of `Idx.toFin` for OneSort signatures: maps `Fin σ.length` back to `σ.Idx s`. -/
def toFinInv : ∀ {σ : Signature S}, OneSort s σ → Fin σ.length → σ.Idx s
  | .nil,     .nil,     i => nomatch i
  | .of _,    .of,      _ => Signature.Idx.var
  | .prod σ τ, .prod hσ hτ, i =>
      if hi : (i : Nat) < σ.length then
        Signature.Idx.left (toFinInv hσ ⟨(i : Nat), hi⟩)
      else
        let hle : σ.length ≤ (i : Nat) := Nat.le_of_not_gt hi
        let hj : (i : Nat) - σ.length < τ.length :=
          nat_lt_lemma (n := σ.length) (m := (i : Nat)) (k := τ.length) i.is_lt hle
        Signature.Idx.right (toFinInv hτ ⟨(i : Nat) - σ.length, hj⟩)

lemma toFin_surj {σ : Signature S} (h : OneSort s σ) :
    Function.Surjective (toFin (σ := σ) (s := s)) :=
  by
    induction h with
    | nil =>
        intro i
        cases i with
        | mk n hn =>
          cases hn
    | of =>
        intro i
        refine ⟨(Signature.Idx.var : ⦃s⦄.Idx s), ?_⟩
        cases i with
        | mk n hn =>
          have hn0 : n = 0 := Nat.eq_of_lt_succ_of_not_lt hn (by simp)
          ext
          simp [Signature.Idx.toFin, hn0]
    | @prod σ τ hσ hτ ihσ ihτ =>
        intro i
        by_cases hi : (i : Nat) < σ.length
        · rcases ihσ ⟨(i : Nat), hi⟩ with ⟨vσ, hvσ⟩
          refine ⟨Signature.Idx.left vσ, ?_⟩
          calc
            Signature.Idx.toFin (σ := σ ⨯ τ) (s := s) (Signature.Idx.left vσ)
                = Signature.injLeft σ τ (Signature.Idx.toFin (σ := σ) (s := s) vσ) := by
                    rfl
            _ = Signature.injLeft σ τ ⟨(i : Nat), hi⟩ := by
                  simp [hvσ]
            _ = i := by
                  ext
                  rfl
        · have hle : σ.length ≤ (i : Nat) := Nat.le_of_not_gt hi
          have hj : (i : Nat) - σ.length < τ.length := by
            have h' := Nat.sub_lt_sub_right (b := (σ ⨯ τ).length) hle
            simp_all [Signature.length]
          let j : Fin τ.length := ⟨(i : Nat) - σ.length, hj⟩
          rcases ihτ j with ⟨vτ, hvτ⟩
          refine ⟨Signature.Idx.right vτ, ?_⟩
          calc
            Signature.Idx.toFin (σ := σ ⨯ τ) (s := s) (Signature.Idx.right vτ)
                = Signature.injRight σ τ (Signature.Idx.toFin (σ := τ) (s := s) vτ) := by
                    rfl
            _ = Signature.injRight σ τ j := by
                  simp [hvτ]
            _ = i := by
                  ext
                  simp [Signature.injRight, j, Nat.add_sub_of_le hle]

/-- For a OneSort signature, `σ.Idx s` is equivalent to `Fin σ.length`.
    This is the main structural result: all variables can be numbered 0, 1, ..., n-1. -/
noncomputable def SigEquivFin {σ : Signature S} (h : OneSort s σ) :
    σ.Idx s ≃ (Fin σ.length)  :=
  Equiv.ofBijective
    (fun v => (Signature.Idx.toFin (σ := σ) (s := s) v))
    ⟨Signature.Idx.toFin_inj (σ := σ) (s := s),
     toFin_surj (σ := σ) (s := s) h⟩

/-- Restrict a fibered map to just the `s`-component. -/
def restrict {α : S → Type*} {σ : Signature S} (g : σ.Idx →ₛ α) : σ.Idx s → α s :=
  g s

/-- Extend a simple map `σ.Idx s → α s` to a fibered map `σ.Idx →ₛ α`. -/
def extend {α : S → Type*} {σ : Signature S} (h : OneSort s σ) (f : σ.Idx s → α s) : σ.Idx →ₛ α :=
  fun t v =>
    by
      cases (OneSort.sort_is_s (s := s) (σ := σ) h (v := v)) with
      | refl => exact f v

@[simp] lemma restrict_extend {α : S → Type*} {σ : Signature S}
    (h : OneSort s σ) (f : σ.Idx s → α s) :
    restrict (σ := σ) (α := α) (extend (σ := σ) (α := α) h f) = f := by
  funext v
  simp [restrict, extend]

@[simp] lemma extend_restrict {α : S → Type*} {σ : Signature S}
    (h : OneSort s σ) (g : σ.Idx →ₛ α) :
    extend (σ := σ) (α := α) h (restrict (σ := σ) (α := α) g) = g := by
  funext t v
  cases (OneSort.sort_is_s (s := s) (σ := σ) h (v := v)) with
  | refl => rfl

/-- For OneSort signatures, fibered maps are equivalent to simple maps.
    This simplifies working with variable assignments when all variables share a sort. -/
def fibredMapEquiv {α : S → Type*} {σ : Signature S} (h : OneSort s σ) :
    (σ.Idx →ₛ α) ≃ (σ.Idx s → α s) :=
{ toFun := restrict (σ := σ) (α := α)
, invFun := extend (σ := σ) (α := α) h
, left_inv := extend_restrict (σ := σ) (α := α) h
, right_inv := restrict_extend (σ := σ) (α := α) h
}

/-- OneSort signatures have finitely many variables at sort `s`. -/
noncomputable instance oneSortFinType {σ : Signature S} {s : S}
    (h : OneSort s σ) : Fintype (σ.Idx s) :=
  Fintype.ofEquiv (Fin σ.length) (SigEquivFin (σ := σ) (s := s) h).symm

/-- The number of `s`-variables equals the signature length (as a natural number). -/
theorem card_Idx_eq_length {σ : Signature S} (h : OneSort s σ) :
    (oneSortFinType h).card (σ.Idx s) = σ.length := by
  classical
  let e := SigEquivFin (σ := σ) (s := s) h
  letI : Fintype (σ.Idx s) := Fintype.ofEquiv (Fin σ.length) e.symm
  simpa using (Fintype.card_congr e)

/-- The cardinality of `s`-variables equals the signature length (as a cardinal). -/
theorem mk_Idx_eq_length {σ : Signature S} (h : OneSort s σ) :
    Cardinal.mk (σ.Idx s) = σ.length := by
  classical
  simp only [(Cardinal.mk_congr
      ((SigEquivFin (σ := σ) (s := s) h).trans Equiv.ulift.{u, 0}.symm)),
    Cardinal.mk_fintype, Fintype.card_ulift, Fintype.card_fin]

end OneSort

end one_sort

namespace SigEquiv

variable {S : Type u}

def prod_congr {σ σ' τ τ' : Signature S} (e1 : SigEquiv σ σ') (e2 : SigEquiv τ τ') :
    SigEquiv (σ ⨯ τ) (σ'.prod τ') :=
  SigEquiv.extend_left e2 |>.trans (SigEquiv.extend_right e1)

end SigEquiv

end Signature
end MSFirstOrder
