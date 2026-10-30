import Mathlib.Analysis.Complex.Basic
import HeckeSkeleton.LowHybrid.CommonTactics

/-!
# Frozen valuations and the full cube

This module proves the arithmetic and finite-reindexing core of the frozen-cube
argument.  A valuation vector is a function from a prime index type to `ℕ`.
No arithmetic structure is assigned to the prime index type.  In particular,
this file does not introduce a replacement for `ExteriorIdeal`.

The original ideal-valued interface still has to transport these results
through its prime valuations and establish the symbol and local-table inputs.
-/

namespace HeckeSkeleton.LowFrozenCube

open scoped BigOperators Classical

/-! ## Canonical local frozen exponent -/

/-- The nonzero local table allows precisely residues zero and one modulo three. -/
def AdmissibleExponent (e : ℕ) : Prop := e % 3 = 0 ∨ e % 3 = 1

/-- Zero is frozen at zero; positive residues one and zero are frozen at one and three. -/
def frozenMin (e : ℕ) : ℕ :=
  if e = 0 then 0 else if e % 3 = 1 then 1 else 3

/-- The exponent of the cube remaining after the minimum exponent is frozen. -/
def frozenCubeExp (e : ℕ) : ℕ := (e - frozenMin e) / 3

@[simp] theorem frozenMin_zero : frozenMin 0 = 0 := by
  simp [frozenMin]

@[simp] theorem frozenCubeExp_zero : frozenCubeExp 0 = 0 := by
  simp [frozenCubeExp]

theorem frozenMin_cases (e : ℕ) :
    frozenMin e = 0 ∨ frozenMin e = 1 ∨ frozenMin e = 3 := by
  unfold frozenMin
  split_ifs <;> simp

@[simp] theorem frozenMin_eq_zero_iff (e : ℕ) :
    frozenMin e = 0 ↔ e = 0 := by
  unfold frozenMin
  split_ifs <;> simp_all

theorem frozenMin_le (e : ℕ) (he : AdmissibleExponent e) :
    frozenMin e ≤ e := by
  unfold AdmissibleExponent at he
  unfold frozenMin
  split_ifs <;> omega

/-- Exact local decomposition.  The residue restriction is essential. -/
theorem frozenExponent_decomposition (e : ℕ) (he : AdmissibleExponent e) :
    e = frozenMin e + 3 * frozenCubeExp e := by
  unfold AdmissibleExponent at he
  simp only [frozenCubeExp, frozenMin]
  split_ifs <;> omega

/-- A zero base cannot hide a nontrivial cube in the canonical decomposition. -/
theorem frozenCubeExp_eq_zero_of_base_zero {e : ℕ} (he : frozenMin e = 0) :
    frozenCubeExp e = 0 := by
  have h := (frozenMin_eq_zero_iff e).mp he
  simpa [h]

/-- The allowed canonical pairs are `(1,x)`, `(3,x)`, and `(0,0)`. -/
def CanonicalFrozenPair (m x : ℕ) : Prop :=
  m = 1 ∨ m = 3 ∨ (m = 0 ∧ x = 0)

theorem frozenPair_canonical (e : ℕ) :
    CanonicalFrozenPair (frozenMin e) (frozenCubeExp e) := by
  rcases frozenMin_cases e with h | h | h
  · exact Or.inr (Or.inr ⟨h, frozenCubeExp_eq_zero_of_base_zero h⟩)
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

/-- Uniqueness also records the special treatment of zero. -/
theorem frozenExponent_unique {e m x : ℕ}
    (hc : CanonicalFrozenPair m x) (he : e = m + 3 * x) :
    m = frozenMin e ∧ x = frozenCubeExp e := by
  unfold CanonicalFrozenPair at hc
  simp only [frozenCubeExp, frozenMin]
  split_ifs <;> omega

theorem canonicalPair_admissible {e m x : ℕ}
    (hc : CanonicalFrozenPair m x) (he : e = m + 3 * x) :
    AdmissibleExponent e := by
  unfold CanonicalFrozenPair at hc
  unfold AdmissibleExponent
  omega

/-! ## Valuation vectors and fixed supports -/

variable {ι : Type*}

/-- The vector vanishes away from the fixed finite set. -/
def SupportedOn (s : Finset ι) (v : ι → ℕ) : Prop :=
  ∀ p, p ∉ s → v p = 0

/-- The vector vanishes on the fixed finite set. -/
def AvoidsSupport (s : Finset ι) (v : ι → ℕ) : Prop :=
  ∀ p, p ∈ s → v p = 0

/-- Disjointness of prime supports, expressed solely in valuations. -/
def DisjointValuations (u v : ι → ℕ) : Prop :=
  ∀ p, u p = 0 ∨ v p = 0

def frozenBase (v : ι → ℕ) : ι → ℕ := fun p => frozenMin (v p)

def frozenCube (v : ι → ℕ) : ι → ℕ := fun p => frozenCubeExp (v p)

theorem frozenValuation_decomposition (v : ι → ℕ)
    (hv : ∀ p, AdmissibleExponent (v p)) :
    v = fun p => frozenBase v p + 3 * frozenCube v p := by
  funext p
  exact frozenExponent_decomposition (v p) (hv p)

theorem frozenValuation_unique {v a x : ι → ℕ}
    (hc : ∀ p, CanonicalFrozenPair (a p) (x p))
    (he : ∀ p, v p = a p + 3 * x p) :
    a = frozenBase v ∧ x = frozenCube v := by
  constructor
  · funext p
    exact (frozenExponent_unique (hc p) (he p)).1
  · funext p
    exact (frozenExponent_unique (hc p) (he p)).2

theorem frozenBase_supported {s : Finset ι} {v : ι → ℕ}
    (hv : SupportedOn s v) : SupportedOn s (frozenBase v) := by
  intro p hp
  simp [frozenBase, hv p hp]

theorem frozenCube_supported {s : Finset ι} {v : ι → ℕ}
    (hv : SupportedOn s v) : SupportedOn s (frozenCube v) := by
  intro p hp
  simp [frozenCube, hv p hp]

theorem frozenBase_support_exact (v : ι → ℕ) (p : ι) :
    frozenBase v p ≠ 0 ↔ v p ≠ 0 := by
  exact not_congr (frozenMin_eq_zero_iff (v p))

section Decidable

variable [DecidableEq ι]

/-- The complete prime-power part supported on the fixed primes. -/
def supportedPart (s : Finset ι) (v : ι → ℕ) : ι → ℕ :=
  fun p => if p ∈ s then v p else 0

/-- The complementary prime-power part. -/
def awayPart (s : Finset ι) (v : ι → ℕ) : ι → ℕ :=
  fun p => if p ∈ s then 0 else v p

theorem supportedPart_supported (s : Finset ι) (v : ι → ℕ) :
    SupportedOn s (supportedPart s v) := by
  intro p hp
  simp [supportedPart, hp]

theorem awayPart_avoids (s : Finset ι) (v : ι → ℕ) :
    AvoidsSupport s (awayPart s v) := by
  intro p hp
  simp [awayPart, hp]

theorem fullCube_decomposition (s : Finset ι) (v : ι → ℕ) :
    v = fun p => supportedPart s v p + awayPart s v p := by
  funext p
  by_cases hp : p ∈ s <;> simp [supportedPart, awayPart, hp]

/-- This is the uniqueness of `b = x n'` with `x` supported on `f₀`
and `n'` prime to `f₀`. -/
theorem fullCube_unique {s : Finset ι} {v x n : ι → ℕ}
    (hx : SupportedOn s x) (hn : AvoidsSupport s n)
    (hv : ∀ p, v p = x p + n p) :
    x = supportedPart s v ∧ n = awayPart s v := by
  constructor
  · funext p
    by_cases hp : p ∈ s
    · simpa [supportedPart, hp, hn p hp] using (hv p).symm
    · simp [supportedPart, hp, hx p hp]
  · funext p
    by_cases hp : p ∈ s
    · simp [awayPart, hp, hn p hp]
    · simpa [awayPart, hp, hx p hp] using (hv p).symm

theorem disjoint_supported_of_avoids {s : Finset ι} {P x : ι → ℕ}
    (hP : AvoidsSupport s P) (hx : SupportedOn s x) :
    DisjointValuations P x := by
  intro p
  by_cases hp : p ∈ s
  · exact Or.inl (hP p hp)
  · exact Or.inr (hx p hp)

theorem disjoint_add_right {P x n : ι → ℕ} :
    DisjointValuations P (fun p => x p + n p) ↔
      DisjointValuations P x ∧ DisjointValuations P n := by
  constructor
  · intro h
    constructor
    · intro p
      rcases h p with hp | hxn
      · exact Or.inl hp
      · right
        change x p + n p = 0 at hxn
        omega
    · intro p
      rcases h p with hp | hxn
      · exact Or.inl hp
      · right
        change x p + n p = 0 at hxn
        omega
  · rintro ⟨hx, hn⟩ p
    rcases hx p with hp | hxp
    · exact Or.inl hp
    · rcases hn p with hp | hnp
      · exact Or.inl hp
      · right
        change x p + n p = 0
        simp [hxp, hnp]

/-- Exact preservation of the moving collision mask under the full-cube merge.
The fixed support condition on `P` is part of the statement. -/
theorem fullCube_collision_mask {s : Finset ι} {P x n : ι → ℕ}
    (hP : AvoidsSupport s P) (hx : SupportedOn s x) :
    DisjointValuations P (fun p => x p + n p) ↔ DisjointValuations P n := by
  rw [disjoint_add_right]
  exact and_iff_right (disjoint_supported_of_avoids hP hx)

theorem overlap_not_disjoint {u v : ι → ℕ}
    (h : ∃ p, u p ≠ 0 ∧ v p ≠ 0) : ¬ DisjointValuations u v := by
  rintro hd
  obtain ⟨p, hu, hv⟩ := h
  exact (hd p).elim hu hv

/-- An overlapping row/mark or column/mark pair contributes exactly zero. -/
theorem overlap_mask_zero {u v : ι → ℕ} (z : ℂ)
    (h : ∃ p, u p ≠ 0 ∧ v p ≠ 0) :
    (if DisjointValuations u v then z else 0) = 0 := by
  classical
  simp [overlap_not_disjoint h]

/-! ## Primal whole-index marks vanish when a mark meets the row -/

/-- Product-form whole-index mark.  Slot primes need not be distinct. -/
def wholeIndexMark {σ : Type*} (slots : Finset σ) (prime : σ → ι)
    (v : ι → ℕ) : ℂ :=
  ∏ i ∈ slots, if 0 < v (prime i) then (1 : ℂ) else 0

/-- If a marked prime lies in the row support, the term vanishes before
reflection: the mark forces divisibility, which forces the row symbol to zero. -/
theorem wholeIndexMark_row_overlap_zero {σ : Type*}
    (slots : Finset σ) (prime : σ → ι) (row : ι → ℕ)
    (χ : (ι → ℕ) → ℂ)
    (hχ : ∀ v p, row p ≠ 0 → v p ≠ 0 → χ v = 0)
    (i : σ) (hi : i ∈ slots) (hrow : row (prime i) ≠ 0)
    (v : ι → ℕ) : χ v * wholeIndexMark slots prime v = 0 := by
  by_cases hv : v (prime i) = 0
  · have hm : wholeIndexMark slots prime v = 0 := by
      unfold wholeIndexMark
      apply Finset.prod_eq_zero hi
      simp [hv]
    simp [hm]
  · simp [hχ v (prime i) hrow hv]

/-- Weighted primal sums vanish for an overlapping tuple, without any
summability, squarefreeness, or restrictions on the complete index. -/
theorem sum_wholeIndexMark_row_overlap_zero {σ α : Type*}
    (slots : Finset σ) (prime : σ → ι) (row : ι → ℕ)
    (χ : (ι → ℕ) → ℂ)
    (hχ : ∀ v p, row p ≠ 0 → v p ≠ 0 → χ v = 0)
    (i : σ) (hi : i ∈ slots) (hrow : row (prime i) ≠ 0)
    (t : Finset α) (index : α → ι → ℕ) (weight : α → ℂ) :
    (∑ a ∈ t, weight a * χ (index a) * wholeIndexMark slots prime (index a)) = 0 := by
  apply Finset.sum_eq_zero
  intro a ha
  rw [mul_assoc, wholeIndexMark_row_overlap_zero slots prime row χ hχ i hi hrow]
  simp

/-! ## Finite reindexing, with no row variable in the new coefficient -/

def mergeCubePair (q : (ι → ℕ) × (ι → ℕ)) : ι → ℕ :=
  fun p => q.1 p + q.2 p

theorem mergeCubePair_injective_on (s : Finset ι)
    (t : Finset ((ι → ℕ) × (ι → ℕ)))
    (ht : ∀ q ∈ t, SupportedOn s q.1 ∧ AvoidsSupport s q.2) :
    Set.InjOn mergeCubePair (t : Set ((ι → ℕ) × (ι → ℕ))) := by
  intro q hq r hr hqr
  obtain ⟨hqx, hqn⟩ := fullCube_unique (ht q hq).1 (ht q hq).2
    (fun p => (rfl : mergeCubePair q p = q.1 p + q.2 p))
  obtain ⟨hrx, hrn⟩ := fullCube_unique (ht r hr).1 (ht r hr).2
    (fun p => (rfl : mergeCubePair r p = r.1 p + r.2 p))
  apply Prod.ext
  · rw [hqx, hrx, hqr]
  · rw [hqn, hrn, hqr]

/-- A coefficient indexed by `(c',x,n')` becomes a coefficient indexed by
`(c',b)` by its canonical support projections.  The equality permits arbitrary
coefficients and preserves the inherited finite support exactly. -/
theorem sum_fullCube_reindex {R : Type*} [AddCommMonoid R]
    (s : Finset ι) (t : Finset ((ι → ℕ) × (ι → ℕ)))
    (ht : ∀ q ∈ t, SupportedOn s q.1 ∧ AvoidsSupport s q.2)
    (G : (ι → ℕ) → (ι → ℕ) → R) :
    (∑ q ∈ t, G q.1 q.2) =
      ∑ b ∈ t.image mergeCubePair, G (supportedPart s b) (awayPart s b) := by
  classical
  rw [Finset.sum_image (mergeCubePair_injective_on s t ht)]
  apply Finset.sum_congr rfl
  intro q hq
  obtain ⟨hx, hn⟩ := fullCube_unique (ht q hq).1 (ht q hq).2
    (fun p => (rfl : mergeCubePair q p = q.1 p + q.2 p))
  rw [← hx, ← hn]

/-! ## The three fixed-row parts -/

/-- All complete prime powers of exponent at least two. -/
def powerfulRowPart (v : ι → ℕ) : ι → ℕ :=
  fun p => if 2 ≤ v p then v p else 0

/-- Valuation-one primes in the fixed label/puncture support. -/
def supportedRowPart (s : Finset ι) (v : ι → ℕ) : ι → ℕ :=
  fun p => if v p = 1 ∧ p ∈ s then 1 else 0

/-- The remaining valuation-one primes. -/
def residualRowPart (s : Finset ι) (v : ι → ℕ) : ι → ℕ :=
  fun p => if v p = 1 ∧ p ∉ s then 1 else 0

theorem row_decomposition (s : Finset ι) (v : ι → ℕ) :
    v = fun p => powerfulRowPart v p + supportedRowPart s v p +
      residualRowPart s v p := by
  funext p
  by_cases h2 : 2 ≤ v p
  · have h1 : v p ≠ 1 := by omega
    simp [powerfulRowPart, supportedRowPart, residualRowPart, h2, h1]
  · have h01 : v p = 0 ∨ v p = 1 := by omega
    rcases h01 with h0 | h1
    · simp [powerfulRowPart, supportedRowPart, residualRowPart, h0]
    · by_cases hp : p ∈ s <;>
        simp [powerfulRowPart, supportedRowPart, residualRowPart, h1, hp]

theorem supportedRowPart_squarefree (s : Finset ι) (v : ι → ℕ) (p : ι) :
    supportedRowPart s v p ≤ 1 := by
  simp only [supportedRowPart]
  split_ifs <;> omega

theorem residualRowPart_squarefree (s : Finset ι) (v : ι → ℕ) (p : ι) :
    residualRowPart s v p ≤ 1 := by
  simp only [residualRowPart]
  split_ifs <;> omega

theorem supportedRowPart_supported (s : Finset ι) (v : ι → ℕ) :
    SupportedOn s (supportedRowPart s v) := by
  intro p hp
  simp [supportedRowPart, hp]

theorem residualRowPart_avoids (s : Finset ι) (v : ι → ℕ) :
    AvoidsSupport s (residualRowPart s v) := by
  intro p hp
  simp [residualRowPart, hp]

theorem row_parts_pairwise_disjoint (s : Finset ι) (v : ι → ℕ) :
    DisjointValuations (powerfulRowPart v) (supportedRowPart s v) ∧
      DisjointValuations (powerfulRowPart v) (residualRowPart s v) ∧
      DisjointValuations (supportedRowPart s v) (residualRowPart s v) := by
  constructor
  · intro p
    simp only [powerfulRowPart, supportedRowPart]
    split_ifs <;> omega
  · constructor
    · intro p
      simp only [powerfulRowPart, residualRowPart]
      split_ifs <;> omega
    · intro p
      by_cases hp : p ∈ s
      · right
        simp [residualRowPart, hp]
      · left
        simp [supportedRowPart, hp]

end Decidable

/-! ## The square-times-squarefree-cube parametrization of powerful rows -/

def powerfulSquareExp (e : ℕ) : ℕ := (e - 3 * (e % 2)) / 2

def powerfulCubeDigit (e : ℕ) : ℕ := e % 2

theorem powerfulCubeDigit_squarefree (e : ℕ) : powerfulCubeDigit e ≤ 1 := by
  unfold powerfulCubeDigit
  omega

theorem powerfulExponent_decomposition (e : ℕ) (he : e = 0 ∨ 2 ≤ e) :
    e = 2 * powerfulSquareExp e + 3 * powerfulCubeDigit e := by
  unfold powerfulSquareExp powerfulCubeDigit
  omega

theorem powerfulExponent_unique {e a b : ℕ} (hb : b ≤ 1)
    (he : e = 2 * a + 3 * b) :
    a = powerfulSquareExp e ∧ b = powerfulCubeDigit e := by
  unfold powerfulSquareExp powerfulCubeDigit
  omega

end HeckeSkeleton.LowFrozenCube
