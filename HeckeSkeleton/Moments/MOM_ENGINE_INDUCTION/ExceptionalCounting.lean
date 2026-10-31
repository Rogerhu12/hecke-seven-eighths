import DedekindZetaZeroFree.Arithmetic.Ideals.LinearCountingBound
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Counting newly exceptional rows after the second transform

The arithmetic classification of a row as `h₀ * a^6` is explicit input from
the single step.  This file derives the counting consequence using the actual
absolute norm on ideals of the number field.  A finite sector coordinate is
retained, and injectivity is required for the pair (sector, row ideal), so
element-row multiplicities are never silently discarded.

The norm calculation gives the stronger exponent `(m - 2*f)/6` from the
lower bound `N(h₀) ≥ Z^(2*f)`.  For `f ≥ 0`, weakening it gives exactly the
paper's exceptional-count exponent `(m - f)/6`.  Arbitrary scale constants
are carried by the parameter `C`, with row cutoff `C^6 * Z^m`.
-/

noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open scoped NumberField Classical
open DedekindZetaZeroFree.LargeSieve

variable {K : Type*} [Field K] [NumberField K]

/-- The classification supplied by the character and valuation calculation.
`Sector` may combine the finite character and unit-sector labels. -/
structure SixthPowerClassification (Row Sector : Type*) (rows : Finset Row) where
  rowIdeal : Row → Ideal (𝓞 K)
  sector : Row → Sector
  core : Sector → Ideal (𝓞 K)
  sixthRoot : Row → Ideal (𝓞 K)
  row_nonzero : ∀ u ∈ rows, rowIdeal u ≠ ⊥
  factorization : ∀ u ∈ rows, rowIdeal u = core (sector u) * sixthRoot u ^ 6
  row_injective : Set.InjOn (fun u => (sector u, rowIdeal u)) (rows : Set Row)

variable {Row Sector : Type*} {rows : Finset Row}

theorem SixthPowerClassification.root_nonzero
    (d : SixthPowerClassification (K := K) Row Sector rows) {u : Row} (hu : u ∈ rows) :
    d.sixthRoot u ≠ ⊥ := by
  intro hroot
  have hfactor := d.factorization u hu
  have hzero : d.rowIdeal u = ⊥ := by simpa [hroot] using hfactor
  exact d.row_nonzero u hu hzero

/-- Exact factorization makes (sector, sixth root) an injective encoding. -/
theorem SixthPowerClassification.root_encoding_injective
    (d : SixthPowerClassification (K := K) Row Sector rows) :
    Set.InjOn (fun u => (d.sector u, d.sixthRoot u)) (rows : Set Row) := by
  intro u hu v hv heq
  have hsector : d.sector u = d.sector v := congrArg Prod.fst heq
  have hroot : d.sixthRoot u = d.sixthRoot v := congrArg Prod.snd heq
  apply d.row_injective hu hv
  apply Prod.ext hsector
  rw [d.factorization u hu, d.factorization v hv, hsector, hroot]

theorem SixthPowerClassification.norm_factorization
    (d : SixthPowerClassification (K := K) Row Sector rows) {u : Row} (hu : u ∈ rows) :
    (Ideal.absNorm (d.rowIdeal u) : ℝ) =
      (Ideal.absNorm (d.core (d.sector u)) : ℝ) *
        (Ideal.absNorm (d.sixthRoot u) : ℝ) ^ 6 := by
  rw [d.factorization u hu, map_mul, map_pow, Nat.cast_mul, Nat.cast_pow]

/-- Divide the true sixth-power norm by the fixed core lower bound. -/
theorem SixthPowerClassification.root_norm_le
    (d : SixthPowerClassification (K := K) Row Sector rows)
    {u : Row} (hu : u ∈ rows) {B H : ℝ} (hB : 0 < B) (hH : 0 ≤ H)
    (hcore : B ≤ (Ideal.absNorm (d.core (d.sector u)) : ℝ))
    (hrow : (Ideal.absNorm (d.rowIdeal u) : ℝ) ≤ B * H ^ 6) :
    (Ideal.absNorm (d.sixthRoot u) : ℝ) ≤ H := by
  have hmul : B * (Ideal.absNorm (d.sixthRoot u) : ℝ) ^ 6 ≤ B * H ^ 6 := by
    calc
      _ ≤ (Ideal.absNorm (d.core (d.sector u)) : ℝ) *
          (Ideal.absNorm (d.sixthRoot u) : ℝ) ^ 6 :=
        mul_le_mul_of_nonneg_right hcore (by positivity)
      _ = (Ideal.absNorm (d.rowIdeal u) : ℝ) := (d.norm_factorization hu).symm
      _ ≤ _ := hrow
  exact le_of_pow_le_pow_left₀ (by decide : (6 : ℕ) ≠ 0) hH
    ((mul_le_mul_iff_right₀ hB).mp (by simpa only [mul_comm] using hmul))

/-- The complete-sector count at a lower root norm scale.  The counting
constant is the standard linear ideal-count constant for the same field. -/
theorem SixthPowerClassification.card_le_root_bound
    [Fintype Sector] (d : SixthPowerClassification (K := K) Row Sector rows)
    {C H : ℝ} (hC : 1 ≤ C)
    (hcount : ∀ X : ℝ, 1 ≤ X → ((boundedNormIdeals K X).card : ℝ) ≤ C * X)
    (hH : 0 ≤ H)
    (hroots : ∀ u ∈ rows, (Ideal.absNorm (d.sixthRoot u) : ℝ) ≤ H) :
    (rows.card : ℝ) ≤ (Fintype.card Sector : ℝ) * C * H := by
  by_cases hempty : rows = ∅
  · rw [hempty]
    simp only [Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (zero_le_one.trans hC)) hH
  have hnonempty : rows.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
  obtain ⟨u, hu⟩ := hnonempty
  have hone : (1 : ℝ) ≤ (Ideal.absNorm (d.sixthRoot u) : ℝ) := by
    have hn : Ideal.absNorm (d.sixthRoot u) ≠ 0 := by
      intro hz
      exact d.root_nonzero hu (Ideal.absNorm_eq_zero_iff.mp hz)
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have hHone : 1 ≤ H := hone.trans (hroots u hu)
  have hcard : rows.card ≤
      (Finset.univ.product (boundedNormIdeals K H) : Finset (Sector × Ideal (𝓞 K))).card :=
    Finset.card_le_card_of_injOn (fun u => (d.sector u, d.sixthRoot u))
      (by
        intro v hv
        exact Finset.mem_product.mpr ⟨Finset.mem_univ _, mem_boundedNormIdeals.mpr (hroots v hv)⟩)
      d.root_encoding_injective
  rw [Finset.card_product, Finset.card_univ] at hcard
  have hcardReal : (rows.card : ℝ) ≤
      (Fintype.card Sector : ℝ) * ((boundedNormIdeals K H).card : ℝ) := by
    exact_mod_cast hcard
  calc
    _ ≤ (Fintype.card Sector : ℝ) * ((boundedNormIdeals K H).card : ℝ) := hcardReal
    _ ≤ (Fintype.card Sector : ℝ) * (C * H) :=
      mul_le_mul_of_nonneg_left (hcount H hHone) (Nat.cast_nonneg _)
    _ = _ := by ring

/-- Exact conversion from the row/core norm exponents to the root cutoff.
No lower bound on `m - 2*f` is needed: a cutoff below one forces the finite
row family to be empty in the counting theorem. -/
theorem SixthPowerClassification.root_norm_le_power
    (d : SixthPowerClassification (K := K) Row Sector rows)
    {u : Row} (hu : u ∈ rows) {Z m f C : ℝ} (hZ : 0 < Z) (hC : 0 ≤ C)
    (hcore : Z ^ (2 * f) ≤ (Ideal.absNorm (d.core (d.sector u)) : ℝ))
    (hrow : (Ideal.absNorm (d.rowIdeal u) : ℝ) ≤ C ^ 6 * Z ^ m) :
    (Ideal.absNorm (d.sixthRoot u) : ℝ) ≤ C * Z ^ ((m - 2 * f) / 6) := by
  have hpow : (Z ^ ((m - 2 * f) / 6)) ^ 6 = Z ^ (m - 2 * f) := by
    rw [← Real.rpow_mul_natCast hZ.le]
    congr 1
    ring
  have hbalance : Z ^ (2 * f) * Z ^ (m - 2 * f) = Z ^ m := by
    rw [← Real.rpow_add hZ]
    congr 1
    ring
  apply d.root_norm_le hu (Real.rpow_pos_of_pos hZ _) (mul_nonneg hC (Real.rpow_nonneg hZ.le _)) hcore
  apply hrow.trans_eq
  rw [mul_pow, hpow]
  calc
    C ^ 6 * Z ^ m = C ^ 6 * (Z ^ (2 * f) * Z ^ (m - 2 * f)) := by rw [hbalance]
    _ = _ := by ring

/-- Count the exact finite-sector exceptional family at the stronger
sixth-root exponent.  The ideal-count constant is independent of all
scales, frozen cores, and row families. -/
theorem sixth_power_exceptional_count_strong (K : Type*) [Field K] [NumberField K] :
    ∃ Ccount : ℝ, 1 ≤ Ccount ∧
      ∀ (Row Sector : Type*) [Fintype Sector] (rows : Finset Row)
        (d : SixthPowerClassification (K := K) Row Sector rows)
        (Z m f C : ℝ), 0 < Z → 0 ≤ C →
        (∀ u ∈ rows, Z ^ (2 * f) ≤ (Ideal.absNorm (d.core (d.sector u)) : ℝ)) →
        (∀ u ∈ rows, (Ideal.absNorm (d.rowIdeal u) : ℝ) ≤ C ^ 6 * Z ^ m) →
        (rows.card : ℝ) ≤ (Fintype.card Sector : ℝ) * Ccount * C * Z ^ ((m - 2 * f) / 6) := by
  obtain ⟨Ccount, hCcount, hcount⟩ := exists_ideal_count_bound K
  refine ⟨Ccount, hCcount, ?_⟩
  intro Row Sector _ rows d Z m f C hZ hC hcore hrow
  have hroots := fun u hu => d.root_norm_le_power hu hZ hC (hcore u hu) (hrow u hu)
  have h := d.card_le_root_bound hCcount hcount
    (mul_nonneg hC (Real.rpow_nonneg hZ.le _)) hroots
  simpa only [mul_assoc] using h

/-- The exponent stated in §4.8 follows by weakening the stronger estimate.
This retains both the finite sector multiplicity and the scale constant. -/
theorem sixth_power_exceptional_count (K : Type*) [Field K] [NumberField K] :
    ∃ Ccount : ℝ, 1 ≤ Ccount ∧
      ∀ (Row Sector : Type*) [Fintype Sector] (rows : Finset Row)
        (d : SixthPowerClassification (K := K) Row Sector rows)
        (Z m f C : ℝ), 1 ≤ Z → 0 ≤ f → 0 ≤ C →
        (∀ u ∈ rows, Z ^ (2 * f) ≤ (Ideal.absNorm (d.core (d.sector u)) : ℝ)) →
        (∀ u ∈ rows, (Ideal.absNorm (d.rowIdeal u) : ℝ) ≤ C ^ 6 * Z ^ m) →
        (rows.card : ℝ) ≤ (Fintype.card Sector : ℝ) * Ccount * C * Z ^ ((m - f) / 6) := by
  obtain ⟨Ccount, hCcount, hstrong⟩ := sixth_power_exceptional_count_strong K
  refine ⟨Ccount, hCcount, ?_⟩
  intro Row Sector _ rows d Z m f C hZ hf hC hcore hrow
  have h := hstrong Row Sector rows d Z m f C (zero_lt_one.trans_le hZ) hC hcore hrow
  apply h.trans
  apply mul_le_mul_of_nonneg_left
  · exact Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  · exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (zero_le_one.trans hCcount)) hC

end HeckeSkeleton.Moments.EngineInduction
