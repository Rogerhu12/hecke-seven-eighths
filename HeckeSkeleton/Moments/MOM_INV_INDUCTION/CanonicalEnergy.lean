import HeckeGeneral.Analysis.MomentInputs
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.Terminal

/-!
# Literal canonical ideal energies

A canonical datum records actual nonzero integral ideals, the squarefree
column and label supports, the retained common puncture, the background
Hecke character, and the original arrays of prime-slot coefficients.
The norm and the energy are defined from these data; neither is a field.

`gamma₂` and `symbol` are the arithmetic coefficient families supplied by a
calibrated step provider.  Their arithmetic identities, support scales,
annular localization, and uniform analytic estimates are separate input
obligations.  Supplying the families does not assert those identities.
The live column has no additional residual coefficient depending on its
row or label: its only such dependence is the displayed pair of symbols.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION

open NumberField IsDedekindDomain
open HeckeGeneral.Characters HeckeGeneral.Analysis
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]

/-- A finite canonical block before any energy estimate.  The arrays of
slot coefficients, the background, puncture, and common profile are fixed
throughout the row and label sums. -/
structure CanonicalDatum where
  Lambda : HeckeCharacter K
  target : HeckeCharacter K
  background : HeckeCharacter K
  finiteBackgrounds : Finset (HeckeCharacter K)
  finiteBackgrounds_finite : ∀ θ ∈ finiteBackgrounds, FiniteOrder θ
  background_class : background ∈ finiteBackgrounds ∨
    ∃ θ ∈ finiteBackgrounds, background = target * θ
  gamma₂ : NonzeroIdeal K → ℂ
  symbol : NonzeroIdeal K → NonzeroIdeal K → ℂ
  excluded : Finset (HeightOneSpectrum (𝓞 K))
  rows : Finset (NonzeroIdeal K)
  labels : Finset (NonzeroIdeal K)
  columns : Finset (NonzeroIdeal K)
  labels_squarefree : ∀ f ∈ labels, Squarefree f.val
  columns_squarefree : ∀ n ∈ columns, Squarefree n.val
  labels_exterior : ∀ f ∈ labels, ∀ p ∈ excluded, ¬ p.asIdeal ∣ f.val
  columns_exterior : ∀ n ∈ columns, ∀ p ∈ excluded, ¬ p.asIdeal ∣ n.val
  labelWeight : NonzeroIdeal K → ℝ
  labelWeight_nonneg : ∀ f ∈ labels, 0 ≤ labelWeight f
  puncture : NonzeroIdeal K
  slotCount : ℕ
  surviving : Finset (Fin slotCount)
  primeList : Fin slotCount → Finset (HeightOneSpectrum (𝓞 K))
  slotCoefficient : Fin slotCount → HeightOneSpectrum (𝓞 K) → ℂ
  slotCoefficient_bound : ∀ i ∈ surviving, ∀ p ∈ primeList i,
    ‖slotCoefficient i p‖ ≤ 1
  primeList_exterior : ∀ i ∈ surviving, ∀ p ∈ primeList i, p ∉ excluded
  slotLength : Fin slotCount → ℝ
  slotLength_nonneg : ∀ i ∈ surviving, 0 ≤ slotLength i
  profile : ℝ → ℂ
  rowLength : ℝ
  columnLength : ℝ
  labelLength : ℝ
  punctureLength : ℝ
  markCap : ℝ
  rowLength_nonneg : 0 ≤ rowLength
  columnLength_nonneg : 0 ≤ columnLength
  labelLength_nonneg : 0 ≤ labelLength
  punctureLength_nonneg : 0 ≤ punctureLength
  markCap_nonneg : 0 ≤ markCap
  mark_length_le : ∑ i ∈ surviving, slotLength i ≤ markCap

namespace CanonicalDatum

variable {K}

/-- The combined column-and-label length `F = N + V`. -/
def totalLength (d : CanonicalDatum K) : ℝ := d.columnLength + d.labelLength

theorem totalLength_nonneg (d : CanonicalDatum K) : 0 ≤ d.totalLength :=
  add_nonneg d.columnLength_nonneg d.labelLength_nonneg

/-- The canonical coefficient `a₀(n) = conjugate(Λ(n)) γ₂(n)`. -/
def canonicalCoefficient (d : CanonicalDatum K) (n : NonzeroIdeal K) : ℂ :=
  star (heckeIdealCoefficient K d.Lambda n) * d.gamma₂ n

/-- The original product-form mark with actual prime-divisibility masks.
Every coefficient is independent of the live row and squarefree label. -/
def markValue (d : CanonicalDatum K) (n : NonzeroIdeal K) : ℂ :=
  ∏ i ∈ d.surviving,
    ∑ p ∈ d.primeList i,
      d.slotCoefficient i p * (if p.asIdeal ∣ n.val then 1 else 0)

theorem markValue_empty (d : CanonicalDatum K) (h : d.surviving = ∅)
    (n : NonzeroIdeal K) : d.markValue n = 1 := by
  simp only [markValue, h, Finset.prod_empty]

/-- The fixed moving puncture is retained as a complete ideal mask. -/
def punctureMask (d : CanonicalDatum K) (n : NonzeroIdeal K) : ℂ :=
  if IsCoprime n.val d.puncture.val then 1 else 0

theorem punctureMask_zero (d : CanonicalDatum K) (n : NonzeroIdeal K)
    (h : ¬ IsCoprime n.val d.puncture.val) : d.punctureMask n = 0 := by
  simp only [punctureMask, if_neg h]

/-- The finite squarefree column before its prescribed normalization. -/
def columnSum (d : CanonicalDatum K) (Z : ℝ)
    (k f : NonzeroIdeal K) : ℂ :=
  ∑ n ∈ d.columns,
    d.canonicalCoefficient n * heckeIdealCoefficient K d.background n *
      d.punctureMask n * d.symbol n k * (d.symbol n f) ^ 4 *
      d.markValue n * d.profile (idealNorm K n / Z ^ d.columnLength)

/-- The normalized finite squarefree column in Proposition 4.10.
There is no independently chosen row energy or residual coefficient. -/
def columnValue (d : CanonicalDatum K) (Z : ℝ)
    (k f : NonzeroIdeal K) : ℂ :=
  (Real.sqrt (Z ^ d.columnLength) : ℂ)⁻¹ * d.columnSum Z k f

/-- The squared norm over the actual finite row set, for one fixed label. -/
def labelEnergy (d : CanonicalDatum K) (Z : ℝ) (f : NonzeroIdeal K) : ℝ :=
  ∑ k ∈ d.rows, ‖d.columnValue Z k f‖ ^ 2

/-- The label-normalized canonical energy `Z^(-V) ∑f w(f) ∑k |...|²`. -/
def energy (d : CanonicalDatum K) (Z : ℝ) : ℝ :=
  Z ^ (-d.labelLength) * ∑ f ∈ d.labels, d.labelWeight f * d.labelEnergy Z f

theorem labelEnergy_nonneg (d : CanonicalDatum K) (Z : ℝ)
    (f : NonzeroIdeal K) : 0 ≤ d.labelEnergy Z f := by
  exact Finset.sum_nonneg (fun k _ => sq_nonneg _)

theorem weightedLabelEnergy_nonneg (d : CanonicalDatum K) (Z : ℝ) :
    0 ≤ ∑ f ∈ d.labels, d.labelWeight f * d.labelEnergy Z f := by
  exact Finset.sum_nonneg (fun f hf =>
    mul_nonneg (d.labelWeight_nonneg f hf) (d.labelEnergy_nonneg Z f))

theorem energy_nonneg (d : CanonicalDatum K) (Z : ℝ) (hZ : 0 ≤ Z) :
    0 ≤ d.energy Z := by
  exact mul_nonneg (Real.rpow_nonneg hZ _) (d.weightedLabelEnergy_nonneg Z)

theorem energy_eq_normalized_label_sum (d : CanonicalDatum K) (Z : ℝ) :
    d.energy Z = Z ^ (-d.labelLength) *
      ∑ f ∈ d.labels, d.labelWeight f * d.labelEnergy Z f := rfl

/-- Squaring the column norm removes exactly one column-length power. -/
theorem columnValue_norm_sq (d : CanonicalDatum K) (Z : ℝ) (hZ : 0 ≤ Z)
    (k f : NonzeroIdeal K) :
    ‖d.columnValue Z k f‖ ^ 2 =
      (Z ^ d.columnLength)⁻¹ * ‖d.columnSum Z k f‖ ^ 2 := by
  simp only [columnValue, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, inv_pow,
    Real.sq_sqrt (Real.rpow_nonneg hZ _)]

theorem labelEnergy_eq_column_sum (d : CanonicalDatum K) (Z : ℝ) (hZ : 0 ≤ Z)
    (f : NonzeroIdeal K) :
    d.labelEnergy Z f =
      (Z ^ d.columnLength)⁻¹ * ∑ k ∈ d.rows, ‖d.columnSum Z k f‖ ^ 2 := by
  unfold labelEnergy
  simp_rw [d.columnValue_norm_sq Z hZ]
  rw [Finset.mul_sum]

/-- Restoring both normalizations yields the total length `F = N + V`.
The label normalization and the squared column normalization occur once
each, before the two-transform prefactor is applied. -/
theorem energy_eq_rpow_neg_totalLength (d : CanonicalDatum K)
    (Z : ℝ) (hZ : 0 < Z) :
    d.energy Z = Z ^ (-d.totalLength) *
      ∑ f ∈ d.labels, d.labelWeight f *
        ∑ k ∈ d.rows, ‖d.columnSum Z k f‖ ^ 2 := by
  unfold energy
  simp_rw [d.labelEnergy_eq_column_sum Z hZ.le]
  calc
    _ = (Z ^ (-d.labelLength) * (Z ^ d.columnLength)⁻¹) *
        ∑ f ∈ d.labels, d.labelWeight f *
          ∑ k ∈ d.rows, ‖d.columnSum Z k f‖ ^ 2 := by
      have hs : (∑ f ∈ d.labels, d.labelWeight f *
          ((Z ^ d.columnLength)⁻¹ * ∑ k ∈ d.rows, ‖d.columnSum Z k f‖ ^ 2)) =
          (Z ^ d.columnLength)⁻¹ * ∑ f ∈ d.labels, d.labelWeight f *
            ∑ k ∈ d.rows, ‖d.columnSum Z k f‖ ^ 2 := by
        calc
          _ = ∑ f ∈ d.labels, (Z ^ d.columnLength)⁻¹ *
              (d.labelWeight f * ∑ k ∈ d.rows, ‖d.columnSum Z k f‖ ^ 2) := by
            apply Finset.sum_congr rfl
            intro f _
            ring
          _ = _ := (Finset.mul_sum ..).symm
      rw [hs, mul_assoc]
    _ = _ := by
      rw [← Real.rpow_neg hZ.le, ← Real.rpow_add hZ]
      congr 2
      unfold totalLength
      ring

/-- The reflected terminal ledger bounds this literal canonical energy;
the squarefree label normalization is consumed by the proved sum lemma. -/
theorem energy_le_of_terminal_labels (d : CanonicalDatum K)
    {Z δ C L cnode c step η τ π : ℝ}
    (hZ : 1 ≤ Z) (hC : 0 ≤ C)
    (hmass : ∑ f ∈ d.labels, d.labelWeight f ≤ L * Z ^ (d.labelLength + δ))
    (hc : 0 < c) (hnode : c / 2 ≤ cnode)
    (hstep : step ≤ c / 200) (hη : η ≤ c / 1000)
    (hτ : τ ≤ c / 1000) (hπ : π ≤ c / 1000)
    (hlabels : ∀ f ∈ d.labels, d.labelEnergy Z f ≤ C *
      (Z ^ (d.totalLength - cnode + 5 * η / 3 + π) +
       Z ^ (d.totalLength - 2 * cnode + 5 * step + 17 * η / 3 + τ + π) +
       Z ^ (d.totalLength - d.rowLength / 4 - 3 * cnode / 4 +
         5 * step / 2 + 19 * η / 6 + τ / 2 + π))) :
    d.energy Z ≤ (3 * C * L) * Z ^ (d.totalLength - c / 4 + δ) := by
  exact terminal_normalized_label_energy_le d.labels d.labelWeight (d.labelEnergy Z)
    hZ hC d.labelWeight_nonneg hmass hc d.rowLength_nonneg hnode
    hstep hη hτ hπ hlabels

end CanonicalDatum

end HeckeSkeleton.Moments.MOM_INV_INDUCTION
