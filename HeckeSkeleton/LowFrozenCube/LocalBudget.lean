import HeckeSkeleton.LowFrozenCube.ColumnNormalization
import HeckeSkeleton.LowFrozenCube.Scale

/-!
# The local-table budget and the actual coefficient exponent

The primitive inputs below are the squared Gauss bounds for the first
Whittaker scalar, the positive-valuation prefactor, and the zero-valuation
table entries. They imply the minimum-entry budget one prime at a time.
The charged primes form an actual prime product. Its norm supplies the
paper's `S + B` denominator, and the extracted scalar has precisely the
previously proved coefficient exponent.
-/

namespace HeckeSkeleton.LowFrozenCube

open scoped BigOperators Classical

noncomputable section

namespace LocalTable

/-- A minimum-three entry always costs a half norm; a minimum-zero entry
costs a half norm exactly for ordinary digits zero and four. -/
def minimumCharge (j m : ℕ) : ℕ :=
  if m = 3 ∨ (m = 0 ∧ (j = 0 ∨ j = 4)) then 1 else 0

theorem minimumCharge_le_one (j m : ℕ) : minimumCharge j m ≤ 1 := by
  unfold minimumCharge
  split_ifs <;> omega

/-- The stated raw Gauss bounds imply every minimum-valuation coefficient
bound; no assembled-product estimate is an assumption here. -/
theorem ordinaryScalar_minimum_sq_le (q : ℝ) (hq : 0 < q)
    (first prefactor : ℂ) (atZero : ℕ → ℂ) (j m : ℕ)
    (hm : m = 0 ∨ m = 1 ∨ m = 3)
    (hfirst : ‖first‖ ^ 2 ≤ 1 / q)
    (hprefactor : ‖prefactor‖ ^ 2 ≤ q)
    (hzero : ‖atZero j‖ ^ 2 ≤ if j = 0 ∨ j = 4 then 1 / q else 1) :
    ‖ordinaryScalar (q : ℂ) first prefactor atZero j m‖ ^ 2 ≤
      (q ^ minimumCharge j m)⁻¹ := by
  have hq0 : q ≠ 0 := ne_of_gt hq
  rcases hm with rfl | rfl | rfl
  · by_cases hj : j = 0 ∨ j = 4 <;>
      simpa [ordinaryScalar, minimumCharge, hj, one_div] using hzero
  · by_cases hj : j = 4
    · have hm : ‖prefactor‖ ^ 2 * ‖first‖ ^ 2 ≤ 1 := by
        calc
          _ ≤ q * (1 / q) :=
            mul_le_mul hprefactor hfirst (sq_nonneg _) (le_of_lt hq)
          _ = 1 := by field_simp [hq0]
      simpa [ordinaryScalar, hj, norm_mul, mul_pow, minimumCharge] using hm
    · simp [ordinaryScalar, hj, minimumCharge]
  · by_cases hj : j = 4
    · have hm : ‖prefactor‖ ^ 2 * (q⁻¹) ^ 2 ≤ q⁻¹ := by
        calc
          _ ≤ q * (q⁻¹) ^ 2 :=
            mul_le_mul_of_nonneg_right hprefactor (sq_nonneg _)
          _ = q⁻¹ := by field_simp [hq0]
      simpa [ordinaryScalar, hj, norm_mul, mul_pow, minimumCharge, norm_inv,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq] using hm
    · simp [ordinaryScalar, hj, minimumCharge, le_of_lt hq]

end LocalTable

namespace FrozenReduction.Data

variable {ι A : Type*} [CommMonoid A] (D : FrozenReduction.Data ι A)

def chargeIdeal : A :=
  ∏ p ∈ D.ordinary,
    D.prime p ^ LocalTable.minimumCharge (D.digit p)
      (PrimeCoordinates.valuation D.coords D.minimum p)

theorem norm_chargeIdeal (normI : A →* ℝ) :
    normI D.chargeIdeal = ∏ p ∈ D.ordinary,
      normI (D.prime p) ^ LocalTable.minimumCharge (D.digit p)
        (PrimeCoordinates.valuation D.coords D.minimum p) := by
  simp only [chargeIdeal, map_prod, map_pow]

theorem minimum_cases_of_activeInput (normI : A → ℝ) (first prefactor : ι → ℂ)
    (atZero : ι → ℕ → ℂ) (inputs : Finset (A × A)) (q : A × A)
    (hq : q ∈ D.activeInputBlock normI first prefactor atZero inputs) (p : ι) :
    PrimeCoordinates.valuation D.coords D.minimum p = 0 ∨
    PrimeCoordinates.valuation D.coords D.minimum p = 1 ∨
    PrimeCoordinates.valuation D.coords D.minimum p = 3 := by
  have hm := ((D.mem_activeInputBlock normI first prefactor atZero inputs q).mp hq).2.1
  rw [← hm]
  simp only [PrimeCoordinates.minimumFactor, PrimeCoordinates.valuation_mapExponents]
  exact frozenMin_cases _

/-- Squaring the exact minimum product gives one reciprocal norm for each
charged prime. This is derived from the primitive local table bounds. -/
theorem tableMajorant_sq_le_charge (normI : A →* ℝ) (hpos : ∀ a, 0 < normI a)
    (first prefactor : ι → ℂ) (atZero : ι → ℕ → ℂ)
    (hminimum : ∀ p ∈ D.ordinary,
      PrimeCoordinates.valuation D.coords D.minimum p = 0 ∨
      PrimeCoordinates.valuation D.coords D.minimum p = 1 ∨
      PrimeCoordinates.valuation D.coords D.minimum p = 3)
    (hfirst : ∀ p ∈ D.ordinary, ‖first p‖ ^ 2 ≤ 1 / normI (D.prime p))
    (hprefactor : ∀ p ∈ D.ordinary, ‖prefactor p‖ ^ 2 ≤ normI (D.prime p))
    (hzero : ∀ p ∈ D.ordinary, ‖atZero p (D.digit p)‖ ^ 2 ≤
      if D.digit p = 0 ∨ D.digit p = 4 then 1 / normI (D.prime p) else 1) :
    D.tableMajorant normI first prefactor atZero ^ 2 ≤ (normI D.chargeIdeal)⁻¹ := by
  unfold tableMajorant
  rw [← Finset.prod_pow]
  calc
    (∏ p ∈ D.ordinary,
        ‖LocalTable.ordinaryScalar (normI (D.prime p) : ℂ) (first p) (prefactor p)
          (atZero p) (D.digit p) (PrimeCoordinates.valuation D.coords D.minimum p)‖ ^ 2) ≤
        ∏ p ∈ D.ordinary,
          (normI (D.prime p) ^ LocalTable.minimumCharge (D.digit p)
            (PrimeCoordinates.valuation D.coords D.minimum p))⁻¹ := by
      apply Finset.prod_le_prod₀
      · intro p hp
        exact sq_nonneg _
      · intro p hp
        exact LocalTable.ordinaryScalar_minimum_sq_le (normI (D.prime p))
          (hpos (D.prime p)) (first p) (prefactor p) (atZero p) (D.digit p)
          (PrimeCoordinates.valuation D.coords D.minimum p)
          (hminimum p hp) (hfirst p hp) (hprefactor p hp) (hzero p hp)
    _ = (normI D.chargeIdeal)⁻¹ := by
      rw [Finset.prod_inv_distrib, D.norm_chargeIdeal]

end FrozenReduction.Data

/-- Exact real-power form of the column, full-cube, and charged-prime
denominators. -/
theorem coefficientScale_identity (Z v ell S B : ℝ) (hZ : 0 < Z) :
    (Z ^ (S + B))⁻¹ / (Z ^ ell) ^ 2 / Z ^ v =
      Z ^ (squaredCoefficientExponent v ell S B) := by
  rw [← Real.rpow_neg (le_of_lt hZ),
    ← Real.rpow_mul_natCast (le_of_lt hZ) ell 2,
    ← Real.rpow_sub hZ, ← Real.rpow_sub hZ]
  congr 1
  unfold squaredCoefficientExponent
  ring

/-- A proved local budget and the actual norm-scale substitutions give the
paper's squared coefficient exponent without discarding the column weight. -/
theorem normalizedCoefficient_le_ledger (C N cubeNorm chargeNorm Z v ell S B : ℝ)
    (hN : 0 < N) (hZ : 0 < Z) (hC : C ^ 2 ≤ chargeNorm⁻¹)
    (hNscale : N = Z ^ v) (hBscale : cubeNorm = Z ^ ell)
    (hcharge : chargeNorm = Z ^ (S + B)) :
    (C / cubeNorm) ^ 2 / N ≤ Z ^ (squaredCoefficientExponent v ell S B) := by
  rw [div_pow]
  calc
    C ^ 2 / cubeNorm ^ 2 / N ≤ chargeNorm⁻¹ / cubeNorm ^ 2 / N :=
      div_le_div_of_nonneg_right
        (div_le_div_of_nonneg_right hC (sq_nonneg _)) (le_of_lt hN)
    _ = _ := by
      rw [hcharge, hBscale, hNscale]
      exact coefficientScale_identity Z v ell S B hZ

end

end HeckeSkeleton.LowFrozenCube
