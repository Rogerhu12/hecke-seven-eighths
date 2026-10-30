import HeckeSkeleton.LowFrozenCube.WeightedHybridBound
import HeckeSkeleton.LowFrozenCube.LocalBudget

/-!
# The exponent ledger bounds the actual original source energy

`SourceBlock` contains finite input data, and `AnnularSupport` contains only
the elementary support and norm conditions. Neither contains an energy
estimate or a normal-form identity. The theorem below first proves the
source estimate using LOW-HYBRID, then applies the exact coefficient and
kernel ledger. Dyadic lower endpoints cost eight; the hybrid scale costs
six, accounting for the explicit factor 48 in the proof.
-/

namespace HeckeSkeleton.LowFrozenCube.FrozenReduction

open scoped BigOperators Classical

noncomputable section

variable {ι A : Type*} [CommMonoid A]

structure SourceBlock (ι A : Type*) where
  first : ι → ℂ
  prefactor : ι → ℂ
  atZero : ι → ℕ → ℂ
  phase : A → A → A → ℂ
  a₀ : A → ℂ
  ρ₀ : A → ℂ
  lam : A → ℂ
  pow : A
  sup : A
  rows : Finset A
  marks : Finset A
  columns : Finset A
  inputs : Finset (A × A)

namespace SourceBlock

def energy (b : SourceBlock ι A) (D : Data ι A) (normI : A → ℝ) : ℝ :=
  D.rawBlockSourceEnergy normI b.first b.prefactor b.atZero b.phase b.a₀ b.ρ₀
    (annularColumn normI b.lam) b.pow b.sup b.rows b.marks b.columns b.inputs

theorem energy_nonneg (b : SourceBlock ι A) (D : Data ι A) (normI : A → ℝ) :
    0 ≤ b.energy D normI :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem energy_zero_of_empty_active (b : SourceBlock ι A) (D : Data ι A)
    (normI : A → ℝ)
    (hsupport : ∀ q ∈ b.inputs, PrimeCoordinates.Supported D.coords D.ordinary q.1)
    (hempty : D.activeInputBlock normI b.first b.prefactor b.atZero b.inputs = ∅) :
    b.energy D normI = 0 := by
  have hpairs : D.frozenInputPairs normI b.first b.prefactor b.atZero b.inputs = ∅ := by
    simp [Data.frozenInputPairs, hempty]
  unfold energy Data.rawBlockSourceEnergy
  apply Finset.sum_eq_zero
  intro k hk
  rw [D.rawSourceRow_eq_sourceRow normI b.first b.prefactor b.atZero b.phase
    b.a₀ b.ρ₀ (annularColumn normI b.lam) b.marks b.columns b.inputs hsupport]
  simp [hpairs, Data.sourceRow]

end SourceBlock

/-- Ordinary support and actual annular norm conditions, together with the
primitive scalar phase bounds in the unfrozen formula. -/
structure AnnularSupport (D : Data ι A) (normI : A → ℝ)
    (Z H v ell z : ℝ) (b : SourceBlock ι A) where
  rowBall : ℝ
  rows_norm : ∀ k ∈ b.rows, normI k ≤ rowBall
  residual_norm : ∀ d ∈ PrimeCoordinates.residualRows D.coords D.support b.pow b.sup b.rows,
    normI d ≤ Z ^ H
  rho_norm : ∀ d, (∀ p, PrimeCoordinates.valuation D.coords d p ≤ 1) →
    PrimeCoordinates.Avoids D.coords D.support d → ‖b.ρ₀ d‖ = 1
  marks_away : ∀ P ∈ b.marks, PrimeCoordinates.Avoids D.coords D.support P
  marks_sf_norm : ∀ P ∈ b.marks,
    HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree D.coords P ∧ normI P ≤ Z ^ z
  marks_coeff : ∀ P ∈ b.marks, ‖b.a₀ P‖ ≤ 1
  columns_away : ∀ c ∈ b.columns, PrimeCoordinates.Avoids D.coords D.ordinary c
  columns_sf_norm : ∀ c ∈ b.columns,
    HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree D.coords c ∧ normI c ≤ Z ^ v
  columns_coeff : ∀ c ∈ b.columns, ‖b.lam c‖ ≤ 1
  columns_lower : ∀ c ∈ b.columns, Z ^ v / 2 ≤ normI c
  input_supported : ∀ u ∈ b.inputs, PrimeCoordinates.Supported D.coords D.ordinary u.1
  input_away : ∀ u ∈ b.inputs, PrimeCoordinates.Avoids D.coords D.ordinary u.2
  input_phase : ∀ c ∈ b.columns, ∀ u ∈ b.inputs, ‖b.phase c u.1 u.2‖ ≤ 1
  cube_lower : ∀ u ∈ b.inputs,
    Z ^ ell / 2 ≤ normI (PrimeCoordinates.residualCubeFactor D.coords u.1 * u.2)
  cube_upper : ∀ u ∈ b.inputs,
    normI (PrimeCoordinates.residualCubeFactor D.coords u.1 * u.2) ≤ Z ^ ell

/-- These are exactly the three primitive local Gauss bounds used by the
minimum-table calculation; no assembled coefficient bound is a field. -/
structure PrimitiveLocalBounds (D : Data ι A) (normI : A → ℝ) (b : SourceBlock ι A) where
  first_sq : ∀ p ∈ D.ordinary, ‖b.first p‖ ^ 2 ≤ 1 / normI (D.prime p)
  prefactor_sq : ∀ p ∈ D.ordinary, ‖b.prefactor p‖ ^ 2 ≤ normI (D.prime p)
  zero_sq : ∀ p ∈ D.ordinary, ‖b.atZero p (D.digit p)‖ ^ 2 ≤
    if D.digit p = 0 ∨ D.digit p = 4 then 1 / normI (D.prime p) else 1

theorem four_scale_power (Z H v ell z eps : ℝ) (hZ : 0 < Z) :
    (Z ^ H * Z ^ v * Z ^ ell * Z ^ z) ^ eps = Z ^ (eps * (H + v + ell + z)) := by
  rw [← Real.rpow_add hZ, ← Real.rpow_add hZ, ← Real.rpow_add hZ,
    ← Real.rpow_mul (le_of_lt hZ)]
  congr 1
  ring

theorem dyadic_coefficient_scale (C N B : ℝ) (hN : 0 < N) (hB : 0 < B) :
    (C / (B / 2)) ^ 2 / (N / 2) = 8 * ((C / B) ^ 2 / N) := by
  field_simp [ne_of_gt hN, ne_of_gt hB] <;> ring

namespace Data

variable (D : Data ι A)

/-- The source-to-ledger theorem. Its constant is uniform in all scales and
all finite source data. The left side is the actual weighted raw source
energy multiplied by the powerful-row and common-kernel scalars; the right
side is the paper's reflected exponent with the precise sieve small power.
-/
theorem source_energy_ledger
    (normI : A →* ℝ) (q : A → ℕ)
    (hnatural : ∀ a, normI a = (q a : ℝ)) (hqpos : ∀ a, 1 ≤ q a)
    (Ccount : ℝ) (hCcount : 0 < Ccount)
    (hcount : HeckeSkeleton.LowHybrid.LinearNormCounting q Ccount)
    (hq : HeckeSkeleton.LowHybrid.QuadraticSieveInput normI
      (HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree D.coords) (fun a b => D.symbol a b))
    (hc : HeckeSkeleton.LowHybrid.CubicSieveInput normI
      (HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree D.coords) (fun a b => D.symbol a b))
    (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧
      ∀ Z O H v ell S B z T : ℝ,
      1 ≤ Z → 0 ≤ H → 0 ≤ v → 0 ≤ ell → 0 ≤ z →
      ∀ b : SourceBlock ι A, AnnularSupport D normI Z H v ell z b →
        PrimitiveLocalBounds D normI b → Z ^ (S + B) ≤ normI D.chargeIdeal →
        Z ^ (O / 2) * b.energy D normI * Z ^ (squaredKernelExponent T v ell) ≤
          C * Z ^ (reflectedExponent O H v ell S B z T + eps * (H + v + ell + z)) := by
  have hnorm := HeckeSkeleton.LowHybrid.one_le_real_norm_of_natural q normI hnatural hqpos
  have hpos (a : A) : 0 < normI a := lt_of_lt_of_le zero_lt_one (hnorm a)
  obtain ⟨C0, hC0, hbound⟩ := D.weighted_raw_hybrid_bound normI q hnatural hqpos
    Ccount hCcount hcount hq hc eps heps
  refine ⟨48 * C0, mul_pos (by norm_num) hC0, ?_⟩
  intro Z O H v ell S B z T hZ hH hv hell hz b hs hlocal hcharge
  have hZpos : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hZ0 : 0 ≤ Z := le_of_lt hZpos
  have hNpos : 0 < Z ^ v := Real.rpow_pos_of_pos hZpos v
  have hBpos : 0 < Z ^ ell := Real.rpow_pos_of_pos hZpos ell
  by_cases hactive : (D.activeInputBlock normI b.first b.prefactor b.atZero b.inputs).Nonempty
  · obtain ⟨u, hu⟩ := hactive
    have hCtable := D.tableMajorant_sq_le_charge normI hpos b.first b.prefactor b.atZero
      (fun p hp => D.minimum_cases_of_activeInput normI b.first b.prefactor b.atZero b.inputs u hu p)
      hlocal.first_sq hlocal.prefactor_sq hlocal.zero_sq
    have hCscale : D.tableMajorant normI b.first b.prefactor b.atZero ^ 2 ≤
        (Z ^ (S + B))⁻¹ := by
      apply hCtable.trans
      simpa only [one_div] using
        one_div_le_one_div_of_le (Real.rpow_pos_of_pos hZpos (S + B)) hcharge
    have hcoeff : (D.tableMajorant normI b.first b.prefactor b.atZero / (Z ^ ell / 2)) ^ 2 /
        (Z ^ v / 2) ≤ 8 * Z ^ (squaredCoefficientExponent v ell S B) := by
      rw [dyadic_coefficient_scale _ _ _ hNpos hBpos]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact normalizedCoefficient_le_ledger _ _ _ _ Z v ell S B
        hNpos hZpos hCscale rfl rfl rfl
    have hE := hbound hs.rowBall (Z ^ H) (Z ^ v) (Z ^ ell) (Z ^ z)
      (Z ^ v / 2) (Z ^ ell / 2)
      (Real.one_le_rpow hZ hH) (Real.one_le_rpow hZ hv)
      (Real.one_le_rpow hZ hell) (Real.one_le_rpow hZ hz)
      (div_pos hNpos (by norm_num)) (div_pos hBpos (by norm_num))
      b.first b.prefactor b.atZero b.phase b.a₀ b.ρ₀ b.lam b.pow b.sup
      b.rows b.marks b.columns b.inputs hs.rows_norm hs.residual_norm hs.rho_norm
      hs.marks_away hs.marks_sf_norm hs.marks_coeff hs.columns_away hs.columns_sf_norm
      hs.columns_coeff hs.columns_lower hs.input_supported hs.input_away hs.input_phase
      hs.cube_lower hs.cube_upper
    have hE' : b.energy D normI ≤
        (D.tableMajorant normI b.first b.prefactor b.atZero / (Z ^ ell / 2)) ^ 2 / (Z ^ v / 2) *
          ((C0 * Z ^ (eps * (H + v + ell + z))) * hybridScale Z H v ell z) := by
      rw [four_scale_power Z H v ell z eps hZpos] at hE
      simpa only [SourceBlock.energy, hybridScale, quadraticScale, cubicScale,
        mul_assoc] using hE
    have hlead : 0 ≤ C0 * Z ^ (eps * (H + v + ell + z)) :=
      mul_nonneg (le_of_lt hC0) (Real.rpow_nonneg hZ0 _)
    have hhybrid : 0 ≤ hybridScale Z H v ell z := by
      unfold hybridScale quadraticScale cubicScale
      positivity
    have hEsimple : b.energy D normI ≤
        (48 * C0) * Z ^ (eps * (H + v + ell + z)) *
          Z ^ (squaredCoefficientExponent v ell S B + hybridGrowthExponent H v ell z) := by
      calc
        _ ≤ (8 * Z ^ (squaredCoefficientExponent v ell S B)) *
            ((C0 * Z ^ (eps * (H + v + ell + z))) *
              (6 * Z ^ (hybridGrowthExponent H v ell z))) := by
          apply hE'.trans
          exact mul_le_mul hcoeff
            (mul_le_mul_of_nonneg_left (hybridScale_le Z H v ell z hZ) hlead)
            (mul_nonneg hlead hhybrid)
            (mul_nonneg (by norm_num) (Real.rpow_nonneg hZ0 _))
        _ = _ := by
          rw [Real.rpow_add hZpos]
          ring
    calc
      Z ^ (O / 2) * b.energy D normI * Z ^ (squaredKernelExponent T v ell) ≤
          Z ^ (O / 2) *
            ((48 * C0) * Z ^ (eps * (H + v + ell + z)) *
              Z ^ (squaredCoefficientExponent v ell S B + hybridGrowthExponent H v ell z)) *
                Z ^ (squaredKernelExponent T v ell) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hEsimple (Real.rpow_nonneg hZ0 _))
          (Real.rpow_nonneg hZ0 _)
      _ = _ := by
        rw [← reflected_exponent_identity O H v ell S B z T]
        simp only [Real.rpow_add hZpos]
        ring
  · have hempty : D.activeInputBlock normI b.first b.prefactor b.atZero b.inputs = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hactive
    rw [b.energy_zero_of_empty_active D normI hs.input_supported hempty]
    simp only [mul_zero, zero_mul]
    exact mul_nonneg (mul_nonneg (by norm_num) (le_of_lt hC0)) (Real.rpow_nonneg hZ0 _)

end Data

end

end HeckeSkeleton.LowFrozenCube.FrozenReduction
