import HeckeSkeleton.LowFrozenCube.RawRowBlockExit

/-!
# Preserve and extract the original squarefree-column normalization

The original reflected row contains `1 / sqrt(N(c))`. On a lower annulus
`N ≤ N(c)`, this file constructs a bounded column coefficient and extracts
the exact scalar `1 / sqrt(N)` from the entire row. Combined with the cube
normalization, the squared scalar is `(C / B)^2 / N`.
-/

namespace HeckeSkeleton.LowFrozenCube.FrozenReduction

open scoped BigOperators Classical

noncomputable section

variable {ι A : Type*} [CommMonoid A]

def annularColumn (normI : A → ℝ) (lam : A → ℂ) (c : A) : ℂ :=
  lam c / (Real.sqrt (normI c) : ℂ)

def unitAnnularColumn (normI : A → ℝ) (N : ℝ) (lam : A → ℂ) (c : A) : ℂ :=
  ((Real.sqrt N : ℂ) / (Real.sqrt (normI c) : ℂ)) * lam c

theorem unitAnnularColumn_norm_le (normI : A → ℝ) (N : ℝ) (hN : 0 < N)
    (lam : A → ℂ) (c : A) (hlower : N ≤ normI c) (hlam : ‖lam c‖ ≤ 1) :
    ‖unitAnnularColumn normI N lam c‖ ≤ 1 := by
  have hc : 0 < Real.sqrt (normI c) := Real.sqrt_pos.mpr (hN.trans_le hlower)
  simp only [unitAnnularColumn, norm_mul, norm_div, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg N),
    abs_of_nonneg (Real.sqrt_nonneg (normI c))]
  calc
    Real.sqrt N / Real.sqrt (normI c) * ‖lam c‖ ≤
        Real.sqrt N / Real.sqrt (normI c) * 1 :=
      mul_le_mul_of_nonneg_left hlam
        (div_nonneg (Real.sqrt_nonneg N) (Real.sqrt_nonneg (normI c)))
    _ ≤ 1 := by
      rw [mul_one]
      exact (div_le_one hc).mpr (Real.sqrt_le_sqrt hlower)

theorem annularColumn_eq_scalar_unit (normI : A → ℝ) (N : ℝ) (hN : 0 < N)
    (lam : A → ℂ) (c : A) :
    annularColumn normI lam c = (Real.sqrt N : ℂ)⁻¹ *
      unitAnnularColumn normI N lam c := by
  have hs : (Real.sqrt N : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr hN))
  unfold annularColumn unitAnnularColumn
  calc
    lam c / (Real.sqrt (normI c) : ℂ) =
        ((Real.sqrt N : ℂ)⁻¹ * (Real.sqrt N : ℂ)) *
          (lam c / (Real.sqrt (normI c) : ℂ)) := by
      rw [inv_mul_cancel₀ hs, one_mul]
    _ = _ := by ring

theorem inv_sqrt_norm_sq (N : ℝ) (hN : 0 < N) :
    ‖(Real.sqrt N : ℂ)⁻¹‖ ^ 2 = 1 / N := by
  simp only [norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg N), inv_pow, Real.sq_sqrt (le_of_lt hN), one_div]

namespace Data

variable (D : Data ι A)

theorem rawSourceRow_scale_column (normI : A → ℝ) (first prefactor : ι → ℂ)
    (atZero : ι → ℕ → ℂ) (phase : A → A → A → ℂ)
    (a₀ ρ₀ lam gamma : A → ℂ) (scalar : ℂ)
    (marks columns : Finset A) (inputs : Finset (A × A))
    (hlam : ∀ c ∈ columns, lam c = scalar * gamma c) (d : A) :
    D.rawSourceRow normI first prefactor atZero phase a₀ ρ₀ lam marks columns inputs d =
      scalar * D.rawSourceRow normI first prefactor atZero phase a₀ ρ₀ gamma
        marks columns inputs d := by
  unfold rawSourceRow
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro P hP
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro q hq
  unfold rawSourceTerm columnCoefficient
  rw [hlam c hc]
  ring

theorem rawBlockSourceEnergy_scale_column (normI : A → ℝ) (first prefactor : ι → ℂ)
    (atZero : ι → ℕ → ℂ) (phase : A → A → A → ℂ)
    (a₀ ρ₀ lam gamma : A → ℂ) (scalar : ℂ) (pow sup : A)
    (rows marks columns : Finset A) (inputs : Finset (A × A))
    (hlam : ∀ c ∈ columns, lam c = scalar * gamma c) :
    D.rawBlockSourceEnergy normI first prefactor atZero phase a₀ ρ₀ lam
      pow sup rows marks columns inputs =
      ‖scalar‖ ^ 2 * D.rawBlockSourceEnergy normI first prefactor atZero phase
        a₀ ρ₀ gamma pow sup rows marks columns inputs := by
  unfold rawBlockSourceEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [D.rawSourceRow_scale_column normI first prefactor atZero phase
    a₀ ρ₀ lam gamma scalar marks columns inputs hlam,
    norm_mul, mul_pow]

/-- Complete original-row/original-input exit with the original column
weight retained. The coefficient outside the hybrid norm has the exact
squared size `(C / B)^2 / N`, the paper's column and full-cube powers. -/
theorem weighted_raw_frozen_row_block_exit
    (normI : A →* ℝ) (hpos : ∀ a, 0 < normI a)
    (first prefactor : ι → ℂ) (atZero : ι → ℕ → ℂ)
    (phase : A → A → A → ℂ) (a₀ ρ₀ lam : A → ℂ)
    (K N B : ℝ) (hN : 0 < N) (hB : 0 < B) (pow sup : A)
    (rows marks columns : Finset A) (inputs : Finset (A × A))
    (hrows : ∀ k ∈ rows, normI k ≤ K)
    (hρ₀ : ∀ d, (∀ p, PrimeCoordinates.valuation D.coords d p ≤ 1) →
      PrimeCoordinates.Avoids D.coords D.support d → ‖ρ₀ d‖ = 1)
    (hmarks : ∀ P ∈ marks, PrimeCoordinates.Avoids D.coords D.support P)
    (ha₀ : ∀ P ∈ marks, ‖a₀ P‖ ≤ 1)
    (hcolumns : ∀ c ∈ columns, PrimeCoordinates.Avoids D.coords D.ordinary c)
    (hlam : ∀ c ∈ columns, ‖lam c‖ ≤ 1)
    (hcolumnLower : ∀ c ∈ columns, N ≤ normI c)
    (hsupport : ∀ q ∈ inputs, PrimeCoordinates.Supported D.coords D.ordinary q.1)
    (haway : ∀ q ∈ inputs, PrimeCoordinates.Avoids D.coords D.ordinary q.2)
    (hphase : ∀ c ∈ columns, ∀ q ∈ inputs, ‖phase c q.1 q.2‖ ≤ 1)
    (hlower : ∀ q ∈ inputs,
      B ≤ normI (PrimeCoordinates.residualCubeFactor D.coords q.1 * q.2)) :
    let residual := PrimeCoordinates.residualRows D.coords D.support pow sup rows
    let pairs := D.frozenInputPairs normI first prefactor atZero inputs
    let Ω := D.tableOmega normI first prefactor atZero (D.frozenPhase phase)
    let C := D.tableMajorant normI first prefactor atZero
    let gamma := unitAnnularColumn normI N lam
    (1 ≤ D.residualParameter normI K pow sup) ∧
    (∀ d ∈ residual, (∀ p, PrimeCoordinates.valuation D.coords d p ≤ 1) ∧
      PrimeCoordinates.Avoids D.coords D.support d ∧
      normI d ≤ D.residualParameter normI K pow sup) ∧
    (∀ P ∈ marks, ‖D.mark a₀ P‖ ≤ 1) ∧
    (∀ c ∈ columns, ∀ b ∈ pairs.image cubeProduct,
      ‖D.unitBeta normI gamma Ω B C c b‖ ≤ 1) ∧
    D.rawBlockSourceEnergy normI first prefactor atZero phase a₀ ρ₀
      (annularColumn normI lam) pow sup rows marks columns inputs =
      ((C / B) ^ 2 / N) * HeckeSkeleton.LowHybrid.hybridEnergy
        (fun a b => D.symbol a b) (PrimeCoordinates.Coprime D.coords) normI
        (D.mark a₀) (D.unitBeta normI gamma Ω B C)
        residual marks columns (pairs.image cubeProduct) := by
  have h := D.raw_frozen_row_block_exit normI hpos first prefactor atZero phase
    a₀ ρ₀ (unitAnnularColumn normI N lam) K B hB pow sup rows marks columns inputs
    hrows hρ₀ hmarks ha₀ hcolumns
    (fun c hc => unitAnnularColumn_norm_le normI N hN lam c
      (hcolumnLower c hc) (hlam c hc)) hsupport haway hphase hlower
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, ?_⟩
  rw [D.rawBlockSourceEnergy_scale_column normI first prefactor atZero phase
    a₀ ρ₀ (annularColumn normI lam) (unitAnnularColumn normI N lam)
    (Real.sqrt N : ℂ)⁻¹ pow sup rows marks columns inputs
    (fun c hc => annularColumn_eq_scalar_unit normI N hN lam c),
    inv_sqrt_norm_sq N hN, h.2.2.2.2]
  ring

end Data

end

end HeckeSkeleton.LowFrozenCube.FrozenReduction
