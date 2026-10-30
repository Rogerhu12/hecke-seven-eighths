import HeckeSkeleton.LowFrozenCube.RawSource
import HeckeSkeleton.LowFrozenCube.RowTableExit

/-!
# Complete frozen row-block exit from the original finite indices

Both sides of the construction are automatic: original rows are split into
powerful, supported, and squarefree residual factors; original local indices
are frozen after their local-table zero terms have been removed. The result
is the literal normalized hybrid energy, with derived coefficient bounds.
-/

namespace HeckeSkeleton.LowFrozenCube.FrozenReduction

open scoped BigOperators Classical

noncomputable section

variable {ι A : Type*} [CommMonoid A]

namespace Data

variable (D : Data ι A)

def rawBlockSourceEnergy (normI : A → ℝ) (first prefactor : ι → ℂ)
    (atZero : ι → ℕ → ℂ) (phase : A → A → A → ℂ)
    (a₀ ρ₀ lam : A → ℂ) (pow sup : A) (rows marks columns : Finset A)
    (inputs : Finset (A × A)) : ℝ :=
  ∑ k ∈ PrimeCoordinates.rowBlock D.coords D.support pow sup rows,
    ‖D.rawSourceRow normI first prefactor atZero phase a₀ ρ₀ lam marks columns inputs
      (PrimeCoordinates.residualRowFactor D.coords D.support k)‖ ^ 2

theorem rawBlockSourceEnergy_reindex (normI : A → ℝ) (first prefactor : ι → ℂ)
    (atZero : ι → ℕ → ℂ) (phase : A → A → A → ℂ)
    (a₀ ρ₀ lam : A → ℂ) (pow sup : A) (rows marks columns : Finset A)
    (inputs : Finset (A × A)) :
    D.rawBlockSourceEnergy normI first prefactor atZero phase a₀ ρ₀ lam
      pow sup rows marks columns inputs =
      ∑ d ∈ PrimeCoordinates.residualRows D.coords D.support pow sup rows,
        ‖D.rawSourceRow normI first prefactor atZero phase a₀ ρ₀ lam
          marks columns inputs d‖ ^ 2 :=
  PrimeCoordinates.sum_rowBlock_reindex D.coords D.support pow sup rows
    (fun d => ‖D.rawSourceRow normI first prefactor atZero phase a₀ ρ₀ lam
      marks columns inputs d‖ ^ 2)

/-- The complete exact frozen exit. There are no input assumptions asserting
an energy estimate, row identity, splitting map, admissible exponents,
canonical cube pairs, or whole-product local majorant. The empty local-table
case is included; a nonempty case supplies its minimum support automatically.
-/
theorem raw_frozen_row_block_exit
    (normI : A →* ℝ) (hpos : ∀ a, 0 < normI a)
    (first prefactor : ι → ℂ) (atZero : ι → ℕ → ℂ)
    (phase : A → A → A → ℂ) (a₀ ρ₀ lam : A → ℂ)
    (K B : ℝ) (hB : 0 < B) (pow sup : A)
    (rows marks columns : Finset A) (inputs : Finset (A × A))
    (hrows : ∀ k ∈ rows, normI k ≤ K)
    (hρ₀ : ∀ d, (∀ p, PrimeCoordinates.valuation D.coords d p ≤ 1) →
      PrimeCoordinates.Avoids D.coords D.support d → ‖ρ₀ d‖ = 1)
    (hmarks : ∀ P ∈ marks, PrimeCoordinates.Avoids D.coords D.support P)
    (ha₀ : ∀ P ∈ marks, ‖a₀ P‖ ≤ 1)
    (hcolumns : ∀ c ∈ columns, PrimeCoordinates.Avoids D.coords D.ordinary c)
    (hlam : ∀ c ∈ columns, ‖lam c‖ ≤ 1)
    (hsupport : ∀ q ∈ inputs, PrimeCoordinates.Supported D.coords D.ordinary q.1)
    (haway : ∀ q ∈ inputs, PrimeCoordinates.Avoids D.coords D.ordinary q.2)
    (hphase : ∀ c ∈ columns, ∀ q ∈ inputs, ‖phase c q.1 q.2‖ ≤ 1)
    (hlower : ∀ q ∈ inputs,
      B ≤ normI (PrimeCoordinates.residualCubeFactor D.coords q.1 * q.2)) :
    let residual := PrimeCoordinates.residualRows D.coords D.support pow sup rows
    let pairs := D.frozenInputPairs normI first prefactor atZero inputs
    let Ω := D.tableOmega normI first prefactor atZero (D.frozenPhase phase)
    let C := D.tableMajorant normI first prefactor atZero
    (1 ≤ D.residualParameter normI K pow sup) ∧
    (∀ d ∈ residual, (∀ p, PrimeCoordinates.valuation D.coords d p ≤ 1) ∧
      PrimeCoordinates.Avoids D.coords D.support d ∧
      normI d ≤ D.residualParameter normI K pow sup) ∧
    (∀ P ∈ marks, ‖D.mark a₀ P‖ ≤ 1) ∧
    (∀ c ∈ columns, ∀ b ∈ pairs.image cubeProduct,
      ‖D.unitBeta normI lam Ω B C c b‖ ≤ 1) ∧
    D.rawBlockSourceEnergy normI first prefactor atZero phase a₀ ρ₀ lam
      pow sup rows marks columns inputs =
      (C / B) ^ 2 * HeckeSkeleton.LowHybrid.hybridEnergy
        (fun a b => D.symbol a b) (PrimeCoordinates.Coprime D.coords) normI
        (D.mark a₀) (D.unitBeta normI lam Ω B C)
        residual marks columns (pairs.image cubeProduct) := by
  have hres : ∀ d ∈ PrimeCoordinates.residualRows D.coords D.support pow sup rows,
      (∀ p, PrimeCoordinates.valuation D.coords d p ≤ 1) ∧
      PrimeCoordinates.Avoids D.coords D.support d ∧
      normI d ≤ D.residualParameter normI K pow sup :=
    D.residualRows_admissible normI hpos K pow sup rows hrows
  by_cases hactive : (D.activeInputBlock normI first prefactor atZero inputs).Nonempty
  · obtain ⟨q, hq⟩ := hactive
    have hminimum := D.minimum_supported_of_activeInput normI first prefactor atZero
      inputs hsupport q hq
    have h := D.raw_local_table_frozen_exit normI hpos first prefactor atZero phase
      hminimum a₀ ρ₀ lam B hB
      (PrimeCoordinates.residualRows D.coords D.support pow sup rows)
      marks columns inputs (fun d hd => (hres d hd).2.1)
      (fun d hd => hρ₀ d (hres d hd).1 (hres d hd).2.1)
      hmarks ha₀ hcolumns hlam hsupport haway hphase hlower
    refine ⟨D.residualParameter_one_le normI K pow sup, hres, h.1, h.2.1, ?_⟩
    rw [D.rawBlockSourceEnergy_reindex]
    exact h.2.2
  · have hempty : D.activeInputBlock normI first prefactor atZero inputs = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hactive
    have hpairs : D.frozenInputPairs normI first prefactor atZero inputs = ∅ := by
      simp [frozenInputPairs, hempty]
    have hzero : ∀ d,
        D.rawSourceRow normI first prefactor atZero phase a₀ ρ₀ lam marks columns inputs d = 0 := by
      intro d
      rw [D.rawSourceRow_eq_sourceRow normI first prefactor atZero phase
        a₀ ρ₀ lam marks columns inputs hsupport d]
      simp [hpairs, sourceRow]
    refine ⟨D.residualParameter_one_le normI K pow sup, hres, ?_, ?_, ?_⟩
    · intro P hP
      rw [D.mark_norm a₀ P (hmarks P hP)]
      exact ha₀ P hP
    · intro c hc b hb
      simp [hpairs] at hb
    · simp [rawBlockSourceEnergy, hpairs, hzero,
        HeckeSkeleton.LowHybrid.hybridEnergy, HeckeSkeleton.LowHybrid.hybridRow]

end Data

end

end HeckeSkeleton.LowFrozenCube.FrozenReduction
