import HeckeSkeleton.LowFrozenCube.TableExit
import HeckeSkeleton.LowFrozenCube.RowCoordinates

/-!
# A fixed block of original rows enters the frozen hybrid norm

The powerful and support factors are constructed from each original row.
Fixing those factors leaves a squarefree, support-free hybrid row, whose
norm parameter is the original bound divided by the two fixed norms.
The finite energy identity retains the original row indices on its left.
-/

namespace HeckeSkeleton.LowFrozenCube.FrozenReduction

open scoped BigOperators Classical

noncomputable section

variable {ι A : Type*} [CommMonoid A]

namespace Data

variable (D : Data ι A)

def blockSourceEnergy (normI : A → ℝ) (a₀ ρ₀ lam : A → ℂ)
    (Ω : A → A → A → ℂ) (pow sup : A) (rows marks columns : Finset A)
    (pairs : Finset (A × A)) : ℝ :=
  ∑ k ∈ PrimeCoordinates.rowBlock D.coords D.support pow sup rows,
    ‖D.sourceRow normI a₀ ρ₀ lam Ω marks columns pairs
      (PrimeCoordinates.residualRowFactor D.coords D.support k)‖ ^ 2

def residualParameter (_D : Data ι A) (normI : A → ℝ) (K : ℝ) (pow sup : A) : ℝ :=
  max 1 (K / (normI pow * normI sup))

theorem residualParameter_one_le (normI : A → ℝ) (K : ℝ) (pow sup : A) :
    1 ≤ D.residualParameter normI K pow sup := le_max_left _ _

theorem residualRows_admissible (normI : A →* ℝ) (hpos : ∀ a, 0 < normI a)
    (K : ℝ) (pow sup : A) (rows : Finset A)
    (hrows : ∀ k ∈ rows, normI k ≤ K)
    (d : A) (hd : d ∈ PrimeCoordinates.residualRows D.coords D.support pow sup rows) :
    (∀ p, PrimeCoordinates.valuation D.coords d p ≤ 1) ∧
    PrimeCoordinates.Avoids D.coords D.support d ∧
    normI d ≤ D.residualParameter normI K pow sup := by
  refine ⟨PrimeCoordinates.residualRows_squarefree D.coords D.support pow sup rows d hd,
    PrimeCoordinates.residualRows_avoids D.coords D.support pow sup rows d hd, ?_⟩
  exact (PrimeCoordinates.residualRows_norm_le D.coords D.support pow sup rows
    normI hpos K hrows d hd).trans (le_max_right _ _)

theorem blockSourceEnergy_reindex (normI : A → ℝ) (a₀ ρ₀ lam : A → ℂ)
    (Ω : A → A → A → ℂ) (pow sup : A) (rows marks columns : Finset A)
    (pairs : Finset (A × A)) :
    D.blockSourceEnergy normI a₀ ρ₀ lam Ω pow sup rows marks columns pairs =
      ∑ d ∈ PrimeCoordinates.residualRows D.coords D.support pow sup rows,
        ‖D.sourceRow normI a₀ ρ₀ lam Ω marks columns pairs d‖ ^ 2 :=
  PrimeCoordinates.sum_rowBlock_reindex D.coords D.support pow sup rows
    (fun d => ‖D.sourceRow normI a₀ ρ₀ lam Ω marks columns pairs d‖ ^ 2)

/-- The full explicit table exit for a naturally constructed original-row
block. The final row support conditions and its sieve parameter are derived,
as are the row-independent coefficient bounds and the exact energy scalar. -/
theorem local_table_row_block_exit
    (normI : A →* ℝ) (hpos : ∀ a, 0 < normI a)
    (first prefactor : ι → ℂ) (atZero : ι → ℕ → ℂ)
    (phase : A → A → A → ℂ)
    (hminimum : PrimeCoordinates.Supported D.coords D.ordinary D.minimum)
    (a₀ ρ₀ lam : A → ℂ) (K B : ℝ) (hB : 0 < B)
    (pow sup : A) (rows marks columns : Finset A) (pairs : Finset (A × A))
    (hrows : ∀ k ∈ rows, normI k ≤ K)
    (hρ₀ : ∀ d, (∀ p, PrimeCoordinates.valuation D.coords d p ≤ 1) →
      PrimeCoordinates.Avoids D.coords D.support d → ‖ρ₀ d‖ = 1)
    (hmarks : ∀ P ∈ marks, PrimeCoordinates.Avoids D.coords D.support P)
    (ha₀ : ∀ P ∈ marks, ‖a₀ P‖ ≤ 1)
    (hcolumns : ∀ c ∈ columns, PrimeCoordinates.Avoids D.coords D.ordinary c)
    (hlam : ∀ c ∈ columns, ‖lam c‖ ≤ 1)
    (hpairs : ∀ q ∈ pairs, D.CanonicalCube q.1 ∧
      PrimeCoordinates.Avoids D.coords D.ordinary q.2)
    (hphase : ∀ c ∈ columns, ∀ q ∈ pairs, ‖phase c q.1 q.2‖ ≤ 1)
    (hlower : ∀ q ∈ pairs, B ≤ normI (cubeProduct q)) :
    let residual := PrimeCoordinates.residualRows D.coords D.support pow sup rows
    let Ω := D.tableOmega normI first prefactor atZero phase
    let C := D.tableMajorant normI first prefactor atZero
    (1 ≤ D.residualParameter normI K pow sup) ∧
    (∀ d ∈ residual, (∀ p, PrimeCoordinates.valuation D.coords d p ≤ 1) ∧
      PrimeCoordinates.Avoids D.coords D.support d ∧
      normI d ≤ D.residualParameter normI K pow sup) ∧
    (∀ P ∈ marks, ‖D.mark a₀ P‖ ≤ 1) ∧
    (∀ c ∈ columns, ∀ b ∈ pairs.image cubeProduct,
      ‖D.unitBeta normI lam Ω B C c b‖ ≤ 1) ∧
    D.blockSourceEnergy normI a₀ ρ₀ lam Ω pow sup rows marks columns pairs =
      (C / B) ^ 2 * HeckeSkeleton.LowHybrid.hybridEnergy
        (fun a b => D.symbol a b) (PrimeCoordinates.Coprime D.coords) normI
        (D.mark a₀) (D.unitBeta normI lam Ω B C)
        residual marks columns (pairs.image cubeProduct) := by
  have hres : ∀ d ∈ PrimeCoordinates.residualRows D.coords D.support pow sup rows,
      (∀ p, PrimeCoordinates.valuation D.coords d p ≤ 1) ∧
      PrimeCoordinates.Avoids D.coords D.support d ∧
      normI d ≤ D.residualParameter normI K pow sup :=
    D.residualRows_admissible normI hpos K pow sup rows hrows
  have h := D.local_table_frozen_exit normI hpos first prefactor atZero phase
    hminimum a₀ ρ₀ lam B hB
    (PrimeCoordinates.residualRows D.coords D.support pow sup rows)
    marks columns pairs (fun d hd => (hres d hd).2.1)
    (fun d hd => hρ₀ d (hres d hd).1 (hres d hd).2.1)
    hmarks ha₀ hcolumns hlam hpairs hphase hlower
  refine ⟨D.residualParameter_one_le normI K pow sup, hres, h.1, h.2.1, ?_⟩
  rw [D.blockSourceEnergy_reindex]
  exact h.2.2

end Data

end

end HeckeSkeleton.LowFrozenCube.FrozenReduction
