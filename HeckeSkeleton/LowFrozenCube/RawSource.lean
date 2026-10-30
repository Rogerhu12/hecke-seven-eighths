import HeckeSkeleton.LowFrozenCube.RawInput

/-!
# The original local-index row equals the constructed frozen row

The source here uses the original local ideal `a`, its actual exponent
vector, all three unfrozen coefficients, and the literal local table. Zero
table entries are removed within the proof. The final full-cube support and
normalized coefficients are constructed from this original finite sum.
-/

namespace HeckeSkeleton.LowFrozenCube.FrozenReduction

open scoped BigOperators Classical

noncomputable section

variable {ι A : Type*} [CommMonoid A]

namespace Data

variable (D : Data ι A)

def frozenPhase (phase : A → A → A → ℂ) (c x n : A) : ℂ :=
  phase c (D.minimum * x ^ 3) n

def rawSourceTerm (normI : A → ℝ) (first prefactor : ι → ℂ)
    (atZero : ι → ℕ → ℂ) (phase : A → A → A → ℂ)
    (a₀ ρ₀ lam : A → ℂ) (d P c a n : A) : ℂ :=
  (markCoefficient D.symbol D.ordinary D.ordinarySymbol D.digit
      (PrimeCoordinates.valuation D.coords a) a₀ a P / (Real.sqrt (normI P) : ℂ)) *
    rowCoefficient D.symbol D.ordinary D.ordinarySymbol D.digit
      (PrimeCoordinates.valuation D.coords a) ρ₀ a d *
    columnCoefficient D.symbol D.ordinary D.ordinarySymbol D.digit
      (PrimeCoordinates.valuation D.coords a) lam a c *
    (phase c a n * D.rawTable normI first prefactor atZero a / (normI n : ℂ)) *
      D.mixedPhase d P c n

def rawSourceRow (normI : A → ℝ) (first prefactor : ι → ℂ)
    (atZero : ι → ℕ → ℂ) (phase : A → A → A → ℂ)
    (a₀ ρ₀ lam : A → ℂ) (marks columns : Finset A)
    (inputs : Finset (A × A)) (d : A) : ℂ :=
  ∑ P ∈ marks, ∑ c ∈ columns, ∑ q ∈ D.minimumBlock inputs,
    D.rawSourceTerm normI first prefactor atZero phase a₀ ρ₀ lam d P c q.1 q.2

theorem rawSourceTerm_zero (normI : A → ℝ) (first prefactor : ι → ℂ)
    (atZero : ι → ℕ → ℂ) (phase : A → A → A → ℂ)
    (a₀ ρ₀ lam : A → ℂ) (d P c a n : A)
    (hz : D.rawTable normI first prefactor atZero a = 0) :
    D.rawSourceTerm normI first prefactor atZero phase a₀ ρ₀ lam d P c a n = 0 := by
  simp [rawSourceTerm, hz]

/-- A genuine factorization of the original index identifies every original
coefficient and local-table factor with its frozen-source expression. -/
theorem rawSourceTerm_eq_sourceTerm (normI : A → ℝ) (first prefactor : ι → ℂ)
    (atZero : ι → ℕ → ℂ) (phase : A → A → A → ℂ)
    (a₀ ρ₀ lam : A → ℂ) (d P c a x n : A)
    (ha : a = D.minimum * x ^ 3) :
    D.rawSourceTerm normI first prefactor atZero phase a₀ ρ₀ lam d P c a n =
      D.sourceTerm normI a₀ ρ₀ lam
        (D.tableOmega normI first prefactor atZero (D.frozenPhase phase)) d P c x n := by
  subst a
  rfl

/-- This equality starts at the raw finite sum, including forbidden local
residues. Their contributions are zero, and the remaining reindexing is
injective by the actual prime-coordinate reconstruction. -/
theorem rawSourceRow_eq_sourceRow (normI : A → ℝ) (first prefactor : ι → ℂ)
    (atZero : ι → ℕ → ℂ) (phase : A → A → A → ℂ)
    (a₀ ρ₀ lam : A → ℂ) (marks columns : Finset A) (inputs : Finset (A × A))
    (hsupport : ∀ q ∈ inputs, PrimeCoordinates.Supported D.coords D.ordinary q.1)
    (d : A) :
    D.rawSourceRow normI first prefactor atZero phase a₀ ρ₀ lam marks columns inputs d =
      D.sourceRow normI a₀ ρ₀ lam
        (D.tableOmega normI first prefactor atZero (D.frozenPhase phase))
        marks columns (D.frozenInputPairs normI first prefactor atZero inputs) d := by
  unfold rawSourceRow sourceRow
  apply Finset.sum_congr rfl
  intro P hP
  apply Finset.sum_congr rfl
  intro c hc
  calc
    (∑ q ∈ D.minimumBlock inputs,
        D.rawSourceTerm normI first prefactor atZero phase a₀ ρ₀ lam d P c q.1 q.2) =
        ∑ q ∈ D.activeInputBlock normI first prefactor atZero inputs,
          D.rawSourceTerm normI first prefactor atZero phase a₀ ρ₀ lam d P c q.1 q.2 := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro q hq hqnot
      apply D.rawSourceTerm_zero
      by_contra hn
      exact hqnot (Finset.mem_filter.mpr ⟨hq, hn⟩)
    _ = _ := by
      unfold frozenInputPairs
      rw [Finset.sum_image (D.freezePair_injOn normI first prefactor atZero inputs hsupport)]
      apply Finset.sum_congr rfl
      intro q hq
      exact D.rawSourceTerm_eq_sourceTerm normI first prefactor atZero phase
        a₀ ρ₀ lam d P c q.1 (PrimeCoordinates.residualCubeFactor D.coords q.1) q.2
        (D.activeInput_reconstruct normI first prefactor atZero inputs hsupport q hq)

theorem frozenPhase_norm_le (normI : A → ℝ) (first prefactor : ι → ℂ)
    (atZero : ι → ℕ → ℂ) (phase : A → A → A → ℂ)
    (columns : Finset A) (inputs : Finset (A × A))
    (hsupport : ∀ q ∈ inputs, PrimeCoordinates.Supported D.coords D.ordinary q.1)
    (hphase : ∀ c ∈ columns, ∀ q ∈ inputs, ‖phase c q.1 q.2‖ ≤ 1)
    (c : A) (hc : c ∈ columns) (q : A × A)
    (hq : q ∈ D.frozenInputPairs normI first prefactor atZero inputs) :
    ‖D.frozenPhase phase c q.1 q.2‖ ≤ 1 := by
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hq
  have hr' := (D.mem_activeInputBlock normI first prefactor atZero inputs r).mp hr
  change ‖phase c (D.minimum * (PrimeCoordinates.residualCubeFactor D.coords r.1) ^ 3)
    r.2‖ ≤ 1
  rw [← D.activeInput_reconstruct normI first prefactor atZero inputs hsupport r hr]
  exact hphase c hc r hr'.1

theorem frozenInputPairs_norm_lower (normI : A → ℝ) (first prefactor : ι → ℂ)
    (atZero : ι → ℕ → ℂ) (inputs : Finset (A × A)) (B : ℝ)
    (hlower : ∀ q ∈ inputs,
      B ≤ normI (PrimeCoordinates.residualCubeFactor D.coords q.1 * q.2))
    (q : A × A) (hq : q ∈ D.frozenInputPairs normI first prefactor atZero inputs) :
    B ≤ normI (cubeProduct q) := by
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hq
  exact hlower r ((D.mem_activeInputBlock normI first prefactor atZero inputs r).mp hr).1

/-- End-to-end frozen reduction from original local indices. There is no
admissibility, canonical-pair, chosen-splitting, coefficient-majorant, or
separated-row assumption: those conclusions are derived from the table. -/
theorem raw_local_table_frozen_exit
    (normI : A →* ℝ) (hpos : ∀ a, 0 < normI a)
    (first prefactor : ι → ℂ) (atZero : ι → ℕ → ℂ)
    (phase : A → A → A → ℂ)
    (hminimum : PrimeCoordinates.Supported D.coords D.ordinary D.minimum)
    (a₀ ρ₀ lam : A → ℂ) (B : ℝ) (hB : 0 < B)
    (rows marks columns : Finset A) (inputs : Finset (A × A))
    (hrows : ∀ d ∈ rows, PrimeCoordinates.Avoids D.coords D.support d)
    (hρ₀ : ∀ d ∈ rows, ‖ρ₀ d‖ = 1)
    (hmarks : ∀ P ∈ marks, PrimeCoordinates.Avoids D.coords D.support P)
    (ha₀ : ∀ P ∈ marks, ‖a₀ P‖ ≤ 1)
    (hcolumns : ∀ c ∈ columns, PrimeCoordinates.Avoids D.coords D.ordinary c)
    (hlam : ∀ c ∈ columns, ‖lam c‖ ≤ 1)
    (hsupport : ∀ q ∈ inputs, PrimeCoordinates.Supported D.coords D.ordinary q.1)
    (haway : ∀ q ∈ inputs, PrimeCoordinates.Avoids D.coords D.ordinary q.2)
    (hphase : ∀ c ∈ columns, ∀ q ∈ inputs, ‖phase c q.1 q.2‖ ≤ 1)
    (hlower : ∀ q ∈ inputs,
      B ≤ normI (PrimeCoordinates.residualCubeFactor D.coords q.1 * q.2)) :
    let pairs := D.frozenInputPairs normI first prefactor atZero inputs
    let Ω := D.tableOmega normI first prefactor atZero (D.frozenPhase phase)
    let C := D.tableMajorant normI first prefactor atZero
    (∀ P ∈ marks, ‖D.mark a₀ P‖ ≤ 1) ∧
    (∀ c ∈ columns, ∀ b ∈ pairs.image cubeProduct,
      ‖D.unitBeta normI lam Ω B C c b‖ ≤ 1) ∧
    (∑ d ∈ rows,
      ‖D.rawSourceRow normI first prefactor atZero phase a₀ ρ₀ lam marks columns inputs d‖ ^ 2) =
      (C / B) ^ 2 * HeckeSkeleton.LowHybrid.hybridEnergy
        (fun a b => D.symbol a b) (PrimeCoordinates.Coprime D.coords) normI
        (D.mark a₀) (D.unitBeta normI lam Ω B C)
        rows marks columns (pairs.image cubeProduct) := by
  have h := D.local_table_frozen_exit normI hpos first prefactor atZero
    (D.frozenPhase phase) hminimum a₀ ρ₀ lam B hB rows marks columns
    (D.frozenInputPairs normI first prefactor atZero inputs) hrows hρ₀
    hmarks ha₀ hcolumns hlam
    (D.frozenInputPairs_canonical normI first prefactor atZero inputs haway)
    (D.frozenPhase_norm_le normI first prefactor atZero phase columns inputs hsupport hphase)
    (D.frozenInputPairs_norm_lower normI first prefactor atZero inputs B hlower)
  refine ⟨h.1, h.2.1, ?_⟩
  calc
    (∑ d ∈ rows,
        ‖D.rawSourceRow normI first prefactor atZero phase a₀ ρ₀ lam
          marks columns inputs d‖ ^ 2) =
        ∑ d ∈ rows, ‖D.sourceRow normI a₀ ρ₀ lam
          (D.tableOmega normI first prefactor atZero (D.frozenPhase phase))
          marks columns (D.frozenInputPairs normI first prefactor atZero inputs) d‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [D.rawSourceRow_eq_sourceRow normI first prefactor atZero phase
        a₀ ρ₀ lam marks columns inputs hsupport d]
    _ = _ := h.2.2

end Data

end

end HeckeSkeleton.LowFrozenCube.FrozenReduction
