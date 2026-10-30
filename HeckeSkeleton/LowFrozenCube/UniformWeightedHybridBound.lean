import HeckeSkeleton.LowFrozenCube.WeightedHybridBound

/-!
# A single weighted LOW-HYBRID constant for all frozen data

The arithmetic coordinates, symbol, norm counting estimate and the two sieve
inputs are fixed before the constant is chosen. Every frozen support, ordinary
set, digit and minimum is quantified afterwards. The proof uses the already
constructed exact weighted frozen exit; it adds no energy hypothesis.
-/

namespace HeckeSkeleton.LowFrozenCube.FrozenReduction

open scoped BigOperators Classical

noncomputable section

variable {ι A : Type*} [CommMonoid A]

namespace Data

/-- The complete weighted source bound at an explicitly supplied constant.
This abbreviation is used to pass one constant through the source ledger. -/
def WeightedRawHybridBound (D : Data ι A) (normI : A →* ℝ)
    (eps C0 : ℝ) : Prop :=
      ∀ R K N B L Nmin Bmin : ℝ,
      1 ≤ K → 1 ≤ N → 1 ≤ B → 1 ≤ L → 0 < Nmin → 0 < Bmin →
      ∀ (first prefactor : ι → ℂ) (atZero : ι → ℕ → ℂ)
        (phase : A → A → A → ℂ) (a₀ ρ₀ lam : A → ℂ)
        (pow sup : A) (rows marks columns : Finset A) (inputs : Finset (A × A)),
        (∀ k ∈ rows, normI k ≤ R) →
        (∀ d ∈ PrimeCoordinates.residualRows D.coords D.support pow sup rows, normI d ≤ K) →
        (∀ d, (∀ p, PrimeCoordinates.valuation D.coords d p ≤ 1) →
          PrimeCoordinates.Avoids D.coords D.support d → ‖ρ₀ d‖ = 1) →
        (∀ P ∈ marks, PrimeCoordinates.Avoids D.coords D.support P) →
        (∀ P ∈ marks, HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree D.coords P ∧
          normI P ≤ L) →
        (∀ P ∈ marks, ‖a₀ P‖ ≤ 1) →
        (∀ c ∈ columns, PrimeCoordinates.Avoids D.coords D.ordinary c) →
        (∀ c ∈ columns, HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree D.coords c ∧
          normI c ≤ N) →
        (∀ c ∈ columns, ‖lam c‖ ≤ 1) →
        (∀ c ∈ columns, Nmin ≤ normI c) →
        (∀ u ∈ inputs, PrimeCoordinates.Supported D.coords D.ordinary u.1) →
        (∀ u ∈ inputs, PrimeCoordinates.Avoids D.coords D.ordinary u.2) →
        (∀ c ∈ columns, ∀ u ∈ inputs, ‖phase c u.1 u.2‖ ≤ 1) →
        (∀ u ∈ inputs,
          Bmin ≤ normI (PrimeCoordinates.residualCubeFactor D.coords u.1 * u.2)) →
        (∀ u ∈ inputs,
          normI (PrimeCoordinates.residualCubeFactor D.coords u.1 * u.2) ≤ B) →
        D.rawBlockSourceEnergy normI first prefactor atZero phase a₀ ρ₀
          (annularColumn normI lam) pow sup rows marks columns inputs ≤
          ((D.tableMajorant normI first prefactor atZero / Bmin) ^ 2 / Nmin) *
            (C0 * (K * N * B * L) ^ eps * (K + N * B) * B *
              (N + L + (N * L) ^ (2 / 3 : ℝ)))

/-- The weighted source constant is uniform in all frozen data sharing the
fixed prime coordinates and sextic symbol. In particular it is independent
of the support, ordinary prime set, digit and minimum. -/
theorem uniform_weighted_raw_hybrid_bound
    (coords : A ≃* Multiplicative (ι →₀ ℕ))
    (symbol : A → A →* ℂ)
    (hleft : ∀ a b c, symbol (a * b) c = symbol a c * symbol b c)
    (h6 : ∀ a b, symbol a b ^ 6 =
      if PrimeCoordinates.Coprime coords a b then (1 : ℂ) else 0)
    (normI : A →* ℝ) (q : A → ℕ)
    (hnatural : ∀ a, normI a = (q a : ℝ)) (hqpos : ∀ a, 1 ≤ q a)
    (Ccount : ℝ) (hCcount : 0 < Ccount)
    (hcount : HeckeSkeleton.LowHybrid.LinearNormCounting q Ccount)
    (hq : HeckeSkeleton.LowHybrid.QuadraticSieveInput normI
      (HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree coords) (fun a b => symbol a b))
    (hc : HeckeSkeleton.LowHybrid.CubicSieveInput normI
      (HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree coords) (fun a b => symbol a b))
    (eps : ℝ) (heps : 0 < eps) :
    ∃ C0 : ℝ, 0 < C0 ∧ ∀ D : Data ι A,
      D.coords = coords → D.symbol = symbol → WeightedRawHybridBound D normI eps C0 := by
  have hnorm := HeckeSkeleton.LowHybrid.one_le_real_norm_of_natural q normI hnatural hqpos
  have hpos (a : A) : 0 < normI a := lt_of_lt_of_le zero_lt_one (hnorm a)
  obtain ⟨C0, hC0, hhybrid⟩ := HeckeSkeleton.LowHybrid.hybrid_energy_bounded
    coords normI q hnatural hqpos Ccount hCcount hcount (fun a b => symbol a b)
    hleft (fun a b c => (symbol a).map_mul b c) h6 hq hc eps heps
  refine ⟨C0, hC0, ?_⟩
  intro D hcoords hsymbol
  rw [← hcoords, ← hsymbol] at hhybrid
  unfold WeightedRawHybridBound
  intro R K N B L Nmin Bmin hK hN hB hL hNmin hBmin first prefactor atZero phase
    a₀ ρ₀ lam pow sup rows marks columns inputs hrows hresnorm hρ₀ hmarks hmarksf ha₀
    hcolumns hcolumnsf hlam hcolumnLower hsupport haway hphase hlower hupper
  have hexit := D.weighted_raw_frozen_row_block_exit normI hpos first prefactor atZero phase
    a₀ ρ₀ lam R Nmin Bmin hNmin hBmin pow sup rows marks columns inputs hrows hρ₀
    hmarks ha₀ hcolumns hlam hcolumnLower hsupport haway hphase hlower
  dsimp only at hexit
  obtain ⟨hKr, hres, ha, hbeta, heq⟩ := hexit
  have hcubes : ∀ b ∈ (D.frozenInputPairs normI first prefactor atZero inputs).image cubeProduct,
      normI b ≤ B := by
    intro b hb
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
    exact hupper v ((D.mem_activeInputBlock normI first prefactor atZero inputs v).mp hv).1
  rw [heq]
  apply mul_le_mul_of_nonneg_left _ (div_nonneg (sq_nonneg _) (le_of_lt hNmin))
  exact hhybrid K N B L hK hN hB hL
    (PrimeCoordinates.residualRows D.coords D.support pow sup rows) marks columns
    ((D.frozenInputPairs normI first prefactor atZero inputs).image cubeProduct)
    (D.mark a₀)
    (D.unitBeta normI (unitAnnularColumn normI Nmin lam)
      (D.tableOmega normI first prefactor atZero (D.frozenPhase phase))
      Bmin (D.tableMajorant normI first prefactor atZero))
    (fun d hd => ⟨(hres d hd).1, hresnorm d hd⟩)
    hmarksf hcolumnsf hcubes ha hbeta

end Data

end

end HeckeSkeleton.LowFrozenCube.FrozenReduction
