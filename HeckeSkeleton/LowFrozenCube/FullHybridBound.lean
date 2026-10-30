import HeckeSkeleton.LowFrozenCube.RawRowBlockExit
import HeckeSkeleton.LowHybrid.Corollaries

/-!
# The original frozen row block is bounded by LOW-HYBRID

This theorem composes the proved raw finite-sum reduction with the proved
hybrid inequality. Its left side still uses the original row ideal and
original local ideal. The complete cube, the residual squarefree rows, both
coefficient bounds, and the exact outside scalar are all derived.
-/

namespace HeckeSkeleton.LowFrozenCube.FrozenReduction

open scoped BigOperators Classical

noncomputable section

variable {ι A : Type*} [CommMonoid A]

namespace Data

variable (D : Data ι A)

theorem symbol_mul_first (a b c : A) :
    D.symbol (a * b) c = D.symbol a c * D.symbol b c := by
  calc
    D.symbol (a * b) c = D.symbol c (a * b) := D.reciprocal _ _
    _ = D.symbol c a * D.symbol c b := (D.symbol c).map_mul a b
    _ = _ := by rw [D.reciprocal c a, D.reciprocal c b]

/-- A bound for the actual original frozen block, with no assumed energy
estimate or normal-form identity. The displayed `tableMajorant / Bmin` is
the exact scalar furnished by the local table and the full-cube annulus.
The remaining four scale factors are precisely those of LOW-HYBRID.
-/
theorem raw_frozen_hybrid_bound
    (normI : A →* ℝ) (q : A → ℕ)
    (hnatural : ∀ a, normI a = (q a : ℝ)) (hqpos : ∀ a, 1 ≤ q a)
    (Ccount : ℝ) (hCcount : 0 < Ccount)
    (hcount : HeckeSkeleton.LowHybrid.LinearNormCounting q Ccount)
    (hq : HeckeSkeleton.LowHybrid.QuadraticSieveInput normI
      (HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree D.coords) (fun a b => D.symbol a b))
    (hc : HeckeSkeleton.LowHybrid.CubicSieveInput normI
      (HeckeSkeleton.LowHybrid.PrimeArithmetic.Squarefree D.coords) (fun a b => D.symbol a b))
    (eps : ℝ) (heps : 0 < eps) :
    ∃ C0 : ℝ, 0 < C0 ∧
      ∀ K N B L Bmin : ℝ, 1 ≤ N → 1 ≤ B → 1 ≤ L → 0 < Bmin →
      ∀ (first prefactor : ι → ℂ) (atZero : ι → ℕ → ℂ)
        (phase : A → A → A → ℂ) (a₀ ρ₀ lam : A → ℂ)
        (pow sup : A) (rows marks columns : Finset A) (inputs : Finset (A × A)),
        (∀ k ∈ rows, normI k ≤ K) →
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
        (∀ u ∈ inputs, PrimeCoordinates.Supported D.coords D.ordinary u.1) →
        (∀ u ∈ inputs, PrimeCoordinates.Avoids D.coords D.ordinary u.2) →
        (∀ c ∈ columns, ∀ u ∈ inputs, ‖phase c u.1 u.2‖ ≤ 1) →
        (∀ u ∈ inputs,
          Bmin ≤ normI (PrimeCoordinates.residualCubeFactor D.coords u.1 * u.2)) →
        (∀ u ∈ inputs,
          normI (PrimeCoordinates.residualCubeFactor D.coords u.1 * u.2) ≤ B) →
        D.rawBlockSourceEnergy normI first prefactor atZero phase a₀ ρ₀ lam
          pow sup rows marks columns inputs ≤
          (D.tableMajorant normI first prefactor atZero / Bmin) ^ 2 *
            (C0 * (D.residualParameter normI K pow sup * N * B * L) ^ eps *
              (D.residualParameter normI K pow sup + N * B) * B *
                (N + L + (N * L) ^ (2 / 3 : ℝ))) := by
  have hnorm := HeckeSkeleton.LowHybrid.one_le_real_norm_of_natural
    q normI hnatural hqpos
  have hpos (a : A) : 0 < normI a := lt_of_lt_of_le zero_lt_one (hnorm a)
  obtain ⟨C0, hC0, hhybrid⟩ := HeckeSkeleton.LowHybrid.hybrid_energy_bounded
    D.coords normI q hnatural hqpos Ccount hCcount hcount (fun a b => D.symbol a b)
    D.symbol_mul_first (fun a b c => (D.symbol a).map_mul b c) D.sixth hq hc eps heps
  refine ⟨C0, hC0, ?_⟩
  intro K N B L Bmin hN hB hL hBmin first prefactor atZero phase a₀ ρ₀ lam
    pow sup rows marks columns inputs hrows hρ₀ hmarks hmarksf ha₀
    hcolumns hcolumnsf hlam hsupport haway hphase hlower hupper
  have hexit := D.raw_frozen_row_block_exit normI hpos first prefactor atZero phase
    a₀ ρ₀ lam K Bmin hBmin pow sup rows marks columns inputs hrows hρ₀
    hmarks ha₀ hcolumns hlam hsupport haway hphase hlower
  dsimp only at hexit
  obtain ⟨hKr, hres, ha, hbeta, heq⟩ := hexit
  have hcubes : ∀ b ∈ (D.frozenInputPairs normI first prefactor atZero inputs).image cubeProduct,
      normI b ≤ B := by
    intro b hb
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
    exact hupper v ((D.mem_activeInputBlock normI first prefactor atZero inputs v).mp hv).1
  rw [heq]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  exact hhybrid (D.residualParameter normI K pow sup) N B L hKr hN hB hL
    (PrimeCoordinates.residualRows D.coords D.support pow sup rows) marks columns
    ((D.frozenInputPairs normI first prefactor atZero inputs).image cubeProduct)
    (D.mark a₀)
    (D.unitBeta normI lam (D.tableOmega normI first prefactor atZero (D.frozenPhase phase))
      Bmin (D.tableMajorant normI first prefactor atZero))
    (fun d hd => ⟨(hres d hd).1, (hres d hd).2.2⟩)
    hmarksf hcolumnsf hcubes ha hbeta

#print axioms raw_frozen_hybrid_bound

end Data

end
end HeckeSkeleton.LowFrozenCube.FrozenReduction
