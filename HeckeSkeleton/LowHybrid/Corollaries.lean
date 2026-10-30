import HeckeSkeleton.LowHybrid.HybridEnergy
import HeckeSkeleton.LowHybrid.Homogeneity
import HeckeSkeleton.LowHybrid.CountingBridge

/-!
# LOW-HYBRID in coefficient-mass and bounded-coefficient forms

The first theorem permits arbitrary complex beta and uses its actual finite
maximum squared norm.  The second removes both coefficient masses when the
original coefficients have norm at most one.  Its extra harmonic mark mass
is absorbed uniformly into half of the requested epsilon.
-/

namespace HeckeSkeleton.LowHybrid

open scoped BigOperators Classical
open HeckeSkeleton.LowFrozenCube.PrimeCoordinates

noncomputable section

variable {ι A : Type*} [CommMonoid A]

/-- Arbitrary complex coefficients, with the original normalized mark mass
and the actual finite maximum squared beta coefficient. -/
theorem hybrid_energy_with_beta_mass
    (coords : A ≃* Multiplicative (ι →₀ ℕ))
    (normI : A →* ℝ) (q : A → ℕ)
    (hnatural : ∀ a, normI a = (q a : ℝ)) (hqpos : ∀ a, 1 ≤ q a)
    (Ccount : ℝ) (hCcount : 0 < Ccount) (hcount : LinearNormCounting q Ccount)
    (symbol : A → A → ℂ)
    (hleft : ∀ a b c, symbol (a * b) c = symbol a c * symbol b c)
    (hright : ∀ a b c, symbol a (b * c) = symbol a b * symbol a c)
    (h6 : ∀ a b, symbol a b ^ 6 = if Coprime coords a b then 1 else 0)
    (hq : QuadraticSieveInput normI (PrimeArithmetic.Squarefree coords) symbol)
    (hc : CubicSieveInput normI (PrimeArithmetic.Squarefree coords) symbol)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ C0 : ℝ, 0 < C0 ∧
      ∀ K N B L : ℝ, 1 ≤ K → 1 ≤ N → 1 ≤ B → 1 ≤ L →
      ∀ (rows marks columns cubes : Finset A) (a : A → ℂ) (beta : A → A → ℂ),
        (∀ k ∈ rows, PrimeArithmetic.Squarefree coords k ∧ normI k ≤ K) →
        (∀ p ∈ marks, PrimeArithmetic.Squarefree coords p ∧ normI p ≤ L) →
        (∀ n ∈ columns, PrimeArithmetic.Squarefree coords n ∧ normI n ≤ N) →
        (∀ b ∈ cubes, normI b ≤ B) →
        hybridEnergy symbol (Coprime coords) normI a beta rows marks columns cubes ≤
          C0 * (K * N * B * L) ^ eps * (K + N * B) * B *
            (N + L + (N * L) ^ (2 / 3 : ℝ)) *
            (∑ p ∈ marks, ‖a p‖ ^ 2 / normI p) * betaSquaredMass beta columns cubes := by
  obtain ⟨C0, hC0, hbound⟩ := hybrid_energy coords normI q hnatural hqpos
    Ccount hCcount hcount symbol hleft hright h6 hq hc eps heps
  refine ⟨C0, hC0, ?_⟩
  intro K N B L hK hN hB hL rows marks columns cubes a beta hrows hmarks hcolumns hcubes
  have h := hybridEnergy_beta_mass_of_unit symbol (Coprime coords) normI a beta
    rows marks columns cubes
    (C0 * (K * N * B * L) ^ eps * (K + N * B) * B *
      (N + L + (N * L) ^ (2 / 3 : ℝ)) * (∑ p ∈ marks, ‖a p‖ ^ 2 / normI p))
    (fun gamma hgamma => hbound K N B L hK hN hB hL
      rows marks columns cubes a gamma hrows hmarks hcolumns hcubes hgamma)
  exact h.trans_eq (by ring)

/-- The displayed LOW-HYBRID estimate for unit-bounded coefficients.
The constant is uniform in all four scales, all supports, and both original
coefficient families. No coefficient mass remains on the right. -/
theorem hybrid_energy_bounded
    (coords : A ≃* Multiplicative (ι →₀ ℕ))
    (normI : A →* ℝ) (q : A → ℕ)
    (hnatural : ∀ a, normI a = (q a : ℝ)) (hqpos : ∀ a, 1 ≤ q a)
    (Ccount : ℝ) (hCcount : 0 < Ccount) (hcount : LinearNormCounting q Ccount)
    (symbol : A → A → ℂ)
    (hleft : ∀ a b c, symbol (a * b) c = symbol a c * symbol b c)
    (hright : ∀ a b c, symbol a (b * c) = symbol a b * symbol a c)
    (h6 : ∀ a b, symbol a b ^ 6 = if Coprime coords a b then 1 else 0)
    (hq : QuadraticSieveInput normI (PrimeArithmetic.Squarefree coords) symbol)
    (hc : CubicSieveInput normI (PrimeArithmetic.Squarefree coords) symbol)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ C0 : ℝ, 0 < C0 ∧
      ∀ K N B L : ℝ, 1 ≤ K → 1 ≤ N → 1 ≤ B → 1 ≤ L →
      ∀ (rows marks columns cubes : Finset A) (a : A → ℂ) (beta : A → A → ℂ),
        (∀ k ∈ rows, PrimeArithmetic.Squarefree coords k ∧ normI k ≤ K) →
        (∀ p ∈ marks, PrimeArithmetic.Squarefree coords p ∧ normI p ≤ L) →
        (∀ n ∈ columns, PrimeArithmetic.Squarefree coords n ∧ normI n ≤ N) →
        (∀ b ∈ cubes, normI b ≤ B) →
        (∀ p ∈ marks, ‖a p‖ ≤ 1) →
        (∀ n ∈ columns, ∀ b ∈ cubes, ‖beta n b‖ ≤ 1) →
        hybridEnergy symbol (Coprime coords) normI a beta rows marks columns cubes ≤
          C0 * (K * N * B * L) ^ eps * (K + N * B) * B *
            (N + L + (N * L) ^ (2 / 3 : ℝ)) := by
  let eta := eps / 2
  have heta : 0 < eta := by dsimp only [eta]; positivity
  obtain ⟨Cmain, hCmain, hbound⟩ := hybrid_energy coords normI q hnatural hqpos
    Ccount hCcount hcount symbol hleft hright h6 hq hc eta heta
  obtain ⟨CH, hCH, hH⟩ := real_norm_reciprocal_sum_subpower q normI hnatural
    Ccount hCcount hqpos hcount eta heta
  refine ⟨Cmain * CH, mul_pos hCmain hCH, ?_⟩
  intro K N B L hK hN hB hL rows marks columns cubes a beta
    hrows hmarks hcolumns hcubes ha hbeta
  have hn : ∀ x, 1 ≤ normI x := one_le_real_norm_of_natural q normI hnatural hqpos
  obtain ⟨hM, hKM, hNM, hBM, hLM, hNBM, hKNBM, hNLM⟩ :=
    hybrid_total_scale_bounds K N B L hK hN hB hL
  let M := K * N * B * L
  let growth := (K + N * B) * B * (N + L + (N * L) ^ (2 / 3 : ℝ))
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hgrowth : 0 ≤ growth := by dsimp only [growth]; positivity
  have hmass : (∑ p ∈ marks, ‖a p‖ ^ 2 / normI p) ≤ CH * M ^ eta := by
    calc
      _ ≤ ∑ p ∈ marks, 1 / normI p := by
        apply Finset.sum_le_sum
        intro p hp
        have hsquare : ‖a p‖ ^ 2 ≤ 1 := by nlinarith [ha p hp, norm_nonneg (a p)]
        exact div_le_div_of_nonneg_right hsquare (le_trans zero_le_one (hn p))
      _ ≤ CH * L ^ eta := hH L hL marks (fun p hp => (hmarks p hp).2)
      _ ≤ CH * M ^ eta := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (le_trans zero_le_one hL) hLM (le_of_lt heta)) (le_of_lt hCH)
  have hpower : M ^ eta * M ^ eta = M ^ eps := by
    rw [← Real.rpow_add hMpos]
    congr 1
    dsimp only [eta]
    ring
  have hb := hbound K N B L hK hN hB hL rows marks columns cubes a beta
    hrows hmarks hcolumns hcubes hbeta
  calc
    _ ≤ Cmain * M ^ eta * growth * (∑ p ∈ marks, ‖a p‖ ^ 2 / normI p) := by
      simpa only [M, growth, mul_assoc] using hb
    _ ≤ Cmain * M ^ eta * growth * (CH * M ^ eta) :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = (Cmain * CH) * (M ^ eta * M ^ eta) * growth := by ring
    _ = (Cmain * CH) * M ^ eps * growth := by rw [hpower]
    _ = _ := by dsimp only [M, growth]; ring

#print axioms hybrid_energy_with_beta_mass
#print axioms hybrid_energy_bounded

end
end HeckeSkeleton.LowHybrid
