import ExpansionDetector.FixedTypeGammaReflection
import HeckeSkeleton.HeckeGammaReciprocal

/-! Project adapter for the newly proved dynamic reflected Gamma bound.
Unlike the existing finite-order numerator lemma, this applies to arbitrary
fixed infinity type. Project vendor dependencies remain external. -/
noncomputable section
namespace ExpansionDetector.Hecke
open NumberField IsDedekindDomain
open HeckeGeneral.Characters HeckeGeneral.Bridge HeckeGeneral.Analysis
open HeckeSkeleton.ExplicitHeckeFunctionalEquation HeckeSkeleton.HeckeGammaReciprocal
open scoped Classical BigOperators
variable (K : Type) [Field K] [NumberField K]

theorem fixedType_gamma_multiplier_dynamic_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (τ : InfinitePlace K → ℝ) (m : InfinitePlace K → ℤ) :
    ∃ G : ℝ, 0 < G ∧ ∀ s : ℂ,
      -(1 / 4 : ℝ) ≤ s.re ∧ s.re ≤ 1 / 2 →
      ‖heckeGammaProfile K (-τ) (-m) (1 - s) *
        (heckeGammaProfile K τ m s)⁻¹‖ ≤
          G * (2 + |s.im|) ^ (2 * Fintype.card (InfinitePlace K)) := by
  have hlocal : ∀ v : InfinitePlace K, ∃ G : ℝ, 0 < G ∧ ∀ s : ℂ,
      -(1 / 4 : ℝ) ≤ s.re ∧ s.re ≤ 1 / 2 →
      ‖Complex.Gammaℂ (1 - s - (τ v : ℂ) * Complex.I + ((m v).natAbs : ℂ) / 2) *
        (Complex.Gammaℂ (s + (τ v : ℂ) * Complex.I + ((m v).natAbs : ℂ) / 2))⁻¹‖ ≤
          G * (2 + |s.im|) ^ 2 := by
    intro v
    simpa only [Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_ofNat] using
      ExpansionDetector.Analytic.gammaC_fixedType_reflected_dynamic_bound
        ((m v).natAbs / 2 : ℝ) (τ v) (by positivity)
  choose G hGpos hG using hlocal
  refine ⟨∏ v, G v, Finset.prod_pos (fun v _ => hGpos v), ?_⟩
  intro s hs
  rw [heckeGammaProfile_dual, heckeGammaProfile, ← Finset.prod_inv_distrib,
    ← Finset.prod_mul_distrib, norm_prod]
  calc
    _ ≤ ∏ v : InfinitePlace K, G v * (2 + |s.im|) ^ 2 := by
      apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      intro v _
      simpa only [if_neg (v.not_isReal_iff_isComplex.mpr (hcomplex v))] using hG v s hs
    _ = (∏ v, G v) * (2 + |s.im|) ^ (2 * Fintype.card (InfinitePlace K)) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← pow_mul]

/-- The actual ordinary Hecke continuation is reflected with the sharp
conductor exponent 1/2-Re(s), and a fixed polynomial height cost.
No finite-order hypothesis on the character or background is used. -/
theorem exists_fixedType_reflected_ordinary_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (τ : InfinitePlace K → ℝ) (m : InfinitePlace K → ℤ) :
    ∃ G : ℝ, 0 < G ∧ ∀ χ : HeckeCharacter K,
      (∀ t : ℝ, χ ≠ heckeNormTwist K t) →
      (fun v => heckeRadialParameter K v χ) = τ → heckeArchWeight K χ = m →
      ∀ s : ℂ, -(1 / 4 : ℝ) ≤ s.re ∧ s.re ≤ 1 / 2 →
        ‖heckeContinuation K χ s‖ ≤
          G * heckeConductorScale K χ ^ (1 / 2 - s.re) *
            (2 + |s.im|) ^ (2 * Fintype.card (InfinitePlace K)) *
              ‖heckeContinuation K χ⁻¹ (1 - s)‖ := by
  obtain ⟨G, hGpos, hG⟩ := fixedType_gamma_multiplier_dynamic_bound K hcomplex τ m
  refine ⟨G, hGpos, ?_⟩
  intro χ hχ hτ hm s hs
  obtain ⟨ε, hε, hQ, hFE⟩ := exists_uncompleted_functionalEquation_left_of_one K χ hχ
  have hcan : canonicalHeckeGammaProfile K χ s = heckeGammaProfile K τ m s := by
    simp only [canonicalHeckeGammaProfile, hτ, hm]
  have hcanD : canonicalHeckeGammaProfile K χ⁻¹ (1 - s) =
      heckeGammaProfile K (-τ) (-m) (1 - s) := by
    rw [canonicalHeckeGammaProfile_inv, hτ, hm]
  have hGb : ‖(canonicalHeckeGammaProfile K χ s)⁻¹ *
      canonicalHeckeGammaProfile K χ⁻¹ (1 - s)‖ ≤
        G * (2 + |s.im|) ^ (2 * Fintype.card (InfinitePlace K)) := by
    rw [hcan, hcanD, mul_comm]
    exact hG s hs
  have hre : (s - 1 / 2).re = -(1 / 2 - s.re) := by simp
  have hnorm : ‖heckeContinuation K χ s‖ =
      (‖(canonicalHeckeGammaProfile K χ s)⁻¹ * canonicalHeckeGammaProfile K χ⁻¹ (1 - s)‖ *
        ‖heckeContinuation K χ⁻¹ (1 - s)‖) * heckeConductorScale K χ ^ (1 / 2 - s.re) := by
    rw [hFE s (by linarith [hs.2]), norm_div, norm_mul, norm_mul ε, hε, one_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos hQ, hre, Real.rpow_neg hQ.le, div_inv_eq_mul]
  rw [hnorm]
  calc
    _ ≤ ((G * (2 + |s.im|) ^ (2 * Fintype.card (InfinitePlace K))) *
        ‖heckeContinuation K χ⁻¹ (1 - s)‖) * heckeConductorScale K χ ^ (1 / 2 - s.re) := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hQ.le _)
      exact mul_le_mul_of_nonneg_right hGb (norm_nonneg _)
    _ = _ := by ring

end ExpansionDetector.Hecke
