import HeckeSkeleton.SmallRadius.FiniteUnitShellIntegrals
/-!
Ported from the old repository cache candidate of 2026-10-12; compiled in this project.
The actual unit-shell test has Fourier transform equal to the difference
of two dual valuation balls. The different exponent and the additive Haar
mass are retained. After the physical division by mu(O), the remaining
coefficient is exactly the inverse residue-field cardinality.
This is a pointwise Fourier evaluation, not the weighted Mellin integral.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeGeneral.ThetaSkeleton.Physical.FiniteUnitShellFourierDraft

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum MeasureTheory
open NumberField.StandardAddChar NumberField.AdelicFourier
open HeckeGeneral.Characters HeckeGeneral.Arithmetic
open HeckeGeneral.ThetaSkeleton.Physical.FiniteUnitShellTestDraft
open HeckeGeneral.ThetaSkeleton.Physical.FiniteUnitShellIntegralsDraft
open scoped Classical

variable (K : Type) [Field K] [NumberField K]
variable (v : HeightOneSpectrum (𝓞 K))

theorem localUnitShellTest_eq_sub :
    localUnitShellTest K v =
      localIntegerResidueCosetIndicator K v 0 0 -
        localIntegerResidueCosetIndicator K v 1 0 := by
  have hzero : localIntegerResidueCosetIndicator K v 0 0 =
      (v.adicCompletionIntegers K : Set (v.adicCompletion K)).indicator (fun _ => (1 : ℂ)) := by
    funext x
    simp only [localIntegerResidueCosetIndicator, ZeroMemClass.coe_zero, sub_zero,
      Nat.cast_zero, neg_zero, WithZero.exp_zero, Set.indicator, Set.mem_setOf_eq,
      SetLike.mem_coe, mem_adicCompletionIntegers]
  have hone : localIntegerResidueCosetIndicator K v 1 0 =
      localResidueCosetIndicator K v 1 0 :=
    (localResidueCosetIndicator_eq_center K v 1 0 0 (map_zero _)).symm
  rw [hzero, hone]
  funext x
  by_cases hx : x ∈ localResidueCosetSet K v 1 0
  · have hO : x ∈ v.adicCompletionIntegers K := by
      apply localIntegerResidueCosetIndicator_nonzero_integral K v 1 0 x
      rw [hone]
      simp only [localResidueCosetIndicator, Set.indicator_of_mem hx, ne_eq, one_ne_zero,
        not_false_eq_true]
    simp [localUnitShellTest, localUnitShellSet, localResidueCosetIndicator, hx, hO]
  · simp [localUnitShellTest, localUnitShellSet, localResidueCosetIndicator, Set.indicator, hx]

variable [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
variable (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]

private theorem integrable_localBallFourierIntegrand (n : ℕ) (w : v.adicCompletion K) :
    Integrable (fun x : v.adicCompletion K =>
      psiLocal K v (-(x * w)) * localIntegerResidueCosetIndicator K v n 0 x) μ := by
  obtain ⟨hlc, hcs⟩ := localIntegerResidueCosetIndicator_locallyConstant_compactSupport K v n 0
  have hc : Continuous (fun x : v.adicCompletion K => psiLocal K v (-(x * w))) :=
    (continuous_psiLocal K v).comp (continuous_id.mul continuous_const).neg
  exact (hc.mul hlc.continuous).integrable_of_hasCompactSupport hcs.mul_left

/-- The literal negative-sign transform, including the actual different. -/
theorem fourierIntegral_localUnitShellTest (w : v.adicCompletion K) :
    fourierIntegral (psiLocal K v) μ (localUnitShellTest K v) w =
      (μ.real (v.adicCompletionIntegers K : Set (v.adicCompletion K)) : ℂ) *
        ((if Valued.v w ≤ WithZero.exp (localDifferentExponent K v) then (1 : ℂ) else 0) -
          (v.asIdeal.absNorm : ℂ)⁻¹ *
            (if Valued.v w ≤ WithZero.exp (localDifferentExponent K v + 1) then 1 else 0)) := by
  rw [localUnitShellTest_eq_sub]
  change (∫ x : v.adicCompletion K, psiLocal K v (-(x * w)) *
    (localIntegerResidueCosetIndicator K v 0 0 x -
      localIntegerResidueCosetIndicator K v 1 0 x) ∂μ) = _
  simp_rw [mul_sub]
  rw [integral_sub (integrable_localBallFourierIntegrand K v μ 0 w)
    (integrable_localBallFourierIntegrand K v μ 1 w)]
  change fourierIntegral (psiLocal K v) μ (localIntegerResidueCosetIndicator K v 0 0) w -
    fourierIntegral (psiLocal K v) μ (localIntegerResidueCosetIndicator K v 1 0) w = _
  rw [fourierIntegral_localIntegerResidueCosetIndicator_mass K v μ 0 0 w,
    fourierIntegral_localIntegerResidueCosetIndicator_mass K v μ 1 0 w]
  simp only [ZeroMemClass.coe_zero, zero_mul, neg_zero, AddChar.map_zero_eq_one, one_mul,
    Nat.cast_zero, zpow_zero, Nat.cast_one, zpow_neg_one, add_zero,
    Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast]
  ring

theorem localIntegerRing_measureReal_pos :
    0 < μ.real (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
  letI : CompactSpace (LocalIntegerRing K v) :=
    NumberField.AdelicHaar.compactSpace_adicCompletionIntegers (𝓞 K) K v
  have hcompact : IsCompact (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
    isCompact_iff_compactSpace.mpr inferInstance
  have hopen := (Valued.isClopen_valuationSubring (v.adicCompletion K)).isOpen
  exact ENNReal.toReal_pos (hopen.measure_ne_zero μ ⟨0, zero_mem _⟩)
    hcompact.measure_lt_top.ne

/-- Cancel precisely the physical additive Haar normalization. -/
theorem normalizedFourier_localUnitShellTest (w : v.adicCompletion K) :
    (μ.real (v.adicCompletionIntegers K : Set (v.adicCompletion K)) : ℂ)⁻¹ *
        fourierIntegral (psiLocal K v) μ (localUnitShellTest K v) w =
      (if Valued.v w ≤ WithZero.exp (localDifferentExponent K v) then (1 : ℂ) else 0) -
        (v.asIdeal.absNorm : ℂ)⁻¹ *
          (if Valued.v w ≤ WithZero.exp (localDifferentExponent K v + 1) then 1 else 0) := by
  have hm : (μ.real (v.adicCompletionIntegers K : Set (v.adicCompletion K)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (localIntegerRing_measureReal_pos K v μ))
  rw [fourierIntegral_localUnitShellTest, ← mul_assoc, inv_mul_cancel₀ hm, one_mul]

end HeckeGeneral.ThetaSkeleton.Physical.FiniteUnitShellFourierDraft
