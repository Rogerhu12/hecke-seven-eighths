import HeckeSkeleton.ExpansionModels.SmallRowMellin

/-!
# Actual Mellin factors on every fixed positive line

The absolute large-row contour uses a fixed real Mellin parameter above
one.  Its Fourier transform is the same genuine Schwartz tensor as in the
small-row estimate.  Extra Schwartz decay controls the larger positive
moment; the actual multiplicative Haar and radial comparison scalar are
retained.  Thus the literal Mellin integral is integrable before its norm
bound is used, including near every coordinate hyperplane.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Expansion.LargeRows

open NumberField NumberField.InfinitePlace IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Bridge
open HeckeGeneral.ThetaSkeleton
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.Analysis.SLocalRadialHaarDraft
open HeckeGeneral.Analysis.ActualSLocalPositiveMomentDraft
open HeckeGeneral.Analysis.MixedPositiveHaarDraft
open HeckeGeneral.Analysis.SmallPositiveFiniteMomentDraft
open HeckeGeneral.Analysis.SLocalRadialHaarDraft.TotallyComplexHaarDraft
open HeckeSkeleton.Expansion.SmallRows
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]

local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "W" => mixedEmbedding.mixedSpace K

/-- Arbitrary Schwartz decay, with no factorization requirement on the test. -/
private theorem norm_le_complex_product_decay
    (M : ℕ) (phi : SchwartzMap W ℂ) (y : W) :
    ‖phi y‖ ≤
      (2 ^ (M * Fintype.card (ComplexPlace K)) *
        (Finset.Iic (M * Fintype.card (ComplexPlace K), 0)).sup
          (fun m => SchwartzMap.seminorm ℝ m.1 m.2) phi) *
        ∏ v : ComplexPlace K, (1 + ‖y.2 v‖) ^ (-(M : ℝ)) := by
  let d := M * Fintype.card (ComplexPlace K)
  let D : ℝ := ∏ v : ComplexPlace K, (1 + ‖y.2 v‖) ^ M
  have hDpos : 0 < D := by dsimp only [D]; positivity
  have hD : D ≤ (1 + ‖y‖) ^ d := by
    calc
      _ ≤ ∏ _v : ComplexPlace K, (1 + ‖y‖) ^ M := by
        apply Finset.prod_le_prod₀ (fun _ _ => by positivity)
        intro v _
        exact pow_le_pow_left₀ (by positivity)
          (add_le_add (le_rfl : (1 : ℝ) ≤ 1)
            ((norm_le_pi_norm y.2 v).trans (norm_snd_le y))) M
      _ = _ := by rw [Finset.prod_const, Finset.card_univ, ← pow_mul]
  have hphi : ‖phi y‖ * D ≤
      2 ^ d * (Finset.Iic (d, 0)).sup
        (fun m => SchwartzMap.seminorm ℝ m.1 m.2) phi := by
    calc
      _ ≤ ‖phi y‖ * (1 + ‖y‖) ^ d := mul_le_mul_of_nonneg_left hD (norm_nonneg _)
      _ ≤ _ := by
        simpa only [norm_iteratedFDeriv_zero, mul_comm] using
          (SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
            (m := (d, 0)) (k := d) (n := 0) le_rfl le_rfl phi y)
  have hdecay : (∏ v : ComplexPlace K, (1 + ‖y.2 v‖) ^ (-(M : ℝ))) = D⁻¹ := by
    dsimp only [D]
    rw [← Finset.prod_inv_distrib]
    apply Finset.prod_congr rfl
    intro v _
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
  rw [hdecay, ← div_eq_mul_inv]
  exact (le_div_iff₀ hDpos).mpr hphi

/-- Additional Schwartz powers absorb any fixed increase in the Mellin
weight; the comparison envelope has its genuinely proved moment at one. -/
private theorem complex_large_moment_envelope_le
    {sigma : ℝ} (hsigma : 1 ≤ sigma) {M : ℕ}
    (hM : 2 * sigma + 1 ≤ (M : ℝ)) (r : ℝ) (hr : 0 < r) :
    (1 + r) ^ (-(M : ℝ)) * r ^ (2 * sigma) ≤
      (1 + r) ^ (-(3 : ℝ)) * r ^ (2 : ℕ) := by
  have hbase : 0 < 1 + r := by linarith
  have hexp : 0 ≤ 2 * sigma - 2 := by linarith
  have hrpow : r ^ (2 * sigma - 2) ≤ (1 + r) ^ (2 * sigma - 2) :=
    Real.rpow_le_rpow hr.le (by linarith) hexp
  have hrest : (1 + r) ^ (-(M : ℝ) + (2 * sigma - 2)) ≤
      (1 + r) ^ (-(3 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  calc
    _ = (1 + r) ^ (-(M : ℝ)) * r ^ (2 * sigma - 2) * r ^ (2 : ℕ) := by
      rw [← Real.rpow_two, mul_assoc, ← Real.rpow_add hr,
        show 2 * sigma - 2 + 2 = 2 * sigma by ring]
    _ ≤ (1 + r) ^ (-(M : ℝ)) * (1 + r) ^ (2 * sigma - 2) * r ^ (2 : ℕ) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hrpow (by positivity)) (sq_nonneg _)
    _ = (1 + r) ^ (-(M : ℝ) + (2 * sigma - 2)) * r ^ (2 : ℕ) := by
      rw [Real.rpow_add hbase]
    _ ≤ _ := mul_le_mul_of_nonneg_right hrest (sq_nonneg _)

local instance : MeasurableSpace Wˣ := borel _
local instance : BorelSpace Wˣ := ⟨rfl⟩

local instance : SecondCountableTopology (mixedEmbedding.mixedSpace K)ˣ := by
  letI : SecondCountableTopology (mixedEmbedding.mixedSpace K)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

/-- Integrability for an arbitrary actual archimedean Schwartz test on
every real line at least one.  The norm weight is the original mixed norm. -/
theorem integrable_mixed_large_positive_moment [IsTotallyComplex K]
    (phi : SchwartzMap V ℂ) {sigma : ℝ} (hsigma : 1 ≤ sigma) :
    Integrable (weightedArchAbsolute K phi sigma) (mixedMultiplicativeHaar K) := by
  obtain ⟨M, hM⟩ := exists_nat_ge (2 * sigma + 1)
  -- Keep the coordinate transport opaque during seminorm elaboration.
  -- Its pointwise equality retains the original Schwartz test exactly.
  obtain ⟨Phi, hPhi⟩ : ∃ Phi : SchwartzMap W ℂ,
      ∀ y : W, Phi y = phi ((traceToMixed K).symm y) :=
    ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (traceToMixed K).symm phi,
      fun _ => rfl⟩
  let d := M * Fintype.card (ComplexPlace K)
  let B : ℝ := 2 ^ d * (Finset.Iic (d, 0)).sup
    (fun m => SchwartzMap.seminorm ℝ m.1 m.2) Phi
  have hB : 0 ≤ B :=
    mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) d)
      (apply_nonneg ((Finset.Iic (d, 0)).sup
        (fun m => SchwartzMap.seminorm ℝ m.1 m.2)) Phi)
  have hpoint (u : Wˣ) : weightedArchAbsolute K phi sigma u ≤ B * mixedHaarEnvelope K 1 u := by
    have hphi := norm_le_complex_product_decay K M Phi (u : W)
    rw [hPhi (u : W)] at hphi
    have hproduct :
        (∏ v : ComplexPlace K, (1 + ‖(u : W).2 v‖) ^ (-(M : ℝ))) *
          (mixedEmbedding.norm (u : W)) ^ sigma ≤ mixedHaarEnvelope K 1 u := by
      rw [mixedNorm_rpow_complexProduct K]
      simp only [mixedHaarEnvelope, complexUnitEnvelope, mixedComplexUnitsEquiv_apply]
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_le_prod₀ (fun _ _ => by positivity)
      intro v _
      have hr : 0 < ‖(mixedComplexUnitsEquiv K u v : ℂ)‖ :=
        norm_pos_iff.mpr (Units.ne_zero _)
      simpa only [mixedComplexUnitsEquiv_apply, mul_one, Real.rpow_two] using
        complex_large_moment_envelope_le hsigma hM _ hr
    calc
      _ ≤ (B * ∏ v : ComplexPlace K, (1 + ‖(u : W).2 v‖) ^ (-(M : ℝ))) *
          (mixedEmbedding.norm (u : W)) ^ sigma :=
        mul_le_mul_of_nonneg_right hphi (Real.rpow_nonneg (mixedEmbedding.norm_nonneg _) _)
      _ = B * ((∏ v : ComplexPlace K, (1 + ‖(u : W).2 v‖) ^ (-(M : ℝ))) *
          (mixedEmbedding.norm (u : W)) ^ sigma) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hproduct hB
  have hmeas : AEStronglyMeasurable (weightedArchAbsolute K phi sigma)
      (mixedMultiplicativeHaar K) := by
    have hm : Measurable (fun u : Wˣ => mixedEmbedding.norm (u : W)) :=
      ((mixedEmbedding.continuous_norm K).comp Units.continuous_val).measurable
    exact (((phi.continuous.comp ((traceToMixed K).symm.continuous.comp
      Units.continuous_val)).norm.measurable).mul (hm.pow_const sigma)).aestronglyMeasurable
  apply ((integrable_mixedHaarEnvelope K 1 (by norm_num) le_rfl).const_mul B).mono' hmeas
  exact Filter.Eventually.of_forall fun u => by
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (mixedEmbedding.norm_nonneg _) _))]
    exact hpoint u

variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "G" => sLocalMultiplicativeGroup K Sset

local instance (p : Sset) : MeasurableSpace (p.val.adicCompletion K)ˣ := borel _
local instance (p : Sset) : BorelSpace (p.val.adicCompletion K)ˣ := ⟨rfl⟩

local instance (p : Sset) : SecondCountableTopology (p.val.adicCompletion K)ˣ :=
  Units.isEmbedding_val₀.secondCountableTopology

variable [∀ p : HeightOneSpectrum (𝓞 K), MeasurableSpace (p.adicCompletion K)]
variable [∀ p : HeightOneSpectrum (𝓞 K), BorelSpace (p.adicCompletion K)]
variable (mu : ∀ p : HeightOneSpectrum (𝓞 K), Measure (p.adicCompletion K))
variable [∀ p, (mu p).IsAddHaarMeasure]
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
variable [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
variable (nu : Measure (FiniteAdeleRing (𝓞 K) K)) [nu.IsAddHaarMeasure]
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
variable [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]

include nu in
/-- The literal additive Mellin integral is bounded on any fixed positive
line.  Its weighted Fourier integral is also proved integrable, rather than
using the zero value of a nonintegrable Bochner integral. -/
theorem exists_actual_additiveMellin_positive_line_bound [IsTotallyComplex K]
    (test : AdditiveProbeTest K Sset) {sigma : ℝ} (hsigma : 0 < sigma) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, z.re = sigma →
      Integrable
        (fun x : G => additiveFourier K Sset (fun p => mu p.val) test x *
          (sLocalProductNorm K Sset x : ℂ) ^ z)
        (sLocalRadialMeasure K Sset) ∧
      ‖additiveMellin K Sset (fun p => mu p.val) test z‖ ≤ C := by
  by_cases hsigma1 : sigma ≤ 1
  · exact exists_actual_additiveMellin_line_bound K S mu nu test hsigma hsigma1
  let phi : SchwartzMap V ℂ := traceSchwartzFourier K test.infiniteTest
  let psi := additiveFourierFiniteProfile K S mu test
  obtain ⟨hloc, hsupport⟩ :=
    additiveFourierFiniteProfile_locallyConstant_compactSupport K S mu nu test
  obtain ⟨Cf, hCf, hfin, hfinbound⟩ :=
    exists_finite_compactSupport_weightedL1_bound K Sset psi hloc.continuous hsupport sigma hsigma
  have harch := integrable_mixed_large_positive_moment K phi (le_of_not_ge hsigma1)
  have hprod : Integrable (weightedTensorAbsolute K Sset phi psi sigma)
      (sLocalProductMultiplicativeHaar K Sset) :=
    (harch.mul_prod hfin).congr (Filter.Eventually.of_forall fun x =>
      (weightedTensorAbsolute_eq_product K Sset phi psi sigma x).symm)
  have hint : Integrable (weightedTensorAbsolute K Sset phi psi sigma)
      (sLocalRadialMeasure K Sset) := by
    rw [radialMeasure_eq_positiveScalar_productHaar K Sset]
    exact hprod.smul_measure_nnreal
  let C : ℝ := (∫ x : G, weightedTensorAbsolute K Sset phi psi sigma x
    ∂sLocalRadialMeasure K Sset) + 1
  have hC : 0 < C := by
    have hi : 0 ≤ ∫ x : G, weightedTensorAbsolute K Sset phi psi sigma x
        ∂sLocalRadialMeasure K Sset :=
      MeasureTheory.integral_nonneg
        (weightedTensorAbsolute_nonneg K Sset phi psi sigma)
    dsimp only [C]
    linarith
  refine ⟨C, hC, ?_⟩
  intro z hz
  let F : G → ℂ := fun x => additiveFourier K Sset (fun p => mu p.val) test x *
    (sLocalProductNorm K Sset x : ℂ) ^ z
  have hnorm (x : G) : ‖F x‖ = weightedTensorAbsolute K Sset phi psi sigma x := by
    dsimp only [F]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (sLocalProductNorm_pos K Sset x), hz,
      additiveFourier_eq_actual_tensor K S mu test x]
    rfl
  have hcontinuous : Continuous F := by
    have hbase : Continuous (fun x : G => (sLocalProductNorm K Sset x : ℂ)) :=
      Complex.continuous_ofReal.comp (continuous_sLocalProductNorm K Sset)
    have hpow : Continuous (fun x : G => (sLocalProductNorm K Sset x : ℂ) ^ z) :=
      hbase.cpow continuous_const (fun x =>
        Complex.ofReal_mem_slitPlane.mpr (sLocalProductNorm_pos K Sset x))
    have hfourier : Continuous (fun x : G => additiveFourier K Sset (fun p => mu p.val) test x) := by
      simp_rw [additiveFourier_eq_actual_tensor K S mu test]
      exact continuous_sLocalTensorTestFunction K Sset phi psi hloc.continuous
    exact hfourier.mul hpow
  have hF : Integrable F (sLocalRadialMeasure K Sset) := by
    apply hint.mono' hcontinuous.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun x => (hnorm x).le
  refine ⟨hF, ?_⟩
  calc
    ‖additiveMellin K Sset (fun p => mu p.val) test z‖ =
        ‖∫ x : G, F x ∂sLocalRadialMeasure K Sset‖ := by
      rw [additiveMellin_eq_integral_radialMeasure K Sset (fun p => mu p.val) test z hF]
    _ ≤ ∫ x : G, ‖F x‖ ∂sLocalRadialMeasure K Sset := norm_integral_le_integral_norm _
    _ = ∫ x : G, weightedTensorAbsolute K Sset phi psi sigma x
        ∂sLocalRadialMeasure K Sset := by simp_rw [hnorm]
    _ ≤ C := le_add_of_nonneg_right zero_le_one

/-- Fixed annular denominator tests have a uniform bound on every real
Mellin line, including the absolute line at two. -/
theorem exists_actual_denominatorMellin_line_bound (test : DenominatorTest) (sigma : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℂ, w.re = sigma → ‖mellin test.toFun w‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := HighBinBoundary.ActualDenominator.exists_mellin_uniform_strip_bound
    test.toSmoothAnnularTest sigma sigma 0
  refine ⟨C, hC, ?_⟩
  intro w hw
  have heq : (sigma : ℂ) + (w.im : ℂ) * Complex.I = w := by
    apply Complex.ext <;> simp [hw]
  simpa only [pow_zero, one_mul, heq] using hb sigma w.im le_rfl le_rfl

end HeckeSkeleton.Expansion.LargeRows

#print axioms HeckeSkeleton.Expansion.LargeRows.integrable_mixed_large_positive_moment
#print axioms HeckeSkeleton.Expansion.LargeRows.exists_actual_additiveMellin_positive_line_bound
#print axioms HeckeSkeleton.Expansion.LargeRows.exists_actual_denominatorMellin_line_bound
