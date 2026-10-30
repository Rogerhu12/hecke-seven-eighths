import HeckeSkeleton.SmallRadius.FiniteUnitShellFourier
import HeckeSkeleton.SmallRadius.FiniteMultiplicativeHaarDensity
import FLTReuse.M1c722af550c2b699
import FLTReuse.Mad950c02a4314b2a
import Mathlib.MeasureTheory.Group.Integral

/-!
Ported from the old repository cache candidate of 2026-10-12; compiled in this project.
Compute the actual normalized unit-shell Fourier Mellin factor at real 1/6.
The public unramified local zeta formula supplies the positive integral of
the integer ball for every positive real exponent. Nonzero integral then
implies genuine Bochner integrability; neither is supplied as a premise.
Multiplicative Haar translations give every valuation ball and the adjacent
ball scaling. The actual different and both Haar comparison constants remain.
No private FLT ball formula or Fourier functional equation is used.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeGeneral.ThetaSkeleton.Physical.FiniteUnitShellFourierMellinDraft

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open NumberField.AdelicLevel NumberField.StandardAddChar NumberField.AdelicFourier
open LanglandsTunnell.TateLocal MeasureTheory MeasureTheory.Measure Set
open HeckeGeneral.Characters HeckeGeneral.Arithmetic
open HeckeGeneral.Analysis.SLocalRadialHaarDraft.FiniteHaarDensityDraft
open HeckeGeneral.ThetaSkeleton.Physical.FiniteUnitShellTestDraft
open HeckeGeneral.ThetaSkeleton.Physical.FiniteUnitShellFourierDraft
open scoped Classical NNReal ENNReal

variable (K : Type) [Field K] [NumberField K]
variable (v : HeightOneSpectrum (𝓞 K))

-- The public local-zeta provider fixes this actual Borel structure.
attribute [local instance] localBorel borelSpace_localBorel

variable [MeasurableSpace (v.adicCompletion K)ˣ] [BorelSpace (v.adicCompletion K)ˣ]

theorem residueNorm_gt_one : (1 : ℝ) < (v.asIdeal.absNorm : ℝ) := by
  have hzero : v.asIdeal.absNorm ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot
  have hone : v.asIdeal.absNorm ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact v.isPrime.ne_top
  have hn : 1 < v.asIdeal.absNorm := by omega
  exact_mod_cast hn

private instance selfDualHaar_isAddHaar : (selfDualHaarAt K v).IsAddHaarMeasure := by
  unfold selfDualHaarAt
  have hq : (0 : ℝ≥0) < (v.asIdeal.absNorm : ℝ≥0) := by
    exact_mod_cast (lt_trans zero_lt_one (residueNorm_gt_one K v))
  exact Measure.IsAddHaarMeasure.nnreal_smul _ (NNReal.rpow_pos hq).ne'

theorem selfDual_unitSphere_mass_pos :
    0 < (selfDualHaarAt K v).real {x : v.adicCompletion K | Valued.v x = 1} := by
  rw [selfDualHaarAt_real_units_eq K v]
  exact mul_pos (sub_pos.mpr (inv_lt_one_of_one_lt₀ (residueNorm_gt_one K v)))
    (Real.rpow_pos_of_pos (lt_trans zero_lt_one (residueNorm_gt_one K v)) _)

/-- Actual positive integer-ball integral constant, including the Haar scalar. -/
def zeroBallMellinScalar (σ : ℝ) : ℝ :=
  (finiteHaarDensityScalar K v (selfDualHaarAt K v) : ℝ) *
    (selfDualHaarAt K v).real {x : v.adicCompletion K | Valued.v x = 1} *
      (1 - (v.asIdeal.absNorm : ℝ) ^ (-σ))⁻¹

theorem zeroBallMellinScalar_pos {σ : ℝ} (hσ : 0 < σ) :
    0 < zeroBallMellinScalar K v σ := by
  unfold zeroBallMellinScalar
  apply mul_pos
  · exact mul_pos (by exact_mod_cast finiteHaarDensityScalar_pos K v (selfDualHaarAt K v))
      (selfDual_unitSphere_mass_pos K v)
  · exact inv_pos.mpr (sub_pos.mpr
      (Real.rpow_lt_one_of_one_lt_of_neg (residueNorm_gt_one K v) (by linarith)))

/-- Literal valuation-ball norm weight on actual nonzero local elements. -/
def weightedValuationBall (k : ℤ) (σ : ℝ) (u : (v.adicCompletion K)ˣ) : ℂ :=
  if Valued.v (u : v.adicCompletion K) ≤ WithZero.exp k then
    (‖(u : v.adicCompletion K)‖ : ℂ) ^ (σ : ℂ)
  else 0

private theorem density_integral_zeroBall (σ : ℝ) :
    (∫ u : (v.adicCompletion K)ˣ, weightedValuationBall K v 0 σ u
      ∂finiteDensityHaar K v (selfDualHaarAt K v)) =
      localZeta (selfDualHaarAt K v)
        ((v.adicCompletionIntegers K : Set (v.adicCompletion K)).indicator
          (fun _ => (1 : ℂ))) 1 (σ : ℂ) := by
  let f : v.adicCompletion K → ℂ := fun x =>
    (v.adicCompletionIntegers K : Set (v.adicCompletion K)).indicator
      (fun _ => (1 : ℂ)) x * charExt (1 : (v.adicCompletion K)ˣ →* ℂˣ) x *
        (‖x‖ : ℂ) ^ (σ : ℂ)
  calc
    _ = ∫ u : (v.adicCompletion K)ˣ, f (u : v.adicCompletion K)
        ∂finiteDensityHaar K v (selfDualHaarAt K v) := by
      apply integral_congr_ae
      filter_upwards [] with u
      dsimp only [f]
      simp only [weightedValuationBall, WithZero.exp_zero, charExt_coe_units,
        MonoidHom.one_apply, Units.val_one, mul_one, Set.indicator,
        SetLike.mem_coe, mem_adicCompletionIntegers]
      by_cases hu : Valued.v (u : v.adicCompletion K) ≤ 1 <;> simp [hu]
    _ = ∫ x, f x ∂mulMeasure (selfDualHaarAt K v) :=
      integral_finiteDensityHaar K v (selfDualHaarAt K v) f
    _ = _ := by
      simp only [localZeta, finite_modulus_eq_nnnorm K v, coe_nnnorm, f]

/-- The public unramified zeta theorem proves the actual integer-ball value. -/
theorem integral_weightedValuationBall_zero {σ : ℝ} (hσ : 0 < σ) :
    (∫ u : (v.adicCompletion K)ˣ, weightedValuationBall K v 0 σ u
      ∂(Measure.haar : Measure (v.adicCompletion K)ˣ)) =
      (zeroBallMellinScalar K v σ : ℂ) := by
  have hconv : ‖((1 : (v.adicCompletion K)ˣ →* ℂˣ)
      (uniformizerUnit K v) : ℂ)‖ * (v.asIdeal.absNorm : ℝ) ^ (-(σ : ℂ).re) < 1 := by
    simpa only [MonoidHom.one_apply, Units.val_one, norm_one, one_mul,
      Complex.ofReal_re] using
      Real.rpow_lt_one_of_one_lt_of_neg (residueNorm_gt_one K v) (by linarith : -σ < 0)
  have hz := localZeta_stdTestFunAt_eq_of_unramified K v 1 (σ : ℂ)
    (hasConductorExponentAt_one_zero K v) hconv
  rw [stdTestFunAt, if_pos (hasConductorExponentAt_one_zero K v), localLFactorAt_one] at hz
  rw [finiteHaar_eq_smul_density K v (selfDualHaarAt K v), integral_smul_nnreal_measure,
    NNReal.smul_def, Complex.real_smul, density_integral_zeroBall K v σ, hz]
  have hpow : (v.asIdeal.absNorm : ℂ) ^ (-(σ : ℂ)) =
      (((v.asIdeal.absNorm : ℝ) ^ (-σ) : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_neg, Complex.ofReal_natCast] using
      (Complex.ofReal_cpow
        (by positivity : (0 : ℝ) ≤ (v.asIdeal.absNorm : ℝ)) (-σ)).symm
  rw [hpow]
  simp only [zeroBallMellinScalar, Complex.ofReal_mul, Complex.ofReal_inv,
    Complex.ofReal_sub, Complex.ofReal_one]
  ring

private theorem valued_uniformizer_zpow (k : ℤ) :
    Valued.v ((uniformizerUnit K v ^ k : (v.adicCompletion K)ˣ) : v.adicCompletion K) =
      WithZero.exp (-k) := by
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, valued_uniformizerUnit,
    ← WithZero.exp_zsmul]
  congr 1
  simp

private theorem weightedValuationBall_translate (k l : ℤ) (σ : ℝ)
    (c : (v.adicCompletion K)ˣ)
    (hc : Valued.v (c : v.adicCompletion K) = WithZero.exp l)
    (u : (v.adicCompletion K)ˣ) :
    weightedValuationBall K v (k + l) σ (c * u) =
      (‖(c : v.adicCompletion K)‖ : ℂ) ^ (σ : ℂ) *
        weightedValuationBall K v k σ u := by
  have hiff : Valued.v ((c * u : (v.adicCompletion K)ˣ) : v.adicCompletion K) ≤
      WithZero.exp (k + l) ↔
      Valued.v (u : v.adicCompletion K) ≤ WithZero.exp k := by
    rw [Units.val_mul, map_mul, hc]
    have he : WithZero.exp (k + l) = WithZero.exp l * WithZero.exp k := by
      rw [← WithZero.exp_add]
      congr 1
      omega
    rw [he]
    exact mul_le_mul_iff_right₀ (WithZero.exp_pos (a := l))
  by_cases hu : Valued.v (u : v.adicCompletion K) ≤ WithZero.exp k
  · have hcu := hiff.mpr hu
    simp only [weightedValuationBall, if_pos hu, if_pos hcu]
    rw [Units.val_mul, norm_mul, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (norm_nonneg _) (norm_nonneg _)]
  · have hcu : ¬Valued.v ((c * u : (v.adicCompletion K)ˣ) : v.adicCompletion K) ≤
        WithZero.exp (k + l) := fun h => hu (hiff.mp h)
    simp only [weightedValuationBall, if_neg hu, if_neg hcu, mul_zero]

/-- Every genuine valuation ball has a positive real integral. -/
def ballMellinScalar (k : ℤ) (σ : ℝ) : ℝ :=
  ‖((uniformizerUnit K v ^ (-k) : (v.adicCompletion K)ˣ) : v.adicCompletion K)‖ ^ σ *
    zeroBallMellinScalar K v σ

theorem ballMellinScalar_pos (k : ℤ) {σ : ℝ} (hσ : 0 < σ) :
    0 < ballMellinScalar K v k σ := by
  unfold ballMellinScalar
  apply mul_pos
  · exact Real.rpow_pos_of_pos
      (norm_pos_iff.mpr (uniformizerUnit K v ^ (-k)).ne_zero) _
  · exact zeroBallMellinScalar_pos K v hσ

theorem integral_weightedValuationBall (k : ℤ) {σ : ℝ} (hσ : 0 < σ) :
    (∫ u : (v.adicCompletion K)ˣ, weightedValuationBall K v k σ u
      ∂(Measure.haar : Measure (v.adicCompletion K)ˣ)) =
      (ballMellinScalar K v k σ : ℂ) := by
  let c : (v.adicCompletion K)ˣ := uniformizerUnit K v ^ (-k)
  have hc : Valued.v (c : v.adicCompletion K) = WithZero.exp k := by
    simpa only [c, neg_neg] using valued_uniformizer_zpow K v (-k)
  calc
    _ = ∫ u : (v.adicCompletion K)ˣ,
        weightedValuationBall K v k σ (c * u)
          ∂(Measure.haar : Measure (v.adicCompletion K)ˣ) :=
      (integral_mul_left_eq_self (weightedValuationBall K v k σ) c).symm
    _ = (‖(c : v.adicCompletion K)‖ : ℂ) ^ (σ : ℂ) *
        ∫ u : (v.adicCompletion K)ˣ, weightedValuationBall K v 0 σ u
          ∂(Measure.haar : Measure (v.adicCompletion K)ˣ) := by
      have ht : ∀ u : (v.adicCompletion K)ˣ,
          weightedValuationBall K v k σ (c * u) =
            (‖(c : v.adicCompletion K)‖ : ℂ) ^ (σ : ℂ) *
              weightedValuationBall K v 0 σ u := by
        intro u
        simpa only [zero_add] using weightedValuationBall_translate K v 0 k σ c hc u
      simp_rw [ht]
      exact integral_const_mul _ _
    _ = _ := by
      rewrite [integral_weightedValuationBall_zero K v hσ,
        ← Complex.ofReal_cpow (norm_nonneg _)]
      simp only [ballMellinScalar, c, Complex.ofReal_mul]

/-- Integrability is deduced from the proved positive value, not assumed. -/
theorem weightedValuationBall_integrable (k : ℤ) {σ : ℝ} (hσ : 0 < σ) :
    Integrable (weightedValuationBall K v k σ)
      (Measure.haar : Measure (v.adicCompletion K)ˣ) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_weightedValuationBall K v k hσ, Complex.ofReal_ne_zero]
  exact (ballMellinScalar_pos K v k hσ).ne'

private theorem norm_uniformizer :
    ‖(uniformizerUnit K v : v.adicCompletion K)‖ = (v.asIdeal.absNorm : ℝ)⁻¹ := by
  rw [NumberField.FinitePlace.norm_def, valued_uniformizerUnit,
    WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero, WithZero.log_exp]
  simp only [zpow_neg, zpow_one, NNReal.coe_inv, NNReal.coe_natCast]

theorem integral_weightedValuationBall_succ (k : ℤ) (σ : ℝ) :
    (∫ u : (v.adicCompletion K)ˣ, weightedValuationBall K v (k + 1) σ u
      ∂(Measure.haar : Measure (v.adicCompletion K)ˣ)) =
      (((v.asIdeal.absNorm : ℝ) ^ σ : ℝ) : ℂ) *
        ∫ u : (v.adicCompletion K)ˣ, weightedValuationBall K v k σ u
          ∂(Measure.haar : Measure (v.adicCompletion K)ˣ) := by
  let c : (v.adicCompletion K)ˣ := (uniformizerUnit K v)⁻¹
  have hc : Valued.v (c : v.adicCompletion K) = WithZero.exp (1 : ℤ) := by
    simp only [c, Units.val_inv_eq_inv_val, map_inv₀, valued_uniformizerUnit,
      ← WithZero.exp_neg, neg_neg]
  calc
    _ = ∫ u : (v.adicCompletion K)ˣ,
        weightedValuationBall K v (k + 1) σ (c * u)
          ∂(Measure.haar : Measure (v.adicCompletion K)ˣ) :=
      (integral_mul_left_eq_self (weightedValuationBall K v (k + 1) σ) c).symm
    _ = (‖(c : v.adicCompletion K)‖ : ℂ) ^ (σ : ℂ) *
        ∫ u : (v.adicCompletion K)ˣ, weightedValuationBall K v k σ u
          ∂(Measure.haar : Measure (v.adicCompletion K)ˣ) := by
      simp_rw [weightedValuationBall_translate K v k 1 σ c hc]
      exact integral_const_mul _ _
    _ = _ := by
      simp only [c, Units.val_inv_eq_inv_val, norm_inv, norm_uniformizer K v, inv_inv]
      rw [Complex.ofReal_cpow (by positivity : (0 : ℝ) ≤ (v.asIdeal.absNorm : ℝ))]

variable (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]

def normalizedShellFourierWeight (σ : ℝ) (u : (v.adicCompletion K)ˣ) : ℂ :=
  (μ.real (v.adicCompletionIntegers K : Set (v.adicCompletion K)) : ℂ)⁻¹ *
    fourierIntegral (psiLocal K v) μ (localUnitShellTest K v) u.val *
      (‖u.val‖ : ℂ) ^ (σ : ℂ)

theorem normalizedShellFourierWeight_eq (σ : ℝ) (u : (v.adicCompletion K)ˣ) :
    normalizedShellFourierWeight K v μ σ u =
      weightedValuationBall K v (localDifferentExponent K v) σ u -
        (v.asIdeal.absNorm : ℂ)⁻¹ *
          weightedValuationBall K v (localDifferentExponent K v + 1) σ u := by
  rw [normalizedShellFourierWeight, normalizedFourier_localUnitShellTest K v μ]
  unfold weightedValuationBall
  split_ifs <;> ring

theorem normalizedShellFourierWeight_integrable {σ : ℝ} (hσ : 0 < σ) :
    Integrable (normalizedShellFourierWeight K v μ σ)
      (Measure.haar : Measure (v.adicCompletion K)ˣ) := by
  have h := (weightedValuationBall_integrable K v (localDifferentExponent K v) hσ).sub
    ((weightedValuationBall_integrable K v (localDifferentExponent K v + 1) hσ).const_mul
      (v.asIdeal.absNorm : ℂ)⁻¹)
  exact h.congr (Filter.Eventually.of_forall fun u =>
    (normalizedShellFourierWeight_eq K v μ σ u).symm)

/-- The shell Fourier Mellin factor, with the actual different ball retained. -/
theorem integral_normalizedShellFourierWeight {σ : ℝ} (hσ : 0 < σ) :
    (∫ u : (v.adicCompletion K)ˣ, normalizedShellFourierWeight K v μ σ u
      ∂(Measure.haar : Measure (v.adicCompletion K)ˣ)) =
      (((1 - (v.asIdeal.absNorm : ℝ) ^ (σ - 1)) *
        ballMellinScalar K v (localDifferentExponent K v) σ : ℝ) : ℂ) := by
  simp_rw [normalizedShellFourierWeight_eq K v μ σ]
  rw [integral_sub
    (weightedValuationBall_integrable K v (localDifferentExponent K v) hσ)
    ((weightedValuationBall_integrable K v (localDifferentExponent K v + 1) hσ).const_mul _),
    integral_const_mul, integral_weightedValuationBall_succ,
    integral_weightedValuationBall K v (localDifferentExponent K v) hσ]
  rw [Real.rpow_sub_one (ne_of_gt (lt_trans zero_lt_one (residueNorm_gt_one K v))) σ]
  simp only [Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one,
    Complex.ofReal_div]
  push_cast
  ring

theorem normalizedShellFourier_mellin_oneSixth_eq :
    (∫ u : (v.adicCompletion K)ˣ, normalizedShellFourierWeight K v μ (1 / 6) u
      ∂(Measure.haar : Measure (v.adicCompletion K)ˣ)) =
      (((1 - (v.asIdeal.absNorm : ℝ) ^ (-5 / 6 : ℝ)) *
        ballMellinScalar K v (localDifferentExponent K v) (1 / 6) : ℝ) : ℂ) := by
  convert integral_normalizedShellFourierWeight K v μ (by norm_num : (0 : ℝ) < 1 / 6)
    using 1 <;> norm_num

theorem normalizedShellFourier_mellin_oneSixth_ne_zero :
    (∫ u : (v.adicCompletion K)ˣ, normalizedShellFourierWeight K v μ (1 / 6) u
      ∂(Measure.haar : Measure (v.adicCompletion K)ˣ)) ≠ 0 := by
  rw [integral_normalizedShellFourierWeight K v μ (by norm_num : (0 : ℝ) < 1 / 6),
    Complex.ofReal_ne_zero]
  apply ne_of_gt
  apply mul_pos
  · exact sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg
      (residueNorm_gt_one K v) (by norm_num : (1 / 6 : ℝ) - 1 < 0))
  · exact ballMellinScalar_pos K v (localDifferentExponent K v) (by norm_num)

/-- The literal physical local factor for any Borel structure on the completion.
The local-zeta provider's canonical Borel choice creates no additional input. -/
theorem normalizedShellFourier_oneSixth_actualBorel
    (m : MeasurableSpace (v.adicCompletion K))
    (hmBorel : @BorelSpace (v.adicCompletion K) _ m)
    (ν : @Measure (v.adicCompletion K) m)
    (hν : letI := m; ν.IsAddHaarMeasure) :
    letI := m
    letI := hmBorel
    letI := hν
    Integrable
      (fun u : (v.adicCompletion K)ˣ =>
        (ν.real (v.adicCompletionIntegers K : Set (v.adicCompletion K)) : ℂ)⁻¹ *
          fourierIntegral (psiLocal K v) ν (localUnitShellTest K v) u.val *
            (‖u.val‖ : ℂ) ^ ((1 / 6 : ℝ) : ℂ))
      (Measure.haar : Measure (v.adicCompletion K)ˣ) ∧
      (∫ u : (v.adicCompletion K)ˣ,
        (ν.real (v.adicCompletionIntegers K : Set (v.adicCompletion K)) : ℂ)⁻¹ *
          fourierIntegral (psiLocal K v) ν (localUnitShellTest K v) u.val *
            (‖u.val‖ : ℂ) ^ ((1 / 6 : ℝ) : ℂ)
          ∂(Measure.haar : Measure (v.adicCompletion K)ˣ)) ≠ 0 := by
  have hm : m = localBorel K v := hmBorel.measurable_eq
  subst m
  letI : ν.IsAddHaarMeasure := hν
  exact ⟨normalizedShellFourierWeight_integrable K v ν (by norm_num : (0 : ℝ) < 1 / 6),
    normalizedShellFourier_mellin_oneSixth_ne_zero K v ν⟩

end HeckeGeneral.ThetaSkeleton.Physical.FiniteUnitShellFourierMellinDraft
