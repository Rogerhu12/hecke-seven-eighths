import HeckeSkeleton.Moments.MOM_INV_STEP.FirstParentRetained
import HeckeSkeleton.Moments.MOM_INV_STEP.SharpCommonKernelBounds

/-!
# One Fourier envelope independent of the first dual row

The first normalized radius is N(z)/(r N(d) N(R₁) X Y), which may
be below one. The proved all-radius small-power estimate and N(z) ≥ 1
remove z from the envelope. Extra fixed Fourier decay is kept to pay for
the seminorm growth of the later combined Mellin frequency.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.FirstCommonEnvelope

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.Analysis HeckeGeneral.Bridge HeckeGeneral.ThetaSkeleton
  HeckeGeneral.ThetaSkeleton.Global MeasureTheory
open CommonKernel CanonicalFirstEnergy FirstPoissonNormalization
open scoped Classical BigOperators nonZeroDivisors

def frequencyEnvelope (m : ℕ) (ξ : LogPlane) : ℝ :=
  fourierEnvelope ξ / (1 + ‖ξ‖) ^ m

theorem frequencyEnvelope_nonneg (m : ℕ) (ξ : LogPlane) :
    0 ≤ frequencyEnvelope m ξ :=
  div_nonneg (fourierEnvelope_nonneg ξ) (pow_nonneg (by positivity) m)

theorem frequencyEnvelope_continuous (m : ℕ) : Continuous (frequencyEnvelope m) := by
  have hc : Continuous fourierEnvelope := by
    unfold fourierEnvelope
    exact (continuous_const.add continuous_norm).rpow_const
      (fun ξ => Or.inl (by positivity : (1 + ‖ξ‖ : ℝ) ≠ 0))
  exact hc.div ((continuous_const.add continuous_norm).pow m)
    (fun ξ => (pow_pos (by positivity : (0 : ℝ) < 1 + ‖ξ‖) m).ne')

theorem frequencyEnvelope_le (m : ℕ) (ξ : LogPlane) :
    frequencyEnvelope m ξ ≤ fourierEnvelope ξ := by
  have hp : 1 ≤ (1 + ‖ξ‖) ^ m := by
    simpa only [one_pow] using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1)
      (by positivity : (1 : ℝ) ≤ 1 + ‖ξ‖) m
  unfold frequencyEnvelope
  apply (div_le_iff₀ (pow_pos (by positivity : (0 : ℝ) < 1 + ‖ξ‖) m)).mpr
  exact le_mul_of_one_le_right (fourierEnvelope_nonneg ξ) hp

theorem frequencyEnvelope_integrable (m : ℕ) : Integrable (frequencyEnvelope m) := by
  apply fourierEnvelope_integrable.mono_nonneg
    (frequencyEnvelope_continuous m).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (frequencyEnvelope_nonneg m)
  · exact Filter.Eventually.of_forall (frequencyEnvelope_le m)

theorem frequencyEnvelope_moment (m : ℕ) (ξ : LogPlane) :
    (1 + ‖ξ‖) ^ m * frequencyEnvelope m ξ = fourierEnvelope ξ := by
  unfold frequencyEnvelope
  field_simp [(pow_pos (by positivity : (0 : ℝ) < 1 + ‖ξ‖) m).ne']

theorem frequencyEnvelope_moment_integrable (m : ℕ) :
    Integrable (fun ξ : LogPlane => (1 + ‖ξ‖) ^ m * frequencyEnvelope m ξ) := by
  simpa only [frequencyEnvelope_moment] using fourierEnvelope_integrable

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))

local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer Sset K
local notation "Ext" => ExteriorIdeal K Sset
local notation "V" => mixedEmbedding.euclidean.mixedSpace K

def radialScale (r : {r : ℝ // 0 < r}) (d : NonzeroRingElements OS)
    (r₁ r₂ b₁ b₂ : Ext) (X Y : {r : ℝ // 0 < r}) : ℝ :=
  r.val * (sIntegerElementNorm K Sset d).val * cubeNorm K S D r₁ r₂ b₁ b₂ * X.val * Y.val

theorem radialScale_pos (r : {r : ℝ // 0 < r}) (d : NonzeroRingElements OS)
    (r₁ r₂ b₁ b₂ : Ext) (X Y : {r : ℝ // 0 < r}) :
    0 < radialScale K S D r d r₁ r₂ b₁ b₂ X Y :=
  mul_pos (mul_pos (mul_pos (mul_pos r.property (sIntegerElementNorm K Sset d).property)
    (cubeNorm_pos K S D r₁ r₂ b₁ b₂)) X.property) Y.property

theorem outerRadius_power_le (ε : ℝ) (hε : 0 ≤ ε)
    (r : {r : ℝ // 0 < r}) (d : NonzeroRingElements OS)
    (r₁ r₂ b₁ b₂ z : Ext) (X Y : {r : ℝ // 0 < r}) :
    (outerRadius K S D r d r₁ r₂ b₁ b₂ z X Y).val ^ (-ε) ≤
      radialScale K S D r d r₁ r₂ b₁ b₂ X Y ^ ε := by
  have hz : (1 : ℝ) ≤ (z.val.val.absNorm : ℝ) := by
    have hzN : 1 ≤ z.val.val.absNorm := Ideal.absNorm_pos_of_nonZeroDivisors z.val
    exact_mod_cast hzN
  have hp := radialScale_pos K S D r d r₁ r₂ b₁ b₂ X Y
  have hpow : (z.val.val.absNorm : ℝ) ^ (-ε) ≤ 1 := by
    simpa only [Real.one_rpow] using
      Real.rpow_le_rpow_of_nonpos zero_lt_one hz (neg_nonpos.mpr hε)
  change ((z.val.val.absNorm : ℝ) / radialScale K S D r d r₁ r₂ b₁ b₂ X Y) ^ (-ε) ≤ _
  rw [Real.div_rpow (by positivity : (0 : ℝ) ≤ (z.val.val.absNorm : ℝ)) hp.le,
    Real.rpow_neg hp.le, div_inv_eq_mul]
  exact (mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hp.le ε)).trans_eq (one_mul _)

variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))] [Γ.FiniteIndex]
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
  (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)] [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]

/-- Constants and original-test seminorms precede every source ideal,
actual mask divisor, dual row, radius and residual norm scale. -/
theorem exists_first_density_common_envelope
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (hlc : ∀ v ∈ S, IsLocallyConstant (h v))
    (hcs : ∀ v ∈ S, HasCompactSupport (h v))
    (ε : ℝ) (hε : 0 < ε) (m : ℕ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ φ : SchwartzMap V ℂ, ∀ r : {r : ℝ // 0 < r}, ∀ d : NonzeroRingElements OS,
      ∀ r₁ r₂ b₁ b₂ z : Ext, ∀ X Y : {r : ℝ // 0 < r}, ∀ ξ : LogPlane,
        ‖(FirstParentRetained.profile K S D μv ν φ h hlc hcs r d r₁ r₂ b₁ b₂ z X Y).density
          K S Γ ξ‖ ≤
        (C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ *
          radialScale K S D r d r₁ r₂ b₁ b₂ X Y ^ ε) * frequencyEnvelope m ξ := by
  let p := (volume : Measure LogPlane).integrablePower
  have hfinite := sIntegerFiniteFourierTestFunction_locallyConstant_compactSupport
    K S ν μv h hlc hcs
  obtain ⟨s, C, hC, hb⟩ := exists_orbitalDensity_weighted_smallPower_bound
    K Sset Γ (sIntegerFiniteFourierTestFunction K S μv h) hfinite.1.continuous hfinite.2
    dyadicCutoff dyadicCutoff_contDiff dyadicCutoff_hasCompactSupport ε hε (p + m)
  refine ⟨s, C, hC, fun φ r d r₁ r₂ b₁ b₂ z X Y ξ => ?_⟩
  have hR := outerRadius_power_le K S D ε hε.le r d r₁ r₂ b₁ b₂ z X Y
  have hsmall := (hb φ (outerRadius K S D r d r₁ r₂ b₁ b₂ z X Y) ξ).trans
    (mul_le_mul_of_nonneg_left hR (mul_nonneg hC (apply_nonneg _ _)))
  have hdiv : ‖(FirstParentRetained.profile K S D μv ν φ h hlc hcs
      r d r₁ r₂ b₁ b₂ z X Y).density K S Γ ξ‖ ≤
      (C * s.sup (schwartzSeminormFamily ℝ V ℂ) φ *
        radialScale K S D r d r₁ r₂ b₁ b₂ X Y ^ ε) / (1 + ‖ξ‖) ^ (p + m) := by
    apply (le_div_iff₀ (pow_pos (by positivity : (0 : ℝ) < 1 + ‖ξ‖) (p + m))).mpr
    rw [mul_comm]
    exact hsmall
  simpa only [frequencyEnvelope, fourierEnvelope,
    Real.rpow_neg (by positivity : (0 : ℝ) ≤ 1 + ‖ξ‖), Real.rpow_natCast,
    pow_add, div_eq_mul_inv, mul_inv_rev, p, mul_assoc, mul_comm, mul_left_comm] using hdiv

end HeckeSkeleton.Moments.MOM_INV_STEP.FirstCommonEnvelope

end

