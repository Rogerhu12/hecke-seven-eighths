import ActualGramRowBallEnergy
import ActualGramFreeZeroFrequency

/-!
UNCOMPILED candidate. The actual original-sector row-ball energy reduces to
the nonzero dual correlation term plus O(Q/Y). The latter comes from the
proved full zero-frequency calculation with the constructed free majorant.
No Gram estimate or sign condition is supplied as an input.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeGeneral.ThetaSkeleton.Physical.ActualGramMajorantDraft

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Bridge
open HeckeGeneral.ThetaSkeleton.Global
open ActualAdditiveGramDraft ActualAdditiveGramFreeDraft ActualGramFreeZeroDraft
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "SF" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Γ" => sixthPowerUnits K SF
local notation "OQ" => SIntegerOrbits K SF Γ

local instance reduction_sixthUnits_finiteIndex : Subgroup.FiniteIndex Γ :=
  sUnit_power_range_finiteIndex K SF 6 (by decide)

variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]

/-- The unchanged nonzero dual term, including its exact Poisson prefactor,
pair-dependent radius and original full correlation coefficients. -/
def rowBallDualSeriesTerm (P : ProbeData K SF) (c : ExteriorIdeal K SF → ℂ)
    (W : SmoothAnnularTest) (Y η : ℝ) (r : {r : ℝ // 0 < r}) : ℂ :=
  ((r.val : ℂ)⁻¹ * ((Y ^ (-3 : ℝ) : ℝ) : ℂ) * additiveGramPoissonFieldFactor K) *
    ∑ I ∈ additiveGramIdealSupport K SF W Y,
      ∑ J ∈ additiveGramIdealSupport K SF W Y,
        actualAdditiveGramPairCoefficient K SF c W Y η I J *
          freeAdditiveGramPairDualOrbitalSeries K S μv P I J
            (rowBallArchTest K S 1) (rowBallFiniteFamily K S 1) r

variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
  (μf : Measure (FiniteAdeleRing (𝓞 K) K)) [μf.IsAddHaarMeasure]
  [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
  (μ : Measure (AdeleRing (𝓞 K) K)) [μ.IsAddHaarMeasure]

include μ μf in
/-- The same covolume in the majorization and the genuine orbital Poisson
zero correction cancels exactly. It is never normalized to one. -/
theorem rowBallWeightedSeries_re_eq_dual_add_zero
    (P : ProbeData K SF) (c : ExteriorIdeal K SF → ℂ) (W : SmoothAnnularTest)
    (Y η : ℝ) (hY : 0 < Y) (r : {r : ℝ // 0 < r}) :
    (sUnitHaarCovolume K SF Γ).toReal⁻¹ *
      (sIntegerWeightedOrbitalSeries K S Γ (rowBallArchTest K S 1)
        (sIntegerFiniteTestFunction K S (rowBallFiniteFamily K S 1)) r
        (fun q => ((‖actualAdditiveGramOrbitAmplitude K SF P c W Y η q‖ ^ 2 : ℝ) : ℂ))).re =
    (sUnitHaarCovolume K SF Γ).toReal⁻¹ * (rowBallDualSeriesTerm K S μv P c W Y η r).re +
      (freeGramNormalizedZeroCorrection K S μv P c W Y η
        (rowBallArchTest K S 1) (rowBallFiniteFamily K S 1) r).re := by
  have hp :
      sIntegerWeightedOrbitalSeries K S Γ (rowBallArchTest K S 1)
        (sIntegerFiniteTestFunction K S (rowBallFiniteFamily K S 1)) r
        (fun q => ((‖actualAdditiveGramOrbitAmplitude K SF P c W Y η q‖ ^ 2 : ℝ) : ℂ)) =
      rowBallDualSeriesTerm K S μv P c W Y η r +
        ((sUnitHaarCovolume K SF Γ).toReal : ℂ) *
          freeGramNormalizedZeroCorrection K S μv P c W Y η
            (rowBallArchTest K S 1) (rowBallFiniteFamily K S 1) r := by
    change (∑' q : OQ,
      ((‖actualAdditiveGramOrbitAmplitude K SF P c W Y η q‖ ^ 2 : ℝ) : ℂ) *
        freeAdditiveGramOrbitProfile K S (rowBallArchTest K S 1)
          (rowBallFiniteFamily K S 1) r q) = _
    rw [tsum_actualAdditiveGramOrbitAmplitude_norm_sq_freeProfile_poisson
      K S μf μv μ P c W Y η hY (rowBallArchTest K S 1) (rowBallFiniteFamily K S 1)
      (rowBallFiniteFamily_locallyConstant K S 1)
      (rowBallFiniteFamily_compactSupport K S 1) r]
    dsimp only [rowBallDualSeriesTerm, freeGramNormalizedZeroCorrection]
    ring
  rw [hp, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, mul_add, ← mul_assoc,
    inv_mul_cancel₀ (rowBall_covolume_pos K S).ne', one_mul]

include μ μf in
/-- Zero frequency is bounded by C*Q/Y. The remaining expression is exactly
the nonzero dual correlation sum for the fixed constructed row-ball test.
The constant and threshold precede all moving data and finite sector sets. -/
theorem exists_actualGram_rowBall_reduction (W : SmoothAnnularTest) :
    ∃ C Y₀ : ℝ, 0 < C ∧ 1 ≤ Y₀ ∧
      ∀ (P : ProbeData K SF) (c : ExteriorIdeal K SF → ℂ),
        (∀ I, ‖c I‖ ≤ 1) → ∀ (Q Y η : ℝ) (hQ : 0 < Q), Y₀ ≤ Y →
      ∀ F : Finset OQ, (∀ q ∈ F, (sIntegerOrbitNorm K SF Γ q).val ≤ Q) →
      (∑ q ∈ F, ‖actualAdditiveGramOrbitAmplitude K SF P c W Y η q‖ ^ 2) ≤
        (sUnitHaarCovolume K SF Γ).toReal⁻¹ *
          ‖rowBallDualSeriesTerm K S μv P c W Y η ⟨Q⁻¹, inv_pos.mpr hQ⟩‖ + C * Q / Y := by
  obtain ⟨C, Y₀, hC, hY₀, hzero⟩ := exists_rowBall_freeZero_re_Q_div_Y_bound K S μv 1 W
  refine ⟨C, Y₀, hC, hY₀, ?_⟩
  intro P c hc Q Y η hQ hY F hF
  have hYpos : 0 < Y := zero_lt_one.trans_le (hY₀.trans hY)
  have hbound := sum_actualGram_rowBall_le_weightedSeries K S P c W Y η hYpos Q hQ F hF
  rw [rowBallWeightedSeries_re_eq_dual_add_zero K S μv μf μ P c W Y η hYpos] at hbound
  exact hbound.trans (add_le_add
    (mul_le_mul_of_nonneg_left (Complex.re_le_norm _)
      (inv_nonneg.mpr (rowBall_covolume_pos K S).le))
    (hzero P c hc Q Y η hQ hY))

end HeckeGeneral.ThetaSkeleton.Physical.ActualGramMajorantDraft
