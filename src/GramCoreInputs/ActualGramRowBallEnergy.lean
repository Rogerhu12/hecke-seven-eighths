import ActualAdditiveGramFreeOrbitalAssembly
import ActualGramRowBallOrbitalMajorant
import Mathlib.Analysis.Complex.Basic

/-!
UNCOMPILED candidate. Actual finite sector energies are dominated by a
convergent orbital series with the constructed free row-ball test. Its
nonnegativity and positive covolume lower bound are proved providers, not
analytic hypotheses. The original sixth-power-unit quotient is retained.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeGeneral.ThetaSkeleton.Physical.ActualGramMajorantDraft

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Bridge
open HeckeGeneral.ThetaSkeleton.Global
open ActualAdditiveGramDraft ActualAdditiveGramFreeDraft
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "SF" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Γ" => sixthPowerUnits K SF
local notation "OQ" => SIntegerOrbits K SF Γ

local instance energy_sixthUnits_finiteIndex : Subgroup.FiniteIndex Γ :=
  sUnit_power_range_finiteIndex K SF 6 (by decide)

variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]

/-- Every finite set in the scaled original row ball is controlled by the
real part of the actual positive weighted series. Summability is derived
from the finite ideal-pair expansion and actual Haar unfolding. -/
theorem sum_actualGram_sectors_le_rowBallWeightedSeries
    (P : ProbeData K SF) (c : ExteriorIdeal K SF → ℂ) (W : SmoothAnnularTest)
    (Y η : ℝ) (hY : 0 < Y) (B : ℝ) (r : {r : ℝ // 0 < r}) (F : Finset OQ)
    (hF : ∀ q ∈ F, r.val * (sIntegerOrbitNorm K SF Γ q).val ≤ B) :
    (∑ q ∈ F, ‖actualAdditiveGramOrbitAmplitude K SF P c W Y η q‖ ^ 2) ≤
      (sUnitHaarCovolume K SF Γ).toReal⁻¹ *
        (sIntegerWeightedOrbitalSeries K S Γ (rowBallArchTest K S B)
          (sIntegerFiniteTestFunction K S (rowBallFiniteFamily K S B)) r
          (fun q => ((‖actualAdditiveGramOrbitAmplitude K SF P c W Y η q‖ ^ 2 : ℝ) : ℂ))).re := by
  let E : OQ → ℝ := fun q => ‖actualAdditiveGramOrbitAmplitude K SF P c W Y η q‖ ^ 2
  let H : OQ → ℂ := freeAdditiveGramOrbitProfile K S
    (rowBallArchTest K S B) (rowBallFiniteFamily K S B) r
  have hs : Summable (fun q : OQ => (E q : ℂ) * H q) :=
    summable_actualAdditiveGramOrbitAmplitude_norm_sq_freeProfile K S P c W Y η hY
      (rowBallArchTest K S B) (rowBallFiniteFamily K S B)
      (rowBallFiniteFamily_locallyConstant K S B)
      (rowBallFiniteFamily_compactSupport K S B) r
  have hsR : HasSum (fun q : OQ => E q * (H q).re)
      (∑' q : OQ, (E q : ℂ) * H q).re := by
    have hsC : HasSum (fun q : OQ => ((E q : ℂ) * H q).re)
        (∑' q : OQ, (E q : ℂ) * H q).re := RCLike.hasSum_re ℂ hs.hasSum
    simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero] using hsC
  have hH (q : OQ) : 0 ≤ (H q).re :=
    (rowBall_orbitalProfile_real_nonnegative K S B
      ⟨r.val * (sIntegerOrbitNorm K SF Γ q).val,
        mul_pos r.property (sIntegerOrbitNorm K SF Γ q).property⟩).2
  have hscaled : (sUnitHaarCovolume K SF Γ).toReal * (∑ q ∈ F, E q) ≤
      (∑' q : OQ, (E q : ℂ) * H q).re := by
    calc
      _ = ∑ q ∈ F, (sUnitHaarCovolume K SF Γ).toReal * E q := Finset.mul_sum _ _ _
      _ ≤ ∑ q ∈ F, E q * (H q).re := by
        apply Finset.sum_le_sum
        intro q hq
        have hE : 0 ≤ E q :=
          sq_nonneg ‖actualAdditiveGramOrbitAmplitude K SF P c W Y η q‖
        have hlow : (sUnitHaarCovolume K SF Γ).toReal ≤ (H q).re :=
          rowBall_orbit_profile_lower K S B r q (hF q hq)
        calc
          _ = E q * (sUnitHaarCovolume K SF Γ).toReal := mul_comm _ _
          _ ≤ _ := mul_le_mul_of_nonneg_left hlow hE
      _ ≤ ∑' q : OQ, E q * (H q).re :=
        hsR.summable.sum_le_tsum F (fun q _ => mul_nonneg (sq_nonneg _) (hH q))
      _ = _ := hsR.tsum_eq
  have hdiv : (∑ q ∈ F, E q) ≤
      (∑' q : OQ, (E q : ℂ) * H q).re / (sUnitHaarCovolume K SF Γ).toReal :=
    (le_div_iff₀ (rowBall_covolume_pos K S)).mpr (by simpa only [mul_comm] using hscaled)
  simpa only [sIntegerWeightedOrbitalSeries, E, H, freeAdditiveGramOrbitProfile,
    div_eq_mul_inv, mul_comm] using hdiv

/-- A single fixed test (B=1) works for every positive row cutoff Q. The
radius is exactly Q inverse; the covolume factor is fixed before Q or Y. -/
theorem sum_actualGram_rowBall_le_weightedSeries
    (P : ProbeData K SF) (c : ExteriorIdeal K SF → ℂ) (W : SmoothAnnularTest)
    (Y η : ℝ) (hY : 0 < Y) (Q : ℝ) (hQ : 0 < Q) (F : Finset OQ)
    (hF : ∀ q ∈ F, (sIntegerOrbitNorm K SF Γ q).val ≤ Q) :
    (∑ q ∈ F, ‖actualAdditiveGramOrbitAmplitude K SF P c W Y η q‖ ^ 2) ≤
      (sUnitHaarCovolume K SF Γ).toReal⁻¹ *
        (sIntegerWeightedOrbitalSeries K S Γ (rowBallArchTest K S 1)
          (sIntegerFiniteTestFunction K S (rowBallFiniteFamily K S 1))
          ⟨Q⁻¹, inv_pos.mpr hQ⟩
          (fun q => ((‖actualAdditiveGramOrbitAmplitude K SF P c W Y η q‖ ^ 2 : ℝ) : ℂ))).re := by
  apply sum_actualGram_sectors_le_rowBallWeightedSeries K S P c W Y η hY 1
    ⟨Q⁻¹, inv_pos.mpr hQ⟩ F
  intro q hq
  calc
    _ ≤ Q⁻¹ * Q := mul_le_mul_of_nonneg_left (hF q hq) (inv_nonneg.mpr hQ.le)
    _ = 1 := inv_mul_cancel₀ hQ.ne'

end HeckeGeneral.ThetaSkeleton.Physical.ActualGramMajorantDraft
