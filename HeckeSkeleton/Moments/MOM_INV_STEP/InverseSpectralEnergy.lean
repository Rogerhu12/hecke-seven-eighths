import HeckeSkeleton.Moments.MOM_INV_STEP.InverseRowMajorant
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
# Integrability of the actual intermediate spectral energy

The coefficient hypotheses below are finite, pointwise facts. They imply
continuity and an integrable majorant for the actual infinite orbital
energy. In particular, enlarging the original finite rows to the free
positive orbital energy is valid under a Mellin integral.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.InverseSpectralEnergy

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.Analysis HeckeGeneral.Bridge HeckeGeneral.ThetaSkeleton
  HeckeGeneral.ThetaSkeleton.Global MeasureTheory
open InverseRowMajorant
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))] [Γ.FiniteIndex]

local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset
local notation "Orbit" => SIntegerOrbits K Sset Γ

-- Keep K and S explicit: the pinned Lean version can lose section dependencies
-- hidden by local notation when re-elaborating included variables.
variable (N : Finset (ExteriorIdeal K (S : Set (HeightOneSpectrum (𝓞 K)))))
variable (a : ℝ → ExteriorIdeal K (S : Set (HeightOneSpectrum (𝓞 K))) → ℂ)
variable (ha : ∀ n ∈ N, Continuous (fun t => a t n))
variable (B : ℝ) (hbound : ∀ t, (∑ n ∈ N, ‖a t n‖) ≤ B)

include ha in
theorem amplitude_continuous (q : Orbit) :
    Continuous (fun t => amplitude K S Γ D N (a t) q) := by
  exact continuous_finsetSum N (fun n hn => (ha n hn).mul continuous_const)

include hbound in
theorem amplitude_bound (t : ℝ) (q : Orbit) :
    ‖amplitude K S Γ D N (a t) q‖ ≤ B :=
  (amplitude_norm_le K S Γ D N (a t) q).trans (hbound t)

theorem summable_fixedProfile (H : {r : ℝ // 0 < r}) :
    Summable (fixedProfile K S Γ H) :=
  (summable_norm_fixedProfile K S Γ H).of_norm

include hbound in
theorem spectral_term_bound (H : {r : ℝ // 0 < r}) (q : Orbit) (t : ℝ) :
    ‖‖amplitude K S Γ D N (a t) q‖ ^ 2 * fixedProfile K S Γ H q‖ ≤
      B ^ 2 * fixedProfile K S Γ H q := by
  rw [Real.norm_of_nonneg
    (mul_nonneg (sq_nonneg _) (fixedProfile_nonneg K S Γ H q))]
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (norm_nonneg _) (amplitude_bound K S Γ D N a B hbound t q) 2)
    (fixedProfile_nonneg K S Γ H q)

include ha hbound in
theorem energy_continuous (H : {r : ℝ // 0 < r}) :
    Continuous (fun t => energy K S Γ D N (a t) H) := by
  exact continuous_tsum
    (fun q => ((amplitude_continuous K S Γ D N a ha q).norm.pow 2).mul continuous_const)
    ((summable_fixedProfile K S Γ H).mul_left (B ^ 2))
    (spectral_term_bound K S Γ D N a B hbound H)

include hbound in
theorem energy_bound (H : {r : ℝ // 0 < r}) (t : ℝ) :
    energy K S Γ D N (a t) H ≤ B ^ 2 * ∑' q, fixedProfile K S Γ H q := by
  rw [energy, ← tsum_mul_left]
  apply (summable_energy K S Γ D N (a t) H).tsum_le_tsum
    (fun q => ?_) ((summable_fixedProfile K S Γ H).mul_left (B ^ 2))
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (norm_nonneg _) (amplitude_bound K S Γ D N a B hbound t q) 2)
    (fixedProfile_nonneg K S Γ H q)

include ha hbound in
theorem weighted_energy_integrable (H : {r : ℝ // 0 < r})
    (w : ℝ → ℝ) (hw : Integrable w) :
    Integrable (fun t => w t * energy K S Γ D N (a t) H) := by
  have hc := energy_continuous K S Γ D N a ha B hbound H
  apply (hw.norm.mul_const (B ^ 2 * ∑' q, fixedProfile K S Γ H q)).mono'
    (hw.aestronglyMeasurable.mul hc.aestronglyMeasurable)
  filter_upwards [] with t
  change ‖w t * energy K S Γ D N (a t) H‖ ≤
    ‖w t‖ * (B ^ 2 * ∑' q, fixedProfile K S Γ H q)
  rw [norm_mul, Real.norm_of_nonneg (energy_nonneg K S Γ D N (a t) H)]
  exact mul_le_mul_of_nonneg_left (energy_bound K S Γ D N a B hbound H t)
    (norm_nonneg _)

include ha in
theorem finite_rows_continuous (T : Finset Orbit) :
    Continuous (fun t => ∑ q ∈ T, ‖amplitude K S Γ D N (a t) q‖ ^ 2) :=
  continuous_finsetSum T
    (fun q hq => (amplitude_continuous K S Γ D N a ha q).norm.pow 2)

include ha hbound in
theorem weighted_finite_rows_integrable (H : {r : ℝ // 0 < r}) (T : Finset Orbit)
    (hT : ∀ q ∈ T, (sIntegerOrbitNorm K Sset Γ q).val ≤ H.val)
    (w : ℝ → ℝ) (hw : Integrable w) (hw0 : ∀ t, 0 ≤ w t) :
    Integrable (fun t => w t * ∑ q ∈ T, ‖amplitude K S Γ D N (a t) q‖ ^ 2) := by
  have hright := (weighted_energy_integrable K S Γ D N a ha B hbound H w hw).const_mul
    (rowCovolume K S)⁻¹
  apply hright.mono_nonneg
    (hw.aestronglyMeasurable.mul
      (finite_rows_continuous K S Γ D N a ha T).aestronglyMeasurable)
  · exact Filter.Eventually.of_forall (fun t =>
      mul_nonneg (hw0 t) (Finset.sum_nonneg (fun q hq => sq_nonneg _)))
  · filter_upwards [] with t
    change w t * (∑ q ∈ T, ‖amplitude K S Γ D N (a t) q‖ ^ 2) ≤
      (rowCovolume K S)⁻¹ * (w t * energy K S Γ D N (a t) H)
    have h := mul_le_mul_of_nonneg_left
      (finite_rows_le_energy K S Γ D N (a t) H T hT) (hw0 t)
    simpa only [mul_left_comm (rowCovolume K S)⁻¹] using h

include ha hbound in
/-- Both sides are genuine integrals: the preceding lemmas establish
integrability from the finite coefficient envelope before comparison. -/
theorem integral_finite_rows_le_energy (H : {r : ℝ // 0 < r}) (T : Finset Orbit)
    (hT : ∀ q ∈ T, (sIntegerOrbitNorm K Sset Γ q).val ≤ H.val)
    (w : ℝ → ℝ) (hw : Integrable w) (hw0 : ∀ t, 0 ≤ w t) :
    (∫ t, w t * ∑ q ∈ T, ‖amplitude K S Γ D N (a t) q‖ ^ 2) ≤
      (rowCovolume K S)⁻¹ * ∫ t, w t * energy K S Γ D N (a t) H := by
  rw [← integral_const_mul]
  apply integral_mono
    (weighted_finite_rows_integrable K S Γ D N a ha B hbound H T hT w hw hw0)
    ((weighted_energy_integrable K S Γ D N a ha B hbound H w hw).const_mul _)
  intro t
  have h := mul_le_mul_of_nonneg_left
    (finite_rows_le_energy K S Γ D N (a t) H T hT) (hw0 t)
  simpa only [mul_left_comm (rowCovolume K S)⁻¹] using h

end HeckeSkeleton.Moments.MOM_INV_STEP.InverseSpectralEnergy

end

