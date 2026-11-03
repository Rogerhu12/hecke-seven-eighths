import HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.SourceProfileJets
import HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.FourierApplication
import HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.ProfileCommonFourier

/-!
# The actual inverse profile has the common weighted Fourier bound

The Schwartz function below equals the original physical inverse profile
in logarithmic coordinates.  The compact extension only packages the
one-sided cutoff: its values on every nonnegative scaled norm are unchanged.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.Moments.UniformAmplify

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Global
open _root_.ExpansionRecipe.LogProfile
open scoped Classical BigOperators ContDiff FourierTransform

variable (K : Type) [Field K] [NumberField K] (c : TargetContext K)

def actualInverseLogProfile (U D a ν ξ : ℝ) : SchwartzMap ℝ ℂ :=
  scaledCompactExpTwist (profileLogPullback dyadicSmoothAnnularTest.toFun)
    (cutoffSchwartz Expansion.Dyadic.cutoffProfile Expansion.Dyadic.cutoffProfile_smooth
      Expansion.Dyadic.cutoffProfile_zero)
    (annular_log_compact dyadicSmoothAnnularTest) (annular_log_smooth dyadicSmoothAnnularTest)
    (D / U ^ (2 * ξ)) ((a : ℂ) + (ν : ℂ) * Complex.I)

/-- Exact equality to every original ideal-row profile, before Fourier
transformation or norm estimates are applied. -/
theorem actualInverseLogProfile_apply (u : NonzeroIdeal K) (U D a ν ξ : ℝ)
    (hU : 0 < U) (hD : 0 ≤ D) (x : ℝ) :
    actualInverseLogProfile U D a ν ξ x =
      actualInverseScalarProfile K c u U D a ν ξ (Real.exp x) := by
  rw [actualInverseScalarProfile_eq]
  rw [annularCutoffNormTwist_log]
  change _ * cutoffSchwartz Expansion.Dyadic.cutoffProfile
      Expansion.Dyadic.cutoffProfile_smooth Expansion.Dyadic.cutoffProfile_zero
        ((D / U ^ (2 * ξ)) * Real.exp x) * _ = _
  rw [cutoffSchwartz_apply, cutoffSchwartzFun_eq_nonneg Expansion.Dyadic.cutoffProfile
    Expansion.Dyadic.cutoffProfile_one
      (mul_nonneg (div_nonneg hD (Real.rpow_pos_of_pos hU _).le) (Real.exp_pos x).le)]

/-- Its weighted Fourier mass is uniform in the original independent
scales and cutoff coordinate, with a fixed polynomial height degree. -/
theorem actual_source_inverse_fourier_moment (J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ U : ℝ, 0 < U → ∀ D : ℝ, 0 ≤ D →
      ∀ T : ℝ, 0 ≤ T → ∀ a ν ξ : ℝ, |a| ≤ 8 →
      |ν| ≤ |(expansionRecipeRaw K c).family.frequencyScale| * (1 + T) →
      (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖(𝓕 (actualInverseLogProfile U D a ν ξ)) t‖) ≤
        C * (1 + T) ^ (J + integrationPower : ℕ) := by
  let W := dyadicSmoothAnnularTest
  let V := cutoffSchwartz Expansion.Dyadic.cutoffProfile
    Expansion.Dyadic.cutoffProfile_smooth Expansion.Dyadic.cutoffProfile_zero
  let M := |(expansionRecipeRaw K c).family.frequencyScale|
  obtain ⟨C, hC, hb⟩ := scaled_compact_exp_twist_uniform_fourier_moment
    (profileLogPullback W.toFun) V (annular_log_compact W) (annular_log_smooth W)
    8 (annularLogRadius W) (by norm_num) (annularLogRadius_nonneg W)
    (annular_log_support W) J
  let n := J + integrationPower
  refine ⟨C * (1 + M) ^ n, by dsimp [M]; positivity, ?_⟩
  intro U hU D hD T hT a ν ξ ha hν
  have h := hb (D / U ^ (2 * ξ)) (div_nonneg hD (Real.rpow_pos_of_pos hU _).le)
    ((a : ℂ) + (ν : ℂ) * Complex.I) (by simpa using ha)
  have hp := polynomial_twist_height (abs_nonneg ((expansionRecipeRaw K c).family.frequencyScale))
    hT hν n
  rw [Real.rpow_natCast] at hp
  have him : (((a : ℂ) + (ν : ℂ) * Complex.I)).im = ν := by simp
  rw [him] at h
  exact h.trans ((mul_le_mul_of_nonneg_left hp hC).trans_eq (by ring))


/-- One pointwise majorant is selected before all independent scales,
rowwise real/imaginary shifts and cutoff coordinates of the actual source. -/
theorem actual_source_inverse_common_fourier_majorant (J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 ≤ T → ∃ W : ℝ → ℝ,
      (∀ t, 0 ≤ W t) ∧ Integrable (fun t : ℝ => (1 + ‖t‖) ^ J * W t) ∧
      (∫ t : ℝ, (1 + ‖t‖) ^ J * W t) ≤ C * (1 + T) ^ (J + 2 : ℕ) ∧
      ∀ U : ℝ, 0 < U → ∀ D : ℝ, 0 ≤ D → ∀ a ν ξ : ℝ,
        |a| ≤ 8 → |ν| ≤ |(expansionRecipeRaw K c).family.frequencyScale| * (1 + T) →
        ∀ t : ℝ, ‖(𝓕 (actualInverseLogProfile U D a ν ξ)) t‖ ≤ W t := by
  obtain ⟨C, hC, hb⟩ := scaled_common_profile_fourier_majorant
    (profileLogPullback dyadicSmoothAnnularTest.toFun)
    (cutoffSchwartz Expansion.Dyadic.cutoffProfile Expansion.Dyadic.cutoffProfile_smooth
      Expansion.Dyadic.cutoffProfile_zero)
    (annular_log_compact dyadicSmoothAnnularTest) (annular_log_smooth dyadicSmoothAnnularTest)
    8 (annularLogRadius dyadicSmoothAnnularTest) |(expansionRecipeRaw K c).family.frequencyScale|
    (by norm_num) (annularLogRadius_nonneg _) (abs_nonneg _) (annular_log_support _) J
  refine ⟨C, hC, ?_⟩
  intro T hT
  obtain ⟨W, hW0, hWi, hWmass, hWbound⟩ := hb T hT
  refine ⟨W, hW0, hWi, hWmass, ?_⟩
  intro U hU D hD a ν ξ ha hν t
  exact hWbound (D / U ^ (2 * ξ)) (div_nonneg hD (Real.rpow_pos_of_pos hU _).le)
    ((a : ℂ) + (ν : ℂ) * Complex.I) (by simpa using ha) (by simpa using hν) t

/-- The actual source Fourier factors can vary by row.  Their products
with a measurable child vector are integrable under the one common
majorant, and the resulting Hilbert bound has no cardinality factor. -/
theorem actual_source_rowwise_fourier_envelope (J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 ≤ T →
      ∀ (ι : Type*) [Fintype ι] (U D a ν ξ : ι → ℝ),
        (∀ i, 0 < U i) → (∀ i, 0 ≤ D i) → (∀ i, |a i| ≤ 8) →
        (∀ i, |ν i| ≤ |(expansionRecipeRaw K c).family.frequencyScale| * (1 + T)) →
        ∀ child : ℝ → ι → ℂ,
        (∀ i, AEStronglyMeasurable (fun t : ℝ => child t i)) →
        ∀ E : ℝ, 0 ≤ E →
        (∀ t : ℝ, Real.sqrt (∑ i, ‖child t i‖ ^ 2) ≤ E * (1 + ‖t‖) ^ J) →
        Real.sqrt (∑ i, ‖∫ t : ℝ,
          (𝓕 (actualInverseLogProfile (U i) (D i) (a i) (ν i) (ξ i))) t * child t i‖ ^ 2) ≤
          C * (1 + T) ^ (J + 2 : ℕ) * E := by
  obtain ⟨C, hC, hb⟩ := scaled_rowwise_fourier_envelope
    (profileLogPullback dyadicSmoothAnnularTest.toFun)
    (cutoffSchwartz Expansion.Dyadic.cutoffProfile Expansion.Dyadic.cutoffProfile_smooth
      Expansion.Dyadic.cutoffProfile_zero)
    (annular_log_compact dyadicSmoothAnnularTest) (annular_log_smooth dyadicSmoothAnnularTest)
    8 (annularLogRadius dyadicSmoothAnnularTest) |(expansionRecipeRaw K c).family.frequencyScale|
    (by norm_num) (annularLogRadius_nonneg _) (abs_nonneg _) (annular_log_support _) J
  refine ⟨C, hC, ?_⟩
  intro T hT ι _ U D a ν ξ hU hD ha hν child hc E hE hchild
  exact hb T hT ι (fun i => D i / U i ^ (2 * ξ i))
    (fun i => (a i : ℂ) + (ν i : ℂ) * Complex.I)
    (fun i => div_nonneg (hD i) (Real.rpow_pos_of_pos (hU i) _).le)
    (fun i => by simpa using ha i) (fun i => by simpa using hν i)
    child hc E hE hchild

end HeckeSkeleton.Moments.UniformAmplify
