import HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.SourceProfileControl
import HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.ProfileScaleJets

/-!
# Mixed derivatives of the same actual source profile

The scalar coordinates below are the real exponent, imaginary exponent,
and cutoff coordinate of the literal unmarked model.  They do not
include the discrete arithmetic-presentation selector.  The equalities
identify these scalar slices with the source model before differentiation.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.Moments.UniformAmplify

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ExpansionRecipe
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical HeckeGeneral.ThetaSkeleton.TIP
open scoped Classical BigOperators ContDiff

variable (K : Type) [Field K] [NumberField K] (c : TargetContext K)

/-- This is the actual raw inverse annular/cutoff formula in continuous
scalar coordinates.  No smoothness or seminorm bound is assumed. -/
def actualInverseScalarProfile (u : NonzeroIdeal K) (U D a ν ξ y : ℝ) : ℂ :=
  (expansionRecipeRaw K c).family.inverseAnnular.profile u 0 y *
    (expansionRecipeRaw K c).family.cutoff ((D / U ^ (2 * ξ)) * y) *
      profilePower ((a : ℂ) + (ν : ℂ) * Complex.I) y

theorem actualInverseScalarProfile_eq (u : NonzeroIdeal K) (U D a ν ξ : ℝ) :
    actualInverseScalarProfile K c u U D a ν ξ =
      annularCutoffNormTwist dyadicSmoothAnnularTest Expansion.Dyadic.cutoffProfile
        (D / U ^ (2 * ξ)) ((a : ℂ) + (ν : ℂ) * Complex.I) := rfl

/-- Every row of the independently scaled source family is one of these
same scalar profiles at its original real/imaginary shifts. -/
theorem actual_unmarked_inverse_profile (U D : ℝ)
    (sector : SixthUnitClasses K (places K c)) (ξ : RecipeVector)
    (σ τ : NonzeroIdeal K → RecipeVector) (u : NonzeroIdeal K) :
    ((recipeMomentModels K c (expansionRecipeRaw K c)).unmarked U D sector ξ σ τ).inverseTest.profile
        u 0 =
      actualInverseScalarProfile K c u U D (-(σ u 0))
        ((expansionRecipeRaw K c).family.frequencyScale * τ u 0) (ξ 3) := by
  funext y
  simp only [actualInverseScalarProfile, Complex.ofReal_neg]
  rfl

def actualInverseMixedJet (u : NonzeroIdeal K) (U D : ℝ)
    (r s n : ℕ) (a ν ξ y : ℝ) : ℂ :=
  iteratedDeriv n (fun q : ℝ => iteratedDeriv r (fun a' : ℝ => iteratedDeriv s
    (fun ν' : ℝ => actualInverseScalarProfile K c u U D a' ν' q y) ν) a) ξ

theorem actualInverseMixedJet_eq (u : NonzeroIdeal K) (U D : ℝ)
    (r s n : ℕ) (a ν ξ : ℝ) :
    actualInverseMixedJet K c u U D r s n a ν ξ =
      annularMixedScaleJet dyadicSmoothAnnularTest Expansion.Dyadic.cutoffProfile
        U D r s n a ν ξ := rfl

/-- The mixed derivative bound is produced for the actual source formula,
including arbitrary independent U,D and the logarithmic cutoff coordinate.
Its finite order and height degree are fixed before every moving parameter. -/
theorem actual_source_inverse_mixed_profile_control (r s n J : ℕ) (A : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : NonzeroIdeal K) (U : ℝ), 0 < U →
      ∀ D : ℝ, 0 ≤ D → ∀ T : ℝ, 0 ≤ T →
      ∀ ξ a ν : ℝ, |a| ≤ 8 →
        |ν| ≤ |(expansionRecipeRaw K c).family.frequencyScale| * (1 + T) →
        SliceControl J A (C * (1 + |Real.log U|) ^ n) (J : ℝ) (1 / 2) 2 T
          (actualInverseMixedJet K c u U D r s n a ν ξ) := by
  obtain ⟨C, hC, hb⟩ := annular_mixed_scale_jet_slice_control
    dyadicSmoothAnnularTest Expansion.Dyadic.cutoffProfile
    Expansion.Dyadic.cutoffProfile_smooth Expansion.Dyadic.cutoffProfile_one
    Expansion.Dyadic.cutoffProfile_zero r s n J 8
    |(expansionRecipeRaw K c).family.frequencyScale| A (by norm_num) (abs_nonneg _)
  refine ⟨C, hC, ?_⟩
  intro u U hU D hD T hT ξ a ν ha hν
  rw [actualInverseMixedJet_eq]
  exact hb U hU D hD T hT ξ a ν ha hν

/-- Prime windows have the same literal norm-power mixed derivatives.  A
fixed slot system is finite; its maximum scalar can be chosen before the
physical spectral parameter, as in the whole-model proof. -/
theorem actual_source_prime_mixed_profile_control (j : Fin c.geometry.slots)
    (r s J : ℕ) (A : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 ≤ T → ∀ a ν : ℝ,
      |a| ≤ 1 → |ν| ≤ 1 + T →
      SliceControl J A C (J : ℝ) (1 / 2) 2 T
        (fun y => iteratedDeriv r (fun a' : ℝ => iteratedDeriv s
          (fun ν' : ℝ => (c.geometry.weight j).toFun y *
            profilePower ((a' : ℂ) + (ν' : ℂ) * Complex.I) y) ν) a) := by
  obtain ⟨C, hC, hb⟩ := annular_mixed_norm_twist_slice_control
    (primeSmoothAnnularTest c.geometry j) r s 1 1 (by norm_num) (by norm_num) J A
  refine ⟨C, hC, ?_⟩
  intro T hT a ν ha hν
  have h := hb T hT ((a : ℂ) + (ν : ℂ) * Complex.I)
    (by simpa using ha) (by simpa using hν)
  have he : (fun y => iteratedDeriv r (fun a' : ℝ => iteratedDeriv s
      (fun ν' : ℝ => (c.geometry.weight j).toFun y *
        profilePower ((a' : ℂ) + (ν' : ℂ) * Complex.I) y) ν) a) =
      annularNormTwist (annularMixedWindow (primeSmoothAnnularTest c.geometry j) r s)
        ((a : ℂ) + (ν : ℂ) * Complex.I) := by
    funext y
    exact annularNormTwist_mixed_derivative (primeSmoothAnnularTest c.geometry j) r s a ν y
  rw [he]
  exact h

end HeckeSkeleton.Moments.UniformAmplify
