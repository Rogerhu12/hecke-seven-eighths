import ThetaGlobal.LocalArchRootCore
import ThetaGlobal.FiniteLocalHighK
import HeckeSkeleton.ThetaLocal.ProjectArchimedeanWhittaker

/-!
# The actual high K-type local profile in the positive-character convention

`FiniteLocalHighK.localProfile` multiplies the direct Whittaker coefficient
by the positive actual character.  Its vector therefore has the angular
weight of the inverse character.  The merged local direct/reflected
profiles, evaluated at that inverse character, then give the literal
matrix coefficient divided by its value at the identity.

The coordinate is the repository's completion-to-complex isometry, the
functional is the actual continuous theta Jacquet functional, and the
normalizing value is `besselKThird (4 * Real.pi)`.  No local realization,
character compatibility, or profile identity is assumed.

-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace ThetaGlobal.LocalArchProfile

open NumberField DedekindZetaZeroFree
open DedekindZetaZeroFree.MomentSources
open KPCplxCharacterHaar KPCplxPrincipalSeriesCharts KPCplxActualImage
open KPCplxRootDerivativeVectors KPCplxJacquetFunctional KPCplxBessel
open FourierContinuation.ComplexLines
open HeckeGeneral.Characters HeckeSkeleton.ThetaLocal
open ThetaGlobal.LocalArchRootCore
open scoped NumberField Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η) (θ : HeckeCharacter F)

/-- The inverse-character angular weight cancels the positive direct character. -/
def vector (w : InfinitePlace F) : KPGlobalResidualConstruction.complexCore :=
  traceRootCore (heckeComplexWeight F w (R.A.complex_place w) θ⁻¹)

theorem inclusion_vector (w : InfinitePlace F) :
    harmonicInclusion (vector R θ w) =
      archRootVector (4 * Real.pi) traceFrequency
        (heckeComplexWeight F w (R.A.complex_place w) θ⁻¹) :=
  harmonicInclusion_traceRootCore _

theorem functional_value (w : InfinitePlace F) :
    thetaJacquetFunctional traceFrequency (harmonicInclusion (vector R θ w)) =
      (besselKThird (4 * Real.pi) : ℂ) :=
  traceRootCore_value _

theorem functional_nonzero (w : InfinitePlace F) :
    thetaJacquetFunctional traceFrequency (harmonicInclusion (vector R θ w)) ≠ 0 :=
  traceRootCore_functional_nonzero _

theorem completion_character (w : InfinitePlace F) (z : w.Completionˣ) :
    complexHeckeComponent F w (R.A.complex_place w) θ
      (completionUnitsToComplex (R.A.complex_place w) z) =
        infiniteComponent F w θ z := by
  change infiniteComponent F w θ
    (complexUnitsToCompletion (R.A.complex_place w)
      (completionUnitsToComplex (R.A.complex_place w) z)) = _
  rw [complexUnitsToCompletion_inverse]

theorem inverse_completion_character (w : InfinitePlace F) (z : w.Completionˣ) :
    (complexHeckeComponent F w (R.A.complex_place w) θ⁻¹
      (completionUnitsToComplex (R.A.complex_place w) z) : ℂ) =
        (infiniteComponent F w θ z : ℂ)⁻¹ := by
  rw [completion_character R θ⁻¹ w z]
  change (((infiniteComponent F w θ z)⁻¹ : Circle) : ℂ) = _
  exact Circle.coe_inv _

theorem completion_radius (w : InfinitePlace F) (z : w.Completionˣ) :
    radius (completionUnitsToComplex (R.A.complex_place w) z) = ‖z.val‖ :=
  norm_completionUnitsToComplex (R.A.complex_place w) z

theorem localArgument_direct (w : InfinitePlace F) (z : w.Completionˣ) :
    FiniteLocalHighK.localArgument R w false z =
      Matrix.ProjGenLinGroup.mk
        (diagonal (completionUnitsToComplex (R.A.complex_place w) z)) := by
  change Matrix.ProjGenLinGroup.mk
    (diagonal (completionUnitsToComplex (R.A.complex_place w) z) * 1) = _
  rw [mul_one]

theorem localArgument_reflected (w : InfinitePlace F) (z : w.Completionˣ) :
    FiniteLocalHighK.localArgument R w true z =
      Matrix.ProjGenLinGroup.mk
        (diagonal (completionUnitsToComplex (R.A.complex_place w) z)) *
          Matrix.ProjGenLinGroup.mk weyl := by
  change Matrix.ProjGenLinGroup.mk
    (diagonal (completionUnitsToComplex (R.A.complex_place w) z) * weyl) = _
  rw [map_mul]

private theorem imageAction_mul (β : ℂˣ) (g h : ComplexPGL2) (v : Theta β) :
    imageAction β (g * h) v = imageAction β g (imageAction β h v) := by
  apply Subtype.ext
  exact pi_mul negativeParameter g h v.val

/-- The exact direct source profile, with the fixed canonical denominator. -/
theorem direct_profile (w : InfinitePlace F) (z : w.Completionˣ) :
    FiniteLocalHighK.localProfile R θ (thetaJacquetFunctional traceFrequency)
      (vector R θ w) w false z =
      HeckeSkeleton.ThetaLocal.Project.directProfile F θ⁻¹
        ⟨w, R.A.complex_place w⟩ (4 * Real.pi) (‖z.val‖ ^ 2) /
          (besselKThird (4 * Real.pi) : ℂ) := by
  let y := completionUnitsToComplex (R.A.complex_place w) z
  have h := HeckeSkeleton.ThetaLocal.Project.directProfile_from_whittaker_character
    F θ⁻¹ ⟨w, R.A.complex_place w⟩ (4 * Real.pi) (by positivity)
    traceFrequency rfl y
  dsimp only [y] at h
  rw [inverse_completion_character R θ w z, inv_inv, completion_radius R w z] at h
  change (infiniteComponent F w θ z : ℂ) *
      thetaJacquetFunctional traceFrequency
        (imageAction traceFrequency (FiniteLocalHighK.localArgument R w false z)
          (harmonicInclusion (vector R θ w))) /
        thetaJacquetFunctional traceFrequency (harmonicInclusion (vector R θ w)) = _
  rw [functional_value R θ w, inclusion_vector R θ w, localArgument_direct R w z]
  change (infiniteComponent F w θ z : ℂ) *
      whittakerValue traceFrequency
        (archRootVector (4 * Real.pi) traceFrequency
          (heckeComplexWeight F w (R.A.complex_place w) θ⁻¹)) y /
        (besselKThird (4 * Real.pi) : ℂ) = _
  rw [mul_comm (infiniteComponent F w θ z : ℂ)]
  exact congrArg (fun a : ℂ => a / (besselKThird (4 * Real.pi) : ℂ)) h

/-- The actual diagonal-times-Weyl argument gives the corresponding reflected profile. -/
theorem reflected_profile (w : InfinitePlace F) (z : w.Completionˣ) :
    FiniteLocalHighK.localProfile R θ (thetaJacquetFunctional traceFrequency)
      (vector R θ w) w true z =
      HeckeSkeleton.ThetaLocal.Project.reflectedProfile F θ⁻¹
        ⟨w, R.A.complex_place w⟩ (4 * Real.pi) (‖z.val‖ ^ 2) /
          (besselKThird (4 * Real.pi) : ℂ) := by
  let y := completionUnitsToComplex (R.A.complex_place w) z
  have h := HeckeSkeleton.ThetaLocal.Project.reflectedProfile_from_whittaker_character
    F θ⁻¹ ⟨w, R.A.complex_place w⟩ (4 * Real.pi) (by positivity)
    traceFrequency rfl y
  dsimp only [y] at h
  rw [inverse_completion_character R θ w z, completion_radius R w z] at h
  change (infiniteComponent F w θ z : ℂ)⁻¹ *
      thetaJacquetFunctional traceFrequency
        (imageAction traceFrequency (FiniteLocalHighK.localArgument R w true z)
          (harmonicInclusion (vector R θ w))) /
        thetaJacquetFunctional traceFrequency (harmonicInclusion (vector R θ w)) = _
  rw [functional_value R θ w, inclusion_vector R θ w,
    localArgument_reflected R w z, imageAction_mul]
  change (infiniteComponent F w θ z : ℂ)⁻¹ *
      whittakerValue traceFrequency
        (imageAction traceFrequency (Matrix.ProjGenLinGroup.mk weyl)
          (archRootVector (4 * Real.pi) traceFrequency
            (heckeComplexWeight F w (R.A.complex_place w) θ⁻¹))) y /
        (besselKThird (4 * Real.pi) : ℂ) = _
  rw [mul_comm ((infiniteComponent F w θ z : ℂ)⁻¹)]
  exact congrArg (fun a : ℂ => a / (besselKThird (4 * Real.pi) : ℂ)) h

end ThetaGlobal.LocalArchProfile

#print axioms ThetaGlobal.LocalArchProfile.inclusion_vector
#print axioms ThetaGlobal.LocalArchProfile.functional_nonzero
#print axioms ThetaGlobal.LocalArchProfile.direct_profile
#print axioms ThetaGlobal.LocalArchProfile.reflected_profile
