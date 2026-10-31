import ThetaGlobal.LocalArchMellin
import ThetaGlobal.LocalArchBounds

/-!
# The canonical local high K-type input for the fixed actual source

All fields of the existing `FiniteLocalHighK.Input` are supplied by actual
repository constructions: the inverse-character root vector, the trace
Jacquet functional, the source's retained local Whittaker functional,
and the literal completion-unit Haar measure.  Its angular mass remains
in each Mellin constant.  The positive Bessel value at the identity is
the normalization in both the Mellin formulas and the pointwise bounds.

The source record retains the continuous Whittaker certificate proved
in its spherical construction. It is preserved by the finite projector,
and transfers nonvanishing to the stored functional on the selected vector
without an additional existence or nonvanishing premise.
-/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace ThetaGlobal.LocalArchInput

open NumberField DedekindZetaZeroFree
open DedekindZetaZeroFree.MomentSources
open KPCplxJacquetFunctional KPCplxBessel FourierContinuation.ComplexLines
open HeckeGeneral.Characters HeckeSkeleton.ThetaLocal
open scoped NumberField Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η) (θ : HeckeCharacter F)

/-- Divide the actual direct profile bound by its fixed value at one. -/
theorem direct_bound (w : InfinitePlace F) (σ : ℝ) (hσ : -(1 / 3 : ℝ) < σ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z : w.Completionˣ,
      ‖FiniteLocalHighK.localProfile R θ (thetaJacquetFunctional traceFrequency)
        (LocalArchProfile.vector R θ w) w false z‖ ≤
          B * (‖z.val‖ ^ 2 : ℝ) ^ (-σ) := by
  obtain ⟨B, hB, hbound⟩ := LocalArchBounds.archDirectProfile_bound
    (4 * Real.pi) (by positivity)
    (heckeComplexWeight F w (R.A.complex_place w) θ⁻¹)
    (heckeComplexParameter F w (R.A.complex_place w) θ⁻¹) σ hσ
  refine ⟨B / ‖(besselKThird (4 * Real.pi) : ℂ)‖,
    div_nonneg hB (norm_nonneg _), ?_⟩
  intro z
  have ht : 0 < (‖z.val‖ ^ 2 : ℝ) :=
    sq_pos_of_pos (norm_pos_iff.mpr z.ne_zero)
  have hb := hbound (‖z.val‖ ^ 2) ht
  change ‖HeckeSkeleton.ThetaLocal.Project.directProfile F θ⁻¹
      ⟨w, R.A.complex_place w⟩ (4 * Real.pi) (‖z.val‖ ^ 2)‖ ≤
        B * (‖z.val‖ ^ 2 : ℝ) ^ (-σ) at hb
  rw [LocalArchProfile.direct_profile R θ w z, norm_div]
  simpa only [div_mul_eq_mul_div] using
    div_le_div_of_nonneg_right hb (norm_nonneg (besselKThird (4 * Real.pi) : ℂ))

/-- The reflected actual coefficient has the opposite radial twist and
the same positive normalizing Bessel value. -/
theorem reflected_bound (w : InfinitePlace F) (σ : ℝ) (hσ : -(1 / 3 : ℝ) < σ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z : w.Completionˣ,
      ‖FiniteLocalHighK.localProfile R θ (thetaJacquetFunctional traceFrequency)
        (LocalArchProfile.vector R θ w) w true z‖ ≤
          B * (‖z.val‖ ^ 2 : ℝ) ^ (-σ) := by
  obtain ⟨B, hB, hbound⟩ := LocalArchBounds.archReflectedProfile_bound
    (4 * Real.pi) (by positivity)
    (heckeComplexWeight F w (R.A.complex_place w) θ⁻¹)
    (heckeComplexParameter F w (R.A.complex_place w) θ⁻¹) σ hσ
  refine ⟨B / ‖(besselKThird (4 * Real.pi) : ℂ)‖,
    div_nonneg hB (norm_nonneg _), ?_⟩
  intro z
  have ht : 0 < (‖z.val‖ ^ 2 : ℝ) :=
    sq_pos_of_pos (norm_pos_iff.mpr z.ne_zero)
  have hb := hbound (‖z.val‖ ^ 2) ht
  change ‖HeckeSkeleton.ThetaLocal.Project.reflectedProfile F θ⁻¹
      ⟨w, R.A.complex_place w⟩ (4 * Real.pi) (‖z.val‖ ^ 2)‖ ≤
        B * (‖z.val‖ ^ 2 : ℝ) ^ (-σ) at hb
  rw [LocalArchProfile.reflected_profile R θ w z, norm_div]
  simpa only [div_mul_eq_mul_div] using
    div_le_div_of_nonneg_right hb (norm_nonneg (besselKThird (4 * Real.pi) : ℂ))

/-- Every existing local input field is constructed from the actual recipe,
target character and same fixed source.  No separate local input is an
argument of this constructor. -/
def input (C : FiniteFixedSource.Source R θ) : FiniteLocalHighK.Input R θ C where
  vector := LocalArchProfile.vector R θ
  functional := fun _ => thetaJacquetFunctional traceFrequency
  whittaker := fun _ => LocalArchRootCore.traceJacquet_whittaker
  functional_nonzero := LocalArchProfile.functional_nonzero R θ
  source_nonzero := fun w =>
    FiniteFixedSource.Source.archimedean_nonzero R θ C w
      (thetaJacquetFunctional traceFrequency) LocalArchRootCore.traceJacquet_whittaker
      (LocalArchProfile.vector R θ w) (LocalArchProfile.functional_nonzero R θ w)
  scale := fun _ => archScale (4 * Real.pi)
  scale_pos := fun _ => archScale_pos (4 * Real.pi) (by positivity)
  directConstant := LocalArchMellin.directConstant R θ C.transport
  directConstant_nonzero := LocalArchMellin.directConstant_nonzero R θ C.transport
  reflectedConstant := LocalArchMellin.reflectedConstant R θ C.transport
  reflectedConstant_nonzero := LocalArchMellin.reflectedConstant_nonzero R θ C.transport
  direct_integrable := fun w s hs =>
    (LocalArchMellin.direct_mellin R θ C.transport w s hs).1
  reflected_integrable := fun w s hs =>
    (LocalArchMellin.reflected_mellin R θ C.transport w s hs).1
  direct_bound := direct_bound R θ
  reflected_bound := reflected_bound R θ
  direct_mellin := fun w s hs =>
    (LocalArchMellin.direct_mellin R θ C.transport w s hs).2
  reflected_mellin := fun w s hs =>
    (LocalArchMellin.reflected_mellin R θ C.transport w s hs).2

end ThetaGlobal.LocalArchInput

#print axioms ThetaGlobal.LocalArchInput.direct_bound
#print axioms ThetaGlobal.LocalArchInput.reflected_bound
#print axioms ThetaGlobal.LocalArchInput.input
