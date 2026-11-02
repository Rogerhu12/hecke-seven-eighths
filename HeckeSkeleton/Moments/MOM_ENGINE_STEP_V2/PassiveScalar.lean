import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.PassiveSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondCoefficientBinding

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Extracting a specified original scalar without division

A common scalar stored in the first plain factor can be moved to the
outer normalization by an exact algebraic identity. The unscaled plain
weight is given by its original formula, never by dividing the old
profile. The result covers zero scalars and leaves every frozen scalar,
row weight and original arithmetic extraction unchanged.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.PassiveSource

open EngineStep NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]
variable {A : DedekindZetaZeroFree.SArithmeticData K} {σ : K →+* ℂ} {H : Type*} {k : ℕ}

theorem rawSourceCoefficient_left_scalar
    (T : FixedChildCharacters K k) (g h' : A.R) (N₁ N₂ Z : ℝ)
    (length : Fin k → ℝ) (w₁ w₂ : NonzeroIdeal K → ℂ)
    (w : Fin k → HeightOneSpectrum (𝓞 K) → ℂ)
    (z : ℂ) (i : AllocationColumn K k) :
    rawSourceCoefficient (σ := σ) T g h' N₁ N₂ Z length
      (fun I => z * w₁ I) w₂ w i =
      z * rawSourceCoefficient (σ := σ) T g h' N₁ N₂ Z length w₁ w₂ w i := by
  simp only [rawSourceCoefficient, FixedChildCharacters.coefficient,
    childCartesianCoefficient, sourcePlainTerm]
  ring

variable (s : ActualAllocatedSource A EngineParameter H k)

def withLeftWeight (weight : H → NonzeroIdeal K → ℂ) :
    ActualAllocatedSource A EngineParameter H k :=
  { s with leftWeight := weight }

def scaleLeft (z : ℂ) : ActualAllocatedSource A EngineParameter H k :=
  withLeftWeight s (fun h I => z * s.leftWeight h I)

@[simp] theorem withLeftWeight_frozenScalar (weight : H → NonzeroIdeal K → ℂ) (h : H) :
    (withLeftWeight s weight).frozenScalar (σ := σ) h = s.frozenScalar (σ := σ) h := rfl

@[simp] theorem withLeftWeight_childWeight (weight : H → NonzeroIdeal K → ℂ) (h : H) :
    (withLeftWeight s weight).childWeight (σ := σ) h = s.childWeight (σ := σ) h := rfl

@[simp] theorem scaleLeft_frozenScalar (z : ℂ) (h : H) :
    (scaleLeft s z).frozenScalar (σ := σ) h = s.frozenScalar (σ := σ) h := rfl

@[simp] theorem scaleLeft_childWeight (z : ℂ) (h : H) :
    (scaleLeft s z).childWeight (σ := σ) h = s.childWeight (σ := σ) h := rfl

/-- Exact energy scaling, including the zero scalar. -/
theorem scaleLeft_energy (z : ℂ) (ξ : EngineParameter) :
    (scaleLeft s z).energy (σ := σ) ξ = ‖z‖ ^ 2 * s.energy (σ := σ) ξ := by
  simp only [ActualAllocatedSource.energy, scaleLeft, withLeftWeight]
  change jointColumnEnergy s.rows s.allocation.columns s.weight
    (fun h i => rawSourceCoefficient (σ := σ) (s.characters h)
      (s.extractedFactor h) (s.row h).element s.scale₁ s.scale₂ s.base s.length
      (fun I => z * s.leftWeight h I) (s.rightWeight h) (s.slotWeight h) i)
    (fun h => rawSourceLocation (s.leftLocation h) (s.rightLocation h) (s.slotLocation h)) ξ = _
  simp only [rawSourceCoefficient_left_scalar]
  exact joint_energy_constant_coefficient s.rows s.allocation.columns s.weight
    (fun h => rawSourceCoefficient (σ := σ) (s.characters h)
      (s.extractedFactor h) (s.row h).element s.scale₁ s.scale₂ s.base s.length
      (s.leftWeight h) (s.rightWeight h) (s.slotWeight h))
    (fun h => rawSourceLocation (s.leftLocation h) (s.rightLocation h) (s.slotLocation h)) z ξ

/-- The caller supplies the original unscaled formula and its literal
pointwise factorization. No nonvanishing or reciprocal is required. -/
theorem energy_of_leftWeight_eq (weight : H → NonzeroIdeal K → ℂ) (z : ℂ)
    (hweight : ∀ h I, s.leftWeight h I = z * weight h I) (ξ : EngineParameter) :
    s.energy (σ := σ) ξ = ‖z‖ ^ 2 * (withLeftWeight s weight).energy (σ := σ) ξ := by
  have he : s.leftWeight = fun h I => z * weight h I :=
    funext fun h => funext fun I => hweight h I
  calc
    _ = (scaleLeft (withLeftWeight s weight) z).energy (σ := σ) ξ := by
      simp only [ActualAllocatedSource.energy, scaleLeft, withLeftWeight]
      rw [he]
    _ = _ := scaleLeft_energy (withLeftWeight s weight) z ξ

/-- Combining the fixed old normalizer with the prescribed complex
scalar is an equality of numerical factors, not a normalization choice. -/
theorem normalized_energy_of_leftWeight_eq
    (weight : H → NonzeroIdeal K → ℂ) (z normalizer : ℂ)
    (hweight : ∀ h I, s.leftWeight h I = z * weight h I) (ξ : EngineParameter) :
    ‖normalizer‖ ^ 2 * s.energy (σ := σ) ξ =
      ‖normalizer * z‖ ^ 2 * (withLeftWeight s weight).energy (σ := σ) ξ := by
  rw [energy_of_leftWeight_eq s weight z hweight, norm_mul, mul_pow]
  ring

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.PassiveSource

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.PassiveSource.energy_of_leftWeight_eq
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.PassiveSource.normalized_energy_of_leftWeight_eq
