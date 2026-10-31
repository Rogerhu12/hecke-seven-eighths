import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.FiniteBranchMeasure
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.ReflectionBranch
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.StepOutputAdapter
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# One fixed parameter space for strict and reflected calls

A measurable embedding transports the original positive measure. A
left inverse extends every original child and numerical function to
the larger space. The extensions need not be measurable as maps into
the type of polynomial models. Their numerical integrability, integrals
and almost-everywhere geometry follow from the original ones, while
the complete mass is unchanged.

The sum injections and their explicit retractions give a fixed common
space for the engine's two frequencies and the reflection's finite
window/line label with its one frequency. The unused side has zero
measure; its child data use one original parameter value, so even the
engine's pointwise invariants and zero-twist equations remain valid.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField MeasureTheory HeckeGeneral.Characters
open HeckeGeneral.Analysis.ConditionalMoments
open scoped Classical BigOperators

universe u v w

variable {Ω : Type v} {Ω' : Type w} [MeasurableSpace Ω] [MeasurableSpace Ω']

/-- The original finite positive measure is retained by an injection. -/
theorem parameterMap_finite (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → Ω') :
    IsFiniteMeasure (μ.map f) := by infer_instance

/-- Exact total mass, with no support or branch discarded. -/
theorem parameterMap_mass (μ : Measure Ω) {f : Ω → Ω'} (hf : MeasurableEmbedding f) :
    (μ.map f).real Set.univ = μ.real Set.univ := by
  change ((μ.map f) Set.univ).toReal = (μ Set.univ).toReal
  simp only [hf.map_apply, Set.preimage_univ]

/-- Only the actual scalar function is asserted integrable. -/
theorem parameterMap_integrable (μ : Measure Ω) {f : Ω → Ω'}
    (hf : MeasurableEmbedding f) (g : Ω' → Ω) (hgf : Function.LeftInverse g f)
    (value : Ω → ℝ) (hi : Integrable value μ) :
    Integrable (fun η => value (g η)) (μ.map f) := by
  apply hf.integrable_map_iff.mpr
  simpa only [Function.comp_def, hgf] using hi

/-- Exact numerical integral transport does not require a measurable
map into the actual node family, nor a measurable extension off the image. -/
theorem parameterMap_integral (μ : Measure Ω) {f : Ω → Ω'}
    (hf : MeasurableEmbedding f) (g : Ω' → Ω) (hgf : Function.LeftInverse g f)
    (value : Ω → ℝ) :
    (∫ η, value (g η) ∂μ.map f) = ∫ ξ, value ξ ∂μ := by
  rw [hf.integral_map]
  simp only [hgf]

/-- Embedding transport also applies to arbitrary geometric predicates. -/
theorem parameterMap_ae (μ : Measure Ω) {f : Ω → Ω'}
    (hf : MeasurableEmbedding f) (g : Ω' → Ω) (hgf : Function.LeftInverse g f)
    {p : Ω → Prop} (hp : ∀ᵐ ξ ∂μ, p ξ) :
    ∀ᵐ η ∂μ.map f, p (g η) := by
  apply ae_iff.mpr
  rw [hf.map_apply]
  change μ {ξ | ¬p (g (f ξ))} = 0
  simpa only [hgf] using ae_iff.mp hp

/-- The fixed left summand has its standard measurable embedding. -/
theorem measurableEmbedding_parameterInl :
    MeasurableEmbedding (Sum.inl : Ω → Ω ⊕ Ω') :=
  ⟨Sum.inl_injective, measurable_inl, fun _ hs => hs.inl_image⟩

/-- The fixed right summand has its standard measurable embedding. -/
theorem measurableEmbedding_parameterInr :
    MeasurableEmbedding (Sum.inr : Ω' → Ω ⊕ Ω') :=
  ⟨Sum.inr_injective, measurable_inr, fun _ hs => hs.inr_image⟩

def parameterInlRetraction (original : Ω) : Ω ⊕ Ω' → Ω
  | .inl ξ => ξ
  | .inr _ => original

def parameterInrRetraction (original : Ω') : Ω ⊕ Ω' → Ω'
  | .inl _ => original
  | .inr ξ => ξ

theorem parameterInlRetraction_leftInverse (original : Ω) :
    Function.LeftInverse (parameterInlRetraction (Ω' := Ω') original) Sum.inl :=
  fun _ => rfl

theorem parameterInrRetraction_leftInverse (original : Ω') :
    Function.LeftInverse (parameterInrRetraction (Ω := Ω) original) Sum.inr :=
  fun _ => rfl

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}
variable {σ W : ℝ} {S : PolynomialSystem.{u} K ω ψ σ W}

/-- Change only the numerical parameter space of an actual outer
reflection. Its original child, remainder and measure are retained. -/
def CoreReflectionData.mapParameter {parent : S.Label} {U t padding : ℝ}
    (out : CoreReflectionData (Ω := Ω) S parent U t padding)
    (f : Ω → Ω') (hf : MeasurableEmbedding f)
    (g : Ω' → Ω) (hgf : Function.LeftInverse g f) :
    CoreReflectionData (Ω := Ω') S parent U t padding where
  kernel := out.kernel.map f
  finite_kernel := by
    letI := out.finite_kernel
    exact parameterMap_finite out.kernel f
  child η := out.child (g η)
  remainder := out.remainder
  remainder_nonneg := out.remainder_nonneg
  child_integrable := parameterMap_integrable out.kernel hf g hgf _ out.child_integrable
  child_geometry := parameterMap_ae out.kernel hf g hgf out.child_geometry
  estimate := by
    rw [hf.integral_map]
    simpa only [hgf] using out.estimate

theorem CoreReflectionData.mapParameter_mass {parent : S.Label} {U t padding : ℝ}
    (out : CoreReflectionData (Ω := Ω) S parent U t padding)
    (f : Ω → Ω') (hf : MeasurableEmbedding f)
    (g : Ω' → Ω) (hgf : Function.LeftInverse g f) :
    (out.mapParameter f hf g hgf).kernel.real Set.univ = out.kernel.real Set.univ :=
  parameterMap_mass out.kernel hf

/-- The same transport preserves the genuine reflected-comparison
length inequality and the literal source polynomial. -/
def ReflectedComparisonData.mapParameter {parent source : S.Label} {U t boundary : ℝ}
    (out : ReflectedComparisonData (Ω := Ω) S parent source U t boundary)
    (f : Ω → Ω') (hf : MeasurableEmbedding f)
    (g : Ω' → Ω) (hgf : Function.LeftInverse g f) :
    ReflectedComparisonData (Ω := Ω') S parent source U t boundary where
  kernel := out.kernel.map f
  finite_kernel := by
    letI := out.finite_kernel
    exact parameterMap_finite out.kernel f
  child η := out.child (g η)
  remainder := out.remainder
  remainder_nonneg := out.remainder_nonneg
  child_integrable := parameterMap_integrable out.kernel hf g hgf _ out.child_integrable
  child_geometry := parameterMap_ae out.kernel hf g hgf out.child_geometry
  estimate := by
    rw [hf.integral_map]
    simpa only [hgf] using out.estimate

theorem ReflectedComparisonData.mapParameter_mass {parent source : S.Label}
    {U t boundary : ℝ}
    (out : ReflectedComparisonData (Ω := Ω) S parent source U t boundary)
    (f : Ω → Ω') (hf : MeasurableEmbedding f)
    (g : Ω' → Ω) (hgf : Function.LeftInverse g f) :
    (out.mapParameter f hf g hgf).kernel.real Set.univ = out.kernel.real Set.univ :=
  parameterMap_mass out.kernel hf

end HeckeSkeleton.Moments.EngineInduction

namespace HeckeSkeleton.Moments.EngineStep.PairedEngineConclusion

open NumberField MeasureTheory HeckeGeneral.Characters
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeSkeleton.Moments.EngineInduction
open scoped Classical BigOperators

universe v w

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}
variable {Ω : Type v} {Ω' : Type w} [MeasurableSpace Ω] [MeasurableSpace Ω']
variable {centered : Bool} {d : MomentData K ω ψ} {a : RealParameters}
variable {Z t Y₁ Y₂ σ ε terminalExponent C control : ℝ}
variable {admissible : MomentData K ω ψ → RealParameters → Prop}

/-- Transport the canonical complete engine output. The actual child
data and all pointwise arithmetic invariants are evaluated at the
retraction. The provider's zero-twist equations remain literal, and
every branch has exactly its original positive mass. -/
def mapParameter
    (out : PairedEngineConclusion (Ω := Ω) centered d a
      Z t Y₁ Y₂ σ ε terminalExponent C control admissible)
    (f : Ω → Ω') (hf : MeasurableEmbedding f)
    (g : Ω' → Ω) (hgf : Function.LeftInverse g f) :
    PairedEngineConclusion (Ω := Ω') centered d a
      Z t Y₁ Y₂ σ ε terminalExponent C control admissible where
  branches := out.branches
  leftData b η := out.leftData b (g η)
  rightData b η := out.rightData b (g η)
  leftParameters := out.leftParameters
  rightParameters := out.rightParameters
  leftTwist b η := out.leftTwist b (g η)
  rightTwist b η := out.rightTwist b (g η)
  leftTwist_zero b η := out.leftTwist_zero b (g η)
  rightTwist_zero b η := out.rightTwist_zero b (g η)
  kernel b := (out.kernel b).map f
  finite_kernel b := by
    letI := out.finite_kernel b
    exact parameterMap_finite (out.kernel b) f
  left_width := out.left_width
  right_width := out.right_width
  left_width_nonneg := out.left_width_nonneg
  right_width_nonneg := out.right_width_nonneg
  left_plain_left_nonneg := out.left_plain_left_nonneg
  left_plain_right_nonneg := out.left_plain_right_nonneg
  right_plain_left_nonneg := out.right_plain_left_nonneg
  right_plain_right_nonneg := out.right_plain_right_nonneg
  left_length b η := out.left_length b (g η)
  right_length b η := out.right_length b (g η)
  left_kappa := out.left_kappa
  right_kappa := out.right_kappa
  left_slots b η := out.left_slots b (g η)
  right_slots b η := out.right_slots b (g η)
  left_theta b η := out.left_theta b (g η)
  right_theta b η := out.right_theta b (g η)
  left_slot_characters b η i := out.left_slot_characters b (g η) i
  right_slot_characters b η i := out.right_slot_characters b (g η) i
  left_admissible b η := out.left_admissible b (g η)
  right_admissible b η := out.right_admissible b (g η)
  left_capacity := out.left_capacity
  right_capacity := out.right_capacity
  firstZero := out.firstZero
  secondZero := out.secondZero
  exceptional := out.exceptional
  tail := out.tail
  firstZero_nonneg := out.firstZero_nonneg
  secondZero_nonneg := out.secondZero_nonneg
  exceptional_nonneg := out.exceptional_nonneg
  tail_nonneg := out.tail_nonneg
  terminals := out.terminals
  left_integrable b := parameterMap_integrable (out.kernel b) hf g hgf _ (out.left_integrable b)
  right_integrable b := parameterMap_integrable (out.kernel b) hf g hgf _ (out.right_integrable b)
  cauchy_integrable b := parameterMap_integrable (out.kernel b) hf g hgf _ (out.cauchy_integrable b)
  parent := by
    have he (b : Fin out.branches) := parameterMap_integral (out.kernel b) hf g hgf
      (fun ξ => Real.sqrt (normalizedPairedEnergy (out.leftData b ξ) (out.leftParameters b)
          Z (out.leftTwist b ξ)) *
        Real.sqrt (normalizedPairedEnergy (out.rightData b ξ) (out.rightParameters b)
          Z (out.rightTwist b ξ)))
    simpa only [he] using out.parent
  mass := by
    have he (b : Fin out.branches) := parameterMap_mass (out.kernel b) hf
    simpa only [he] using out.mass

theorem mapParameter_mass
    (out : PairedEngineConclusion (Ω := Ω) centered d a
      Z t Y₁ Y₂ σ ε terminalExponent C control admissible)
    (f : Ω → Ω') (hf : MeasurableEmbedding f)
    (g : Ω' → Ω) (hgf : Function.LeftInverse g f) :
    (∑ b, ((out.mapParameter f hf g hgf).kernel b).real Set.univ) =
      ∑ b, (out.kernel b).real Set.univ := by
  change (∑ b, ((out.kernel b).map f).real Set.univ) = _
  apply Finset.sum_congr rfl
  intro b _hb
  exact parameterMap_mass (out.kernel b) hf

end HeckeSkeleton.Moments.EngineStep.PairedEngineConclusion
