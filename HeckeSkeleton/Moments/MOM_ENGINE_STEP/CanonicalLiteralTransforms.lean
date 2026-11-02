import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralRectangles
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

set_option linter.unusedSectionVars false

/-!
# Exact individual norm factors of the two actual transforms

An inverse complete ideal norm and either Mellin norm power are products
of the corresponding factors at the two plain occurrences and every
prime occurrence. The extra positive Gauss scales are inserted by
putting their square roots into those same original profiles; their
inverse square roots then cancel exactly in the whole coefficient.

These are operations on the computed literal atom table. They neither
replace the original support nor assume a whole-column identity. The
same factors act on both complete centered rectangles, and the empty
slot product follows the same formulas.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments HeckePort.Moments.Support

variable {K : Type} [Field K] [NumberField K] {k : ℕ}

namespace CanonicalLiteralTransforms

/-- Multiplication is checked before the original atoms are summed or
centered. All original prime occurrences remain separate factors. -/
theorem bare_mul_weights (T : FixedChildCharacters K k)
    (N₁ N₂ Z : ℝ) (length : Fin k → ℝ)
    (w₁ w₂ v₁ v₂ : HeckeGeneral.Analysis.NonzeroIdeal K → ℂ)
    (w v : Fin k → HeightOneSpectrum (𝓞 K) → ℂ)
    (i : AllocationColumn K k) :
    rawBareSourceCoefficient T N₁ N₂ Z length
        (fun I => w₁ I * v₁ I) (fun I => w₂ I * v₂ I)
        (fun j p => w j p * v j p) i =
      rawBareSourceCoefficient T N₁ N₂ Z length w₁ w₂ w i *
        (v₁ (sourceMomentIdeal i.1.1) * v₂ (sourceMomentIdeal i.1.2) *
          ∏ j, v j (i.2 j)) := by
  sorry

theorem norm_power_product (i : AllocationColumn K k)
    (h₁ : i.1.1 ≠ 0) (h₂ : i.1.2 ≠ 0) (δ : ℝ) :
    ((idealNorm K (sourceMomentIdeal i.1.1) ^ δ : ℝ) : ℂ) *
        ((idealNorm K (sourceMomentIdeal i.1.2) ^ δ : ℝ) : ℂ) *
        ∏ j, (((Ideal.absNorm (i.2 j).asIdeal : ℝ) ^ δ : ℝ) : ℂ) =
      (((Ideal.absNorm (allocationColumnIdeal i) : ℝ) ^ δ : ℝ) : ℂ) := by
  sorry

/-- The extra Gauss scalar is a positive real square-root denominator,
as a complex identity, not merely an equality of norms. -/
theorem normalizer_eq_inv_sqrt (G₁ G₂ : ℝ) (G : Fin k → ℝ)
    (h₁ : 0 < G₁) (h₂ : 0 < G₂) (hG : ∀ j, 0 < G j) :
    extraGaussNormalizer G₁ G₂ G =
      (Real.sqrt (extraGaussScale G₁ G₂ G) : ℂ)⁻¹ := by
  sorry

theorem normalizer_mul (N₁ N₂ G₁ G₂ : ℝ) (N G : Fin k → ℝ)
    (hN₁ : 0 < N₁) (hN₂ : 0 < N₂) (hN : ∀ j, 0 < N j) :
    extraGaussNormalizer (N₁ * G₁) (N₂ * G₂) (fun j => N j * G j) =
      extraGaussNormalizer N₁ N₂ N * extraGaussNormalizer G₁ G₂ G := by
  sorry

theorem normalizer_cancel_roots (G₁ G₂ : ℝ) (G : Fin k → ℝ)
    (h₁ : 0 < G₁) (h₂ : 0 < G₂) (hG : ∀ j, 0 < G j) :
    extraGaussNormalizer G₁ G₂ G *
        ((Real.sqrt G₁ : ℂ) * (Real.sqrt G₂ : ℂ) * ∏ j, (Real.sqrt (G j) : ℂ)) = 1 := by
  sorry

end CanonicalLiteralTransforms

namespace CanonicalLiteralRectangles.Atoms

variable (d : CanonicalLiteralRectangles.Atoms (K := K) k)

/-- This inserts the actual additional positive Gauss scales while
preserving the complete source, by compensating each original profile
with precisely its own square root. -/
def addGauss (G₁ G₂ : ℝ) (G : Fin k → ℝ)
    (h₁ : 0 < G₁) (h₂ : 0 < G₂) (hG : ∀ j, 0 < G j) :
    CanonicalLiteralRectangles.Atoms (K := K) k :=
  { d with
    leftWeight := fun r I => d.leftWeight r I * (Real.sqrt G₁ : ℂ)
    rightWeight := fun r I => d.rightWeight r I * (Real.sqrt G₂ : ℂ)
    slotWeight := fun j p => d.slotWeight j p * (Real.sqrt (G j) : ℂ)
    gauss₁ := d.gauss₁ * G₁
    gauss₂ := d.gauss₂ * G₂
    gaussSlot := fun j => d.gaussSlot j * G j
    gauss₁_pos := mul_pos d.gauss₁_pos h₁
    gauss₂_pos := mul_pos d.gauss₂_pos h₂
    gaussSlot_pos := fun j => mul_pos (d.gaussSlot_pos j) (hG j) }

theorem addGauss_rectangleLeftWeight (G₁ G₂ : ℝ) (G : Fin k → ℝ)
    (h₁ : 0 < G₁) (h₂ : 0 < G₂) (hG : ∀ j, 0 < G j)
    (r : Bool) (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    (d.addGauss G₁ G₂ G h₁ h₂ hG).rectangleLeftWeight r I =
      d.rectangleLeftWeight r I * (Real.sqrt G₁ : ℂ) := by
  sorry

theorem addGauss_term (G₁ G₂ : ℝ) (G : Fin k → ℝ)
    (h₁ : 0 < G₁) (h₂ : 0 < G₂) (hG : ∀ j, 0 < G j)
    (r : Bool) (i : AllocationColumn K k) :
    (d.addGauss G₁ G₂ G h₁ h₂ hG).term r i = d.term r i := by
  sorry

/-- A literal Mellin factor at every original atom. Negative exponents
are permitted; all actual ideal norms are positive. -/
def normPower (δ : ℝ) : CanonicalLiteralRectangles.Atoms (K := K) k :=
  { d with
    leftWeight := fun r I => d.leftWeight r I * ((idealNorm K I ^ δ : ℝ) : ℂ)
    rightWeight := fun r I => d.rightWeight r I * ((idealNorm K I ^ δ : ℝ) : ℂ)
    slotWeight := fun j p => d.slotWeight j p * (((Ideal.absNorm p.asIdeal : ℝ) ^ δ : ℝ) : ℂ) }

theorem normPower_rectangleLeftWeight (δ : ℝ) (r : Bool)
    (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    (d.normPower δ).rectangleLeftWeight r I =
      d.rectangleLeftWeight r I * ((idealNorm K I ^ δ : ℝ) : ℂ) := by
  sorry

theorem normPower_term (δ : ℝ) (r : Bool) (i : AllocationColumn K k)
    (hi : i ∈ childCartesianColumns d.plain₁ d.plain₂ d.slots) :
    (d.normPower δ).term r i =
      d.term r i * (((Ideal.absNorm (allocationColumnIdeal i) : ℝ) ^ δ : ℝ) : ℂ) := by
  sorry

theorem normPower_whole (δ : ℝ) (i : AllocationColumn K k)
    (hi : i ∈ childCartesianColumns d.plain₁ d.plain₂ d.slots) :
    (d.normPower δ).whole i =
      d.whole i * (((Ideal.absNorm (allocationColumnIdeal i) : ℝ) ^ δ : ℝ) : ℂ) := by
  sorry

/-- These are precisely the inverse norm and the two Mellin factors
of the original two transforms. The Gauss normalization is paid once;
both actual rectangles use the same single-occurrence modifications. -/
def twoStageNorms (G₁ G₂ : ℝ) (G : Fin k → ℝ)
    (h₁ : 0 < G₁) (h₂ : 0 < G₂) (hG : ∀ j, 0 < G j)
    (δ₁ δ₂ : ℝ) : CanonicalLiteralRectangles.Atoms (K := K) k :=
  (((d.addGauss G₁ G₂ G h₁ h₂ hG).normPower (-1)).normPower δ₁).normPower δ₂

theorem twoStageNorms_term (G₁ G₂ : ℝ) (G : Fin k → ℝ)
    (h₁ : 0 < G₁) (h₂ : 0 < G₂) (hG : ∀ j, 0 < G j)
    (δ₁ δ₂ : ℝ) (r : Bool) (i : AllocationColumn K k)
    (hi : i ∈ childCartesianColumns d.plain₁ d.plain₂ d.slots) :
    (d.twoStageNorms G₁ G₂ G h₁ h₂ hG δ₁ δ₂).term r i =
      d.term r i * (((Ideal.absNorm (allocationColumnIdeal i) : ℝ) ^ δ₁ : ℝ) : ℂ) *
        (((Ideal.absNorm (allocationColumnIdeal i) : ℝ) ^ δ₂ : ℝ) : ℂ) /
        (Ideal.absNorm (allocationColumnIdeal i) : ℂ) := by
  sorry

theorem twoStageNorms_whole (G₁ G₂ : ℝ) (G : Fin k → ℝ)
    (h₁ : 0 < G₁) (h₂ : 0 < G₂) (hG : ∀ j, 0 < G j)
    (δ₁ δ₂ : ℝ) (i : AllocationColumn K k)
    (hi : i ∈ childCartesianColumns d.plain₁ d.plain₂ d.slots) :
    (d.twoStageNorms G₁ G₂ G h₁ h₂ hG δ₁ δ₂).whole i =
      d.whole i * (((Ideal.absNorm (allocationColumnIdeal i) : ℝ) ^ δ₁ : ℝ) : ℂ) *
        (((Ideal.absNorm (allocationColumnIdeal i) : ℝ) ^ δ₂ : ℝ) : ℂ) /
        (Ideal.absNorm (allocationColumnIdeal i) : ℂ) := by
  sorry

end CanonicalLiteralRectangles.Atoms
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralTransforms.normalizer_eq_inv_sqrt
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.twoStageNorms_whole
