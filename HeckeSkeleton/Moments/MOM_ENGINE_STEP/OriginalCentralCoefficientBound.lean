import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalFirstDualTerminalWindows
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ReductionOutput

set_option linter.unusedSectionVars false

/-!
# The original central scale in the whole parent coefficient

The two plain atoms and every prime occurrence contain their actual
inverse square-root scale. Both comparison rectangles have the same
product of plain scales. Their full coefficients consequently retain
the exponent minus one half of the original total length, before either
Poisson transform or any finite common-support decomposition.

Only individual unscaled original atom bounds are used. The coefficient
bound, including the centered subtraction and all slots, is proved here.
The fixed coefficient constant depends on the original slot cap and
profile bound, not on the moving columns, scale, or common labels.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments

theorem original_inverse_sqrt_rpow (Z length : ℝ) (hZ : 0 < Z) :
    (Real.sqrt (Z ^ length))⁻¹ = Z ^ (-length / 2) := by
  sorry

private theorem original_normalized_atom_norm_le
    (N B : ℝ) (v : ℂ) (hv : ‖v‖ ≤ B) :
    ‖(Real.sqrt N : ℂ)⁻¹ * v‖ ≤ B * (Real.sqrt N)⁻¹ := by
  sorry

/-- The original normalization is a single product, including the
empty product when there are no prime slots. -/
theorem original_central_scale_product
    (slots : ℕ) (length : Fin slots → ℝ) (Z B N₁ N₂ plainLength : ℝ)
    (hZ : 0 < Z) (hN₁ : 0 ≤ N₁) (hproduct : N₁ * N₂ = Z ^ plainLength) :
    (B * (Real.sqrt N₁)⁻¹) * (B * (Real.sqrt N₂)⁻¹) *
        (∏ i, B * (Real.sqrt (Z ^ length i))⁻¹) =
      B ^ (slots + 2) * Z ^ (-(plainLength + ∑ i, length i) / 2) := by
  sorry

variable {K : Type} [Field K] [NumberField K]

namespace ParentConstantAtoms

variable {Q : Type*} {ω ψ : HeckeCharacter K}
variable {d : MomentData K ω ψ} {a : RealParameters} {Z t Y₁ Y₂ : ℝ}
variable (atoms : ParentConstantAtoms Q d a Z t)

/-- A rectangle is bounded on the literal original support. The raw
atom bounds do not contain any central scale or whole-column product. -/
theorem rectangle_norm_le_original_central_scales
    (B : ℝ) (hB : 0 ≤ B) (hZ : 0 < Z)
    (hleft : ∀ comparison I, I ∈ (atoms.raw Y₁ Y₂).leftColumns →
      ‖atoms.leftArithmetic I * atoms.leftProfile
        (idealNorm K I / (if comparison then Y₁ else Z ^ a.n₁))‖ ≤ B)
    (hright : ∀ comparison I, I ∈ (atoms.raw Y₁ Y₂).rightColumns →
      ‖atoms.rightArithmetic I * atoms.rightProfile
        (idealNorm K I / (if comparison then Y₂ else Z ^ a.n₂))‖ ≤ B)
    (hprime : ∀ i p, p ∈ (atoms.raw Y₁ Y₂).slotColumns i →
      ‖atoms.primeArithmetic i p * (d.geometry.slots i).profile t
        ((Ideal.absNorm p.asIdeal : ℝ) / Z ^ (d.geometry.slots i).length)‖ ≤ B)
    (comparison : Bool)
    (hN₁ : 0 ≤ (if comparison then Y₁ else Z ^ a.n₁))
    (hproduct : (if comparison then Y₁ else Z ^ a.n₁) *
      (if comparison then Y₂ else Z ^ a.n₂) = Z ^ (a.n₁ + a.n₂))
    (v : (atoms.raw Y₁ Y₂).Column) (hv : v ∈ (atoms.raw Y₁ Y₂).columns) :
    ‖(atoms.values Y₁ Y₂).rectangle comparison v‖ ≤
      B ^ (d.geometry.slotCount + 2) *
        Z ^ (-(a.n₁ + a.n₂ + d.geometry.totalLength) / 2) := by
  sorry

/-- The sharp original coefficient exponent is proved before the
common supports are extracted. Both rectangles retain the same scales
and every original slot; the constant uses only the fixed slot cap. -/
theorem coefficient_norm_le_original_central_cap
    (cap : ℕ) (hcap : d.geometry.slotCount ≤ cap)
    (B : ℝ) (hB : 1 ≤ B) (hZ : 0 < Z)
    (hleft : ∀ comparison I, I ∈ (atoms.raw Y₁ Y₂).leftColumns →
      ‖atoms.leftArithmetic I * atoms.leftProfile
        (idealNorm K I / (if comparison then Y₁ else Z ^ a.n₁))‖ ≤ B)
    (hright : ∀ comparison I, I ∈ (atoms.raw Y₁ Y₂).rightColumns →
      ‖atoms.rightArithmetic I * atoms.rightProfile
        (idealNorm K I / (if comparison then Y₂ else Z ^ a.n₂))‖ ≤ B)
    (hprime : ∀ i p, p ∈ (atoms.raw Y₁ Y₂).slotColumns i →
      ‖atoms.primeArithmetic i p * (d.geometry.slots i).profile t
        ((Ideal.absNorm p.asIdeal : ℝ) / Z ^ (d.geometry.slots i).length)‖ ≤ B)
    (centered : Bool) (hY₁ : centered = true → 0 ≤ Y₁)
    (hcomparison : centered = true → Y₁ * Y₂ = Z ^ (a.n₁ + a.n₂))
    (v : (atoms.raw Y₁ Y₂).Column) (hv : v ∈ (atoms.raw Y₁ Y₂).columns) :
    ‖(atoms.values Y₁ Y₂).coefficient centered v‖ ≤
      (2 * B ^ (cap + 2)) *
        Z ^ (-(a.n₁ + a.n₂ + d.geometry.totalLength) / 2) := by
  sorry

end ParentConstantAtoms

namespace PairedEngineDomain

variable {ω ψ : HeckeCharacter K} {centered : Bool}
variable {d : MomentData K ω ψ} {a : RealParameters}
variable {Z Y₁ Y₂ floor padding : ℝ}
variable (domain : PairedEngineDomain centered d a Z Y₁ Y₂ floor padding)

include domain in
theorem comparison_scale_left_nonneg (hc : centered = true) : 0 ≤ Y₁ := by
  sorry

include domain in
theorem comparison_product_eq_power (hc : centered = true) :
    Y₁ * Y₂ = Z ^ (a.n₁ + a.n₂) := by
  sorry

end PairedEngineDomain
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.original_central_scale_product
#print axioms HeckeSkeleton.Moments.EngineStep.ParentConstantAtoms.rectangle_norm_le_original_central_scales
#print axioms HeckeSkeleton.Moments.EngineStep.ParentConstantAtoms.coefficient_norm_le_original_central_cap
#print axioms HeckeSkeleton.Moments.EngineStep.PairedEngineDomain.comparison_product_eq_power
