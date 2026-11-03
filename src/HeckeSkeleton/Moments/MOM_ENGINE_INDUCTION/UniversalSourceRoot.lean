import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.UniversalNodeFamily
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.RecipeRoot

/-!
# The literal recipe roots in the actual universal polynomial family

The same source index and sector give the subtype's ordinary root.
The numerical facts come from the original recipe geometry and capacity;
there is no polynomial replacement or energy-equality premise. The
zero-slot projection has unrestricted plain lengths, just as in the
original target. A uniform slot-length cap follows from the actual
capacity and nonnegative plain lengths at every legal node.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open scoped Classical BigOperators

universe u

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}

theorem UniversalNodeInvariant.slot_length_le_width
    {primitive : MomentData K ω ψ → PairedInvariantParameters → Prop}
    {W padding : ℝ} {cap : ℕ} {n : Node K ω ψ}
    (h : UniversalNodeInvariant primitive W padding cap n) :
    n.data.geometry.totalLength ≤ n.width := by
  rw [← h.length]
  rcases h.capacity with hzero | hcap
  · rw [hzero]
    exact h.width_nonneg
  · have hz := n.slot_nonneg h.length
    have hk : 1 ≤ 6 * n.parameters.κ := by linarith [h.kappa_lower]
    have hslot : n.parameters.z ≤ 6 * n.parameters.κ * n.parameters.z := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hk hz
    linarith [h.plain_left_nonneg, h.plain_right_nonneg]

theorem UniversalNodeInvariant.slot_length_le_bound
    {primitive : MomentData K ω ψ → PairedInvariantParameters → Prop}
    {W padding : ℝ} {cap : ℕ} {n : Node K ω ψ}
    (h : UniversalNodeInvariant primitive W padding cap n) :
    n.data.geometry.totalLength ≤ W := h.slot_length_le_width.trans h.width_le

namespace Source

variable {c : TargetContext K}
variable (R : ExpansionRecipe.RecipeExpansion K (places K c) (targetCharacter K c)
  c.geometry (expansionShellAllowance K c))
variable {Z T : ℝ}
variable (i : SourceMomentIndexFor K c (recipeMomentSourceData K c R) Z T)
variable (s : SixthUnitClasses K (places K c))

/-- The original ordinary root's numerical invariants, including its
actual width and slot cap. Primitive admissibility is proved separately
from the source data and actual profile controls. -/
def recipeUniversalRoot
    (primitive : MomentData K c.family.omega (targetCharacter K c) →
      PairedInvariantParameters → Prop) (padding : ℝ) {lengthBound : ℝ}
    (hgeom : R.MomentGeometry lengthBound)
    (hcapacity : (recipeRoot R i s).parameters.z = 0 ∨ pairedCapacityFor i)
    (hadmissible : admissibleOfInvariant primitive
      (recipeRoot R i s).data (recipeRoot R i s).parameters) :
    UniversalNode primitive 2 padding c.geometry.slots := by
  have hplain := recipeRoot_plain_lengths R i s hgeom
  have hwidth := recipeRoot_width_range R i s
  have hkappa := recipeRoot_kappa R i s
  refine UniversalNode.ordinary primitive 2 padding c.geometry.slots
    (recipeRoot R i s).data (recipeRoot R i s).parameters
    (recipeRoot_length R i s) hplain.1 hplain.2.2.1 hkappa.1.le hkappa.2 ?_
    (zero_lt_one.trans hwidth.1).le hwidth.2 (recipeRoot_slotCount_le R i s) hadmissible
  rcases hcapacity with hzero | hpositive
  · exact Or.inl hzero
  · exact Or.inr (recipeRoot_capacity R i s hpositive)

/-- Subtype construction leaves the entire original node unchanged. -/
theorem recipeUniversalRoot_eq
    (primitive : MomentData K c.family.omega (targetCharacter K c) →
      PairedInvariantParameters → Prop) (padding : ℝ) {lengthBound : ℝ}
    (hgeom : R.MomentGeometry lengthBound)
    (hcapacity : (recipeRoot R i s).parameters.z = 0 ∨ pairedCapacityFor i)
    (hadmissible : admissibleOfInvariant primitive
      (recipeRoot R i s).data (recipeRoot R i s).parameters) :
    (recipeUniversalRoot R i s primitive padding hgeom hcapacity hadmissible).val =
      recipeRoot R i s := rfl

/-- Exact label in the common system used by the finite-rank induction. -/
def recipeUniversalRootLabel
    (primitive : MomentData K c.family.omega (targetCharacter K c) →
      PairedInvariantParameters → Prop) (σ padding : ℝ) (hσ : 0 < σ)
    {lengthBound : ℝ} (hgeom : R.MomentGeometry lengthBound)
    (hcapacity : (recipeRoot R i s).parameters.z = 0 ∨ pairedCapacityFor i)
    (hadmissible : admissibleOfInvariant primitive
      (recipeRoot R i s).data (recipeRoot R i s).parameters) :
    (universalPolynomialSystem.{u} primitive σ 2 padding c.geometry.slots hσ).Label :=
  ⟨recipeUniversalRoot R i s primitive padding hgeom hcapacity hadmissible⟩

theorem recipeUniversalRootLabel_eq
    (primitive : MomentData K c.family.omega (targetCharacter K c) →
      PairedInvariantParameters → Prop) (σ padding : ℝ) (hσ : 0 < σ)
    {lengthBound : ℝ} (hgeom : R.MomentGeometry lengthBound)
    (hcapacity : (recipeRoot R i s).parameters.z = 0 ∨ pairedCapacityFor i)
    (hadmissible : admissibleOfInvariant primitive
      (recipeRoot R i s).data (recipeRoot R i s).parameters) :
    (universalPolynomialSystem.{u} primitive σ 2 padding c.geometry.slots hσ).node
      (recipeUniversalRootLabel R i s primitive σ padding hσ hgeom hcapacity hadmissible) =
      recipeRoot R i s := rfl

/-- The unrestricted no-slot root needs no positive-slot capacity. -/
theorem recipeRoot_noSlots_zero : (recipeRoot R i.noSlots s).parameters.z = 0 := by
  change selectedLengthFor i.noSlots = 0
  simp only [selectedLengthFor, HeckeSkeleton.SourceMomentIndexFor.noSlots, Finset.sum_empty]

end Source

end HeckeSkeleton.Moments.EngineInduction
