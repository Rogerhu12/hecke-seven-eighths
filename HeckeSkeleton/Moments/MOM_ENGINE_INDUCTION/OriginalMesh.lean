import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.MellinScalarStep
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.UniversalReflectionBranches
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.RecipeRoot

/-!
# The original slot mesh through literal profile operations

Every mesh conclusion here follows from preservation of the individual
slot lengths, not from slot count or total length. The same mesh can be
included in primitive admissibility before the generic ordinary-reflection
factory constructs its child labels. It is not inferred afterwards from
an output which has forgotten the slot dictionary.

Strict outputs use the producer's original-slot dictionary separately.
These lemmas retain the parent's mesh at its same-rank Mellin input and
at the genuinely earlier ordinary-reflection children.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments MeasureTheory
open HeckeGeneral.ThetaSkeleton.Global

universe u

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}

/-- Both literal Mellin windows and all positive profile normalizers
leave each original slot length unchanged. -/
theorem normalizedMellinPlainData_fitsMesh
    (d : MomentData K ω ψ) (B₁ B₂ : SmoothAnnularTest)
    (P : ℝ) (hP : 1 ≤ P) (E : ℝ) (hE : 1 ≤ E)
    (J : ℕ) (frequency : ℝ × ℝ) (mesh : ℝ) :
    (normalizedMellinPlainData d B₁ B₂ P hP E hE J frequency).geometry.fitsMesh mesh ↔
      d.geometry.fitsMesh mesh := Iff.rfl

theorem normalizedOrdinaryPowerChild_fitsMesh
    (d : MomentData K ω ψ) (first : Bool) (sigma frequency E : ℝ)
    (hE : 1 ≤ E) (J : ℕ) (mesh : ℝ) :
    (normalizedOrdinaryPowerChild d first sigma frequency E hE J).geometry.fitsMesh mesh ↔
      d.geometry.fitsMesh mesh := Iff.rfl

theorem Node.fixedLineReflectionChild_fitsMesh
    (n : Node K ω ψ) (first : Bool) (U E : ℝ) (hE : 1 ≤ E)
    (J : ℕ) (x : (ℕ × Bool) × ℝ) (mesh : ℝ) :
    (n.fixedLineReflectionChild first U E hE J x).data.geometry.fitsMesh mesh ↔
      n.data.geometry.fitsMesh mesh := Iff.rfl

/-- Time freezing and the selected actual Mellin constants still retain
the original mesh at the canonical strict input. -/
theorem Node.mellinStrictModel_fitsMesh {Ω : Type u} [MeasurableSpace Ω]
    (n : Node K ω ψ) (cap J : ℕ) (A a b : ℝ)
    (hA : 0 ≤ A) (ha : 0 < a) (hab : a ≤ b)
    (P : ℝ) (hP : 1 ≤ P) (frequency : ℝ × ℝ) (mesh : ℝ) :
    (n.mellinStrictModel (Ω := Ω) cap J A a b hA ha hab P hP frequency).data.geometry.fitsMesh
      mesh ↔ n.data.geometry.fitsMesh mesh := Iff.rfl

/-- A primitive geometric restriction, independent of energy and of
the two plain lengths separately. -/
def withOriginalMesh (mesh : ℝ)
    (primitive : MomentData K ω ψ → PairedInvariantParameters → Prop)
    (d : MomentData K ω ψ) (p : PairedInvariantParameters) : Prop :=
  d.geometry.fitsMesh mesh ∧ primitive d p

/-- Strengthen a real node before constructing branches. -/
theorem UniversalNodeInvariant.withOriginalMesh
    {primitive : MomentData K ω ψ → PairedInvariantParameters → Prop}
    {W padding mesh : ℝ} {cap : ℕ} {n : Node K ω ψ}
    (h : UniversalNodeInvariant primitive W padding cap n)
    (hmesh : n.data.geometry.fitsMesh mesh) :
    UniversalNodeInvariant (withOriginalMesh mesh primitive) W padding cap n where
  length := h.length
  plain_left_nonneg := h.plain_left_nonneg
  plain_right_nonneg := h.plain_right_nonneg
  kappa_lower := h.kappa_lower
  kappa_upper := h.kappa_upper
  capacity := h.capacity
  width_nonneg := h.width_nonneg
  width_le := h.width_le
  slot_count := h.slot_count
  admissible := ⟨hmesh, h.admissible⟩
  centered_core := h.centered_core
  centered_left := h.centered_left
  centered_right := h.centered_right
  comparison_left := h.comparison_left
  comparison_right := h.comparison_right

/-- The generic reflection producer can construct its labels directly
in the stronger family. The extra conclusion is proved for its literal
fixed-line child, rather than required from an opaque branch output. -/
theorem ReflectionPrimitiveTransfer.withOriginalMesh
    {primitive : MomentData K ω ψ → PairedInvariantParameters → Prop}
    {sigma W padding A lower upper U E mesh : ℝ} {hE : 1 ≤ E}
    {childOrder : ℕ} {parent : Node K ω ψ}
    (hmesh : parent.data.geometry.fitsMesh mesh)
    (htransfer : ReflectionPrimitiveTransfer primitive sigma W padding A lower upper
      U E hE childOrder parent) :
    ReflectionPrimitiveTransfer (withOriginalMesh mesh primitive) sigma W padding A lower upper
      U E hE childOrder parent := by
  intro x child hunit harithmetic hearlier
  refine ⟨?_, htransfer x hunit harithmetic hearlier⟩
  exact (parent.fixedLineReflectionChild_fitsMesh
    (reflectionLongFirst parent.parameters) U E hE childOrder x mesh).2 hmesh

namespace Source

variable {c : TargetContext K}
variable (R : ExpansionRecipe.RecipeExpansion K (places K c) (targetCharacter K c)
  c.geometry (expansionShellAllowance K c))

/-- The original no-slot model fits the original mesh, or any other
mesh, without a positive-slot capacity premise. -/
theorem recipeRoot_noSlots_fitsMesh {Z T : ℝ}
    (i : SourceMomentIndexFor K c (recipeMomentSourceData K c R) Z T)
    (s : SixthUnitClasses K (places K c)) (mesh : ℝ) :
    (recipeRoot R i.noSlots s).data.geometry.fitsMesh mesh := by
  have hzero : (recipeRoot R i.noSlots s).data.geometry.slotCount = 0 := rfl
  intro j
  have hj : j.val < 0 := hzero ▸ j.isLt
  omega

end Source

end HeckeSkeleton.Moments.EngineInduction
