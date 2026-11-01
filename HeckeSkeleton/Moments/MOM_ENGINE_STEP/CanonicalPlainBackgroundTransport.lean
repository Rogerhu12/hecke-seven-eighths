import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPassiveInheritance
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.NormalizedFamilyBase
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DependentNormalizedFamily
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.PairedEngineAdmissibilityTransport

/-!
# Exact background transport on the existing engine output

The raw calibration background is read through the same selected capacity
children, the original sigma family, its existing finite enumeration and
admissibility-only refinements. The next background condition follows from
this exact field identity and the output's existing theta equality.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical NumberField

namespace HeckeSkeleton.Moments.EngineStep.CanonicalPlainBackgroundTransport

open NumberField DedekindZetaZeroFree
open HeckeGeneral.Characters HeckeGeneral.Analysis.ConditionalMoments

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ} {ω ψ : HeckeCharacter K}
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- A property of the stored raw calibration, before capacity selection. -/
def Raw {Λ : Type*} {Z : ℝ}
    (family : ActualNormalizedPairFamily A σ V Λ ω ψ Z)
    (parent : MomentData K ω ψ) : Prop :=
  ∀ b z,
    ((family.leftCalibration b).data z).plainBackground = parent.plainBackground ∧
    ((family.rightCalibration b).data z).plainBackground = parent.plainBackground

/-- The same two selected children, using the existing frozen-field theorem. -/
theorem selected {Λ : Type*} {Z : ℝ}
    (family : ActualNormalizedPairFamily A σ V Λ ω ψ Z)
    (labels : Finset Λ) (parent : MomentData K ω ψ) (hraw : Raw family parent)
    (b : family.active labels) (z : V) :
    (family.leftData labels b z).plainBackground = parent.plainBackground ∧
    (family.rightData labels b z).plainBackground = parent.plainBackground := by
  constructor
  · exact ((family.leftChild labels b).frozen_plainBackground_eq z).trans
      (hraw b.val z).1
  · exact ((family.rightChild labels b).frozen_plainBackground_eq z).trans
      (hraw b.val z).2

theorem atBase {Λ : Type*} {Z : ℝ}
    (family : ActualNormalizedPairFamily A σ V Λ ω ψ Z)
    (parent : MomentData K ω ψ) (hraw : Raw family parent)
    (base : ℝ) (sameBase : Z = base) :
    Raw (family.atBase base sameBase) parent := hraw

/-- The raw calibration of the sigma family is the original component's. -/
theorem sigmaCombine {J : Type*} {Λ : J → Type*} {Z : ℝ}
    (families : ∀ j, ActualNormalizedPairFamily A σ V (Λ j) ω ψ Z)
    (parent : MomentData K ω ψ) (hraw : ∀ j, Raw (families j) parent) :
    Raw (ActualNormalizedPairFamily.sigmaCombine families) parent :=
  fun b z => hraw b.1 b.2 z

/-- Read the same actual finite family after its existing Fin enumeration. -/
theorem selectedFin {Λ : Type*} [Fintype Λ] {Z : ℝ}
    (family : ActualNormalizedPairFamily A σ V Λ ω ψ Z)
    (parent : MomentData K ω ψ) (hraw : Raw family parent)
    (i : Fin (Fintype.card (family.active Finset.univ))) (z : V) :
    (family.leftData Finset.univ
      ((Fintype.equivFin (family.active Finset.univ)).symm i) z).plainBackground =
        parent.plainBackground ∧
    (family.rightData Finset.univ
      ((Fintype.equivFin (family.active Finset.univ)).symm i) z).plainBackground =
        parent.plainBackground :=
  selected family Finset.univ parent hraw
    ((Fintype.equivFin (family.active Finset.univ)).symm i) z

theorem next_background {parent child : MomentData K ω ψ}
    (hbackground : child.plainBackground = parent.plainBackground)
    (htheta : child.theta = parent.theta)
    (hparent : parent.plainBackground⁻¹ ∈ parent.theta ∨
      ¬ FiniteOrder parent.plainBackground) :
    child.plainBackground⁻¹ ∈ child.theta ∨ ¬ FiniteOrder child.plainBackground := by
  simpa only [hbackground, htheta] using hparent

end HeckeSkeleton.Moments.EngineStep.CanonicalPlainBackgroundTransport

namespace HeckeSkeleton.Moments.EngineStep.PairedEngineConclusion

open NumberField MeasureTheory
open HeckeGeneral.Characters HeckeGeneral.Analysis.ConditionalMoments

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}
variable {Ω : Type*} [MeasurableSpace Ω]
variable {centered : Bool} {d : MomentData K ω ψ} {a : RealParameters}
variable {Z t Y₁ Y₂ step ε terminalExponent C control : ℝ}
variable {admissible : MomentData K ω ψ → RealParameters → Prop}
variable (out : PairedEngineConclusion (Ω := Ω) centered d a
  Z t Y₁ Y₂ step ε terminalExponent C control admissible)

/-- A companion of the existing output, not a replacement output. -/
def SamePlainBackground : Prop :=
  ∀ (b : Fin out.branches) (z : Ω),
    (out.leftData b z).plainBackground = d.plainBackground ∧
      (out.rightData b z).plainBackground = d.plainBackground

theorem samePlainBackground_of_zero_branches (hzero : out.branches = 0) :
    out.SamePlainBackground := by
  intro b z
  exact Fin.elim0 (Fin.cast hzero b)

/-- Exact arithmetic fields plus the already public theta identity suffice. -/
theorem next_background_of_samePlainBackground
    (h : out.SamePlainBackground)
    (hparent : d.plainBackground⁻¹ ∈ d.theta ∨ ¬ FiniteOrder d.plainBackground)
    (b : Fin out.branches) (z : Ω) :
    ((out.leftData b z).plainBackground⁻¹ ∈ (out.leftData b z).theta ∨
      ¬ FiniteOrder (out.leftData b z).plainBackground) ∧
    ((out.rightData b z).plainBackground⁻¹ ∈ (out.rightData b z).theta ∨
      ¬ FiniteOrder (out.rightData b z).plainBackground) := by
  constructor
  · exact CanonicalPlainBackgroundTransport.next_background
      (h b z).1 (out.left_theta b z) hparent
  · exact CanonicalPlainBackgroundTransport.next_background
      (h b z).2 (out.right_theta b z) hparent

/-- Refining proofs does not alter either background field. -/
theorem samePlainBackground_withAdmissible
    (target : MomentData K ω ψ → RealParameters → Prop)
    (hleft : ∀ b z, target (out.leftData b z) (out.leftParameters b))
    (hright : ∀ b z, target (out.rightData b z) (out.rightParameters b))
    (h : out.SamePlainBackground) :
    (out.withAdmissible target hleft hright).SamePlainBackground := h

end HeckeSkeleton.Moments.EngineStep.PairedEngineConclusion
