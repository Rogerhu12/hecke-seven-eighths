import HeckeSkeleton.Moments.MOM_ENGINE_STEP.NormalizedHybridLeaves
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.NormalizedFamilyGeometry

/-!
# Raw parent geometry and fixed windows on the original finite leaves

The parent identities are stated for each original side calibration.
The engine transports them to the combined live-leaf/rectangle carrier.
Its active-label projection also preserves the exact chosen children,
so the fixed unit-ball conclusion applies to those actual output data.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Characters HeckeGeneral.Analysis.ConditionalMoments

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {H : Type} {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {ω ψ : HeckeCharacter K}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {Ray : Type*} [CommGroup Ray] [Fintype Ray] {Z : ℝ}
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
variable {heightDomain window : Set ℝ} {seminorms : Finset (ℕ × ℕ)}

namespace ActualHybridLeaf.NormalizationData

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {leaf : ActualHybridLeaf K H U E}
variable (N : leaf.NormalizationData (ι := ι) C Ray ω ψ Z
  rowDomain heightDomain window seminorms)

/-- Only the original raw nominal ledger, character and slot-count
identities are supplied. No invariant of a produced child is a field. -/
structure ParentGeometry (d : MomentData K ω ψ) (a : RealParameters) (step : ℝ) : Prop where
  left_parent : ∀ r, (N.left r).capacity.skeleton.parentWidth = a.m + a.q
  right_parent : ∀ r, (N.right r).capacity.skeleton.parentWidth = a.m + a.q
  left_gap : ∀ r, step ≤ (N.left r).capacity.gap
  right_gap : ∀ r, step ≤ (N.right r).capacity.gap
  left_kappa : ∀ r, (N.left r).calibration.parameters.κ = a.κ
  right_kappa : ∀ r, (N.right r).calibration.parameters.κ = a.κ
  left_slots : leaf.leftSlots ≤ d.geometry.slotCount
  right_slots : leaf.rightSlots ≤ d.geometry.slotCount
  left_theta : ∀ r ξ, ((N.left r).calibration.data ξ).theta = d.theta
  right_theta : ∀ r ξ, ((N.right r).calibration.data ξ).theta = d.theta

namespace ParentGeometry

variable {N} {d : MomentData K ω ψ} {a : RealParameters} {step : ℝ}

def family (raw : N.ParentGeometry d a step) :
    N.family.ParentGeometry Finset.univ d a step where
  left_parent b _ := raw.left_parent b.1
  right_parent b _ := raw.right_parent b.2
  left_gap b _ := raw.left_gap b.1
  right_gap b _ := raw.right_gap b.2
  left_kappa b _ := raw.left_kappa b.1
  right_kappa b _ := raw.right_kappa b.2
  left_slots _ _ := raw.left_slots
  right_slots _ _ := raw.right_slots
  left_theta b _ := raw.left_theta b.1
  right_theta b _ := raw.right_theta b.2

end ParentGeometry

end ActualHybridLeaf.NormalizationData

namespace ActualHybridFamily

variable {J : Type*} [Fintype J]
variable {I : J → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable (leaves : J → ActualHybridLeaf K H U E)
variable (N : ∀ j, (leaves j).NormalizationData (ι := I j)
  C Ray ω ψ Z rowDomain heightDomain window seminorms)

/-- Both Boolean source energies are nonzero on the same retained
outer label, so its original rectangle pair is active in its own family. -/
def activeRectangle (b : (normalizedFamily leaves N).active Finset.univ) :
    (N b.val.1).family.active Finset.univ :=
  ⟨b.val.2, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    (Finset.mem_filter.mp b.property).2⟩⟩

/-- Choice is made once from the same capacity theorem and the same
nonzero source. Proof irrelevance identifies the two presentations. -/
theorem leftChild_eq (b : (normalizedFamily leaves N).active Finset.univ) :
    (normalizedFamily leaves N).leftChild Finset.univ b =
      (N b.val.1).family.leftChild Finset.univ (activeRectangle leaves N b) := rfl

theorem rightChild_eq (b : (normalizedFamily leaves N).active Finset.univ) :
    (normalizedFamily leaves N).rightChild Finset.univ b =
      (N b.val.1).family.rightChild Finset.univ (activeRectangle leaves N b) := rfl

theorem leftData_eq (b : (normalizedFamily leaves N).active Finset.univ)
    (ξ : WithLp 2 (U × E)) :
    (normalizedFamily leaves N).leftData Finset.univ b ξ =
      (N b.val.1).family.leftData Finset.univ (activeRectangle leaves N b) ξ := rfl

theorem rightData_eq (b : (normalizedFamily leaves N).active Finset.univ)
    (ξ : WithLp 2 (U × E)) :
    (normalizedFamily leaves N).rightData Finset.univ b ξ =
      (N b.val.1).family.rightData Finset.univ (activeRectangle leaves N b) ξ := rfl

/-- The same fixed unit ball contains the actual data selected on the
combined carrier. Neither data nor admissibility is re-chosen per ξ. -/
theorem in_fixed_window (b : (normalizedFamily leaves N).active Finset.univ)
    (ξ : WithLp 2 (U × E)) :
    InFixedProfileWindow rowDomain Set.univ window seminorms
      ((normalizedFamily leaves N).leftData Finset.univ b ξ) ∧
    InFixedProfileWindow rowDomain Set.univ window seminorms
      ((normalizedFamily leaves N).rightData Finset.univ b ξ) := by
  rw [leftData_eq leaves N b ξ, rightData_eq leaves N b ξ]
  exact (N b.val.1).in_fixed_window (activeRectangle leaves N b) ξ

/-- These inputs precede capacity deletion. All successor width,
capacity, nonnegative plain lengths and zero-slot conclusions follow
from the concrete family geometry theorems. -/
def parentGeometry (d : MomentData K ω ψ) (a : RealParameters) (step : ℝ)
    (raw : ∀ j, (N j).ParentGeometry d a step) :
    (normalizedFamily leaves N).ParentGeometry Finset.univ d a step where
  left_parent b _ := (raw b.1).left_parent b.2.1
  right_parent b _ := (raw b.1).right_parent b.2.2
  left_gap b _ := (raw b.1).left_gap b.2.1
  right_gap b _ := (raw b.1).right_gap b.2.2
  left_kappa b _ := (raw b.1).left_kappa b.2.1
  right_kappa b _ := (raw b.1).right_kappa b.2.2
  left_slots b _ := (raw b.1).left_slots
  right_slots b _ := (raw b.1).right_slots
  left_theta b _ := (raw b.1).left_theta b.2.1
  right_theta b _ := (raw b.1).right_theta b.2.2

end ActualHybridFamily

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualHybridLeaf.NormalizationData.ParentGeometry.family
#print axioms HeckeSkeleton.Moments.EngineStep.ActualHybridFamily.leftChild_eq
#print axioms HeckeSkeleton.Moments.EngineStep.ActualHybridFamily.rightChild_eq
#print axioms HeckeSkeleton.Moments.EngineStep.ActualHybridFamily.in_fixed_window
#print axioms HeckeSkeleton.Moments.EngineStep.ActualHybridFamily.parentGeometry

