import HeckeSkeleton.Moments.MOM_ENGINE_STEP.JointNormalizedLeaves
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.NormalizedFamilyAtoms

/-!
# Output conditions of the same actual normalized child family

The constructors in this file prove the geometry, actual profile/mask
admissibility and numerical integrability fields used by the final
finite output. They start from the original per-side dictionaries and
individual atom controls. There is no parent inequality, total mass or
terminal estimate among their inputs.

The public child data are the retained, normalized profiles with their
actual evaluation height frozen into them. All output energies below
are evaluated at twist zero under the same original Fourier measure.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree MeasureTheory
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ} {ω ψ : HeckeCharacter K}

namespace ActualNormalizedPairFamily

section Geometry

variable {V Λ : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {Z : ℝ}
variable (family : ActualNormalizedPairFamily A σ V Λ ω ψ Z) (labels : Finset Λ)

/-- The actual public left data are already normalized and frozen.
The retained source and deletion are those chosen by this same family. -/
theorem leftData_eq_frozen_normalized (b : family.active labels) (ξ : V) :
    family.leftData labels b ξ =
      frozenMomentProfiles
        (normalizedMomentProfiles ((family.leftChild labels b).rawData ξ)
          ((family.leftCapacity b.val).radius ξ) ((family.leftCapacity b.val).radius_pos ξ))
        ((family.leftCalibration b.val).height ξ) := by
  change frozenMomentProfiles ((family.leftChild labels b).data ξ)
    ((family.leftCalibration b.val).height ξ) = _
  rw [(family.leftChild labels b).data_eq_normalized_raw]

theorem rightData_eq_frozen_normalized (b : family.active labels) (ξ : V) :
    family.rightData labels b ξ =
      frozenMomentProfiles
        (normalizedMomentProfiles ((family.rightChild labels b).rawData ξ)
          ((family.rightCapacity b.val).radius ξ) ((family.rightCapacity b.val).radius_pos ξ))
        ((family.rightCalibration b.val).height ξ) := by
  change frozenMomentProfiles ((family.rightChild labels b).data ξ)
    ((family.rightCalibration b.val).height ξ) = _
  rw [(family.rightChild labels b).data_eq_normalized_raw]

/-- These are output facts of the constructed active family, not an
additional source calibration. They contain no aggregate estimate. -/
structure OutputGeometry (d : MomentData K ω ψ) (a : RealParameters) (step : ℝ)
    (rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)) (window : Set ℝ)
    (seminorms : Finset (ℕ × ℕ)) : Prop where
  left_width : ∀ b : family.active labels,
    (family.leftParameters labels b).m + (family.leftParameters labels b).q ≤
      a.m + a.q - step / 2
  right_width : ∀ b : family.active labels,
    (family.rightParameters labels b).m + (family.rightParameters labels b).q ≤
      a.m + a.q - step / 2
  left_width_nonneg : ∀ b : family.active labels,
    0 ≤ (family.leftParameters labels b).m + (family.leftParameters labels b).q
  right_width_nonneg : ∀ b : family.active labels,
    0 ≤ (family.rightParameters labels b).m + (family.rightParameters labels b).q
  left_plain_left_nonneg : ∀ b : family.active labels, 0 ≤ (family.leftParameters labels b).n₁
  left_plain_right_nonneg : ∀ b : family.active labels, 0 ≤ (family.leftParameters labels b).n₂
  right_plain_left_nonneg : ∀ b : family.active labels, 0 ≤ (family.rightParameters labels b).n₁
  right_plain_right_nonneg : ∀ b : family.active labels, 0 ≤ (family.rightParameters labels b).n₂
  left_length : ∀ b : family.active labels, ∀ ξ,
    (family.leftParameters labels b).z = (family.leftData labels b ξ).geometry.totalLength
  right_length : ∀ b : family.active labels, ∀ ξ,
    (family.rightParameters labels b).z = (family.rightData labels b ξ).geometry.totalLength
  left_kappa : ∀ b : family.active labels, (family.leftParameters labels b).κ = a.κ
  right_kappa : ∀ b : family.active labels, (family.rightParameters labels b).κ = a.κ
  left_slots : ∀ b : family.active labels, ∀ ξ,
    (family.leftData labels b ξ).geometry.slotCount ≤ d.geometry.slotCount
  right_slots : ∀ b : family.active labels, ∀ ξ,
    (family.rightData labels b ξ).geometry.slotCount ≤ d.geometry.slotCount
  left_theta : ∀ b : family.active labels, ∀ ξ, (family.leftData labels b ξ).theta = d.theta
  right_theta : ∀ b : family.active labels, ∀ ξ, (family.rightData labels b ξ).theta = d.theta
  left_slot_characters : ∀ b : family.active labels, ∀ ξ i,
    (family.leftData labels b ξ).slotCoefficient i ∈ d.theta
  right_slot_characters : ∀ b : family.active labels, ∀ ξ i,
    (family.rightData labels b ξ).slotCoefficient i ∈ d.theta
  left_admissible : ∀ b : family.active labels, ∀ ξ,
    EngineChildAdmissible A rowDomain window seminorms Z
      (family.leftData labels b ξ) (family.leftParameters labels b)
  right_admissible : ∀ b : family.active labels, ∀ ξ,
    EngineChildAdmissible A rowDomain window seminorms Z
      (family.rightData labels b ξ) (family.rightParameters labels b)
  left_capacity : ∀ b : family.active labels,
    (family.leftParameters labels b).z = 0 ∨
      (family.leftParameters labels b).n₁ + (family.leftParameters labels b).n₂ +
        6 * (family.leftParameters labels b).κ * (family.leftParameters labels b).z ≤
          (family.leftParameters labels b).m + (family.leftParameters labels b).q
  right_capacity : ∀ b : family.active labels,
    (family.rightParameters labels b).z = 0 ∨
      (family.rightParameters labels b).n₁ + (family.rightParameters labels b).n₂ +
        6 * (family.rightParameters labels b).κ * (family.rightParameters labels b).z ≤
          (family.rightParameters labels b).m + (family.rightParameters labels b).q

end Geometry

section Analysis

variable {U E Λ : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace (WithLp 2 (U × E))] [BorelSpace (WithLp 2 (U × E))]
variable {Z : ℝ}
variable (family : ActualNormalizedPairFamily A σ (WithLp 2 (U × E)) Λ ω ψ Z)
variable (labels : Finset Λ)

/-- Numerical output convergence under the literal constructed kernels.
Every displayed child is the normalized frozen data and uses twist zero. -/
structure OutputIntegrability
    (kernel : family.active labels → Measure (WithLp 2 (U × E))) : Prop where
  finite_kernel : ∀ b, IsFiniteMeasure (kernel b)
  left_integrable : ∀ b, Integrable (fun ξ =>
    normalizedPairedEnergy (family.leftData labels b ξ)
      (family.leftParameters labels b) Z 0) (kernel b)
  right_integrable : ∀ b, Integrable (fun ξ =>
    normalizedPairedEnergy (family.rightData labels b ξ)
      (family.rightParameters labels b) Z 0) (kernel b)
  cauchy_integrable : ∀ b, Integrable (fun ξ =>
    Real.sqrt (normalizedPairedEnergy (family.leftData labels b ξ)
      (family.leftParameters labels b) Z 0) *
    Real.sqrt (normalizedPairedEnergy (family.rightData labels b ξ)
      (family.rightParameters labels b) Z 0)) (kernel b)

namespace FourierAtomControl

variable {family labels}
variable {J₁₁ J₁₂ J₂₁ J₂₂ : ℕ}
variable (atoms : family.FourierAtomControl labels J₁₁ J₁₂ J₂₁ J₂₂)

/-- Finite individual atom controls and the exact polynomial profile
radii prove all output convergence fields, without a total mass input. -/
def outputIntegrability
    (F₁ : Λ → 𝓢(U, ℂ)) (F₂ : Λ → 𝓢(E, ℂ)) (outer : Λ → ℝ)
    (parentWidth : ℝ) (hZ : 0 < Z) :
    family.OutputIntegrability labels
      (family.kernel labels (actualNestedLabelMeasure F₁ F₂ outer) parentWidth) where
  finite_kernel b := by
    have hb : b.val ∈ labels := (Finset.mem_filter.mp b.property).1
    rw [family.kernel_actualNestedLabelMeasure labels F₁ F₂ outer parentWidth b]
    letI := normalizedCapacityPairKernel_nested_finite
      (atoms.leftAmplitude b.val) (atoms.rightAmplitude b.val) J₁₁ J₁₂ J₂₁ J₂₂
      (atoms.left_radius b.val hb) (atoms.right_radius b.val hb)
      (F₁ b.val) (F₂ b.val) (atoms.left_nonneg b.val hb) (atoms.right_nonneg b.val hb)
      (family.leftChild labels b) (family.rightChild labels b)
      (family.leftNormalizer b.val) (family.rightNormalizer b.val) Z parentWidth
    exact Measure.smul_finite _ ENNReal.ofReal_ne_top
  left_integrable b := (atoms.children_integrable F₁ F₂ outer parentWidth hZ b).1
  right_integrable b := (atoms.children_integrable F₁ F₂ outer parentWidth hZ b).2
  cauchy_integrable b :=
    actual_normalized_pair_integrable
      (family.kernel labels (actualNestedLabelMeasure F₁ F₂ outer) parentWidth b)
      (family.leftData labels b) (family.rightData labels b)
      (family.leftParameters labels b) (family.rightParameters labels b)
      (fun _ => 0) (fun _ => 0) Z hZ
      (atoms.children_integrable F₁ F₂ outer parentWidth hZ b).1
      (atoms.children_integrable F₁ F₂ outer parentWidth hZ b).2

end FourierAtomControl
end Analysis
end ActualNormalizedPairFamily

namespace ActualHybridFamily

variable {H : Type} {U E J : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable [Fintype J]
variable {I : J → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {Ray : Type*} [CommGroup Ray] [Fintype Ray] {Z : ℝ}
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
variable {heightDomain window : Set ℝ} {seminorms : Finset (ℕ × ℕ)}
variable (leaves : J → ActualHybridLeaf K H U E)
variable (N : ∀ j, (leaves j).NormalizationData (ι := I j)
  C Ray ω ψ Z rowDomain heightDomain window seminorms)
variable (raw : ∀ j, (N j).JointRowInput)
variable (d : MomentData K ω ψ) (a : RealParameters) (step : ℝ)

/-- All final child conditions follow from the original parent geometry
and original individual joint row-mask recipes. The actual capacity
choices are those already made by this same active normalized family. -/
def joint_outputGeometry
    (geometry : ∀ j, (N j).ParentGeometry d a step) :
    (normalizedFamily leaves (jointNormalizations leaves N raw)).OutputGeometry
      Finset.univ d a step rowDomain window seminorms := by
  let family := normalizedFamily leaves (jointNormalizations leaves N raw)
  have G : family.ParentGeometry Finset.univ d a step :=
    joint_parentGeometry leaves N raw d a step geometry
  exact {
    left_width := G.left_width
    right_width := G.right_width
    left_width_nonneg := fun b => (family.left_parameters_nonneg Finset.univ b).1
    right_width_nonneg := fun b => (family.right_parameters_nonneg Finset.univ b).1
    left_plain_left_nonneg := fun b => (family.left_parameters_nonneg Finset.univ b).2.1
    left_plain_right_nonneg := fun b => (family.left_parameters_nonneg Finset.univ b).2.2
    right_plain_left_nonneg := fun b => (family.right_parameters_nonneg Finset.univ b).2.1
    right_plain_right_nonneg := fun b => (family.right_parameters_nonneg Finset.univ b).2.2
    left_length := fun b ξ => (family.actual_total_lengths Finset.univ b ξ).1
    right_length := fun b ξ => (family.actual_total_lengths Finset.univ b ξ).2
    left_kappa := G.left_kappa_eq
    right_kappa := G.right_kappa_eq
    left_slots := G.left_slot_count
    right_slots := G.right_slot_count
    left_theta := G.left_theta_eq
    right_theta := G.right_theta_eq
    left_slot_characters := G.left_character
    right_slot_characters := G.right_character
    left_admissible := fun b ξ => (joint_family_admissible leaves N raw b ξ).1
    right_admissible := fun b ξ => (joint_family_admissible leaves N raw b ξ).2
    left_capacity := fun b => (family.leftChild Finset.univ b).capacity
    right_capacity := fun b => (family.rightChild Finset.univ b).capacity }

end ActualHybridFamily
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualNormalizedPairFamily.leftData_eq_frozen_normalized
#print axioms HeckeSkeleton.Moments.EngineStep.ActualNormalizedPairFamily.FourierAtomControl.outputIntegrability
#print axioms HeckeSkeleton.Moments.EngineStep.ActualHybridFamily.joint_outputGeometry

