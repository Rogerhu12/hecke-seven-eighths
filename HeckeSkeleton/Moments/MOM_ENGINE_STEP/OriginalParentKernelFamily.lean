import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalParentLeafScaling
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ScaledNormalizedKernels
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DependentNormalizedKernels

/-!
# The original live parents keep their dependent normalized families

The dependent family reads every component source, calibration,
capacity and chosen child verbatim. Its outer carrier is the original
live-parent carrier. The parent scalar is computed from the original
source definitions and multiplies the original two-kernel measure
once. The old frozen allocation cost is kept outside each component.

These composition identities consume the local conclusions of the
actual literal producers. They introduce no new child selection and
no change of the physical source or its finite labels.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap
open MeasureTheory

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.Moments

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {Γ : Subgroup A.U} [Γ.FiniteIndex]
variable {hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6}
variable [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable {μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K)}
  [∀ v, (μv v).IsAddHaarMeasure]
variable {hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0}
variable {E W : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]
local notation "Q" => SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ

local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local instance originalParentKernelFamilyCircleCharacterFintype :
    Fintype ((PUnit × PUnit) →* Circle) := Fintype.ofFinite _

variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}

variable [MeasurableSpace (WithLp 2 (W × E))] [BorelSpace (WithLp 2 (W × E))]

section DirectParents
variable {Z : ℝ}
variable {ω ψ : HeckeCharacter K} {centered : Bool}
variable {d : MomentData K ω ψ} {a : RealParameters}
variable {t Y₁ Y₂ X : ℝ} {hX : 1 ≤ X}
variable {s : ActualDirectFirstSource (E := W) hΓ μv C Z finiteTest centered d a t Y₁ Y₂ X hX}

namespace ActualDirectFirstSource.SecondStages
variable (R : s.SecondStages (E := E) (hDiff := hDiff))
variable (L : SourceCartesianAtlas s.columns s.ideal)

variable (exceptional : R.CoverHybridPredicates L) (N : s.Normalization)
local notation "Leaves" => R.liveLeaves L exceptional N
variable (Λ : R.liveLeaves L exceptional N → Type*) [∀ j, Fintype (Λ j)]
variable (families : ∀ j, ActualNormalizedPairFamily A σ (WithLp 2 (W × E)) (Λ j) ω ψ Z)
variable (frozen : R.liveLeaves L exceptional N → ℝ)

local notation "leaf" => fun j : Leaves => R.unscaledParentLeaf L exceptional j.val
local notation "factor" => fun j : Leaves => R.parentOuterScalar L N j.val
local notation "localMeasure" => fun j : Leaves =>
  actualNestedLabelMeasure (fun _ : Λ j => (leaf j).firstKernel)
    (fun _ : Λ j => (leaf j).secondKernel) (fun _ : Λ j => (leaf j).weight * frozen j)
local notation "scaledMeasure" => fun j : Leaves =>
  actualNestedLabelMeasure (fun _ : Λ j => (leaf j).firstKernel)
    (fun _ : Λ j => (leaf j).secondKernel)
    (fun _ : Λ j => factor j * ((leaf j).weight * frozen j))

/-- The original live leaf and its own actual passive label. -/
def dependentNormalizedFamily :
    ActualNormalizedPairFamily A σ (WithLp 2 (W × E)) (Σ j : Leaves, Λ j) ω ψ Z :=
  ActualNormalizedPairFamily.sigmaCombine families

/-- The two original Fourier kernels, with the original parent and
old frozen allocation factors each included once. -/
def dependentParentMeasure (b : Σ j : Leaves, Λ j) : Measure (WithLp 2 (W × E)) :=
  scaledMeasure b.1 b.2

/-- This is the actual parent leaf's measure, not a replacement of its
kernels or arithmetic outer weight. -/
theorem dependentParentMeasure_eq_original (b : Σ j : Leaves, Λ j) :
    R.dependentParentMeasure L exceptional N Λ frozen b =
      actualNestedLabelMeasure
        (fun _ : Λ b.1 => (R.parentLeaf L exceptional N b.1.val).firstKernel)
        (fun _ : Λ b.1 => (R.parentLeaf L exceptional N b.1.val).secondKernel)
        (fun _ : Λ b.1 => (R.parentLeaf L exceptional N b.1.val).weight * frozen b.1) b.2 := by
  rw [R.parentLeaf_eq_unscaled_scale L exceptional N b.1.val]
  simp only [dependentParentMeasure, ActualHybridLeaf.scale, mul_assoc]

/-- The source is unchanged when all actual child integrals are
written under the dependent parent kernel. -/
theorem dependent_child_integral_sum (parentWidth : ℝ) :
    (∑ b : (R.dependentNormalizedFamily L exceptional N Λ families).active Finset.univ,
      ∫ ξ, (R.dependentNormalizedFamily L exceptional N Λ families).childPair Finset.univ b ξ
        ∂(R.dependentNormalizedFamily L exceptional N Λ families).kernel Finset.univ
          (R.dependentParentMeasure L exceptional N Λ frozen) parentWidth b) =
      ∑ j : Leaves, factor j *
        ∑ b : (families j).active Finset.univ,
          ∫ ξ, (families j).childPair Finset.univ b ξ
            ∂(families j).kernel Finset.univ (localMeasure j) parentWidth b := by
  calc
    _ = ∑ j : Leaves, ∑ b : (families j).active Finset.univ,
          ∫ ξ, (families j).childPair Finset.univ b ξ
            ∂(families j).kernel Finset.univ (scaledMeasure j) parentWidth b := by
      simpa only [Finset.univ_sigma_univ, Finset.sum_coe_sort] using
        ActualNormalizedPairFamily.sum_sigmaCombine_child_integral families
          Finset.univ (fun _ => Finset.univ) scaledMeasure parentWidth
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      exact (families j).sum_child_integral_outer_mul Finset.univ
        (fun _ => (leaf j).firstKernel) (fun _ => (leaf j).secondKernel)
        (fun _ => (leaf j).weight * frozen j) parentWidth (factor j)
        (R.parentOuterScalar_nonneg L N j.val)

/-- The entire old outer scalar is paid once in each original
component's mass; the dependent indexing preserves every measure. -/
theorem dependent_kernel_mass_sum (parentWidth : ℝ) :
    (∑ b : (R.dependentNormalizedFamily L exceptional N Λ families).active Finset.univ,
      ((R.dependentNormalizedFamily L exceptional N Λ families).kernel Finset.univ
        (R.dependentParentMeasure L exceptional N Λ frozen) parentWidth b).real Set.univ) =
      ∑ j : Leaves, factor j *
        ∑ b : (families j).active Finset.univ,
          ((families j).kernel Finset.univ (localMeasure j) parentWidth b).real Set.univ := by
  calc
    _ = ∑ j : Leaves, ∑ b : (families j).active Finset.univ,
          ((families j).kernel Finset.univ (scaledMeasure j) parentWidth b).real Set.univ := by
      simpa only [Finset.univ_sigma_univ, Finset.sum_coe_sort] using
        ActualNormalizedPairFamily.sum_sigmaCombine_kernel_mass families
          Finset.univ (fun _ => Finset.univ) scaledMeasure parentWidth
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      exact (families j).sum_kernel_mass_outer_mul Finset.univ
        (fun _ => (leaf j).firstKernel) (fun _ => (leaf j).secondKernel)
        (fun _ => (leaf j).weight * frozen j) parentWidth (factor j)
        (R.parentOuterScalar_nonneg L N j.val)

/-- Local inequalities from the actual literal producers sum on the
original live-parent carrier, using its exact outer scalars. -/
theorem ordinaryCost_le_dependent_kernel (parentWidth : ℝ)
    (hlocal : ∀ j : Leaves, (leaf j).ordinaryCost / Z ^ parentWidth ≤
      ∑ b : (families j).active Finset.univ,
        ∫ ξ, (families j).childPair Finset.univ b ξ
          ∂(families j).kernel Finset.univ (localMeasure j) parentWidth b) :
    (∑ j : Leaves, (R.parentLeaf L exceptional N j.val).ordinaryCost) / Z ^ parentWidth ≤
      ∑ b : (R.dependentNormalizedFamily L exceptional N Λ families).active Finset.univ,
        ∫ ξ, (R.dependentNormalizedFamily L exceptional N Λ families).childPair Finset.univ b ξ
          ∂(R.dependentNormalizedFamily L exceptional N Λ families).kernel Finset.univ
            (R.dependentParentMeasure L exceptional N Λ frozen) parentWidth b := by
  rw [R.dependent_child_integral_sum L exceptional N Λ families frozen parentWidth,
    Finset.sum_div]
  apply Finset.sum_le_sum
  intro j _
  rw [R.parentLeaf_ordinaryCost_unscaled L exceptional N j.val]
  simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left (hlocal j)
    (R.parentOuterScalar_nonneg L N j.val)

/-- Finiteness is inherited from the same actual component kernel
through the original nonnegative parent scalar. -/
theorem dependent_kernel_finite (parentWidth : ℝ)
    (hfinite : ∀ j : Leaves, ∀ b : (families j).active Finset.univ,
      IsFiniteMeasure ((families j).kernel Finset.univ (localMeasure j) parentWidth b))
    (b : (R.dependentNormalizedFamily L exceptional N Λ families).active Finset.univ) :
    IsFiniteMeasure ((R.dependentNormalizedFamily L exceptional N Λ families).kernel Finset.univ
      (R.dependentParentMeasure L exceptional N Λ frozen) parentWidth b) := by
  let j := b.val.1
  let bj := ActualNormalizedPairFamily.sigmaActiveInner families
    Finset.univ (fun _ => Finset.univ) b
  letI := hfinite j bj
  exact (families j).kernel_outer_mul_finite Finset.univ
    (fun _ => (leaf j).firstKernel) (fun _ => (leaf j).secondKernel)
    (fun _ => (leaf j).weight * frozen j) parentWidth (factor j)
    (R.parentOuterScalar_nonneg L N j.val) bj

/-- Both normalized energies use the same chosen data, parameters
and kernel after the original parent factors are restored. -/
theorem dependent_children_integrable (parentWidth : ℝ)
    (hchildren : ∀ j : Leaves, ∀ b : (families j).active Finset.univ,
      Integrable (fun ξ => normalizedPairedEnergy
        ((families j).leftData Finset.univ b ξ) ((families j).leftParameters Finset.univ b) Z 0)
        ((families j).kernel Finset.univ (localMeasure j) parentWidth b) ∧
      Integrable (fun ξ => normalizedPairedEnergy
        ((families j).rightData Finset.univ b ξ) ((families j).rightParameters Finset.univ b) Z 0)
        ((families j).kernel Finset.univ (localMeasure j) parentWidth b))
    (b : (R.dependentNormalizedFamily L exceptional N Λ families).active Finset.univ) :
    Integrable (fun ξ => normalizedPairedEnergy
      ((R.dependentNormalizedFamily L exceptional N Λ families).leftData Finset.univ b ξ)
      ((R.dependentNormalizedFamily L exceptional N Λ families).leftParameters Finset.univ b) Z 0)
      ((R.dependentNormalizedFamily L exceptional N Λ families).kernel Finset.univ
        (R.dependentParentMeasure L exceptional N Λ frozen) parentWidth b) ∧
    Integrable (fun ξ => normalizedPairedEnergy
      ((R.dependentNormalizedFamily L exceptional N Λ families).rightData Finset.univ b ξ)
      ((R.dependentNormalizedFamily L exceptional N Λ families).rightParameters Finset.univ b) Z 0)
      ((R.dependentNormalizedFamily L exceptional N Λ families).kernel Finset.univ
        (R.dependentParentMeasure L exceptional N Λ frozen) parentWidth b) := by
  let j := b.val.1
  let bj := ActualNormalizedPairFamily.sigmaActiveInner families
    Finset.univ (fun _ => Finset.univ) b
  have h := hchildren j bj
  exact ⟨(families j).kernel_outer_mul_integrable Finset.univ
      (fun _ => (leaf j).firstKernel) (fun _ => (leaf j).secondKernel)
      (fun _ => (leaf j).weight * frozen j) parentWidth (factor j)
      (R.parentOuterScalar_nonneg L N j.val) bj _ h.1,
    (families j).kernel_outer_mul_integrable Finset.univ
      (fun _ => (leaf j).firstKernel) (fun _ => (leaf j).secondKernel)
      (fun _ => (leaf j).weight * frozen j) parentWidth (factor j)
      (R.parentOuterScalar_nonneg L N j.val) bj _ h.2⟩

end ActualDirectFirstSource.SecondStages
end DirectParents

section AmplifiedParents
variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable {P : PowerScaleExteriorPool A bad Z ell eps}
variable {ω ψ : HeckeCharacter K} {centered : Bool}
variable {d : MomentData K ω ψ} {a : RealParameters}
variable {t Y₁ Y₂ X : ℝ} {hX : 1 ≤ X}
variable {s : ActualFirstSource (E := W) hΓ μv C P finiteTest centered d a t Y₁ Y₂ X hX}

namespace ActualFirstSource.SecondStages
variable (R : s.SecondStages (E := E) (hDiff := hDiff))
variable (L : SourceCartesianAtlas s.columns s.ideal)

variable (exceptional : R.CoverHybridPredicates L) (N : s.Normalization)
local notation "Leaves" => R.liveLeaves L exceptional N
variable (Λ : R.liveLeaves L exceptional N → Type*) [∀ j, Fintype (Λ j)]
variable (families : ∀ j, ActualNormalizedPairFamily A σ (WithLp 2 (W × E)) (Λ j) ω ψ Z)
variable (frozen : R.liveLeaves L exceptional N → ℝ)

local notation "leaf" => fun j : Leaves => R.unscaledParentLeaf L exceptional j.val
local notation "factor" => fun j : Leaves => R.parentOuterScalar L N j.val
local notation "localMeasure" => fun j : Leaves =>
  actualNestedLabelMeasure (fun _ : Λ j => (leaf j).firstKernel)
    (fun _ : Λ j => (leaf j).secondKernel) (fun _ : Λ j => (leaf j).weight * frozen j)
local notation "scaledMeasure" => fun j : Leaves =>
  actualNestedLabelMeasure (fun _ : Λ j => (leaf j).firstKernel)
    (fun _ : Λ j => (leaf j).secondKernel)
    (fun _ : Λ j => factor j * ((leaf j).weight * frozen j))

/-- The original live leaf and its own actual passive label. -/
def dependentNormalizedFamily :
    ActualNormalizedPairFamily A σ (WithLp 2 (W × E)) (Σ j : Leaves, Λ j) ω ψ Z :=
  ActualNormalizedPairFamily.sigmaCombine families

/-- The two original Fourier kernels, with the original parent and
old frozen allocation factors each included once. -/
def dependentParentMeasure (b : Σ j : Leaves, Λ j) : Measure (WithLp 2 (W × E)) :=
  scaledMeasure b.1 b.2

/-- This is the actual parent leaf's measure, not a replacement of its
kernels or arithmetic outer weight. -/
theorem dependentParentMeasure_eq_original (b : Σ j : Leaves, Λ j) :
    R.dependentParentMeasure L exceptional N Λ frozen b =
      actualNestedLabelMeasure
        (fun _ : Λ b.1 => (R.parentLeaf L exceptional N b.1.val).firstKernel)
        (fun _ : Λ b.1 => (R.parentLeaf L exceptional N b.1.val).secondKernel)
        (fun _ : Λ b.1 => (R.parentLeaf L exceptional N b.1.val).weight * frozen b.1) b.2 := by
  rw [R.parentLeaf_eq_unscaled_scale L exceptional N b.1.val]
  simp only [dependentParentMeasure, ActualHybridLeaf.scale, mul_assoc]

/-- The source is unchanged when all actual child integrals are
written under the dependent parent kernel. -/
theorem dependent_child_integral_sum (parentWidth : ℝ) :
    (∑ b : (R.dependentNormalizedFamily L exceptional N Λ families).active Finset.univ,
      ∫ ξ, (R.dependentNormalizedFamily L exceptional N Λ families).childPair Finset.univ b ξ
        ∂(R.dependentNormalizedFamily L exceptional N Λ families).kernel Finset.univ
          (R.dependentParentMeasure L exceptional N Λ frozen) parentWidth b) =
      ∑ j : Leaves, factor j *
        ∑ b : (families j).active Finset.univ,
          ∫ ξ, (families j).childPair Finset.univ b ξ
            ∂(families j).kernel Finset.univ (localMeasure j) parentWidth b := by
  calc
    _ = ∑ j : Leaves, ∑ b : (families j).active Finset.univ,
          ∫ ξ, (families j).childPair Finset.univ b ξ
            ∂(families j).kernel Finset.univ (scaledMeasure j) parentWidth b := by
      simpa only [Finset.univ_sigma_univ, Finset.sum_coe_sort] using
        ActualNormalizedPairFamily.sum_sigmaCombine_child_integral families
          Finset.univ (fun _ => Finset.univ) scaledMeasure parentWidth
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      exact (families j).sum_child_integral_outer_mul Finset.univ
        (fun _ => (leaf j).firstKernel) (fun _ => (leaf j).secondKernel)
        (fun _ => (leaf j).weight * frozen j) parentWidth (factor j)
        (R.parentOuterScalar_nonneg L N j.val)

/-- The entire old outer scalar is paid once in each original
component's mass; the dependent indexing preserves every measure. -/
theorem dependent_kernel_mass_sum (parentWidth : ℝ) :
    (∑ b : (R.dependentNormalizedFamily L exceptional N Λ families).active Finset.univ,
      ((R.dependentNormalizedFamily L exceptional N Λ families).kernel Finset.univ
        (R.dependentParentMeasure L exceptional N Λ frozen) parentWidth b).real Set.univ) =
      ∑ j : Leaves, factor j *
        ∑ b : (families j).active Finset.univ,
          ((families j).kernel Finset.univ (localMeasure j) parentWidth b).real Set.univ := by
  calc
    _ = ∑ j : Leaves, ∑ b : (families j).active Finset.univ,
          ((families j).kernel Finset.univ (scaledMeasure j) parentWidth b).real Set.univ := by
      simpa only [Finset.univ_sigma_univ, Finset.sum_coe_sort] using
        ActualNormalizedPairFamily.sum_sigmaCombine_kernel_mass families
          Finset.univ (fun _ => Finset.univ) scaledMeasure parentWidth
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      exact (families j).sum_kernel_mass_outer_mul Finset.univ
        (fun _ => (leaf j).firstKernel) (fun _ => (leaf j).secondKernel)
        (fun _ => (leaf j).weight * frozen j) parentWidth (factor j)
        (R.parentOuterScalar_nonneg L N j.val)

/-- Local inequalities from the actual literal producers sum on the
original live-parent carrier, using its exact outer scalars. -/
theorem ordinaryCost_le_dependent_kernel (parentWidth : ℝ)
    (hlocal : ∀ j : Leaves, (leaf j).ordinaryCost / Z ^ parentWidth ≤
      ∑ b : (families j).active Finset.univ,
        ∫ ξ, (families j).childPair Finset.univ b ξ
          ∂(families j).kernel Finset.univ (localMeasure j) parentWidth b) :
    (∑ j : Leaves, (R.parentLeaf L exceptional N j.val).ordinaryCost) / Z ^ parentWidth ≤
      ∑ b : (R.dependentNormalizedFamily L exceptional N Λ families).active Finset.univ,
        ∫ ξ, (R.dependentNormalizedFamily L exceptional N Λ families).childPair Finset.univ b ξ
          ∂(R.dependentNormalizedFamily L exceptional N Λ families).kernel Finset.univ
            (R.dependentParentMeasure L exceptional N Λ frozen) parentWidth b := by
  rw [R.dependent_child_integral_sum L exceptional N Λ families frozen parentWidth,
    Finset.sum_div]
  apply Finset.sum_le_sum
  intro j _
  rw [R.parentLeaf_ordinaryCost_unscaled L exceptional N j.val]
  simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left (hlocal j)
    (R.parentOuterScalar_nonneg L N j.val)

/-- Finiteness is inherited from the same actual component kernel
through the original nonnegative parent scalar. -/
theorem dependent_kernel_finite (parentWidth : ℝ)
    (hfinite : ∀ j : Leaves, ∀ b : (families j).active Finset.univ,
      IsFiniteMeasure ((families j).kernel Finset.univ (localMeasure j) parentWidth b))
    (b : (R.dependentNormalizedFamily L exceptional N Λ families).active Finset.univ) :
    IsFiniteMeasure ((R.dependentNormalizedFamily L exceptional N Λ families).kernel Finset.univ
      (R.dependentParentMeasure L exceptional N Λ frozen) parentWidth b) := by
  let j := b.val.1
  let bj := ActualNormalizedPairFamily.sigmaActiveInner families
    Finset.univ (fun _ => Finset.univ) b
  letI := hfinite j bj
  exact (families j).kernel_outer_mul_finite Finset.univ
    (fun _ => (leaf j).firstKernel) (fun _ => (leaf j).secondKernel)
    (fun _ => (leaf j).weight * frozen j) parentWidth (factor j)
    (R.parentOuterScalar_nonneg L N j.val) bj

/-- Both normalized energies use the same chosen data, parameters
and kernel after the original parent factors are restored. -/
theorem dependent_children_integrable (parentWidth : ℝ)
    (hchildren : ∀ j : Leaves, ∀ b : (families j).active Finset.univ,
      Integrable (fun ξ => normalizedPairedEnergy
        ((families j).leftData Finset.univ b ξ) ((families j).leftParameters Finset.univ b) Z 0)
        ((families j).kernel Finset.univ (localMeasure j) parentWidth b) ∧
      Integrable (fun ξ => normalizedPairedEnergy
        ((families j).rightData Finset.univ b ξ) ((families j).rightParameters Finset.univ b) Z 0)
        ((families j).kernel Finset.univ (localMeasure j) parentWidth b))
    (b : (R.dependentNormalizedFamily L exceptional N Λ families).active Finset.univ) :
    Integrable (fun ξ => normalizedPairedEnergy
      ((R.dependentNormalizedFamily L exceptional N Λ families).leftData Finset.univ b ξ)
      ((R.dependentNormalizedFamily L exceptional N Λ families).leftParameters Finset.univ b) Z 0)
      ((R.dependentNormalizedFamily L exceptional N Λ families).kernel Finset.univ
        (R.dependentParentMeasure L exceptional N Λ frozen) parentWidth b) ∧
    Integrable (fun ξ => normalizedPairedEnergy
      ((R.dependentNormalizedFamily L exceptional N Λ families).rightData Finset.univ b ξ)
      ((R.dependentNormalizedFamily L exceptional N Λ families).rightParameters Finset.univ b) Z 0)
      ((R.dependentNormalizedFamily L exceptional N Λ families).kernel Finset.univ
        (R.dependentParentMeasure L exceptional N Λ frozen) parentWidth b) := by
  let j := b.val.1
  let bj := ActualNormalizedPairFamily.sigmaActiveInner families
    Finset.univ (fun _ => Finset.univ) b
  have h := hchildren j bj
  exact ⟨(families j).kernel_outer_mul_integrable Finset.univ
      (fun _ => (leaf j).firstKernel) (fun _ => (leaf j).secondKernel)
      (fun _ => (leaf j).weight * frozen j) parentWidth (factor j)
      (R.parentOuterScalar_nonneg L N j.val) bj _ h.1,
    (families j).kernel_outer_mul_integrable Finset.univ
      (fun _ => (leaf j).firstKernel) (fun _ => (leaf j).secondKernel)
      (fun _ => (leaf j).weight * frozen j) parentWidth (factor j)
      (R.parentOuterScalar_nonneg L N j.val) bj _ h.2⟩

end ActualFirstSource.SecondStages
end AmplifiedParents

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualDirectFirstSource.SecondStages.dependentNormalizedFamily
#print axioms HeckeSkeleton.Moments.EngineStep.ActualDirectFirstSource.SecondStages.dependentParentMeasure_eq_original
#print axioms HeckeSkeleton.Moments.EngineStep.ActualDirectFirstSource.SecondStages.ordinaryCost_le_dependent_kernel
#print axioms HeckeSkeleton.Moments.EngineStep.ActualDirectFirstSource.SecondStages.dependent_kernel_mass_sum
#print axioms HeckeSkeleton.Moments.EngineStep.ActualDirectFirstSource.SecondStages.dependent_children_integrable
#print axioms HeckeSkeleton.Moments.EngineStep.ActualFirstSource.SecondStages.dependentNormalizedFamily
#print axioms HeckeSkeleton.Moments.EngineStep.ActualFirstSource.SecondStages.dependentParentMeasure_eq_original
#print axioms HeckeSkeleton.Moments.EngineStep.ActualFirstSource.SecondStages.ordinaryCost_le_dependent_kernel
#print axioms HeckeSkeleton.Moments.EngineStep.ActualFirstSource.SecondStages.dependent_kernel_mass_sum
#print axioms HeckeSkeleton.Moments.EngineStep.ActualFirstSource.SecondStages.dependent_children_integrable
