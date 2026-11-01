import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralAtlasAtoms
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralCommonLeaf
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualGaussFiniteLeaves
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.HybridLeafSupport

/-!
# Literal common extraction on the stored covered leaf

This module acts on `CoveredClassKey.leaf` itself.  It reads the two
existing atlas branches, transports only their support proofs and
extracts their actual common occurrences.  The finite allocation is
the stored leaf's original allocation.  The two kernels, its outer
weight and its complete original physical row set are retained.

The local coefficient arguments below are the individual chart-field
identities supplied by the canonical original-atom calculations. They
are used before any polynomial sum, norm or positive estimate. This
module is their structural adapter, not a replacement raw-source
assumption or a second choice of source/children.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments MeasureTheory
open HeckePort.Moments HeckePort.Moments.Support HeckePort.Moments.MobiusRegroup
open HeckePort.IdealMobiusDivisorSum
open WholeAllocation

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

local instance canonicalLiteralCoveredLeafCircleCharacterFintype :
    Fintype ((PUnit.{1} × PUnit.{1}) →* Circle) := Fintype.ofFinite _

namespace ActualGaussStage.CoveredClassKey

variable {ι : Type*} {G : ActualGaussSource C ι}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {s : ActualGaussStage (E := ℝ) hΓ μv hDiff G finiteTest}
variable {LC RC : SourceCartesianCover G.columns G.ideal}
variable (v : s.CoveredClassKey LC RC)

abbrev literalLeftParent := LC.branch v.2.2.1
abbrev literalRightParent := RC.branch v.2.2.2.1

abbrev literalLeftBranch :=
  v.literalLeftParent.branch (primeSupport v.1.val.1) v.1.val.1 v.2.2.2.2.2.1

abbrev literalRightBranch :=
  v.literalRightParent.branch (primeSupport v.1.val.1) v.1.val.2 v.2.2.2.2.2.2

/-- These atlas objects reuse the stored residual index, including all
its original support transports. Only nonemptiness is proved here. -/
def literalLeftResidualAtlas : SourceCartesianAtlas
    (v.literalLeftParent.commonFibre (primeSupport v.1.val.1) v.1.val.1 v.2.2.2.2.2.1)
    v.block.leftResidual :=
  SourceCartesianAtlas.ofReindex v.leftReindex (by
    obtain ⟨i, hi, he⟩ := Finset.mem_image.mp v.2.2.2.2.2.1.property
    exact ⟨i, Finset.mem_filter.mpr ⟨hi, he⟩⟩)

def literalRightResidualAtlas : SourceCartesianAtlas
    (v.literalRightParent.commonFibre (primeSupport v.1.val.1) v.1.val.2 v.2.2.2.2.2.2)
    v.block.rightResidual :=
  SourceCartesianAtlas.ofReindex v.rightReindex (by
    obtain ⟨i, hi, he⟩ := Finset.mem_image.mp v.2.2.2.2.2.2.property
    exact ⟨i, Finset.mem_filter.mpr ⟨hi, he⟩⟩)

variable (leftAtoms : CanonicalLiteralRectangles.Atoms (K := K)
  (LC.branch v.2.2.1).slotCount)
variable (rightAtoms : CanonicalLiteralRectangles.Atoms (K := K)
  (RC.branch v.2.2.2.1).slotCount)

abbrev literalLeftOriginal := leftAtoms.onAtlas v.literalLeftParent rfl
abbrev literalRightOriginal := rightAtoms.onAtlas v.literalRightParent rfl

/-- The complete original Gauss product stays in the actual residual
atom table. The common scalar is extracted separately exactly once. -/
def literalLeftAtoms : CanonicalLiteralRectangles.Atoms (K := K) v.leftSlots :=
  ((v.literalLeftOriginal leftAtoms).extract v.literalLeftBranch).onAtlas
    v.literalLeftResidualAtlas rfl

def literalRightAtoms : CanonicalLiteralRectangles.Atoms (K := K)
    v.literalRightBranch.keep.card :=
  ((v.literalRightOriginal rightAtoms).extract v.literalRightBranch).onAtlas
    v.literalRightResidualAtlas rfl

@[simp] theorem literalLeftAtoms_whole (i : AllocationColumn K v.leftSlots) :
    (v.literalLeftAtoms leftAtoms).whole i =
      ((v.literalLeftOriginal leftAtoms).extract v.literalLeftBranch).whole i := rfl

@[simp] theorem literalRightAtoms_whole
    (i : AllocationColumn K v.literalRightBranch.keep.card) :
    (v.literalRightAtoms rightAtoms).whole i =
      ((v.literalRightOriginal rightAtoms).extract v.literalRightBranch).whole i := rfl

theorem literalLeft_cartesian (i : AllocationColumn K v.leftSlots) :
    i ∈ v.leftReindex.cartesian ↔ i ∈ v.literalLeftBranch.residualColumns := by
  change i ∈ childCartesianColumns v.leftReindex.plain₁ v.leftReindex.plain₂
    v.leftReindex.slots ↔ _
  rw [SourceCartesianAtlas.residualReindex_plain₁,
    SourceCartesianAtlas.residualReindex_plain₂, SourceCartesianAtlas.residualReindex_slots]
  rfl

theorem literalRight_cartesian (i : AllocationColumn K v.literalRightBranch.keep.card) :
    i ∈ v.rightReindex.cartesian ↔ i ∈ v.literalRightBranch.residualColumns := by
  change i ∈ childCartesianColumns v.rightReindex.plain₁ v.rightReindex.plain₂
    v.rightReindex.slots ↔ _
  rw [SourceCartesianAtlas.residualReindex_plain₁,
    SourceCartesianAtlas.residualReindex_plain₂, SourceCartesianAtlas.residualReindex_slots]
  rfl

theorem literalLeft_index_common (i : AllocationColumn K v.leftSlots)
    (hi : i ∈ v.leftReindex.cartesian) :
    v.leftReindex.index i ∈ v.block.leftColumns G.columns := by
  have hm := v.leftReindex.maps i hi
  have hc := Finset.mem_filter.mp (Finset.mem_filter.mp hm).1
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hc.1).1, hc.2⟩

theorem literalRight_index_common (i : AllocationColumn K v.literalRightBranch.keep.card)
    (hi : i ∈ v.rightReindex.cartesian) :
    v.rightReindex.index i ∈ v.block.rightColumns G.columns := by
  have hm := v.rightReindex.maps i hi
  have hc := Finset.mem_filter.mp (Finset.mem_filter.mp hm).1
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hc.1).1, hc.2⟩

variable (exceptional : s.CoverHybridPredicates LC RC)
variable (F : SchwartzMap ℝ ℂ) (x : ι → ℝ) (j : v.AllocationKey)

private theorem literal_left_mem (i : AllocationColumn K v.leftSlots)
    (hi : i ∈ (v.leaf exceptional F x j).left) : i ∈ v.leftReindex.cartesian := by
  change i ∈ pairedAllocatedColumns j.1.val j.2.2.1.val
    v.leftReindex.plain₁ v.leftReindex.plain₂ v.leftReindex.slots
    id id HeightOneSpectrum.asIdeal at hi
  rw [paired_allocated_columns_eq_filter] at hi
  exact (Finset.mem_filter.mp hi).1

private theorem literal_right_mem (i : AllocationColumn K v.literalRightBranch.keep.card)
    (hi : i ∈ (v.leaf exceptional F x j).right) : i ∈ v.rightReindex.cartesian := by
  change i ∈ pairedAllocatedColumns j.1.val j.2.2.2.val
    v.rightReindex.plain₁ v.rightReindex.plain₂ v.rightReindex.slots
    id id HeightOneSpectrum.asIdeal at hi
  rw [paired_allocated_columns_eq_filter] at hi
  exact (Finset.mem_filter.mp hi).1

variable (leftCoefficient : ∀ i ∈ (LC.branch v.2.2.1).reindex.cartesian,
  (LC.branch v.2.2.1).reindex.index i ∈ v.block.leftColumns G.columns →
    v.chart.sourceLeftCoefficient ((LC.branch v.2.2.1).reindex.index i) = leftAtoms.whole i)
variable (rightCoefficient : ∀ i ∈ (RC.branch v.2.2.2.1).reindex.cartesian,
  (RC.branch v.2.2.2.1).reindex.index i ∈ v.block.rightColumns G.columns →
    v.chart.sourceRightCoefficient ((RC.branch v.2.2.2.1).reindex.index i) = rightAtoms.whole i)

include leftCoefficient in
private theorem literal_left_coefficient
    (i : AllocationColumn K v.leftSlots) (hi : i ∈ v.leftReindex.cartesian) :
    v.chart.sourceLeftCoefficient (v.leftReindex.index i) =
      (v.literalLeftOriginal leftAtoms).commonScalar v.literalLeftBranch *
        (v.literalLeftAtoms leftAtoms).whole i := by
  have hr := (v.literalLeft_cartesian i).mp hi
  have hm := v.literalLeftBranch.reconstruct_mem i hr
  rw [v.literalLeftBranch.originalColumns_eq_filter] at hm
  have hc := v.literalLeft_index_common i hi
  rw [SourceCartesianAtlas.residualReindex_index] at hc ⊢
  rw [leftCoefficient _ (Finset.mem_filter.mp hm).1 hc]
  exact (v.literalLeftOriginal leftAtoms).extract_whole v.literalLeftBranch i hr

include rightCoefficient in
private theorem literal_right_coefficient
    (i : AllocationColumn K v.literalRightBranch.keep.card)
    (hi : i ∈ v.rightReindex.cartesian) :
    v.chart.sourceRightCoefficient (v.rightReindex.index i) =
      (v.literalRightOriginal rightAtoms).commonScalar v.literalRightBranch *
        (v.literalRightAtoms rightAtoms).whole i := by
  have hr := (v.literalRight_cartesian i).mp hi
  have hm := v.literalRightBranch.reconstruct_mem i hr
  rw [v.literalRightBranch.originalColumns_eq_filter] at hm
  have hc := v.literalRight_index_common i hi
  rw [SourceCartesianAtlas.residualReindex_index] at hc ⊢
  rw [rightCoefficient _ (Finset.mem_filter.mp hm).1 hc]
  exact (v.literalRightOriginal rightAtoms).extract_whole v.literalRightBranch i hr

/-- The extraction is attached to the original stored finite leaf.
All coefficient equalities are proved at its actual allocated columns. -/
def literalExtraction : (v.leaf exceptional F x j).ConstantAtomExtraction where
  leftScalar := (v.literalLeftOriginal leftAtoms).commonScalar v.literalLeftBranch
  rightScalar := (v.literalRightOriginal rightAtoms).commonScalar v.literalRightBranch
  leftResidual := secondAllocatedLeftCoefficient (σ := σ) PUnit.{1}
    (fun i => v.block.leftResidual (v.leftReindex.index i))
    (v.chart.actualRows s.mask s.cutoff s.cutoff_one v.rowLabel).frequency
    (fun _ => PUnit.unit) j.2.1 (v.literalLeftAtoms leftAtoms).whole
  rightResidual := fun h i => star (secondAllocatedRightCoefficient (σ := σ) PUnit.{1}
    (fun i => v.block.rightResidual (v.rightReindex.index i))
    (v.chart.actualRows s.mask s.cutoff s.cutoff_one v.rowLabel).frequency
    (fun _ => PUnit.unit) j.2.1 (v.literalRightAtoms rightAtoms).whole h i)
  left h _ i hi := by
    change v.chart.sourceLeftCoefficient (v.leftReindex.index i) * _ * _ = _
    rw [v.literal_left_coefficient leftAtoms leftCoefficient i
      (v.literal_left_mem exceptional F x j i hi)]
    dsimp only [secondAllocatedLeftCoefficient]
    ring
  right h _ i hi := by
    change v.chart.sourceRightCoefficient (v.rightReindex.index i) * _ * _ = _
    rw [v.literal_right_coefficient rightAtoms rightCoefficient i
      (v.literal_right_mem exceptional F x j i hi)]
    simp only [secondAllocatedRightCoefficient, star_star]
    ring

/-- This reweighting is the one forced by the two constants just
extracted from the stored whole coefficients. -/
def literalRows : ActualSecondCorrelationRows A σ
    (SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ) (Fin v.block.primeCount) :=
  { v.chart.actualRows s.mask s.cutoff s.cutoff_one v.rowLabel with
    weight := fun h =>
      (v.chart.actualRows s.mask s.cutoff s.cutoff_one v.rowLabel).weight h *
        (v.literalLeftOriginal leftAtoms).commonScalar v.literalLeftBranch *
        star ((v.literalRightOriginal rightAtoms).commonScalar v.literalRightBranch) }

def literalSupportedRows : ActualSecondCorrelationRows A σ
    (SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ) (Fin v.block.primeCount) :=
  (v.literalRows leftAtoms rightAtoms).restrictRows (fun h =>
    (v.chart.actualRows s.mask s.cutoff s.cutoff_one v.rowLabel).correlation h ≠ 0)

/-- Nonempty original allocated columns and squarefreeness come from
the stored live leaf. No fresh allocation or nonempty-source premise
is chosen for its child. -/
def literalAllocation (hlive : (v.leaf exceptional F x j).Live) :
    liveSecondAllocationBranches (Ray := PUnit.{1})
      v.leftReindex.plain₁ v.leftReindex.plain₂ v.leftReindex.slots
      v.rightReindex.plain₁ v.rightReindex.plain₂ v.rightReindex.slots
      (fun i => v.block.rightResidual (v.rightReindex.index i)) := by
  refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_, ?_⟩⟩
  · by_contra hn
    apply hlive.1
    change ‖(moebius j.1.val : ℂ)‖ * _ = 0
    simp only [moebius_of_not_squarefree hn, Int.cast_zero, norm_zero, zero_mul]
  · obtain ⟨h, hh, i, hi, hc⟩ := hlive.2.1
    exact ⟨i, hi⟩
  · obtain ⟨h, hh, i, hi, hc⟩ := hlive.2.2
    exact ⟨i, hi⟩

/-- Both rectangles now belong to the exact same stored allocation and
the exact original correlation support. -/
def literalRectangles (firstSign : ℝ) (hlive : (v.leaf exceptional F x j).Live) :=
  CanonicalLiteralRectangles.rectangles (v.literalSupportedRows leftAtoms rightAtoms)
    (v.literalLeftAtoms leftAtoms) (v.literalRightAtoms rightAtoms)
    (fun i => v.block.leftResidual (v.leftReindex.index i))
    (fun i => v.block.rightResidual (v.rightReindex.index i))
    v.leftReindex.ideal_product v.rightReindex.ideal_product
    (v.literalAllocation exceptional F x j hlive)
    (v.leaf exceptional F x j).exceptional firstSign (-firstSign)

variable (firstSign : ℝ) (hlive : (v.leaf exceptional F x j).Live)
variable (leftPoint : ∀ h ∈ (v.leaf exceptional F x j).rows,
  ∃ z : WithLp 2 (ℝ × ℝ), ∀ i ∈ (v.leaf exceptional F x j).left,
    WithLp.toLp 2 ((v.leaf exceptional F x j).leftFirst h i,
      (v.leaf exceptional F x j).leftSecond h i) =
        z + rawSourceLocation (CanonicalLiteralLocations.plain firstSign)
          (CanonicalLiteralLocations.plain firstSign)
          (CanonicalLiteralLocations.prime firstSign) i)
variable (rightPoint : ∀ h ∈ (v.leaf exceptional F x j).rows,
  ∃ z : WithLp 2 (ℝ × ℝ), ∀ i ∈ (v.leaf exceptional F x j).right,
    WithLp.toLp 2 (-(v.leaf exceptional F x j).rightFirst h i,
      (v.leaf exceptional F x j).rightSecond h i) =
        z + rawSourceLocation (CanonicalLiteralLocations.plain (-firstSign))
          (CanonicalLiteralLocations.plain (-firstSign))
          (CanonicalLiteralLocations.prime (-firstSign)) i)

/-- The ordinary binding is attached to the extracted original leaf,
not to a separately manufactured finite polynomial. The only omitted
rows have their original full correlation equal to zero. -/
def literalOrdinaryBinding :
    (v.literalExtraction leftAtoms rightAtoms exceptional F x j
      leftCoefficient rightCoefficient).leaf.OrdinaryBinding
        (v.literalRectangles leftAtoms rightAtoms exceptional F x j firstSign hlive) where
  rows h hh := (Finset.mem_filter.mp hh).1
  rows_zero h hh hn := by
    have hc : (v.chart.actualRows s.mask s.cutoff s.cutoff_one v.rowLabel).correlation h = 0 := by
      by_contra hc
      exact hn (Finset.mem_filter.mpr ⟨hh, hc⟩)
    change ((_ * (v.chart.actualRows s.mask s.cutoff s.cutoff_one v.rowLabel).correlation h) *
      _ * _) = 0
    simp only [hc, mul_zero, zero_mul]
  left := rfl
  right := rfl
  exceptional _ _ := Iff.rfl
  rowWeight h _ := by
    change ((_ * _) * _ * _) = ((_ * _ * _) * _)
    ring
  leftCoefficient _ _ _ _ := rfl
  rightCoefficient _ _ _ _ := by
    simp only [literalExtraction, ActualHybridLeaf.ConstantAtomExtraction.leaf,
      ActualHybridLeaf.withConstantAtoms, star_star]
  leftPoint := leftPoint
  rightPoint := rightPoint

@[simp] theorem literalExtraction_firstKernel :
    (v.literalExtraction leftAtoms rightAtoms exceptional F x j
      leftCoefficient rightCoefficient).leaf.firstKernel = F := rfl

@[simp] theorem literalExtraction_secondKernel :
    (v.literalExtraction leftAtoms rightAtoms exceptional F x j
      leftCoefficient rightCoefficient).leaf.secondKernel = v.chart.kernel := rfl

@[simp] theorem literalExtraction_outerWeight :
    (v.literalExtraction leftAtoms rightAtoms exceptional F x j
      leftCoefficient rightCoefficient).leaf.weight = (v.leaf exceptional F x j).weight := rfl

end ActualGaussStage.CoveredClassKey
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.literalLeft_index_common
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.literalExtraction
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.literalOrdinaryBinding
