import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralCoveredLeaf
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralFrozenBounds
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalSupportedRowMass

/-!
# Canonical arithmetic mass of the same literal common rows

Both common atom dictionaries are computed from the actual occurrence
branches. Their values are exactly the two constants extracted from the
original whole columns. Reweighting the rows by those constants is
therefore the same reweighting used by the original row-mass theorem.

The original nonunit classifier fixes both radicals on nonzero
correlations, and the original orbit map proves the fibre Γ.index.
Only the individual original row-profile window is supplied. No bound
on a whole row weight, a fibre cardinality, a child or a source is input.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
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

namespace ActualGaussStage.CoveredClassKey

variable {ι : Type*} {G : ActualGaussSource C ι}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {s : ActualGaussStage (E := ℝ) hΓ μv hDiff G finiteTest}
variable {LC RC : SourceCartesianCover G.columns G.ideal}
variable (v : s.CoveredClassKey LC RC)

variable (leftAtoms : CanonicalLiteralRectangles.Atoms (K := K)
  (LC.branch v.2.2.1).slotCount)
variable (rightAtoms : CanonicalLiteralRectangles.Atoms (K := K)
  (RC.branch v.2.2.2.1).slotCount)
variable (leftMask : leftAtoms.characters.MaskIndicator)
variable (rightMask : rightAtoms.characters.MaskIndicator)

local notation "R₀" => v.chart.actualRows s.mask s.cutoff s.cutoff_one v.rowLabel
local notation "left" => v.literalLeftOriginal leftAtoms
local notation "right" => v.literalRightOriginal rightAtoms

def literalLeftCommonAtoms : FrozenSourceAtoms A σ
    (SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ)
    (v.chart.actualRows s.mask s.cutoff s.cutoff_one v.rowLabel).rows
    (LC.branch v.2.2.1).slotCount :=
  (left.commonAtomBounds v.literalLeftBranch leftMask).atoms R₀.rows

def literalRightCommonAtoms : FrozenSourceAtoms A σ
    (SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ)
    (v.chart.actualRows s.mask s.cutoff s.cutoff_one v.rowLabel).rows
    (RC.branch v.2.2.2.1).slotCount :=
  (right.commonAtomBounds v.literalRightBranch rightMask).atoms R₀.rows

theorem literalLeftCommonAtoms_ideal :
    (v.literalLeftCommonAtoms leftAtoms leftMask).ideal =
      (primePowerProduct v.block.primes v.block.leftMultiplicity).val := by
  exact ((left.commonAtomBounds v.literalLeftBranch leftMask).atoms_ideal R₀.rows).trans
    ((v.literalLeftParent.branch_product (primeSupport v.1.val.1) v.1.val.1
      v.2.2.2.2.2.1).trans v.block.common_left.symm)

theorem literalRightCommonAtoms_ideal :
    (v.literalRightCommonAtoms rightAtoms rightMask).ideal =
      (primePowerProduct v.block.primes v.block.rightMultiplicity).val := by
  exact ((right.commonAtomBounds v.literalRightBranch rightMask).atoms_ideal R₀.rows).trans
    ((v.literalRightParent.branch_product (primeSupport v.1.val.1) v.1.val.2
      v.2.2.2.2.2.2).trans v.block.common_right.symm)

theorem literalLeftCommonAtoms_value
    (h : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ) :
    (v.literalLeftCommonAtoms leftAtoms leftMask).value h =
      left.commonScalar v.literalLeftBranch :=
  (left.commonAtomBounds v.literalLeftBranch leftMask).atoms_value R₀.rows
    (primePowerProduct v.block.primes v.block.leftMultiplicity)
    ((v.literalLeftParent.branch_product (primeSupport v.1.val.1) v.1.val.1
      v.2.2.2.2.2.1).trans v.block.common_left.symm) h

theorem literalRightCommonAtoms_value
    (h : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ) :
    (v.literalRightCommonAtoms rightAtoms rightMask).value h =
      right.commonScalar v.literalRightBranch :=
  (right.commonAtomBounds v.literalRightBranch rightMask).atoms_value R₀.rows
    (primePowerProduct v.block.primes v.block.rightMultiplicity)
    ((v.literalRightParent.branch_product (primeSupport v.1.val.1) v.1.val.2
      v.2.2.2.2.2.2).trans v.block.common_right.symm) h

theorem literalRows_eq_withCommonAtoms :
    v.literalRows leftAtoms rightAtoms =
      R₀.withCommonAtoms (v.literalLeftCommonAtoms leftAtoms leftMask)
        (v.literalRightCommonAtoms rightAtoms rightMask) := by
  unfold literalRows ActualSecondCorrelationRows.withCommonAtoms
  congr 1
  funext h
  rw [v.literalLeftCommonAtoms_value leftAtoms leftMask h,
    v.literalRightCommonAtoms_value rightAtoms rightMask h]

variable (hclass : v.chart.NonunitLabelStable)
variable (bound : ℝ) (hbound : 0 ≤ bound)
variable (hprofile : ∀ h ∈ (v.chart.actualRows s.mask s.cutoff s.cutoff_one v.rowLabel).rows,
  ‖v.chart.weight h‖ ≤ bound)

/-- This record has exactly the actual literal row carrier. Rebuilding
its fields keeps the calculated numerical costs transparent rather than
hiding them behind a transport of the whole dependent record. -/
def literalSupportedRowMass :
    ActualSecondRowMass (v.literalSupportedRows leftAtoms rightAtoms) C
      (LC.branch v.2.2.1).slotCount (RC.branch v.2.2.2.1).slotCount := by
  let W := v.chart.actualRowsSupportedMass hclass s.mask s.cutoff s.cutoff_one v.rowLabel
    (v.literalLeftCommonAtoms leftAtoms leftMask) (v.literalRightCommonAtoms rightAtoms rightMask)
    (v.literalLeftCommonAtoms_ideal leftAtoms leftMask)
    (v.literalRightCommonAtoms_ideal rightAtoms rightMask) bound hbound hprofile
  refine {
    leftAtoms := W.leftAtoms
    rightAtoms := W.rightAtoms
    left_ideal := W.left_ideal
    right_ideal := W.right_ideal
    radius := W.radius
    mask := W.mask
    rowProfile := W.rowProfile
    profileBound := W.profileBound
    profileBound_nonneg := W.profileBound_nonneg
    profile_bound := W.profile_bound
    weight_eq := ?_
    unitIdeal := W.unitIdeal
    unit_ideal := W.unit_ideal
    nonunitIdeal := W.nonunitIdeal
    nonunit_ideal := W.nonunit_ideal
    left_positive := W.left_positive
    originalFiber := W.originalFiber
    original_fibers := W.original_fibers }
  intro h hh
  have hw := W.weight_eq h hh
  change R₀.weight h * (v.literalLeftCommonAtoms leftAtoms leftMask).value h *
    star ((v.literalRightCommonAtoms rightAtoms rightMask).value h) = _ at hw
  rw [v.literalLeftCommonAtoms_value leftAtoms leftMask h,
    v.literalRightCommonAtoms_value rightAtoms rightMask h] at hw
  exact hw

@[simp] theorem literalSupportedRowMass_fiber :
    (v.literalSupportedRowMass leftAtoms rightAtoms leftMask rightMask
      hclass bound hbound hprofile).originalFiber = Γ.index := rfl

@[simp] theorem literalSupportedRowMass_unit :
    (v.literalSupportedRowMass leftAtoms rightAtoms leftMask rightMask
      hclass bound hbound hprofile).unitIdeal =
      secondPatternUnitIdeal v.block.primes v.block.leftMultiplicity v.block.rightMultiplicity
        (v.chart.originalNonunitPattern s.mask s.cutoff s.cutoff_one v.rowLabel) := rfl

@[simp] theorem literalSupportedRowMass_nonunit :
    (v.literalSupportedRowMass leftAtoms rightAtoms leftMask rightMask
      hclass bound hbound hprofile).nonunitIdeal =
      secondPatternNonunitIdeal v.block.primes
        (v.chart.originalNonunitPattern s.mask s.cutoff s.cutoff_one v.rowLabel) := rfl

end ActualGaussStage.CoveredClassKey
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.literalRows_eq_withCommonAtoms
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.literalSupportedRowMass
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.literalSupportedRowMass_fiber
