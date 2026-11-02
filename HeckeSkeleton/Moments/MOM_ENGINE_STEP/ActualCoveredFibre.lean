import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalAllocationFingerprint
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalCoverCardinality
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.HybridLeafSupport

set_option linter.unusedSectionVars false
/-!
# Genuine fibres of the covered source carrier

The row labels below are the image of the original physical row set.
Every live actual leaf supplies a witness for membership in that image.
For fixed common ideals and outer mask, the source-class fibre is
counted by its two original cover keys, occurring row label and two
second extraction keys.  Padding the actual allocations is injective
on each such class, so a fibre of any arithmetic index retaining those
allocations has exactly this additional cost.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap
open MeasureTheory

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckePort.Moments HeckePort.Moments.MobiusRegroup
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
variable {E W : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]
local notation "Q" => SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ
local instance actualCoveredFibreCircleCharacterFintype : Fintype ((PUnit × PUnit) →* Circle) := Fintype.ofFinite _

namespace ActualGaussStage

variable {ι : Type*} {G : ActualGaussSource C ι}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable (s : ActualGaussStage (E := E) hΓ μv hDiff G finiteTest)
variable (LC RC : SourceCartesianCover G.columns G.ideal)

/-- The finite label image of the original physical rows. -/
def actualRowLabels
    (DE : commonSupportPool G.columns G.columns
      (fun i => (G.ideal i).val) (fun j => (G.ideal j).val))
    (D : s.mask.powerset) : Finset (Fin ((s.charts DE D).rowLabelCount + 1)) :=
  (s.sources DE).rows.image (s.charts DE D).rowLabel

namespace CoveredClassKey

variable {s LC RC}
variable (v : s.CoveredClassKey LC RC)

abbrev rightSupportSlots :=
  ((RC.branch v.2.2.2.1).branch (primeSupport v.1.val.1) v.1.val.2
    v.2.2.2.2.2.2).keep.card

theorem leftSlots_le {cap : ℕ} (hLC : ∀ a, (LC.branch a).slotCount ≤ cap) :
    v.leftSlots ≤ cap := by
  sorry

theorem rightSupportSlots_le {cap : ℕ} (hRC : ∀ a, (RC.branch a).slotCount ≤ cap) :
    v.rightSupportSlots ≤ cap := by
  sorry

theorem rowLabel_mem_of_live
    (exceptional : s.CoverHybridPredicates LC RC)
    (F : SchwartzMap W ℂ) (x : ι → W) (j : v.AllocationKey)
    (hlive : (v.leaf exceptional F x j).Live) :
    v.rowLabel ∈ s.actualRowLabels v.1 v.2.1 := by
  sorry

end CoveredClassKey

variable (DE : commonSupportPool G.columns G.columns
  (fun i => (G.ideal i).val) (fun j => (G.ideal j).val))
variable (D : s.mask.powerset)

/-- All four original support/cover keys remain. -/
abbrev PresentSupportClassKey :=
  LC.SupportClassKey RC (s.actualRowLabels DE D) (primeSupport DE.val.1)
    DE.val.1 DE.val.2

def presentSupportClass (a : s.PresentSupportClassKey LC RC DE D) :
    s.CoveredClassKey LC RC :=
  ⟨DE, D, a.1, a.2.1, a.2.2.1.val, a.2.2.2.1, a.2.2.2.2⟩

def presentClassFibre : Finset (s.CoveredClassKey LC RC) :=
  Finset.univ.filter (fun v => v.1 = DE ∧ v.2.1 = D ∧
    v.rowLabel ∈ s.actualRowLabels v.1 v.2.1)

/-- A direct count of the genuine source-class fibre.  This is a
surjection from the displayed original coordinates, not an assumed
injection into an unspecified finite surrogate. -/
theorem presentClassFibre_card_le
    (hDE : DE.val.1 ≠ 0 ∧ DE.val.2 ≠ 0) (cap : ℕ)
    (hLC : ∀ a, (LC.branch a).slotCount ≤ cap)
    (hRC : ∀ a, (RC.branch a).slotCount ≤ cap) :
    (s.presentClassFibre LC RC DE D).card ≤
      LC.labels.card * RC.labels.card * (s.actualRowLabels DE D).card *
        (DedekindZetaZeroFree.LargeSieve.idealDivisors DE.val.1).card ^ (cap + 2) *
          (DedekindZetaZeroFree.LargeSieve.idealDivisors DE.val.2).card ^ (cap + 2) := by
  sorry

/-- Raw finite row coordinates replace the unbounded declared row-label
codomain.  Only a per-original-row factorization identity is needed. -/
theorem actualRowLabels_card_le {P Θ : Type*} [Fintype Θ]
    (support : Finset P) (dimension width : ℕ)
    (code : Q → OriginalFiniteFibre.RowCode support Θ dimension width)
    (encode : OriginalFiniteFibre.RowCode support Θ dimension width →
      Fin ((s.charts DE D).rowLabelCount + 1))
    (hcode : ∀ h ∈ (s.sources DE).rows,
      (s.charts DE D).rowLabel h = encode (code h)) :
    (s.actualRowLabels DE D).card ≤
      2 ^ support.card * Fintype.card Θ * (width + 1) ^ dimension := by
  sorry

/-- The real outer mask remains a coordinate when the arithmetic
index fixes the common ideals but does not retain this mask. -/
def presentCommonFibre : Finset (s.CoveredClassKey LC RC) :=
  Finset.univ.filter (fun v => v.1 = DE ∧
    v.rowLabel ∈ s.actualRowLabels v.1 v.2.1)

theorem presentCommonFibre_card_le_coordinates {P Θ : Type*} [Fintype Θ]
    (support : Finset P) (dimension width : ℕ)
    (code : s.mask.powerset → Q → OriginalFiniteFibre.RowCode support Θ dimension width)
    (encode : ∀ D : s.mask.powerset,
      OriginalFiniteFibre.RowCode support Θ dimension width →
        Fin ((s.charts DE D).rowLabelCount + 1))
    (hcode : ∀ D : s.mask.powerset, ∀ h ∈ (s.sources DE).rows,
      (s.charts DE D).rowLabel h = encode D (code D h))
    (hDE : DE.val.1 ≠ 0 ∧ DE.val.2 ≠ 0) (cap : ℕ)
    (hLC : ∀ a, (LC.branch a).slotCount ≤ cap)
    (hRC : ∀ a, (RC.branch a).slotCount ≤ cap) :
    (s.presentCommonFibre LC RC DE).card ≤
      2 ^ s.mask.card * LC.labels.card * RC.labels.card *
        (2 ^ support.card * Fintype.card Θ * (width + 1) ^ dimension) *
          (DedekindZetaZeroFree.LargeSieve.idealDivisors DE.val.1).card ^ (cap + 2) *
            (DedekindZetaZeroFree.LargeSieve.idealDivisors DE.val.2).card ^ (cap + 2) := by
  sorry

variable {DE D s LC RC}
variable {cap : ℕ}
variable (hleft : ∀ v : s.CoveredClassKey LC RC, v.leftSlots ≤ cap)
variable (hright : ∀ v : s.CoveredClassKey LC RC, v.rightSupportSlots ≤ cap)

def coveredAllocationFingerprint (b : s.CoveredLeafKey LC RC) :
    OriginalAllocationFingerprint K cap :=
  hybridAllocationFingerprint (hleft b.1) (hright b.1) b.2

theorem covered_class_allocationFingerprint_injective :
    Function.Injective (fun b : s.CoveredLeafKey LC RC =>
      (b.1, coveredAllocationFingerprint hleft hright b)) := by
  sorry

/-- This applies to the actual arithmetic index while retaining all of
its extra coordinates (in particular the pool prime and valuation).
The two allocation coordinates cost nothing beyond that index. -/
theorem covered_index_fibre_card_le {J : Type*}
    (index : s.CoveredLeafKey LC RC → J)
    (allocation : J → OriginalAllocationFingerprint K cap)
    (hindex : ∀ b, allocation (index b) = coveredAllocationFingerprint hleft hright b)
    (S : Finset (s.CoveredLeafKey LC RC)) (j : J)
    (DE : commonSupportPool G.columns G.columns
      (fun i => (G.ideal i).val) (fun j => (G.ideal j).val))
    (D : s.mask.powerset)
    (hcommon : ∀ b ∈ S, index b = j → b.1.1 = DE ∧ b.1.2.1 = D)
    (hrow : ∀ b ∈ S, b.1.rowLabel ∈ s.actualRowLabels b.1.1 b.1.2.1)
    (hDE : DE.val.1 ≠ 0 ∧ DE.val.2 ≠ 0)
    (hLC : ∀ a, (LC.branch a).slotCount ≤ cap)
    (hRC : ∀ a, (RC.branch a).slotCount ≤ cap) :
    (S.filter (fun b => index b = j)).card ≤
      LC.labels.card * RC.labels.card * (s.actualRowLabels DE D).card *
        (DedekindZetaZeroFree.LargeSieve.idealDivisors DE.val.1).card ^ (cap + 2) *
          (DedekindZetaZeroFree.LargeSieve.idealDivisors DE.val.2).card ^ (cap + 2) := by
  sorry

/-- The complete extra fibre bound for one actual covered source.
Every factor on the right is an original finite coordinate count:
outer masks, the two earlier cover keys, the raw row code and the two
actual common-extraction tuples.  The arithmetic allocations have
already been preserved injectively by the index projection. -/
theorem covered_index_fibre_card_le_coordinates {J P Θ : Type*} [Fintype Θ]
    (index : s.CoveredLeafKey LC RC → J)
    (allocation : J → OriginalAllocationFingerprint K cap)
    (hindex : ∀ b, allocation (index b) = coveredAllocationFingerprint hleft hright b)
    (S : Finset (s.CoveredLeafKey LC RC)) (j : J)
    (DE : commonSupportPool G.columns G.columns
      (fun i => (G.ideal i).val) (fun j => (G.ideal j).val))
    (hcommon : ∀ b ∈ S, index b = j → b.1.1 = DE)
    (hrow : ∀ b ∈ S, b.1.rowLabel ∈ s.actualRowLabels b.1.1 b.1.2.1)
    (support : Finset P) (dimension width : ℕ)
    (code : s.mask.powerset → Q → OriginalFiniteFibre.RowCode support Θ dimension width)
    (encode : ∀ D : s.mask.powerset,
      OriginalFiniteFibre.RowCode support Θ dimension width →
        Fin ((s.charts DE D).rowLabelCount + 1))
    (hcode : ∀ D : s.mask.powerset, ∀ h ∈ (s.sources DE).rows,
      (s.charts DE D).rowLabel h = encode D (code D h))
    (hDE : DE.val.1 ≠ 0 ∧ DE.val.2 ≠ 0)
    (hLC : ∀ a, (LC.branch a).slotCount ≤ cap)
    (hRC : ∀ a, (RC.branch a).slotCount ≤ cap) :
    (S.filter (fun b => index b = j)).card ≤
      2 ^ s.mask.card * LC.labels.card * RC.labels.card *
        (2 ^ support.card * Fintype.card Θ * (width + 1) ^ dimension) *
          (DedekindZetaZeroFree.LargeSieve.idealDivisors DE.val.1).card ^ (cap + 2) *
            (DedekindZetaZeroFree.LargeSieve.idealDivisors DE.val.2).card ^ (cap + 2) := by
  sorry

end ActualGaussStage
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.CoveredClassKey.rowLabel_mem_of_live
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.presentClassFibre_card_le
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.covered_index_fibre_card_le
#print axioms HeckeSkeleton.Moments.EngineStep.ActualGaussStage.covered_index_fibre_card_le_coordinates
