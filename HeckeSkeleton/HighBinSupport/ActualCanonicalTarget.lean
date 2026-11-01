import HeckeSkeleton.HighBinSupport.ActualCanonicalHighBin
import HeckeSkeleton.HighBinSupport.ActualCanonicalData
import HeckeSkeleton.HighBinSupport.ActualDyadicBoundary

/-!
The canonical HIGHBIN construction for the original target context.

The probe, measures, arithmetic Euler tables, finite-order companions,
common packet boundary and arithmetic calibration are all obtained from
the existing primitive target data. The buffer is chosen from the two
positive losses before any scale, shell, row mask or detector index.

Witness subdivisions remain explicit recipes. No cover theorem or
identification with a different prime-polynomial slot is asserted here.
This module does not import the old named high-expansion construction.

AI-assisted: ChatGPT / GPT-6 Astra Pro, 2026-10-31.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HeckeSkeleton.HighBinCanonicalTarget

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.TIP
open HeckeSkeleton.HighBinActualEuler HeckeSkeleton.HighBinActualInitial
open HeckeSkeleton.HighBinDetectorGeometry HeckeSkeleton.HighBinCanonical
open HighBinVerified HighBinVerified.NormFormRegions
open HighBinVerified.NormFormRegionIntegral HighBinVerified.NormFormRegionPacket
open HighBinVerified.NormFormComputedPacket
open scoped Classical BigOperators Topology

variable (K : Type) [Field K] [NumberField K]
variable (c : TargetContext K)

/-- Every row at every height inherits the original common packet bound.
No improved boundary is an assumption of the canonical construction. -/
theorem targetCommonBoundary :
    ∀ u : FrequencyRow K (places K c), ∀ height : ℝ,
      rowZeroBelow K (places K c) (targetCharacter K c) (targetCompanions K c)
        (probeData K c) (targetEuler K c) u height c.family.B :=
  fun u height => physicalRowFamily_zeroBelow_of_common_bound K (places K c)
    (representative K c).val.property (targetCompanions K c)
    (targetCompanions_finiteOrder K c) (probeData K c) (targetEuler K c)
    c.family.boundary u height

/-- The actual target's finite detector fibers, with an arbitrary source
mask so the outer shell schedule may impose the exact global cutoff. -/
def targetCanonicalRows (R : Finset (FrequencyRow K (places K c)))
    (Z T kappa d : ℝ) (k : DetectorIndex (detectorDepth (targetBuffer K c))) :
    Finset (FrequencyRow K (places K c)) :=
  canonicalRows K (places K c) (probeData K c) (targetCharacter K c)
    (targetCompanions K c) R c.family.B (targetBuffer K c)
    (targetBuffer_pos K c) (targetBoundary_lower K c) (targetCommonBoundary K c)
    Z T kappa d k

abbrev TargetCanonicalBlockIndex (R : Finset (FrequencyRow K (places K c)))
    (Z T kappa d : ℝ) :=
  CanonicalBlockIndex K (places K c) (probeData K c) (targetCharacter K c)
    (targetCompanions K c) R c.family.B (targetBuffer K c)
    (targetBuffer_pos K c) (targetBoundary_lower K c) (targetCommonBoundary K c)
    Z T kappa d

local instance : MeasurableSpace (sLocalNormOneGroup K (places K c)) :=
  (probeMeasures K c).normOneSpace
local instance : BorelSpace (sLocalNormOneGroup K (places K c)) :=
  (probeMeasures K c).normOneBorel
local instance (p : places K c) : MeasurableSpace (p.val.adicCompletion K) :=
  (probeMeasures K c).localSpace p
local instance (p : places K c) : BorelSpace (p.val.adicCompletion K) :=
  (probeMeasures K c).localBorel p
local instance (p : places K c) : ((probeMeasures K c).haar p).IsAddHaarMeasure :=
  (probeMeasures K c).haar_isAddHaar p

/-- A target block is populated by literal restricted contour integrals
and actual computed amplitude regions, using the target's Haar measures. -/
def targetCanonicalBlock (R : Finset (FrequencyRow K (places K c)))
    (Z T kappa d theta : ℝ) (N : ℕ)
    (k : TargetCanonicalBlockIndex K c R Z T kappa d)
    (sc : (Fin c.geometry.slots → Fin (N + 1)) → ℝ → ℕ)
    (sub : (label : Fin c.geometry.slots → Fin (N + 1)) →
      (t : ℝ) → Fin (sc label t) → WitnessSubdivision (FrequencyRow K (places K c))) :
    ModerateBlock (FrequencyRow K (places K c)) c.geometry.slots :=
  canonicalBlock K (excludedPlaces K c) (probeMeasures K c).haar
    (probeData K c) (targetCharacter K c) (targetCompanions K c) R
    c.family.B (targetBuffer K c) (targetBuffer_pos K c) (targetBoundary_lower K c)
    (targetCommonBoundary K c) c.geometry Z T kappa d theta N k sc sub

theorem targetCanonicalBlock_bin_range (R : Finset (FrequencyRow K (places K c)))
    (Z T kappa d theta : ℝ) (N : ℕ)
    (k : TargetCanonicalBlockIndex K c R Z T kappa d)
    (sc : (Fin c.geometry.slots → Fin (N + 1)) → ℝ → ℕ)
    (sub : (label : Fin c.geometry.slots → Fin (N + 1)) →
      (t : ℝ) → Fin (sc label t) → WitnessSubdivision (FrequencyRow K (places K c))) :
    51 / 100 ≤ (targetCanonicalBlock K c R Z T kappa d theta N k sc sub).bin ∧
      (targetCanonicalBlock K c R Z T kappa d theta N k sc sub).bin ≤ c.family.B :=
  canonicalBin_bounds K (places K c) (probeData K c) (targetCharacter K c)
    (targetCompanions K c) R c.family.B (targetBuffer K c)
    (targetBuffer_pos K c) (targetBoundary_lower K c) (targetCommonBoundary K c)
    Z T kappa d k

/-- A fixed finite label set, independent of scales, masks and witnesses. -/
theorem targetCanonicalLabel_card (N : ℕ) :
    (Finset.univ : Finset (Fin c.geometry.slots → Fin (N + 1))).card =
      (N + 1) ^ c.geometry.slots :=
  computedRegionLabel_card c.geometry N

/-- The conclusion proved for a concrete tuple of analytic parameters.
It is a proposition about computed blocks, not an input to their construction. -/
def TargetCanonicalNormFormSpec (kappa theta : ℝ) (N : ℕ) (C Z0 : ℝ) : Prop :=
    0 < kappa ∧ 0 < theta ∧ 0 < C ∧ 1 ≤ Z0 ∧
    ∀ Z T : ℝ, Z0 ≤ Z → 1 ≤ T → T ≤ Z ^ kappa →
    ∀ d : ℝ, (1 / 16 : ℝ) ≤ d → d ≤ 1 →
    ∀ R : Finset (FrequencyRow K (places K c)),
    ∀ k : TargetCanonicalBlockIndex K c R Z T kappa d,
    let F := targetCanonicalRows K c R Z T kappa d k.val
    let a := gridRealPart (targetBuffer K c) k.val.2.val
    integrableRows K (excludedPlaces K c) (probeMeasures K c).haar
      (probeData K c) (targetCharacter K c) c.geometry F Z a (targetBuffer K c)
      (NormForm.internalHeight Z T kappa) = F ∧
    ∀ sc : (Fin c.geometry.slots → Fin (N + 1)) → ℝ → ℕ,
    ∀ sub : (label : Fin c.geometry.slots → Fin (N + 1)) →
      (t : ℝ) → Fin (sc label t) → WitnessSubdivision (FrequencyRow K (places K c)),
    let block := targetCanonicalBlock K c R Z T kappa d theta N k sc sub
    block.value = ∑ u ∈ F,
      rowContourBox K (places K c) (probeMeasures K c).haar (probeData K c)
        (targetCharacter K c) (targetEuler K c) c.geometry ∅ u Z
        (NormForm.internalHeight Z T kappa) (a + 16 * targetBuffer K c)
        (1 - a - 6 * targetBuffer K c) (17 / 50) ∧
    ∀ label : Fin c.geometry.slots → Fin (N + 1),
    (∀ u ∈ (block.amplitudeSet label).rows,
      ActualRegionSlotBounds K (places K c) (probeData K c) (targetCharacter K c)
        c.geometry u Z a (targetBuffer K c)
        (NormForm.internalHeight Z T kappa) theta N label) ∧
    (∑ u ∈ (block.amplitudeSet label).rows,
      ‖actualRegionPiece K (excludedPlaces K c) (probeMeasures K c).haar
        (probeData K c) (targetCharacter K c) c.geometry u Z a (targetBuffer K c)
        (NormForm.internalHeight Z T kappa) theta N label‖) ≤
      C * ((block.amplitudeSet label).rows.card : ℝ) *
        Z ^ (3 / 16 + moderateExponent block.shell (2 * block.bin - 1)
          (block.amplitudeSet label).mean 0 + targetLoss K c / 4)

/-- The true target norm-form endpoint. All arithmetic and detector
inputs are discharged by the target context. Constants precede scales,
shells, source masks, retained blocks, labels and witness recipes. -/
theorem targetCanonicalNormForm :
    ∃ kappa theta : ℝ, ∃ N : ℕ, ∃ C Z0 : ℝ,
      TargetCanonicalNormFormSpec K c kappa theta N C Z0 := by
  exact exists_canonicalBlock_normForm K (excludedPlaces K c) (probeMeasures K c).haar
    (probeData K c) (targetCharacter K c) (targetCompanions K c)
    c.family.B (targetBuffer K c) (targetBuffer_pos K c) (targetBoundary_lower K c)
    (targetCommonBoundary K c) (one_mem_targetCompanions K c) c.geometry
    (arithmeticCalibration K c)
    (fun p => target_unramified_outside K c p.val p.property)
    (targetBuffer_small K c) c.family.B_upper (targetLoss_pos K c)
    (targetBuffer_le_loss K c)

/-- Numerical parameters only. The estimates are proved for the chosen
tuple below; they are not fields supplied by a caller. -/
structure CanonicalParameters where
  kappa : ℝ
  theta : ℝ
  N : ℕ
  C : ℝ
  Z0 : ℝ

theorem exists_targetCanonicalParameters :
    ∃ p : CanonicalParameters,
      TargetCanonicalNormFormSpec K c p.kappa p.theta p.N p.C p.Z0 := by
  obtain ⟨kappa, theta, N, C, Z0, h⟩ := targetCanonicalNormForm K c
  exact ⟨⟨kappa, theta, N, C, Z0⟩, h⟩

/-- One fixed choice of parameters, reused by all computed target blocks. -/
def targetCanonicalParameters : CanonicalParameters :=
  Classical.choose (exists_targetCanonicalParameters K c)

theorem targetCanonicalParameters_spec :
    TargetCanonicalNormFormSpec K c
      (targetCanonicalParameters K c).kappa (targetCanonicalParameters K c).theta
      (targetCanonicalParameters K c).N (targetCanonicalParameters K c).C
      (targetCanonicalParameters K c).Z0 :=
  Classical.choose_spec (exists_targetCanonicalParameters K c)

theorem targetCanonicalParameters_positive :
    0 < (targetCanonicalParameters K c).kappa ∧
      0 < (targetCanonicalParameters K c).theta ∧
      0 < (targetCanonicalParameters K c).C ∧
      1 ≤ (targetCanonicalParameters K c).Z0 := by
  have h := targetCanonicalParameters_spec K c
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

abbrev ChosenTargetBlockIndex (R : Finset (FrequencyRow K (places K c)))
    (Z T d : ℝ) :=
  TargetCanonicalBlockIndex K c R Z T (targetCanonicalParameters K c).kappa d

/-- The named computed block uses precisely the parameters selected by
the proven target norm form. The source and witness recipes stay explicit. -/
def chosenTargetCanonicalBlock (R : Finset (FrequencyRow K (places K c)))
    (Z T d : ℝ) (k : ChosenTargetBlockIndex K c R Z T d)
    (sc : (Fin c.geometry.slots → Fin ((targetCanonicalParameters K c).N + 1)) → ℝ → ℕ)
    (sub : (label : Fin c.geometry.slots → Fin ((targetCanonicalParameters K c).N + 1)) →
      (t : ℝ) → Fin (sc label t) → WitnessSubdivision (FrequencyRow K (places K c))) :
    ModerateBlock (FrequencyRow K (places K c)) c.geometry.slots :=
  targetCanonicalBlock K c R Z T (targetCanonicalParameters K c).kappa d
    (targetCanonicalParameters K c).theta (targetCanonicalParameters K c).N k sc sub

/-- The complete actual dyadic boundary with the same target buffer,
companions, arithmetic provider and detector partition as the blocks. -/
def targetDyadicBoundary (source : ℝ → ℝ → Finset (FrequencyRow K (places K c)))
    (kappa upper Z T : ℝ) : ℂ :=
  HighBinDyadicBoundary.dyadicBoundary K (excludedPlaces K c) (probeMeasures K c).haar
    (probeData K c) (targetCharacter K c) (targetCompanions K c) c.geometry
    c.family.B (targetBuffer K c) (targetBuffer_pos K c) (targetBoundary_lower K c)
    (targetCommonBoundary K c) (rayFilter K c) (source Z T) Z T kappa upper

/-- The full boundary has an arbitrary external-height tail with the
fixed scale exponent 14. All source masks and legal upper cutoffs are
covered by the same constants. -/
theorem targetDyadicBoundary_external_tail :
    ∃ Z0 : ℝ, 2 ≤ Z0 ∧ ∀ N : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (source : ℝ → ℝ → Finset (FrequencyRow K (places K c)))
        (kappa upper Z T : ℝ),
      Z0 ≤ Z → 1 ≤ T → 1 / 16 ≤ upper → upper ≤ 1 →
      ‖targetDyadicBoundary K c source kappa upper Z T‖ ≤
        C * Z ^ 14 * T ^ (-(N : ℝ)) := by
  obtain ⟨Z0, hZ0, htail⟩ := HighBinDyadicBoundary.exists_dyadicBoundary_external_tail
    K (excludedPlaces K c) (probeMeasures K c).haar (probeData K c)
    (targetCharacter K c) (targetCompanions K c) c.geometry
    c.family.B (targetBuffer K c) (targetBuffer_pos K c) (targetBoundary_lower K c)
    (targetCommonBoundary K c) (one_mem_targetCompanions K c)
    (targetBuffer_small K c) c.family.B_upper
  refine ⟨Z0, hZ0, ?_⟩
  intro N
  obtain ⟨C, hC, hb⟩ := htail N
  refine ⟨C, hC, ?_⟩
  intro source kappa upper Z T hZ hT hlo hhi
  exact hb (rayFilter K c) (source Z T) Z T kappa upper hZ hT hlo hhi

theorem targetDyadicBoundary_powerHeightTailBound
    (source : ℝ → ℝ → Finset (FrequencyRow K (places K c)))
    (kappa upper : ℝ) (hlo : 1 / 16 ≤ upper) (hhi : upper ≤ 1) :
    PowerHeightTailBound (targetDyadicBoundary K c source kappa upper) :=
  HighBinDyadicBoundary.dyadicBoundary_powerHeightTailBound
    K (excludedPlaces K c) (probeMeasures K c).haar (probeData K c)
    (targetCharacter K c) (targetCompanions K c) c.geometry
    c.family.B (targetBuffer K c) (targetBuffer_pos K c) (targetBoundary_lower K c)
    (targetCommonBoundary K c) (one_mem_targetCompanions K c)
    (targetBuffer_small K c) c.family.B_upper (rayFilter K c) source kappa upper hlo hhi

end HeckeSkeleton.HighBinCanonicalTarget

#print axioms HeckeSkeleton.HighBinCanonicalTarget.targetEuler_input
#print axioms HeckeSkeleton.HighBinCanonicalTarget.targetCommonBoundary
#print axioms HeckeSkeleton.HighBinCanonicalTarget.targetCanonicalNormForm
#print axioms HeckeSkeleton.HighBinCanonicalTarget.targetCanonicalParameters_spec
#print axioms HeckeSkeleton.HighBinCanonicalTarget.targetDyadicBoundary_powerHeightTailBound
