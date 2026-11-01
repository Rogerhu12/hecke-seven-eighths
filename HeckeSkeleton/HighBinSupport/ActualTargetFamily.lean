import HeckeSkeleton.HighBinSupport.ActualCanonicalFamily
import HeckeSkeleton.HighBinSupport.ActualCanonicalTarget
import HeckeSkeleton.HighBinSupport.ActualCanonicalIdentities

/-!
One concrete retained family for the original target. Its buffer,
moderate cutoff, dyadic shell indices, detector fibers, grid parameters,
amplitude rows and pieces are fixed by the preceding constructions.
Witness subdivision recipes remain explicit data. The norm and boundary
theorems refer to this same family and its original finite source mask.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.HighBinCanonicalTarget

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.TIP
open HeckeSkeleton.HighBinDetectorGeometry HeckeSkeleton.HighBinCanonical
open HeckeSkeleton.HighBinCanonicalFamily HeckeSkeleton.HighBinDyadicRows
open HighBinVerified HighBinVerified.Dyadic HighBinVerified.NormFormRegions
open HighBinVerified.NormFormRegionIntegral HighBinVerified.NormFormComputedPacket
open scoped Classical BigOperators Topology

variable (K : Type) [Field K] [NumberField K]
variable (c : TargetContext K)

/-- A positive moderate-shell allowance within the stated 1/48 range. -/
def targetZeta : ℝ := min (1 / 96) (targetLoss K c / 100)

theorem targetZeta_pos : 0 < targetZeta K c :=
  lt_min (by norm_num) (div_pos (targetLoss_pos K c) (by norm_num))

theorem targetZeta_small : targetZeta K c < 1 / 48 :=
  lt_of_le_of_lt (min_le_left _ _) (by norm_num)

def targetUpper : ℝ := 13 / 16 + targetZeta K c

theorem targetUpper_range : 1 / 16 ≤ targetUpper K c ∧ targetUpper K c ≤ 1 := by
  have hp := targetZeta_pos K c
  have hs := targetZeta_small K c
  unfold targetUpper
  constructor <;> linarith

/-- The finite global source, including the original upper cutoff. -/
def targetModerateSource (Z : ℝ) : Finset (FrequencyRow K (places K c)) :=
  moderateSource K (places K c) Z (targetUpper K c)

abbrev ChosenTargetFamilyIndex (Z T : ℝ) :=
  CanonicalFamilyIndex K (places K c) (probeData K c) (targetCharacter K c)
    (targetCompanions K c) c.family.B (targetBuffer K c)
    (targetBuffer_pos K c) (targetBoundary_lower K c) (targetCommonBoundary K c)
    Z T (targetCanonicalParameters K c).kappa (targetUpper K c)

/-- The actual retained family has subpower block count and height degree zero. -/
theorem chosenTargetFamily_count {Z η : ℝ} (T : ℝ) (hZ : 1 ≤ Z) (hη : 0 < η) :
    (Fintype.card (ChosenTargetFamilyIndex K c Z T) : ℝ) ≤
      (((detectorDepth (targetBuffer K c) + 1 : ℕ) : ℝ) ^ 2 *
        (2 + ((targetUpper K c - 1 / 16) / Real.log 2) / η)) * Z ^ η :=
  canonicalFamilyIndex_subpower K (places K c) (probeData K c) (targetCharacter K c)
    (targetCompanions K c) c.family.B (targetBuffer K c)
    (targetBuffer_pos K c) (targetBoundary_lower K c) (targetCommonBoundary K c)
    T (targetCanonicalParameters K c).kappa hZ (targetUpper_range K c).1 hη

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

/-- A member of the single fixed target family, with the computed
parameters shared by every scale, shell and retained detector fiber. -/
def chosenTargetFamilyBlock (Z T : ℝ) (b : ChosenTargetFamilyIndex K c Z T)
    (sc : (Fin c.geometry.slots → Fin ((targetCanonicalParameters K c).N + 1)) → ℝ → ℕ)
    (sub : (label : Fin c.geometry.slots → Fin ((targetCanonicalParameters K c).N + 1)) →
      (t : ℝ) → Fin (sc label t) → WitnessSubdivision (FrequencyRow K (places K c))) :
    ModerateBlock (FrequencyRow K (places K c)) c.geometry.slots :=
  chosenTargetCanonicalBlock K c (targetModerateSource K c Z) Z T
    (shellExponent Z (1 / 16) b.1.val) b.2 sc sub

/-- The fixed arithmetic row set used on both contours of a family block. -/
def chosenTargetFamilyRows (Z T : ℝ) (b : ChosenTargetFamilyIndex K c Z T) :
    Finset (FrequencyRow K (places K c)) :=
  targetCanonicalRows K c (targetModerateSource K c Z) Z T
    (targetCanonicalParameters K c).kappa (shellExponent Z (1 / 16) b.1.val) b.2.val

/-- Exact final-contour identification at every positive scale, before
the large-scale norm estimate is used. The full assigned fiber survives. -/
theorem chosenTargetFamily_value_eq_final (Z T : ℝ) (hZ : 0 < Z) (hT : 1 ≤ T)
    (b : ChosenTargetFamilyIndex K c Z T)
    (sc : (Fin c.geometry.slots → Fin ((targetCanonicalParameters K c).N + 1)) → ℝ → ℕ)
    (sub : (label : Fin c.geometry.slots → Fin ((targetCanonicalParameters K c).N + 1)) →
      (t : ℝ) → Fin (sc label t) → WitnessSubdivision (FrequencyRow K (places K c))) :
    let block := chosenTargetFamilyBlock K c Z T b sc sub
    block.value = ∑ u ∈ chosenTargetFamilyRows K c Z T b,
      rowContourBox K (places K c) (probeMeasures K c).haar (probeData K c)
        (targetCharacter K c) (targetEuler K c) c.geometry (rayFilter K c) u Z
        (NormForm.internalHeight Z T (targetCanonicalParameters K c).kappa)
        (block.bin + 16 * targetBuffer K c) (1 - block.bin - 6 * targetBuffer K c)
        (17 / 50) :=
  canonicalBlock_value_eq_final K (excludedPlaces K c) (probeMeasures K c).haar
    (probeData K c) (targetCharacter K c) (targetCompanions K c)
    (targetModerateSource K c Z) c.family.B (targetBuffer K c)
    (targetBuffer_pos K c) (targetBoundary_lower K c) (targetCommonBoundary K c)
    (one_mem_targetCompanions K c) c.geometry (targetBuffer_small K c) c.family.B_upper
    Z T (targetCanonicalParameters K c).kappa (shellExponent Z (1 / 16) b.1.val)
    (targetCanonicalParameters K c).theta (targetCanonicalParameters K c).N hZ hT b.2 sc sub

/-- The exact quarter-loss exponent of HB-NORMFORM for the actual
computed pieces, now indexed by the full retained target family. -/
theorem chosenTargetFamily_normForm (Z T : ℝ)
    (hZ : max (targetCanonicalParameters K c).Z0 2 ≤ Z)
    (hT : 1 ≤ T) (hTcap : T ≤ Z ^ (targetCanonicalParameters K c).kappa)
    (b : ChosenTargetFamilyIndex K c Z T)
    (sc : (Fin c.geometry.slots → Fin ((targetCanonicalParameters K c).N + 1)) → ℝ → ℕ)
    (sub : (label : Fin c.geometry.slots → Fin ((targetCanonicalParameters K c).N + 1)) →
      (t : ℝ) → Fin (sc label t) → WitnessSubdivision (FrequencyRow K (places K c)))
    (label : Fin c.geometry.slots → Fin ((targetCanonicalParameters K c).N + 1)) :
    let block := chosenTargetFamilyBlock K c Z T b sc sub
    (∑ u ∈ (block.amplitudeSet label).rows,
      ‖actualRegionPiece K (excludedPlaces K c) (probeMeasures K c).haar
        (probeData K c) (targetCharacter K c) c.geometry u Z block.bin (targetBuffer K c)
        (NormForm.internalHeight Z T (targetCanonicalParameters K c).kappa)
        (targetCanonicalParameters K c).theta (targetCanonicalParameters K c).N label‖) ≤
      (targetCanonicalParameters K c).C * ((block.amplitudeSet label).rows.card : ℝ) *
        Z ^ (3 / 16 + moderateExponent block.shell (2 * block.bin - 1)
          (block.amplitudeSet label).mean 0 + c.lamB / 4) := by
  have hZ0 : (targetCanonicalParameters K c).Z0 ≤ Z := (le_max_left _ _).trans hZ
  have hZ2 : 2 ≤ Z := (le_max_right _ _).trans hZ
  have hZ1 : 1 ≤ Z := by linarith
  have hd := actualShell_range (by linarith : 1 < Z) b.1
  have hspec := (targetCanonicalParameters_spec K c).2.2.2.2
    Z T hZ0 hT hTcap (shellExponent Z (1 / 16) b.1.val) hd.1
    (hd.2.le.trans (targetUpper_range K c).2) (targetModerateSource K c Z) b.2
  have hb := ((hspec.2 sc sub).2 label).2
  apply hb.trans
  apply mul_le_mul_of_nonneg_left
  · apply Real.rpow_le_rpow_of_exponent_le hZ1
    have hm : targetLoss K c ≤ c.lamB := min_le_right _ _
    exact add_le_add le_rfl
      (div_le_div_of_nonneg_right hm (by norm_num : (0 : ℝ) ≤ 4))
  · exact mul_nonneg (targetCanonicalParameters_positive K c).2.2.1.le (Nat.cast_nonneg _)

/-- The whole boundary is the initial contour minus the computed block
for every member of this same retained family. Recipes may vary by block;
no row is added or removed between the two contour sums. -/
theorem chosenTargetFamily_boundary_eq_initial_sub_blocks
    (Z T : ℝ) (hZ : 0 < Z) (hT : 1 ≤ T)
    (sc : ChosenTargetFamilyIndex K c Z T →
      (Fin c.geometry.slots → Fin ((targetCanonicalParameters K c).N + 1)) → ℝ → ℕ)
    (sub : (b : ChosenTargetFamilyIndex K c Z T) →
      (label : Fin c.geometry.slots → Fin ((targetCanonicalParameters K c).N + 1)) →
      (t : ℝ) → Fin (sc b label t) → WitnessSubdivision (FrequencyRow K (places K c))) :
    targetDyadicBoundary K c (fun Z _T => targetModerateSource K c Z)
      (targetCanonicalParameters K c).kappa (targetUpper K c) Z T =
      ∑ b : ChosenTargetFamilyIndex K c Z T,
        let block := chosenTargetFamilyBlock K c Z T b (sc b) (sub b)
        (∑ u ∈ chosenTargetFamilyRows K c Z T b,
          rowContourBox K (places K c) (probeMeasures K c).haar (probeData K c)
            (targetCharacter K c) (targetEuler K c) c.geometry (rayFilter K c) u Z
            (NormForm.internalHeight Z T (targetCanonicalParameters K c).kappa)
            (c.family.B + 20 * targetBuffer K c)
            (1 - block.bin - 6 * targetBuffer K c) (17 / 50)) - block.value := by
  unfold targetDyadicBoundary HighBinDyadicBoundary.dyadicBoundary
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j _
  change (∑ k ∈ canonicalChoices K (places K c) (probeData K c) (targetCharacter K c)
    (targetCompanions K c) (targetModerateSource K c Z) c.family.B (targetBuffer K c)
    (targetBuffer_pos K c) (targetBoundary_lower K c) (targetCommonBoundary K c)
    Z T (targetCanonicalParameters K c).kappa (shellExponent Z (1 / 16) j.val),
    HighBinCanonicalBoundary.maskedBoundaryPiece K (excludedPlaces K c)
      (probeMeasures K c).haar (probeData K c) (targetCharacter K c) (targetCompanions K c)
      c.geometry c.family.B (targetBuffer K c) (targetBuffer_pos K c)
      (targetBoundary_lower K c) (targetCommonBoundary K c) (rayFilter K c)
      (targetModerateSource K c Z) Z T (targetCanonicalParameters K c).kappa
      (shellExponent Z (1 / 16) j.val) k) = _
  rw [← Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro k _
  exact maskedBoundaryPiece_eq_initial_sub_block K (excludedPlaces K c)
    (probeMeasures K c).haar (probeData K c) (targetCharacter K c) (targetCompanions K c)
    (targetModerateSource K c Z) c.family.B (targetBuffer K c) (targetBuffer_pos K c)
    (targetBoundary_lower K c) (targetCommonBoundary K c) (one_mem_targetCompanions K c)
    c.geometry (targetBuffer_small K c) c.family.B_upper Z T
    (targetCanonicalParameters K c).kappa (shellExponent Z (1 / 16) j.val)
    (targetCanonicalParameters K c).theta (targetCanonicalParameters K c).N hZ hT k
    (sc ⟨j, k⟩) (sub ⟨j, k⟩)

/-- The whole boundary attached to exactly this source and internal
height exponent satisfies the original power-height-tail proposition. -/
theorem chosenTargetFamily_boundary :
    PowerHeightTailBound (targetDyadicBoundary K c
      (fun Z _T => targetModerateSource K c Z)
      (targetCanonicalParameters K c).kappa (targetUpper K c)) :=
  targetDyadicBoundary_powerHeightTailBound K c
    (fun Z _T => targetModerateSource K c Z)
    (targetCanonicalParameters K c).kappa (targetUpper K c)
    (targetUpper_range K c).1 (targetUpper_range K c).2

end HeckeSkeleton.HighBinCanonicalTarget

#print axioms HeckeSkeleton.HighBinCanonicalTarget.chosenTargetFamily_count
#print axioms HeckeSkeleton.HighBinCanonicalTarget.chosenTargetFamily_value_eq_final
#print axioms HeckeSkeleton.HighBinCanonicalTarget.chosenTargetFamily_normForm
#print axioms HeckeSkeleton.HighBinCanonicalTarget.chosenTargetFamily_boundary_eq_initial_sub_blocks
#print axioms HeckeSkeleton.HighBinCanonicalTarget.chosenTargetFamily_boundary
