import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.S5GeometryConstruction
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.EmptyGaussMask

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The physical frequency window before and after actual extraction

Only nonzero original profiles enter the finite-source radius maximum.
Their two original column bounds cost eight losses; the positive second
cutoff costs at most one more. The published twelve-loss window leaves
room for this exact calculation. The gcd and nonunit factor is divided
out by the base's actual extracted row, not by a new chosen ideal.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.S5Proof

open EngineStep EngineInduction.Source
open NumberField IsDedekindDomain MeasureTheory DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

def columnCenter (source : PhysicalSource call p) : ℝ :=
  call.workingParameters.n₁ + call.workingParameters.n₂ + call.workingParameters.z -
    idealLogLength call.base source.first.selected.val - source.first.tag.removedLength call.base

def physicalFrequencyCenter (source : PhysicalSource call p) : ℝ :=
  2 * columnCenter source - Real.log source.first.retainedScale / Real.log call.base -
    source.enlargement

theorem retained_rpow (source : PhysicalSource call p) :
    call.base ^ (Real.log source.first.retainedScale / Real.log call.base) =
      source.first.retainedScale := by
  rw [Real.rpow_def_of_pos call.base_pos]
  have hl : Real.log call.base ≠ 0 := (Real.log_pos call.domain.scale).ne'
  have he : Real.log call.base *
      (Real.log source.first.retainedScale / Real.log call.base) =
        Real.log source.first.retainedScale := by field_simp [hl]
  rw [he, Real.exp_log source.first.retainedScale_pos]

theorem second_radius_rpow (source : SecondSource call p) (realized : source.Realizes) :
    source.stage.radius.val =
      call.base ^ (-Real.log source.physical.first.retainedScale / Real.log call.base -
        source.physical.enlargement) := by
  rw [realized.radius]
  conv_lhs => rw [← retained_rpow source.physical, ← Real.rpow_add call.base_pos]
  rw [show -Real.log source.physical.first.retainedScale / Real.log call.base -
      source.physical.enlargement =
    0 - (Real.log source.physical.first.retainedScale / Real.log call.base +
      source.physical.enlargement) by ring,
    Real.rpow_sub call.base_pos, Real.rpow_zero, one_div]

theorem second_pair_inverseRadius (source : SecondSource call p) (DE : source.CommonLabel)
    (i : source.physical.Column) (hi : i ∈ (source.stage.sources DE).leftColumns)
    (j : source.physical.Column) (hj : j ∈ (source.stage.sources DE).rightColumns)
    (D : Finset (HeightOneSpectrum (Arithmetic.data c).R)) :
    (((source.stage.sources DE).pairs i j).dualRadius source.stage.radius D).val⁻¹ =
      source.stage.radius.val *
        (sIntegerElementNorm K ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K)))
          (sIntegerMaskGenerator K
            ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K))) D)).val *
        (Arithmetic.data c).exteriorNorm (source.physical.source.ideal i) *
        (Arithmetic.data c).exteriorNorm (source.physical.source.ideal j) := by
  let b := source.block DE
  let L := generatedOriginalColumn (σ := Arithmetic.embedding c)
    (Arithmetic.units_are_sixth c) (b.secondLeftIdeal i)
    (engineAllowedGenerator (Arithmetic.context c) b.commonLeftIdeal * b.leftGenerator i)
    (b.secondLeft_generates (Arithmetic.context c) i)
  let R := generatedOriginalColumn (σ := Arithmetic.embedding c)
    (Arithmetic.units_are_sixth c) (b.secondRightIdeal j)
    (engineAllowedGenerator (Arithmetic.context c) b.commonRightIdeal * b.rightGenerator j)
    (b.secondRight_generates (Arithmetic.context c) j)
  have hl := CanonicalSecondLogChart.generated_columnNorm (σ := Arithmetic.embedding c)
    (Arithmetic.units_are_sixth c) (b.secondLeftIdeal i) _
    (b.secondLeft_generates (Arithmetic.context c) i)
  have hr := CanonicalSecondLogChart.generated_columnNorm (σ := Arithmetic.embedding c)
    (Arithmetic.units_are_sixth c) (b.secondRightIdeal j) _
    (b.secondRight_generates (Arithmetic.context c) j)
  change CanonicalSecondLogChart.columnNorm L =
    (Arithmetic.data c).exteriorNorm (b.secondLeftIdeal i) at hl
  change CanonicalSecondLogChart.columnNorm R =
    (Arithmetic.data c).exteriorNorm (b.secondRightIdeal j) at hr
  rw [b.secondLeftIdeal_eq source.physical.source.columns i hi] at hl
  rw [b.secondRightIdeal_eq source.physical.source.columns j hj] at hr
  change ((source.stage.radius.val *
    (sIntegerElementNorm K ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K)))
      (sIntegerMaskGenerator K
        ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K))) D)).val *
    (sIntegerElementNorm K ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K)))
      ⟨L.modulus * R.modulus, mul_ne_zero L.nonzero R.nonzero⟩).val)⁻¹)⁻¹ = _
  rw [inv_inv, CanonicalSecondLogChart.pair_modulus_norm, hl, hr]
  ring

theorem second_physicalCutoff_bound (source : SecondSource call p)
    (realized : source.Realizes) (windows : source.physical.Windows)
    (DE : source.CommonLabel) :
    (source.stage.sources DE).physicalCutoff ≤
      call.base ^ (physicalFrequencyCenter source.physical + 12 * p.loss) := by
  have hradii : ∀ i ∈ (source.stage.sources DE).leftColumns,
      ∀ j ∈ (source.stage.sources DE).rightColumns,
      ((source.stage.sources DE).pairs i j).profile ≠ 0 →
      ∀ D ∈ (source.stage.sources DE).mask.powerset,
      (((source.stage.sources DE).pairs i j).dualRadius
        (source.stage.sources DE).radius D).val⁻¹ ≤
      call.base ^ (physicalFrequencyCenter source.physical + 8 * p.loss) := by
    intro i hi j hj hprofile D hD
    have hi0 : source.physical.source.coefficient i ≠ 0 := by
      intro hz
      apply hprofile
      change (source.physical.source.coefficient i *
        star (source.physical.source.coefficient j)) • source.stage.profile = 0
      rw [hz, zero_mul, zero_smul]
    have hj0 : source.physical.source.coefficient j ≠ 0 := by
      intro hz
      apply hprofile
      change (source.physical.source.coefficient i *
        star (source.physical.source.coefficient j)) • source.stage.profile = 0
      rw [hz, star_zero, mul_zero, zero_smul]
    have hi' : i ∈ source.physical.source.columns := (Finset.mem_filter.mp hi).1
    have hj' : j ∈ source.physical.source.columns := (Finset.mem_filter.mp hj).1
    have hni := windows.column_upper i hi' hi0
    have hnj := windows.column_upper j hj' hj0
    have hD0 : D = ∅ := by
      change D ∈ source.stage.mask.powerset at hD
      rw [realized.mask] at hD
      exact (Finset.mem_powerset.mp hD).antisymm (Finset.empty_subset _)
    rw [second_pair_inverseRadius source DE i hi j hj D, hD0,
      sIntegerMaskGenerator_empty_norm, mul_one]
    have hm := mul_le_mul hni hnj
      ((Arithmetic.data c).exteriorNorm_pos (source.physical.source.ideal j)).le
      (Real.rpow_pos_of_pos call.base_pos _).le
    calc
      source.stage.radius.val *
          (Arithmetic.data c).exteriorNorm (source.physical.source.ideal i) *
          (Arithmetic.data c).exteriorNorm (source.physical.source.ideal j) ≤
        source.stage.radius.val *
          (call.base ^ (columnCenter source.physical + 4 * p.loss) *
            call.base ^ (columnCenter source.physical + 4 * p.loss)) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left hm source.stage.radius.property.le
      _ = call.base ^ (physicalFrequencyCenter source.physical + 8 * p.loss) := by
        rw [second_radius_rpow source realized,
          ← Real.rpow_add call.base_pos, ← Real.rpow_add call.base_pos]
        congr 1
        unfold physicalFrequencyCenter
        ring
  have hb := (source.stage.sources DE).physicalCutoff_le_supported
    (call.base ^ (physicalFrequencyCenter source.physical + 8 * p.loss))
    (Real.rpow_pos_of_pos call.base_pos _).le hradii
  apply hb.trans
  change source.stage.cutoff *
    call.base ^ (physicalFrequencyCenter source.physical + 8 * p.loss) ≤ _
  rw [realized.cutoff, SourceParameters.secondCutoff, ← Real.rpow_add call.base_pos]
  apply (Real.rpow_le_rpow_left_iff call.domain.scale).2
  have hl := p.loss_pos
  have hc := p.secondCutoff_small
  linarith

variable (trace : SourceTrace call p) (realized : trace.Realizes)

include realized in
theorem live_originalNorm_bound (key : SecondClassKey trace.second) (h : key.R.live) :
    (Arithmetic.data c).exteriorNorm (key.R.originalIdeal h.val) ≤
      call.base ^ (physicalFrequencyCenter key.source.physical + 12 * p.loss) := by
  have hr := (Finset.mem_filter.mp h.property).1
  have hfinite := (Finset.mem_filter.mp hr).1
  have hcut := ((key.source.stage.sources key.common).mem_rows h.val).mp hfinite
  have hg := key.R.generates h.val hr
  have hp : (Arithmetic.data c).Generates (key.R.originalIdeal h.val) h.val.out.val := by
    refine ⟨h.val.out.property, ?_⟩
    simpa only [SecondClassKey.R, SecondSource.rows, SecondBlockProfileChart.actualRows,
      Ideal.span_singleton_neg] using hg.2
  have hn := generates_sIntegerElementNorm (key.R.originalIdeal h.val) h.val.out.val hp
  have he : (Arithmetic.data c).exteriorNorm (key.R.originalIdeal h.val) =
      (sIntegerOrbitNorm K ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K)))
        (Arithmetic.unitSubgroup c) h.val).val := by
    rw [← sIntegerOrbitNorm_out]
    exact hn.symm
  rw [he]
  exact hcut.trans (second_physicalCutoff_bound key.source
    (realized.second.stage key.sourceIndex) (source_windows trace realized key) key.common)

theorem classGeometry_enlargement (key : SecondClassKey trace.second) (active : key.Active)
    (side : Bool) :
    ((classGeometry trace realized key active).nominal side).enlargement =
      key.source.physical.enlargement := by
  cases side <;>
    dsimp [classGeometry, sideIdeals, leftIdeals, OriginalNominalIdeals.swapSecond,
      OriginalNominalGeometry.enlargement, OriginalNominalGeometry.shiftedCommon,
      OriginalNominalGeometry.retainedLength, OriginalNominalIdeals.firstFrequency,
      PhysicalSource.enlargement, PhysicalSource.firstFrequency]
  all_goals congr 2 <;> ring

set_option maxHeartbeats 800000 in
theorem classGeometry_normFactor (key : SecondClassKey trace.second) (active : key.Active)
    (side : Bool) (h : key.R.live) :
    key.R.normFactor (Arithmetic.context c) h.val =
      call.base ^ (((classGeometry trace realized key active).nominal side).skeleton.g₂ +
        ((classGeometry trace realized key active).nominal side).skeleton.V) := by
  let G := (classGeometry trace realized key active).nominal side
  change key.R.normFactor (Arithmetic.context c) h.val =
    call.base ^ (idealLogLength call.base (gcd G.ideals.second.val G.ideals.secondOpposite.val) +
      idealLogLength call.base G.ideals.nonunitPart.val)
  rw [Real.rpow_add call.base_pos,
    rpow_idealLogLength call.base call.domain.scale _
      (gcd_ne_zero_of_left (nonZeroDivisors.coe_ne_zero G.ideals.second)),
    rpow_idealLogLength call.base call.domain.scale _
      (nonZeroDivisors.coe_ne_zero G.ideals.nonunitPart)]
  rw [show G.ideals.nonunitPart.val = _ from
    classGeometry_nonunitPart trace realized key active side h]
  rw [show G.ideals.second.val = _ from classGeometry_second trace realized key active side,
    show G.ideals.secondOpposite.val = _ from
      classGeometry_secondOpposite trace realized key active side]
  change
    (Ideal.absNorm (gcd (primePowerProduct key.R.primes key.R.leftMultiplicity).val
      (primePowerProduct key.R.primes key.R.rightMultiplicity).val) : ℝ) *
        (Ideal.absNorm (nonunitFrequencyRadical (Arithmetic.context c) key.R.primes
          key.R.leftMultiplicity key.R.rightMultiplicity (key.R.frequency h.val)).val : ℝ) = _
  have hleft : (primePowerProduct key.R.primes key.R.leftMultiplicity).val =
      key.common.val.1 := key.block.common_left
  have hright : (primePowerProduct key.R.primes key.R.rightMultiplicity).val =
      key.common.val.2 := key.block.common_right
  rw [hleft, hright]
  cases side <;>
    simp only [Bool.false_eq_true, ↓reduceIte, gcd_comm]

theorem classGeometry_rowWindow (key : SecondClassKey trace.second) (active : key.Active)
    (side : Bool) (h : key.R.live) :
    idealNorm K (key.R.extractedRow (Arithmetic.context c) h).momentIdeal ≤
      call.base ^ (((classGeometry trace realized key active).nominal side).skeleton.nominalRow +
        12 * p.loss) := by
  apply (key.R.extractedRow (Arithmetic.context c) h).norm_le
  apply (live_originalNorm_bound trace realized key h).trans_eq
  rw [classGeometry_normFactor trace realized key active side h, ← Real.rpow_add call.base_pos]
  congr 1
  let G := (classGeometry trace realized key active).nominal side
  change physicalFrequencyCenter key.source.physical + 12 * p.loss =
    G.skeleton.g₂ + G.skeleton.V + (G.skeleton.nominalRow + 12 * p.loss)
  unfold NominalChildGeometry.nominalRow
  change physicalFrequencyCenter key.source.physical + 12 * p.loss =
    G.skeleton.g₂ + G.skeleton.V +
      (2 * (call.workingParameters.n₁ + call.workingParameters.n₂ + call.workingParameters.z -
        idealLogLength call.base G.ideals.first.val -
        key.source.physical.first.tag.removedLength call.base) -
        Real.log key.source.physical.first.retainedScale / Real.log call.base -
        G.enlargement - G.skeleton.g₂ - G.skeleton.V + 12 * p.loss)
  rw [show G.ideals.first.val = key.source.physical.first.selected.val from
    classGeometry_first trace realized key active side,
    show G.enlargement = key.source.physical.enlargement from
    classGeometry_enlargement trace realized key active side]
  unfold physicalFrequencyCenter columnCenter
  ring

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.S5Proof

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.S5Proof.second_physicalCutoff_bound
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.S5Proof.classGeometry_rowWindow
