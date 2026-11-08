module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.FirstSourceContracts
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ParentOriginalAtlas
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondCommonNormalization

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# S1: the actual first source

The column dictionary, whole centered coefficient, first chart and both
signed row carriers are constructed from the original call. The complete
joint budget pays the original full support in the row radius. The row
weight bound is the maximum over precisely the retained physical rows.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.S1

open EngineStep EngineInduction EngineInduction.Source
open NumberField IsDedekindDomain MeasureTheory DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical.ActualGramMajorantDraft
open HeckePort.Moments HeckePort.Moments.MobiusRegroup
open CommonSupportMass

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar
  Expansion.ActualProbeContext.finiteAdeleSpace
  Expansion.ActualProbeContext.finiteAdeleBorel
  Expansion.ActualProbeContext.finiteAdeleMeasure_isAddHaar

variable {c : TargetContext K}

set_option backward.isDefEq.respectTransparency false in
theorem energy_eq (call : Call c) :
    pairedStageEnergy call.node.centered call.localizedData call.workingParameters
      call.base 0 (call.base ^ call.workingComparison₁) (call.base ^ call.workingComparison₂) =
      call.node.energy call.base 0 := by
  have hrows :
      pairedRows call.localizedData call.workingParameters call.base =
        pairedRows call.localizedData call.node.parameters call.base := by
    ext u
    simp only [pairedRows, Finset.mem_filter, Call.workingParameters, sub_add_cancel]
  have hworking :
      pairedStageEnergy call.node.centered call.localizedData call.workingParameters
        call.base 0 (call.base ^ call.workingComparison₁) (call.base ^ call.workingComparison₂) =
      pairedStageEnergy call.node.centered call.localizedData call.node.parameters
        call.base 0 (call.base ^ call.workingComparison₁) (call.base ^ call.workingComparison₂) := by
    unfold pairedStageEnergy
    apply Finset.sum_congr hrows
    intro u _
    rfl
  rw [hworking]
  have hlocal := localizeOriginalParent_pairedStageEnergy call.node.data call.node.parameters
    call.node.centered call.base 0 (call.base ^ call.workingComparison₁)
    (call.base ^ call.workingComparison₂)
  apply hlocal.trans
  change pairedStageEnergy call.node.centered call.node.data call.node.parameters
      call.base 0 (call.base ^ call.workingComparison₁) (call.base ^ call.workingComparison₂) =
    pairedStageEnergy call.node.centered call.node.data call.node.parameters
      call.base 0 (call.base ^ call.node.comparison₁) (call.base ^ call.node.comparison₂)
  cases hc : call.node.centered with
  | false => simp only [pairedStageEnergy_uncentered]
  | true => simp only [Call.workingComparison₁, Call.workingComparison₂, hc, ite_true]

def radius (call : Call c) : {r : ℝ // 0 < r} :=
  ⟨(Arithmetic.data c).exteriorNorm call.oldSupport /
      call.base ^ (call.node.parameters.m + call.node.parameters.q),
    div_pos ((Arithmetic.data c).exteriorNorm_pos _)
      (Real.rpow_pos_of_pos call.base_pos _)⟩

theorem radius_eq (call : Call c) :
    (radius call).val = call.base ^ (-call.workingParameters.m) := by
  have hs : call.base ^ call.supportLength =
      (Arithmetic.data c).exteriorNorm call.oldSupport := by
    exact rpow_idealLogLength call.base call.domain.scale call.oldSupport.val
      call.oldSupport.property.1
  change (Arithmetic.data c).exteriorNorm call.oldSupport /
      call.base ^ (call.node.parameters.m + call.node.parameters.q) = _
  rw [← hs, ← Real.rpow_sub call.base_pos]
  congr 1
  change call.supportLength - (call.node.parameters.m + call.node.parameters.q) =
    -(call.node.parameters.m + call.node.parameters.q - call.supportLength)
  ring

theorem row_originalIdeal (call : Call c)
    (u : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hu : u ∈ pairedRows call.localizedData call.workingParameters call.base) :
    (ProbeOrbitNormSum.principalExterior (Arithmetic.data c)
      (call.workingRaw.rowMap u).out).val = u.val := by
  exact call.localizedSource.source.recipe.arithmeticAtoms_originalIdeal PUnit.unit u
    (((call.localizedData.rows_spec _ u).mp (Finset.mem_filter.mp hu).1).1)

set_option backward.isDefEq.respectTransparency false in
theorem row_window (call : Call c)
    (u : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hu : u ∈ pairedRows call.localizedData call.workingParameters call.base) :
    (radius call).val *
      (sIntegerOrbitNorm K ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K)))
        (Arithmetic.unitSubgroup c) (call.workingRaw.rowMap u)).val ≤ 1 := by
  have ha := ((call.localizedData.rows_spec _ u).mp (Finset.mem_filter.mp hu).1).1
  have hb := call.localizedSource.source.recipe.effectiveMovingMaskRecipe_jointBudget
    call.base (call.node.parameters.m + call.node.parameters.q)
    call.source.localizedFullJointBudget PUnit.unit u ha
  have hs := call.localizedSource.source.recipe.effectiveMovingMaskRecipe_support u
  rw [hs] at hb
  change idealNorm K u * (Arithmetic.data c).exteriorNorm call.oldSupport ≤
    call.base ^ (call.node.parameters.m + call.node.parameters.q) at hb
  rw [parent_orbit_norm_of_originalIdeal _ u (row_originalIdeal call u hu)]
  change (Arithmetic.data c).exteriorNorm call.oldSupport /
    call.base ^ (call.node.parameters.m + call.node.parameters.q) * idealNorm K u ≤ 1
  calc
    _ = (idealNorm K u * (Arithmetic.data c).exteriorNorm call.oldSupport) /
        call.base ^ (call.node.parameters.m + call.node.parameters.q) := by ring
    _ ≤ 1 := (div_le_iff₀ (Real.rpow_pos_of_pos call.base_pos _)).mpr
      (by simpa only [one_mul] using hb)

def profile (call : Call c) (i j : call.workingRaw.Column) :
    SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ :=
  (call.workingValues.coefficient call.node.centered i *
    star (call.workingValues.coefficient call.node.centered j)) •
      CanonicalRowBall.archTest K (Arithmetic.data c).Sf 1

abbrev Common (call : Call c) :=
  commonSupportPool call.workingRaw.exteriorColumns call.workingRaw.exteriorColumns
    (fun i => (call.workingRaw.columnExterior i).val)
    (fun j => (call.workingRaw.columnExterior j).val)

def block (call : Call c) (v : Common call) :=
  canonicalFirstCommonBlock (Arithmetic.context c)
    call.workingRaw.exteriorColumns call.workingRaw.exteriorColumns
    call.workingRaw.columnExterior call.workingRaw.columnExterior v.val v.property

abbrev Divisor (call : Call c) (v : Common call) :=
  ((block call v).mask ∅).powerset

def chart (call : Call c) (p : SourceParameters c) (v : Common call)
    (D : Divisor call v) :
    FirstBlockProfileChart (E := ℝ) (Arithmetic.units_are_sixth c)
      (Arithmetic.localMeasures (K := K)) (block call v) (Arithmetic.context c)
      call.workingRaw.exteriorColumns call.workingRaw.exteriorColumns (profile call)
      (rowBallFiniteFamily K (Arithmetic.data c).Sf 1) (radius call) D.val := by
  letI : IsTotallyComplex K := Arithmetic.totallyComplex c
  letI : MeasurableSpace (mixedEmbedding.mixedSpace K)ˣ := borel _
  letI : BorelSpace (mixedEmbedding.mixedSpace K)ˣ := ⟨rfl⟩
  letI : ∀ v : ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K))),
      MeasurableSpace (v.val.adicCompletion K)ˣ := fun _ => borel _
  letI : ∀ v : ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K))),
      BorelSpace (v.val.adicCompletion K)ˣ := fun _ => ⟨rfl⟩
  exact FirstBlockProfileChart.canonicalLogWithCoefficients
    (Arithmetic.units_are_sixth c) (Arithmetic.localMeasures (K := K))
    (Arithmetic.finiteMeasure (K := K)) (block call v) (Arithmetic.context c)
    call.workingRaw.exteriorColumns call.workingRaw.exteriorColumns
    (CanonicalRowBall.archTest K (Arithmetic.data c).Sf 1)
    (call.workingValues.coefficient call.node.centered)
    (call.workingValues.coefficient call.node.centered)
    (rowBallFiniteFamily K (Arithmetic.data c).Sf 1)
    (rowBallFiniteFamily_locallyConstant K (Arithmetic.data c).Sf 1)
    (rowBallFiniteFamily_compactSupport K (Arithmetic.data c).Sf 1)
    (radius call) D.val p.tilt p.tilt_pos p.tilt_half

def finiteSource (call : Call c) (p : SourceParameters c) (v : Common call) :=
  (block call v).finiteSource (Arithmetic.units_are_sixth c) (Arithmetic.context c)
    call.workingRaw.exteriorColumns call.workingRaw.exteriorColumns (profile call)
    ∅ (radius call) (p.firstCutoff call) (p.firstCutoff_one call)

def leftData (call : Call c) (v : Common call)
    (rows : Finset (Arithmetic.Orbit c)) :
    DirectGaussData (Arithmetic.context c) call.workingRaw.Column := by
  let b := block call v
  refine {
    rows := rows.image (fun q => q.out.val)
    row_nonzero := ?_
    columns := b.leftColumns call.workingRaw.exteriorColumns
    ideal := b.leftResidual
    generator := b.leftGenerator
    generates := b.left_generates
    allowed := ?_ }
  · intro h hh
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hh
    exact q.out.property
  · intro i _
    obtain ⟨u, hu, ha⟩ :=
      (canonicalFirstCommonBlock_allowed (Arithmetic.context c)
        call.workingRaw.exteriorColumns call.workingRaw.exteriorColumns
        call.workingRaw.columnExterior call.workingRaw.columnExterior v.val v.property).1 i
    have he : u = Units.mk0 (b.leftGenerator i : K)
        (by exact_mod_cast (b.left_generates i).1) := Units.ext hu
    simpa only [← he] using ha

def rightData (call : Call c) (v : Common call)
    (rows : Finset (Arithmetic.Orbit c)) :
    DirectGaussData (Arithmetic.context c) call.workingRaw.Column := by
  let b := block call v
  refine {
    rows := rows.image (fun q => -q.out.val)
    row_nonzero := ?_
    columns := b.rightColumns call.workingRaw.exteriorColumns
    ideal := b.rightResidual
    generator := b.rightGenerator
    generates := b.right_generates
    allowed := ?_ }
  · intro h hh
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hh
    exact neg_ne_zero.mpr q.out.property
  · intro i _
    obtain ⟨u, hu, ha⟩ :=
      (canonicalFirstCommonBlock_allowed (Arithmetic.context c)
        call.workingRaw.exteriorColumns call.workingRaw.exteriorColumns
        call.workingRaw.columnExterior call.workingRaw.columnExterior v.val v.property).2 i
    have he : u = Units.mk0 (b.rightGenerator i : K)
        (by exact_mod_cast (b.right_generates i).1) := Units.ext hu
    simpa only [← he] using ha

def piece (call : Call c) (p : SourceParameters c) (v : Common call)
    (D : Divisor call v) :
    FirstBlockDirectData (chart call p v D) ∅ (p.firstCutoff call) (p.firstCutoff_one call) := by
  let rows := (finiteSource call p v).divisorRows D.val
  exact {
    leftData := leftData call v rows
    rightData := rightData call v rows
    left_columns := rfl
    right_columns := rfl
    left_ideal := rfl
    right_ideal := rfl
    left_generator := rfl
    right_generator := rfl
    left_rows := Finset.Subset.refl _
    right_rows := Finset.Subset.refl _
    weightBound := ((rows.sup (fun q => ‖(chart call p v D).weight q‖₊) : NNReal) : ℝ)
    weight_nonneg := NNReal.coe_nonneg _
    weight_bound := fun q hq => by
      exact_mod_cast (Finset.le_sup (f := fun q => ‖(chart call p v D).weight q‖₊) hq) }

def source (call : Call c) (p : SourceParameters c) : FirstSource call p := by
  have g := CanonicalRowBall.chart
    (pairedRows call.localizedData call.workingParameters call.base)
    call.workingRaw.rowMap (radius call) 1 ∅ 1
    (row_window call) (fun _ _ => by simp [sIntegerOrbitAvoidanceMask])
    (parent_rowMap_fibres_le_one_of_originalIdeal
      (pairedRows call.localizedData call.workingParameters call.base)
      call.workingRaw.rowMap (row_originalIdeal call))
  exact {
    Column := call.workingRaw.Column
    columns := call.workingRaw.exteriorColumns
    ideal := call.workingRaw.columnExterior
    generator i := engineAllowedGenerator (Arithmetic.context c) (call.workingRaw.columnExterior i)
    generates i := engineAllowedGenerator_generates (Arithmetic.context c) (call.workingRaw.columnExterior i)
    profiles := profile call
    radius := radius call
    mask := ∅
    fiber := 1
    charts := chart call p
    pieces := piece call p
    calibration := call.workingValues.actualExteriorCalibrationOfAtomPhases
      (raw := call.workingRaw) (σ := Arithmetic.embedding c) (Arithmetic.units_are_sixth c)
      (fun I _ q => EngineInduction.actualProbeOrbitSexticEvaluation_eq_actualIdealResidue c I q)
      (fun I _ q => EngineInduction.actualProbeOrbitSexticEvaluation_eq_actualIdealResidue c I q)
      (fun _ pr _ q => EngineInduction.actualProbeOrbitSexticEvaluation_eq_actualIdealResidue
        c (momentPrimeIdeal K pr) q)
      g
      (continuous_sIntegerFiniteTestFunction K (Arithmetic.data c).Sf _
        (rowBallFiniteFamily_locallyConstant K (Arithmetic.data c).Sf 1))
      (hasCompactSupport_sIntegerFiniteTestFunction K (Arithmetic.data c).Sf _
        (rowBallFiniteFamily_compactSupport K (Arithmetic.data c).Sf 1))
      call.node.centered
      (fun i => engineAllowedGenerator (Arithmetic.context c) (call.workingRaw.columnExterior i))
      (fun i => engineAllowedGenerator_generates (Arithmetic.context c) (call.workingRaw.columnExterior i)) }

def presentation (call : Call c) (p : SourceParameters c) : FirstPresentation call p where
  source := source call p
  index := Equiv.refl _

theorem presentation_realizes (call : Call c) (p : SourceParameters c)
    (active : call.Active) : (presentation call p).Realizes := by
  refine {
    active := active
    columns := ?_
    ideal := fun _ => rfl
    generator := fun _ => rfl
    profile := rfl
    radius := radius_eq call
    mask := rfl
    fiber := rfl
    chart := fun _ _ => HEq.rfl
    leftRows := fun _ _ => rfl
    rightRows := fun _ _ => rfl
    weight := fun _ _ => rfl }
  exact Finset.map_refl

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.S1

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.S1.presentation_realizes
