import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SecondData
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.RawSourcePhaseIntegral

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Integrability of the original phase-dependent discrepancy

The complete masked series and every actual Poisson zero or nonzero
term are linear in the original profile. The first Fourier parameter
multiplies a pair by its unit Gram phase. All finite column, divisor,
and physical row carriers are the original ones.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails

open EngineStep NumberField IsDedekindDomain MeasureTheory DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.ThetaSkeleton.Global HeckePort.Moments

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

private theorem maskedSeries_profile_smul
    (pair : ParentPeriodicPair K (Arithmetic.data c).Sf (Arithmetic.unitSubgroup c))
    (a : ℂ) (radius : {r : ℝ // 0 < r})
    (mask : Finset (HeightOneSpectrum (Arithmetic.data c).R)) :
    ({ pair with profile := a • pair.profile } :
        ParentPeriodicPair K (Arithmetic.data c).Sf (Arithmetic.unitSubgroup c)).maskedSeries
      (sIntegerFiniteTestFunction K (Arithmetic.data c).Sf
        (rowBallFiniteFamily K (Arithmetic.data c).Sf 1)) radius mask =
      a * pair.maskedSeries
        (sIntegerFiniteTestFunction K (Arithmetic.data c).Sf
          (rowBallFiniteFamily K (Arithmetic.data c).Sf 1)) radius mask := by
  unfold ParentPeriodicPair.maskedSeries sIntegerWeightedOrbitalSeries
  dsimp only [ParentPeriodicPair.orbitWeight]
  simp only [sUnitOrbitalProfile_tensor_smul, smul_eq_mul]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro q
  ring

private theorem transformedZero_profile_smul
    (pair : ParentPeriodicPair K (Arithmetic.data c).Sf (Arithmetic.unitSubgroup c))
    (a : ℂ) (radius : {r : ℝ // 0 < r})
    (D : Finset (HeightOneSpectrum (Arithmetic.data c).R)) :
    ({ pair with profile := a • pair.profile } :
        ParentPeriodicPair K (Arithmetic.data c).Sf (Arithmetic.unitSubgroup c)).transformedZero
      (Arithmetic.localMeasures (K := K)) (Arithmetic.different c)
      (rowBallFiniteFamily K (Arithmetic.data c).Sf 1) radius D =
      a * pair.transformedZero
        (Arithmetic.localMeasures (K := K)) (Arithmetic.different c)
        (rowBallFiniteFamily K (Arithmetic.data c).Sf 1) radius D := by
  have hdual :
      sIntegerDualTensorTerm K (Arithmetic.localMeasures (K := K)) (Arithmetic.data c).Sf
          (traceSchwartzToMixed K (a • pair.profile))
          (rowBallFiniteFamily K (Arithmetic.data c).Sf 1) 0 =
        a * sIntegerDualTensorTerm K (Arithmetic.localMeasures (K := K))
          (Arithmetic.data c).Sf (traceSchwartzToMixed K pair.profile)
          (rowBallFiniteFamily K (Arithmetic.data c).Sf 1) 0 := by
    unfold sIntegerDualTensorTerm
    simp only [map_zero]
    rw [show (0 : mixedEmbedding.mixedSpace K) = traceToMixed K 0 by simp,
      fourierIntegral_traceSchwartzToMixed_traceToMixed,
      fourierIntegral_traceSchwartzToMixed_traceToMixed,
      engine_traceSchwartzFourier_smul]
    simp only [SchwartzMap.smul_apply, smul_eq_mul, mul_assoc]
  have horiginal :
      sIntegerTensorTerm K (Arithmetic.data c).Sf (traceSchwartzToMixed K (a • pair.profile))
          (rowBallFiniteFamily K (Arithmetic.data c).Sf 1) 0 =
        a * sIntegerTensorTerm K (Arithmetic.data c).Sf (traceSchwartzToMixed K pair.profile)
          (rowBallFiniteFamily K (Arithmetic.data c).Sf 1) 0 := by
    simp only [sIntegerTensorTerm, traceSchwartzToMixed_apply,
      SchwartzMap.smul_apply, smul_eq_mul, mul_assoc]
  unfold ParentPeriodicPair.transformedZero
  dsimp only
  rw [hdual, horiginal]
  ring

private theorem phase_pair_eq (source : SecondSource call p) (x : ℝ)
    (DE : source.CommonLabel) (i j : source.physical.Column) :
    ((source.phaseStage x).sources DE).pairs i j =
      { (source.stage.sources DE).pairs i j with
        profile := (jointPhase x (source.physical.firstPoint i) *
          star (jointPhase x (source.physical.firstPoint j))) •
            ((source.stage.sources DE).pairs i j).profile } := by
  have hprofile :
      (fun i j =>
        ((jointPhase x (source.physical.firstPoint i) * source.physical.source.coefficient i) *
          star (jointPhase x (source.physical.firstPoint j) *
            source.physical.source.coefficient j)) • source.stage.profile) =
      (fun i j => (jointPhase x (source.physical.firstPoint i) *
          star (jointPhase x (source.physical.firstPoint j))) •
        ((source.physical.source.coefficient i * star (source.physical.source.coefficient j)) •
          source.stage.profile)) := by
    funext i j
    rw [smul_smul, star_mul]
    congr 1
    ring
  change ((source.block DE).secondPair (Arithmetic.units_are_sixth c)
    (Arithmetic.different c) (Arithmetic.context c)
    (fun i j =>
      ((jointPhase x (source.physical.firstPoint i) * source.physical.source.coefficient i) *
        star (jointPhase x (source.physical.firstPoint j) *
          source.physical.source.coefficient j)) • source.stage.profile) i j) = _
  rw [hprofile]
  rfl

private theorem gram_phase_integrable (source : SecondSource call p)
    (i j : source.physical.Column) (a : ℂ) :
    Integrable (fun x : ℝ =>
      (jointPhase x (source.physical.firstPoint i) *
        star (jointPhase x (source.physical.firstPoint j))) * a)
      (actualFourierMeasure source.physical.firstKernel) := by
  letI := actualFourierMeasure_finite source.physical.firstKernel
  have hc : Continuous (fun x : ℝ => jointPhase x (source.physical.firstPoint i) *
      star (jointPhase x (source.physical.firstPoint j))) :=
    (continuous_jointPhase (source.physical.firstPoint i)).mul
      (continuous_jointPhase (source.physical.firstPoint j)).star
  have hi : Integrable (fun x : ℝ => a *
      (jointPhase x (source.physical.firstPoint i) *
        star (jointPhase x (source.physical.firstPoint j))))
      (actualFourierMeasure source.physical.firstKernel) := by
    apply (integrable_const a).mul_bdd (c := 1) hc.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun x => by
      simp only [norm_mul, norm_star, norm_jointPhase, one_mul, le_refl]
  simpa only [mul_comm] using hi

private theorem phase_maskedSeries_integrable (source : SecondSource call p)
    (DE : source.CommonLabel) (i j : source.physical.Column) :
    Integrable (fun x : ℝ =>
      (((source.phaseStage x).sources DE).pairs i j).maskedSeries
        (sIntegerFiniteTestFunction K (Arithmetic.data c).Sf
          (rowBallFiniteFamily K (Arithmetic.data c).Sf 1))
        source.stage.radius source.stage.mask)
      (actualFourierMeasure source.physical.firstKernel) := by
  have he : (fun x : ℝ =>
      (((source.phaseStage x).sources DE).pairs i j).maskedSeries
        (sIntegerFiniteTestFunction K (Arithmetic.data c).Sf
          (rowBallFiniteFamily K (Arithmetic.data c).Sf 1))
        source.stage.radius source.stage.mask) =
      (fun x : ℝ => (jointPhase x (source.physical.firstPoint i) *
        star (jointPhase x (source.physical.firstPoint j))) *
        ((source.stage.sources DE).pairs i j).maskedSeries
          (sIntegerFiniteTestFunction K (Arithmetic.data c).Sf
            (rowBallFiniteFamily K (Arithmetic.data c).Sf 1))
          source.stage.radius source.stage.mask) := by
    funext x
    rw [phase_pair_eq, maskedSeries_profile_smul]
  rw [he]
  exact gram_phase_integrable source i j _

private theorem phase_zeroPair_integrable (source : SecondSource call p)
    (DE : source.CommonLabel) (D : Finset (HeightOneSpectrum (Arithmetic.data c).R))
    (i j : source.physical.Column) :
    Integrable (fun x : ℝ =>
      (((source.phaseStage x).sources DE).pairs i j).transformedZero
        (Arithmetic.localMeasures (K := K)) (Arithmetic.different c)
        (rowBallFiniteFamily K (Arithmetic.data c).Sf 1) source.stage.radius D)
      (actualFourierMeasure source.physical.firstKernel) := by
  have he : (fun x : ℝ =>
      (((source.phaseStage x).sources DE).pairs i j).transformedZero
        (Arithmetic.localMeasures (K := K)) (Arithmetic.different c)
        (rowBallFiniteFamily K (Arithmetic.data c).Sf 1) source.stage.radius D) =
      (fun x : ℝ => (jointPhase x (source.physical.firstPoint i) *
        star (jointPhase x (source.physical.firstPoint j))) *
        ((source.stage.sources DE).pairs i j).transformedZero
          (Arithmetic.localMeasures (K := K)) (Arithmetic.different c)
          (rowBallFiniteFamily K (Arithmetic.data c).Sf 1) source.stage.radius D) := by
    funext x
    rw [phase_pair_eq, transformedZero_profile_smul]
  rw [he]
  exact gram_phase_integrable source i j _

private theorem phase_zeroTerm_integrable (source : SecondSource call p)
    (DE : source.CommonLabel) :
    Integrable (fun x : ℝ => ((source.phaseStage x).sources DE).zeroTerm
      (Arithmetic.localMeasures (K := K)) (Arithmetic.different c)
      (rowBallFiniteFamily K (Arithmetic.data c).Sf 1))
      (actualFourierMeasure source.physical.firstKernel) := by
  change Integrable (fun x : ℝ =>
    ∑ i ∈ (source.stage.sources DE).leftColumns,
      ∑ j ∈ (source.stage.sources DE).rightColumns, ∑ D ∈ source.stage.mask.powerset,
        (((source.phaseStage x).sources DE).pairs i j).transformedZero
          (Arithmetic.localMeasures (K := K)) (Arithmetic.different c)
          (rowBallFiniteFamily K (Arithmetic.data c).Sf 1) source.stage.radius D) _
  exact integrable_finsetSum _ (fun i _ =>
    integrable_finsetSum _ (fun j _ =>
      integrable_finsetSum _ (fun D _ => phase_zeroPair_integrable source DE D i j)))

/-- The original second additive-zero cost is integrable against the
same first Fourier measure. -/
theorem phaseZero_integrable (source : SecondSource call p) :
    Integrable (fun x : ℝ => (source.phaseStage x).rawZeroCost)
      (actualFourierMeasure source.physical.firstKernel) := by
  change Integrable (fun x : ℝ => ∑ DE : source.CommonLabel,
    ‖((source.phaseStage x).sources DE).zeroTerm
      (Arithmetic.localMeasures (K := K)) (Arithmetic.different c)
      (rowBallFiniteFamily K (Arithmetic.data c).Sf 1)‖) _
  exact integrable_finsetSum _ (fun DE _ => (phase_zeroTerm_integrable source DE).norm)

private theorem phase_transform_integrable (source : SecondSource call p)
    (DE : source.CommonLabel) :
    Integrable (fun x : ℝ => ((source.phaseStage x).sources DE).transform
      (Arithmetic.localMeasures (K := K)) (Arithmetic.different c)
      (rowBallFiniteFamily K (Arithmetic.data c).Sf 1))
      (actualFourierMeasure source.physical.firstKernel) := by
  let f : ℝ → ℂ := fun x =>
    ((source.phaseStage x).sources DE).zeroTerm
      (Arithmetic.localMeasures (K := K)) (Arithmetic.different c)
      (rowBallFiniteFamily K (Arithmetic.data c).Sf 1) +
    ∑ D ∈ source.stage.mask.powerset, ∑ q ∈ (source.stage.sources DE).rows,
      ∑ i ∈ (source.stage.sources DE).leftColumns,
        ∑ j ∈ (source.stage.sources DE).rightColumns,
          (((source.phaseStage x).sources DE).pairs i j).transformedRow
            (Arithmetic.localMeasures (K := K)) (Arithmetic.different c)
            (rowBallFiniteFamily K (Arithmetic.data c).Sf 1) source.stage.radius D q
  have hf : Integrable f (actualFourierMeasure source.physical.firstKernel) := by
    apply (phase_zeroTerm_integrable source DE).add
    exact integrable_finsetSum _ (fun D hD =>
      integrable_finsetSum _ (fun q _ =>
        integrable_finsetSum _ (fun i _ =>
          integrable_finsetSum _ (fun j _ =>
            source.stage.phase_transformedRow_integrable source.physical.firstKernel
              source.physical.firstPoint DE ⟨D, hD⟩ q i j))))
  have he : (fun x : ℝ => ((source.phaseStage x).sources DE).transform
      (Arithmetic.localMeasures (K := K)) (Arithmetic.different c)
      (rowBallFiniteFamily K (Arithmetic.data c).Sf 1)) = f := by
    funext x
    rw [FirstFiniteSource.transform_eq_common_rows]
    have hrows := source.stage.withMultiplier_rows
      (fun i => Real.fourierChar (inner ℝ x (source.physical.firstPoint i))) DE
    dsimp only [f]
    rw [hrows]
  rw [he]
  exact hf

/-- The exact masked-series minus finite-transform discrepancy is a
finite sum of integrable unit Gram phases, with unchanged physical rows. -/
theorem phaseTail_integrable (source : SecondSource call p) :
    Integrable source.phaseTail (actualFourierMeasure source.physical.firstKernel) := by
  change Integrable (fun x : ℝ => ∑ DE : source.CommonLabel,
    ‖(∑ i ∈ (source.stage.sources DE).leftColumns,
        ∑ j ∈ (source.stage.sources DE).rightColumns,
          (((source.phaseStage x).sources DE).pairs i j).maskedSeries
            (sIntegerFiniteTestFunction K (Arithmetic.data c).Sf
              (rowBallFiniteFamily K (Arithmetic.data c).Sf 1))
            source.stage.radius source.stage.mask) -
      ((source.phaseStage x).sources DE).transform
        (Arithmetic.localMeasures (K := K)) (Arithmetic.different c)
        (rowBallFiniteFamily K (Arithmetic.data c).Sf 1)‖) _
  exact integrable_finsetSum _ (fun DE _ =>
    ((integrable_finsetSum _ (fun i _ =>
      integrable_finsetSum _ (fun j _ => phase_maskedSeries_integrable source DE i j))).sub
        (phase_transform_integrable source DE)).norm)

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails.phaseZero_integrable
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails.phaseTail_integrable
