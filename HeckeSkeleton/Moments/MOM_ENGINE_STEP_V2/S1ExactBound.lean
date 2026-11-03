import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.FirstSourceContracts

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# S1: exact source decomposition at the physical divisor cutoffs

The parent calibration first gives the actual masked orbital source.
The common-support partition retains its principal-character mask.
Each resulting source is split at its own divisor-dependent cutoff;
its exact discrepancy is kept until the independent tail estimate.
The remaining finite transform is paid by the genuine zero term and
the original two Cauchy energies, for every positive normalization.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.S1ExactBound

open EngineStep EngineInduction EngineInduction.Source
open NumberField IsDedekindDomain MeasureTheory DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical.ActualGramMajorantDraft

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

/-- The full principal mask belongs to the actual common-support
source, including when the initial source mask is empty. -/
def sourceSeries (s : FirstSource call p) (v : s.CommonLabel) : ℂ :=
  ∑ i ∈ (s.source v).leftColumns,
    ∑ j ∈ (s.source v).rightColumns,
      ((s.source v).pairs i j).maskedSeries
        (sIntegerFiniteTestFunction K (Arithmetic.data c).Sf
          (rowBallFiniteFamily K (Arithmetic.data c).Sf 1))
        s.radius (s.source v).mask

/-- This is the finite transform with the same row carrier used by
`FirstBlockDirectData`; each mask divisor keeps its own cutoff. -/
def sourceTransform (s : FirstSource call p) (v : s.CommonLabel) : ℂ :=
  (s.source v).divisorTransform (Arithmetic.localMeasures (K := K))
    (Arithmetic.different c) (rowBallFiniteFamily K (Arithmetic.data c).Sf 1)

def exactTail (s : FirstSource call p) : ℝ :=
  (s.fiber : ℝ) * ∑ v : s.CommonLabel,
    ‖sourceSeries s v - sourceTransform s v‖

/-- Exact first source inequality. No tail constant or analytic
majorant is selected, and the positive normalizers are arbitrary. -/
theorem pairedStageEnergy_le (s : FirstSource call p) (N : s.Normalization) :
    pairedStageEnergy call.node.centered call.localizedData
      call.workingParameters call.base 0
      (call.base ^ call.workingComparison₁) (call.base ^ call.workingComparison₂) ≤
      (s.fiber : ℝ) * s.zeroCost (Arithmetic.different c) + exactTail s +
        (s.fiber : ℝ) * s.linearizedCost (Arithmetic.different c) N := by
  have hp := parent_orbital_source_bound
    (K := K) (S := (Arithmetic.data c).Sf) (Γ := Arithmetic.unitSubgroup c)
    call.node.centered call.localizedData call.workingParameters call.base 0
    (call.base ^ call.workingComparison₁) (call.base ^ call.workingComparison₂)
    s.columns _
    (sIntegerFiniteTestFunction K (Arithmetic.data c).Sf
      (rowBallFiniteFamily K (Arithmetic.data c).Sf 1))
    (continuous_sIntegerFiniteTestFunction K (Arithmetic.data c).Sf _
      (rowBallFiniteFamily_locallyConstant K (Arithmetic.data c).Sf 1))
    (hasCompactSupport_sIntegerFiniteTestFunction K (Arithmetic.data c).Sf _
      (rowBallFiniteFamily_compactSupport K (Arithmetic.data c).Sf 1))
    s.radius s.mask s.fiber s.calibration
  rw [common_support_original_sources (Arithmetic.units_are_sixth c)
    (Arithmetic.context c) s.columns s.columns s.ideal s.ideal
    s.generator s.generator s.generates s.generates
    (fun DE hDE => canonicalFirstCommonBlock (Arithmetic.context c)
      s.columns s.columns s.ideal s.ideal DE hDE)] at hp
  change pairedStageEnergy call.node.centered call.localizedData
    call.workingParameters call.base 0
    (call.base ^ call.workingComparison₁) (call.base ^ call.workingComparison₂) ≤
      (s.fiber : ℝ) * (∑ v : s.CommonLabel, sourceSeries s v).re at hp
  apply hp.trans
  dsimp only [exactTail]
  rw [← mul_add, ← mul_add]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg s.fiber)
  rw [Complex.re_sum]
  change (∑ v : s.CommonLabel, (sourceSeries s v).re) ≤
    (∑ v : s.CommonLabel, ‖(s.source v).zeroTerm
      (Arithmetic.localMeasures (K := K)) (Arithmetic.different c)
      (rowBallFiniteFamily K (Arithmetic.data c).Sf 1)‖) +
    (∑ v : s.CommonLabel, ‖sourceSeries s v - sourceTransform s v‖) +
    ∑ v : s.CommonLabel, ∑ D : ((s.block v).mask s.mask).powerset,
      (s.pieces v D).linearizedCost (Arithmetic.different c)
        (N.left v D) (N.right v D)
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro v _
  have htransform := canonical_first_block_transform_bound
    (Arithmetic.units_are_sixth c) (Arithmetic.localMeasures (K := K))
    (Arithmetic.context c) s.columns s.columns s.ideal s.ideal v
    s.profiles (Arithmetic.different c)
    (rowBallFiniteFamily K (Arithmetic.data c).Sf 1)
    s.mask s.radius (p.firstCutoff call) (p.firstCutoff_one call) (s.charts v)
  have hlinear :
      (∑ D : ((s.block v).mask s.mask).powerset,
        (s.charts v D).kernelCost (Arithmetic.different c) s.mask
          (p.firstCutoff call) (p.firstCutoff_one call)) ≤
      ∑ D : ((s.block v).mask s.mask).powerset,
        (s.pieces v D).linearizedCost (Arithmetic.different c)
          (N.left v D) (N.right v D) := by
    apply Finset.sum_le_sum
    intro D _
    exact (s.pieces v D).kernelCost_le_linearized
      (Arithmetic.different c) (N.left v D) (N.right v D)
      (N.left_pos v D) (N.right_pos v D)
  have hre := Complex.re_le_norm (sourceSeries s v - sourceTransform s v)
  rw [Complex.sub_re] at hre
  have hfinite := Complex.re_le_norm (sourceTransform s v)
  change ‖sourceTransform s v‖ ≤
    ‖(s.source v).zeroTerm (Arithmetic.localMeasures (K := K))
      (Arithmetic.different c) (rowBallFiniteFamily K (Arithmetic.data c).Sf 1)‖ +
      ∑ D : ((s.block v).mask s.mask).powerset,
        (s.charts v D).kernelCost (Arithmetic.different c) s.mask
          (p.firstCutoff call) (p.firstCutoff_one call) at htransform
  have hfinite' := hfinite.trans
    (htransform.trans (add_le_add le_rfl hlinear))
  linarith only [hre, hfinite']

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.S1ExactBound

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.S1ExactBound.pairedStageEnergy_le
