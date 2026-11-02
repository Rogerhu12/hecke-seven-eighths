import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.S5ClassIdeals

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Constructing the nominal class geometry from the original trace

The original pool supplies the error-prime lower window. The retained
scale comes from the same physical source, and one actual live row
supplies the class radicals. No descendant geometry is an input.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.S5Proof

open EngineStep EngineInduction.Source
open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

theorem expansion_error_prime_lower
    {F : FirstPresentation call p} {family : FirstCauchyFamily F}
    (hfamily : family.Realizes) (expansion : PoolExpansion family)
    (hexpansion : expansion.Realizes) (i : Fin expansion.count)
    (e : AmplifierValuation) (q : HeightOneSpectrum (𝓞 K))
    (htag : (expansion.source i).first.tag = .error e q) :
    call.base ^ (recipeInductionSigma c / 6) ≤ (Ideal.absNorm q.asIdeal : ℝ) := by
  cases expansion with
  | direct =>
    change (family.source i).first.tag = .error e q at htag
    rw [hfamily.tag i] at htag
    cases htag
  | pooled pool count index sources =>
    rcases hexpansion with ⟨_, _, horigin⟩
    have ho := horigin i
    change (sources i).first.tag = .error e q at htag
    cases hk : (index i).2 with
    | inl unit =>
      simp only [PoolPresentation.Origin, hk] at ho
      rcases ho with ⟨_, _, _, _, _, _, _, hfirst⟩
      have ht := congrArg FirstCoordinates.tag hfirst
      change (sources i).first.tag = .main at ht
      rw [ht] at htag
      cases htag
    | inr qe =>
      simp only [PoolPresentation.Origin, hk] at ho
      rcases ho with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ht, _, _⟩
      obtain ⟨_, hq⟩ := OriginalNominalTag.error.inj (ht.symm.trans htag)
      have hn := pool.pool.norm_lower qe.1.val qe.1.property
      simpa only [hq, show (recipeInductionSigma c / 3) / 2 =
        recipeInductionSigma c / 6 by ring] using hn

variable (trace : SourceTrace call p) (realized : trace.Realizes)

include realized in
theorem source_windows (key : SecondClassKey trace.second) :
    key.source.physical.Windows := by
  change (trace.second.source key.sourceIndex).physical.Windows
  rw [realized.second.physical key.sourceIndex]
  exact realized.poolWindows key.sourceIndex

include realized in
theorem source_error_prime_lower (key : SecondClassKey trace.second)
    (e : AmplifierValuation) (q : HeightOneSpectrum (𝓞 K))
    (htag : key.source.physical.first.tag = .error e q) :
    call.base ^ (recipeInductionSigma c / 6) ≤ (Ideal.absNorm q.asIdeal : ℝ) := by
  apply expansion_error_prime_lower realized.cauchy trace.expansion
    realized.expansion key.sourceIndex e q
  rw [← realized.second.physical key.sourceIndex]
  exact htag

def classWitness (key : SecondClassKey trace.second) (active : key.Active) : key.R.live :=
  ⟨active.2.2.2.choose, active.2.2.2.choose_spec⟩

def classGeometry (key : SecondClassKey trace.second) (active : key.Active) : ClassGeometry key where
  nominal side := {
    ideals := sideIdeals key (classWitness trace key active) side
    tag := key.source.physical.first.tag
    retainedScale := key.source.physical.first.retainedScale
    retainedScale_pos := key.source.physical.first.retainedScale_pos
    supportError := 4 * p.loss
    supportError_nonneg := mul_nonneg (by norm_num) p.loss_pos.le
    retained_upper := by
      rw [sideIdeals_firstFrequency]
      exact (source_windows trace realized key).retained_upper active.2.1
    error_prime_lower := source_error_prime_lower trace realized key }

theorem classGeometry_first (key : SecondClassKey trace.second) (active : key.Active) (side : Bool) :
    ((classGeometry trace realized key active).nominal side).ideals.first.val =
      key.source.physical.first.selected.val :=
  sideIdeals_first key (classWitness trace key active) side

theorem classGeometry_opposite (key : SecondClassKey trace.second) (active : key.Active) (side : Bool) :
    ((classGeometry trace realized key active).nominal side).ideals.opposite.val =
      key.source.physical.first.opposite.val :=
  sideIdeals_opposite key (classWitness trace key active) side

theorem classGeometry_complementary
    (key : SecondClassKey trace.second) (active : key.Active) (side : Bool) :
    ((classGeometry trace realized key active).nominal side).ideals.complementary.val =
      key.source.physical.first.complementary.val :=
  sideIdeals_complementary key (classWitness trace key active) side

theorem classGeometry_second (key : SecondClassKey trace.second) (active : key.Active) (side : Bool) :
    ((classGeometry trace realized key active).nominal side).ideals.second.val =
      if side then key.common.val.2 else key.common.val.1 :=
  sideIdeals_second key (classWitness trace key active) side

theorem classGeometry_secondOpposite
    (key : SecondClassKey trace.second) (active : key.Active) (side : Bool) :
    ((classGeometry trace realized key active).nominal side).ideals.secondOpposite.val =
      if side then key.common.val.1 else key.common.val.2 :=
  sideIdeals_secondOpposite key (classWitness trace key active) side

theorem classGeometry_unitPart (key : SecondClassKey trace.second) (active : key.Active)
    (side : Bool) (h : key.R.live) :
    ((classGeometry trace realized key active).nominal side).ideals.unitPart.val =
      (unitFrequencyRadical (Arithmetic.context c) key.R.primes
        key.R.leftMultiplicity key.R.rightMultiplicity (key.R.frequency h.val)).val :=
  sideIdeals_unitPart key (realized.second.stage key.sourceIndex)
    (classWitness trace key active) h side

theorem classGeometry_nonunitPart (key : SecondClassKey trace.second) (active : key.Active)
    (side : Bool) (h : key.R.live) :
    ((classGeometry trace realized key active).nominal side).ideals.nonunitPart.val =
      (nonunitFrequencyRadical (Arithmetic.context c) key.R.primes
        key.R.leftMultiplicity key.R.rightMultiplicity (key.R.frequency h.val)).val :=
  sideIdeals_nonunitPart key (realized.second.stage key.sourceIndex)
    (classWitness trace key active) h side

theorem classGeometry_correlation (key : SecondClassKey trace.second) (active : key.Active)
    (side : Bool) (h : key.R.live) :
    ‖key.R.correlation h.val‖ ≤
      call.base ^ (((classGeometry trace realized key active).nominal side).skeleton.g₂ -
        ((classGeometry trace realized key active).nominal side).skeleton.t₂) := by
  let G := (classGeometry trace realized key active).nominal side
  change ‖key.R.correlation h.val‖ ≤
    call.base ^ (idealLogLength call.base (gcd G.ideals.second.val G.ideals.secondOpposite.val) -
      idealLogLength call.base G.ideals.unitPart.val)
  rw [Real.rpow_sub call.base_pos,
    rpow_idealLogLength call.base call.domain.scale _
      (gcd_ne_zero_of_left (nonZeroDivisors.coe_ne_zero G.ideals.second)),
    rpow_idealLogLength call.base call.domain.scale _
      (nonZeroDivisors.coe_ne_zero G.ideals.unitPart)]
  rw [show G.ideals.unitPart.val = _ from classGeometry_unitPart trace realized key active side h]
  have hb := actual_complete_correlation_gcd_radical_bound_of_generates
    (Arithmetic.context c) key.R.primes key.R.primes_injective
    key.R.leftMultiplicity key.R.rightMultiplicity key.block.left_positive
    key.R.leftGenerator key.R.rightGenerator key.R.leftGenerates key.R.rightGenerates
    (key.R.frequency h.val)
  cases side <;>
    simpa [G, classGeometry, sideIdeals, leftIdeals,
      OriginalNominalIdeals.swapSecond, exteriorMomentIdeal,
      ActualSecondCorrelationRows.correlation, SArithmeticData.exteriorNorm,
      DedekindZetaZeroFree.idealNorm, gcd_comm] using hb

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.S5Proof

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.S5Proof.classGeometry
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.S5Proof.classGeometry_correlation
