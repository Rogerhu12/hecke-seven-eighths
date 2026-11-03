import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.CallData
import Expansion.ActualProbeContext
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.MovingOriginalArithmeticAtoms

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The arithmetic background of the source tasks

These are aliases of the original target's arithmetic choice and the
existing self-dual local measures. They select no transformed source,
prime pool, correlation, child or estimate.
-/

noncomputable section

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.Arithmetic

open NumberField IsDedekindDomain MeasureTheory DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.Analysis.ActualSIntegerMoments
open scoped Classical

variable {K : Type} [Field K] [NumberField K]

abbrev choice (c : TargetContext K) := axiomChoice K c
abbrev data (c : TargetContext K) := (choice c).A
abbrev embedding (c : TargetContext K) := complexEmbedding K c
abbrev context (c : TargetContext K) := (choice c).C

theorem principal (c : TargetContext K) : IsPrincipalIdealRing (data c).R :=
  (context c).principal

theorem totallyComplex (c : TargetContext K) : IsTotallyComplex K :=
  Expansion.ActualProbeContext.totallyComplex K (choice c)

theorem different (c : TargetContext K) (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ (data c).Sf) :
    HeckeGeneral.Characters.localDifferentExponent K v = 0 :=
  (choice c).different v hv

abbrev unitSubgroup (c : TargetContext K) :=
  sixthPowerSUnitSubgroup K ((data c).Sf : Set (HeightOneSpectrum (𝓞 K)))

abbrev Orbit (c : TargetContext K) :=
  SIntegerOrbits K ((data c).Sf : Set (HeightOneSpectrum (𝓞 K))) (unitSubgroup c)

theorem units_are_sixth (c : TargetContext K) :
    ∀ u : unitSubgroup c, ∃ v : (data c).U, u.val = v ^ 6 := by
  intro u
  obtain ⟨v, hv⟩ := u.property
  exact ⟨v, hv.symm⟩

attribute [local instance]
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar
  Expansion.ActualProbeContext.finiteAdeleSpace
  Expansion.ActualProbeContext.finiteAdeleBorel
  Expansion.ActualProbeContext.finiteAdeleMeasure_isAddHaar
  Expansion.ActualProbeContext.adeleSpace
  Expansion.ActualProbeContext.adeleBorel
  Expansion.ActualProbeContext.adeleMeasure_isAddHaar

abbrev localMeasures := Expansion.ActualProbeContext.allLocalMeasures K
abbrev finiteMeasure := Expansion.ActualProbeContext.finiteAdeleMeasure K
abbrev fullMeasure := Expansion.ActualProbeContext.adeleMeasure K

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.Arithmetic
