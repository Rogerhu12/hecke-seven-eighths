import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SourceFrame
import Expansion.ActualProbeContext
import ThetaGlobal.GlobalSameChoice
import DedekindZetaZeroFree.CharacterSums.Gauss.FiniteSupportReciprocityCancellation

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The unchanged target arithmetic and its actual Haar measures

All physical stages use Base's one arithmetic choice. The coefficient
dictionary is selected by the already proved same-recipe binding;
the generators remain the context's allowed generators. The measures
are the existing self-dual local measures and auxiliary adelic Haar
measures, with their existing Borel structures.
-/

noncomputable section

namespace HeckeSkeleton.Moments.EngineStepV2.TargetArithmetic

open NumberField IsDedekindDomain MeasureTheory DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Global
open scoped Classical

variable {K : Type} [Field K] [NumberField K]

abbrev choice (c : TargetContext K) := axiomChoice K c
abbrev arithmetic (c : TargetContext K) := (choice c).A
abbrev embedding (c : TargetContext K) := complexEmbedding K c
abbrev context (c : TargetContext K) := (choice c).C

theorem principalRing (c : TargetContext K) : IsPrincipalIdealRing (arithmetic c).R :=
  (context c).principal

theorem totallyComplex (c : TargetContext K) : IsTotallyComplex K :=
  Expansion.ActualProbeContext.totallyComplex K (choice c)

theorem different (c : TargetContext K) (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ (arithmetic c).Sf) :
    HeckeGeneral.Characters.localDifferentExponent K v = 0 :=
  (choice c).different v hv

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

def coefficients (c : TargetContext K) : ComparisonPoissonCoefficientData K (arithmetic c) :=
  (ThetaGlobal.GlobalSameChoice.exists_binding_with_chosen_recipe
    (arithmetic c) (embedding c) (choice c).η (choice c).hS (context c)).choose

theorem coefficients_recipe (c : TargetContext K) :
    GlobalPairCancel.HasArithmeticRecipes (arithmetic c) (embedding c)
      (choice c).hS (context c).correction.B (coefficients c) := by
  sorry

end HeckeSkeleton.Moments.EngineStepV2.TargetArithmetic
