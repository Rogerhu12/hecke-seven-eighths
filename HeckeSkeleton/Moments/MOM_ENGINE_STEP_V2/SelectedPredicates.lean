import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SelectedStages


set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option quotPrecheck false

/-!
# The exceptional test reads the literal original row character

Both signs and all four amplifier tags retain the original first
factor and their actual prime power. The test is fixed before either
passive allocation, Fourier parameter or normalized child is selected.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2

open EngineStep EngineInduction
open NumberField IsDedekindDomain MeasureTheory DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments

attribute [local instance]
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar
  Expansion.ActualProbeContext.finiteAdeleSpace
  Expansion.ActualProbeContext.finiteAdeleBorel
  Expansion.ActualProbeContext.finiteAdeleMeasure_isAddHaar
  selectedPrincipal selectedComplex selectedNormOneSpace selectedNormOneBorel
  selectedInfinityUnitSpace selectedInfinityUnitBorel selectedLocalUnitSpace selectedLocalUnitBorel

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {frame : SourceFrame} {Cp Hp : ℝ}
variable {hCp : 0 < Cp} {hminimum : (selectedSchedule c frame).minimumCp ≤ Cp}
variable {hHp : 0 ≤ Hp}

namespace SelectedSource

variable (request : Request c frame Cp Hp hCp hminimum hHp) (frequency : ℝ × ℝ)

/-- The first moving phases are the generators already used by the
original signed first-divisor transform. -/
def directPredicates :
    ActualDirectFirstSource.SecondStages.CoverHybridPredicates (directPrepared request frequency) (atlas request frequency) :=
  fun DE D => {
    left := fun S χ => (ActualGaussStage.literalHybridPredicates (s := (ActualGaussStage.gated (s := (ActualGaussStage.supported (s := ((directStages request frequency DE D).left S χ)))))))
      ((FirstBlockDirectData.leftSourceCover (p := ((firstSource request frequency).pieces DE D))) (atlas request frequency) S χ)
      ((FirstBlockDirectData.leftSourceCover (p := ((firstSource request frequency).pieces DE D))) (atlas request frequency) S χ)
      (probeData K c) (momentRowCharacters K c)
      (CanonicalLiteralActualCharacters.unamplifiedPhases
        ((FirstCommonCharacterBlock.literalLeftFixed (b := ((firstSource request frequency).block DE))) D.val)
        (CanonicalLiteralFirstPhase.leftElement (TargetArithmetic.context c) ((firstSource request frequency).block DE).primes
          ((firstSource request frequency).block DE).leftMultiplicity ((firstSource request frequency).block DE).rightMultiplicity
          (sIntegerMaskGenerator K (places K c) D.val).val)
        ((FirstCommonCharacterBlock.literalLeftFixed_generates (b := ((firstSource request frequency).block DE))) (TargetArithmetic.context c) D.val))
      (recipe request frequency).moving (recipe request frequency).correction (model request frequency).data.theta
    right := fun S χ => (ActualGaussStage.literalHybridPredicates (s := (ActualGaussStage.gated (s := (ActualGaussStage.supported (s := ((directStages request frequency DE D).right S χ)))))))
      ((FirstBlockDirectData.rightSourceCover (p := ((firstSource request frequency).pieces DE D))) (atlas request frequency) S χ)
      ((FirstBlockDirectData.rightSourceCover (p := ((firstSource request frequency).pieces DE D))) (atlas request frequency) S χ)
      (probeData K c) (momentRowCharacters K c)
      (CanonicalLiteralActualCharacters.unamplifiedPhases
        ((FirstCommonCharacterBlock.literalRightFixed (b := ((firstSource request frequency).block DE))) D.val)
        (CanonicalLiteralFirstPhase.rightElement (TargetArithmetic.context c) ((firstSource request frequency).block DE).primes
          ((firstSource request frequency).block DE).leftMultiplicity ((firstSource request frequency).block DE).rightMultiplicity
          (sIntegerMaskGenerator K (places K c) D.val).val)
        ((FirstCommonCharacterBlock.literalRightFixed_generates (b := ((firstSource request frequency).block DE))) (TargetArithmetic.context c) D.val))
      (recipe request frequency).moving (recipe request frequency).correction (model request frequency).data.theta }

/-- These predicates read the original row character, including the
actual amplifier frequency before passive mask reduction. -/
def pooledPredicates :
    EngineStep.ActualFirstSource.SecondStages.CoverHybridPredicates (pooledPrepared request frequency) (pooledAtlas request frequency) :=
  fun DE D => {
    left := fun S χ => {
      main := (ActualGaussStage.literalHybridPredicates (s := (ActualGaussStage.gated (s := (ActualGaussStage.supported (s := (((pooledStages request frequency DE D).left S χ).main)))))))
        ((((pooledSource request frequency).pools DE D).leftSourceCovers (pooledAtlas request frequency) S χ).main)
        ((((pooledSource request frequency).pools DE D).leftSourceCovers (pooledAtlas request frequency) S χ).main) (probeData K c) (momentRowCharacters K c)
        (CanonicalLiteralActualCharacters.unamplifiedPhases
          ((FirstCommonCharacterBlock.literalLeftFixed (b := ((pooledSource request frequency).block DE))) D.val)
          (CanonicalLiteralFirstPhase.leftElement (TargetArithmetic.context c) ((pooledSource request frequency).block DE).primes
            ((pooledSource request frequency).block DE).leftMultiplicity ((pooledSource request frequency).block DE).rightMultiplicity
            (sIntegerMaskGenerator K (places K c) D.val).val)
          ((FirstCommonCharacterBlock.literalLeftFixed_generates (b := ((pooledSource request frequency).block DE))) (TargetArithmetic.context c) D.val))
        (recipe request frequency).moving (recipe request frequency).correction (model request frequency).data.theta
      one p := (ActualGaussStage.literalHybridPredicates (s := (ActualGaussStage.gated (s := (ActualGaussStage.supported (s := (((pooledStages request frequency DE D).left S χ).one p)))))))
        ((((pooledSource request frequency).pools DE D).leftSourceCovers (pooledAtlas request frequency) S χ).residual p 1)
        ((((pooledSource request frequency).pools DE D).leftSourceCovers (pooledAtlas request frequency) S χ).residual p 1) (probeData K c) (momentRowCharacters K c)
        (CanonicalLiteralActualCharacters.amplifiedPhases (TargetArithmetic.context c)
          ((FirstCommonCharacterBlock.literalLeftFixed (b := ((pooledSource request frequency).block DE))) D.val)
          (CanonicalLiteralFirstPhase.leftElement (TargetArithmetic.context c) ((pooledSource request frequency).block DE).primes
            ((pooledSource request frequency).block DE).leftMultiplicity ((pooledSource request frequency).block DE).rightMultiplicity
            (sIntegerMaskGenerator K (places K c) D.val).val)
          ((FirstCommonCharacterBlock.literalLeftFixed_generates (b := ((pooledSource request frequency).block DE))) (TargetArithmetic.context c) D.val) p.val 1)
        (recipe request frequency).moving (recipe request frequency).correction (model request frequency).data.theta
      six p := (ActualGaussStage.literalHybridPredicates (s := (ActualGaussStage.gated (s := (ActualGaussStage.supported (s := (((pooledStages request frequency DE D).left S χ).six p)))))))
        ((((pooledSource request frequency).pools DE D).leftSourceCovers (pooledAtlas request frequency) S χ).residual p 6)
        ((((pooledSource request frequency).pools DE D).leftSourceCovers (pooledAtlas request frequency) S χ).residual p 6) (probeData K c) (momentRowCharacters K c)
        (CanonicalLiteralActualCharacters.amplifiedPhases (TargetArithmetic.context c)
          ((FirstCommonCharacterBlock.literalLeftFixed (b := ((pooledSource request frequency).block DE))) D.val)
          (CanonicalLiteralFirstPhase.leftElement (TargetArithmetic.context c) ((pooledSource request frequency).block DE).primes
            ((pooledSource request frequency).block DE).leftMultiplicity ((pooledSource request frequency).block DE).rightMultiplicity
            (sIntegerMaskGenerator K (places K c) D.val).val)
          ((FirstCommonCharacterBlock.literalLeftFixed_generates (b := ((pooledSource request frequency).block DE))) (TargetArithmetic.context c) D.val) p.val 6)
        (recipe request frequency).moving (recipe request frequency).correction (model request frequency).data.theta
      seven p := (ActualGaussStage.literalHybridPredicates (s := (ActualGaussStage.gated (s := (ActualGaussStage.supported (s := (((pooledStages request frequency DE D).left S χ).seven p)))))))
        ((((pooledSource request frequency).pools DE D).leftSourceCovers (pooledAtlas request frequency) S χ).residual p 7)
        ((((pooledSource request frequency).pools DE D).leftSourceCovers (pooledAtlas request frequency) S χ).residual p 7) (probeData K c) (momentRowCharacters K c)
        (CanonicalLiteralActualCharacters.amplifiedPhases (TargetArithmetic.context c)
          ((FirstCommonCharacterBlock.literalLeftFixed (b := ((pooledSource request frequency).block DE))) D.val)
          (CanonicalLiteralFirstPhase.leftElement (TargetArithmetic.context c) ((pooledSource request frequency).block DE).primes
            ((pooledSource request frequency).block DE).leftMultiplicity ((pooledSource request frequency).block DE).rightMultiplicity
            (sIntegerMaskGenerator K (places K c) D.val).val)
          ((FirstCommonCharacterBlock.literalLeftFixed_generates (b := ((pooledSource request frequency).block DE))) (TargetArithmetic.context c) D.val) p.val 7)
        (recipe request frequency).moving (recipe request frequency).correction (model request frequency).data.theta
    }
    right := fun S χ => {
      main := (ActualGaussStage.literalHybridPredicates (s := (ActualGaussStage.gated (s := (ActualGaussStage.supported (s := (((pooledStages request frequency DE D).right S χ).main)))))))
        ((((pooledSource request frequency).pools DE D).rightSourceCovers (pooledAtlas request frequency) S χ).main)
        ((((pooledSource request frequency).pools DE D).rightSourceCovers (pooledAtlas request frequency) S χ).main) (probeData K c) (momentRowCharacters K c)
        (CanonicalLiteralActualCharacters.unamplifiedPhases
          ((FirstCommonCharacterBlock.literalRightFixed (b := ((pooledSource request frequency).block DE))) D.val)
          (CanonicalLiteralFirstPhase.rightElement (TargetArithmetic.context c) ((pooledSource request frequency).block DE).primes
            ((pooledSource request frequency).block DE).leftMultiplicity ((pooledSource request frequency).block DE).rightMultiplicity
            (sIntegerMaskGenerator K (places K c) D.val).val)
          ((FirstCommonCharacterBlock.literalRightFixed_generates (b := ((pooledSource request frequency).block DE))) (TargetArithmetic.context c) D.val))
        (recipe request frequency).moving (recipe request frequency).correction (model request frequency).data.theta
      one p := (ActualGaussStage.literalHybridPredicates (s := (ActualGaussStage.gated (s := (ActualGaussStage.supported (s := (((pooledStages request frequency DE D).right S χ).one p)))))))
        ((((pooledSource request frequency).pools DE D).rightSourceCovers (pooledAtlas request frequency) S χ).residual p 1)
        ((((pooledSource request frequency).pools DE D).rightSourceCovers (pooledAtlas request frequency) S χ).residual p 1) (probeData K c) (momentRowCharacters K c)
        (CanonicalLiteralActualCharacters.amplifiedPhases (TargetArithmetic.context c)
          ((FirstCommonCharacterBlock.literalRightFixed (b := ((pooledSource request frequency).block DE))) D.val)
          (CanonicalLiteralFirstPhase.rightElement (TargetArithmetic.context c) ((pooledSource request frequency).block DE).primes
            ((pooledSource request frequency).block DE).leftMultiplicity ((pooledSource request frequency).block DE).rightMultiplicity
            (sIntegerMaskGenerator K (places K c) D.val).val)
          ((FirstCommonCharacterBlock.literalRightFixed_generates (b := ((pooledSource request frequency).block DE))) (TargetArithmetic.context c) D.val) p.val 1)
        (recipe request frequency).moving (recipe request frequency).correction (model request frequency).data.theta
      six p := (ActualGaussStage.literalHybridPredicates (s := (ActualGaussStage.gated (s := (ActualGaussStage.supported (s := (((pooledStages request frequency DE D).right S χ).six p)))))))
        ((((pooledSource request frequency).pools DE D).rightSourceCovers (pooledAtlas request frequency) S χ).residual p 6)
        ((((pooledSource request frequency).pools DE D).rightSourceCovers (pooledAtlas request frequency) S χ).residual p 6) (probeData K c) (momentRowCharacters K c)
        (CanonicalLiteralActualCharacters.amplifiedPhases (TargetArithmetic.context c)
          ((FirstCommonCharacterBlock.literalRightFixed (b := ((pooledSource request frequency).block DE))) D.val)
          (CanonicalLiteralFirstPhase.rightElement (TargetArithmetic.context c) ((pooledSource request frequency).block DE).primes
            ((pooledSource request frequency).block DE).leftMultiplicity ((pooledSource request frequency).block DE).rightMultiplicity
            (sIntegerMaskGenerator K (places K c) D.val).val)
          ((FirstCommonCharacterBlock.literalRightFixed_generates (b := ((pooledSource request frequency).block DE))) (TargetArithmetic.context c) D.val) p.val 6)
        (recipe request frequency).moving (recipe request frequency).correction (model request frequency).data.theta
      seven p := (ActualGaussStage.literalHybridPredicates (s := (ActualGaussStage.gated (s := (ActualGaussStage.supported (s := (((pooledStages request frequency DE D).right S χ).seven p)))))))
        ((((pooledSource request frequency).pools DE D).rightSourceCovers (pooledAtlas request frequency) S χ).residual p 7)
        ((((pooledSource request frequency).pools DE D).rightSourceCovers (pooledAtlas request frequency) S χ).residual p 7) (probeData K c) (momentRowCharacters K c)
        (CanonicalLiteralActualCharacters.amplifiedPhases (TargetArithmetic.context c)
          ((FirstCommonCharacterBlock.literalRightFixed (b := ((pooledSource request frequency).block DE))) D.val)
          (CanonicalLiteralFirstPhase.rightElement (TargetArithmetic.context c) ((pooledSource request frequency).block DE).primes
            ((pooledSource request frequency).block DE).leftMultiplicity ((pooledSource request frequency).block DE).rightMultiplicity
            (sIntegerMaskGenerator K (places K c) D.val).val)
          ((FirstCommonCharacterBlock.literalRightFixed_generates (b := ((pooledSource request frequency).block DE))) (TargetArithmetic.context c) D.val) p.val 7)
        (recipe request frequency).moving (recipe request frequency).correction (model request frequency).data.theta
    }
  }

end SelectedSource
end HeckeSkeleton.Moments.EngineStepV2

