import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SecondData
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralFixedPhases
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalMovingFactorAppend

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The finite character used by the actual exceptional split

Only the original first divisor, the one pool's actual valuation prime,
the chosen empty-mask unit and the genuine extracted second frequency
are used. All singleton and complete-row character operations are base
definitions. The theta set is exactly the original parent's theta.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep EngineInduction
open NumberField IsDedekindDomain MeasureTheory DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable {F : FirstPresentation call p} {family : FirstCauchyFamily F}

namespace FirstCauchyKey

def moving (key : FirstCauchyKey F) :=
  let b := FirstCauchyKey.block key
  let delta := sIntegerMaskGenerator K
    ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K)))
      (FirstCauchyKey.divisor key).val
  let ideal := firstPhysicalDivisorIdeal (A := Arithmetic.data c)
    (FirstCauchyKey.divisor key).val
  if FirstCauchyKey.side key then
    CanonicalLiteralFirstPhase.rightMoving (Arithmetic.context c)
      (probeData K c) (momentRowCharacters K c) b.primes
      b.leftMultiplicity b.rightMultiplicity ideal delta.val
      (originalFrequencyIdeal_generates _ delta.property)
  else
    CanonicalLiteralFirstPhase.leftMoving (Arithmetic.context c)
      (probeData K c) (momentRowCharacters K c) b.primes
      b.leftMultiplicity b.rightMultiplicity ideal delta.val
      (originalFrequencyIdeal_generates _ delta.property)

end FirstCauchyKey

namespace PoolExpansion

variable (expansion : PoolExpansion family)

def firstIndex : Fin expansion.count → Fin family.count :=
  match expansion with
  | .direct => fun i => i
  | .pooled _ _ index _ => fun i => (index i).1

def poolMoving : Fin expansion.count →
    OriginalMovingFactors (Arithmetic.data c) (probeData K c) (momentRowCharacters K c) :=
  match expansion with
  | .direct => fun _ => OriginalMovingFactors.singleton ⟨1, one_ne_zero⟩ 1
  | .pooled _ _ index _ => fun i =>
    match (index i).2 with
    | .inl _ => OriginalMovingFactors.singleton ⟨1, one_ne_zero⟩ 1
    | .inr qe => OriginalMovingFactors.singleton
        ⟨LocalFiniteSums.generator (Arithmetic.context c) qe.1.val ^ (2 * qe.2.multiplicity),
          (generator_power_generates (Arithmetic.context c) qe.1.val
            (2 * qe.2.multiplicity)).1⟩ 1

def moving (i : Fin expansion.count) :=
  (((call.localizedSource.source.recipe.moving).append
    (FirstCauchyKey.moving (family.index (expansion.firstIndex i)))).append
      (expansion.poolMoving i)).append
        (CanonicalLiteralFixedPhases.emptyDivisorMoving
          (probeData K c) (momentRowCharacters K c))

end PoolExpansion

namespace SecondSource

variable {expansion : PoolExpansion family}

def rowCharacter (source : SecondSource call p) (i : Fin expansion.count)
    (DE : source.CommonLabel) (D : source.stage.mask.powerset)
    (label : Fin ((source.stage.charts DE D).rowLabelCount + 1))
    (q : Arithmetic.Orbit c) : HeckeCharacter K :=
  let R := source.rows DE D label
  if hq : q ∈ R.live then
    let row := R.extractedRow (Arithmetic.context c) ⟨q, hq⟩
    call.localizedSource.source.recipe.correction *
      ((expansion.moving i).append
        (secondOriginalMovingFactors (probeData K c) (momentRowCharacters K c)
          (Arithmetic.context c) R.primes R.leftMultiplicity R.rightMultiplicity
          (actualNonunitPattern (Arithmetic.context c) R.primes
            R.leftMultiplicity R.rightMultiplicity (R.frequency q)))).character *
      completeIdealRowCharacter K
        ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K)))
        (probeData K c) (momentRowCharacters K c) (row.sector (probeData K c)) row.momentIdeal
  else 1

end SecondSource

end HeckeSkeleton.Moments.EngineStepV2.Blueprint
