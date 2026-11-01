import HeckeSkeleton.Moments.MOM_ENGINE_INTEGRATION.ActualLocalInputs
import Expansion.ActualProbeContext

/-!
# The existing physical measures instantiate the complete local input

The actual target uses its already selected arithmetic context and the
same normalized local Haar family as the physical probe. Canonical
Borel structures and auxiliary adelic Haar measures discharge the
original Fourier constructors. These are explicit constructions, not
extra hypotheses on the original moment theorem.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical NumberField

namespace HeckeSkeleton.Moments.EngineInduction.Source

open NumberField IsDedekindDomain DedekindZetaZeroFree MeasureTheory
open HeckeGeneral.Characters HeckeGeneral.Arithmetic HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton.Global
open Expansion.Project EngineStep

variable {K : Type} [Field K] [NumberField K] (c : TargetContext K)

/-- All Fourier measure and arithmetic instances come from the
original target. Only the original single-character volume primitive
is passed on to its actual source constructor. -/
theorem actualRecipeScalarInputs_canonicalMeasures
    (volume : ∀ b : CanonicalPrimitiveEngineChoices.Box,
      CanonicalLiteralExceptionalPaidSource.VolumePrimitive
        (targetCharacter K c) (canonicalDetectorTheta K (targetCharacter K c))
        (Set.Icc b.lo b.hi)) :
    Nonempty (RecipeScalarLocalInput.{0} (expansionRecipeRaw K c)
      (fun _ _ i => i.noSlots) (fun _ _ _ => True)) ∧
    Nonempty (RecipeScalarLocalInput.{0} (expansionRecipeRaw K c)
      (fun _ _ i => i) (fun _ _ i => pairedCapacityFor i ∧ i.selected.Nonempty)) := by
  letI : IsPrincipalIdealRing (axiomChoice K c).A.R := (axiomChoice K c).C.principal
  letI : IsTotallyComplex K :=
    Expansion.ActualProbeContext.totallyComplex K (axiomChoice K c)
  letI : ∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K) :=
    Expansion.ActualProbeContext.localCompletionSpace K
  letI : ∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K) :=
    Expansion.ActualProbeContext.localCompletionBorel K
  letI : ∀ v : HeightOneSpectrum (𝓞 K),
      (Expansion.ActualProbeContext.allLocalMeasures K v).IsAddHaarMeasure :=
    Expansion.ActualProbeContext.allLocalMeasures_isAddHaar K
  letI : MeasurableSpace (FiniteAdeleRing (𝓞 K) K) :=
    Expansion.ActualProbeContext.finiteAdeleSpace K
  letI : BorelSpace (FiniteAdeleRing (𝓞 K) K) :=
    Expansion.ActualProbeContext.finiteAdeleBorel K
  letI : (Expansion.ActualProbeContext.finiteAdeleMeasure K).IsAddHaarMeasure :=
    Expansion.ActualProbeContext.finiteAdeleMeasure_isAddHaar K
  letI : MeasurableSpace (AdeleRing (𝓞 K) K) :=
    Expansion.ActualProbeContext.adeleSpace K
  letI : BorelSpace (AdeleRing (𝓞 K) K) :=
    Expansion.ActualProbeContext.adeleBorel K
  letI : (Expansion.ActualProbeContext.adeleMeasure K).IsAddHaarMeasure :=
    Expansion.ActualProbeContext.adeleMeasure_isAddHaar K
  letI : MeasurableSpace (sLocalNormOneGroup K
      ((axiomChoice K c).A.Sf : Set (HeightOneSpectrum (𝓞 K)))) :=
    Expansion.ActualProbeContext.normOneSpace K (axiomChoice K c)
  letI : BorelSpace (sLocalNormOneGroup K
      ((axiomChoice K c).A.Sf : Set (HeightOneSpectrum (𝓞 K)))) :=
    Expansion.ActualProbeContext.normOneBorel K (axiomChoice K c)
  letI : MeasurableSpace (mixedEmbedding.mixedSpace K)ˣ := borel _
  letI : BorelSpace (mixedEmbedding.mixedSpace K)ˣ := ⟨rfl⟩
  letI : ∀ v : ((axiomChoice K c).A.Sf : Set (HeightOneSpectrum (𝓞 K))),
      MeasurableSpace (v.val.adicCompletion K)ˣ := fun _ => borel _
  letI : ∀ v : ((axiomChoice K c).A.Sf : Set (HeightOneSpectrum (𝓞 K))),
      BorelSpace (v.val.adicCompletion K)ˣ := fun _ => ⟨rfl⟩
  letI : MeasurableSpace (ℕ × Bool) := ⊤
  letI : MeasurableSingletonClass (ℕ × Bool) := by
    constructor
    intro n
    trivial
  exact actualRecipeScalarInputs_of_volume c
    (Expansion.ActualProbeContext.allLocalMeasures K)
    (Expansion.ActualProbeContext.finiteAdeleMeasure K)
    (Expansion.ActualProbeContext.adeleMeasure K) volume

end HeckeSkeleton.Moments.EngineInduction.Source

#print axioms HeckeSkeleton.Moments.EngineInduction.Source.actualRecipeScalarInputs_canonicalMeasures
