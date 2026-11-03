import HeckeSkeleton.SourceData

/-!
# Compatibility names for the canonical fixed source

The shared source types and all polynomial energies are owned by
`HeckeSkeleton.SourceData`. This file contains only transparent names for
that interface, preserving the existing induction-module API while using
exactly the same source, indices, models, row exponents, and finite sectors.
No source structure or model family is defined a second time here.

The complete source is fixed before any uniform-bound constants. None of
these aliases selects `actualMomentSourceData`, `expansionRecipeRaw`, or
another unfinished actual source. The actual specialization remains in
the separate skeleton-integration module.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction.Source

open NumberField
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global

variable (K : Type) [Field K] [NumberField K]

abbrev MomentSourceData (c : TargetContext K) :=
  _root_.HeckeSkeleton.MomentSourceData K c

abbrev SourceMomentIndexFor (c : TargetContext K)
    (S : MomentSourceData K c) (Z T : ℝ) :=
  _root_.HeckeSkeleton.SourceMomentIndexFor K c S Z T

variable {K} {c : TargetContext K} {S : MomentSourceData K c} {Z T : ℝ}

abbrev momentBlock (i : SourceMomentIndexFor K c S Z T) :=
  _root_.HeckeSkeleton.momentBlockFor i

abbrev momentAmplitude (i : SourceMomentIndexFor K c S Z T) :=
  _root_.HeckeSkeleton.momentAmplitudeFor i

abbrev momentWitness (i : SourceMomentIndexFor K c S Z T) :=
  _root_.HeckeSkeleton.momentWitnessFor i

abbrev momentBase (i : SourceMomentIndexFor K c S Z T) : ℝ :=
  _root_.HeckeSkeleton.momentBaseFor i

abbrev rowWidth (i : SourceMomentIndexFor K c S Z T) : ℝ :=
  _root_.HeckeSkeleton.rowWidthFor i

abbrev selectedLength (i : SourceMomentIndexFor K c S Z T) : ℝ :=
  _root_.HeckeSkeleton.selectedLengthFor i

abbrev SourceMomentIndexFor.noSlots (i : SourceMomentIndexFor K c S Z T) :
    SourceMomentIndexFor K c S Z T :=
  _root_.HeckeSkeleton.SourceMomentIndexFor.noSlots i

abbrev inverseParameters (i : SourceMomentIndexFor K c S Z T) : RealParameters :=
  _root_.HeckeSkeleton.inverseParametersFor i

abbrev pairedParameters (i : SourceMomentIndexFor K c S Z T) : RealParameters :=
  _root_.HeckeSkeleton.pairedParametersFor i

abbrev inverseCapacity (i : SourceMomentIndexFor K c S Z T) : Prop :=
  _root_.HeckeSkeleton.inverseCapacityFor i

abbrev pairedCapacity (i : SourceMomentIndexFor K c S Z T) : Prop :=
  _root_.HeckeSkeleton.pairedCapacityFor i

variable (K)

abbrev SourceMomentModelsFor (c : TargetContext K) (S : MomentSourceData K c) :=
  _root_.HeckeSkeleton.SourceMomentModelsFor K c S

variable {K}

abbrev inverseModel (M : SourceMomentModelsFor K c S)
    (i : SourceMomentIndexFor K c S Z T) (s : SixthUnitClasses K (places K c)) :=
  _root_.HeckeSkeleton.inverseModelFor M i s

abbrev pairedModel (M : SourceMomentModelsFor K c S)
    (i : SourceMomentIndexFor K c S Z T) (s : SixthUnitClasses K (places K c)) :=
  _root_.HeckeSkeleton.pairedModelFor M i s

abbrev unmarkedModel (M : SourceMomentModelsFor K c S)
    (i : SourceMomentIndexFor K c S Z T) (s : SixthUnitClasses K (places K c)) :=
  _root_.HeckeSkeleton.unmarkedModelFor M i s

abbrev markedModelEnergy (M : SourceMomentModelsFor K c S)
    (i : SourceMomentIndexFor K c S Z T) : ℝ :=
  _root_.HeckeSkeleton.markedModelEnergyFor M i

abbrev pairedModelEnergy (M : SourceMomentModelsFor K c S)
    (i : SourceMomentIndexFor K c S Z T) : ℝ :=
  _root_.HeckeSkeleton.pairedModelEnergyFor M i

abbrev unmarkedBallEnergy
    (d : MomentData K c.family.omega (targetCharacter K c)) (U D : ℝ) : ℝ :=
  _root_.HeckeSkeleton.unmarkedBallEnergy (K := K) (c := c) d U D

abbrev amplifiedModelEnergy (M : SourceMomentModelsFor K c S)
    (i : SourceMomentIndexFor K c S Z T) : ℝ :=
  _root_.HeckeSkeleton.amplifiedModelEnergyFor M i

abbrev UniformMomentBound
    (energy power : ∀ Z T, SourceMomentIndexFor K c S Z T → ℝ)
    (eligible : ∀ Z T, SourceMomentIndexFor K c S Z T → Prop) : Prop :=
  _root_.HeckeSkeleton.UniformMomentBoundFor (K := K) (c := c) energy power eligible

abbrev PairedPrimeProductBound (M : SourceMomentModelsFor K c S) (κ : ℝ) : Prop :=
  _root_.HeckeSkeleton.PairedPrimeProductBoundFor M κ

end HeckeSkeleton.Moments.EngineInduction.Source
