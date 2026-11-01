import HeckeSkeleton.Moments.MOM_ENGINE_INTEGRATION.ActualStrictFamily

/-!
# Actual strict and reflection sources give the local scalar input

The original source preparation selects its fixed support range and
reflection order. The genuine engine's finite volume orders select its
backward Euler schedule, then the finite child Schwartz coefficient is
paid by the original source coefficient. The complete strict family is
constructed here and supplied to the existing scalar assembly.

All remaining analytic information is a supported single-character
volume theorem on each fixed positive box, before any moving source.
No completed engine, local scalar estimate or final moment bound is
assumed by this assembly.
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
local notation "AA" => (axiomChoice K c).A
local notation "CC" => (axiomChoice K c).C

variable [IsPrincipalIdealRing (AA).R]
variable [MeasurableSpace (sLocalNormOneGroup K ((AA).Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K ((AA).Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable (muLocal : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (muLocal v).IsAddHaarMeasure]
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
variable (muFinite : Measure (FiniteAdeleRing (𝓞 K) K)) [muFinite.IsAddHaarMeasure]
variable [IsTotallyComplex K]
variable [MeasurableSpace (mixedEmbedding.mixedSpace K)ˣ]
  [BorelSpace (mixedEmbedding.mixedSpace K)ˣ]
variable [∀ v : ((AA).Sf : Set (HeightOneSpectrum (𝓞 K))),
  MeasurableSpace (v.val.adicCompletion K)ˣ]
variable [∀ v : ((AA).Sf : Set (HeightOneSpectrum (𝓞 K))),
  BorelSpace (v.val.adicCompletion K)ˣ]
variable [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
variable (muAdele : Measure (AdeleRing (𝓞 K) K)) [muAdele.IsAddHaarMeasure]


variable [MeasurableSpace (ℕ × Bool)] [MeasurableSingletonClass (ℕ × Bool)]
variable (volume : ∀ b : CanonicalPrimitiveEngineChoices.Box,
  CanonicalLiteralExceptionalPaidSource.VolumePrimitive
    (targetCharacter K c) (canonicalDetectorTheta K (targetCharacter K c))
    (Set.Icc b.lo b.hi))

/-- The original actual-source preparation and actual single-step
producer supply both scalar local inputs, with one common finite order
schedule and with no downstream callback left to the caller. -/
theorem actualRecipeScalarInputs_of_volume :
    Nonempty (RecipeScalarLocalInput.{0} (expansionRecipeRaw K c)
      (fun _ _ i => i.noSlots) (fun _ _ _ => True)) ∧
    Nonempty (RecipeScalarLocalInput.{0} (expansionRecipeRaw K c)
      (fun _ _ i => i) (fun _ _ i => pairedCapacityFor i ∧ i.selected.Nonempty)) := by
  obtain ⟨lower, upper, hlower, hlowerSmall, hupper, hinterval,
      A, hA, reflection, hreflection, hprepared⟩ :=
    actualRecipeCompleteMellinFamily_preparation c
  let box := actualStrictAnnularBox c lower upper hlower hlowerSmall hupper
  let rawVolume := fun rank : ℕ => volume (box rank)
  let extra := actualStrictAllVolumeOrders c lower upper hlower hlowerSmall hupper rawVolume
  let engine := actualStrictEngineOrder c lower upper hlower hinterval.le extra A
  let minimumCp := strictChildProfileMinimum (K := K)
    (ω := c.family.omega) (ψ := targetCharacter K c)
    1 engine reflection (recipeInductionSigma c) 2 (recipeInductionSigma c / 16)
    A lower upper hlower (by linarith)
  obtain ⟨Cp, Hp, hCp, hminimum, hHp, hinputs⟩ :=
    hprepared 1 engine le_rfl minimumCp
  let strict := actualMellinStrictFamily c muLocal muFinite muAdele
    lower upper hlower hlowerSmall hupper rawVolume hinterval.le 1 reflection A
    (by linarith) Cp Hp hCp.le hHp hminimum
  exact hinputs (WithLp 2 (ℝ × ℝ)) strict

end HeckeSkeleton.Moments.EngineInduction.Source

#print axioms HeckeSkeleton.Moments.EngineInduction.Source.actualRecipeScalarInputs_of_volume
