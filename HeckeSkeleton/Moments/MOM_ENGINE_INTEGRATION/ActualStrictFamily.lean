import HeckeSkeleton.Moments.MOM_ENGINE_INTEGRATION.ActualStrictEngine

/-!
# The complete actual strict family

A finite sum pays the real Mellin mass constants of every possible
geometric rank. The fixed source profile coefficient supplies the only
height power. Each branch is constructed by the original complete
engine and receives its actual recursively admissible children.
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

variable (lower upper : ℝ) (hlower : 0 < lower) (hlowerSmall : lower ≤ 1 / 2)
variable (hupper : 2 ≤ upper)

local notation "box" => actualStrictAnnularBox c lower upper hlower hlowerSmall hupper
local notation "theta" => canonicalDetectorTheta K (targetCharacter K c)

variable (volume : ∀ rank : ℕ, CanonicalLiteralExceptionalPaidSource.VolumePrimitive
  (targetCharacter K c) theta (Set.Icc (box rank).lo (box rank).hi))

variable (hinterval : lower ≤ upper) (ground : ℕ) (reflection : ℕ → ℕ) (A : ℝ)
variable [MeasurableSpace (ℕ × Bool)] [MeasurableSingletonClass (ℕ × Bool)]

local notation "range" => actualStrictProfileRange c lower upper hlower hinterval
local notation "extra" => actualStrictAllVolumeOrders c lower upper hlower hlowerSmall hupper volume
local notation "engine" => actualStrictEngineOrder c lower upper hlower hinterval extra A
local notation "engineCommon" => ActualStrictChoice.commonCoefficient c muLocal muFinite muAdele
  lower upper hlower hlowerSmall hupper volume hinterval ground reflection A
local notation "Omega" => RecipeMellinParameter (WithLp 2 (ℝ × ℝ))

variable (hA : 0 ≤ A)

/-- The actual Mellin mass at each fixed numerical rank. It depends on
neither the source node nor either transform frequency. -/
def actualStrictMellinMass (rank : ℕ) : ℝ :=
  let J := backwardProfileOrder ground engine reflection (rank - 1)
  let order := (range).mellinOrder
    (K := K) (ω := c.family.omega) (ψ := targetCharacter K c) extra J A
  let bounds := clippedAnnulus_bounds hlower hinterval (recipeStrictRankBound c) rank
  mellinStrictMassConstant (K := K) (ω := c.family.omega) (ψ := targetCharacter K c)
    (Ω := Omega) c.geometry.slots order A
    (clippedAnnulusLower lower upper (recipeStrictRankBound c) rank)
    (rankedAnnulusUpper upper (recipeStrictRankBound c) rank) hA bounds.1 bounds.2

theorem actualStrictMellinMass_nonneg (rank : ℕ) :
    0 ≤ actualStrictMellinMass c lower upper hlower hlowerSmall hupper volume
      hinterval ground reflection A hA rank :=
  mellinStrictMassConstant_nonneg _ _ _ _ _ _ _ _

local notation "mass" => actualStrictMellinMass c lower upper hlower hlowerSmall hupper
  volume hinterval ground reflection A hA

variable (Cp Hp : ℝ) (hCp : 0 ≤ Cp) (hHp : 0 ≤ Hp)
variable (hminimum : strictChildProfileMinimum (K := K)
  (ω := c.family.omega) (ψ := targetCharacter K c)
  ground engine reflection (recipeInductionSigma c) 2 (recipeInductionSigma c / 16)
  A lower upper hlower (by linarith : 0 < upper) ≤ Cp)

/-- Every strict call is now the actual producer, with all constants
and finite orders preceding the scale, height, index, node and frequency.
The outer Mellin mass is paid by one finite scalar and the original
polynomial height budget. No recursive or final energy is a premise. -/
def actualMellinStrictFamily :
    RecipeMellinStrictFamily (WithLp 2 (ℝ × ℝ)) (expansionRecipeRaw K c)
      (actualCompleteSourceBudgetPrimitive c) ground engine reflection A Cp Hp lower upper where
  coefficient := finiteStrictConstant (recipeStrictRankBound c) mass *
    (1 + Cp) ^ (2 * (c.geometry.slots + 2)) * engineCommon
  heightDegree := Hp * (2 * (c.geometry.slots + 2) : ℕ)
  threshold := ActualStrictChoice.physicalThreshold c muLocal muFinite
    lower upper hlower hlowerSmall hupper volume
  coefficient_nonneg := mul_nonneg
    (mul_nonneg (finiteStrictConstant_pos _ _).le (pow_nonneg (by linarith) _))
    (ActualStrictChoice.commonCoefficient_pos c muLocal muFinite muAdele
      lower upper hlower hlowerSmall hupper volume hinterval ground reflection A).le
  heightDegree_nonneg := mul_nonneg hHp (Nat.cast_nonneg _)
  outputs := by
    intro Z hZ T hT i x domain
    let U := momentBaseFor i
    let primitive := recipeDataReflectionPrimitive c
      (recipeThetaFamily (expansionRecipeRaw K c)) (actualCompleteSourceBudgetPrimitive c)
      ground engine reflection (recipeInductionSigma c) (recipeInductionSigma c / 16)
      A Cp Hp lower upper U T
    let n := (recipeDataReflectionSystem c
      (recipeThetaFamily (expansionRecipeRaw K c)) (actualCompleteSourceBudgetPrimitive c)
      ground engine reflection A Cp Hp lower upper U T).node x
    let rank := parameterCoreRank (recipeInductionSigma c) 2
      (recipeInductionSigma c / 16) n.parameters
    let J := backwardProfileOrder ground engine reflection (rank - 1)
    let order := (range).mellinOrder
      (K := K) (ω := c.family.omega) (ψ := targetCharacter K c) extra J A
    let lo := clippedAnnulusLower lower upper (recipeStrictRankBound c) rank
    let hi := rankedAnnulusUpper upper (recipeStrictRankBound c) rank
    have bounds := clippedAnnulus_bounds hlower hinterval (recipeStrictRankBound c) rank
    have hrank : rank ≤ recipeStrictRankBound c :=
      (parameterCoreRank_lt_bound n.parameters (recipeInduction_budget (c := c)).1
        x.down.property.width_le).le
    have hP := profileFamilyBudget_one_le hCp hHp hT
    have hlarge := ActualStrictChoice.sourceBase_ge_rankThreshold c muLocal muFinite
      lower upper hlower hlowerSmall hupper volume hZ i rank hrank
    have hprofile : ModelProfileControl n.data (order + 2) A
        (profileFamilyBudget Cp Hp T) 0 lo hi 0 :=
      actualStrictNode_profile lower upper hlower hinterval extra ground reflection
        A Cp Hp U T x domain
    have hbudget := finiteMellin_profile_budget
      (N := recipeStrictRankBound c) (rank := rank) (cap := c.geometry.slots)
      (mass := mass) (engine := engineCommon) hrank
      (actualStrictMellinMass_nonneg c lower upper hlower hlowerSmall hupper volume
        hinterval ground reflection A hA rank)
      (ActualStrictChoice.commonCoefficient_pos c muLocal muFinite muAdele
        lower upper hlower hlowerSmall hupper volume hinterval ground reflection A).le
      hCp hHp hT
    refine ⟨universalMellinStrictBranch (Ω := Omega) primitive
      (recipeInductionSigma c) 2 (recipeInductionSigma c / 16) c.geometry.slots
      (recipeInduction_budget (c := c)).1 x U T
      (finiteStrictConstant (recipeStrictRankBound c) mass *
        (1 + Cp) ^ (2 * (c.geometry.slots + 2)) * engineCommon)
      (Hp * (2 * (c.geometry.slots + 2) : ℕ))
      (recipeInductionTerminalLoss c) (recipeInductionEdgeLoss c)
      order A lo hi hA bounds.1 bounds.2
      (profileFamilyBudget Cp Hp T) hP hprofile engineCommon 1
      (fun frequency => actualStrictEngineOutput c muLocal muFinite muAdele
        lower upper hlower hlowerSmall hupper volume hinterval ground reflection A
        Cp Hp U T hA hCp hHp hT hminimum x domain hlarge frequency) ?_⟩
    simpa only [mul_one] using hbudget

end HeckeSkeleton.Moments.EngineInduction.Source

#print axioms HeckeSkeleton.Moments.EngineInduction.Source.actualMellinStrictFamily
