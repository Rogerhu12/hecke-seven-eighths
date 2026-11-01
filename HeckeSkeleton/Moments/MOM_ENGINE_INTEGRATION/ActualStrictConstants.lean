import HeckeSkeleton.Moments.MOM_ENGINE_INTEGRATION.ActualStrictOrders
import HeckeSkeleton.Moments.MOM_ENGINE_INTEGRATION.ActualEngineArithmetic
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.TargetPrimeAnalyticInput
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.FiniteMellinBudget

/-!
# One fixed scalar budget for every actual strict source

All arithmetic constants are selected from the original context and
the finite rank boxes. The literal Mellin frequency and source height
do not occur in any engine constant. A finite scalar sum and the proved
shell lower bound give one physical threshold for the entire family.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical NumberField

namespace HeckeSkeleton.Moments.EngineInduction.Source.ActualStrictChoice

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

local notation "range" => actualStrictProfileRange c lower upper hlower hinterval
local notation "extra" => actualStrictAllVolumeOrders c lower upper hlower hlowerSmall hupper volume
local notation "engine" => actualStrictEngineOrder c lower upper hlower hinterval extra A
local notation "J" => fun rank : ℕ => backwardProfileOrder ground engine reflection (rank - 1)
local notation "request" => fun rank : ℕ => actualStrictOutputOrders
  c lower upper hlower hlowerSmall hupper volume hinterval (J rank) A

/-- The same original producer constant, chosen before the source. -/
def coefficient (rank : ℕ) : ℝ :=
  OriginalMeshPairedStep.constant (ω := c.family.omega)
    muLocal muFinite muAdele CC (axiomChoice K c).different
    (actualEngineCoefficientData c) (actualEngineCoefficientData_recipes c)
    (box rank) (momentMesh K c.family).val theta (request rank) (volume rank)
    (actualSourcePrimeAnalyticProvider c (momentRowCharacters K c))

/-- Time is zero in the actual frozen source. Its raw amplitude is
already uniform in both outer Mellin coordinates. -/
def control (rank : ℕ) : ℝ :=
  CanonicalPrimitiveEngineControl.value
      ((range).amplitude (K := K) (ω := c.family.omega) (ψ := targetCharacter K c)
        extra (J rank) A) 0 ^ OriginalMeshPairedStep.degree (box rank)

def rankCoefficient (rank : ℕ) : ℝ :=
  coefficient c muLocal muFinite muAdele lower upper hlower hlowerSmall hupper
    volume hinterval ground reflection A rank *
  control c lower upper hlower hlowerSmall hupper volume hinterval ground reflection A rank

/-- One pre-source scalar for every strict rank. -/
def commonCoefficient : ℝ :=
  finiteStrictConstant (recipeStrictRankBound c)
    (rankCoefficient c muLocal muFinite muAdele lower upper hlower hlowerSmall hupper
      volume hinterval ground reflection A)

def rankThreshold (rank : ℕ) : ℝ :=
  OriginalMeshPairedStep.threshold muLocal muFinite CC (axiomChoice K c).different
    (box rank) theta (volume rank)

def scaleThreshold : ℝ :=
  finiteStrictConstant (recipeStrictRankBound c)
    (rankThreshold c muLocal muFinite lower upper hlower hlowerSmall hupper volume)

/-- The actual shell is at least 1/16, so this physical threshold
forces every original moment base past the common engine threshold. -/
def physicalThreshold : ℝ :=
  scaleThreshold c muLocal muFinite lower upper hlower hlowerSmall hupper volume ^ (16 : ℕ)

theorem coefficient_pos (rank : ℕ) :
    0 < coefficient c muLocal muFinite muAdele lower upper hlower hlowerSmall hupper
      volume hinterval ground reflection A rank :=
  OriginalMeshPairedStep.constant_pos (ω := c.family.omega)
    muLocal muFinite muAdele CC (axiomChoice K c).different
    (actualEngineCoefficientData c) (actualEngineCoefficientData_recipes c)
    (box rank) (momentMesh K c.family).val theta (request rank) (volume rank)
    (actualSourcePrimeAnalyticProvider c (momentRowCharacters K c))

theorem control_nonneg (rank : ℕ) :
    0 ≤ control c lower upper hlower hlowerSmall hupper volume hinterval ground reflection A rank :=
  pow_nonneg (zero_le_one.trans
    (CanonicalPrimitiveEngineControl.one_le _ 0
      ((range).amplitude_one_le extra (J rank) A))) _

theorem commonCoefficient_pos :
    0 < commonCoefficient c muLocal muFinite muAdele lower upper hlower hlowerSmall hupper
      volume hinterval ground reflection A := finiteStrictConstant_pos _ _

theorem rankCoefficient_le_common (rank : ℕ) (hrank : rank ≤ recipeStrictRankBound c) :
    rankCoefficient c muLocal muFinite muAdele lower upper hlower hlowerSmall hupper
      volume hinterval ground reflection A rank ≤
    commonCoefficient c muLocal muFinite muAdele lower upper hlower hlowerSmall hupper
      volume hinterval ground reflection A := le_finiteStrictConstant _ _ rank hrank

theorem scaleThreshold_one_le :
    1 ≤ scaleThreshold c muLocal muFinite lower upper hlower hlowerSmall hupper volume := by
  unfold scaleThreshold finiteStrictConstant
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => le_max_left _ _))

variable {Z T : ℝ}

/-- Every original index, not merely a nonempty dyadic bin, has the
same shell lower bound proved from its literal physical construction. -/
theorem sourceBase_ge_rankThreshold
    (hZ : physicalThreshold c muLocal muFinite lower upper hlower hlowerSmall hupper volume ≤ Z)
    (i : SourceMomentIndexFor K c
      (recipeMomentSourceData K c (expansionRecipeRaw K c)) Z T)
    (rank : ℕ) (hrank : rank ≤ recipeStrictRankBound c) :
    rankThreshold c muLocal muFinite lower upper hlower hlowerSmall hupper volume rank ≤
      momentBaseFor i := by
  apply (le_finiteStrictConstant _ _ rank hrank).trans
  exact _root_.ExpansionRecipe.shell_base_ge_of_physical_cutoff
    (scaleThreshold_one_le c muLocal muFinite lower upper hlower hlowerSmall hupper volume)
    hZ (recipeMoment_shell_lower i)

end HeckeSkeleton.Moments.EngineInduction.Source.ActualStrictChoice

#print axioms HeckeSkeleton.Moments.EngineInduction.Source.ActualStrictChoice.coefficient_pos
#print axioms HeckeSkeleton.Moments.EngineInduction.Source.ActualStrictChoice.sourceBase_ge_rankThreshold
