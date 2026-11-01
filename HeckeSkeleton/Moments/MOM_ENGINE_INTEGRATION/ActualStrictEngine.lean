import HeckeSkeleton.Moments.MOM_ENGINE_INTEGRATION.ActualStrictConstants
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.ActualEngineProfiles
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.ActualEngineLabels
import HeckeSkeleton.Moments.MOM_ENGINE_INTEGRATION.OriginalMeshPairedAnnulus

/-!
# The actual strict engine output for the prepared recursive node

Every input of the original complete engine is discharged from the
same actual target, its complete moving recipe, the literal normalized
Mellin profiles and the fixed rank choices. The returned children are
frozen at their existing zero time, assigned the actual complete source
primitive, and embedded with their unchanged positive kernels into the
common recursion parameter space.

The original annular volume primitive is the sole analytic input still
visible here. It is a single-character series estimate, not an energy,
exceptional leaf, child moment or local reduction assumption.
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

variable (Cp Hp U T : ℝ) (hA : 0 ≤ A) (hCp : 0 ≤ Cp) (hHp : 0 ≤ Hp) (hT : 0 ≤ T)
variable (hminimum : strictChildProfileMinimum (K := K)
  (ω := c.family.omega) (ψ := targetCharacter K c)
  ground engine reflection (recipeInductionSigma c) 2 (recipeInductionSigma c / 16)
  A lower upper hlower (by linarith : 0 < upper) ≤ Cp)

local notation "S" => recipeDataReflectionSystem c
  (recipeThetaFamily (expansionRecipeRaw K c)) (actualCompleteSourceBudgetPrimitive c)
  ground engine reflection A Cp Hp lower upper U T

variable (x : (S).Label)
local notation "n" => (S).node x
local notation "rank" => parameterCoreRank (recipeInductionSigma c) 2
  (recipeInductionSigma c / 16) (n).parameters
local notation "J" => backwardProfileOrder ground engine reflection (rank - 1)
local notation "narrowBox" => recipeStrictEngineBox c lower upper hlower hlowerSmall hupper rank
local notation "b" => box rank
local notation "request" => actualStrictOutputOrders
  c lower upper hlower hlowerSmall hupper volume hinterval J A
local notation "orders" => OriginalMeshPairedStep.orders
  (A := AA) (σ := complexEmbedding K c) (η := (axiomChoice K c).η)
  (hS := (axiomChoice K c).hS) b theta request (volume rank)
local notation "inputs" => OriginalMeshPairedStep.profileOrders
  (A := AA) (σ := complexEmbedding K c) (η := (axiomChoice K c).η)
  (hS := (axiomChoice K c).hS) b theta request (volume rank)
local notation "amplitude" => (range).amplitude
  (K := K) (ω := c.family.omega) (ψ := targetCharacter K c) extra J A
local notation "hP" => profileFamilyBudget_one_le hCp hHp hT
local notation "model" => actualStrictMellinNode (Ω := Omega)
  lower upper hlower hinterval extra ground reflection A Cp Hp U T x hA hP

variable (domain : PairedEngineDomain (n).centered (n).data (n).parameters U
  (U ^ (n).comparison₁) (U ^ (n).comparison₂)
  (16 * recipeInductionSigma c) (recipeInductionSigma c / 16))
variable (hlarge : ActualStrictChoice.rankThreshold c muLocal muFinite
  lower upper hlower hlowerSmall hupper volume rank ≤ U)

/-- This is the actual original producer, including its genuine direct
and pooled exceptional estimates. It returns the same children with
complete primitive membership, before recursive labels are built. -/
def actualStrictEngineOutput (frequency : ℝ × ℝ) :
    (model frequency).EngineOutput (Ω := Omega) U (recipeInductionSigma c)
      (recipeInductionEdgeLoss c) (recipeInductionTerminalLoss c) engineCommon 1
      (admissibleOfInvariant
        (recipeDataReflectionPrimitive c (recipeThetaFamily (expansionRecipeRaw K c))
          (actualCompleteSourceBudgetPrimitive c) ground engine reflection
          (recipeInductionSigma c) (recipeInductionSigma c / 16)
          A Cp Hp lower upper U T)) := by
  have hrank : rank ≤ recipeStrictRankBound c :=
    (parameterCoreRank_lt_bound (n).parameters (recipeInduction_budget (c := c)).1
      x.down.property.width_le).le
  let prepared := actualStrictSource (Ω := Omega) lower upper hlower hinterval
    extra ground reflection A Cp Hp U T x hA hP domain frequency
  let parent := localizeOriginalParent (model frequency).data (n).parameters U
  let narrow : RawProfileWindow Set.univ Set.univ
      (Set.Icc (narrowBox).lo (narrowBox).hi) inputs parent amplitude := by
    rw [actualStrictInputOrders_eq c lower upper hlower hlowerSmall hupper
      volume hinterval J A rank hrank]
    exact prepared.profiles
  let raw := CanonicalPrimitiveEngineAnnulus.rawWindow narrowBox narrow
  have d : PairedEngineDomain (model frequency).centered parent (n).parameters U
      (U ^ (n).comparison₁) (U ^ (n).comparison₂)
      (16 * recipeInductionSigma c) (recipeInductionSigma c / 16) :=
    { domain with total_length := domain.total_length }
  have hmesh : parent.geometry.fitsMesh (momentMesh K c.family).val :=
    recipeDataReflectionSystem_fitsMesh
      (recipeThetaFamily (expansionRecipeRaw K c)) (actualCompleteSourceBudgetPrimitive c)
      ground engine reflection A Cp Hp lower upper U T x
  have htheta : parent.theta = theta := prepared.complete.source.theta_eq
  have hone : (1 : HeckeCharacter K) ∈ parent.theta := by
    rw [htheta]
    exact one_mem_canonicalDetectorTheta K (targetCharacter K c)
  have hbackground : parent.plainBackground⁻¹ ∈ parent.theta ∨
      ¬ FiniteOrder parent.plainBackground := by
    by_cases h : FiniteOrder parent.plainBackground
    · exact Or.inl (canonicalTheta_finite_plainBackground parent htheta h)
    · exact Or.inr h
  have hslot : ∀ j, parent.slotCoefficient j ∈ parent.theta := by
    intro j
    rw [htheta]
    exact prepared.complete.source.slot_characters j
  have hslotInverse := prepared.complete.canonicalInverseSlots
  have hkappa : (n).parameters.κ = 2 * c.family.B - 1 :=
    recipeDataReflectionSystem_kappa
      (recipeThetaFamily (expansionRecipeRaw K c)) (actualCompleteSourceBudgetPrimitive c)
      ground engine reflection A Cp Hp lower upper U T x
  have hprime := prepared.complete.primeSupport.rawProfileWindow raw
  let output := originalMeshPairedEngineStep
    (μv := muLocal) (ν := muFinite) (μ := muAdele) (C := CC)
    (hDiff := (axiomChoice K c).different)
    (Drecipe := actualEngineCoefficientData c) (hD := actualEngineCoefficientData_recipes c)
    (b := b) (mesh := (momentMesh K c.family).val) (theta := theta)
    (outputOrders := request) (primitive := volume rank)
    (provider := actualSourcePrimeAnalyticProvider c (momentRowCharacters K c))
    (Q := prepared.complete.source.recipe) (W := prepared.normRecipe) (ξ := PUnit.unit)
    (hroot := rfl) (hemb := rfl) (a := (n).parameters) (Z := U) (t := 0)
    (Y₁ := U ^ (n).comparison₁) (Y₂ := U ^ (n).comparison₂) (centered := (n).centered)
    (domain := d) (hbudget := prepared.fullBudget) (hwidth := x.down.property.width_le)
    (hpadding := le_rfl) (hcap := x.down.property.slot_count) (hlarge := hlarge)
    (hmesh := (momentMesh K c.family).property.le) (hfit := hmesh)
    (amplitude := amplitude) (hamplitude := (range).amplitude_one_le extra J A)
    (profiles := raw) (hrows := fun _ _ => Set.mem_univ _) (htime := Set.mem_univ 0)
    (hprime := fun j => hprime j 0) (htheta := htheta)
    (hlower := CanonicalPrimitiveEngineAnnulus.inverse_hi_le_lo narrowBox)
    (hplaces := actualEngineTheta_badPrimes c)
    (boundary := fun _ => targetDynamicFiniteOrderBoundary c (n).parameters.κ hkappa)
    (hone := hone) (hbackground := hbackground) (hslot := hslot) (hslotInverse := hslotInverse)
  have supports := OriginalMeshPairedSupport.narrowAnnulusSupport
    (μv := muLocal) (ν := muFinite) (μ := muAdele) (C := CC)
    (hDiff := (axiomChoice K c).different)
    (Drecipe := actualEngineCoefficientData c) (hD := actualEngineCoefficientData_recipes c)
    (b := b) (mesh := (momentMesh K c.family).val) (theta := theta)
    (outputOrders := request) (primitive := volume rank)
    (provider := actualSourcePrimeAnalyticProvider c (momentRowCharacters K c))
    (Q := prepared.complete.source.recipe) (W := prepared.normRecipe) (ξ := PUnit.unit)
    (hroot := rfl) (hemb := rfl) (a := (n).parameters) (Z := U) (t := 0)
    (Y₁ := U ^ (n).comparison₁) (Y₂ := U ^ (n).comparison₂) (centered := (n).centered)
    (domain := d) (hbudget := prepared.fullBudget) (hwidth := x.down.property.width_le)
    (hpadding := le_rfl) (hcap := x.down.property.slot_count) (hlarge := hlarge)
    (hmesh := (momentMesh K c.family).property.le) (hfit := hmesh)
    (amplitude := amplitude) (hamplitude := (range).amplitude_one_le extra J A)
    (profiles := raw) (hrows := fun _ _ => Set.mem_univ _) (htime := Set.mem_univ 0)
    (hprime := fun j => hprime j 0) (htheta := htheta)
    (hlower := CanonicalPrimitiveEngineAnnulus.inverse_hi_le_lo narrowBox)
    (hplaces := actualEngineTheta_badPrimes c)
    (boundary := fun _ => targetDynamicFiniteOrderBoundary c (n).parameters.κ hkappa)
    (hone := hone) (hbackground := hbackground) (hslot := hslot) (hslotInverse := hslotInverse)
    (narrowLo := (narrowBox).lo) (narrowHi := (narrowBox).hi) (hnarrowLo := (narrowBox).lo_pos)
    (hnarrowHi := (narrowBox).hi_ge_one)
    (hnarrowHiLe := CanonicalPrimitiveEngineAnnulus.hi_le_annularBox narrowBox)
    (narrowProfiles := narrow)
  let actual := engineOutput_of_localizedOriginalParent output
  have horders : eulerSchwartzOrders (K := K)
      (ω := c.family.omega) (ψ := targetCharacter K c)
      (range).lower (range).upper (range).lower_pos J A ⊆ orders := by
    rw [actualStrictOrders_eq c lower upper hlower hlowerSmall hupper
      volume hinterval J A rank hrank]
    exact (range).childOrders_euler extra J A
  have hprofiles := engineOutput_frozen_rankedProfiles (n := model frequency)
    ground engine reflection (recipeInductionSigma c) 2 (recipeInductionSigma c / 16)
    A lower upper hlower (by linarith) Cp Hp T hminimum hHp hT actual
    (recipeInduction_budget (c := c)).1 x.down.property.width_le domain.total_length
    orders horders (fun branch xi => (supports.window branch xi).1)
      (fun branch xi => (supports.window branch xi).2)
  exact actualRecipeEngineOutput (model frequency) parent U
    ((b).ε + (momentMesh K c.family).val) ((b).paddingMax + 3 * (b).step + (b).ε)
    (ActualStrictChoice.coefficient c muLocal muFinite muAdele lower upper hlower hlowerSmall hupper
      volume hinterval ground reflection A rank)
    (ActualStrictChoice.control c lower upper hlower hlowerSmall hupper
      volume hinterval ground reflection A rank)
    engineCommon ground engine reflection A Cp Hp lower upper T actual htheta hkappa hmesh
    (fun branch xi => (supports.prime branch xi).1)
    (fun branch xi => (supports.prime branch xi).2)
    hprofiles.1 hprofiles.2 domain.scale.le
    (ActualStrictChoice.commonCoefficient_pos c muLocal muFinite muAdele
      lower upper hlower hlowerSmall hupper volume hinterval ground reflection A).le
    (ActualStrictChoice.rankCoefficient_le_common c muLocal muFinite muAdele
      lower upper hlower hlowerSmall hupper volume hinterval ground reflection A rank hrank)
    (recipeStrictEngineBox_mass_budget c lower upper hlower hlowerSmall hupper rank)
    (recipeStrictEngineBox_terminal_budget c lower upper hlower hlowerSmall hupper rank) 0

end HeckeSkeleton.Moments.EngineInduction.Source

#print axioms HeckeSkeleton.Moments.EngineInduction.Source.actualStrictEngineOutput
