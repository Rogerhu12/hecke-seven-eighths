import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralDirectExceptionalSides
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralExceptionalStoredSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralDirectFactorFreeNormalization

/-!
# Actual direct exceptional sides and the stored original integrand

The exact occurrence fields returned by the original side factory
identify its frames with the frames of the stored literal source. The
source's existing common extraction and binding then identify the same
theta-class integrand. No estimate of that integrand is an input.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments MeasureTheory
open HeckeGeneral.ThetaSkeleton.Physical (ProbeData RowCharacterInput)
open HeckePort.Moments HeckePort.Moments.Support HeckePort.Moments.MobiusRegroup
open HeckePort.IdealMobiusDivisorSum

section ExactSideFields

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {ω ψ : HeckeCharacter K} {X : Type*} {data : X → MomentData K ω ψ}
variable {Q : CompleteMovingRowRecipe A P R data} {ξ : X}
variable {Z amplitude : ℝ} {orders : Finset (ℕ × ℕ)} {window : Set ℝ}
variable {hcompact : IsCompact window} {hpositive : window ⊆ Set.Ioi 0}
variable {firstSupport secondSupport : Finset (Ideal (𝓞 K))}
variable {hfirstSupport : ∀ p ∈ firstSupport, Prime p}
variable {F : CanonicalLiteralPhaseCalibration.FixedPhases A} {δ₁ δ₂ : ℝ}
variable {n k l : ℕ} {original : CanonicalLiteralRectangles.Atoms (K := K) n}
variable {firstL firstR secondL secondR : Ideal (𝓞 K)} {scalarL scalarR : ℂ}
variable {left : CanonicalLiteralRectangles.Atoms (K := K) k}
variable {right : CanonicalLiteralRectangles.Atoms (K := K) l}
variable {ray : (PUnit.{1} × PUnit.{1}) →* Circle}
variable {IL : AllocationColumn K k → A.Exterior}
variable {IR : AllocationColumn K l → A.Exterior}
variable {leftSign rightSign : ℝ} {divisor : Ideal (𝓞 K)}
variable {selectionL : primeSupport divisor → Finset (Fin (k + 2))}
variable {selectionR : primeSupport divisor → Finset (Fin (l + 2))}

namespace CanonicalLiteralExceptionalOriginalSideFactory.Result

variable (L : Result (σ := σ) Q ξ Z orders amplitude hcompact hpositive
  hfirstSupport F δ₁ δ₂ (secondSupport := secondSupport)
  original firstL secondL scalarL left ray IL leftSign divisor selectionL)
variable (R' : Result (σ := σ) Q ξ Z orders amplitude hcompact hpositive
  hfirstSupport F δ₁ δ₂ (secondSupport := secondSupport)
  original firstR secondR scalarR right ray IR rightSign divisor selectionR)
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable (C : A.GeneralArithmeticContext σ η hS)
variable {H ι : Type*} [Fintype ι] [DecidableEq ι]
variable (S : ActualSecondCorrelationRows A σ H ι)
variable (hIL : ∀ i ∈ childCartesianColumns left.plain₁ left.plain₂ left.slots,
  (IL i).val = allocationColumnIdeal i)
variable (hIR : ∀ i ∈ childCartesianColumns right.plain₁ right.plain₂ right.slots,
  (IR i).val = allocationColumnIdeal i)
variable (hneL : (pairedAllocatedColumns divisor selectionL left.plain₁ left.plain₂
  left.slots id id HeightOneSpectrum.asIdeal).Nonempty)
variable (hneR : (pairedAllocatedColumns divisor selectionR right.plain₁ right.plain₂
  right.slots id id HeightOneSpectrum.asIdeal).Nonempty)
variable {theta : Finset (HeckeCharacter K)} (characters : PairedFiniteCharacters theta H)

local notation "leftFrame" =>
  (left.factors S .left ray IL hIL leftSign false).frame C divisor selectionL hneL
local notation "rightFrame" =>
  (right.factors S .right ray IR hIR rightSign false).frame C divisor selectionR hneR
local notation "leftComparison" => CanonicalLiteralExceptionalFactory.comparison
  left (SecondColumnSide.left.phase PUnit.{1} ray)
local notation "rightComparison" => CanonicalLiteralExceptionalFactory.comparison
  right (SecondColumnSide.right.phase PUnit.{1} ray)

/-- The first seven exact output fields suffice to identify the whole
pair magnitude. All analytic and history fields remain those already
constructed in the returned sides. -/
theorem pair_magnitude_eq (z : WithLp 2 (ℝ × ℝ)) :
    (L.val.frame S C .left).exceptionalMagnitude (R'.val.frame S C .right)
      (L.val.comparison S C .left) (R'.val.comparison S C .right) characters z =
      (leftFrame).exceptionalMagnitude rightFrame leftComparison rightComparison characters z := by
  rcases L with ⟨LD, hL⟩
  rcases R' with ⟨RD, hR⟩
  rcases hL with ⟨hcountL, hatomsL, hrayL, hidealL, hsignL, hdivisorL, hselectionL, _⟩
  rcases hR with ⟨hcountR, hatomsR, hrayR, hidealR, hsignR, hdivisorR, hselectionR, _⟩
  rcases LD with ⟨countL, atomsL, historyL, countEqL, baseEqL, profilesL, modelL,
    recipeL, commonRecipeL, leftScaleL, rightScaleL, gaussL, originalGaussL, supportL,
    rayL, idealL, idealEqL, signL, signBoundL, divisorL, selectL, nonemptyL,
    squarefreeL, selectionMemL⟩
  rcases RD with ⟨countR, atomsR, historyR, countEqR, baseEqR, profilesR, modelR,
    recipeR, commonRecipeR, leftScaleR, rightScaleR, gaussR, originalGaussR, supportR,
    rayR, idealR, idealEqR, signR, signBoundR, divisorR, selectR, nonemptyR,
    squarefreeR, selectionMemR⟩
  cases hcountL
  cases hcountR
  have haL : atomsL = left := eq_of_heq hatomsL
  have haR : atomsR = right := eq_of_heq hatomsR
  subst atomsL
  subst atomsR
  have hiL : idealL = IL := eq_of_heq hidealL
  have hiR : idealR = IR := eq_of_heq hidealR
  subst idealL
  subst idealR
  subst rayL
  subst rayR
  subst signL
  subst signR
  subst divisorL
  subst divisorR
  have hsL : selectL = selectionL := eq_of_heq hselectionL
  have hsR : selectR = selectionR := eq_of_heq hselectionR
  subst selectL
  subst selectR
  rfl

/-- The same exact occurrence fields also identify the ordinary pair,
without any condition on the unused comparison dictionaries. -/
theorem pair_ordinaryMagnitude_eq (z : WithLp 2 (ℝ × ℝ)) :
    (L.val.frame S C .left).ordinaryExceptionalMagnitude (R'.val.frame S C .right)
      characters z =
      (leftFrame).ordinaryExceptionalMagnitude rightFrame characters z := by
  rcases L with ⟨LD, hL⟩
  rcases R' with ⟨RD, hR⟩
  rcases hL with ⟨hcountL, hatomsL, hrayL, hidealL, hsignL, hdivisorL, hselectionL, _⟩
  rcases hR with ⟨hcountR, hatomsR, hrayR, hidealR, hsignR, hdivisorR, hselectionR, _⟩
  rcases LD with ⟨countL, atomsL, historyL, countEqL, baseEqL, profilesL, modelL,
    recipeL, commonRecipeL, leftScaleL, rightScaleL, gaussL, originalGaussL, supportL,
    rayL, idealL, idealEqL, signL, signBoundL, divisorL, selectL, nonemptyL,
    squarefreeL, selectionMemL⟩
  rcases RD with ⟨countR, atomsR, historyR, countEqR, baseEqR, profilesR, modelR,
    recipeR, commonRecipeR, leftScaleR, rightScaleR, gaussR, originalGaussR, supportR,
    rayR, idealR, idealEqR, signR, signBoundR, divisorR, selectR, nonemptyR,
    squarefreeR, selectionMemR⟩
  cases hcountL
  cases hcountR
  have haL : atomsL = left := eq_of_heq hatomsL
  have haR : atomsR = right := eq_of_heq hatomsR
  subst atomsL
  subst atomsR
  have hiL : idealL = IL := eq_of_heq hidealL
  have hiR : idealR = IR := eq_of_heq hidealR
  subst idealL
  subst idealR
  subst rayL
  subst rayR
  subst signL
  subst signR
  subst divisorL
  subst divisorR
  have hsL : selectL = selectionL := eq_of_heq hselectionL
  have hsR : selectR = selectionR := eq_of_heq hselectionR
  subst selectL
  subst selectR
  rfl

end CanonicalLiteralExceptionalOriginalSideFactory.Result
end ExactSideFields

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {htrace : A.ContainsTraceBadPlaces}
variable {Γ : Subgroup A.U} [Γ.FiniteIndex]
variable (hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6)
variable [IsPrincipalIdealRing A.R]
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]
variable [MeasurableSpace (FiniteAdeleRing (𝓞 K) K)]
  [BorelSpace (FiniteAdeleRing (𝓞 K) K)]
variable (ν : Measure (FiniteAdeleRing (𝓞 K) K)) [ν.IsAddHaarMeasure]
variable [IsTotallyComplex K]
variable [MeasurableSpace (mixedEmbedding.mixedSpace K)ˣ]
  [BorelSpace (mixedEmbedding.mixedSpace K)ˣ]
variable [∀ v : (A.Sf : Set (HeightOneSpectrum (𝓞 K))),
  MeasurableSpace (v.val.adicCompletion K)ˣ]
variable [∀ v : (A.Sf : Set (HeightOneSpectrum (𝓞 K))),
  BorelSpace (v.val.adicCompletion K)ˣ]

namespace CompleteMovingRowRecipe

variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {ω ψ : HeckeCharacter K} {X : Type*}
variable {data : X → MomentData K ω ψ}
variable (Q : CompleteMovingRowRecipe A P R data) (ξ : X)
variable (W : NormProfileRecipe (fun _ : PUnit => data ξ))
variable (a : RealParameters) (Z t Y₁ Y₂ : ℝ) (centered : Bool)
variable (hZ : 1 < Z) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)

local notation "original" => (Q.arithmeticAtoms ξ).constantAtoms W a Z t
local notation "raw" => (original).raw Y₁ Y₂
local notation "seed" => Q.literalOriginalAtoms ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
local notation "c" => ((original).values Y₁ Y₂).coefficient centered

variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}
variable (b : FirstCommonCharacterBlock
  (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).columnExterior
  (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).columnExterior DE)
variable (C : A.GeneralArithmeticContext σ η htrace)
variable (φ : SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ)
variable (finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
variable (hlc : ∀ v ∈ A.Sf, IsLocallyConstant (finiteTest v))
variable (hcs : ∀ v ∈ A.Sf, HasCompactSupport (finiteTest v))
variable (radius : {r : ℝ // 0 < r}) (D : Finset (HeightOneSpectrum A.R))
variable (δ₁ : ℝ) (hδ₁ : 0 < δ₁) (hδ₁half : δ₁ ≤ 1 / 2)
variable {M : Finset (HeightOneSpectrum A.R)} {cutoff : ℝ} {hcutoff : 1 ≤ cutoff}
variable (p : FirstBlockDirectData
  (FirstBlockProfileChart.canonicalLogWithCoefficients hΓ μv ν b C
    (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).exteriorColumns
    (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).exteriorColumns φ
    ((((Q.arithmeticAtoms ξ).constantAtoms W a Z t).values Y₁ Y₂).coefficient centered)
    ((((Q.arithmeticAtoms ξ).constantAtoms W a Z t).values Y₁ Y₂).coefficient centered)
    finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half) M cutoff hcutoff)
variable (S : divisorPool p.rightData.columns (fun j => (p.rightData.ideal j).val))
variable (χ : (PUnit × PUnit) →* Circle)
variable (hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0)
variable (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
variable (δ₂ : ℝ) (hδ₂ : 0 < δ₂) (hδ₂half : δ₂ ≤ 1 / 2)
variable (retainedScale g : ℝ) (hscale : 0 < retainedScale)
variable (cutoff₂ : ℝ) (hcutoff₂ : 1 ≤ cutoff₂)
variable {Θ : Type*} [Fintype Θ] (dimension width : ℕ)


variable (hδsum : δ₁ + δ₂ ≤ 1 / 2)
variable (reference : HeckeGeneral.Analysis.NonzeroIdeal K)
variable (href : reference ∈ pairedRows (data ξ) a Z)
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
variable {heightDomain : Set ℝ}
variable (lo hi : ℝ) (hlo : 0 < lo) (hhi : 1 ≤ hi)
variable (orders : Finset (ℕ × ℕ)) (originalBound : ℝ) (horiginalBound : 0 ≤ originalBound)
variable (originalWindow : RawProfileWindow rowDomain heightDomain (Set.Icc lo hi)
  (CanonicalLogProfiles.sourceOrders (CanonicalLogProfiles.sourceOrders orders))
  (data ξ) originalBound)
variable (hreference : reference ∈ rowDomain) (htime : t ∈ heightDomain)
variable (hprime : ∀ i, Function.support (originalWindow.primeRep i t) ⊆ Set.Ioo (1 : ℝ) 2)
variable {floor padding : ℝ}
variable (domain : PairedEngineDomain centered (data ξ) a Z Y₁ Y₂ floor padding)

section LeftDirectExceptionalBinding

variable (hnorm : ∀ h ∈ p.leftData.rows,
  A.exteriorNorm (originalFrequencyIdeal h) ≤ retainedScale * Z ^ g)
variable (character : ∀ E : commonSupportPool p.leftData.columns p.leftData.columns
  (fun i => (p.leftData.ideal i).val) (fun i => (p.leftData.ideal i).val),
  SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ → Θ)
variable (dyad : ∀ E : commonSupportPool p.leftData.columns p.leftData.columns
  (fun i => (p.leftData.ideal i).val) (fun i => (p.leftData.ideal i).val),
  SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ →
    Fin dimension → Fin (width + 1))

local notation "stage" => (ActualGaussStage.canonicalUnmaskedSectorRowBallByBlock
  (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
  P δ₂ hδ₂ hδ₂half (p.leftData.directSource (p.leftDivisorCoefficient S χ)) retainedScale Z g hscale (zero_lt_one.trans hZ)
  cutoff₂ hcutoff₂ hnorm dimension width character dyad)
local notation "cover" => (p.leftSourceCover (raw).originalAtlas S χ)
local notation "firstPoint" => (fun i => -Real.log (A.exteriorNorm (b.leftResidual i)))

variable (v : (ActualGaussStage.canonicalUnmaskedSectorRowBallByBlock
  (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
  P δ₂ hδ₂ hδ₂half (p.leftData.directSource (p.leftDivisorCoefficient S χ)) retainedScale Z g hscale (zero_lt_one.trans hZ)
  cutoff₂ hcutoff₂ hnorm dimension width character dyad).supported.gated.CoveredClassKey (p.leftSourceCover (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).originalAtlas S χ) (p.leftSourceCover (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).originalAtlas S χ))
variable (exceptional : (ActualGaussStage.canonicalUnmaskedSectorRowBallByBlock
  (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
  P δ₂ hδ₂ hδ₂half (p.leftData.directSource (p.leftDivisorCoefficient S χ)) retainedScale Z g hscale (zero_lt_one.trans hZ)
  cutoff₂ hcutoff₂ hnorm dimension width character dyad).supported.gated.CoverHybridPredicates (p.leftSourceCover (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).originalAtlas S χ) (p.leftSourceCover (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).originalAtlas S χ))
variable (F : SchwartzMap ℝ ℂ)
variable (firstFixed : A.Exterior)
variable (hfirst : A.Generates firstFixed
  (CanonicalLiteralFirstPhase.leftElement C b.primes
    b.leftMultiplicity b.rightMultiplicity
    (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
variable (j : v.AllocationKey)

local notation "oldLeftAtoms" => literalLeftDirectAtoms hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
  firstFixed hfirst δ₂ v.2.2.1
local notation "oldRightAtoms" => literalLeftDirectAtoms hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
  firstFixed hfirst δ₂ v.2.2.2.1
local notation "oldLeftScalar" => literalLeftDirectScalar hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ v.2.2.1
local notation "oldRightScalar" => literalLeftDirectScalar hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ v.2.2.2.1
local notation "leftAtoms" => (oldLeftAtoms).redistributeNormFactors δ₁ δ₂
local notation "rightAtoms" => (oldRightAtoms).redistributeNormFactors δ₁ δ₂
local notation "leftScalar" => oldLeftScalar * ((oldLeftAtoms).normProfileFactor δ₁ δ₂ : ℂ)
local notation "rightScalar" => oldRightScalar * ((oldRightAtoms).normProfileFactor δ₁ δ₂ : ℂ)
local notation "leftBalance" => (fun _ : Bool => (1 : ℝ))
local notation "rightBalance" => (fun _ : Bool => (1 : ℝ))
local notation "fixedPhases" => CanonicalLiteralActualCharacters.unamplifiedPhases
  firstFixed (CanonicalLiteralFirstPhase.leftElement C b.primes b.leftMultiplicity
    b.rightMultiplicity
    (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val) hfirst
local notation "extra" => literalDeletionIdeal (primeSupport DE.1) (fun _ hp => support_prime hp)
local notation "source" => p.leftData.directSource (p.leftDivisorCoefficient S χ)
local notation "secondPattern" => v.chart.originalNonunitPattern ∅ cutoff₂ hcutoff₂ v.rowLabel
local notation "secondSector" => v.chart.originalSector P ∅ cutoff₂ hcutoff₂ v.rowLabel

variable (hS : Squarefree S.val) (hlive : (v.leaf exceptional F firstPoint j).Live)

/-- The original coefficient identities and the actual live leaf
construct this common extraction, its dictionary and the two nonzero
first scalars. These are the objects used before the exceptional bound. -/
def literalLeftDirectExceptionalExtraction :
    { extraction : (v.leaf exceptional F firstPoint j).ConstantAtomExtraction //
      extraction.leaf.OrdinaryBinding
        (v.literalRectangles leftAtoms rightAtoms exceptional F firstPoint j 1 hlive) ∧
        leftScalar ≠ 0 ∧ rightScalar ≠ 0 } :=
  let enhancedCharacter := fun E : commonSupportPool (source).columns (source).columns
      (fun i => ((source).ideal i).val) (fun i => ((source).ideal i).val) =>
    (canonicalFirstCommonBlock C (source).columns (source).columns (source).ideal (source).ideal
      E.val E.property).sectorCharacter C P (character E)
  let baseExtraction := literalLeftDirectExtraction hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    hDiff hroot hemb δ₂ hδ₂ hδ₂half retainedScale g hscale cutoff₂ hcutoff₂
    dimension width hnorm enhancedCharacter dyad v exceptional F firstFixed hfirst j hS hlive
  let baseBinding := literalLeftDirectOrdinaryBinding hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    hDiff hroot hemb δ₂ hδ₂ hδ₂half retainedScale g hscale cutoff₂ hcutoff₂
    dimension width hnorm enhancedCharacter dyad v exceptional F firstFixed hfirst j hS hlive
  have hcOldL : oldLeftScalar ≠ 0 := v.bound_literal_left_scalar_nonzero oldLeftAtoms oldRightAtoms
    exceptional F firstPoint j 1 hlive baseExtraction baseBinding
    (literalLeftDirectCore hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ firstFixed hfirst δ₂ v.2.2.1)
    oldLeftScalar (literalLeftDirectAtoms_eq_scale_core hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ firstFixed hfirst δ₂ v.2.2.1)
  have hcOldR : oldRightScalar ≠ 0 := v.bound_literal_right_scalar_nonzero oldLeftAtoms oldRightAtoms
    exceptional F firstPoint j 1 hlive baseExtraction baseBinding
    (literalLeftDirectCore hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ firstFixed hfirst δ₂ v.2.2.2.1)
    oldRightScalar (literalLeftDirectAtoms_eq_scale_core hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ firstFixed hfirst δ₂ v.2.2.2.1)
  have hproductL : (oldLeftAtoms).centered = true →
      (oldLeftAtoms).scale₁ true * (oldLeftAtoms).scale₂ true =
        (oldLeftAtoms).scale₁ false * (oldLeftAtoms).scale₂ false := by
    dsimp only [literalLeftDirectAtoms]
    apply CanonicalLiteralRectangles.Atoms.comparison_product_deleteMask
    apply CanonicalLiteralRectangles.Atoms.comparison_product_onAtlas
    apply CanonicalLiteralRectangles.Atoms.comparison_product_secondInput
    exact Q.literalOriginalAtoms_comparison_product ξ W a Z t Y₁ Y₂
      centered hZ hY₁ hY₂ domain
  have hproductR : (oldRightAtoms).centered = true →
      (oldRightAtoms).scale₁ true * (oldRightAtoms).scale₂ true =
        (oldRightAtoms).scale₁ false * (oldRightAtoms).scale₂ false := by
    dsimp only [literalLeftDirectAtoms]
    apply CanonicalLiteralRectangles.Atoms.comparison_product_deleteMask
    apply CanonicalLiteralRectangles.Atoms.comparison_product_onAtlas
    apply CanonicalLiteralRectangles.Atoms.comparison_product_secondInput
    exact Q.literalOriginalAtoms_comparison_product ξ W a Z t Y₁ Y₂
      centered hZ hY₁ hY₂ domain
  let originalExtraction := v.redistributedLiteralExtraction oldLeftAtoms oldRightAtoms
    δ₁ δ₂ hproductL hproductR exceptional F firstPoint j 1 hlive
    baseExtraction baseBinding rfl rfl
  let originalBinding := v.redistributedLiteralOrdinaryBinding oldLeftAtoms oldRightAtoms
    δ₁ δ₂ hproductL hproductR exceptional F firstPoint j 1 hlive
    baseExtraction baseBinding rfl rfl
  have hcL : leftScalar ≠ 0 := mul_ne_zero hcOldL
    (Complex.ofReal_ne_zero.mpr (ne_of_gt ((oldLeftAtoms).normProfileFactor_pos δ₁ δ₂)))
  have hcR : rightScalar ≠ 0 := mul_ne_zero hcOldR
    (Complex.ofReal_ne_zero.mpr (ne_of_gt ((oldRightAtoms).normProfileFactor_pos δ₁ δ₂)))
  ⟨originalExtraction, originalBinding, hcL, hcR⟩

local notation "construction" => literalLeftDirectExceptionalExtraction
    (hΓ := hΓ) (μv := μv) (ν := ν) (Q := Q) (ξ := ξ) (W := W)
    (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (centered := centered)
    (hZ := hZ) (hY₁ := hY₁) (hY₂ := hY₂) (b := b) (C := C) (φ := φ)
    (finiteTest := finiteTest) (hlc := hlc) (hcs := hcs) (radius := radius) (D := D)
    (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half) (p := p) (S := S) (χ := χ)
    (hDiff := hDiff) (δ₂ := δ₂)
    (hroot := hroot) (hemb := hemb) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
    (retainedScale := retainedScale) (g := g) (hscale := hscale)
    (cutoff₂ := cutoff₂) (hcutoff₂ := hcutoff₂) (dimension := dimension) (width := width)
    (domain := domain) (hnorm := hnorm) (character := character) (dyad := dyad)
    (v := v) (exceptional := exceptional) (F := F) (firstFixed := firstFixed)
    (hfirst := hfirst) (j := j) (hS := hS) (hlive := hlive)
local notation "sides" => literalLeftDirectExceptionalSides
    (hΓ := hΓ) (μv := μv) (ν := ν) (Q := Q) (ξ := ξ) (W := W)
    (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (centered := centered)
    (hZ := hZ) (hY₁ := hY₁) (hY₂ := hY₂) (b := b) (C := C) (φ := φ)
    (finiteTest := finiteTest) (hlc := hlc) (hcs := hcs) (radius := radius) (D := D)
    (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half) (p := p) (S := S) (χ := χ)
    (hDiff := hDiff) (δ₂ := δ₂)
    (reference := reference) (href := href) (orders := orders)
    (amplitude := originalBound) (hamplitude := horiginalBound)
    (originalWindow := originalWindow) (hreference := hreference) (ht := htime)
    (hcompact := isCompact_Icc) (hpositive := fun _ hy => lt_of_lt_of_le hlo hy.1)
    (hprime := hprime) (v := v) (exceptional := exceptional) (kernel := F)
    (j := j) (hlive := hlive) (firstFixed := firstFixed) (hfirst := hfirst)

variable {theta : Finset (HeckeCharacter K)}
variable (characters : PairedFiniteCharacters theta
  (SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ))
variable (thetaPair : theta × theta)
local notation "classRows" =>
  (v.literalSupportedRows leftAtoms rightAtoms).restrictRows (characters.thetaClass thetaPair)

/-- The original theta partition of the stored leaf is exactly the
pair of exceptional frames returned by the same original side factory.
The input equality specifies that original partition; no coefficient,
whole-polynomial identity or estimate is assumed. -/
theorem literalLeftDirectExceptionalSource_eq
    (hpredicate : (v.leaf exceptional F firstPoint j).exceptional = characters.exceptional)
    (z : ℝ × ℝ) :
    ((((construction).val.stripOuter leftScalar rightScalar
        (construction).property.2.1 (construction).property.2.2).thetaClassLeaf characters thetaPair).exceptionalIntegrand z) =
        (sides.1.val.frame classRows C .left).exceptionalMagnitude
          (sides.2.val.frame classRows C .right)
          (sides.1.val.comparison classRows C .left)
          (sides.2.val.comparison classRows C .right) characters (WithLp.toLp 2 z) := by
  have live : (v.leaf exceptional F firstPoint j).Live := hlive
  let allocation := v.literalAllocation exceptional F firstPoint j live
  have hb := v.literalStripOuter_theta_integrand leftAtoms rightAtoms exceptional F
    firstPoint j 1 live (construction).val (construction).property.1
    leftScalar rightScalar (construction).property.2.1 (construction).property.2.2
    (fun _ => 1) (fun _ => 1) (fun _ => zero_lt_one) (fun _ => zero_lt_one)
    characters hpredicate thetaPair z
  have hp := CanonicalLiteralExceptionalOriginalSideFactory.Result.pair_magnitude_eq
    sides.1 sides.2 C classRows v.leftReindex.ideal_product v.rightReindex.ideal_product
    (Finset.mem_filter.mp allocation.property).2.2.1
    (Finset.mem_filter.mp allocation.property).2.2.2 characters (WithLp.toLp 2 z)
  exact hb.trans hp.symm

end LeftDirectExceptionalBinding

section RightDirectExceptionalBinding

variable (hnorm : ∀ h ∈ p.rightData.rows,
  A.exteriorNorm (originalFrequencyIdeal h) ≤ retainedScale * Z ^ g)
variable (character : ∀ E : commonSupportPool p.rightData.columns p.rightData.columns
  (fun i => (p.rightData.ideal i).val) (fun i => (p.rightData.ideal i).val),
  SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ → Θ)
variable (dyad : ∀ E : commonSupportPool p.rightData.columns p.rightData.columns
  (fun i => (p.rightData.ideal i).val) (fun i => (p.rightData.ideal i).val),
  SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ →
    Fin dimension → Fin (width + 1))

local notation "stage" => (ActualGaussStage.canonicalUnmaskedSectorRowBallByBlock
  (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
  P δ₂ hδ₂ hδ₂half (p.rightData.directSource (p.rightDivisorCoefficient S χ)) retainedScale Z g hscale (zero_lt_one.trans hZ)
  cutoff₂ hcutoff₂ hnorm dimension width character dyad)
local notation "cover" => (p.rightSourceCover (raw).originalAtlas S χ)
local notation "firstPoint" => (fun i => -(-Real.log (A.exteriorNorm (b.rightResidual i))))

variable (v : (ActualGaussStage.canonicalUnmaskedSectorRowBallByBlock
  (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
  P δ₂ hδ₂ hδ₂half (p.rightData.directSource (p.rightDivisorCoefficient S χ)) retainedScale Z g hscale (zero_lt_one.trans hZ)
  cutoff₂ hcutoff₂ hnorm dimension width character dyad).supported.gated.CoveredClassKey (p.rightSourceCover (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).originalAtlas S χ) (p.rightSourceCover (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).originalAtlas S χ))
variable (exceptional : (ActualGaussStage.canonicalUnmaskedSectorRowBallByBlock
  (hΓ := hΓ) (μv := μv) (hDiff := hDiff) (ν := ν)
  P δ₂ hδ₂ hδ₂half (p.rightData.directSource (p.rightDivisorCoefficient S χ)) retainedScale Z g hscale (zero_lt_one.trans hZ)
  cutoff₂ hcutoff₂ hnorm dimension width character dyad).supported.gated.CoverHybridPredicates (p.rightSourceCover (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).originalAtlas S χ) (p.rightSourceCover (((Q.arithmeticAtoms ξ).constantAtoms W a Z t).raw Y₁ Y₂).originalAtlas S χ))
variable (F : SchwartzMap ℝ ℂ)
variable (firstFixed : A.Exterior)
variable (hfirst : A.Generates firstFixed
  (CanonicalLiteralFirstPhase.rightElement C b.primes
    b.leftMultiplicity b.rightMultiplicity
    (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val))
variable (j : v.AllocationKey)

local notation "oldLeftAtoms" => literalRightDirectAtoms hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
  firstFixed hfirst δ₂ v.2.2.1
local notation "oldRightAtoms" => literalRightDirectAtoms hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
  firstFixed hfirst δ₂ v.2.2.2.1
local notation "oldLeftScalar" => literalRightDirectScalar hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ v.2.2.1
local notation "oldRightScalar" => literalRightDirectScalar hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ v.2.2.2.1
local notation "leftAtoms" => (oldLeftAtoms).redistributeNormFactors δ₁ δ₂
local notation "rightAtoms" => (oldRightAtoms).redistributeNormFactors δ₁ δ₂
local notation "leftScalar" => oldLeftScalar * ((oldLeftAtoms).normProfileFactor δ₁ δ₂ : ℂ)
local notation "rightScalar" => oldRightScalar * ((oldRightAtoms).normProfileFactor δ₁ δ₂ : ℂ)
local notation "leftBalance" => (fun _ : Bool => (1 : ℝ))
local notation "rightBalance" => (fun _ : Bool => (1 : ℝ))
local notation "fixedPhases" => CanonicalLiteralActualCharacters.unamplifiedPhases
  firstFixed (CanonicalLiteralFirstPhase.rightElement C b.primes b.leftMultiplicity
    b.rightMultiplicity
    (sIntegerMaskGenerator K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) D).val) hfirst
local notation "extra" => literalDeletionIdeal (primeSupport DE.1) (fun _ hp => support_prime hp)
local notation "source" => p.rightData.directSource (p.rightDivisorCoefficient S χ)
local notation "secondPattern" => v.chart.originalNonunitPattern ∅ cutoff₂ hcutoff₂ v.rowLabel
local notation "secondSector" => v.chart.originalSector P ∅ cutoff₂ hcutoff₂ v.rowLabel

variable (hS : Squarefree S.val) (hlive : (v.leaf exceptional F firstPoint j).Live)

/-- The original coefficient identities and the actual live leaf
construct this common extraction, its dictionary and the two nonzero
first scalars. These are the objects used before the exceptional bound. -/
def literalRightDirectExceptionalExtraction :
    { extraction : (v.leaf exceptional F firstPoint j).ConstantAtomExtraction //
      extraction.leaf.OrdinaryBinding
        (v.literalRectangles leftAtoms rightAtoms exceptional F firstPoint j (-1) hlive) ∧
        leftScalar ≠ 0 ∧ rightScalar ≠ 0 } :=
  let enhancedCharacter := fun E : commonSupportPool (source).columns (source).columns
      (fun i => ((source).ideal i).val) (fun i => ((source).ideal i).val) =>
    (canonicalFirstCommonBlock C (source).columns (source).columns (source).ideal (source).ideal
      E.val E.property).sectorCharacter C P (character E)
  let baseExtraction := literalRightDirectExtraction hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    hDiff hroot hemb δ₂ hδ₂ hδ₂half retainedScale g hscale cutoff₂ hcutoff₂
    dimension width hnorm enhancedCharacter dyad v exceptional F firstFixed hfirst j hS hlive
  let baseBinding := literalRightDirectOrdinaryBinding hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ
    hDiff hroot hemb δ₂ hδ₂ hδ₂half retainedScale g hscale cutoff₂ hcutoff₂
    dimension width hnorm enhancedCharacter dyad v exceptional F firstFixed hfirst j hS hlive
  have hcOldL : oldLeftScalar ≠ 0 := v.bound_literal_left_scalar_nonzero oldLeftAtoms oldRightAtoms
    exceptional F firstPoint j (-1) hlive baseExtraction baseBinding
    (literalRightDirectCore hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ firstFixed hfirst δ₂ v.2.2.1)
    oldLeftScalar (literalRightDirectAtoms_eq_scale_core hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ firstFixed hfirst δ₂ v.2.2.1)
  have hcOldR : oldRightScalar ≠ 0 := v.bound_literal_right_scalar_nonzero oldLeftAtoms oldRightAtoms
    exceptional F firstPoint j (-1) hlive baseExtraction baseBinding
    (literalRightDirectCore hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ firstFixed hfirst δ₂ v.2.2.2.1)
    oldRightScalar (literalRightDirectAtoms_eq_scale_core hΓ μv ν Q ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      b C φ finiteTest hlc hcs radius D δ₁ hδ₁ hδ₁half p S χ firstFixed hfirst δ₂ v.2.2.2.1)
  have hproductL : (oldLeftAtoms).centered = true →
      (oldLeftAtoms).scale₁ true * (oldLeftAtoms).scale₂ true =
        (oldLeftAtoms).scale₁ false * (oldLeftAtoms).scale₂ false := by
    dsimp only [literalRightDirectAtoms]
    apply CanonicalLiteralRectangles.Atoms.comparison_product_deleteMask
    apply CanonicalLiteralRectangles.Atoms.comparison_product_onAtlas
    apply CanonicalLiteralRectangles.Atoms.comparison_product_secondInput
    exact Q.literalOriginalAtoms_comparison_product ξ W a Z t Y₁ Y₂
      centered hZ hY₁ hY₂ domain
  have hproductR : (oldRightAtoms).centered = true →
      (oldRightAtoms).scale₁ true * (oldRightAtoms).scale₂ true =
        (oldRightAtoms).scale₁ false * (oldRightAtoms).scale₂ false := by
    dsimp only [literalRightDirectAtoms]
    apply CanonicalLiteralRectangles.Atoms.comparison_product_deleteMask
    apply CanonicalLiteralRectangles.Atoms.comparison_product_onAtlas
    apply CanonicalLiteralRectangles.Atoms.comparison_product_secondInput
    exact Q.literalOriginalAtoms_comparison_product ξ W a Z t Y₁ Y₂
      centered hZ hY₁ hY₂ domain
  let originalExtraction := v.redistributedLiteralExtraction oldLeftAtoms oldRightAtoms
    δ₁ δ₂ hproductL hproductR exceptional F firstPoint j (-1) hlive
    baseExtraction baseBinding rfl rfl
  let originalBinding := v.redistributedLiteralOrdinaryBinding oldLeftAtoms oldRightAtoms
    δ₁ δ₂ hproductL hproductR exceptional F firstPoint j (-1) hlive
    baseExtraction baseBinding rfl rfl
  have hcL : leftScalar ≠ 0 := mul_ne_zero hcOldL
    (Complex.ofReal_ne_zero.mpr (ne_of_gt ((oldLeftAtoms).normProfileFactor_pos δ₁ δ₂)))
  have hcR : rightScalar ≠ 0 := mul_ne_zero hcOldR
    (Complex.ofReal_ne_zero.mpr (ne_of_gt ((oldRightAtoms).normProfileFactor_pos δ₁ δ₂)))
  ⟨originalExtraction, originalBinding, hcL, hcR⟩

local notation "construction" => literalRightDirectExceptionalExtraction
    (hΓ := hΓ) (μv := μv) (ν := ν) (Q := Q) (ξ := ξ) (W := W)
    (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (centered := centered)
    (hZ := hZ) (hY₁ := hY₁) (hY₂ := hY₂) (b := b) (C := C) (φ := φ)
    (finiteTest := finiteTest) (hlc := hlc) (hcs := hcs) (radius := radius) (D := D)
    (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half) (p := p) (S := S) (χ := χ)
    (hDiff := hDiff) (δ₂ := δ₂)
    (hroot := hroot) (hemb := hemb) (hδ₂ := hδ₂) (hδ₂half := hδ₂half)
    (retainedScale := retainedScale) (g := g) (hscale := hscale)
    (cutoff₂ := cutoff₂) (hcutoff₂ := hcutoff₂) (dimension := dimension) (width := width)
    (domain := domain) (hnorm := hnorm) (character := character) (dyad := dyad)
    (v := v) (exceptional := exceptional) (F := F) (firstFixed := firstFixed)
    (hfirst := hfirst) (j := j) (hS := hS) (hlive := hlive)
local notation "sides" => literalRightDirectExceptionalSides
    (hΓ := hΓ) (μv := μv) (ν := ν) (Q := Q) (ξ := ξ) (W := W)
    (a := a) (Z := Z) (t := t) (Y₁ := Y₁) (Y₂ := Y₂) (centered := centered)
    (hZ := hZ) (hY₁ := hY₁) (hY₂ := hY₂) (b := b) (C := C) (φ := φ)
    (finiteTest := finiteTest) (hlc := hlc) (hcs := hcs) (radius := radius) (D := D)
    (δ₁ := δ₁) (hδ₁ := hδ₁) (hδ₁half := hδ₁half) (p := p) (S := S) (χ := χ)
    (hDiff := hDiff) (δ₂ := δ₂)
    (reference := reference) (href := href) (orders := orders)
    (amplitude := originalBound) (hamplitude := horiginalBound)
    (originalWindow := originalWindow) (hreference := hreference) (ht := htime)
    (hcompact := isCompact_Icc) (hpositive := fun _ hy => lt_of_lt_of_le hlo hy.1)
    (hprime := hprime) (v := v) (exceptional := exceptional) (kernel := F)
    (j := j) (hlive := hlive) (firstFixed := firstFixed) (hfirst := hfirst)

variable {theta : Finset (HeckeCharacter K)}
variable (characters : PairedFiniteCharacters theta
  (SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ))
variable (thetaPair : theta × theta)
local notation "classRows" =>
  (v.literalSupportedRows leftAtoms rightAtoms).restrictRows (characters.thetaClass thetaPair)

/-- The original theta partition of the stored leaf is exactly the
pair of exceptional frames returned by the same original side factory.
The input equality specifies that original partition; no coefficient,
whole-polynomial identity or estimate is assumed. -/
theorem literalRightDirectExceptionalSource_eq
    (hpredicate : (v.leaf exceptional F firstPoint j).exceptional = characters.exceptional)
    (z : ℝ × ℝ) :
    ((((construction).val.stripOuter leftScalar rightScalar
        (construction).property.2.1 (construction).property.2.2).thetaClassLeaf characters thetaPair).exceptionalIntegrand z) =
        (sides.1.val.frame classRows C .left).exceptionalMagnitude
          (sides.2.val.frame classRows C .right)
          (sides.1.val.comparison classRows C .left)
          (sides.2.val.comparison classRows C .right) characters (WithLp.toLp 2 z) := by
  have live : (v.leaf exceptional F firstPoint j).Live := hlive
  let allocation := v.literalAllocation exceptional F firstPoint j live
  have hb := v.literalStripOuter_theta_integrand leftAtoms rightAtoms exceptional F
    firstPoint j (-1) live (construction).val (construction).property.1
    leftScalar rightScalar (construction).property.2.1 (construction).property.2.2
    (fun _ => 1) (fun _ => 1) (fun _ => zero_lt_one) (fun _ => zero_lt_one)
    characters hpredicate thetaPair z
  have hp := CanonicalLiteralExceptionalOriginalSideFactory.Result.pair_magnitude_eq
    sides.1 sides.2 C classRows v.leftReindex.ideal_product v.rightReindex.ideal_product
    (Finset.mem_filter.mp allocation.property).2.2.1
    (Finset.mem_filter.mp allocation.property).2.2.2 characters (WithLp.toLp 2 z)
  simp only [show -(-(1 : ℝ)) = 1 from neg_neg (1 : ℝ)] at hb
  exact hb.trans hp.symm

end RightDirectExceptionalBinding

end CompleteMovingRowRecipe
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalOriginalSideFactory.Result.pair_magnitude_eq

#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalLeftDirectExceptionalExtraction
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalLeftDirectExceptionalSource_eq
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalRightDirectExceptionalExtraction
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalRightDirectExceptionalSource_eq

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalOriginalSideFactory.Result.pair_ordinaryMagnitude_eq
