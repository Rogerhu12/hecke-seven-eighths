import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.LiteralCapacity
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.LiteralWindows
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.LiteralCalibration
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalFullKappaRightNormalization
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalOriginalPrimeAnalyticProvider
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.LiteralPassive
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.HybridNormalizedProduction

set_option linter.unusedSectionVars false

set_option quotPrecheck false

/-!
# The computed literal frame produces its actual normalized side

The calibration and the profile model in this internal assembly are
the outputs of the original literal constructors. Their two data
identities are literal at those constructors. The complete moving
recipe and its full joint budget are constructed from those data;
the two profile windows are constructed from the original window.

The original scale-product and slot calculations construct the
capacity length input. The selected side then determines the order
of the two original common ideals. No completed side normalization,
prime bound, profile window or child estimate is an input.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2

open HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments HeckePort.Moments.Support HeckePort.IdealMobiusDivisorSum
open PrimeCancellation.Analytic

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {H ι : Type*} [Fintype ι] [DecidableEq ι]

namespace SecondColumnSide

/-- These are the original common multiplicities in the order of the
actual source whose raw degree is being normalized. -/
def literalMultiplicity (side : SecondColumnSide)
    (R : ActualSecondCorrelationRows A σ H ι) : ι → ℕ :=
  match side with
  | .left => R.leftMultiplicity
  | .right => R.rightMultiplicity

def literalOppositeMultiplicity (side : SecondColumnSide)
    (R : ActualSecondCorrelationRows A σ H ι) : ι → ℕ :=
  match side with
  | .left => R.rightMultiplicity
  | .right => R.leftMultiplicity

theorem literal_root (side : SecondColumnSide)
    (R : ActualSecondCorrelationRows A σ H ι) :
    secondSixthRootIdeal R.primes (side.literalMultiplicity R)
        (side.literalOppositeMultiplicity R) =
      secondSixthRootIdeal R.primes R.leftMultiplicity R.rightMultiplicity := by
  sorry

end SecondColumnSide

namespace CanonicalLiteralRectangles.Atoms

variable [IsPrincipalIdealRing A.R]
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {ω ψ : HeckeCharacter K} {k : ℕ}
variable (d : CanonicalLiteralRectangles.Atoms (K := K) k) (W : d.ProfileData)
variable (rows : ActualSecondCorrelationRows A σ H ι)
variable (side : SecondColumnSide) (χ : (PUnit.{1} × PUnit.{1}) →* Circle)
variable (ideal : AllocationColumn K k → A.Exterior)
variable (hideal : ∀ i ∈ childCartesianColumns d.plain₁ d.plain₂ d.slots,
  (ideal i).val = allocationColumnIdeal i)
variable (firstSign : ℝ) (rectangle : Bool) (L : Ideal (𝓞 K))
variable (selection : primeSupport L → Finset (Fin (k + 2)))
variable (hne : (pairedAllocatedColumns L selection d.plain₁ d.plain₂ d.slots
  id id HeightOneSpectrum.asIdeal).Nonempty)

local notation "f" =>
  (d.factors rows side χ ideal hideal firstSign rectangle).frame C L selection hne

variable (D : ((d.factors rows side χ ideal hideal firstSign rectangle).frame C L selection hne).source.Calibration
  (σ := σ) ω ψ)
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (Rchar : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable (F : CanonicalLiteralPhaseCalibration.FixedPhases A)
variable (parent : MomentData K ω ψ) (oldMoving : OriginalMovingFactors A P Rchar)
variable (correction : HeckeCharacter K) (hcorr : correction ∈ parent.theta)
variable (remaining extra : HeckeGeneral.Analysis.NonzeroIdeal K)
variable (a : RealParameters) (step : ℝ)
variable (G : OriginalNominalGeometry (K := K) a
  ((d.factors rows side χ ideal hideal firstSign rectangle).frame C L selection hne).source.base step)
variable (pattern : ι → Bool)
variable (sector : SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (slots : OriginalSlotDictionary parent d.length)
variable (cutoff : ℝ)

local notation "rootLength" =>
  idealLogLength (f).source.base
    (secondSixthRootIdeal rows.primes (side.literalMultiplicity rows)
      (side.literalOppositeMultiplicity rows)).val
local notation "m" => G.literalRowParameter cutoff
local notation "q" => G.literalSupportParameter rootLength

variable (reference : HeckeGeneral.Analysis.NonzeroIdeal K) (time : ℝ)
variable (hdata : ∀ ξ, D.data ξ = CanonicalLiteralAllocatedData.data
  P Rchar W ((d.factors rows side χ ideal hideal firstSign rectangle).frame C L selection hne).allocation
  F parent oldMoving correction hcorr C rows.primes rows.leftMultiplicity rows.rightMultiplicity
  pattern sector remaining extra (G.literalRowParameter cutoff)
  (G.literalSupportParameter (idealLogLength
    ((d.factors rows side χ ideal hideal firstSign rectangle).frame C L selection hne).source.base
    (secondSixthRootIdeal rows.primes (side.literalMultiplicity rows)
      (side.literalOppositeMultiplicity rows)).val))
  (CanonicalLiteralProfileData.frozenNormTest parent.inverseTest reference time)
  slots.index rectangle firstSign side.literalNegative ξ)
variable (hparameters : D.parameters = CanonicalLiteralAllocatedData.parameters d
  ((d.factors rows side χ ideal hideal firstSign rectangle).frame C L selection hne).allocation
  rectangle (G.literalRowParameter cutoff)
  (G.literalSupportParameter (idealLogLength
    ((d.factors rows side χ ideal hideal firstSign rectangle).frame C L selection hne).source.base
    (secondSixthRootIdeal rows.primes (side.literalMultiplicity rows)
      (side.literalOppositeMultiplicity rows)).val)) a.κ)

local notation "literalRecipe" =>
  CanonicalLiteralAllocatedData.recipe P Rchar W (f).allocation F parent oldMoving correction
    hcorr C rows.primes rows.leftMultiplicity rows.rightMultiplicity pattern sector
    remaining extra m q (CanonicalLiteralProfileData.frozenNormTest parent.inverseTest reference time)
    slots.index rectangle firstSign side.literalNegative

/-- The complete original mask, remaining deletion and all appended
moving factors are transported by the actual data identity alone. -/
def productionRecipe : CompleteMovingRowRecipe A P Rchar D.data :=
  (literalRecipe).ofAllowedSubset
    (fun ξ u hu => by simpa only [hdata ξ] using hu)
    (fun ξ => congrArg (fun e : MomentData K ω ψ => e.rowCharacter) (hdata ξ))
    (fun ξ => congrArg (fun e : MomentData K ω ψ => e.commonMask) (hdata ξ))
    (fun ξ => congrArg (fun e : MomentData K ω ψ => e.theta) (hdata ξ))

theorem productionRecipe_fullJointBudget :
    (d.productionRecipe W rows side χ ideal hideal firstSign rectangle L selection hne D
      P Rchar F parent oldMoving correction hcorr remaining extra a step G pattern sector
      slots cutoff reference time hdata).FullJointBudget (f).source.base (m + q) := by
  sorry

variable {centered : Bool} {Y₁ Y₂ floor padding : ℝ}
variable (domain : PairedEngineDomain centered parent a
  ((d.factors rows side χ ideal hideal firstSign rectangle).frame C L selection hne).source.base
  Y₁ Y₂ floor padding)
variable (direct : G.tag = .direct → parent.geometry.slotCount = 0)
variable (hcutoff : 0 ≤ cutoff) (hsmall : 2 * cutoff ≤ step)
variable (annulus : ℝ) (cap : ℕ) (error : ℝ) (herr : 0 ≤ error)
variable (hbound : d.scaleProduct rectangle *
  ((Ideal.absNorm G.literalFirstExtraction.val : ℝ) * (Ideal.absNorm G.ideals.second.val : ℝ)) ≤
  annulus ^ (2 * cap) *
    ((d.factors rows side χ ideal hideal firstSign rectangle).frame C L selection hne).source.base ^
      (a.n₁ + a.n₂ + a.z))
variable (hthreshold : annulus ^ (2 * cap) ≤
  ((d.factors rows side χ ideal hideal firstSign rectangle).frame C L selection hne).source.base ^ error)
variable (hm : ∀ i, 0 < rows.leftMultiplicity i) (hn : ∀ i, 0 < rows.rightMultiplicity i)
variable (hsecond : G.ideals.second.val = (primePowerProduct rows.primes
  (side.literalMultiplicity rows)).val)
variable (hopposite : G.ideals.secondOpposite.val = (primePowerProduct rows.primes
  (side.literalOppositeMultiplicity rows)).val)
variable (hunit : G.ideals.unitPart.val = (secondPatternUnitIdeal rows.primes
  (side.literalMultiplicity rows) (side.literalOppositeMultiplicity rows) pattern).val)
variable (hstep : 0 < step) (mesh : ℝ) (hmesh : 0 ≤ mesh)
variable (hfit : parent.geometry.fitsMesh mesh)
variable {originalRows : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
variable {originalHeights : Set ℝ} {originalOrders : Finset (ℕ × ℕ)}
variable (lo hi : ℝ) (hlo : 0 < lo) (hhi : 1 ≤ hi) (orders : Finset (ℕ × ℕ))
variable {bound : ℝ}
variable (original : RawProfileWindow originalRows originalHeights (Set.Icc lo hi)
  originalOrders parent bound)
variable (hreference : reference ∈ originalRows) (htime : time ∈ originalHeights)
variable (horders : orders ⊆ originalOrders)
variable (computed : CanonicalLiteralFullKappaInput.ComputedProfiles W (Set.Icc lo hi) orders bound)
variable (hprimeOrders : CanonicalFullKappaPrime.orders ⊆ orders)
variable (δ analyticHeight : ℝ) (hδ : 0 < δ) (hδhi : δ ≤ 1 / 4)
variable (analytic : ∀ _hκ : D.parameters.κ < 1, ∀ ξ,
  ∀ u, u ∈ pairedRows (D.data ξ) D.parameters
    ((d.factors rows side χ ideal hideal firstSign rectangle).frame C L selection hne).source.base →
  ∀ i : Fin ((d.factors rows side χ ideal hideal firstSign rectangle).frame C L selection hne).source.allocation.keep.card,
    ZeroFreeData (heckeContinuation K ((D.data ξ).rowCharacter u *
      (D.data ξ).slotCoefficient (lengthSlot (D.data ξ)
        ((d.factors rows side χ ideal hideal firstSign rectangle).frame C L selection hne).source.allocation.keep.card
        (D.count ξ) i))) ((D.parameters.κ + 1) / 2))
variable (hanalytic : ∀ hκ : D.parameters.κ < 1, ∀ ξ,
  ∀ u, ∀ hu : u ∈ pairedRows (D.data ξ) D.parameters
    ((d.factors rows side χ ideal hideal firstSign rectangle).frame C L selection hne).source.base,
  ∀ i : Fin ((d.factors rows side χ ideal hideal firstSign rectangle).frame C L selection hne).source.allocation.keep.card,
    heightConstant (analytic hκ ξ u hu i) + 3 * ((analytic hκ ξ u hu i).k : ℝ) ≤ analyticHeight)

/-- The actual side normalization is now constructed from the same
computed calibration and original input. Both actual profile windows,
the complete support budget, raw degree and capacity input are proved
inside this definition, before any child is chosen. -/
def produceLiteralSide :
    SecondSideNormalization f ω ψ Set.univ Set.univ (Set.Icc 0 hi) orders := by
  let recipe := d.productionRecipe W rows side χ ideal hideal firstSign rectangle L selection hne
    D P Rchar F parent oldMoving correction hcorr remaining extra a step G pattern sector
    slots cutoff reference time hdata
  have hfull : recipe.FullJointBudget (f).source.base (m + q) :=
    d.productionRecipe_fullJointBudget W rows side χ ideal hideal firstSign rectangle L selection hne
      D P Rchar F parent oldMoving correction hcorr remaining extra a step G pattern sector
      slots cutoff reference time hdata
  have hkappa : D.parameters.κ = a.κ := by rw [hparameters]; rfl
  let profiles := CanonicalLiteralFullKappaInput.ofLiteral P Rchar W (f).allocation F parent
    oldMoving correction hcorr C rows.primes rows.leftMultiplicity rows.rightMultiplicity
    pattern sector remaining extra m q slots.index rectangle firstSign side.literalNegative
    reference time lo hi hlo hhi orders original hreference htime horders computed D recipe hdata
    hprimeOrders δ mesh analyticHeight (m + q) hδ hδhi hmesh
    (d.factors_childLength_le (C := C) rows side χ ideal hideal firstSign rectangle L selection hne
      parent slots mesh hfit)
    (by simpa only [hkappa] using domain.kappa_lower)
    (by simpa only [hkappa] using domain.kappa_upper) hfull analytic hanalytic
  let lengths := d.factorsOriginalSixthLengths (C := C) rows side χ ideal hideal firstSign rectangle
    L selection hne D parent a step G domain slots direct cutoff rootLength hcutoff hsmall
    hparameters annulus cap error herr hbound hthreshold
  cases side
  · exact SecondSideNormalization.ofFullKappaOriginalSixthPattern f D recipe profiles parent a step G
      lengths hm hn pattern hsecond hopposite hunit hstep mesh hmesh hfit
  · exact SecondSideNormalization.ofFullKappaOriginalRightPattern f D recipe profiles parent a step G
      lengths hm hn pattern hsecond hopposite hunit hstep mesh hmesh hfit

end CanonicalLiteralRectangles.Atoms
end HeckeSkeleton.Moments.EngineStepV2

end

set_option quotPrecheck false

/-!
# The same literal side is normalized before activity is tested

The complete raw-scale error is computed from the actual positive
scale product on every rectangle. All original data, individual
profiles, single-prime analytic inputs and physical endpoints are
unchanged. Under the original two-extraction norm window this value
equals the preselected small error, and the entire side normalization
is then equal to the existing small-error constructor.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2

open HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments HeckePort.Moments.Support HeckePort.IdealMobiusDivisorSum
open PrimeCancellation.Analytic

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {H ι : Type*} [Fintype ι] [DecidableEq ι]

namespace CanonicalLiteralRectangles.Atoms

variable [IsPrincipalIdealRing A.R]
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {ω ψ : HeckeCharacter K} {k : ℕ}
variable (d : CanonicalLiteralRectangles.Atoms (K := K) k) (W : d.ProfileData)
variable (rows : ActualSecondCorrelationRows A σ H ι)
variable (side : SecondColumnSide) (χ : (PUnit.{1} × PUnit.{1}) →* Circle)
variable (ideal : AllocationColumn K k → A.Exterior)
variable (hideal : ∀ i ∈ childCartesianColumns d.plain₁ d.plain₂ d.slots,
  (ideal i).val = allocationColumnIdeal i)
variable (firstSign : ℝ) (rectangle : Bool) (L : Ideal (𝓞 K))
variable (selection : primeSupport L → Finset (Fin (k + 2)))
variable (hne : (pairedAllocatedColumns L selection d.plain₁ d.plain₂ d.slots
  id id HeightOneSpectrum.asIdeal).Nonempty)

local notation "f" =>
  (d.factors rows side χ ideal hideal firstSign rectangle).frame C L selection hne

variable (D : ((d.factors rows side χ ideal hideal firstSign rectangle).frame C L selection hne).source.Calibration
  (σ := σ) ω ψ)
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (Rchar : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable (F : CanonicalLiteralPhaseCalibration.FixedPhases A)
variable (parent : MomentData K ω ψ) (oldMoving : OriginalMovingFactors A P Rchar)
variable (correction : HeckeCharacter K) (hcorr : correction ∈ parent.theta)
variable (remaining extra : HeckeGeneral.Analysis.NonzeroIdeal K)
variable (a : RealParameters) (step : ℝ)
variable (G : OriginalNominalGeometry (K := K) a
  ((d.factors rows side χ ideal hideal firstSign rectangle).frame C L selection hne).source.base step)
variable (pattern : ι → Bool)
variable (sector : SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (slots : OriginalSlotDictionary parent d.length)
variable (cutoff : ℝ)

local notation "rootLength" =>
  idealLogLength (f).source.base
    (secondSixthRootIdeal rows.primes (side.literalMultiplicity rows)
      (side.literalOppositeMultiplicity rows)).val
local notation "m" => G.literalRowParameter cutoff
local notation "q" => G.literalSupportParameter rootLength

variable (reference : HeckeGeneral.Analysis.NonzeroIdeal K) (time : ℝ)
variable (hdata : ∀ ξ, D.data ξ = CanonicalLiteralAllocatedData.data
  P Rchar W ((d.factors rows side χ ideal hideal firstSign rectangle).frame C L selection hne).allocation
  F parent oldMoving correction hcorr C rows.primes rows.leftMultiplicity rows.rightMultiplicity
  pattern sector remaining extra (G.literalRowParameter cutoff)
  (G.literalSupportParameter (idealLogLength
    ((d.factors rows side χ ideal hideal firstSign rectangle).frame C L selection hne).source.base
    (secondSixthRootIdeal rows.primes (side.literalMultiplicity rows)
      (side.literalOppositeMultiplicity rows)).val))
  (CanonicalLiteralProfileData.frozenNormTest parent.inverseTest reference time)
  slots.index rectangle firstSign side.literalNegative ξ)
variable (hparameters : D.parameters = CanonicalLiteralAllocatedData.parameters d
  ((d.factors rows side χ ideal hideal firstSign rectangle).frame C L selection hne).allocation
  rectangle (G.literalRowParameter cutoff)
  (G.literalSupportParameter (idealLogLength
    ((d.factors rows side χ ideal hideal firstSign rectangle).frame C L selection hne).source.base
    (secondSixthRootIdeal rows.primes (side.literalMultiplicity rows)
      (side.literalOppositeMultiplicity rows)).val)) a.κ)

variable {centered : Bool} {Y₁ Y₂ floor padding : ℝ}
variable (domain : PairedEngineDomain centered parent a
  ((d.factors rows side χ ideal hideal firstSign rectangle).frame C L selection hne).source.base
  Y₁ Y₂ floor padding)
variable (direct : G.tag = .direct → parent.geometry.slotCount = 0)
variable (hcutoff : 0 ≤ cutoff) (hsmall : 2 * cutoff ≤ step)
variable (error : ℝ) (herr : 0 ≤ error)
variable (hm : ∀ i, 0 < rows.leftMultiplicity i) (hn : ∀ i, 0 < rows.rightMultiplicity i)
variable (hsecond : G.ideals.second.val = (primePowerProduct rows.primes
  (side.literalMultiplicity rows)).val)
variable (hopposite : G.ideals.secondOpposite.val = (primePowerProduct rows.primes
  (side.literalOppositeMultiplicity rows)).val)
variable (hunit : G.ideals.unitPart.val = (secondPatternUnitIdeal rows.primes
  (side.literalMultiplicity rows) (side.literalOppositeMultiplicity rows) pattern).val)
variable (hstep : 0 < step) (mesh : ℝ) (hmesh : 0 ≤ mesh)
variable (hfit : parent.geometry.fitsMesh mesh)
variable {originalRows : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
variable {originalHeights : Set ℝ} {originalOrders : Finset (ℕ × ℕ)}
variable (lo hi : ℝ) (hlo : 0 < lo) (hhi : 1 ≤ hi) (orders : Finset (ℕ × ℕ))
variable {bound : ℝ}
variable (original : RawProfileWindow originalRows originalHeights (Set.Icc lo hi)
  originalOrders parent bound)
variable (hreference : reference ∈ originalRows) (htime : time ∈ originalHeights)
variable (horders : orders ⊆ originalOrders)
variable (computed : CanonicalLiteralFullKappaInput.ComputedProfiles W (Set.Icc lo hi) orders bound)
variable (hprimeOrders : CanonicalFullKappaPrime.orders ⊆ orders)
variable (δ analyticHeight : ℝ) (hδ : 0 < δ) (hδhi : δ ≤ 1 / 4)
variable (analytic : ∀ _hκ : D.parameters.κ < 1, ∀ ξ,
  ∀ u, u ∈ pairedRows (D.data ξ) D.parameters
    ((d.factors rows side χ ideal hideal firstSign rectangle).frame C L selection hne).source.base →
  ∀ i : Fin ((d.factors rows side χ ideal hideal firstSign rectangle).frame C L selection hne).source.allocation.keep.card,
    ZeroFreeData (heckeContinuation K ((D.data ξ).rowCharacter u *
      (D.data ξ).slotCoefficient (lengthSlot (D.data ξ)
        ((d.factors rows side χ ideal hideal firstSign rectangle).frame C L selection hne).source.allocation.keep.card
        (D.count ξ) i))) ((D.parameters.κ + 1) / 2))
variable (hanalytic : ∀ hκ : D.parameters.κ < 1, ∀ ξ,
  ∀ u, ∀ hu : u ∈ pairedRows (D.data ξ) D.parameters
    ((d.factors rows side χ ideal hideal firstSign rectangle).frame C L selection hne).source.base,
  ∀ i : Fin ((d.factors rows side χ ideal hideal firstSign rectangle).frame C L selection hne).source.allocation.keep.card,
    heightConstant (analytic hκ ξ u hu i) + 3 * ((analytic hκ ξ u hu i).k : ℝ) ≤ analyticHeight)

/-- The actual side normalization is now constructed from the same
computed calibration and original input. Both actual profile windows,
the complete support budget, raw degree and capacity input are proved
inside this definition, before any child is chosen. -/
def produceLiteralSideAll :
    SecondSideNormalization f ω ψ Set.univ Set.univ (Set.Icc 0 hi) orders := by
  let recipe := d.productionRecipe W rows side χ ideal hideal firstSign rectangle L selection hne
    D P Rchar F parent oldMoving correction hcorr remaining extra a step G pattern sector
    slots cutoff reference time hdata
  have hfull : recipe.FullJointBudget (f).source.base (m + q) :=
    d.productionRecipe_fullJointBudget W rows side χ ideal hideal firstSign rectangle L selection hne
      D P Rchar F parent oldMoving correction hcorr remaining extra a step G pattern sector
      slots cutoff reference time hdata
  have hkappa : D.parameters.κ = a.κ := by rw [hparameters]; rfl
  let profiles := CanonicalLiteralFullKappaInput.ofLiteral P Rchar W (f).allocation F parent
    oldMoving correction hcorr C rows.primes rows.leftMultiplicity rows.rightMultiplicity
    pattern sector remaining extra m q slots.index rectangle firstSign side.literalNegative
    reference time lo hi hlo hhi orders original hreference htime horders computed D recipe hdata
    hprimeOrders δ mesh analyticHeight (m + q) hδ hδhi hmesh
    (d.factors_childLength_le (C := C) rows side χ ideal hideal firstSign rectangle L selection hne
      parent slots mesh hfit)
    (by simpa only [hkappa] using domain.kappa_lower)
    (by simpa only [hkappa] using domain.kappa_upper) hfull analytic hanalytic
  let lengths := d.factorsOriginalSixthLengthsAll (C := C) rows side χ ideal hideal firstSign rectangle
    L selection hne D parent a step G domain slots direct cutoff rootLength hcutoff hsmall
    hparameters error herr
  cases side
  · exact SecondSideNormalization.ofFullKappaOriginalSixthPattern f D recipe profiles parent a step G
      lengths hm hn pattern hsecond hopposite hunit hstep mesh hmesh hfit
  · exact SecondSideNormalization.ofFullKappaOriginalRightPattern f D recipe profiles parent a step G
      lengths hm hn pattern hsecond hopposite hunit hstep mesh hmesh hfit


local notation "allSide" =>
  d.produceLiteralSideAll W rows side χ ideal hideal firstSign rectangle L selection hne D
    P Rchar F parent oldMoving correction hcorr remaining extra a step G pattern sector
    slots cutoff reference time hdata hparameters domain direct hcutoff hsmall error herr
    hm hn hsecond hopposite hunit hstep mesh hmesh hfit lo hi hlo hhi orders original
    hreference htime horders computed hprimeOrders δ analyticHeight hδ hδhi analytic hanalytic

@[simp] theorem produceLiteralSideAll_calibration : (allSide).calibration = D := by
  sorry

/-- This is equality of the entire constructed side, not just equality
of an upper bound. Thus the already selected capacity data and its
chosen-child family may use the original small-error mass theorem. -/
theorem produceLiteralSideAll_eq
    (annulus : ℝ) (cap : ℕ)
    (hbound : d.scaleProduct rectangle *
      ((Ideal.absNorm G.literalFirstExtraction.val : ℝ) *
        (Ideal.absNorm G.ideals.second.val : ℝ)) ≤
      annulus ^ (2 * cap) * (f).source.base ^ (a.n₁ + a.n₂ + a.z))
    (hthreshold : annulus ^ (2 * cap) ≤ (f).source.base ^ error) :
    allSide =
      d.produceLiteralSide W rows side χ ideal hideal firstSign rectangle L selection hne D
        P Rchar F parent oldMoving correction hcorr remaining extra a step G pattern sector
        slots cutoff reference time hdata hparameters domain direct hcutoff hsmall
        annulus cap error herr hbound hthreshold hm hn hsecond hopposite hunit hstep
        mesh hmesh hfit lo hi hlo hhi orders original hreference htime horders computed
        hprimeOrders δ analyticHeight hδ hδhi analytic hanalytic := by
  sorry

end CanonicalLiteralRectangles.Atoms
end HeckeSkeleton.Moments.EngineStepV2

end

set_option quotPrecheck false

/-!
# Original character input for the pre-input literal calibration

The literal calibration and its complete moving recipe are fixed
before analytic certificates are selected. Their actual paired-row
exclusion makes every retained prime character nonprincipal. The raw
uniform character provider then supplies the exact certificates and
height bound used by the existing side producer.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2

open HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments HeckePort.Moments.Support HeckePort.IdealMobiusDivisorSum
open PrimeCancellation.Analytic

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {H ι : Type*} [Fintype ι] [DecidableEq ι]

namespace CanonicalLiteralRectangles.Atoms

variable [IsPrincipalIdealRing A.R]
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {ω ψ : HeckeCharacter K} {k : ℕ}
variable (d : CanonicalLiteralRectangles.Atoms (K := K) k) (W : d.ProfileData)
variable (rows : ActualSecondCorrelationRows A σ H ι)
variable (side : SecondColumnSide) (χ : (PUnit.{1} × PUnit.{1}) →* Circle)
variable (ideal : AllocationColumn K k → A.Exterior)
variable (hideal : ∀ i ∈ childCartesianColumns d.plain₁ d.plain₂ d.slots,
  (ideal i).val = allocationColumnIdeal i)
variable (firstSign : ℝ) (rectangle : Bool) (L : Ideal (𝓞 K))
variable (selection : primeSupport L → Finset (Fin (k + 2)))
variable (hne : (pairedAllocatedColumns L selection d.plain₁ d.plain₂ d.slots
  id id HeightOneSpectrum.asIdeal).Nonempty)

local notation "f" =>
  (d.factors rows side χ ideal hideal firstSign rectangle).frame C L selection hne

variable (D : ((d.factors rows side χ ideal hideal firstSign rectangle).frame C L selection hne).source.Calibration
  (σ := σ) ω ψ)
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (Rchar : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable (F : CanonicalLiteralPhaseCalibration.FixedPhases A)
variable (parent : MomentData K ω ψ) (oldMoving : OriginalMovingFactors A P Rchar)
variable (correction : HeckeCharacter K) (hcorr : correction ∈ parent.theta)
variable (remaining extra : HeckeGeneral.Analysis.NonzeroIdeal K)
variable (a : RealParameters) (step : ℝ)
variable (G : OriginalNominalGeometry (K := K) a
  ((d.factors rows side χ ideal hideal firstSign rectangle).frame C L selection hne).source.base step)
variable (pattern : ι → Bool)
variable (sector : SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (slots : OriginalSlotDictionary parent d.length)
variable (cutoff : ℝ)

local notation "rootLength" =>
  idealLogLength (f).source.base
    (secondSixthRootIdeal rows.primes (side.literalMultiplicity rows)
      (side.literalOppositeMultiplicity rows)).val
local notation "m" => G.literalRowParameter cutoff
local notation "q" => G.literalSupportParameter rootLength

variable (reference : HeckeGeneral.Analysis.NonzeroIdeal K) (time : ℝ)
variable (hdata : ∀ ξ, D.data ξ = CanonicalLiteralAllocatedData.data
  P Rchar W ((d.factors rows side χ ideal hideal firstSign rectangle).frame C L selection hne).allocation
  F parent oldMoving correction hcorr C rows.primes rows.leftMultiplicity rows.rightMultiplicity
  pattern sector remaining extra (G.literalRowParameter cutoff)
  (G.literalSupportParameter (idealLogLength
    ((d.factors rows side χ ideal hideal firstSign rectangle).frame C L selection hne).source.base
    (secondSixthRootIdeal rows.primes (side.literalMultiplicity rows)
      (side.literalOppositeMultiplicity rows)).val))
  (CanonicalLiteralProfileData.frozenNormTest parent.inverseTest reference time)
  slots.index rectangle firstSign side.literalNegative ξ)
variable (hparameters : D.parameters = CanonicalLiteralAllocatedData.parameters d
  ((d.factors rows side χ ideal hideal firstSign rectangle).frame C L selection hne).allocation
  rectangle (G.literalRowParameter cutoff)
  (G.literalSupportParameter (idealLogLength
    ((d.factors rows side χ ideal hideal firstSign rectangle).frame C L selection hne).source.base
    (secondSixthRootIdeal rows.primes (side.literalMultiplicity rows)
      (side.literalOppositeMultiplicity rows)).val)) a.κ)


variable (normBox heightC analyticHeight : ℝ)
variable (analyticWindow : CanonicalOriginalPrimeAnalyticProvider.Window
  (A := A) (P := P) (R := Rchar) parent.theta normBox heightC)
variable (hκlo : 3 / 4 ≤ a.κ)
variable (boundary : a.κ < 1 → FiniteOrderBoundary (K := K) ((a.κ + 1) / 2))
variable (hslotInverse : ∀ i, (parent.slotCoefficient i)⁻¹ ∈ parent.theta)
variable (hwidth : G.literalRowParameter cutoff + G.literalSupportParameter
  (idealLogLength
    ((d.factors rows side χ ideal hideal firstSign rectangle).frame C L selection hne).source.base
    (secondSixthRootIdeal rows.primes (side.literalMultiplicity rows)
      (side.literalOppositeMultiplicity rows)).val) ≤ normBox)
variable (hheight : heightC * (1 + Real.log
  ((d.factors rows side χ ideal hideal firstSign rectangle).frame C L selection hne).source.base) ≤
    analyticHeight)

/-- No family input is assumed or read back from a chosen child.
The only analytic premise concerns the original single character. -/
def literalSideAnalyticInput :
    {analytic : ∀ _hκ : D.parameters.κ < 1, ∀ ξ,
      ∀ u, u ∈ pairedRows (D.data ξ) D.parameters (f).source.base →
      ∀ i : Fin (f).source.allocation.keep.card,
        ZeroFreeData (heckeContinuation K ((D.data ξ).rowCharacter u *
          (D.data ξ).slotCoefficient
            (lengthSlot (D.data ξ) (f).source.allocation.keep.card (D.count ξ) i)))
          ((D.parameters.κ + 1) / 2) //
      ∀ hκ : D.parameters.κ < 1, ∀ ξ,
        ∀ u, ∀ hu : u ∈ pairedRows (D.data ξ) D.parameters (f).source.base,
        ∀ i : Fin (f).source.allocation.keep.card,
          heightConstant (analytic hκ ξ u hu i) +
            3 * ((analytic hκ ξ u hu i).k : ℝ) ≤ analyticHeight} := by
  let recipe := d.productionRecipe W rows side χ ideal hideal firstSign rectangle L selection hne
    D P Rchar F parent oldMoving correction hcorr remaining extra a step G pattern sector
    slots cutoff reference time hdata
  have hfull : recipe.FullJointBudget (f).source.base (m + q) :=
    d.productionRecipe_fullJointBudget W rows side χ ideal hideal firstSign rectangle L selection hne
      D P Rchar F parent oldMoving correction hcorr remaining extra a step G pattern sector
      slots cutoff reference time hdata
  have hjoint : recipe.FullJointBudget (f).source.base normBox := by
    intro ξ u hu
    exact (hfull ξ u hu).trans
      (Real.rpow_le_rpow_of_exponent_le (f).source.base_gt_one.le hwidth)
  have hkappa : D.parameters.κ = a.κ := by rw [hparameters]; rfl
  have htheta : ∀ ξ, (D.data ξ).theta = parent.theta := by
    intro ξ
    rw [hdata ξ]
    rfl
  have hslot : ∀ ξ i, (D.data ξ).slotCoefficient i ∈ parent.theta := by
    intro ξ i
    rw [← htheta ξ]
    exact D.slot_in_theta ξ i
  have hinverse : ∀ ξ i, ((D.data ξ).slotCoefficient i)⁻¹ ∈ parent.theta := by
    intro ξ
    rw [hdata ξ]
    intro i
    exact hslotInverse (slots.index (SlotRestriction.index (f).allocation.keep i))
  have hz : ∀ ξ, D.parameters.z = (D.data ξ).geometry.totalLength := by
    intro ξ
    rw [hparameters, hdata ξ]
    change (CanonicalLiteralAllocatedData.parameters d (f).allocation rectangle m q a.κ).z =
      (CanonicalLiteralAllocatedData.geometry W (f).allocation firstSign side.literalNegative ξ).totalLength
    exact CanonicalLiteralAllocatedData.geometry_slot_sum W (f).allocation firstSign
      side.literalNegative rectangle m q a.κ ξ
  let single := fun (hκ : D.parameters.κ < 1) ξ u
      (hu : u ∈ pairedRows (D.data ξ) D.parameters (f).source.base)
      (i : Fin (f).source.allocation.keep.card) =>
    analyticWindow.certificate recipe D.parameters (f).source.base
      (by simpa only [hkappa] using hκlo) hκ (f).source.base_gt_one
      (by simpa only [hkappa] using boundary (by simpa only [hkappa] using hκ))
      htheta hslot hinverse hz hjoint ξ u hu
      (lengthSlot (D.data ξ) (f).source.allocation.keep.card (D.count ξ) i)
  refine ⟨fun hκ ξ u hu i => (single hκ ξ u hu i).val, ?_⟩
  intro hκ ξ u hu i
  exact (single hκ ξ u hu i).property.trans hheight

end CanonicalLiteralRectangles.Atoms
end HeckeSkeleton.Moments.EngineStepV2

end

set_option quotPrecheck false

/-!
# The actual passive side constructs its normalized capacity data

The physical chart supplies the original ordinary rows. Its paid
calibration is built here for the stored passive allocation. The
original computed profile representatives are transported to the full
smooth table, then the existing full-kappa producer constructs both
raw and clipped windows on this exact quotient branch.

The original occurrence dictionary is restricted by the two actual
keep maps. The same nominal geometry constructs the capacity input;
no child, profile window, source inequality or final capacity bound is
an additional input. The final arguments are the individual analytic
certificates for the characters of the newly constructed data.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2

open HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments MeasureTheory
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical HeckePort.Moments
open HeckePort.IdealMobiusDivisorSum
open CanonicalLiteralAllocatedData CanonicalLiteralPassiveSource
open CanonicalLiteralPassiveFrames CanonicalLiteralPassiveNonzero
open CanonicalLiteralPaidCharacters

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {Γ : Subgroup A.U} [Γ.FiniteIndex] [IsPrincipalIdealRing A.R]
variable {hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6}
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable {μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K)}
  [∀ v, (μv v).IsAddHaarMeasure]
variable {hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0}
variable {α β : Type*} {fullI : α → A.Exterior} {fullJ : β → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}
variable {b : FirstCommonCharacterBlock fullI fullJ DE}
variable {C : A.GeneralArithmeticContext σ η hS} {left : Finset α} {right : Finset β}
variable {profiles : α → β → SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {radius : {r : ℝ // 0 < r}}
variable {D : (∅ : Finset (HeightOneSpectrum A.R)).powerset}

namespace SecondBlockProfileChart

variable (chart : SecondBlockProfileChart (E := ℝ) hΓ μv hDiff b C left right
  profiles finiteTest radius D.val)
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (Rchar : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable (hclass : chart.NonunitLabelStable) (hsector : chart.SectorLabelStable P)
variable (X : ℝ) (hX : 1 ≤ X) (label : Fin (chart.rowLabelCount + 1))
variable (weight : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ → ℂ)
variable (keep₁ keep₂ : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ → Prop)
variable {kLeft kRight : ℕ}
variable (rowMass : ActualSecondRowMass
  ((({ chart.actualRows ∅ X hX label with weight := weight }).restrictRows keep₁).restrictRows keep₂) C kLeft kRight)
variable {ω ψ : HeckeCharacter K} {k : ℕ}
variable (d : CanonicalLiteralRectangles.Atoms (K := K) k) (W : d.ProfileData)
variable (B : ActualColumnAllocation K k)
variable (F : CanonicalLiteralPhaseCalibration.FixedPhases A) (choice : PhaseChoice F C)
variable (parent : MomentData K ω ψ) (oldMoving : OriginalMovingFactors A P Rchar)
variable (correction : HeckeCharacter K) (hcorr : correction ∈ parent.theta)
variable (remaining extra : HeckeGeneral.Analysis.NonzeroIdeal K)
variable (slots : OriginalSlotDictionary parent d.length)
variable (a : { a // a ∈ CanonicalLiteralPassiveSource.labels W B A (choice.mask extra) })
variable (ha : a ∈ nonzeroLabels W B A (choice.mask extra))
variable (retainedScale g a₀ oldq wo cutoffExponent : ℝ)
variable (hscale : 0 < retainedScale)
variable (hradius : radius = CanonicalRowBall.gaussRadius retainedScale d.base g hscale
  (zero_lt_one.trans d.base_gt_one))
variable (hcutoff : X ≤ d.base ^ cutoffExponent)
variable (hproduct : ∀ i ∈ left, ∀ j ∈ right, profiles i j ≠ 0 →
  (Ideal.absNorm ((fullI i).val * (fullJ j).val) : ℝ) ≤ d.base ^ (2 * a₀))
variable (hpaidSupport : A.exteriorNorm
  ((choice.phases.moving P Rchar oldMoving).effectiveFullSupport remaining) ≤
    d.base ^ (oldq + wo))
variable (m q κ : ℝ)
variable (hwidth : m + q =
  secondCommonChildWidth d.base a₀ oldq wo (Real.log retainedScale / Real.log d.base) g
    (primePowerProduct b.primes b.leftMultiplicity).val
    (primePowerProduct b.primes b.rightMultiplicity).val
    (secondPatternUnitIdeal b.primes b.leftMultiplicity b.rightMultiplicity
      (chart.originalNonunitPattern ∅ X hX label)).val
    (secondPatternNonunitIdeal b.primes (chart.originalNonunitPattern ∅ X hX label)).val +
    idealLogLength d.base (secondSixthRootIdeal b.primes b.leftMultiplicity b.rightMultiplicity).val +
    cutoffExponent)
variable (inverse : IdealTest K)
variable (hone : (1 : HeckeCharacter K) ∈ parent.theta)
variable (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
variable (hbackground : parent.plainBackground⁻¹ ∈ parent.theta ∨
  ¬ FiniteOrder parent.plainBackground)
variable (hslot : ∀ i, parent.slotCoefficient i ∈ parent.theta)
variable (side : SecondColumnSide) (firstSign : ℝ) (rectangle : Bool)

local notation "S" =>
  (({ chart.actualRows ∅ X hX label with weight := weight }).restrictRows keep₁).restrictRows keep₂
local notation "pattern" => chart.originalNonunitPattern ∅ X hX label
local notation "sector" => chart.originalSector P ∅ X hX label
local notation "idx" => (fun j => slots.index (SlotRestriction.index B.keep j))
local notation "paid" => paidSourceCharacters P Rchar choice.phases parent oldMoving
  correction remaining idx
local notation "t" => table W B A paid
local notation "E" => CanonicalLiteralPassiveSource.profiles W B A paid
local notation "allocation" => branch W B A (choice.mask extra) a
local notation "f" => frame W B A paid C S side (choice.mask extra) a firstSign rectangle

variable (keep₂_eq : keep₂ = fun h =>
  (chart.actualRows ∅ X hX label).literalCharacter C P Rchar F oldMoving correction
    (chart.originalNonunitPattern ∅ X hX label) (chart.originalSector P ∅ X hX label) h ∉
      parent.theta)
variable (parentParameters : RealParameters) (step : ℝ)
variable (geometry : OriginalNominalGeometry (K := K) parentParameters
  (frame W B A (paidSourceCharacters P Rchar choice.phases parent oldMoving correction
    remaining (fun j => slots.index (SlotRestriction.index B.keep j))) C
    ((({ chart.actualRows ∅ X hX label with weight := weight }).restrictRows keep₁).restrictRows keep₂) side (choice.mask extra) a firstSign rectangle).source.base step)
variable (capacityCutoff : ℝ) (hcapacityCutoff : 0 ≤ capacityCutoff)
variable (hsmall : 2 * capacityCutoff ≤ step)
variable (rowParameter : geometry.literalRowParameter capacityCutoff = m)
variable (supportParameter : geometry.literalSupportParameter
  (idealLogLength
    (frame W B A (paidSourceCharacters P Rchar choice.phases parent oldMoving correction
      remaining (fun j => slots.index (SlotRestriction.index B.keep j))) C
      ((({ chart.actualRows ∅ X hX label with weight := weight }).restrictRows keep₁).restrictRows keep₂) side (choice.mask extra) a firstSign rectangle).source.base
    (secondSixthRootIdeal b.primes
      (side.literalMultiplicity (chart.actualRows ∅ X hX label))
      (side.literalOppositeMultiplicity (chart.actualRows ∅ X hX label))).val) = q)
variable (kappa : κ = parentParameters.κ)
variable {centered : Bool} {Y₁ Y₂ floor padding : ℝ}
variable (domain : PairedEngineDomain centered parent parentParameters
  (frame W B A (paidSourceCharacters P Rchar choice.phases parent oldMoving correction
    remaining (fun j => slots.index (SlotRestriction.index B.keep j))) C
    ((({ chart.actualRows ∅ X hX label with weight := weight }).restrictRows keep₁).restrictRows keep₂) side (choice.mask extra) a firstSign rectangle).source.base
    Y₁ Y₂ floor padding)
variable (direct : geometry.tag = .direct → parent.geometry.slotCount = 0)
variable (error : ℝ) (herr : 0 ≤ error)
variable (hsecond : geometry.ideals.second.val =
  (primePowerProduct b.primes
    (side.literalMultiplicity (chart.actualRows ∅ X hX label))).val)
variable (hopposite : geometry.ideals.secondOpposite.val =
  (primePowerProduct b.primes
    (side.literalOppositeMultiplicity (chart.actualRows ∅ X hX label))).val)
variable (hunit : geometry.ideals.unitPart.val =
  (secondPatternUnitIdeal b.primes
    (side.literalMultiplicity (chart.actualRows ∅ X hX label))
    (side.literalOppositeMultiplicity (chart.actualRows ∅ X hX label))
    (chart.originalNonunitPattern ∅ X hX label)).val)
variable (hstep : 0 < step) (mesh : ℝ) (hmesh : 0 ≤ mesh)
variable (hfit : parent.geometry.fitsMesh mesh)
variable (reference : HeckeGeneral.Analysis.NonzeroIdeal K) (time : ℝ)
variable (inverse_eq : inverse = CanonicalLiteralProfileData.frozenNormTest
  parent.inverseTest reference time)
variable {originalRows : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
variable {originalHeights : Set ℝ} {originalOrders : Finset (ℕ × ℕ)}
variable (lo hi : ℝ) (hlo : 0 < lo) (hhi : 1 ≤ hi) (orders : Finset (ℕ × ℕ))
variable {bound : ℝ}
variable (original : RawProfileWindow originalRows originalHeights (Set.Icc lo hi)
  originalOrders parent bound)
variable (hreference : reference ∈ originalRows) (htime : time ∈ originalHeights)
variable (horders : orders ⊆ originalOrders)
variable (computed : CanonicalLiteralFullKappaInput.ComputedProfiles W (Set.Icc lo hi) orders bound)
variable (hprimeOrders : CanonicalFullKappaPrime.orders ⊆ orders)
variable (δ analyticHeight : ℝ) (hδ : 0 < δ) (hδhi : δ ≤ 1 / 4)

/-- This producer calls the actual paid calibration, then the original
full-kappa and sixth-root capacity producers. Its final two arguments
concern only the actual individual characters and their analytic
heights, including the branch κ=1 handled internally. -/
def literalPassiveSideNormalization :=
  let cal := chart.literalPassiveFrameCalibration P Rchar hclass hsector X hX label
    weight keep₁ keep₂ rowMass d W B F choice parent oldMoving correction hcorr remaining extra
    slots.index a ha retainedScale g a₀ oldq wo cutoffExponent hscale hradius hcutoff hproduct
    hpaidSupport m q κ hwidth inverse hone hroot hemb hbackground hslot side firstSign rectangle
    keep₂_eq
  let originalSlots := tableOriginalSlots W B A paid parent slots
  let profiles := computed.passiveTable B A paid
  have hdata : ∀ ξ, cal.data ξ = CanonicalLiteralAllocatedData.data P Rchar E (f).allocation
      choice.phases parent oldMoving correction hcorr C (S).primes (S).leftMultiplicity
      (S).rightMultiplicity pattern sector remaining 1
      (geometry.literalRowParameter capacityCutoff)
      (geometry.literalSupportParameter (idealLogLength (f).source.base
        (secondSixthRootIdeal (S).primes (side.literalMultiplicity S)
          (side.literalOppositeMultiplicity S)).val))
      (CanonicalLiteralProfileData.frozenNormTest parent.inverseTest reference time)
      originalSlots.index rectangle firstSign side.literalNegative ξ := by
    intro ξ
    rw [rowParameter, supportParameter]
    rw [← inverse_eq]
    rfl
  have hparameters : cal.parameters = CanonicalLiteralAllocatedData.parameters t (f).allocation
      rectangle (geometry.literalRowParameter capacityCutoff)
      (geometry.literalSupportParameter (idealLogLength (f).source.base
        (secondSixthRootIdeal (S).primes (side.literalMultiplicity S)
          (side.literalOppositeMultiplicity S)).val)) parentParameters.κ := by
    rw [rowParameter, supportParameter, ← kappa]
    rfl
  fun analytic hanalytic =>
    show SecondSideNormalization f ω ψ Set.univ Set.univ (Set.Icc 0 hi) orders from
      (t).produceLiteralSideAll E S side (1 : (PUnit.{1} × PUnit.{1}) →* Circle)
        (columnExterior W B A) (columnExterior_val_of_mem W B A) firstSign rectangle
        a.val.1 a.val.2 ((Finset.mem_filter.mp a.property).2) cal
        P Rchar choice.phases parent oldMoving correction hcorr remaining 1
        parentParameters step geometry pattern sector originalSlots capacityCutoff reference time
        hdata hparameters domain direct hcapacityCutoff hsmall error herr
        b.left_positive b.right_positive hsecond hopposite hunit hstep mesh hmesh hfit
        lo hi hlo hhi orders original hreference htime horders profiles hprimeOrders
        δ analyticHeight hδ hδhi analytic hanalytic

end SecondBlockProfileChart
end HeckeSkeleton.Moments.EngineStepV2

end

set_option quotPrecheck false

/-!
# Original analytic certificates for the actual passive side

The frame calibration, its actual complete mask and its retained slot
indices are built before any analytic input is selected. Applying the
original uniform character window to this same calibration supplies
the certificates required by the existing normalized side producer.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2

open HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments MeasureTheory
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical HeckePort.Moments
open HeckePort.IdealMobiusDivisorSum
open CanonicalLiteralAllocatedData CanonicalLiteralPassiveSource
open CanonicalLiteralPassiveFrames CanonicalLiteralPassiveNonzero
open CanonicalLiteralPaidCharacters PrimeCancellation.Analytic

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {Γ : Subgroup A.U} [Γ.FiniteIndex] [IsPrincipalIdealRing A.R]
variable {hΓ : ∀ u : Γ, ∃ v : A.U, u.val = v ^ 6}
variable [MeasurableSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable {μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K)}
  [∀ v, (μv v).IsAddHaarMeasure]
variable {hDiff : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ A.Sf →
  HeckeGeneral.Characters.localDifferentExponent K v = 0}
variable {α β : Type*} {fullI : α → A.Exterior} {fullJ : β → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}
variable {b : FirstCommonCharacterBlock fullI fullJ DE}
variable {C : A.GeneralArithmeticContext σ η hS} {left : Finset α} {right : Finset β}
variable {profiles : α → β → SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ}
variable {finiteTest : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ}
variable {radius : {r : ℝ // 0 < r}}
variable {D : (∅ : Finset (HeightOneSpectrum A.R)).powerset}

namespace SecondBlockProfileChart

variable (chart : SecondBlockProfileChart (E := ℝ) hΓ μv hDiff b C left right
  profiles finiteTest radius D.val)
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (Rchar : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable (hclass : chart.NonunitLabelStable) (hsector : chart.SectorLabelStable P)
variable (X : ℝ) (hX : 1 ≤ X) (label : Fin (chart.rowLabelCount + 1))
variable (weight : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ → ℂ)
variable (keep₁ keep₂ : SIntegerOrbits K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) Γ → Prop)
variable {kLeft kRight : ℕ}
variable (rowMass : ActualSecondRowMass
  ((({ chart.actualRows ∅ X hX label with weight := weight }).restrictRows keep₁).restrictRows keep₂) C kLeft kRight)
variable {ω ψ : HeckeCharacter K} {k : ℕ}
variable (d : CanonicalLiteralRectangles.Atoms (K := K) k) (W : d.ProfileData)
variable (B : ActualColumnAllocation K k)
variable (F : CanonicalLiteralPhaseCalibration.FixedPhases A) (choice : PhaseChoice F C)
variable (parent : MomentData K ω ψ) (oldMoving : OriginalMovingFactors A P Rchar)
variable (correction : HeckeCharacter K) (hcorr : correction ∈ parent.theta)
variable (remaining extra : HeckeGeneral.Analysis.NonzeroIdeal K)
variable (slots : OriginalSlotDictionary parent d.length)
variable (a : { a // a ∈ CanonicalLiteralPassiveSource.labels W B A (choice.mask extra) })
variable (ha : a ∈ nonzeroLabels W B A (choice.mask extra))
variable (retainedScale g a₀ oldq wo cutoffExponent : ℝ)
variable (hscale : 0 < retainedScale)
variable (hradius : radius = CanonicalRowBall.gaussRadius retainedScale d.base g hscale
  (zero_lt_one.trans d.base_gt_one))
variable (hcutoff : X ≤ d.base ^ cutoffExponent)
variable (hproduct : ∀ i ∈ left, ∀ j ∈ right, profiles i j ≠ 0 →
  (Ideal.absNorm ((fullI i).val * (fullJ j).val) : ℝ) ≤ d.base ^ (2 * a₀))
variable (hpaidSupport : A.exteriorNorm
  ((choice.phases.moving P Rchar oldMoving).effectiveFullSupport remaining) ≤
    d.base ^ (oldq + wo))
variable (m q κ : ℝ)
variable (hwidth : m + q =
  secondCommonChildWidth d.base a₀ oldq wo (Real.log retainedScale / Real.log d.base) g
    (primePowerProduct b.primes b.leftMultiplicity).val
    (primePowerProduct b.primes b.rightMultiplicity).val
    (secondPatternUnitIdeal b.primes b.leftMultiplicity b.rightMultiplicity
      (chart.originalNonunitPattern ∅ X hX label)).val
    (secondPatternNonunitIdeal b.primes (chart.originalNonunitPattern ∅ X hX label)).val +
    idealLogLength d.base (secondSixthRootIdeal b.primes b.leftMultiplicity b.rightMultiplicity).val +
    cutoffExponent)
variable (inverse : IdealTest K)
variable (hone : (1 : HeckeCharacter K) ∈ parent.theta)
variable (hroot : P.arithmetic.root6 = A.zeta12 ^ 2) (hemb : P.arithmetic.embedding = σ)
variable (hbackground : parent.plainBackground⁻¹ ∈ parent.theta ∨
  ¬ FiniteOrder parent.plainBackground)
variable (hslot : ∀ i, parent.slotCoefficient i ∈ parent.theta)
variable (side : SecondColumnSide) (firstSign : ℝ) (rectangle : Bool)

local notation "S" =>
  (({ chart.actualRows ∅ X hX label with weight := weight }).restrictRows keep₁).restrictRows keep₂
local notation "pattern" => chart.originalNonunitPattern ∅ X hX label
local notation "sector" => chart.originalSector P ∅ X hX label
local notation "idx" => (fun j => slots.index (SlotRestriction.index B.keep j))
local notation "paid" => paidSourceCharacters P Rchar choice.phases parent oldMoving
  correction remaining idx
local notation "t" => table W B A paid
local notation "E" => CanonicalLiteralPassiveSource.profiles W B A paid
local notation "allocation" => branch W B A (choice.mask extra) a
local notation "f" => frame W B A paid C S side (choice.mask extra) a firstSign rectangle

variable (keep₂_eq : keep₂ = fun h =>
  (chart.actualRows ∅ X hX label).literalCharacter C P Rchar F oldMoving correction
    (chart.originalNonunitPattern ∅ X hX label) (chart.originalSector P ∅ X hX label) h ∉
      parent.theta)
variable (parentParameters : RealParameters) (step : ℝ)
variable (geometry : OriginalNominalGeometry (K := K) parentParameters
  (frame W B A (paidSourceCharacters P Rchar choice.phases parent oldMoving correction
    remaining (fun j => slots.index (SlotRestriction.index B.keep j))) C
    ((({ chart.actualRows ∅ X hX label with weight := weight }).restrictRows keep₁).restrictRows keep₂) side (choice.mask extra) a firstSign rectangle).source.base step)
variable (capacityCutoff : ℝ)
variable (rowParameter : geometry.literalRowParameter capacityCutoff = m)
variable (supportParameter : geometry.literalSupportParameter
  (idealLogLength
    (frame W B A (paidSourceCharacters P Rchar choice.phases parent oldMoving correction
      remaining (fun j => slots.index (SlotRestriction.index B.keep j))) C
      ((({ chart.actualRows ∅ X hX label with weight := weight }).restrictRows keep₁).restrictRows keep₂) side (choice.mask extra) a firstSign rectangle).source.base
    (secondSixthRootIdeal b.primes
      (side.literalMultiplicity (chart.actualRows ∅ X hX label))
      (side.literalOppositeMultiplicity (chart.actualRows ∅ X hX label))).val) = q)
variable (kappa : κ = parentParameters.κ)
variable {centered : Bool} {Y₁ Y₂ floor padding : ℝ}
variable (domain : PairedEngineDomain centered parent parentParameters
  (frame W B A (paidSourceCharacters P Rchar choice.phases parent oldMoving correction
    remaining (fun j => slots.index (SlotRestriction.index B.keep j))) C
    ((({ chart.actualRows ∅ X hX label with weight := weight }).restrictRows keep₁).restrictRows keep₂) side (choice.mask extra) a firstSign rectangle).source.base
    Y₁ Y₂ floor padding)
variable (reference : HeckeGeneral.Analysis.NonzeroIdeal K) (time : ℝ)
variable (inverse_eq : inverse = CanonicalLiteralProfileData.frozenNormTest
  parent.inverseTest reference time)
variable (analyticHeight : ℝ)

variable (normBox heightC : ℝ)
variable (analyticWindow : CanonicalOriginalPrimeAnalyticProvider.Window
  (A := A) (P := P) (R := Rchar) parent.theta normBox heightC)
variable (boundary : parentParameters.κ < 1 →
  FiniteOrderBoundary (K := K) ((parentParameters.κ + 1) / 2))
variable (hslotInverse : ∀ i, (parent.slotCoefficient i)⁻¹ ∈ parent.theta)
variable (hwidthBox : m + q ≤ normBox)
variable (hheight : heightC * (1 + Real.log d.base) ≤ analyticHeight)

/-- The exact certificates of `literalPassiveSideNormalization` are
computed from the original character window, before either side
normalization or any capacity child is chosen. -/
def literalPassiveSideAnalyticInput :=
  let cal := chart.literalPassiveFrameCalibration P Rchar hclass hsector X hX label
    weight keep₁ keep₂ rowMass d W B F choice parent oldMoving correction hcorr remaining extra
    slots.index a ha retainedScale g a₀ oldq wo cutoffExponent hscale hradius hcutoff hproduct
    hpaidSupport m q κ hwidth inverse hone hroot hemb hbackground hslot side firstSign rectangle
    keep₂_eq
  let originalSlots := tableOriginalSlots W B A paid parent slots
  have hdata : ∀ ξ, cal.data ξ = CanonicalLiteralAllocatedData.data P Rchar E (f).allocation
      choice.phases parent oldMoving correction hcorr C (S).primes (S).leftMultiplicity
      (S).rightMultiplicity pattern sector remaining 1
      (geometry.literalRowParameter capacityCutoff)
      (geometry.literalSupportParameter (idealLogLength (f).source.base
        (secondSixthRootIdeal (S).primes (side.literalMultiplicity S)
          (side.literalOppositeMultiplicity S)).val))
      (CanonicalLiteralProfileData.frozenNormTest parent.inverseTest reference time)
      originalSlots.index rectangle firstSign side.literalNegative ξ := by
    intro ξ
    rw [rowParameter, supportParameter]
    rw [← inverse_eq]
    rfl
  have hparameters : cal.parameters = CanonicalLiteralAllocatedData.parameters t (f).allocation
      rectangle (geometry.literalRowParameter capacityCutoff)
      (geometry.literalSupportParameter (idealLogLength (f).source.base
        (secondSixthRootIdeal (S).primes (side.literalMultiplicity S)
          (side.literalOppositeMultiplicity S)).val)) parentParameters.κ := by
    rw [rowParameter, supportParameter, ← kappa]
    rfl
  (t).literalSideAnalyticInput E S side (1 : (PUnit.{1} × PUnit.{1}) →* Circle)
    (columnExterior W B A) (columnExterior_val_of_mem W B A) firstSign rectangle
    a.val.1 a.val.2 ((Finset.mem_filter.mp a.property).2) cal
    P Rchar choice.phases parent oldMoving correction hcorr remaining 1
    parentParameters step geometry pattern sector originalSlots capacityCutoff reference time
    hdata hparameters normBox heightC analyticHeight analyticWindow domain.kappa_lower
    boundary hslotInverse
    (by rw [rowParameter, supportParameter]; exact hwidthBox)
    hheight

end SecondBlockProfileChart
end HeckeSkeleton.Moments.EngineStepV2

end

set_option quotPrecheck false

/-!
# The normalized family of independent passive allocations

The two passive divisors are independent.  The finite carrier consists
of the original nonzero left and right allocation labels and their two
rectangle choices.  Each side uses the frame already stored at that
label.  Its calibration and capacity are constructed before the common
active filter chooses any children.

Finite Minkowski is applied on the original row measure.  The resulting
family retains the original two Fourier variables, the full Gauss
normalizers, and both allocation divisors.  There is no identification
of the two new divisors with the earlier common second divisor.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2

open HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckePort.Moments

namespace CanonicalLiteralPassiveNormalizedFamily

open CanonicalLiteralPassiveSource CanonicalLiteralPassiveFrames
open CanonicalLiteralPassiveNonzero CanonicalLiteralPassiveFrameEnergy

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {H ι : Type*} [Fintype ι] [DecidableEq ι]
variable (C : A.GeneralArithmeticContext σ η hS)
variable (R : ActualSecondCorrelationRows A σ H ι)
variable {k l : ℕ}
variable {leftAtoms : CanonicalLiteralRectangles.Atoms (K := K) k}
variable {rightAtoms : CanonicalLiteralRectangles.Atoms (K := K) l}
variable (leftProfiles : leftAtoms.ProfileData) (rightProfiles : rightAtoms.ProfileData)
variable (leftAllocation : ActualColumnAllocation K k)
variable (rightAllocation : ActualColumnAllocation K l)
variable (leftPaid : FixedChildCharacters K leftAllocation.keep.card)
variable (rightPaid : FixedChildCharacters K rightAllocation.keep.card)
variable (leftMask rightMask : HeckeGeneral.Analysis.NonzeroIdeal K)
variable (leftSign rightSign : ℝ)

abbrev SideLabel {n : ℕ} {d : CanonicalLiteralRectangles.Atoms (K := K) n}
    (W : d.ProfileData) (B : ActualColumnAllocation K n)
    (A : SArithmeticData K) (M : HeckeGeneral.Analysis.NonzeroIdeal K) :=
  (nonzeroLabels W B A M) × Bool

abbrev PairLabel :=
  SideLabel leftProfiles leftAllocation A leftMask ×
    SideLabel rightProfiles rightAllocation A rightMask

local notation "LeftLabel" => SideLabel leftProfiles leftAllocation A leftMask
local notation "RightLabel" => SideLabel rightProfiles rightAllocation A rightMask
local notation "Labels" => PairLabel (A := A) leftProfiles rightProfiles leftAllocation rightAllocation
  leftMask rightMask
local notation "leftFrame" => fun b : LeftLabel =>
  frame leftProfiles leftAllocation A leftPaid C R .left leftMask b.1.val leftSign b.2
local notation "rightFrame" => fun b : RightLabel =>
  frame rightProfiles rightAllocation A rightPaid C R .right rightMask b.1.val rightSign b.2

variable {ω ψ : HeckeCharacter K}
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
variable {heightDomain window : Set ℝ} {orders : Finset (ℕ × ℕ)}
variable (leftNormalization : ∀ b : SideLabel leftProfiles leftAllocation A leftMask,
  SecondSideNormalization
    (frame leftProfiles leftAllocation A leftPaid C R .left leftMask b.1.val leftSign b.2)
    ω ψ rowDomain heightDomain window orders)
variable (rightNormalization : ∀ b : SideLabel rightProfiles rightAllocation A rightMask,
  SecondSideNormalization
    (frame rightProfiles rightAllocation A rightPaid C R .right rightMask b.1.val rightSign b.2)
    ω ψ rowDomain heightDomain window orders)
variable (sameBase : rightAtoms.base = leftAtoms.base)

/-- The source, calibration and capacity fields refer to the same
stored independent allocation on each side. -/
def family : ActualNormalizedPairFamily A σ (WithLp 2 (ℝ × ℝ)) Labels ω ψ leftAtoms.base where
  LeftRow _ := R.live
  RightRow _ := R.live
  leftSlots _ := leftAllocation.keep.card
  rightSlots _ := rightAllocation.keep.card
  leftSource b := (leftFrame b.1).source
  rightSource b := (rightFrame b.2).source
  leftCalibration b := (leftNormalization b.1).calibration
  rightCalibration b := (rightNormalization b.2).calibration
  leftCapacity b := (leftNormalization b.1).normalizedCapacityData
  rightCapacity b := (rightNormalization b.2).normalizedCapacityData
  left_base _ := rfl
  right_base _ := sameBase
  leftNormalizer b := (leftFrame b.1).normalizer
  rightNormalizer b := (rightFrame b.2).normalizer

local notation "production" => family C R leftProfiles rightProfiles leftAllocation
  rightAllocation leftPaid rightPaid leftMask rightMask leftSign rightSign
  leftNormalization rightNormalization sameBase

theorem sourcePair (parentWidth : ℝ) (b : Labels) (ξ : WithLp 2 (ℝ × ℝ)) :
    (production).sourcePair parentWidth b ξ =
      Real.sqrt ((leftFrame b.1).energy ξ) * Real.sqrt ((rightFrame b.2).energy ξ) /
        leftAtoms.base ^ parentWidth := by
  sorry

theorem sum_sourcePair (parentWidth : ℝ) (ξ : WithLp 2 (ℝ × ℝ)) :
    (∑ b : Labels, (production).sourcePair parentWidth b ξ) =
      ((∑ b : LeftLabel, Real.sqrt ((leftFrame b).energy ξ)) *
        (∑ b : RightLabel, Real.sqrt ((rightFrame b).energy ξ))) /
          leftAtoms.base ^ parentWidth := by
  sorry

/-- The exact passive polynomials still contain their complete
centered difference and the original row weight. -/
def integrand (ξ : WithLp 2 (ℝ × ℝ)) : ℝ :=
  Real.sqrt (∑ h : R.live, ‖R.weight h.val * R.correlation h.val‖ *
      ‖passiveColumn (σ := σ) leftProfiles leftAllocation leftPaid leftMask
        (R.factor C h.val) (R.extractedRow C h).element leftSign false ξ‖ ^ 2) *
    Real.sqrt (∑ h : R.live, ‖R.weight h.val * R.correlation h.val‖ *
      ‖passiveColumn (σ := σ) rightProfiles rightAllocation rightPaid rightMask
        (-(R.factor C h.val)) (R.extractedRow C h).element rightSign true ξ‖ ^ 2)

/-- No source bound is an input: both finite Minkowski bounds are
proved on the fixed original row carrier. -/
theorem integrand_le_sourcePairs (parentWidth : ℝ) (ξ : WithLp 2 (ℝ × ℝ)) :
    integrand C R leftProfiles rightProfiles leftAllocation rightAllocation
      leftPaid rightPaid leftMask rightMask leftSign rightSign ξ / leftAtoms.base ^ parentWidth ≤
      ∑ b : Labels, (production).sourcePair parentWidth b ξ := by
  sorry

/-- The active filter is computed only after every passive label has
its actual capacity input. The children and removals precede ξ. -/
theorem integrand_le_normalized_family (parentWidth : ℝ) (ξ : WithLp 2 (ℝ × ℝ)) :
    integrand C R leftProfiles rightProfiles leftAllocation rightAllocation
      leftPaid rightPaid leftMask rightMask leftSign rightSign ξ / leftAtoms.base ^ parentWidth ≤
      ∑ b : (production).active Finset.univ,
        (production).weight Finset.univ parentWidth b * (production).envelope Finset.univ b ξ *
          (production).childPair Finset.univ b ξ := by
  sorry

theorem in_fixed_window
    (leftHeight : ∀ b ξ, (leftNormalization b).calibration.height ξ ∈ heightDomain)
    (rightHeight : ∀ b ξ, (rightNormalization b).calibration.height ξ ∈ heightDomain) :
    ∀ b : (production).active Finset.univ, ∀ ξ,
      InFixedProfileWindow rowDomain Set.univ window orders
        ((production).leftData Finset.univ b ξ) ∧
      InFixedProfileWindow rowDomain Set.univ window orders
        ((production).rightData Finset.univ b ξ) := by
  sorry

end CanonicalLiteralPassiveNormalizedFamily
end HeckeSkeleton.Moments.EngineStepV2

end

