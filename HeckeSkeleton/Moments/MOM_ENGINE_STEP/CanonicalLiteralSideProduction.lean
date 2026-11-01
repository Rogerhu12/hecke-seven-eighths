import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralFrameLengths
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralFullKappaInput
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralAllocatedRecipe
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralFrameCalibration
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalFullKappaRightNormalization

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

namespace HeckeSkeleton.Moments.EngineStep

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
  cases side
  · rfl
  · unfold literalMultiplicity literalOppositeMultiplicity secondSixthRootIdeal
    apply congrArg (primePowerProduct R.primes)
    funext i
    rw [min_comm]

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
  idealLogLength f.source.base
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
  CanonicalLiteralAllocatedData.recipe P Rchar W f.allocation F parent oldMoving correction
    hcorr C rows.primes rows.leftMultiplicity rows.rightMultiplicity pattern sector
    remaining extra m q (CanonicalLiteralProfileData.frozenNormTest parent.inverseTest reference time)
    slots.index rectangle firstSign side.literalNegative

/-- The complete original mask, remaining deletion and all appended
moving factors are transported by the actual data identity alone. -/
def productionRecipe : CompleteMovingRowRecipe A P Rchar D.data :=
  literalRecipe.ofAllowedSubset
    (fun ξ u hu => by simpa only [hdata ξ] using hu)
    (fun ξ => congrArg (fun e : MomentData K ω ψ => e.rowCharacter) (hdata ξ))
    (fun ξ => congrArg (fun e : MomentData K ω ψ => e.commonMask) (hdata ξ))
    (fun ξ => congrArg (fun e : MomentData K ω ψ => e.theta) (hdata ξ))

theorem productionRecipe_fullJointBudget :
    (d.productionRecipe W rows side χ ideal hideal firstSign rectangle L selection hne D
      P Rchar F parent oldMoving correction hcorr remaining extra a step G pattern sector
      slots cutoff reference time hdata).FullJointBudget f.source.base (m + q) := by
  intro ξ u hu
  have hliteral : (CanonicalLiteralAllocatedData.data P Rchar W f.allocation F parent
      oldMoving correction hcorr C rows.primes rows.leftMultiplicity rows.rightMultiplicity
      pattern sector remaining extra m q
      (CanonicalLiteralProfileData.frozenNormTest parent.inverseTest reference time)
      slots.index rectangle firstSign side.literalNegative ξ).allowedRow u := by
    simpa only [hdata ξ] using hu
  have he := CanonicalLiteralAllocatedData.recipe_fullJointBudget P Rchar W f.allocation F parent
    oldMoving correction hcorr C rows.primes rows.leftMultiplicity rows.rightMultiplicity
    pattern sector remaining extra m q
    (CanonicalLiteralProfileData.frozenNormTest parent.inverseTest reference time)
    slots.index rectangle firstSign side.literalNegative ξ u hliteral
  have hbase : f.source.base = d.base := by cases side <;> rfl
  simpa only [productionRecipe, CompleteMovingRowRecipe.FullJointBudget,
    CompleteMovingRowRecipe.ofAllowedSubset, hbase] using he

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
  have hfull : recipe.FullJointBudget f.source.base (m + q) :=
    d.productionRecipe_fullJointBudget W rows side χ ideal hideal firstSign rectangle L selection hne
      D P Rchar F parent oldMoving correction hcorr remaining extra a step G pattern sector
      slots cutoff reference time hdata
  have hkappa : D.parameters.κ = a.κ := by rw [hparameters]; rfl
  let profiles := CanonicalLiteralFullKappaInput.ofLiteral P Rchar W f.allocation F parent
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
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.SecondColumnSide.literal_root
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.productionRecipe_fullJointBudget
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.produceLiteralSide
