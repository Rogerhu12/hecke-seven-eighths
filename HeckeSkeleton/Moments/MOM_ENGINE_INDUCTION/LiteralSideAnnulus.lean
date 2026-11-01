import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.SideAnnulusSupport
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralSideProductionAll

/-!
# Support of the exact literal side constructor

The canonical side constructor retains its literal calibration. Its
original positive profile windows and strict prime support are proved
from the same original representatives, before its active child is
selected. These proofs do not modify the normalization radius.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineInduction

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

namespace LiteralSideSupport

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

local notation "allSide" =>
  d.produceLiteralSideAll W rows side χ ideal hideal firstSign rectangle L selection hne D
    P Rchar F parent oldMoving correction hcorr remaining extra a step G pattern sector
    slots cutoff reference time hdata hparameters domain direct hcutoff hsmall error herr
    hm hn hsecond hopposite hunit hstep mesh hmesh hfit lo hi hlo hhi orders original
    hreference htime horders computed hprimeOrders δ analyticHeight hδ hδhi analytic hanalytic

/-- The same canonical normalization has its original positive raw
annulus and strict original prime support. -/
theorem annulusSupport : SideAnnulusSupport allSide lo hi := by
  obtain ⟨budget, raw, prime⟩ := literalCalibration_original_profiles
    P Rchar W (f).allocation F parent oldMoving correction hcorr C rows.primes
    rows.leftMultiplicity rows.rightMultiplicity pattern sector remaining extra m q
    slots.index rectangle firstSign side.literalNegative reference time lo hi hlo orders
    original hreference htime horders computed D hdata
  constructor
  · simpa only [CanonicalLiteralRectangles.Atoms.produceLiteralSideAll_calibration]
      using (show ∃ budget : WithLp 2 (ℝ × ℝ) → ℝ,
        Nonempty (∀ ξ, RawProfileWindow Set.univ Set.univ (Set.Icc lo hi) orders
          (D.data ξ) (budget ξ)) from ⟨budget, raw⟩)
  · simpa only [CanonicalLiteralRectangles.Atoms.produceLiteralSideAll_calibration]
      using prime

end LiteralSideSupport
end HeckeSkeleton.Moments.EngineInduction

#print axioms HeckeSkeleton.Moments.EngineInduction.LiteralSideSupport.annulusSupport
