import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralCapacityMass
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualSecondRowMassSwap

/-!
# The existing literal capacity is the actual row-mass capacity

The original row pattern already determines the unit ideal of the
actual row mass.  Its active-row witness changes only proof fields in
the capacity input.  These two identities therefore identify the
capacity selected by the literal left and right producers with the
actual original-row capacity, before any normalized child is changed.

The right identity uses the original column swap and its original
anchor.  Both multiplicities are exchanged exactly once.  The same
pattern ideal is symmetric, so the common classification is not chosen
again.  No numerical mass estimate is an input to either identity.
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

namespace CanonicalLiteralRectangles.Atoms

section Left

variable [IsPrincipalIdealRing A.R]
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {ω ψ : HeckeCharacter K} {k : ℕ}
variable (d : CanonicalLiteralRectangles.Atoms (K := K) k) (W : d.ProfileData)
variable (rows : ActualSecondCorrelationRows A σ H ι)
variable (χ : (PUnit.{1} × PUnit.{1}) →* Circle)
variable (ideal : AllocationColumn K k → A.Exterior)
variable (hideal : ∀ i ∈ childCartesianColumns d.plain₁ d.plain₂ d.slots,
  (ideal i).val = allocationColumnIdeal i)
variable (firstSign : ℝ) (rectangle : Bool) (L : Ideal (𝓞 K))
variable (selection : primeSupport L → Finset (Fin (k + 2)))
variable (hne : (pairedAllocatedColumns L selection d.plain₁ d.plain₂ d.slots
  id id HeightOneSpectrum.asIdeal).Nonempty)

local notation "f" =>
  (d.factors rows (SecondColumnSide.left) χ ideal hideal firstSign rectangle).frame C L selection hne

variable (D : ((d.factors rows (SecondColumnSide.left) χ ideal hideal firstSign rectangle).frame C L selection hne).source.Calibration
  (σ := σ) ω ψ)
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (Rchar : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable (F : CanonicalLiteralPhaseCalibration.FixedPhases A)
variable (parent : MomentData K ω ψ) (oldMoving : OriginalMovingFactors A P Rchar)
variable (correction : HeckeCharacter K) (hcorr : correction ∈ parent.theta)
variable (remaining extra : HeckeGeneral.Analysis.NonzeroIdeal K)
variable (a : RealParameters) (step : ℝ)
variable (G : OriginalNominalGeometry (K := K) a
  ((d.factors rows (SecondColumnSide.left) χ ideal hideal firstSign rectangle).frame C L selection hne).source.base step)
variable (pattern : ι → Bool)
variable (sector : SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (slots : OriginalSlotDictionary parent d.length)
variable (cutoff : ℝ)

local notation "rootLength" =>
  idealLogLength f.source.base
    (secondSixthRootIdeal rows.primes ((SecondColumnSide.left).literalMultiplicity rows)
      ((SecondColumnSide.left).literalOppositeMultiplicity rows)).val
local notation "m" => G.literalRowParameter cutoff
local notation "q" => G.literalSupportParameter rootLength

variable (reference : HeckeGeneral.Analysis.NonzeroIdeal K) (time : ℝ)
variable (hdata : ∀ ξ, D.data ξ = CanonicalLiteralAllocatedData.data
  P Rchar W ((d.factors rows (SecondColumnSide.left) χ ideal hideal firstSign rectangle).frame C L selection hne).allocation
  F parent oldMoving correction hcorr C rows.primes rows.leftMultiplicity rows.rightMultiplicity
  pattern sector remaining extra (G.literalRowParameter cutoff)
  (G.literalSupportParameter (idealLogLength
    ((d.factors rows (SecondColumnSide.left) χ ideal hideal firstSign rectangle).frame C L selection hne).source.base
    (secondSixthRootIdeal rows.primes ((SecondColumnSide.left).literalMultiplicity rows)
      ((SecondColumnSide.left).literalOppositeMultiplicity rows)).val))
  (CanonicalLiteralProfileData.frozenNormTest parent.inverseTest reference time)
  slots.index rectangle firstSign (SecondColumnSide.left).literalNegative ξ)
variable (hparameters : D.parameters = CanonicalLiteralAllocatedData.parameters d
  ((d.factors rows (SecondColumnSide.left) χ ideal hideal firstSign rectangle).frame C L selection hne).allocation
  rectangle (G.literalRowParameter cutoff)
  (G.literalSupportParameter (idealLogLength
    ((d.factors rows (SecondColumnSide.left) χ ideal hideal firstSign rectangle).frame C L selection hne).source.base
    (secondSixthRootIdeal rows.primes ((SecondColumnSide.left).literalMultiplicity rows)
      ((SecondColumnSide.left).literalOppositeMultiplicity rows)).val)) a.κ)

variable {centered : Bool} {Y₁ Y₂ floor padding : ℝ}
variable (domain : PairedEngineDomain centered parent a
  ((d.factors rows (SecondColumnSide.left) χ ideal hideal firstSign rectangle).frame C L selection hne).source.base
  Y₁ Y₂ floor padding)
variable (direct : G.tag = .direct → parent.geometry.slotCount = 0)
variable (hcutoff : 0 ≤ cutoff) (hsmall : 2 * cutoff ≤ step)
variable (error : ℝ) (herr : 0 ≤ error)
variable (hm : ∀ i, 0 < rows.leftMultiplicity i) (hn : ∀ i, 0 < rows.rightMultiplicity i)
variable (hsecond : G.ideals.second.val = (primePowerProduct rows.primes
  ((SecondColumnSide.left).literalMultiplicity rows)).val)
variable (hopposite : G.ideals.secondOpposite.val = (primePowerProduct rows.primes
  ((SecondColumnSide.left).literalOppositeMultiplicity rows)).val)
variable (hunit : G.ideals.unitPart.val = (secondPatternUnitIdeal rows.primes
  ((SecondColumnSide.left).literalMultiplicity rows) ((SecondColumnSide.left).literalOppositeMultiplicity rows) pattern).val)
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
    ((d.factors rows (SecondColumnSide.left) χ ideal hideal firstSign rectangle).frame C L selection hne).source.base →
  ∀ i : Fin ((d.factors rows (SecondColumnSide.left) χ ideal hideal firstSign rectangle).frame C L selection hne).source.allocation.keep.card,
    ZeroFreeData (heckeContinuation K ((D.data ξ).rowCharacter u *
      (D.data ξ).slotCoefficient (lengthSlot (D.data ξ)
        ((d.factors rows (SecondColumnSide.left) χ ideal hideal firstSign rectangle).frame C L selection hne).source.allocation.keep.card
        (D.count ξ) i))) ((D.parameters.κ + 1) / 2))
variable (hanalytic : ∀ hκ : D.parameters.κ < 1, ∀ ξ,
  ∀ u, ∀ hu : u ∈ pairedRows (D.data ξ) D.parameters
    ((d.factors rows (SecondColumnSide.left) χ ideal hideal firstSign rectangle).frame C L selection hne).source.base,
  ∀ i : Fin ((d.factors rows (SecondColumnSide.left) χ ideal hideal firstSign rectangle).frame C L selection hne).source.allocation.keep.card,
    heightConstant (analytic hκ ξ u hu i) + 3 * ((analytic hκ ξ u hu i).k : ℝ) ≤ analyticHeight)


local notation "originalAtoms" =>
  d.literalCapacityAtoms W rows (SecondColumnSide.left) χ ideal hideal firstSign rectangle L selection hne D
    P Rchar F parent oldMoving correction hcorr remaining extra a step G pattern sector
    slots cutoff reference time hdata hparameters domain mesh hmesh hfit lo hi hlo hhi orders
    original hreference htime horders computed hprimeOrders δ analyticHeight hδ hδhi
    analytic hanalytic

local notation "originalLengths" =>
  d.literalCapacityBinding rows (SecondColumnSide.left) χ ideal hideal firstSign rectangle L selection hne D
    parent a step G (slots := slots) (cutoff := cutoff) (hparameters := hparameters)
    (domain := domain) (direct := direct) (hcutoff := hcutoff) (hsmall := hsmall)
    (error := error) (herr := herr)


local notation "allSide" =>
  d.produceLiteralSideAll W rows (SecondColumnSide.left) χ ideal hideal firstSign rectangle L selection hne D
    P Rchar F parent oldMoving correction hcorr remaining extra a step G pattern sector
    slots cutoff reference time hdata hparameters domain direct hcutoff hsmall error herr
    hm hn hsecond hopposite hunit hstep mesh hmesh hfit lo hi hlo hhi orders original
    hreference htime horders computed hprimeOrders δ analyticHeight hδ hδhi analytic hanalytic

variable {kLeft kRight : ℕ}
variable (mass : ActualSecondRowMass rows C kLeft kRight)
variable (anchor : rows.rows)
variable (hmassUnit : mass.unitIdeal.val =
  (secondPatternUnitIdeal rows.primes rows.leftMultiplicity rows.rightMultiplicity pattern).val)

local notation "actualUnit" => hunit.trans hmassUnit.symm

/-- The same actual left producer already contains this original
row-mass capacity input.  The anchor supplies only the original
nonempty-row witness needed by the established same-child theorem. -/
theorem produceLiteralLeftSideAll_capacity_actual_heq :
    HEq allSide.capacity
      (originalLengths.capacityInput mass hn anchor hsecond hopposite actualUnit
        hstep mesh hmesh hfit originalAtoms) := by
  have hpattern : HEq allSide.capacity
      (originalLengths.capacityInputOfPattern rows.primes_injective
        mass.left_positive hn pattern hsecond hopposite hunit hstep mesh hmesh hfit originalAtoms) :=
    d.produceLiteralSideAll_capacity_heq W rows (SecondColumnSide.left) χ ideal hideal firstSign rectangle
        L selection hne D P Rchar F parent oldMoving correction hcorr remaining extra a step G
        pattern sector slots cutoff reference time hdata hparameters domain direct hcutoff hsmall
        error herr hm hn hsecond hopposite hunit hstep mesh hmesh hfit lo hi hlo hhi orders
        original hreference htime horders computed hprimeOrders δ analyticHeight hδ hδhi
        analytic hanalytic
  exact hpattern.trans (heq_of_eq
    (originalLengths.capacityInputOfPattern_eq_actual mass hn
      pattern anchor hsecond hopposite hunit actualUnit hstep mesh hmesh hfit originalAtoms))

end Left

section Right

variable [IsPrincipalIdealRing A.R]
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {ω ψ : HeckeCharacter K} {k : ℕ}
variable (d : CanonicalLiteralRectangles.Atoms (K := K) k) (W : d.ProfileData)
variable (rows : ActualSecondCorrelationRows A σ H ι)
variable (χ : (PUnit.{1} × PUnit.{1}) →* Circle)
variable (ideal : AllocationColumn K k → A.Exterior)
variable (hideal : ∀ i ∈ childCartesianColumns d.plain₁ d.plain₂ d.slots,
  (ideal i).val = allocationColumnIdeal i)
variable (firstSign : ℝ) (rectangle : Bool) (L : Ideal (𝓞 K))
variable (selection : primeSupport L → Finset (Fin (k + 2)))
variable (hne : (pairedAllocatedColumns L selection d.plain₁ d.plain₂ d.slots
  id id HeightOneSpectrum.asIdeal).Nonempty)

local notation "f" =>
  (d.factors rows (SecondColumnSide.right) χ ideal hideal firstSign rectangle).frame C L selection hne

variable (D : ((d.factors rows (SecondColumnSide.right) χ ideal hideal firstSign rectangle).frame C L selection hne).source.Calibration
  (σ := σ) ω ψ)
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (Rchar : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable (F : CanonicalLiteralPhaseCalibration.FixedPhases A)
variable (parent : MomentData K ω ψ) (oldMoving : OriginalMovingFactors A P Rchar)
variable (correction : HeckeCharacter K) (hcorr : correction ∈ parent.theta)
variable (remaining extra : HeckeGeneral.Analysis.NonzeroIdeal K)
variable (a : RealParameters) (step : ℝ)
variable (G : OriginalNominalGeometry (K := K) a
  ((d.factors rows (SecondColumnSide.right) χ ideal hideal firstSign rectangle).frame C L selection hne).source.base step)
variable (pattern : ι → Bool)
variable (sector : SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (slots : OriginalSlotDictionary parent d.length)
variable (cutoff : ℝ)

local notation "rootLength" =>
  idealLogLength f.source.base
    (secondSixthRootIdeal rows.primes ((SecondColumnSide.right).literalMultiplicity rows)
      ((SecondColumnSide.right).literalOppositeMultiplicity rows)).val
local notation "m" => G.literalRowParameter cutoff
local notation "q" => G.literalSupportParameter rootLength

variable (reference : HeckeGeneral.Analysis.NonzeroIdeal K) (time : ℝ)
variable (hdata : ∀ ξ, D.data ξ = CanonicalLiteralAllocatedData.data
  P Rchar W ((d.factors rows (SecondColumnSide.right) χ ideal hideal firstSign rectangle).frame C L selection hne).allocation
  F parent oldMoving correction hcorr C rows.primes rows.leftMultiplicity rows.rightMultiplicity
  pattern sector remaining extra (G.literalRowParameter cutoff)
  (G.literalSupportParameter (idealLogLength
    ((d.factors rows (SecondColumnSide.right) χ ideal hideal firstSign rectangle).frame C L selection hne).source.base
    (secondSixthRootIdeal rows.primes ((SecondColumnSide.right).literalMultiplicity rows)
      ((SecondColumnSide.right).literalOppositeMultiplicity rows)).val))
  (CanonicalLiteralProfileData.frozenNormTest parent.inverseTest reference time)
  slots.index rectangle firstSign (SecondColumnSide.right).literalNegative ξ)
variable (hparameters : D.parameters = CanonicalLiteralAllocatedData.parameters d
  ((d.factors rows (SecondColumnSide.right) χ ideal hideal firstSign rectangle).frame C L selection hne).allocation
  rectangle (G.literalRowParameter cutoff)
  (G.literalSupportParameter (idealLogLength
    ((d.factors rows (SecondColumnSide.right) χ ideal hideal firstSign rectangle).frame C L selection hne).source.base
    (secondSixthRootIdeal rows.primes ((SecondColumnSide.right).literalMultiplicity rows)
      ((SecondColumnSide.right).literalOppositeMultiplicity rows)).val)) a.κ)

variable {centered : Bool} {Y₁ Y₂ floor padding : ℝ}
variable (domain : PairedEngineDomain centered parent a
  ((d.factors rows (SecondColumnSide.right) χ ideal hideal firstSign rectangle).frame C L selection hne).source.base
  Y₁ Y₂ floor padding)
variable (direct : G.tag = .direct → parent.geometry.slotCount = 0)
variable (hcutoff : 0 ≤ cutoff) (hsmall : 2 * cutoff ≤ step)
variable (error : ℝ) (herr : 0 ≤ error)
variable (hm : ∀ i, 0 < rows.leftMultiplicity i) (hn : ∀ i, 0 < rows.rightMultiplicity i)
variable (hsecond : G.ideals.second.val = (primePowerProduct rows.primes
  ((SecondColumnSide.right).literalMultiplicity rows)).val)
variable (hopposite : G.ideals.secondOpposite.val = (primePowerProduct rows.primes
  ((SecondColumnSide.right).literalOppositeMultiplicity rows)).val)
variable (hunit : G.ideals.unitPart.val = (secondPatternUnitIdeal rows.primes
  ((SecondColumnSide.right).literalMultiplicity rows) ((SecondColumnSide.right).literalOppositeMultiplicity rows) pattern).val)
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
    ((d.factors rows (SecondColumnSide.right) χ ideal hideal firstSign rectangle).frame C L selection hne).source.base →
  ∀ i : Fin ((d.factors rows (SecondColumnSide.right) χ ideal hideal firstSign rectangle).frame C L selection hne).source.allocation.keep.card,
    ZeroFreeData (heckeContinuation K ((D.data ξ).rowCharacter u *
      (D.data ξ).slotCoefficient (lengthSlot (D.data ξ)
        ((d.factors rows (SecondColumnSide.right) χ ideal hideal firstSign rectangle).frame C L selection hne).source.allocation.keep.card
        (D.count ξ) i))) ((D.parameters.κ + 1) / 2))
variable (hanalytic : ∀ hκ : D.parameters.κ < 1, ∀ ξ,
  ∀ u, ∀ hu : u ∈ pairedRows (D.data ξ) D.parameters
    ((d.factors rows (SecondColumnSide.right) χ ideal hideal firstSign rectangle).frame C L selection hne).source.base,
  ∀ i : Fin ((d.factors rows (SecondColumnSide.right) χ ideal hideal firstSign rectangle).frame C L selection hne).source.allocation.keep.card,
    heightConstant (analytic hκ ξ u hu i) + 3 * ((analytic hκ ξ u hu i).k : ℝ) ≤ analyticHeight)


local notation "originalAtoms" =>
  d.literalCapacityAtoms W rows (SecondColumnSide.right) χ ideal hideal firstSign rectangle L selection hne D
    P Rchar F parent oldMoving correction hcorr remaining extra a step G pattern sector
    slots cutoff reference time hdata hparameters domain mesh hmesh hfit lo hi hlo hhi orders
    original hreference htime horders computed hprimeOrders δ analyticHeight hδ hδhi
    analytic hanalytic

local notation "originalLengths" =>
  d.literalCapacityBinding rows (SecondColumnSide.right) χ ideal hideal firstSign rectangle L selection hne D
    parent a step G (slots := slots) (cutoff := cutoff) (hparameters := hparameters)
    (domain := domain) (direct := direct) (hcutoff := hcutoff) (hsmall := hsmall)
    (error := error) (herr := herr)


local notation "allSide" =>
  d.produceLiteralSideAll W rows (SecondColumnSide.right) χ ideal hideal firstSign rectangle L selection hne D
    P Rchar F parent oldMoving correction hcorr remaining extra a step G pattern sector
    slots cutoff reference time hdata hparameters domain direct hcutoff hsmall error herr
    hm hn hsecond hopposite hunit hstep mesh hmesh hfit lo hi hlo hhi orders original
    hreference htime horders computed hprimeOrders δ analyticHeight hδ hδhi analytic hanalytic

variable {kLeft kRight : ℕ}
variable (mass : ActualSecondRowMass rows C kLeft kRight)
variable (anchor : rows.rows)
variable (hmassUnit : mass.unitIdeal.val =
  (secondPatternUnitIdeal rows.primes rows.leftMultiplicity rows.rightMultiplicity pattern).val)

local notation "actualUnit" => hunit.trans ((congrArg (fun I : A.Exterior => I.val)
    (secondPatternUnitIdeal_swap rows.primes rows.leftMultiplicity
      rows.rightMultiplicity pattern)).trans hmassUnit.symm)

/-- The same actual right producer uses the swapped original row
mass.  Its right common multiplicities become the left multiplicities,
and its unit ideal and row anchor remain the original ones. -/
theorem produceLiteralRightSideAll_capacity_actual_heq :
    HEq allSide.capacity
      (originalLengths.capacityInput (mass.swapColumns hn) mass.left_positive anchor hsecond hopposite actualUnit
        hstep mesh hmesh hfit originalAtoms) := by
  have hpattern : HEq allSide.capacity
      (originalLengths.capacityInputOfPattern rows.primes_injective
        hn mass.left_positive pattern hsecond hopposite hunit hstep mesh hmesh hfit originalAtoms) :=
    d.produceLiteralSideAll_capacity_heq W rows (SecondColumnSide.right) χ ideal hideal firstSign rectangle
        L selection hne D P Rchar F parent oldMoving correction hcorr remaining extra a step G
        pattern sector slots cutoff reference time hdata hparameters domain direct hcutoff hsmall
        error herr hm hn hsecond hopposite hunit hstep mesh hmesh hfit lo hi hlo hhi orders
        original hreference htime horders computed hprimeOrders δ analyticHeight hδ hδhi
        analytic hanalytic
  exact hpattern.trans (heq_of_eq
    (originalLengths.capacityInputOfPattern_eq_actual (mass.swapColumns hn) mass.left_positive
      pattern anchor hsecond hopposite hunit actualUnit hstep mesh hmesh hfit originalAtoms))

end Right

end CanonicalLiteralRectangles.Atoms
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.produceLiteralLeftSideAll_capacity_actual_heq
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.produceLiteralRightSideAll_capacity_actual_heq
