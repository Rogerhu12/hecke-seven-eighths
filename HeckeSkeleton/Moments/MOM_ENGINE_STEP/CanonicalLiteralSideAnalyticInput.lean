import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralSideProductionAll
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalOriginalPrimeAnalyticProvider

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
      ∀ u, u ∈ pairedRows (D.data ξ) D.parameters f.source.base →
      ∀ i : Fin f.source.allocation.keep.card,
        ZeroFreeData (heckeContinuation K ((D.data ξ).rowCharacter u *
          (D.data ξ).slotCoefficient
            (lengthSlot (D.data ξ) f.source.allocation.keep.card (D.count ξ) i)))
          ((D.parameters.κ + 1) / 2) //
      ∀ hκ : D.parameters.κ < 1, ∀ ξ,
        ∀ u, ∀ hu : u ∈ pairedRows (D.data ξ) D.parameters f.source.base,
        ∀ i : Fin f.source.allocation.keep.card,
          heightConstant (analytic hκ ξ u hu i) +
            3 * ((analytic hκ ξ u hu i).k : ℝ) ≤ analyticHeight} := by
  let recipe := d.productionRecipe W rows side χ ideal hideal firstSign rectangle L selection hne
    D P Rchar F parent oldMoving correction hcorr remaining extra a step G pattern sector
    slots cutoff reference time hdata
  have hfull : recipe.FullJointBudget f.source.base (m + q) :=
    d.productionRecipe_fullJointBudget W rows side χ ideal hideal firstSign rectangle L selection hne
      D P Rchar F parent oldMoving correction hcorr remaining extra a step G pattern sector
      slots cutoff reference time hdata
  have hjoint : recipe.FullJointBudget f.source.base normBox := by
    intro ξ u hu
    exact (hfull ξ u hu).trans
      (Real.rpow_le_rpow_of_exponent_le f.source.base_gt_one.le hwidth)
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
    exact hslotInverse (slots.index (SlotRestriction.index f.allocation.keep i))
  have hz : ∀ ξ, D.parameters.z = (D.data ξ).geometry.totalLength := by
    intro ξ
    rw [hparameters, hdata ξ]
    change (CanonicalLiteralAllocatedData.parameters d f.allocation rectangle m q a.κ).z =
      (CanonicalLiteralAllocatedData.geometry W f.allocation firstSign side.literalNegative ξ).totalLength
    exact CanonicalLiteralAllocatedData.geometry_slot_sum W f.allocation firstSign
      side.literalNegative rectangle m q a.κ ξ
  let single := fun (hκ : D.parameters.κ < 1) ξ u
      (hu : u ∈ pairedRows (D.data ξ) D.parameters f.source.base)
      (i : Fin f.source.allocation.keep.card) =>
    analyticWindow.certificate recipe D.parameters f.source.base
      (by simpa only [hkappa] using hκlo) hκ f.source.base_gt_one
      (by simpa only [hkappa] using boundary (by simpa only [hkappa] using hκ))
      htheta hslot hinverse hz hjoint ξ u hu
      (lengthSlot (D.data ξ) f.source.allocation.keep.card (D.count ξ) i)
  refine ⟨fun hκ ξ u hu i => (single hκ ξ u hu i).val, ?_⟩
  intro hκ ξ u hu i
  exact (single hκ ξ u hu i).property.trans hheight

end CanonicalLiteralRectangles.Atoms
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.literalSideAnalyticInput
