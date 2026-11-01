import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.ActiveFamilyAnnulus
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralFullKappaInput

/-!
# Original support of the actual literal Fourier calibration

The raw calibration used by the canonical full-kappa constructor has
the original positive annulus before clipping. Its inverse profile is
the original test at the same reference row and time. Its other profiles
are the literal computed Fourier representatives, whose support is
inherited from the original profiles.

This theorem exposes those already constructed raw windows and the
strict original prime support on the same calibration. It does not
replace the calibration, normalization radius, active carrier or chosen
capacity child. The subsequent active-family lemmas can therefore
strengthen support on the actual numerical engine output.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField IsDedekindDomain
open DedekindZetaZeroFree (SArithmeticData RayClassCharacter)
open DedekindZetaZeroFree.LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments HeckePort.Moments.Support
open HeckeSkeleton.Moments.EngineStep
open CanonicalLiteralFullKappaInput

variable {K : Type} [Field K] [NumberField K] {k : ℕ}
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable {ω ψ : HeckeCharacter K}
variable {d : CanonicalLiteralRectangles.Atoms (K := K) k}
variable (W : d.ProfileData) (allocation : ActualColumnAllocation K k)
variable (F : CanonicalLiteralPhaseCalibration.FixedPhases A)
variable (parent : MomentData K ω ψ) (oldMoving : OriginalMovingFactors A P R)
variable (correction : HeckeCharacter K) (hcorr : correction ∈ parent.theta)
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (C : A.GeneralArithmeticContext σ η hS) (p : ι → ExteriorPrime A)
variable (leftMultiplicity rightMultiplicity : ι → ℕ) (pattern : ι → Bool)
variable (sector : SixthUnitClasses K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (remaining extra : NonzeroIdeal K) (m q : ℝ)
variable (index : Fin k → Fin parent.geometry.slotCount)
variable (rectangle : Bool) (firstSign : ℝ) (negative : Bool)
variable (reference : NonzeroIdeal K) (time : ℝ)
variable {originalRows : Set (NonzeroIdeal K)} {originalHeights : Set ℝ}
variable {originalOrders : Finset (ℕ × ℕ)}
variable (lo hi : ℝ) (hlo : 0 < lo) (orders : Finset (ℕ × ℕ))
variable {B : ℝ}
variable (original : RawProfileWindow originalRows originalHeights (Set.Icc lo hi)
  originalOrders parent B)
variable (hreference : reference ∈ originalRows) (htime : time ∈ originalHeights)
variable (horders : orders ⊆ originalOrders)
variable (computed : ComputedProfiles W (Set.Icc lo hi) orders B)
variable {H : Type*} {sourceSlots : ℕ}
variable {source : ActualAllocatedSource A (WithLp 2 (ℝ × ℝ)) H sourceSlots}
variable (cal : source.Calibration (σ := σ) ω ψ)

/-- Every literal calibration receives the original positive raw
windows and original strict prime support. The same data equality is
definitionally true at the canonical frame constructors. -/
theorem literalCalibration_original_profiles
    (hdata : ∀ ξ, cal.data ξ = CanonicalLiteralAllocatedData.data P R W allocation F
      parent oldMoving correction hcorr C p leftMultiplicity rightMultiplicity pattern sector
      remaining extra m q
      (CanonicalLiteralProfileData.frozenNormTest parent.inverseTest reference time)
      index rectangle firstSign negative ξ) :
    ∃ budget : WithLp 2 (ℝ × ℝ) → ℝ,
      Nonempty (∀ ξ, RawProfileWindow Set.univ Set.univ (Set.Icc lo hi) orders
        (cal.data ξ) (budget ξ)) ∧
      ∀ ξ i t, Function.support (((cal.data ξ).geometry.slots i).profile t) ⊆
        Set.Ioo (1 : ℝ) 2 := by
  let hpositive := CanonicalLogProfiles.positiveAnnulus lo hi hlo
  let Braw := computed.rawCoefficient isCompact_Icc hpositive firstSign rectangle
  let rawLiteral (ξ : WithLp 2 (ℝ × ℝ)) :=
    CanonicalLiteralAllocatedData.frozenInverseRawWindow P R W allocation F parent
      oldMoving correction hcorr C p leftMultiplicity rightMultiplicity pattern sector
      remaining extra m q index rectangle firstSign negative reference time original
      hreference htime computed.model isCompact_Icc hpositive orders horders
      (computed.bound_nonneg rectangle) (computed.original_bound rectangle)
      (computed.left_bound rectangle) (computed.right_bound rectangle)
      (computed.slot_bound rectangle) ξ
  let raw (ξ : WithLp 2 (ℝ × ℝ)) :
      RawProfileWindow Set.univ Set.univ (Set.Icc lo hi) orders (cal.data ξ)
        (polynomialProfileRadius Braw (orders.sup Prod.snd) (orders.sup Prod.snd)
          (WithLp.ofLp ξ)) :=
    transportWindow (hdata ξ).symm (rawLiteral ξ)
  have hprime (ξ : WithLp 2 (ℝ × ℝ)) :
      ∀ i t, Function.support ((raw ξ).primeRep i t) ⊆ Set.Ioo (1 : ℝ) 2 := by
    apply transportWindow_prime_support (hdata ξ).symm (rawLiteral ξ)
    intro i t
    exact (computed.model.slotFourierRep_support_subset isCompact_Icc hpositive
      firstSign negative (SlotRestriction.index allocation.keep i) ξ).trans
      (computed.prime_window (SlotRestriction.index allocation.keep i))
  refine ⟨fun ξ => polynomialProfileRadius Braw (orders.sup Prod.snd)
    (orders.sup Prod.snd) (WithLp.ofLp ξ), ⟨raw⟩, ?_⟩
  intro ξ i t y hy
  rw [(raw ξ).prime_eq] at hy
  exact hprime ξ i t hy

/-- The canonical full-kappa input already proves prime support at
the actual calibration height. Freeze and normalization preserve that
support for any of its same-calibration capacity children. -/
theorem fullKappa_frozen_child_prime_support
    {recipe : CompleteMovingRowRecipe A P R cal.data}
    {rowDomain : Set (NonzeroIdeal K)} {heightDomain window : Set ℝ}
    {seminorms : Finset (ℕ × ℕ)}
    {profileBound delta lengthBound analyticHeight width : ℝ} {J₁ J₂ : ℕ}
    (input : cal.FullKappaProfileInput recipe rowDomain heightDomain window seminorms
      profileBound J₁ J₂ delta lengthBound analyticHeight width)
    {capacity : cal.NormalizedCapacityData} (out : capacity.Child) :
    ∀ ξ i t, Function.support (((out.frozenData ξ).geometry.slots i).profile t) ⊆
      Set.Ioo (1 : ℝ) 2 := by
  apply ActiveChildAnnulus.frozen_child_prime_support_at out
  intro ξ i y hy
  rw [(input.raw ξ).prime_eq] at hy
  exact input.prime_support ξ i hy

end HeckeSkeleton.Moments.EngineInduction

#print axioms HeckeSkeleton.Moments.EngineInduction.literalCalibration_original_profiles
#print axioms HeckeSkeleton.Moments.EngineInduction.fullKappa_frozen_child_prime_support
