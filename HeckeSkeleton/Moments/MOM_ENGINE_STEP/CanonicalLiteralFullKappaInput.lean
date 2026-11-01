import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralFrozenInverse
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralActiveProfileBounds
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalFullKappaNormalization

/-!
# Constructing the full-kappa input on actual literal Fourier data

The profile certificates in this file are outputs of the original
profile construction. Its seed uses the original finite seminorms;
the real-power transforms, scalar removal and plain balance compute
the coefficient. Actual extraction, atlas transport and mask deletion
preserve that coefficient and its representatives.

The final constructor builds both raw and clipped windows itself,
including the original frozen inverse test and the open prime window.
The remaining inputs concern only the original support budget, slot
lengths, kappa range and single-prime zero-free data. No normalized
profile window, child estimate or kernel-mass bound is an input.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments HeckePort.Moments.Support
open PrimeCancellation.Analytic

namespace CanonicalLiteralFullKappaInput

variable {K : Type} [Field K] [NumberField K] {k : ℕ}

/-- A returned intermediate for the actual individual tests. The
constructors below derive its bounds from the original representatives
and preserve the chosen coefficient through each literal operation. -/
structure ComputedProfiles {d : CanonicalLiteralRectangles.Atoms (K := K) k}
    (W : d.ProfileData) (window : Set ℝ) (s : Finset (ℕ × ℕ)) (originalBound : ℝ) where
  model : W.SchwartzModel window
  bound : Bool → ℝ
  bound_nonneg : ∀ r, 0 ≤ bound r
  original_bound : ∀ r, originalBound ≤ bound r
  left_bound : ∀ r, (CanonicalLogProfiles.sourceOrders s).sup
    (schwartzSeminormFamily ℂ ℝ ℂ) (model.left r) ≤ bound r
  right_bound : ∀ r, (CanonicalLogProfiles.sourceOrders s).sup
    (schwartzSeminormFamily ℂ ℝ ℂ) (model.right r) ≤ bound r
  slot_bound : ∀ r j, (CanonicalLogProfiles.sourceOrders s).sup
    (schwartzSeminormFamily ℂ ℝ ℂ) (model.slot j) ≤ bound r
  prime_window : ∀ j, Function.support (model.slot j) ⊆ Set.Ioo (1 : ℝ) 2

namespace ComputedProfiles

variable {d : CanonicalLiteralRectangles.Atoms (K := K) k} {W : d.ProfileData}
variable {window : Set ℝ} {s : Finset (ℕ × ℕ)} {B : ℝ}
variable (T : ComputedProfiles W window s B)

def extract {support : Finset (Ideal (𝓞 K))}
    (b : SupportCartesianBranch d.plain₁ d.plain₂ d.slots support) :
    ComputedProfiles (W.extract b) window s B where
  model := T.model.extract b
  bound := T.bound
  bound_nonneg := T.bound_nonneg
  original_bound := T.original_bound
  left_bound := T.left_bound
  right_bound := T.right_bound
  slot_bound r j := T.slot_bound r (SlotRestriction.index b.keep j)
  prime_window := T.model.extract_prime_support b T.prime_window

def onAtlas {A : SArithmeticData K} {ι : Type*}
    {columns : Finset ι} {ideal : ι → A.Exterior}
    (atlas : SourceCartesianAtlas columns ideal) (count : k = atlas.slotCount) :
    ComputedProfiles (W.onAtlas atlas count) window s B := by
  cases count
  exact
    { model := T.model.onAtlas atlas rfl
      bound := T.bound
      bound_nonneg := T.bound_nonneg
      original_bound := T.original_bound
      left_bound := T.left_bound
      right_bound := T.right_bound
      slot_bound := T.slot_bound
      prime_window := T.prime_window }

def deleteMask (M : HeckeGeneral.Analysis.NonzeroIdeal K) :
    ComputedProfiles (W.deleteMask M) window s B where
  model := T.model.deleteMask M
  bound := T.bound
  bound_nonneg := T.bound_nonneg
  original_bound := T.original_bound
  left_bound := T.left_bound
  right_bound := T.right_bound
  slot_bound := T.slot_bound
  prime_window := T.prime_window

/-- Exact identities of individual tests suffice when the existing
table stores the same operations in a different order. No inequality
or identity of a whole source is requested by this transport. -/
def reprofile {d' : CanonicalLiteralRectangles.Atoms (K := K) k} (W' : d'.ProfileData)
    (hleft : ∀ r u t y, (W'.left r).profile u t y = (W.left r).profile u t y)
    (hright : ∀ r u t y, (W'.right r).profile u t y = (W.right r).profile u t y)
    (hslot : ∀ j t y, (W'.slot j).profile t y = (W.slot j).profile t y) :
    ComputedProfiles W' window s B where
  model :=
    { left := T.model.left
      right := T.model.right
      slot := T.model.slot
      left_eq r u t y := (hleft r u t y).trans (T.model.left_eq r u t y)
      right_eq r u t y := (hright r u t y).trans (T.model.right_eq r u t y)
      slot_eq j t y := (hslot j t y).trans (T.model.slot_eq j t y)
      left_support := T.model.left_support
      right_support := T.model.right_support
      slot_support := T.model.slot_support }
  bound := T.bound
  bound_nonneg := T.bound_nonneg
  original_bound := T.original_bound
  left_bound := T.left_bound
  right_bound := T.right_bound
  slot_bound := T.slot_bound
  prime_window := T.prime_window

/-- The actual table strips and balances after the second extraction.
The same original representatives may be computed before it: the
individual tests agree definitionally, and the balance is unchanged. -/
def extractThenScaleBalance (c : ℂ) (balance : Bool → ℝ)
    (T : ComputedProfiles ((W.scale c).balancePlain balance) window s B)
    {support : Finset (Ideal (𝓞 K))}
    (b : SupportCartesianBranch d.plain₁ d.plain₂ d.slots support) :
    ComputedProfiles (((W.extract b).scale c).balancePlain balance) window s B :=
  (T.extract b).reprofile (((W.extract b).scale c).balancePlain balance)
    (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)

def onAtlasThenScaleBalance (c : ℂ) (balance : Bool → ℝ)
    (T : ComputedProfiles ((W.scale c).balancePlain balance) window s B)
    {A : SArithmeticData K} {ι : Type*} {columns : Finset ι} {ideal : ι → A.Exterior}
    (atlas : SourceCartesianAtlas columns ideal) (count : k = atlas.slotCount) :
    ComputedProfiles (((W.onAtlas atlas count).scale c).balancePlain balance) window s B := by
  cases count
  exact (T.onAtlas atlas rfl).reprofile (((W.onAtlas atlas rfl).scale c).balancePlain balance)
    (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)

def deleteMaskThenScaleBalance (c : ℂ) (balance : Bool → ℝ)
    (T : ComputedProfiles ((W.scale c).balancePlain balance) window s B)
    (M : HeckeGeneral.Analysis.NonzeroIdeal K) :
    ComputedProfiles (((W.deleteMask M).scale c).balancePlain balance) window s B :=
  (T.deleteMask M).reprofile (((W.deleteMask M).scale c).balancePlain balance)
    (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl)

end ComputedProfiles

section OriginalConstruction

variable {d : CanonicalLiteralRectangles.Atoms (K := K) k} {W : d.ProfileData}
variable {window : Set ℝ} (E : W.SchwartzModel window)
variable {support : Finset (Ideal (𝓞 K))}
variable (b : SupportCartesianBranch d.plain₁ d.plain₂ d.slots support)
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable (power firstFixed poolFixed unitFixed : A.Exterior)
variable (firstElement poolElement unitElement : A.R)
variable (hfirst : A.Generates firstFixed firstElement)
variable (hpool : A.Generates poolFixed poolElement)
variable (hunit : A.Generates unitFixed unitElement)
variable (δ₁ δ₂ : ℝ)

local notation "outer" => d.commonScalar b *
  (((A.exteriorNorm power ^ δ₁ : ℝ) : ℂ) *
    actualIdealResidue (A := A) (σ := σ) power.val firstElement)
local notation "actualProfiles" =>
  ((W.secondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
    firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂).scale outer⁻¹)
      .balancePlain (CanonicalLiteralBalancedSchwartz.balance d b δ₁ δ₂)

/-- The only seminorm premises are on the original seed model. Its
actual two-stage scalar removal and balance produce all the estimates
recorded in the returned value, for both rectangles including zero. -/
def scalarFreeBalanced (hcompact : IsCompact window) (hpositive : window ⊆ Set.Ioi 0)
    (s : Finset (ℕ × ℕ)) (B : ℝ) (hB : 0 ≤ B) (hδhi : δ₁ + δ₂ ≤ 1 / 2)
    (hleft : ∀ r, (CanonicalLogProfiles.sourceOrders (CanonicalLogProfiles.sourceOrders s)).sup
      (schwartzSeminormFamily ℂ ℝ ℂ) (E.left r) ≤ B)
    (hright : ∀ r, (CanonicalLogProfiles.sourceOrders (CanonicalLogProfiles.sourceOrders s)).sup
      (schwartzSeminormFamily ℂ ℝ ℂ) (E.right r) ≤ B)
    (hslot : ∀ j, (CanonicalLogProfiles.sourceOrders (CanonicalLogProfiles.sourceOrders s)).sup
      (schwartzSeminormFamily ℂ ℝ ℂ) (E.slot j) ≤ B)
    (hprime : ∀ j, Function.support (E.slot j) ⊆ Set.Ioo (1 : ℝ) 2) :
    ComputedProfiles actualProfiles window s B := by
  let Cshape := CanonicalLogProfiles.shapeCoefficient window hcompact hpositive
    (CanonicalLiteralProfileScalars.exponent δ₁ δ₂) (CanonicalLogProfiles.sourceOrders s)
  have hC : 0 ≤ Cshape := CanonicalLogProfiles.shapeCoefficient_nonneg
    window hcompact hpositive _ _
  have hcomputed (r : Bool) := E.scalarFreeBalanced_computed_bounds (σ := σ) b P R
    power firstFixed poolFixed unitFixed firstElement poolElement unitElement
    hfirst hpool hunit δ₁ δ₂ hcompact hpositive r (CanonicalLogProfiles.sourceOrders s)
    B hB hδhi (hleft r) (hright r) hslot
  refine
    { model := E.scalarFreeBalancedSecondInput (σ := σ) b P R
        power firstFixed poolFixed unitFixed firstElement poolElement unitElement
        hfirst hpool hunit δ₁ δ₂ hcompact hpositive
      bound := fun r => B + B * Cshape *
        (1 + CanonicalLiteralBalancedSchwartz.factor d b δ₁ δ₂ r)
      bound_nonneg := ?_
      original_bound := ?_
      left_bound := fun r => (hcomputed r).1
      right_bound := fun r => (hcomputed r).2.1
      slot_bound := fun r => (hcomputed r).2.2
      prime_window := E.scalarFreeBalancedSecondInput_prime_support (σ := σ) b P R
        power firstFixed poolFixed unitFixed firstElement poolElement unitElement
        hfirst hpool hunit δ₁ δ₂ hcompact hpositive hprime }
  · intro r
    exact add_nonneg hB (mul_nonneg (mul_nonneg hB hC)
      (add_nonneg zero_le_one (Real.sqrt_nonneg _)))
  · intro r
    exact le_add_of_nonneg_right (mul_nonneg (mul_nonneg hB hC)
      (add_nonneg zero_le_one (Real.sqrt_nonneg _)))

end OriginalConstruction

namespace ComputedProfiles

variable {d : CanonicalLiteralRectangles.Atoms (K := K) k} {W : d.ProfileData}
variable {window : Set ℝ} {s : Finset (ℕ × ℕ)} {B : ℝ}
variable (T : ComputedProfiles W window s B)

def rawCoefficient (hcompact : IsCompact window) (hpositive : window ⊆ Set.Ioi 0)
    (firstSign : ℝ) (rectangle : Bool) : ℝ :=
  T.bound rectangle * (1 + CanonicalLiteralFourierWindows.coefficient
    window hcompact hpositive firstSign s)

theorem rawCoefficient_nonneg (hcompact : IsCompact window)
    (hpositive : window ⊆ Set.Ioi 0) (firstSign : ℝ) (rectangle : Bool) :
    0 ≤ T.rawCoefficient hcompact hpositive firstSign rectangle :=
  mul_nonneg (T.bound_nonneg rectangle) (add_nonneg zero_le_one
    (CanonicalLiteralFourierWindows.coefficient_nonneg window hcompact hpositive firstSign s))

def coefficient (Z : ℝ) (parameters : RealParameters)
    (hcompact : IsCompact window) (hpositive : window ⊆ Set.Ioi 0)
    (firstSign : ℝ) (rectangle : Bool) : ℝ :=
  CanonicalLiteralAllSideClipping.cost Z parameters s *
    (1 + T.rawCoefficient hcompact hpositive firstSign rectangle)

theorem coefficient_nonneg (Z : ℝ) (parameters : RealParameters) (hZ : 1 ≤ Z)
    (hcompact : IsCompact window) (hpositive : window ⊆ Set.Ioi 0)
    (firstSign : ℝ) (rectangle : Bool) :
    0 ≤ T.coefficient Z parameters hcompact hpositive firstSign rectangle :=
  mul_nonneg (zero_le_one.trans (CanonicalLiteralAllSideClipping.cost_bounds Z parameters hZ s).1)
    (add_nonneg zero_le_one (T.rawCoefficient_nonneg hcompact hpositive firstSign rectangle))

end ComputedProfiles

section DataTransport

variable {ω ψ : HeckeCharacter K}
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
variable {heightDomain window target : Set ℝ} {s : Finset (ℕ × ℕ)} {B : ℝ}
variable {d e : MomentData K ω ψ}

/-- Only a literal data identity is transported. The profiles and
their computed bounds have already been constructed. -/
def transportWindow (h : d = e)
    (w : RawProfileWindow rowDomain heightDomain window s d B) :
    RawProfileWindow rowDomain heightDomain window s e B := by
  cases h
  exact w

theorem transportWindow_prime_support (h : d = e)
    (w : RawProfileWindow rowDomain heightDomain window s d B)
    (hprime : ∀ j t, Function.support (w.primeRep j t) ⊆ target) :
    ∀ j t, Function.support ((transportWindow h w).primeRep j t) ⊆ target := by
  cases h
  exact hprime

end DataTransport

section ActualCalibration

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
variable (remaining extra : HeckeGeneral.Analysis.NonzeroIdeal K) (m q : ℝ)
variable (index : Fin k → Fin parent.geometry.slotCount)
variable (rectangle : Bool) (firstSign : ℝ) (negative : Bool)
variable (reference : HeckeGeneral.Analysis.NonzeroIdeal K) (time : ℝ)
variable {originalRows : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
variable {originalHeights : Set ℝ} {originalOrders : Finset (ℕ × ℕ)}
variable (lo hi : ℝ) (hlo : 0 < lo) (hhi : 1 ≤ hi) (s : Finset (ℕ × ℕ))
variable {B : ℝ}
variable (original : RawProfileWindow originalRows originalHeights (Set.Icc lo hi)
  originalOrders parent B)
variable (hreference : reference ∈ originalRows) (htime : time ∈ originalHeights)
variable (horders : s ⊆ originalOrders)
variable (T : ComputedProfiles W (Set.Icc lo hi) s B)
variable {H : Type*} {sourceSlots : ℕ}
variable {source : ActualAllocatedSource A (WithLp 2 (ℝ × ℝ)) H sourceSlots}
variable (D : source.Calibration (σ := σ) ω ψ)
variable (Q : CompleteMovingRowRecipe A P R D.data)

/-- The data equality is `rfl` for the literal frame calibration. All
analytic profile fields are constructed below from the original
representatives, before the normalized capacity data is chosen.
Only original single-prime analytic information remains external. -/
def ofLiteral
    (hdata : ∀ ξ, D.data ξ = CanonicalLiteralAllocatedData.data P R W allocation F
      parent oldMoving correction hcorr C p leftMultiplicity rightMultiplicity pattern sector
      remaining extra m q
      (CanonicalLiteralProfileData.frozenNormTest parent.inverseTest reference time)
      index rectangle firstSign negative ξ)
    (hprimeOrders : CanonicalFullKappaPrime.orders ⊆ s)
    (δ lengthBound analyticHeight width : ℝ)
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 4)
    (hlength : 0 ≤ lengthBound) (hlengths : ∀ i, source.childLength i ≤ lengthBound)
    (hκlo : 3 / 4 ≤ D.parameters.κ) (hκhi : D.parameters.κ ≤ 1)
    (hfull : Q.FullJointBudget source.base width)
    (analytic : ∀ _hκ : D.parameters.κ < 1, ∀ ξ,
      ∀ u, u ∈ pairedRows (D.data ξ) D.parameters source.base →
      ∀ i : Fin source.allocation.keep.card,
        ZeroFreeData (heckeContinuation K ((D.data ξ).rowCharacter u *
          (D.data ξ).slotCoefficient
            (lengthSlot (D.data ξ) source.allocation.keep.card (D.count ξ) i)))
          ((D.parameters.κ + 1) / 2))
    (hanalytic : ∀ hκ : D.parameters.κ < 1, ∀ ξ,
      ∀ u, ∀ hu : u ∈ pairedRows (D.data ξ) D.parameters source.base,
      ∀ i : Fin source.allocation.keep.card,
        heightConstant (analytic hκ ξ u hu i) + 3 * ((analytic hκ ξ u hu i).k : ℝ) ≤
          analyticHeight) :
    D.FullKappaProfileInput Q Set.univ Set.univ (Set.Icc 0 hi) s
      (T.coefficient source.base D.parameters isCompact_Icc
        (CanonicalLogProfiles.positiveAnnulus lo hi hlo) firstSign rectangle)
      (s.sup Prod.snd) (s.sup Prod.snd) δ lengthBound analyticHeight width := by
  let hpositive := CanonicalLogProfiles.positiveAnnulus lo hi hlo
  let Braw := T.rawCoefficient isCompact_Icc hpositive firstSign rectangle
  have hBraw : 0 ≤ Braw :=
    T.rawCoefficient_nonneg isCompact_Icc hpositive firstSign rectangle
  let rawLiteral (ξ : WithLp 2 (ℝ × ℝ)) :=
    CanonicalLiteralAllocatedData.frozenInverseRawWindow P R W allocation F parent
      oldMoving correction hcorr C p leftMultiplicity rightMultiplicity pattern sector
      remaining extra m q index rectangle firstSign negative reference time original
      hreference htime T.model isCompact_Icc hpositive s horders (T.bound_nonneg rectangle)
      (T.original_bound rectangle) (T.left_bound rectangle) (T.right_bound rectangle)
      (T.slot_bound rectangle) ξ
  let raw (ξ : WithLp 2 (ℝ × ℝ)) :
      RawProfileWindow Set.univ Set.univ (Set.Icc lo hi) s (D.data ξ)
        (polynomialProfileRadius Braw (s.sup Prod.snd) (s.sup Prod.snd) (WithLp.ofLp ξ)) :=
    transportWindow (hdata ξ).symm (rawLiteral ξ)
  have hrawPrime (ξ : WithLp 2 (ℝ × ℝ)) :
      ∀ j t, Function.support ((raw ξ).primeRep j t) ⊆ Set.Ioo (1 : ℝ) 2 := by
    apply transportWindow_prime_support (hdata ξ).symm (rawLiteral ξ)
    intro j t
    exact (T.model.slotFourierRep_support_subset isCompact_Icc hpositive firstSign negative
      (SlotRestriction.index allocation.keep j) ξ).trans
      (T.prime_window (SlotRestriction.index allocation.keep j))
  let both (ξ : WithLp 2 (ℝ × ℝ)) := CanonicalLiteralAllSideClipping.familyWindows
    D.data D.parameters source.base source.base_gt_one.le lo hi hlo s Braw hBraw
    (s.sup Prod.snd) raw ξ
  refine
    { coefficient_nonneg := T.coefficient_nonneg source.base D.parameters source.base_gt_one.le
        isCompact_Icc hpositive firstSign rectangle
      orders := hprimeOrders
      raw := fun ξ => (both ξ).1
      clipped := fun ξ => (both ξ).2
      annulus := hi
      annulus_one := hhi
      window_upper := fun _ hy => hy.2
      prime_support := ?_
      rows := fun _ _ _ => Set.mem_univ _
      height := fun _ => Set.mem_univ _
      delta_pos := hδ
      delta_le := hδhi
      length_nonneg := hlength
      length_le := hlengths
      kappa_lower := hκlo
      kappa_upper := hκhi
      full_support := hfull
      analytic := analytic
      analytic_height := hanalytic }
  intro ξ i
  exact (CanonicalLiteralAllSideClipping.familyWindows_prime_support
    D.data D.parameters source.base source.base_gt_one.le lo hi hlo s Braw hBraw
    (s.sup Prod.snd) raw hrawPrime ξ i (D.height ξ)).1

end ActualCalibration

end CanonicalLiteralFullKappaInput

namespace CompleteMovingRowRecipe

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {ω ψ : HeckeCharacter K} {X : Type*} {data : X → MomentData K ω ψ}

/-- Direct original-data entrance for the computed profile object.
The original window itself proves every seminorm premise of the
two-stage scalar-free balanced constructor. The extra prime-window
clause is the original single-prime support condition. -/
def literalScalarFreeComputedProfiles
    (Q : CompleteMovingRowRecipe A P R data) (ξ : X)
    (recipe : NormProfileRecipe (fun _ : PUnit => data ξ))
    (a : RealParameters) (Z t Y₁ Y₂ : ℝ) (centered : Bool)
    (hZ : 1 < Z) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)
    (reference : HeckeGeneral.Analysis.NonzeroIdeal K)
    (href : (data ξ).allowedRow reference)
    {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
    {heightDomain window : Set ℝ}
    (s : Finset (ℕ × ℕ)) (B : ℝ) (hB : 0 ≤ B)
    (original : RawProfileWindow rowDomain heightDomain window
      (CanonicalLogProfiles.sourceOrders (CanonicalLogProfiles.sourceOrders s)) (data ξ) B)
    (hreference : reference ∈ rowDomain) (ht : t ∈ heightDomain)
    (hcompact : IsCompact window) (hpositive : window ⊆ Set.Ioi 0)
    (hprime : ∀ j, Function.support (original.primeRep j t) ⊆ Set.Ioo (1 : ℝ) 2)
    {support : Finset (Ideal (𝓞 K))}
    (b : SupportCartesianBranch
      (Q.literalOriginalAtoms ξ recipe a Z t Y₁ Y₂ centered hZ hY₁ hY₂).plain₁
      (Q.literalOriginalAtoms ξ recipe a Z t Y₁ Y₂ centered hZ hY₁ hY₂).plain₂
      (Q.literalOriginalAtoms ξ recipe a Z t Y₁ Y₂ centered hZ hY₁ hY₂).slots support)
    (power firstFixed poolFixed unitFixed : A.Exterior)
    (firstElement poolElement unitElement : A.R)
    (hfirst : A.Generates firstFixed firstElement)
    (hpool : A.Generates poolFixed poolElement)
    (hunit : A.Generates unitFixed unitElement)
    (δ₁ δ₂ : ℝ) (hδhi : δ₁ + δ₂ ≤ 1 / 2) :
    let W := Q.literalOriginalProfileDataOfWindow ξ recipe a Z t Y₁ Y₂ centered
      hZ hY₁ hY₂ reference href original hreference ht hpositive
    let d := Q.literalOriginalAtoms ξ recipe a Z t Y₁ Y₂ centered hZ hY₁ hY₂
    let outer := d.commonScalar b * (((A.exteriorNorm power ^ δ₁ : ℝ) : ℂ) *
      actualIdealResidue (A := A) (σ := σ) power.val firstElement)
    CanonicalLiteralFullKappaInput.ComputedProfiles
      (((W.secondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
        firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂).scale outer⁻¹)
          .balancePlain (CanonicalLiteralBalancedSchwartz.balance d b δ₁ δ₂)) window s B := by
  let E := Q.literalOriginalSchwartzModel ξ recipe a Z t Y₁ Y₂ centered
    hZ hY₁ hY₂ reference href original hreference ht hpositive hcompact.isClosed
  have hb := Q.literalOriginalSchwartzModel_bound ξ recipe a Z t Y₁ Y₂ centered
    hZ hY₁ hY₂ reference href original hreference ht hpositive hcompact.isClosed hB
  exact CanonicalLiteralFullKappaInput.scalarFreeBalanced (σ := σ) E b P R power firstFixed
    poolFixed unitFixed firstElement poolElement unitElement hfirst hpool hunit
    δ₁ δ₂ hcompact hpositive s B hB hδhi hb.1 hb.2.1 hb.2.2 hprime

end CompleteMovingRowRecipe
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralFullKappaInput.scalarFreeBalanced
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralFullKappaInput.ofLiteral
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalScalarFreeComputedProfiles
