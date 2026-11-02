import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralExceptionalAtoms
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralActiveOriginalScale

set_option linter.unusedSectionVars false
set_option quotPrecheck false

/-!
# Fixed annulus payment in the actual exceptional atomic scales

An extracted prime has its true ideal norm, not its nominal power of Z.
Two original extraction windows therefore contribute a fixed annulus
factor. This factor changes only the numerical root constant in the
atomic estimate. The allocation, profiles, source and formal slot
lengths remain exactly the original ones.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalPaidScales

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments HeckePort.Moments.Support

variable {K : Type} [Field K] [NumberField K]

section Scales

variable {k : ℕ} (B : ActualColumnAllocation K k)
variable (Z targetTotal : ℝ) (length : Fin k → ℝ) (hlength : ∀ i, 0 ≤ length i)
variable (annulus amplitude : ℝ) (cap : ℕ)
variable (hannulus : 1 ≤ annulus) (hamplitude : 0 ≤ amplitude)

def scales : ExceptionalAtomicScales B :=
  { B.originalAtomicScales Z (targetTotal - ∑ i, length i) length hlength
      (fun _ => annulus) (fun _ => amplitude) (fun _ => hannulus) (fun _ => hamplitude) with
    rootConstant := annulus ^ cap
    rootConstant_nonneg := pow_nonneg (zero_le_one.trans hannulus) cap }

theorem scales_exponent :
    (scales B Z targetTotal length hlength annulus amplitude cap hannulus hamplitude).exponent =
      targetTotal / 2 - B.rawExtractionLength Z length := by
  sorry

theorem rectangle_root_window (hZ : 1 < Z)
    (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hproduct : X₁ * X₂ * ∏ i, Z ^ length i ≤ (annulus ^ cap) ^ 2 * Z ^ targetTotal) :
    Z ^ (2 * ((Real.log (X₁ * X₂) / Real.log Z - B.plainExtractionLength Z) / 2)) ≤
      (annulus ^ cap) ^ 2 *
        Z ^ (2 * ((targetTotal - ∑ i, length i - B.plainExtractionLength Z) / 2)) := by
  sorry

end Scales

section ActualControl

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {Ψ : Ideal (𝓞 K) →* ℂ} {W₁ W₂ : ℝ → ℂ} {g h : A.R} {k : ℕ}
variable (s : AllocatedExceptionalSource (V := V) (σ := σ) Ψ W₁ W₂ g h k)
variable (Z targetTotal : ℝ) (length : Fin k → ℝ) (hlength : ∀ i, 0 ≤ length i)
variable (annulus amplitude : ℝ) (cap : ℕ)
variable (hannulus : 1 ≤ annulus) (hamplitude : 0 ≤ amplitude)

/-- All original character and prime controls are inherited from the
actual constructor. Only the rectangle window is enlarged by the
fixed annulus cost proved on the two original occurrence extractions. -/
def control (hZ : 1 < Z) (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (original : s.AtomicControl Z
      (s.allocation.originalAtomicScales Z (Real.log (X₁ * X₂) / Real.log Z)
        length hlength (fun _ => annulus) (fun _ => amplitude)
        (fun _ => hannulus) (fun _ => hamplitude)))
    (hproduct : X₁ * X₂ * ∏ i, Z ^ length i ≤ (annulus ^ cap) ^ 2 * Z ^ targetTotal) :
    s.AtomicControl Z
      (scales s.allocation Z targetTotal length hlength annulus amplitude cap hannulus hamplitude) where
  base_pos := original.base_pos
  plain₁ := original.plain₁
  plain₂ := original.plain₂
  frozen_prime := original.frozen_prime
  frozen_annulus := original.frozen_annulus
  frozen_profile := original.frozen_profile
  frozen_norm := original.frozen_norm
  rectangle_product := by
    apply original.rectangle_product.trans
    simpa only [ActualColumnAllocation.originalAtomicScales, scales, one_pow, one_mul] using
      rectangle_root_window s.allocation Z targetTotal length annulus cap hZ
        X₁ X₂ hX₁ hX₂ hproduct
  prime_norm := original.prime_norm
  prime_atom := original.prime_atom

end ActualControl

section OriginalExtractions

variable {A : SArithmeticData K} {σ : K →+* ℂ} {k : ℕ}
variable (d : CanonicalLiteralRectangles.Atoms (K := K) k)
variable {support₁ : Finset (Ideal (𝓞 K))}
variable (b₁ : SupportCartesianBranch d.plain₁ d.plain₂ d.slots support₁)
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable (power firstFixed poolFixed unitFixed : A.Exterior)
variable (firstElement poolElement unitElement : A.R)
variable (hfirst : A.Generates firstFixed firstElement)
variable (hpool : A.Generates poolFixed poolElement)
variable (hunit : A.Generates unitFixed unitElement) (δ₁ δ₂ : ℝ)

local notation "beforeSecond" => d.secondInput (σ := σ) b₁ P R
  power firstFixed poolFixed unitFixed firstElement poolElement unitElement
    hfirst hpool hunit δ₁ δ₂

variable {support₂ : Finset (Ideal (𝓞 K))}
variable (b₂ : SupportCartesianBranch (beforeSecond).plain₁ (beforeSecond).plain₂
  (beforeSecond).slots support₂)
variable (annulus : ℝ) (hannulus : 1 ≤ annulus) (cap : ℕ) (hcap : k ≤ cap)
variable (hprime : d.PrimeNormWindow annulus)

local notation "N₁" => (Ideal.absNorm (frozenSourceIdeal b₁.plainDivisor₁
  b₁.plainDivisor₂ b₁.keep b₁.witness.2) : ℝ)
local notation "N₂" => (Ideal.absNorm (frozenSourceIdeal b₂.plainDivisor₁
  b₂.plainDivisor₂ b₂.keep b₂.witness.2) : ℝ)

include hprime hannulus hcap in
/-- Both original frozen ideals occur in this exact comparison.
Only their individual prime annuli are bounded, and each is paid once. -/
theorem two_extraction_product (rectangle : Bool) :
    ((beforeSecond).extract b₂).scaleProduct rectangle * (N₁ * N₂) ≤
      (annulus ^ cap) ^ 2 * d.scaleProduct rectangle := by
  sorry

variable {ι : Type*} {columns : Finset ι} {ideal : ι → A.Exterior}
variable (atlas : SourceCartesianAtlas columns ideal) (count : b₂.keep.card = atlas.slotCount)
variable (scalar : ℂ) (balance : Bool → ℝ)

local notation "finalTable" =>
  ((((beforeSecond).extract b₂).onAtlas atlas count).scale scalar).balancePlain balance

include hprime hannulus hcap in
/-- The real final atlas, scalar and balancing keep their original
formal scales. No bound on a completed source is requested. -/
theorem final_scaleProduct_window (rectangle : Bool) (originalTotal : ℝ)
    (horiginal : d.scaleProduct rectangle = d.base ^ originalTotal) :
    (finalTable).scaleProduct rectangle ≤ (annulus ^ cap) ^ 2 *
      d.base ^ (originalTotal - idealLogLength d.base
        (frozenSourceIdeal b₁.plainDivisor₁ b₁.plainDivisor₂ b₁.keep b₁.witness.2) -
          idealLogLength d.base
            (frozenSourceIdeal b₂.plainDivisor₁ b₂.plainDivisor₂ b₂.keep b₂.witness.2)) := by
  sorry

end OriginalExtractions

section History

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable {k : ℕ} (d : CanonicalLiteralRectangles.Atoms (K := K) k)

/-- A literal numerical trace of the two original extractions. The
only final-table fields are equalities of unchanged formal scales;
no norm inequality or source estimate is stored. The actual atlas,
scalar and balance constructor supplies them by the scale identities
above. -/
structure History where
  originalCount : ℕ
  original : CanonicalLiteralRectangles.Atoms (K := K) originalCount
  firstSupport : Finset (Ideal (𝓞 K))
  first : SupportCartesianBranch original.plain₁ original.plain₂ original.slots firstSupport
  power : A.Exterior
  firstFixed : A.Exterior
  poolFixed : A.Exterior
  unitFixed : A.Exterior
  firstElement : A.R
  poolElement : A.R
  unitElement : A.R
  first_generates : A.Generates firstFixed firstElement
  pool_generates : A.Generates poolFixed poolElement
  unit_generates : A.Generates unitFixed unitElement
  firstTilt : ℝ
  secondTilt : ℝ
  secondSupport : Finset (Ideal (𝓞 K))
  second : SupportCartesianBranch
    (original.secondInput (σ := σ) first P R power firstFixed poolFixed unitFixed
      firstElement poolElement unitElement first_generates pool_generates unit_generates
      firstTilt secondTilt).plain₁
    (original.secondInput (σ := σ) first P R power firstFixed poolFixed unitFixed
      firstElement poolElement unitElement first_generates pool_generates unit_generates
      firstTilt secondTilt).plain₂
    (original.secondInput (σ := σ) first P R power firstFixed poolFixed unitFixed
      firstElement poolElement unitElement first_generates pool_generates unit_generates
      firstTilt secondTilt).slots secondSupport
  base_eq : d.base = original.base
  scale_eq : d.scaleProduct false =
    ((original.secondInput (σ := σ) first P R power firstFixed poolFixed unitFixed
      firstElement poolElement unitElement first_generates pool_generates unit_generates
      firstTilt secondTilt).extract second).scaleProduct false

variable {P R d} (H : History (σ := σ) P R d)

def History.firstIdeal : Ideal (𝓞 K) :=
  frozenSourceIdeal H.first.plainDivisor₁ H.first.plainDivisor₂ H.first.keep H.first.witness.2

def History.secondIdeal : Ideal (𝓞 K) :=
  frozenSourceIdeal H.second.plainDivisor₁ H.second.plainDivisor₂ H.second.keep H.second.witness.2

theorem History.firstIdeal_ne_zero : H.firstIdeal ≠ 0 := by
  sorry
theorem History.secondIdeal_ne_zero : H.secondIdeal ≠ 0 := by
  sorry

/-- The original prime window and original scale product produce the
final table window, with both actual frozen ideals retained. -/
theorem History.window (annulus : ℝ) (hannulus : 1 ≤ annulus) (cap : ℕ)
    (hcap : H.originalCount ≤ cap) (hprime : H.original.PrimeNormWindow annulus)
    (originalTotal : ℝ)
    (horiginal : H.original.scaleProduct false = H.original.base ^ originalTotal) :
    d.scaleProduct false ≤ (annulus ^ cap) ^ 2 *
      d.base ^ (originalTotal - idealLogLength d.base H.firstIdeal -
        idealLogLength d.base H.secondIdeal) := by
  sorry

variable {n : ℕ} (original : CanonicalLiteralRectangles.Atoms (K := K) n)
variable {firstSupport : Finset (Ideal (𝓞 K))}
variable (first : SupportCartesianBranch original.plain₁ original.plain₂ original.slots firstSupport)
variable (power firstFixed poolFixed unitFixed : A.Exterior)
variable (firstElement poolElement unitElement : A.R)
variable (hfirst : A.Generates firstFixed firstElement)
variable (hpool : A.Generates poolFixed poolElement)
variable (hunit : A.Generates unitFixed unitElement) (δ₁ δ₂ : ℝ)
local notation "secondInput" => original.secondInput (σ := σ) first P R power firstFixed
  poolFixed unitFixed firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂
variable {secondSupport : Finset (Ideal (𝓞 K))}
variable (second : SupportCartesianBranch (secondInput).plain₁ (secondInput).plain₂
  (secondInput).slots secondSupport)
variable {ι : Type*} {columns : Finset ι} {ideal : ι → A.Exterior}
variable (atlas : SourceCartesianAtlas columns ideal) (count : second.keep.card = atlas.slotCount)
variable (scalar : ℂ) (balance : Bool → ℝ)

/-- The actual constructor supplies every equality in the history;
its caller provides no final scale-product certificate. -/
def History.ofActual : History (σ := σ) P R
    (((((secondInput).extract second).onAtlas atlas count).scale scalar).balancePlain balance) where
  originalCount := n
  original := original
  firstSupport := firstSupport
  first := first
  power := power
  firstFixed := firstFixed
  poolFixed := poolFixed
  unitFixed := unitFixed
  firstElement := firstElement
  poolElement := poolElement
  unitElement := unitElement
  first_generates := hfirst
  pool_generates := hpool
  unit_generates := hunit
  firstTilt := δ₁
  secondTilt := δ₂
  secondSupport := secondSupport
  second := second
  base_eq := by
    change (((secondInput).extract second).onAtlas atlas count).base = original.base
    cases count
    rfl
  scale_eq := by
    rw [CanonicalLiteralRectangles.Atoms.balancePlain_scaleProduct,
      CanonicalLiteralRectangles.Atoms.scale_scaleProduct,
      CanonicalLiteralRectangles.Atoms.onAtlas_scaleProduct]

end History

end HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalPaidScales

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalPaidScales.scales_exponent
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalPaidScales.control
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalPaidScales.two_extraction_product
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalPaidScales.final_scaleProduct_window
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalPaidScales.History.window
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralExceptionalPaidScales.History.ofActual
