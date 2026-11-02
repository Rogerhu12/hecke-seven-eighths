import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.LiteralProfiles
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLogProfileBounds
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.LiteralAtlas
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.LiteralPhases
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalClippedProfileBounds
import HeckeGeneral.Analysis.IdealDirichlet
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalFullKappaNormalization

set_option linter.unusedSectionVars false

/-!
# The exact scalar costs in the actual two-stage profiles

The inverse norm and both Mellin powers give one fixed power of the
profile variable. The remaining scale factors are displayed separately
at each original occurrence. In particular the two plain factors are
not replaced by their maximum: their product has the original centered
scale cancellation. The actual first common scalar and pool scalar
remain explicit complex factors.

The positive reciprocal balance below has an exact product identity.
It is an input to an equality-preserving atom-table construction, not
an assertion that the existing table was already balanced.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2

open HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments HeckePort.Moments.Support

namespace CanonicalLiteralProfileScalars

def exponent (δ₁ δ₂ : ℝ) : ℝ := -1 + δ₁ + δ₂

/-- The scale of the original Gauss denominator and the scale of the
selected centered rectangle need not agree. -/
def plainFactor (gaussScale profileScale δ₁ δ₂ : ℝ) : ℝ :=
  Real.sqrt gaussScale * profileScale ^ exponent δ₁ δ₂

theorem plainFactor_pos {G N : ℝ} (hG : 0 < G) (hN : 0 < N) (δ₁ δ₂ : ℝ) :
    0 < plainFactor G N δ₁ δ₂ := by
  sorry

theorem normPower_product {N y : ℝ} (hN : 0 < N) (hy : 0 < y) (δ₁ δ₂ : ℝ) :
    (((N * y) ^ (-1 : ℝ) : ℝ) : ℂ) * (((N * y) ^ δ₁ : ℝ) : ℂ) * (((N * y) ^ δ₂ : ℝ) : ℂ) =
      ((N ^ exponent δ₁ δ₂ : ℝ) : ℂ) * ((y ^ exponent δ₁ δ₂ : ℝ) : ℂ) := by
  sorry

theorem plainFactor_product {G₁ G₂ N₁ N₂ : ℝ}
    (hG₁ : 0 < G₁) (hG₂ : 0 < G₂) (hN₁ : 0 < N₁) (hN₂ : 0 < N₂)
    (δ₁ δ₂ : ℝ) :
    plainFactor G₁ N₁ δ₁ δ₂ * plainFactor G₂ N₂ δ₁ δ₂ =
      Real.sqrt (G₁ * G₂) * (N₁ * N₂) ^ exponent δ₁ δ₂ := by
  sorry

/-- The two rectangle scales are compared through their product,
never by separate upper bounds on the comparison scales. -/
theorem plainFactor_product_of_equal_product {G₁ G₂ N₁ N₂ : ℝ}
    (hG₁ : 0 < G₁) (hG₂ : 0 < G₂) (hN₁ : 0 < N₁) (hN₂ : 0 < N₂)
    (heq : N₁ * N₂ = G₁ * G₂) (δ₁ δ₂ : ℝ) :
    plainFactor G₁ N₁ δ₁ δ₂ * plainFactor G₂ N₂ δ₁ δ₂ =
      (G₁ * G₂) ^ (-1 / 2 + δ₁ + δ₂) := by
  sorry

/-- This is a positive scalar even when either original complex
profile or the common frozen scalar vanishes. -/
def balance (left right : ℝ) : ℝ := Real.sqrt right / Real.sqrt left

theorem balance_pos {left right : ℝ} (hl : 0 < left) (hr : 0 < right) :
    0 < balance left right := by
  sorry

theorem balance_mul_left {left right : ℝ} (hl : 0 < left) (hr : 0 < right) :
    balance left right * left = Real.sqrt (left * right) := by
  sorry

theorem right_div_balance {left right : ℝ} (hl : 0 < left) (hr : 0 < right) :
    right / balance left right = Real.sqrt (left * right) := by
  sorry

theorem balance_preserves_product {left right : ℝ} (hl : 0 < left) (hr : 0 < right) :
    (balance left right * left) * (right / balance left right) = left * right := by
  sorry

end CanonicalLiteralProfileScalars

variable {K : Type} [Field K] [NumberField K] {k : ℕ}

namespace CanonicalLiteralRectangles.Atoms

variable (d : CanonicalLiteralRectangles.Atoms (K := K) k)
variable {support : Finset (Ideal (𝓞 K))}
variable (b : SupportCartesianBranch d.plain₁ d.plain₂ d.slots support)

theorem extract_scale_product (r : Bool)
    (h : d.scale₁ r * d.scale₂ r = d.scale₁ false * d.scale₂ false) :
    (d.extract b).scale₁ r * (d.extract b).scale₂ r =
      (d.extract b).scale₁ false * (d.extract b).scale₂ false := by
  sorry

theorem extracted_plainFactor_product (r : Bool) (δ₁ δ₂ : ℝ)
    (h : d.scale₁ r * d.scale₂ r = d.scale₁ false * d.scale₂ false) :
    CanonicalLiteralProfileScalars.plainFactor
        ((d.extract b).scale₁ false) ((d.extract b).scale₁ r) δ₁ δ₂ *
      CanonicalLiteralProfileScalars.plainFactor
        ((d.extract b).scale₂ false) ((d.extract b).scale₂ r) δ₁ δ₂ =
      ((d.extract b).scale₁ false * (d.extract b).scale₂ false) ^
        (-1 / 2 + δ₁ + δ₂) := by
  sorry

namespace ProfileData

variable {d} (W : d.ProfileData)
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable (P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P)
variable (power firstFixed poolFixed unitFixed : A.Exterior)
variable (firstElement poolElement unitElement : A.R)
variable (hfirst : A.Generates firstFixed firstElement)
variable (hpool : A.Generates poolFixed poolElement)
variable (hunit : A.Generates unitFixed unitElement)
variable (δ₁ δ₂ : ℝ)

/-- Literal left profile, with both fixed complex scalars kept
outside the positive per-occurrence factor. -/
theorem secondInput_left_shape (r : Bool)
    (u : HeckeGeneral.Analysis.NonzeroIdeal K) (time : ℝ) {y : ℝ} (hy : 0 < y) :
    ((W.secondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
        firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂).left r).profile u time y =
      (d.commonScalar b *
        (((A.exteriorNorm power ^ δ₁ : ℝ) : ℂ) *
          actualIdealResidue (A := A) (σ := σ) power.val firstElement)) *
        (CanonicalLiteralProfileScalars.plainFactor
          ((d.extract b).scale₁ false) ((d.extract b).scale₁ r) δ₁ δ₂ : ℂ) *
        ((W.left r).profile u time y *
          ((y ^ CanonicalLiteralProfileScalars.exponent δ₁ δ₂ : ℝ) : ℂ)) := by
  sorry

theorem secondInput_right_shape (r : Bool)
    (u : HeckeGeneral.Analysis.NonzeroIdeal K) (time : ℝ) {y : ℝ} (hy : 0 < y) :
    ((W.secondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
        firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂).right r).profile u time y =
      (CanonicalLiteralProfileScalars.plainFactor
        ((d.extract b).scale₂ false) ((d.extract b).scale₂ r) δ₁ δ₂ : ℂ) *
        ((W.right r).profile u time y *
          ((y ^ CanonicalLiteralProfileScalars.exponent δ₁ δ₂ : ℝ) : ℂ)) := by
  sorry

theorem secondInput_slot_shape (j : Fin b.keep.card) (time : ℝ) {y : ℝ} (hy : 0 < y) :
    ((W.secondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
        firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂).slot j).profile time y =
      (CanonicalLiteralProfileScalars.plainFactor
        ((d.extract b).base ^ (d.extract b).length j)
        ((d.extract b).base ^ (d.extract b).length j) δ₁ δ₂ : ℂ) *
        ((W.slot (SlotRestriction.index b.keep j)).profile time y *
          ((y ^ CanonicalLiteralProfileScalars.exponent δ₁ δ₂ : ℝ) : ℂ)) := by
  sorry

end ProfileData
end CanonicalLiteralRectangles.Atoms
end HeckeSkeleton.Moments.EngineStepV2

end

/-!
# Constructed Schwartz representatives of the actual literal profiles

Each representative is built from the original profile at the original
row and time. The two norm transforms contribute their exact real
power and scalar. Extraction and atlas transport only select the same
original occurrences. Every coefficient in the seminorm estimates is
displayed; no maximum over moving leaves is chosen.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2

open HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments HeckePort.Moments.Support

namespace CanonicalLiteralSchwartzProfiles

def powerAtom (exponent : ℝ) : CanonicalLogProfiles.Atom ℝ where
  scale := 1
  scale_pos := zero_lt_one
  exponent := exponent
  offset := 0
  direction := 0

def powerSchwartz (window : Set ℝ) (hcompact : IsCompact window)
    (hpositive : window ⊆ Set.Ioi 0) (c : ℂ) (exponent : ℝ)
    (φ : 𝓢(ℝ, ℂ)) (hsupport : tsupport φ ⊆ window) : 𝓢(ℝ, ℂ) :=
  c • (powerAtom exponent).schwartz window hcompact hpositive 0 φ hsupport

@[simp] theorem powerSchwartz_apply (window : Set ℝ) (hcompact : IsCompact window)
    (hpositive : window ⊆ Set.Ioi 0) (c : ℂ) (exponent : ℝ)
    (φ : 𝓢(ℝ, ℂ)) (hsupport : tsupport φ ⊆ window) (y : ℝ) :
    powerSchwartz window hcompact hpositive c exponent φ hsupport y =
      c * (φ y * ((y ^ exponent : ℝ) : ℂ)) := by
  sorry

theorem powerSchwartz_support (window : Set ℝ) (hcompact : IsCompact window)
    (hpositive : window ⊆ Set.Ioi 0) (c : ℂ) (exponent : ℝ)
    (φ : 𝓢(ℝ, ℂ)) (hsupport : tsupport φ ⊆ window) :
    tsupport (powerSchwartz window hcompact hpositive c exponent φ hsupport) ⊆ window := by
  sorry

/-- Its coefficient and required original orders are fixed by the
annulus, real power and target orders before the original profile. -/
theorem powerSchwartz_finset_bound (window : Set ℝ) (hcompact : IsCompact window)
    (hpositive : window ⊆ Set.Ioi 0) (c : ℂ) (exponent : ℝ)
    (s : Finset (ℕ × ℕ)) (φ : 𝓢(ℝ, ℂ)) (hsupport : tsupport φ ⊆ window) :
    s.sup (schwartzSeminormFamily ℂ ℝ ℂ)
        (powerSchwartz window hcompact hpositive c exponent φ hsupport) ≤
      ‖c‖ * CanonicalLogProfiles.shapeCoefficient window hcompact hpositive exponent s *
        (CanonicalLogProfiles.sourceOrders s).sup (schwartzSeminormFamily ℂ ℝ ℂ) φ := by
  sorry

end CanonicalLiteralSchwartzProfiles

variable {K : Type} [Field K] [NumberField K]

namespace CanonicalLiteralRectangles.Atoms.ProfileData

variable {k : ℕ} {d : CanonicalLiteralRectangles.Atoms (K := K) k}

/-- These are computed representatives of the already fixed tests.
No bound on a child, sum, energy or kernel is a field. -/
structure SchwartzModel (W : d.ProfileData) (window : Set ℝ) where
  left : Bool → 𝓢(ℝ, ℂ)
  right : Bool → 𝓢(ℝ, ℂ)
  slot : Fin k → 𝓢(ℝ, ℂ)
  left_eq : ∀ r u t y, (W.left r).profile u t y = left r y
  right_eq : ∀ r u t y, (W.right r).profile u t y = right r y
  slot_eq : ∀ j t y, (W.slot j).profile t y = slot j y
  left_support : ∀ r, tsupport (left r) ⊆ window
  right_support : ∀ r, tsupport (right r) ⊆ window
  slot_support : ∀ j, tsupport (slot j) ⊆ window

namespace SchwartzModel

variable {W : d.ProfileData} {window : Set ℝ} (E : W.SchwartzModel window)

def extract {support : Finset (Ideal (𝓞 K))}
    (b : SupportCartesianBranch d.plain₁ d.plain₂ d.slots support) :
    (W.extract b).SchwartzModel window where
  left := E.left
  right := E.right
  slot j := E.slot (SlotRestriction.index b.keep j)
  left_eq := E.left_eq
  right_eq := E.right_eq
  slot_eq j := E.slot_eq (SlotRestriction.index b.keep j)
  left_support := E.left_support
  right_support := E.right_support
  slot_support j := E.slot_support (SlotRestriction.index b.keep j)

def onAtlas {A : SArithmeticData K} {ι : Type*}
    {columns : Finset ι} {ideal : ι → A.Exterior}
    (T : SourceCartesianAtlas columns ideal) (count : k = T.slotCount) :
    (W.onAtlas T count).SchwartzModel window := by
  cases count
  exact
    { left := E.left
      right := E.right
      slot := E.slot
      left_eq := E.left_eq
      right_eq := E.right_eq
      slot_eq := E.slot_eq
      left_support := E.left_support
      right_support := E.right_support
      slot_support := E.slot_support }

def deleteMask (M : HeckeGeneral.Analysis.NonzeroIdeal K) :
    (W.deleteMask M).SchwartzModel window where
  left := E.left
  right := E.right
  slot := E.slot
  left_eq := E.left_eq
  right_eq := E.right_eq
  slot_eq := E.slot_eq
  left_support := E.left_support
  right_support := E.right_support
  slot_support := E.slot_support

def balancePlain (c : Bool → ℝ) : (W.balancePlain c).SchwartzModel window where
  left r := (c r : ℂ) • E.left r
  right r := (c r : ℂ)⁻¹ • E.right r
  slot := E.slot
  left_eq r u t y := by
    change (W.left r).profile u t y * (c r : ℂ) = (c r : ℂ) * E.left r y
    rw [E.left_eq]
    ring
  right_eq r u t y := by
    change (W.right r).profile u t y * (c r : ℂ)⁻¹ = (c r : ℂ)⁻¹ * E.right r y
    rw [E.right_eq]
    ring
  slot_eq := E.slot_eq
  left_support r := (tsupport_smul_subset_right (fun _ : ℝ => (c r : ℂ))
    (E.left r)).trans (E.left_support r)
  right_support r := (tsupport_smul_subset_right (fun _ : ℝ => (c r : ℂ)⁻¹)
    (E.right r)).trans (E.right_support r)
  slot_support := E.slot_support

theorem balancePlain_left_seminorm (c : Bool → ℝ) (r : Bool) (s : Finset (ℕ × ℕ)) :
    s.sup (schwartzSeminormFamily ℂ ℝ ℂ) ((E.balancePlain c).left r) =
      ‖(c r : ℂ)‖ * s.sup (schwartzSeminormFamily ℂ ℝ ℂ) (E.left r) := by
  sorry

theorem balancePlain_right_seminorm (c : Bool → ℝ) (r : Bool) (s : Finset (ℕ × ℕ)) :
    s.sup (schwartzSeminormFamily ℂ ℝ ℂ) ((E.balancePlain c).right r) =
      ‖(c r : ℂ)⁻¹‖ * s.sup (schwartzSeminormFamily ℂ ℝ ℂ) (E.right r) := by
  sorry

/-- A transport for literal individual profile identities. The
following `secondInput` constructor supplies these identities from the
actual original operations. -/
def powerProfiles {d' : CanonicalLiteralRectangles.Atoms (K := K) k}
    (W' : d'.ProfileData) (hcompact : IsCompact window)
    (hpositive : window ⊆ Set.Ioi 0) (exponent : ℝ)
    (leftScalar rightScalar : Bool → ℂ) (slotScalar : Fin k → ℂ)
    (hleft : ∀ r u t y, 0 < y →
      (W'.left r).profile u t y = leftScalar r * ((W.left r).profile u t y * ((y ^ exponent : ℝ) : ℂ)))
    (hright : ∀ r u t y, 0 < y →
      (W'.right r).profile u t y = rightScalar r * ((W.right r).profile u t y * ((y ^ exponent : ℝ) : ℂ)))
    (hslot : ∀ j t y, 0 < y →
      (W'.slot j).profile t y = slotScalar j * ((W.slot j).profile t y * ((y ^ exponent : ℝ) : ℂ))) :
    W'.SchwartzModel window where
  left r := CanonicalLiteralSchwartzProfiles.powerSchwartz window hcompact hpositive
    (leftScalar r) exponent (E.left r) (E.left_support r)
  right r := CanonicalLiteralSchwartzProfiles.powerSchwartz window hcompact hpositive
    (rightScalar r) exponent (E.right r) (E.right_support r)
  slot j := CanonicalLiteralSchwartzProfiles.powerSchwartz window hcompact hpositive
    (slotScalar j) exponent (E.slot j) (E.slot_support j)
  left_eq r u t y := by
    by_cases hy : 0 < y
    · rw [hleft r u t y hy, CanonicalLiteralSchwartzProfiles.powerSchwartz_apply, E.left_eq]
    · have hnew : (W'.left r).profile u t y = 0 := by
        by_contra hn
        exact hy (W'.left_positive r u t y hn)
      have hold : E.left r y = 0 := by
        by_contra hn
        exact hy (hpositive (E.left_support r (subset_tsupport _ hn)))
      rw [hnew, CanonicalLiteralSchwartzProfiles.powerSchwartz_apply, hold, zero_mul, mul_zero]
  right_eq r u t y := by
    by_cases hy : 0 < y
    · rw [hright r u t y hy, CanonicalLiteralSchwartzProfiles.powerSchwartz_apply, E.right_eq]
    · have hnew : (W'.right r).profile u t y = 0 := by
        by_contra hn
        exact hy (W'.right_positive r u t y hn)
      have hold : E.right r y = 0 := by
        by_contra hn
        exact hy (hpositive (E.right_support r (subset_tsupport _ hn)))
      rw [hnew, CanonicalLiteralSchwartzProfiles.powerSchwartz_apply, hold, zero_mul, mul_zero]
  slot_eq j t y := by
    by_cases hy : 0 < y
    · rw [hslot j t y hy, CanonicalLiteralSchwartzProfiles.powerSchwartz_apply, E.slot_eq]
    · have hnew : (W'.slot j).profile t y = 0 := by
        by_contra hn
        exact hy (W'.slot_positive j t y hn)
      have hold : E.slot j y = 0 := by
        by_contra hn
        exact hy (hpositive (E.slot_support j (subset_tsupport _ hn)))
      rw [hnew, CanonicalLiteralSchwartzProfiles.powerSchwartz_apply, hold, zero_mul, mul_zero]
  left_support r := CanonicalLiteralSchwartzProfiles.powerSchwartz_support
    window hcompact hpositive _ _ _ (E.left_support r)
  right_support r := CanonicalLiteralSchwartzProfiles.powerSchwartz_support
    window hcompact hpositive _ _ _ (E.right_support r)
  slot_support j := CanonicalLiteralSchwartzProfiles.powerSchwartz_support
    window hcompact hpositive _ _ _ (E.slot_support j)

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

/-- The same actual two-stage profile table now has constructed
Schwartz representatives. Its first common scalar, actual pool
residue, quotient scales and every retained occurrence are unchanged. -/
def secondInput (hcompact : IsCompact window) (hpositive : window ⊆ Set.Ioi 0) :
    (W.secondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
      firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂).SchwartzModel window :=
  (E.extract b).powerProfiles
    (W.secondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
      firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂)
    hcompact hpositive (CanonicalLiteralProfileScalars.exponent δ₁ δ₂)
    (fun r => (d.commonScalar b *
      (((A.exteriorNorm power ^ δ₁ : ℝ) : ℂ) *
        actualIdealResidue (A := A) (σ := σ) power.val firstElement)) *
      (CanonicalLiteralProfileScalars.plainFactor
        ((d.extract b).scale₁ false) ((d.extract b).scale₁ r) δ₁ δ₂ : ℂ))
    (fun r => (CanonicalLiteralProfileScalars.plainFactor
      ((d.extract b).scale₂ false) ((d.extract b).scale₂ r) δ₁ δ₂ : ℂ))
    (fun j => (CanonicalLiteralProfileScalars.plainFactor
      ((d.extract b).base ^ (d.extract b).length j)
      ((d.extract b).base ^ (d.extract b).length j) δ₁ δ₂ : ℂ))
    (fun r u t y hy => W.secondInput_left_shape (σ := σ) b P R
      power firstFixed poolFixed unitFixed firstElement poolElement unitElement
      hfirst hpool hunit δ₁ δ₂ r u t hy)
    (fun r u t y hy => W.secondInput_right_shape (σ := σ) b P R
      power firstFixed poolFixed unitFixed firstElement poolElement unitElement
      hfirst hpool hunit δ₁ δ₂ r u t hy)
    (fun j t y hy => W.secondInput_slot_shape (σ := σ) b P R
      power firstFixed poolFixed unitFixed firstElement poolElement unitElement
      hfirst hpool hunit δ₁ δ₂ j t hy)

theorem secondInput_left_seminorm_le (hcompact : IsCompact window)
    (hpositive : window ⊆ Set.Ioi 0) (r : Bool) (s : Finset (ℕ × ℕ)) :
    s.sup (schwartzSeminormFamily ℂ ℝ ℂ)
      ((E.secondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
        firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂ hcompact hpositive).left r) ≤
      ‖(d.commonScalar b *
        (((A.exteriorNorm power ^ δ₁ : ℝ) : ℂ) *
          actualIdealResidue (A := A) (σ := σ) power.val firstElement)) *
        (CanonicalLiteralProfileScalars.plainFactor
          ((d.extract b).scale₁ false) ((d.extract b).scale₁ r) δ₁ δ₂ : ℂ)‖ *
        CanonicalLogProfiles.shapeCoefficient window hcompact hpositive
          (CanonicalLiteralProfileScalars.exponent δ₁ δ₂) s *
        (CanonicalLogProfiles.sourceOrders s).sup (schwartzSeminormFamily ℂ ℝ ℂ) (E.left r) := by
  sorry

theorem secondInput_right_seminorm_le (hcompact : IsCompact window)
    (hpositive : window ⊆ Set.Ioi 0) (r : Bool) (s : Finset (ℕ × ℕ)) :
    s.sup (schwartzSeminormFamily ℂ ℝ ℂ)
      ((E.secondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
        firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂ hcompact hpositive).right r) ≤
      ‖(CanonicalLiteralProfileScalars.plainFactor
        ((d.extract b).scale₂ false) ((d.extract b).scale₂ r) δ₁ δ₂ : ℂ)‖ *
        CanonicalLogProfiles.shapeCoefficient window hcompact hpositive
          (CanonicalLiteralProfileScalars.exponent δ₁ δ₂) s *
        (CanonicalLogProfiles.sourceOrders s).sup (schwartzSeminormFamily ℂ ℝ ℂ) (E.right r) := by
  sorry

theorem secondInput_slot_seminorm_le (hcompact : IsCompact window)
    (hpositive : window ⊆ Set.Ioi 0) (j : Fin b.keep.card) (s : Finset (ℕ × ℕ)) :
    s.sup (schwartzSeminormFamily ℂ ℝ ℂ)
      ((E.secondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
        firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂ hcompact hpositive).slot j) ≤
      ‖(CanonicalLiteralProfileScalars.plainFactor
        ((d.extract b).base ^ (d.extract b).length j)
        ((d.extract b).base ^ (d.extract b).length j) δ₁ δ₂ : ℂ)‖ *
        CanonicalLogProfiles.shapeCoefficient window hcompact hpositive
          (CanonicalLiteralProfileScalars.exponent δ₁ δ₂) s *
        (CanonicalLogProfiles.sourceOrders s).sup (schwartzSeminormFamily ℂ ℝ ℂ)
          (E.slot (SlotRestriction.index b.keep j)) := by
  sorry

end SchwartzModel
end CanonicalLiteralRectangles.Atoms.ProfileData

namespace CompleteMovingRowRecipe

variable {A : SArithmeticData K}
variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {ω ψ : HeckeCharacter K} {X : Type*} {data : X → MomentData K ω ψ}
variable (Q : CompleteMovingRowRecipe A P R data)

/-- The original window constructs the literal frozen representatives.
Only one original allowed row is used, before any descendant exists. -/
def literalOriginalSchwartzModel (ξ : X)
    (W : NormProfileRecipe (fun _ : PUnit => data ξ))
    (a : RealParameters) (Z t Y₁ Y₂ : ℝ) (centered : Bool)
    (hZ : 1 < Z) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)
    (reference : HeckeGeneral.Analysis.NonzeroIdeal K)
    (href : (data ξ).allowedRow reference)
    {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
    {heightDomain window : Set ℝ} {seminorms : Finset (ℕ × ℕ)} {bound : ℝ}
    (original : RawProfileWindow rowDomain heightDomain window seminorms (data ξ) bound)
    (hreference : reference ∈ rowDomain) (ht : t ∈ heightDomain)
    (hwindow : window ⊆ Set.Ioi 0) (hclosed : IsClosed window) :
    ((HeckeSkeleton.Moments.EngineStepV2.CompleteMovingRowRecipe.literalOriginalProfileDataOfWindow Q) ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      reference href original hreference ht hwindow).SchwartzModel window where
  left r := if r && !centered then 0 else original.leftRep reference t
  right _ := original.rightRep reference t
  slot j := original.primeRep j t
  left_eq r u time y := by
    change (data ξ).plainTest₁.profile reference t y *
        (if r && !centered then 0 else 1) =
      (if r && !centered then (0 : 𝓢(ℝ, ℂ)) else original.leftRep reference t) y
    split_ifs <;> simp only [mul_zero, mul_one, SchwartzMap.zero_apply, original.left_eq]
  right_eq r u time y := original.right_eq reference t y
  slot_eq j time y := original.prime_eq j t y
  left_support r := by
    split_ifs
    · simp only [SchwartzMap.coe_zero, tsupport_zero, Set.empty_subset]
    · exact closure_minimal (original.left_support reference hreference t ht) hclosed
  right_support _ :=
    closure_minimal (original.right_support reference hreference t ht) hclosed
  slot_support j := closure_minimal (original.prime_support j t ht) hclosed

theorem literalOriginalSchwartzModel_bound (ξ : X)
    (W : NormProfileRecipe (fun _ : PUnit => data ξ))
    (a : RealParameters) (Z t Y₁ Y₂ : ℝ) (centered : Bool)
    (hZ : 1 < Z) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)
    (reference : HeckeGeneral.Analysis.NonzeroIdeal K)
    (href : (data ξ).allowedRow reference)
    {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
    {heightDomain window : Set ℝ} {seminorms : Finset (ℕ × ℕ)} {bound : ℝ}
    (original : RawProfileWindow rowDomain heightDomain window seminorms (data ξ) bound)
    (hreference : reference ∈ rowDomain) (ht : t ∈ heightDomain)
    (hwindow : window ⊆ Set.Ioi 0) (hclosed : IsClosed window) (hbound : 0 ≤ bound) :
    let E := (HeckeSkeleton.Moments.EngineStepV2.CompleteMovingRowRecipe.literalOriginalSchwartzModel Q) ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      reference href original hreference ht hwindow hclosed
    (∀ r, seminorms.sup (schwartzSeminormFamily ℂ ℝ ℂ) (E.left r) ≤ bound) ∧
      (∀ r, seminorms.sup (schwartzSeminormFamily ℂ ℝ ℂ) (E.right r) ≤ bound) ∧
      (∀ j, seminorms.sup (schwartzSeminormFamily ℂ ℝ ℂ) (E.slot j) ≤ bound) := by
  sorry

end CompleteMovingRowRecipe
end HeckeSkeleton.Moments.EngineStepV2

end

/-!
# The actual Fourier profiles and their computed windows

The representatives below refer to the literal allocated data, with
the actual original scales inside every Fourier phase. Those scales
contribute only constant phases: their logarithms do not enter the
seminorm coefficient. Bounds on the representatives before Fourier
transformation are supplied by the original-profile constructors in
`CanonicalLiteralSchwartzProfiles`, including their displayed scalar
costs. The final raw or clipped window is a return value.
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
open HeckePort.Moments HeckePort.Moments.Support

namespace CanonicalLiteralFourierWindows

def coefficient (window : Set ℝ) (hcompact : IsCompact window)
    (hpositive : window ⊆ Set.Ioi 0) (firstSign : ℝ) (s : Finset (ℕ × ℕ)) : ℝ :=
  CanonicalLogProfiles.shapeCoefficient window hcompact hpositive 0 s *
    (1 + 2 * Real.pi * ‖CanonicalLiteralLocations.direction firstSign‖) ^ (s.sup Prod.snd)

theorem coefficient_nonneg (window : Set ℝ) (hcompact : IsCompact window)
    (hpositive : window ⊆ Set.Ioi 0) (firstSign : ℝ) (s : Finset (ℕ × ℕ)) :
    0 ≤ coefficient window hcompact hpositive firstSign s := by
  sorry

theorem atom_coefficient (window : Set ℝ) (hcompact : IsCompact window)
    (hpositive : window ⊆ Set.Ioi 0) (scale : ℝ) (hscale : 0 < scale)
    (firstSign : ℝ) (negative : Bool) (s : Finset (ℕ × ℕ)) :
    (CanonicalLiteralProfileData.fourierAtom scale hscale firstSign negative).profileCoefficient window hcompact hpositive s =
      coefficient window hcompact hpositive firstSign s := by
  sorry

theorem atom_tsupport {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (p : CanonicalLogProfiles.Atom V) (window : Set ℝ) (hcompact : IsCompact window)
    (hpositive : window ⊆ Set.Ioi 0) (ξ : V) (φ : 𝓢(ℝ, ℂ))
    (hsupport : tsupport φ ⊆ window) :
    tsupport (p.schwartz window hcompact hpositive ξ φ hsupport) ⊆ tsupport φ := by
  sorry

theorem fourier_bound {C B : ℝ} (hC : 0 ≤ C) (hB : 0 ≤ B)
    (J : ℕ) (ξ : WithLp 2 (ℝ × ℝ)) :
    C * (1 + ‖ξ‖) ^ J * B ≤
      polynomialProfileRadius (B * (1 + C)) J J (WithLp.ofLp ξ) := by
  sorry

theorem bound_le_radius {C B : ℝ} (hC : 0 ≤ C) (hB : 0 ≤ B)
    (J : ℕ) (ξ : WithLp 2 (ℝ × ℝ)) :
    B ≤ polynomialProfileRadius (B * (1 + C)) J J (WithLp.ofLp ξ) := by
  sorry

end CanonicalLiteralFourierWindows

variable {K : Type} [Field K] [NumberField K] {k : ℕ}

namespace CanonicalLiteralRectangles.Atoms.ProfileData.SchwartzModel

variable {d : CanonicalLiteralRectangles.Atoms (K := K) k} {W : d.ProfileData}
variable {window : Set ℝ} (E : W.SchwartzModel window)
variable (hcompact : IsCompact window) (hpositive : window ⊆ Set.Ioi 0)
variable (firstSign : ℝ) (negative : Bool)

def leftFourierRep (r : Bool) (ξ : WithLp 2 (ℝ × ℝ)) : 𝓢(ℝ, ℂ) :=
  (CanonicalLiteralProfileData.fourierAtom (d.scale₁ r) (d.scale₁_pos r) firstSign negative).schwartz window hcompact hpositive ξ (E.left r) (E.left_support r)

def rightFourierRep (r : Bool) (ξ : WithLp 2 (ℝ × ℝ)) : 𝓢(ℝ, ℂ) :=
  (CanonicalLiteralProfileData.fourierAtom (d.scale₂ r) (d.scale₂_pos r) firstSign negative).schwartz window hcompact hpositive ξ (E.right r) (E.right_support r)

def slotFourierRep (j : Fin k) (ξ : WithLp 2 (ℝ × ℝ)) : 𝓢(ℝ, ℂ) :=
  (CanonicalLiteralProfileData.fourierAtom (d.base ^ d.length j)
    (Real.rpow_pos_of_pos (zero_lt_one.trans d.base_gt_one) _) firstSign negative).schwartz window hcompact hpositive ξ (E.slot j) (E.slot_support j)

theorem leftFourierRep_eq (r : Bool) (ξ : WithLp 2 (ℝ × ℝ))
    (u : HeckeGeneral.Analysis.NonzeroIdeal K) (t y : ℝ) :
    (W.fourierLeft r firstSign negative ξ).profile u t y =
      E.leftFourierRep hcompact hpositive firstSign negative r ξ y := by
  sorry

theorem rightFourierRep_eq (r : Bool) (ξ : WithLp 2 (ℝ × ℝ))
    (u : HeckeGeneral.Analysis.NonzeroIdeal K) (t y : ℝ) :
    (W.fourierRight r firstSign negative ξ).profile u t y =
      E.rightFourierRep hcompact hpositive firstSign negative r ξ y := by
  sorry

theorem slotFourierRep_eq (j : Fin k) (ξ : WithLp 2 (ℝ × ℝ)) (t y : ℝ) :
    (W.fourierSlot j firstSign negative ξ).profile t y =
      E.slotFourierRep hcompact hpositive firstSign negative j ξ y := by
  sorry

theorem leftFourierRep_support (r : Bool) (ξ : WithLp 2 (ℝ × ℝ)) :
    tsupport (E.leftFourierRep hcompact hpositive firstSign negative r ξ) ⊆ window := by
  sorry

theorem rightFourierRep_support (r : Bool) (ξ : WithLp 2 (ℝ × ℝ)) :
    tsupport (E.rightFourierRep hcompact hpositive firstSign negative r ξ) ⊆ window := by
  sorry

theorem slotFourierRep_support (j : Fin k) (ξ : WithLp 2 (ℝ × ℝ)) :
    tsupport (E.slotFourierRep hcompact hpositive firstSign negative j ξ) ⊆ window := by
  sorry

theorem leftFourierRep_bound (r : Bool) (ξ : WithLp 2 (ℝ × ℝ)) (s : Finset (ℕ × ℕ)) :
    s.sup (schwartzSeminormFamily ℂ ℝ ℂ)
        (E.leftFourierRep hcompact hpositive firstSign negative r ξ) ≤
      CanonicalLiteralFourierWindows.coefficient window hcompact hpositive firstSign s *
        (1 + ‖ξ‖) ^ (s.sup Prod.snd) *
        (CanonicalLogProfiles.sourceOrders s).sup (schwartzSeminormFamily ℂ ℝ ℂ) (E.left r) := by
  sorry

theorem rightFourierRep_bound (r : Bool) (ξ : WithLp 2 (ℝ × ℝ)) (s : Finset (ℕ × ℕ)) :
    s.sup (schwartzSeminormFamily ℂ ℝ ℂ)
        (E.rightFourierRep hcompact hpositive firstSign negative r ξ) ≤
      CanonicalLiteralFourierWindows.coefficient window hcompact hpositive firstSign s *
        (1 + ‖ξ‖) ^ (s.sup Prod.snd) *
        (CanonicalLogProfiles.sourceOrders s).sup (schwartzSeminormFamily ℂ ℝ ℂ) (E.right r) := by
  sorry

theorem slotFourierRep_bound (j : Fin k) (ξ : WithLp 2 (ℝ × ℝ)) (s : Finset (ℕ × ℕ)) :
    s.sup (schwartzSeminormFamily ℂ ℝ ℂ)
        (E.slotFourierRep hcompact hpositive firstSign negative j ξ) ≤
      CanonicalLiteralFourierWindows.coefficient window hcompact hpositive firstSign s *
        (1 + ‖ξ‖) ^ (s.sup Prod.snd) *
        (CanonicalLogProfiles.sourceOrders s).sup (schwartzSeminormFamily ℂ ℝ ℂ) (E.slot j) := by
  sorry

end CanonicalLiteralRectangles.Atoms.ProfileData.SchwartzModel
end HeckeSkeleton.Moments.EngineStepV2

end

/-!
# Raw and clipped windows on the same actual allocated data

The raw constructor uses the computed original Schwartz representatives
and their individual estimates. It fills the profile-window fields of
the literal `CanonicalLiteralAllocatedData.data`; no calibrated data
or finished child window is an input. The unchanged inverse test is
read from the original parent's window.

Clipping is justified by one genuinely nonzero member of this same
family. If the family is zero at every Fourier parameter the existing
zero branch applies instead. The annular dilation constant is explicit
and is put into the common radius before any slot removal.
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
open HeckePort.Moments HeckePort.Moments.Support

namespace CanonicalLiteralAllocatedData

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
variable (remaining extra : HeckeGeneral.Analysis.NonzeroIdeal K) (m q : ℝ)
variable (index : Fin k → Fin parent.geometry.slotCount)
variable (rectangle : Bool) (firstSign : ℝ) (negative : Bool)

local notation "originalData" =>
  data P R W allocation F parent oldMoving correction hcorr C p
    leftMultiplicity rightMultiplicity pattern sector remaining extra m q
    parent.inverseTest index rectangle firstSign negative

variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
variable {heightDomain window : Set ℝ}
variable (E : W.SchwartzModel window)
variable (hcompact : IsCompact window) (hpositive : window ⊆ Set.Ioi 0)
variable (s : Finset (ℕ × ℕ)) {bound : ℝ}

/-- The displayed estimates are on the computed original
representatives. `SchwartzModel.secondInput_*_seminorm_le`, its seed
bound, and its exact atlas/balance transports construct them. -/
def originalRawWindow
    (original : RawProfileWindow rowDomain heightDomain window s parent bound)
    (hbound : 0 ≤ bound)
    (hleft : ∀ r, (CanonicalLogProfiles.sourceOrders s).sup
      (schwartzSeminormFamily ℂ ℝ ℂ) (E.left r) ≤ bound)
    (hright : ∀ r, (CanonicalLogProfiles.sourceOrders s).sup
      (schwartzSeminormFamily ℂ ℝ ℂ) (E.right r) ≤ bound)
    (hslot : ∀ j, (CanonicalLogProfiles.sourceOrders s).sup
      (schwartzSeminormFamily ℂ ℝ ℂ) (E.slot j) ≤ bound)
    (ξ : WithLp 2 (ℝ × ℝ)) :
    RawProfileWindow rowDomain heightDomain window s (originalData ξ)
      (polynomialProfileRadius
        (bound * (1 + CanonicalLiteralFourierWindows.coefficient
          window hcompact hpositive firstSign s)) (s.sup Prod.snd) (s.sup Prod.snd)
        (WithLp.ofLp ξ)) := by
  have hcoefficient := CanonicalLiteralFourierWindows.coefficient_nonneg
    window hcompact hpositive firstSign s
  have hsize := CanonicalLiteralFourierWindows.bound_le_radius
    hcoefficient hbound (s.sup Prod.snd) ξ
  have hfourier := CanonicalLiteralFourierWindows.fourier_bound
    hcoefficient hbound (s.sup Prod.snd) ξ
  have hnonneg : 0 ≤ CanonicalLiteralFourierWindows.coefficient
      window hcompact hpositive firstSign s * (1 + ‖ξ‖) ^ (s.sup Prod.snd) :=
    mul_nonneg hcoefficient (pow_nonneg (by positivity) _)
  refine
    { inverseRep := original.inverseRep
      leftRep := fun _ _ => E.leftFourierRep hcompact hpositive firstSign negative rectangle ξ
      rightRep := fun _ _ => E.rightFourierRep hcompact hpositive firstSign negative rectangle ξ
      primeRep := fun j _ => E.slotFourierRep hcompact hpositive firstSign negative
        (SlotRestriction.index allocation.keep j) ξ
      inverse_eq := original.inverse_eq
      left_eq := fun u t y => E.leftFourierRep_eq
        hcompact hpositive firstSign negative rectangle ξ u t y
      right_eq := fun u t y => E.rightFourierRep_eq
        hcompact hpositive firstSign negative rectangle ξ u t y
      prime_eq := fun j t y => E.slotFourierRep_eq
        hcompact hpositive firstSign negative (SlotRestriction.index allocation.keep j) ξ t y
      inverse_support := original.inverse_support
      left_support := fun _ _ _ _ _ hy =>
        E.leftFourierRep_support hcompact hpositive firstSign negative rectangle ξ
          (subset_tsupport _ hy)
      right_support := fun _ _ _ _ _ hy =>
        E.rightFourierRep_support hcompact hpositive firstSign negative rectangle ξ
          (subset_tsupport _ hy)
      prime_support := fun j _ _ _ hy => E.slotFourierRep_support
        hcompact hpositive firstSign negative (SlotRestriction.index allocation.keep j) ξ
          (subset_tsupport _ hy)
      inverse_bound := fun u hu t ht => (original.inverse_bound u hu t ht).trans hsize
      left_bound := fun _ _ _ _ =>
        (E.leftFourierRep_bound hcompact hpositive firstSign negative rectangle ξ s).trans
          ((mul_le_mul_of_nonneg_left (hleft rectangle) hnonneg).trans hfourier)
      right_bound := fun _ _ _ _ =>
        (E.rightFourierRep_bound hcompact hpositive firstSign negative rectangle ξ s).trans
          ((mul_le_mul_of_nonneg_left (hright rectangle) hnonneg).trans hfourier)
      prime_bound := fun j _ _ =>
        (E.slotFourierRep_bound hcompact hpositive firstSign negative
          (SlotRestriction.index allocation.keep j) ξ s).trans
            ((mul_le_mul_of_nonneg_left
              (hslot (SlotRestriction.index allocation.keep j)) hnonneg).trans hfourier) }

end CanonicalLiteralAllocatedData

namespace CanonicalLiteralFourierWindows

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
variable {heightDomain window window' : Set ℝ} {s : Finset (ℕ × ℕ)}

def enlargeWindow {d : MomentData K ω ψ} {bound : ℝ}
    (w : RawProfileWindow rowDomain heightDomain window s d bound)
    (hwindow : window ⊆ window') :
    RawProfileWindow rowDomain heightDomain window' s d bound :=
  { w with
    inverse_support := fun u hu t ht => (w.inverse_support u hu t ht).trans hwindow
    left_support := fun u hu t ht => (w.left_support u hu t ht).trans hwindow
    right_support := fun u hu t ht => (w.right_support u hu t ht).trans hwindow
    prime_support := fun j t ht => (w.prime_support j t ht).trans hwindow }

/-- A family of already constructed raw representatives is clipped
with one actual nonzero member. The radius and both support windows
are enlarged by explicit constants independent of the Fourier point. -/
def rawClippedWindows
    (family : WithLp 2 (ℝ × ℝ) → MomentData K ω ψ) (parameters : RealParameters)
    (Z time : ℝ) (hZ : 1 < Z) (lo hi : ℝ) (hlo : 0 < lo) (hhi : 1 ≤ hi)
    (s : Finset (ℕ × ℕ)) (B : ℝ) (hB : 0 ≤ B) (J : ℕ)
    (raw : ∀ ξ, RawProfileWindow rowDomain heightDomain (Set.Icc lo hi) s (family ξ)
      (polynomialProfileRadius B J J (WithLp.ofLp ξ)))
    (ξ₀ : WithLp 2 (ℝ × ℝ))
    (hrows : ∀ u ∈ pairedRows (family ξ₀) parameters Z, u ∈ rowDomain)
    (ht : time ∈ heightDomain) (hne : pairedEnergy (family ξ₀) parameters Z time ≠ 0)
    (ξ : WithLp 2 (ℝ × ℝ)) :
    RawProfileWindow rowDomain heightDomain (Set.Icc (lo / hi) hi) s (family ξ)
      (polynomialProfileRadius (CanonicalLogProfiles.clippingCoefficient hi s * (1 + B))
        J J (WithLp.ofLp ξ)) ×
    RawProfileWindow rowDomain heightDomain (Set.Icc (lo / hi) hi) s
      (clipPlainData (family ξ) parameters Z (zero_lt_one.trans hZ))
      (polynomialProfileRadius (CanonicalLogProfiles.clippingCoefficient hi s * (1 + B))
        J J (WithLp.ofLp ξ)) := by
  let Cclip := CanonicalLogProfiles.clippingCoefficient hi s
  have hC : 1 ≤ Cclip := CanonicalLogProfiles.clippingCoefficient_one_le hi hhi s
  have hclip := CanonicalLogProfiles.clipping_factors_le_of_window_nonzero
    (family ξ₀) parameters Z time lo hi hZ hhi s
    (polynomialProfileRadius B J J (WithLp.ofLp ξ₀)) (raw ξ₀) hrows ht hne
  have hrawpos : 0 ≤ polynomialProfileRadius B J J (WithLp.ofLp ξ) :=
    (polynomialProfileRadius_pos B hB J J (WithLp.ofLp ξ)).le
  let clipped := CanonicalLogProfiles.clipRawWindow (family ξ) parameters Z hZ.le lo hi
    hlo hhi s hrawpos (raw ξ) hclip.1 hclip.2
  have henvelope : Cclip * polynomialProfileRadius B J J (WithLp.ofLp ξ) ≤
      polynomialProfileRadius (Cclip * (1 + B)) J J (WithLp.ofLp ξ) := by
    have h := mul_le_mul_of_nonneg_left
      (polynomialProfileRadius_le B J J (WithLp.ofLp ξ)) (zero_le_one.trans hC)
    unfold polynomialProfileRadius at h ⊢
    nlinarith
  have hraw : polynomialProfileRadius B J J (WithLp.ofLp ξ) ≤
      polynomialProfileRadius (Cclip * (1 + B)) J J (WithLp.ofLp ξ) :=
    (le_mul_of_one_le_left hrawpos hC).trans henvelope
  exact ⟨(enlargeWindow (raw ξ)
    (CanonicalLogProfiles.originalAnnulus_subset_clipped lo hi hlo hhi)).mono hraw,
    clipped.mono henvelope⟩

end CanonicalLiteralFourierWindows
end HeckeSkeleton.Moments.EngineStepV2

end

/-!
# Clipping every literal side, including an identically zero side

A zero source need not have a central scale bounded below. Its actual
clipping factor is therefore retained in the normalization radius.
The fixed broad window starts at zero; each actual dilated profile is
still a constructed Schwartz function. On every active side a genuine
nonzero member bounds these same clipping factors by the original
annulus. This proves the uniform active cost and the narrower positive
window without changing any profile, chosen child or Fourier measure.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2

open HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments

namespace CanonicalLiteralAllSideClipping

theorem clippingCoefficient_mono (s : Finset (ℕ × ℕ))
    {c B : ℝ} (hc : 1 ≤ c) (h : c ≤ B) :
    CanonicalLogProfiles.clippingCoefficient c s ≤
      CanonicalLogProfiles.clippingCoefficient B s := by
  sorry

def cost (Z : ℝ) (parameters : RealParameters) (s : Finset (ℕ × ℕ)) : ℝ :=
  1 + CanonicalLogProfiles.clippingCoefficient (plainClippingFactor Z parameters.n₁) s +
    CanonicalLogProfiles.clippingCoefficient (plainClippingFactor Z parameters.n₂) s

theorem cost_bounds (Z : ℝ) (parameters : RealParameters) (hZ : 1 ≤ Z)
    (s : Finset (ℕ × ℕ)) :
    1 ≤ cost Z parameters s ∧
      CanonicalLogProfiles.clippingCoefficient (plainClippingFactor Z parameters.n₁) s ≤
        cost Z parameters s ∧
      CanonicalLogProfiles.clippingCoefficient (plainClippingFactor Z parameters.n₂) s ≤
        cost Z parameters s := by
  sorry

theorem dilation_support (lo hi c : ℝ) (hlo : 0 < lo) (hc : 1 ≤ c)
    (φ : 𝓢(ℝ, ℂ)) (hφ : Function.support φ ⊆ Set.Icc lo hi) :
    Function.support (CanonicalLogProfiles.dilationSchwartz c hc φ) ⊆ Set.Icc 0 hi := by
  sorry

theorem original_support (lo hi : ℝ) (hlo : 0 < lo) :
    Set.Icc lo hi ⊆ Set.Icc 0 hi := by
  sorry

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)} {heightDomain : Set ℝ}

/-- The only cost is the explicitly computed dilation at the same
two original exponents. No nonzero-source premise is needed here. -/
def clipWindow (d : MomentData K ω ψ) (parameters : RealParameters)
    (Z : ℝ) (hZ : 1 ≤ Z) (lo hi : ℝ) (hlo : 0 < lo)
    (s : Finset (ℕ × ℕ)) {B : ℝ} (hB : 0 ≤ B)
    (w : RawProfileWindow rowDomain heightDomain (Set.Icc lo hi) s d B) :
    RawProfileWindow rowDomain heightDomain (Set.Icc 0 hi) s
      (clipPlainData d parameters Z (zero_lt_one.trans_le hZ)) (cost Z parameters s * B) := by
  let c₁ := plainClippingFactor Z parameters.n₁
  let c₂ := plainClippingFactor Z parameters.n₂
  have hc₁ : 1 ≤ c₁ := plainClippingFactor_one_le Z parameters.n₁ hZ
  have hc₂ : 1 ≤ c₂ := plainClippingFactor_one_le Z parameters.n₂ hZ
  have hcost := cost_bounds Z parameters hZ s
  have hBC : B ≤ cost Z parameters s * B := le_mul_of_one_le_left hB hcost.1
  have hleft (φ : 𝓢(ℝ, ℂ)) (hφ : s.sup (schwartzSeminormFamily ℂ ℝ ℂ) φ ≤ B) :
      s.sup (schwartzSeminormFamily ℂ ℝ ℂ)
          (CanonicalLogProfiles.dilationSchwartz c₁ hc₁ φ) ≤ cost Z parameters s * B :=
    (CanonicalLogProfiles.dilationSchwartz_finset_bound c₁ hc₁ s c₁ hc₁ le_rfl φ).trans
      (mul_le_mul hcost.2.1 hφ (apply_nonneg _ _) (zero_le_one.trans hcost.1))
  have hright (φ : 𝓢(ℝ, ℂ)) (hφ : s.sup (schwartzSeminormFamily ℂ ℝ ℂ) φ ≤ B) :
      s.sup (schwartzSeminormFamily ℂ ℝ ℂ)
          (CanonicalLogProfiles.dilationSchwartz c₂ hc₂ φ) ≤ cost Z parameters s * B :=
    (CanonicalLogProfiles.dilationSchwartz_finset_bound c₂ hc₂ s c₂ hc₂ le_rfl φ).trans
      (mul_le_mul hcost.2.2 hφ (apply_nonneg _ _) (zero_le_one.trans hcost.1))
  refine
    { inverseRep := w.inverseRep
      leftRep := fun u t => CanonicalLogProfiles.dilationSchwartz c₁ hc₁ (w.leftRep u t)
      rightRep := fun u t => CanonicalLogProfiles.dilationSchwartz c₂ hc₂ (w.rightRep u t)
      primeRep := w.primeRep
      inverse_eq := w.inverse_eq
      left_eq := ?_
      right_eq := ?_
      prime_eq := w.prime_eq
      inverse_support := fun u hu t ht =>
        (w.inverse_support u hu t ht).trans (original_support lo hi hlo)
      left_support := fun u hu t ht =>
        dilation_support lo hi c₁ hlo hc₁ _ (w.left_support u hu t ht)
      right_support := fun u hu t ht =>
        dilation_support lo hi c₂ hlo hc₂ _ (w.right_support u hu t ht)
      prime_support := fun j t ht => (w.prime_support j t ht).trans (original_support lo hi hlo)
      inverse_bound := fun u hu t ht => (w.inverse_bound u hu t ht).trans hBC
      left_bound := fun u hu t ht => hleft _ (w.left_bound u hu t ht)
      right_bound := fun u hu t ht => hright _ (w.right_bound u hu t ht)
      prime_bound := fun j t ht => (w.prime_bound j t ht).trans hBC }
  · intro u t y
    change (Real.sqrt c₁ : ℂ) * d.plainTest₁.profile u t (c₁ * y) = _
    rw [CanonicalLogProfiles.dilationSchwartz_apply, w.left_eq]
  · intro u t y
    change (Real.sqrt c₂ : ℂ) * d.plainTest₂.profile u t (c₂ * y) = _
    rw [CanonicalLogProfiles.dilationSchwartz_apply, w.right_eq]

/-- Only the support proofs are sharpened on an active family. The
representatives and the previously computed radius are identical. -/
def clipWindowNarrow (d : MomentData K ω ψ) (parameters : RealParameters)
    (Z : ℝ) (hZ : 1 ≤ Z) (lo hi : ℝ) (hlo : 0 < lo) (hhi : 1 ≤ hi)
    (s : Finset (ℕ × ℕ)) {B : ℝ} (hB : 0 ≤ B)
    (w : RawProfileWindow rowDomain heightDomain (Set.Icc lo hi) s d B)
    (hleft : plainClippingFactor Z parameters.n₁ ≤ hi)
    (hright : plainClippingFactor Z parameters.n₂ ≤ hi) :
    RawProfileWindow rowDomain heightDomain (Set.Icc (lo / hi) hi) s
      (clipPlainData d parameters Z (zero_lt_one.trans_le hZ)) (cost Z parameters s * B) :=
  { clipWindow d parameters Z hZ lo hi hlo s hB w with
    inverse_support := fun u hu t ht => (w.inverse_support u hu t ht).trans
      (CanonicalLogProfiles.originalAnnulus_subset_clipped lo hi hlo hhi)
    left_support := fun u hu t ht => CanonicalLogProfiles.dilationSchwartz_support
      lo hi hlo hhi _ (plainClippingFactor_one_le Z parameters.n₁ hZ) hleft _
      (w.left_support u hu t ht)
    right_support := fun u hu t ht => CanonicalLogProfiles.dilationSchwartz_support
      lo hi hlo hhi _ (plainClippingFactor_one_le Z parameters.n₂ hZ) hright _
      (w.right_support u hu t ht)
    prime_support := fun j t ht => (w.prime_support j t ht).trans
      (CanonicalLogProfiles.originalAnnulus_subset_clipped lo hi hlo hhi) }

theorem cost_le_of_factors (Z : ℝ) (parameters : RealParameters) (hZ : 1 ≤ Z)
    (hi : ℝ) (s : Finset (ℕ × ℕ))
    (hleft : plainClippingFactor Z parameters.n₁ ≤ hi)
    (hright : plainClippingFactor Z parameters.n₂ ≤ hi) :
    cost Z parameters s ≤ 1 + 2 * CanonicalLogProfiles.clippingCoefficient hi s := by
  sorry

/-- The active clipping cost is bounded from the actual nonzero
energy and the original annulus, without a final profile bound. -/
theorem cost_le_of_nonzero (d : MomentData K ω ψ) (parameters : RealParameters)
    (Z time lo hi : ℝ) (hZ : 1 < Z) (hhi : 1 ≤ hi)
    (s : Finset (ℕ × ℕ)) (B : ℝ)
    (w : RawProfileWindow rowDomain heightDomain (Set.Icc lo hi) s d B)
    (hrows : ∀ u ∈ pairedRows d parameters Z, u ∈ rowDomain)
    (ht : time ∈ heightDomain) (hne : pairedEnergy d parameters Z time ≠ 0) :
    cost Z parameters s ≤ 1 + 2 * CanonicalLogProfiles.clippingCoefficient hi s := by
  sorry

/-- A polynomial radius for every side. Active sides later use
`cost_le_of_nonzero`; inactive sides never enter the kernel carrier. -/
def familyWindows
    (family : WithLp 2 (ℝ × ℝ) → MomentData K ω ψ) (parameters : RealParameters)
    (Z : ℝ) (hZ : 1 ≤ Z) (lo hi : ℝ) (hlo : 0 < lo)
    (s : Finset (ℕ × ℕ)) (B : ℝ) (hB : 0 ≤ B) (J : ℕ)
    (raw : ∀ ξ, RawProfileWindow rowDomain heightDomain (Set.Icc lo hi) s (family ξ)
      (polynomialProfileRadius B J J (WithLp.ofLp ξ)))
    (ξ : WithLp 2 (ℝ × ℝ)) :
    RawProfileWindow rowDomain heightDomain (Set.Icc 0 hi) s (family ξ)
      (polynomialProfileRadius (cost Z parameters s * (1 + B)) J J (WithLp.ofLp ξ)) ×
    RawProfileWindow rowDomain heightDomain (Set.Icc 0 hi) s
      (clipPlainData (family ξ) parameters Z (zero_lt_one.trans_le hZ))
      (polynomialProfileRadius (cost Z parameters s * (1 + B)) J J (WithLp.ofLp ξ)) := by
  have hC := (cost_bounds Z parameters hZ s).1
  have hrawpos := (polynomialProfileRadius_pos B hB J J (WithLp.ofLp ξ)).le
  have henvelope : cost Z parameters s * polynomialProfileRadius B J J (WithLp.ofLp ξ) ≤
      polynomialProfileRadius (cost Z parameters s * (1 + B)) J J (WithLp.ofLp ξ) := by
    have h := mul_le_mul_of_nonneg_left
      (polynomialProfileRadius_le B J J (WithLp.ofLp ξ)) (zero_le_one.trans hC)
    unfold polynomialProfileRadius at h ⊢
    nlinarith
  refine ⟨?_, (clipWindow (family ξ) parameters Z hZ lo hi hlo s hrawpos (raw ξ)).mono henvelope⟩
  exact (CanonicalLiteralFourierWindows.enlargeWindow (raw ξ) (original_support lo hi hlo)).mono
    ((le_mul_of_one_le_left hrawpos hC).trans henvelope)

end CanonicalLiteralAllSideClipping
end HeckeSkeleton.Moments.EngineStepV2

end

/-!
# The original Fourier window of one actual rectangle

Only the two profiles selected by this side's actual rectangle enter
its normalization radius. The unused ordinary comparison rectangle
may have arbitrary central scales; its zero coefficient does not
justify charging those scales to the active rectangle.

All representatives are those constructed from the original tests.
This is the selected-rectangle version of the literal raw constructor;
the data, slots, phases, inverse test and Fourier measure are unchanged.
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
open HeckePort.Moments HeckePort.Moments.Support

namespace CanonicalLiteralAllocatedData

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
variable (remaining extra : HeckeGeneral.Analysis.NonzeroIdeal K) (m q : ℝ)
variable (index : Fin k → Fin parent.geometry.slotCount)
variable (rectangle : Bool) (firstSign : ℝ) (negative : Bool)

local notation "originalData" =>
  data P R W allocation F parent oldMoving correction hcorr C p
    leftMultiplicity rightMultiplicity pattern sector remaining extra m q
    parent.inverseTest index rectangle firstSign negative

variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
variable {heightDomain window : Set ℝ}
variable (E : W.SchwartzModel window)
variable (hcompact : IsCompact window) (hpositive : window ⊆ Set.Ioi 0)
variable (s : Finset (ℕ × ℕ)) {bound : ℝ}

/-- The displayed estimates are on the computed original
representatives. `SchwartzModel.secondInput_*_seminorm_le`, its seed
bound, and its exact atlas/balance transports construct them. -/
def selectedRawWindow
    (original : RawProfileWindow rowDomain heightDomain window s parent bound)
    (hbound : 0 ≤ bound)
    (hleft : (CanonicalLogProfiles.sourceOrders s).sup
      (schwartzSeminormFamily ℂ ℝ ℂ) (E.left rectangle) ≤ bound)
    (hright : (CanonicalLogProfiles.sourceOrders s).sup
      (schwartzSeminormFamily ℂ ℝ ℂ) (E.right rectangle) ≤ bound)
    (hslot : ∀ j, (CanonicalLogProfiles.sourceOrders s).sup
      (schwartzSeminormFamily ℂ ℝ ℂ) (E.slot j) ≤ bound)
    (ξ : WithLp 2 (ℝ × ℝ)) :
    RawProfileWindow rowDomain heightDomain window s (originalData ξ)
      (polynomialProfileRadius
        (bound * (1 + CanonicalLiteralFourierWindows.coefficient
          window hcompact hpositive firstSign s)) (s.sup Prod.snd) (s.sup Prod.snd)
        (WithLp.ofLp ξ)) := by
  have hcoefficient := CanonicalLiteralFourierWindows.coefficient_nonneg
    window hcompact hpositive firstSign s
  have hsize := CanonicalLiteralFourierWindows.bound_le_radius
    hcoefficient hbound (s.sup Prod.snd) ξ
  have hfourier := CanonicalLiteralFourierWindows.fourier_bound
    hcoefficient hbound (s.sup Prod.snd) ξ
  have hnonneg : 0 ≤ CanonicalLiteralFourierWindows.coefficient
      window hcompact hpositive firstSign s * (1 + ‖ξ‖) ^ (s.sup Prod.snd) :=
    mul_nonneg hcoefficient (pow_nonneg (by positivity) _)
  refine
    { inverseRep := original.inverseRep
      leftRep := fun _ _ => E.leftFourierRep hcompact hpositive firstSign negative rectangle ξ
      rightRep := fun _ _ => E.rightFourierRep hcompact hpositive firstSign negative rectangle ξ
      primeRep := fun j _ => E.slotFourierRep hcompact hpositive firstSign negative
        (SlotRestriction.index allocation.keep j) ξ
      inverse_eq := original.inverse_eq
      left_eq := fun u t y => E.leftFourierRep_eq
        hcompact hpositive firstSign negative rectangle ξ u t y
      right_eq := fun u t y => E.rightFourierRep_eq
        hcompact hpositive firstSign negative rectangle ξ u t y
      prime_eq := fun j t y => E.slotFourierRep_eq
        hcompact hpositive firstSign negative (SlotRestriction.index allocation.keep j) ξ t y
      inverse_support := original.inverse_support
      left_support := fun _ _ _ _ _ hy =>
        E.leftFourierRep_support hcompact hpositive firstSign negative rectangle ξ
          (subset_tsupport _ hy)
      right_support := fun _ _ _ _ _ hy =>
        E.rightFourierRep_support hcompact hpositive firstSign negative rectangle ξ
          (subset_tsupport _ hy)
      prime_support := fun j _ _ _ hy => E.slotFourierRep_support
        hcompact hpositive firstSign negative (SlotRestriction.index allocation.keep j) ξ
          (subset_tsupport _ hy)
      inverse_bound := fun u hu t ht => (original.inverse_bound u hu t ht).trans hsize
      left_bound := fun _ _ _ _ =>
        (E.leftFourierRep_bound hcompact hpositive firstSign negative rectangle ξ s).trans
          ((mul_le_mul_of_nonneg_left hleft hnonneg).trans hfourier)
      right_bound := fun _ _ _ _ =>
        (E.rightFourierRep_bound hcompact hpositive firstSign negative rectangle ξ s).trans
          ((mul_le_mul_of_nonneg_left hright hnonneg).trans hfourier)
      prime_bound := fun j _ _ =>
        (E.slotFourierRep_bound hcompact hpositive firstSign negative
          (SlotRestriction.index allocation.keep j) ξ s).trans
            ((mul_le_mul_of_nonneg_left
              (hslot (SlotRestriction.index allocation.keep j)) hnonneg).trans hfourier) }

end CanonicalLiteralAllocatedData
end HeckeSkeleton.Moments.EngineStepV2

end

/-!
# Quantitative profiles after exact scalar extraction and balancing

The atom table is scaled by the inverse of its actual first common and
pool scalar, then balanced by positive reciprocal plain factors. The
two operations are the literal existing atom constructors. Even when
the extracted scalar is zero these representatives exist; its inverse
is then zero and the left profile vanishes. On a live source the
nonzero scalar is transferred to the original row weight separately.

The remaining seminorm costs contain the product of the two true plain
scale factors. Neither the removed complex scalar nor the ratio of the
centered scales enters their common normalization radius.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2

open HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments HeckePort.Moments.Support

variable {K : Type} [Field K] [NumberField K] {k : ℕ}

namespace CanonicalLiteralBalancedSchwartz

variable (d : CanonicalLiteralRectangles.Atoms (K := K) k)
variable {support : Finset (Ideal (𝓞 K))}
variable (b : SupportCartesianBranch d.plain₁ d.plain₂ d.slots support)

def leftFactor (δ₁ δ₂ : ℝ) (r : Bool) : ℝ :=
  CanonicalLiteralProfileScalars.plainFactor
    ((d.extract b).scale₁ false) ((d.extract b).scale₁ r) δ₁ δ₂

def rightFactor (δ₁ δ₂ : ℝ) (r : Bool) : ℝ :=
  CanonicalLiteralProfileScalars.plainFactor
    ((d.extract b).scale₂ false) ((d.extract b).scale₂ r) δ₁ δ₂

theorem leftFactor_pos (δ₁ δ₂ : ℝ) (r : Bool) : 0 < leftFactor d b δ₁ δ₂ r := by
  sorry

theorem rightFactor_pos (δ₁ δ₂ : ℝ) (r : Bool) : 0 < rightFactor d b δ₁ δ₂ r := by
  sorry

def balance (δ₁ δ₂ : ℝ) (r : Bool) : ℝ :=
  CanonicalLiteralPlainBalance.ratio (leftFactor d b δ₁ δ₂ r) (rightFactor d b δ₁ δ₂ r)

theorem balance_pos (δ₁ δ₂ : ℝ) (r : Bool) : 0 < balance d b δ₁ δ₂ r := by
  sorry

def factor (δ₁ δ₂ : ℝ) (r : Bool) : ℝ :=
  Real.sqrt (leftFactor d b δ₁ δ₂ r * rightFactor d b δ₁ δ₂ r)

theorem left_mul_balance (δ₁ δ₂ : ℝ) (r : Bool) :
    leftFactor d b δ₁ δ₂ r * balance d b δ₁ δ₂ r = factor d b δ₁ δ₂ r := by
  sorry

theorem right_mul_balance_inv (δ₁ δ₂ : ℝ) (r : Bool) :
    rightFactor d b δ₁ δ₂ r * (balance d b δ₁ δ₂ r)⁻¹ = factor d b δ₁ δ₂ r := by
  sorry

/-- An active rectangle's actual ideal lower bounds give the lower
product window. This estimate then uses only the original annulus and
fixed tilt exponents. -/
theorem factor_le (δ₁ δ₂ hi : ℝ) (r : Bool) (hhi : 1 ≤ hi)
    (hδlo : 0 ≤ δ₁ + δ₂) (hδhi : δ₁ + δ₂ ≤ 1 / 2)
    (hproduct : d.scale₁ r * d.scale₂ r = d.scale₁ false * d.scale₂ false)
    (hlower : hi ^ (-2 : ℝ) ≤ (d.extract b).scale₁ false * (d.extract b).scale₂ false) :
    factor d b δ₁ δ₂ r ≤ Real.sqrt hi := by
  sorry

theorem slotFactor_le_one (δ₁ δ₂ : ℝ) (j : Fin b.keep.card)
    (hδhi : δ₁ + δ₂ ≤ 1 / 2) :
    CanonicalLiteralProfileScalars.plainFactor
      ((d.extract b).base ^ (d.extract b).length j)
      ((d.extract b).base ^ (d.extract b).length j) δ₁ δ₂ ≤ 1 := by
  sorry

theorem norm_inv_mul_self_le_one (c : ℂ) : ‖c⁻¹ * c‖ ≤ 1 := by
  sorry

end CanonicalLiteralBalancedSchwartz

namespace CanonicalLiteralRectangles.Atoms.ProfileData.SchwartzModel

variable {d : CanonicalLiteralRectangles.Atoms (K := K) k} {W : d.ProfileData}
variable {window : Set ℝ} (E : W.SchwartzModel window)

def scale (c : ℂ) : (W.scale c).SchwartzModel window where
  left r := c • E.left r
  right := E.right
  slot := E.slot
  left_eq r u t y := by
    change (W.left r).profile u t y * c = c * E.left r y
    rw [E.left_eq]
    ring
  right_eq := E.right_eq
  slot_eq := E.slot_eq
  left_support r := (tsupport_smul_subset_right (fun _ : ℝ => c) (E.left r)).trans
    (E.left_support r)
  right_support := E.right_support
  slot_support := E.slot_support

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
local notation "balance" => CanonicalLiteralBalancedSchwartz.balance d b δ₁ δ₂
local notation "factor" => CanonicalLiteralBalancedSchwartz.factor d b δ₁ δ₂
local notation "transformed" => W.secondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
  firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂

/-- The scalar-free balanced table is exactly `secondInput.scale
outer⁻¹` followed by the positive reciprocal plain balance. -/
def scalarFreeBalancedSecondInput (hcompact : IsCompact window)
    (hpositive : window ⊆ Set.Ioi 0) :
    (((transformed).scale outer⁻¹).balancePlain balance).SchwartzModel window := by
  apply (E.extract b).powerProfiles (((transformed).scale outer⁻¹).balancePlain balance)
    hcompact hpositive (CanonicalLiteralProfileScalars.exponent δ₁ δ₂)
    (fun r => (outer⁻¹ * outer) * (factor r : ℂ))
    (fun r => (factor r : ℂ))
    (fun j => (CanonicalLiteralProfileScalars.plainFactor
      ((d.extract b).base ^ (d.extract b).length j)
      ((d.extract b).base ^ (d.extract b).length j) δ₁ δ₂ : ℂ))
  · intro r u t y hy
    change (((transformed).left r).profile u t y * outer⁻¹) * (balance r : ℂ) = _
    rw [W.secondInput_left_shape (σ := σ) b P R power firstFixed poolFixed unitFixed
      firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂ r u t hy]
    calc
      _ = (outer⁻¹ * outer) *
          ((CanonicalLiteralBalancedSchwartz.leftFactor d b δ₁ δ₂ r * balance r : ℝ) : ℂ) *
          ((W.left r).profile u t y *
            ((y ^ CanonicalLiteralProfileScalars.exponent δ₁ δ₂ : ℝ) : ℂ)) := by
        simp only [Complex.ofReal_mul, CanonicalLiteralBalancedSchwartz.leftFactor]
        ring
      _ = _ := by rw [CanonicalLiteralBalancedSchwartz.left_mul_balance] <;> rfl
  · intro r u t y hy
    change ((transformed).right r).profile u t y * (balance r : ℂ)⁻¹ = _
    rw [W.secondInput_right_shape (σ := σ) b P R power firstFixed poolFixed unitFixed
      firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂ r u t hy]
    calc
      _ = ((CanonicalLiteralBalancedSchwartz.rightFactor d b δ₁ δ₂ r *
          (balance r)⁻¹ : ℝ) : ℂ) * ((W.right r).profile u t y *
            ((y ^ CanonicalLiteralProfileScalars.exponent δ₁ δ₂ : ℝ) : ℂ)) := by
        simp only [Complex.ofReal_mul, Complex.ofReal_inv, CanonicalLiteralBalancedSchwartz.rightFactor]
        ring
      _ = _ := by rw [CanonicalLiteralBalancedSchwartz.right_mul_balance_inv] <;> rfl
  · intro j t y hy
    exact W.secondInput_slot_shape (σ := σ) b P R power firstFixed poolFixed unitFixed
      firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂ j t hy

theorem scalarFreeBalanced_left_bound (hcompact : IsCompact window)
    (hpositive : window ⊆ Set.Ioi 0) (r : Bool) (s : Finset (ℕ × ℕ)) :
    s.sup (schwartzSeminormFamily ℂ ℝ ℂ)
      ((E.scalarFreeBalancedSecondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
        firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂ hcompact hpositive).left r) ≤
      factor r * CanonicalLogProfiles.shapeCoefficient window hcompact hpositive
        (CanonicalLiteralProfileScalars.exponent δ₁ δ₂) s *
        (CanonicalLogProfiles.sourceOrders s).sup (schwartzSeminormFamily ℂ ℝ ℂ) (E.left r) := by
  sorry

theorem scalarFreeBalanced_right_bound (hcompact : IsCompact window)
    (hpositive : window ⊆ Set.Ioi 0) (r : Bool) (s : Finset (ℕ × ℕ)) :
    s.sup (schwartzSeminormFamily ℂ ℝ ℂ)
      ((E.scalarFreeBalancedSecondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
        firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂ hcompact hpositive).right r) ≤
      factor r * CanonicalLogProfiles.shapeCoefficient window hcompact hpositive
        (CanonicalLiteralProfileScalars.exponent δ₁ δ₂) s *
        (CanonicalLogProfiles.sourceOrders s).sup (schwartzSeminormFamily ℂ ℝ ℂ) (E.right r) := by
  sorry

theorem scalarFreeBalanced_slot_bound (hcompact : IsCompact window)
    (hpositive : window ⊆ Set.Ioi 0) (j : Fin b.keep.card) (s : Finset (ℕ × ℕ))
    (hδhi : δ₁ + δ₂ ≤ 1 / 2) :
    s.sup (schwartzSeminormFamily ℂ ℝ ℂ)
      ((E.scalarFreeBalancedSecondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
        firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂ hcompact hpositive).slot j) ≤
      CanonicalLogProfiles.shapeCoefficient window hcompact hpositive
        (CanonicalLiteralProfileScalars.exponent δ₁ δ₂) s *
        (CanonicalLogProfiles.sourceOrders s).sup (schwartzSeminormFamily ℂ ℝ ℂ)
          (E.slot (SlotRestriction.index b.keep j)) := by
  sorry

end CanonicalLiteralRectangles.Atoms.ProfileData.SchwartzModel
end HeckeSkeleton.Moments.EngineStepV2

end

/-!
# The original prime window through the literal construction

The prime profiles retain their original function support. Real-power
multipliers and Fourier phases cannot create a nonzero value where the
original profile vanishes. The actual extraction and atlas operations
select the original occurrences; plain balancing and clipping leave
the prime profiles unchanged. In particular the original open prime
window `(1, 2)` is available to the full-kappa single-slot estimate,
even though the common plain-profile window is enlarged by clipping.
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
open HeckePort.Moments HeckePort.Moments.Support

namespace CanonicalLiteralSchwartzProfiles

theorem powerSchwartz_support_subset (window : Set ℝ) (hcompact : IsCompact window)
    (hpositive : window ⊆ Set.Ioi 0) (c : ℂ) (exponent : ℝ)
    (φ : 𝓢(ℝ, ℂ)) (hsupport : tsupport φ ⊆ window) :
    Function.support (powerSchwartz window hcompact hpositive c exponent φ hsupport) ⊆
      Function.support φ := by
  sorry

end CanonicalLiteralSchwartzProfiles

namespace CanonicalLiteralFourierWindows

theorem atom_support {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (p : CanonicalLogProfiles.Atom V) (window : Set ℝ) (hcompact : IsCompact window)
    (hpositive : window ⊆ Set.Ioi 0) (ξ : V) (φ : 𝓢(ℝ, ℂ))
    (hsupport : tsupport φ ⊆ window) :
    Function.support (p.schwartz window hcompact hpositive ξ φ hsupport) ⊆
      Function.support φ := by
  sorry

end CanonicalLiteralFourierWindows

variable {K : Type} [Field K] [NumberField K] {k : ℕ}

namespace CanonicalLiteralRectangles.Atoms.ProfileData.SchwartzModel

variable {d : CanonicalLiteralRectangles.Atoms (K := K) k} {W : d.ProfileData}
variable {window target : Set ℝ} (E : W.SchwartzModel window)

theorem extract_prime_support {support : Finset (Ideal (𝓞 K))}
    (b : SupportCartesianBranch d.plain₁ d.plain₂ d.slots support)
    (hprime : ∀ j, Function.support (E.slot j) ⊆ target) :
    ∀ j, Function.support ((E.extract b).slot j) ⊆ target := by
  sorry

theorem onAtlas_prime_support {A : SArithmeticData K} {ι : Type*}
    {columns : Finset ι} {ideal : ι → A.Exterior}
    (T : SourceCartesianAtlas columns ideal) (count : k = T.slotCount)
    (hprime : ∀ j, Function.support (E.slot j) ⊆ target) :
    ∀ j, Function.support ((E.onAtlas T count).slot j) ⊆ target := by
  sorry

theorem deleteMask_prime_support (M : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hprime : ∀ j, Function.support (E.slot j) ⊆ target) :
    ∀ j, Function.support ((E.deleteMask M).slot j) ⊆ target := by
  sorry

theorem scale_prime_support (c : ℂ)
    (hprime : ∀ j, Function.support (E.slot j) ⊆ target) :
    ∀ j, Function.support ((E.scale c).slot j) ⊆ target := by
  sorry

theorem balancePlain_prime_support (c : Bool → ℝ)
    (hprime : ∀ j, Function.support (E.slot j) ⊆ target) :
    ∀ j, Function.support ((E.balancePlain c).slot j) ⊆ target := by
  sorry

theorem slotFourierRep_support_subset (hcompact : IsCompact window)
    (hpositive : window ⊆ Set.Ioi 0) (firstSign : ℝ) (negative : Bool)
    (j : Fin k) (ξ : WithLp 2 (ℝ × ℝ)) :
    Function.support (E.slotFourierRep hcompact hpositive firstSign negative j ξ) ⊆
      Function.support (E.slot j) := by
  sorry

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

theorem secondInput_prime_support (hcompact : IsCompact window)
    (hpositive : window ⊆ Set.Ioi 0)
    (hprime : ∀ j, Function.support (E.slot j) ⊆ target) :
    ∀ j, Function.support
      ((E.secondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
        firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂ hcompact hpositive).slot j)
      ⊆ target := by
  sorry

/-- This is the representative used after moving the actual scalar
to the row weight and balancing the two original plain factors. Its
prime profile is the same real-power transform as before. -/
theorem scalarFreeBalancedSecondInput_prime_support (hcompact : IsCompact window)
    (hpositive : window ⊆ Set.Ioi 0)
    (hprime : ∀ j, Function.support (E.slot j) ⊆ target) :
    ∀ j, Function.support
      ((E.scalarFreeBalancedSecondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
        firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂ hcompact hpositive).slot j)
      ⊆ target := by
  sorry

end CanonicalLiteralRectangles.Atoms.ProfileData.SchwartzModel

namespace CanonicalLiteralAllocatedData

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
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
variable {heightDomain window target : Set ℝ}
variable (E : W.SchwartzModel window)
variable (hcompact : IsCompact window) (hpositive : window ⊆ Set.Ioi 0)
variable (s : Finset (ℕ × ℕ)) {bound : ℝ}

/-- The returned raw window uses the Fourier transform of the same
retained slot. Taking `target = Set.Ioo 1 2` supplies precisely the
prime-support field of `FullKappaProfileInput`. -/
theorem selectedRawWindow_prime_support
    (original : RawProfileWindow rowDomain heightDomain window s parent bound)
    (hbound : 0 ≤ bound)
    (hleft : (CanonicalLogProfiles.sourceOrders s).sup
      (schwartzSeminormFamily ℂ ℝ ℂ) (E.left rectangle) ≤ bound)
    (hright : (CanonicalLogProfiles.sourceOrders s).sup
      (schwartzSeminormFamily ℂ ℝ ℂ) (E.right rectangle) ≤ bound)
    (hslot : ∀ j, (CanonicalLogProfiles.sourceOrders s).sup
      (schwartzSeminormFamily ℂ ℝ ℂ) (E.slot j) ≤ bound)
    (hprime : ∀ j, Function.support (E.slot j) ⊆ target)
    (ξ : WithLp 2 (ℝ × ℝ)) (j : Fin allocation.keep.card) (t : ℝ) :
    Function.support
      ((selectedRawWindow P R W allocation F parent oldMoving correction hcorr C p
        leftMultiplicity rightMultiplicity pattern sector remaining extra m q index
        rectangle firstSign negative E hcompact hpositive s original hbound hleft hright hslot ξ).primeRep j t) ⊆ target := by
  sorry

end CanonicalLiteralAllocatedData

namespace CanonicalLiteralAllSideClipping

variable {ω ψ : HeckeCharacter K}
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
variable {heightDomain target : Set ℝ}

/-- Neither the broad window nor either clipping dilation changes
the returned prime representative. This applies to every rectangle,
including identically zero rectangles. -/
theorem familyWindows_prime_support
    (family : WithLp 2 (ℝ × ℝ) → MomentData K ω ψ) (parameters : RealParameters)
    (Z : ℝ) (hZ : 1 ≤ Z) (lo hi : ℝ) (hlo : 0 < lo)
    (s : Finset (ℕ × ℕ)) (B : ℝ) (hB : 0 ≤ B) (J : ℕ)
    (raw : ∀ ξ, RawProfileWindow rowDomain heightDomain (Set.Icc lo hi) s (family ξ)
      (polynomialProfileRadius B J J (WithLp.ofLp ξ)))
    (hprime : ∀ ξ j t, Function.support ((raw ξ).primeRep j t) ⊆ target)
    (ξ : WithLp 2 (ℝ × ℝ)) (j : Fin (family ξ).geometry.slotCount) (t : ℝ) :
    Function.support
      ((familyWindows family parameters Z hZ lo hi hlo s B hB J raw ξ).1.primeRep j t) ⊆ target ∧
    Function.support
      ((familyWindows family parameters Z hZ lo hi hlo s B hB J raw ξ).2.primeRep j t) ⊆ target := by
  sorry

end CanonicalLiteralAllSideClipping
end HeckeSkeleton.Moments.EngineStepV2

end

/-!
# The original inverse test on every actual child row

`NormProfileRecipe` controls the two plain tests, not the inverse test.
We therefore do not claim that an arbitrary original inverse profile
is independent of its row. The paired source does not use that test.
Before its calibration and normalized children are chosen, its unused
inverse test is fixed to the original test at the same original row
and time that supplied the literal profiles.

The resulting raw window is proved on all rows and all heights from
that one original representative and the computed Fourier profiles.
No bound on a newly generated row, profile family, or child is assumed.
All clipping and radius constructors can consume this returned window
without any further change of data.
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
open HeckePort.Moments HeckePort.Moments.Support

namespace CanonicalLiteralAllocatedData

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
variable (remaining extra : HeckeGeneral.Analysis.NonzeroIdeal K) (m q : ℝ)
variable (index : Fin k → Fin parent.geometry.slotCount)
variable (rectangle : Bool) (firstSign : ℝ) (negative : Bool)

local notation "allocated" =>
  data P R W allocation F parent oldMoving correction hcorr C p
    leftMultiplicity rightMultiplicity pattern sector remaining extra m q

/-- The original paired polynomial and row enumeration are independent
of this unused test. This equality precedes all normalization choices. -/
theorem data_pairedEnergy_inverse (inverse₁ inverse₂ : IdealTest K)
    (a : RealParameters) (Z t : ℝ) (ξ : WithLp 2 (ℝ × ℝ)) :
    pairedEnergy (allocated inverse₁ index rectangle firstSign negative ξ) a Z t =
      pairedEnergy (allocated inverse₂ index rectangle firstSign negative ξ) a Z t := rfl

variable (reference : HeckeGeneral.Analysis.NonzeroIdeal K) (time : ℝ)
variable {originalRows : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
variable {originalHeights window : Set ℝ}
variable {originalOrders : Finset (ℕ × ℕ)} {originalBound : ℝ}
variable (original : RawProfileWindow originalRows originalHeights window originalOrders
  parent originalBound)
variable (hreference : reference ∈ originalRows) (htime : time ∈ originalHeights)
variable (E : W.SchwartzModel window)
variable (hcompact : IsCompact window) (hpositive : window ⊆ Set.Ioi 0)
variable (s : Finset (ℕ × ℕ)) (horders : s ⊆ originalOrders)
variable {bound : ℝ} (hbound : 0 ≤ bound) (horiginalBound : originalBound ≤ bound)
variable (hleft : (CanonicalLogProfiles.sourceOrders s).sup
  (schwartzSeminormFamily ℂ ℝ ℂ) (E.left rectangle) ≤ bound)
variable (hright : (CanonicalLogProfiles.sourceOrders s).sup
  (schwartzSeminormFamily ℂ ℝ ℂ) (E.right rectangle) ≤ bound)
variable (hslot : ∀ j, (CanonicalLogProfiles.sourceOrders s).sup
  (schwartzSeminormFamily ℂ ℝ ℂ) (E.slot j) ≤ bound)

local notation "frozenInverse" =>
  CanonicalLiteralProfileData.frozenNormTest parent.inverseTest reference time

/-- The same literal Fourier profiles, with the original inverse test
fixed before constructing the actual calibration. The returned domain
is all rows and all heights, including height zero. -/
def frozenInverseRawWindow (ξ : WithLp 2 (ℝ × ℝ)) :
    RawProfileWindow Set.univ Set.univ window s
      (allocated frozenInverse index rectangle firstSign negative ξ)
      (polynomialProfileRadius
        (bound * (1 + CanonicalLiteralFourierWindows.coefficient
          window hcompact hpositive firstSign s)) (s.sup Prod.snd) (s.sup Prod.snd)
        (WithLp.ofLp ξ)) := by
  have hcoefficient := CanonicalLiteralFourierWindows.coefficient_nonneg
    window hcompact hpositive firstSign s
  have hsize := CanonicalLiteralFourierWindows.bound_le_radius
    hcoefficient hbound (s.sup Prod.snd) ξ
  have hfourier := CanonicalLiteralFourierWindows.fourier_bound
    hcoefficient hbound (s.sup Prod.snd) ξ
  have hnonneg : 0 ≤ CanonicalLiteralFourierWindows.coefficient
      window hcompact hpositive firstSign s * (1 + ‖ξ‖) ^ (s.sup Prod.snd) :=
    mul_nonneg hcoefficient (pow_nonneg (by positivity) _)
  have hinverse : s.sup (schwartzSeminormFamily ℂ ℝ ℂ)
      (original.inverseRep reference time) ≤ bound := by
    have hmono : s.sup (schwartzSeminormFamily ℂ ℝ ℂ)
        (original.inverseRep reference time) ≤
        originalOrders.sup (schwartzSeminormFamily ℂ ℝ ℂ)
          (original.inverseRep reference time) :=
      Seminorm.finset_sup_apply_le (apply_nonneg _ _)
        (fun j hj => Seminorm.le_finset_sup_apply (horders hj))
    exact hmono.trans
      ((original.inverse_bound reference hreference time htime).trans horiginalBound)
  refine
    { inverseRep := fun _ _ => original.inverseRep reference time
      leftRep := fun _ _ => E.leftFourierRep hcompact hpositive firstSign negative rectangle ξ
      rightRep := fun _ _ => E.rightFourierRep hcompact hpositive firstSign negative rectangle ξ
      primeRep := fun j _ => E.slotFourierRep hcompact hpositive firstSign negative
        (SlotRestriction.index allocation.keep j) ξ
      inverse_eq := fun _ _ y => original.inverse_eq reference time y
      left_eq := fun u t y => E.leftFourierRep_eq
        hcompact hpositive firstSign negative rectangle ξ u t y
      right_eq := fun u t y => E.rightFourierRep_eq
        hcompact hpositive firstSign negative rectangle ξ u t y
      prime_eq := fun j t y => E.slotFourierRep_eq
        hcompact hpositive firstSign negative (SlotRestriction.index allocation.keep j) ξ t y
      inverse_support := fun _ _ _ _ => original.inverse_support reference hreference time htime
      left_support := fun _ _ _ _ _ hy =>
        E.leftFourierRep_support hcompact hpositive firstSign negative rectangle ξ
          (subset_tsupport _ hy)
      right_support := fun _ _ _ _ _ hy =>
        E.rightFourierRep_support hcompact hpositive firstSign negative rectangle ξ
          (subset_tsupport _ hy)
      prime_support := fun j _ _ _ hy => E.slotFourierRep_support
        hcompact hpositive firstSign negative (SlotRestriction.index allocation.keep j) ξ
          (subset_tsupport _ hy)
      inverse_bound := fun _ _ _ _ => hinverse.trans hsize
      left_bound := fun _ _ _ _ =>
        (E.leftFourierRep_bound hcompact hpositive firstSign negative rectangle ξ s).trans
          ((mul_le_mul_of_nonneg_left hleft hnonneg).trans hfourier)
      right_bound := fun _ _ _ _ =>
        (E.rightFourierRep_bound hcompact hpositive firstSign negative rectangle ξ s).trans
          ((mul_le_mul_of_nonneg_left hright hnonneg).trans hfourier)
      prime_bound := fun j _ _ =>
        (E.slotFourierRep_bound hcompact hpositive firstSign negative
          (SlotRestriction.index allocation.keep j) ξ s).trans
            ((mul_le_mul_of_nonneg_left
              (hslot (SlotRestriction.index allocation.keep j)) hnonneg).trans hfourier) }

theorem frozenInverseRawWindow_prime_support {target : Set ℝ}
    (hprime : ∀ j, Function.support (E.slot j) ⊆ target)
    (ξ : WithLp 2 (ℝ × ℝ)) (j : Fin allocation.keep.card) (t : ℝ) :
    Function.support
      ((frozenInverseRawWindow P R W allocation F parent oldMoving correction hcorr C p
        leftMultiplicity rightMultiplicity pattern sector remaining extra m q index
        rectangle firstSign negative reference time original hreference htime E
        hcompact hpositive s horders hbound horiginalBound hleft hright hslot ξ).primeRep j t)
      ⊆ target := by
  sorry

end CanonicalLiteralAllocatedData
end HeckeSkeleton.Moments.EngineStepV2

end

/-!
# Original norm lower bounds for active balanced profiles

The lower bound on a plain central scale is derived from a genuinely
nonzero ideal summand and the original annulus. Dividing that scale by
the norms of the actual extracted ideals only decreases it. Thus the
pre-extraction scale product required by the balanced-profile estimate
is a consequence of the literal quotient-scale identities, rather than
a final profile or capacity assumption.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2

open HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments HeckePort.Moments.Support

namespace CanonicalLiteralActiveProfileBounds

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}

theorem plainScale_lower (W : IdealTest K)
    (u : HeckeGeneral.Analysis.NonzeroIdeal K) (N time hi : ℝ)
    (hN : 0 < N) (hhi : 0 < hi)
    (hannulus : ∀ y, W.profile u time y ≠ 0 → y ≤ hi)
    (hne : (W.support u time N).Nonempty) : 1 / hi ≤ N := by
  sorry

theorem pairedScale_lower (d : MomentData K ω ψ) (parameters : RealParameters)
    (Z time lo hi : ℝ) (hZ : 0 < Z) (hhi : 0 < hi)
    {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)} {heightDomain : Set ℝ}
    {s : Finset (ℕ × ℕ)} {B : ℝ}
    (w : RawProfileWindow rowDomain heightDomain (Set.Icc lo hi) s d B)
    (hrows : ∀ u ∈ pairedRows d parameters Z, u ∈ rowDomain)
    (ht : time ∈ heightDomain) (hne : pairedEnergy d parameters Z time ≠ 0) :
    1 / hi ≤ Z ^ parameters.n₁ ∧ 1 / hi ≤ Z ^ parameters.n₂ := by
  sorry

/-- The ideals may be the products of the actual second-common and
allocation divisors. Their norm lower bound is proved internally. -/
theorem quotient_product_lower_of_nonzero
    (d : MomentData K ω ψ) (parameters : RealParameters)
    (Z time lo hi N₁ N₂ : ℝ) (hZ : 0 < Z) (hhi : 0 < hi)
    (hN₁ : 0 < N₁) (hN₂ : 0 < N₂)
    (I₁ I₂ : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hscale₁ : Z ^ parameters.n₁ = N₁ / idealNorm K I₁)
    (hscale₂ : Z ^ parameters.n₂ = N₂ / idealNorm K I₂)
    {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)} {heightDomain : Set ℝ}
    {s : Finset (ℕ × ℕ)} {B : ℝ}
    (w : RawProfileWindow rowDomain heightDomain (Set.Icc lo hi) s d B)
    (hrows : ∀ u ∈ pairedRows d parameters Z, u ∈ rowDomain)
    (ht : time ∈ heightDomain) (hne : pairedEnergy d parameters Z time ≠ 0) :
    hi ^ (-2 : ℝ) ≤ N₁ * N₂ := by
  sorry

end CanonicalLiteralActiveProfileBounds

variable {K : Type} [Field K] [NumberField K]

namespace CanonicalLiteralRectangles.Atoms.ProfileData.SchwartzModel

variable {k : ℕ} {d : CanonicalLiteralRectangles.Atoms (K := K) k} {W : d.ProfileData}
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

/-- The common numerical coefficient is computed from the original
profile bound, fixed annulus and tilt/order constants. Its only scale
premise is the literal product lower bound proved above from a real
nonzero member. -/
theorem scalarFreeBalanced_original_bounds
    (hcompact : IsCompact window) (hpositive : window ⊆ Set.Ioi 0)
    (r : Bool) (s : Finset (ℕ × ℕ)) (B hi : ℝ) (hB : 0 ≤ B) (hhi : 1 ≤ hi)
    (hδlo : 0 ≤ δ₁ + δ₂) (hδhi : δ₁ + δ₂ ≤ 1 / 2)
    (hproduct : d.scale₁ r * d.scale₂ r = d.scale₁ false * d.scale₂ false)
    (hlower : hi ^ (-2 : ℝ) ≤ (d.extract b).scale₁ false * (d.extract b).scale₂ false)
    (hleft : (CanonicalLogProfiles.sourceOrders s).sup
      (schwartzSeminormFamily ℂ ℝ ℂ) (E.left r) ≤ B)
    (hright : (CanonicalLogProfiles.sourceOrders s).sup
      (schwartzSeminormFamily ℂ ℝ ℂ) (E.right r) ≤ B)
    (hslot : ∀ j, (CanonicalLogProfiles.sourceOrders s).sup
      (schwartzSeminormFamily ℂ ℝ ℂ) (E.slot j) ≤ B) :
    let T := E.scalarFreeBalancedSecondInput (σ := σ) b P R
      power firstFixed poolFixed unitFixed firstElement poolElement unitElement
      hfirst hpool hunit δ₁ δ₂ hcompact hpositive
    let bound := B * CanonicalLogProfiles.shapeCoefficient window hcompact hpositive
      (CanonicalLiteralProfileScalars.exponent δ₁ δ₂) s * (1 + Real.sqrt hi)
    s.sup (schwartzSeminormFamily ℂ ℝ ℂ) (T.left r) ≤ bound ∧
      s.sup (schwartzSeminormFamily ℂ ℝ ℂ) (T.right r) ≤ bound ∧
      ∀ j, s.sup (schwartzSeminormFamily ℂ ℝ ℂ) (T.slot j) ≤ bound := by
  sorry

/-- Every rectangle, including a zero rectangle, gets a radius from
its actual scale product. No nonzero-source premise or maximum over
other rectangles occurs in this construction. The preceding theorem
bounds this same coefficient uniformly when the rectangle is active. -/
theorem scalarFreeBalanced_computed_bounds
    (hcompact : IsCompact window) (hpositive : window ⊆ Set.Ioi 0)
    (r : Bool) (s : Finset (ℕ × ℕ)) (B : ℝ) (hB : 0 ≤ B)
    (hδhi : δ₁ + δ₂ ≤ 1 / 2)
    (hleft : (CanonicalLogProfiles.sourceOrders s).sup
      (schwartzSeminormFamily ℂ ℝ ℂ) (E.left r) ≤ B)
    (hright : (CanonicalLogProfiles.sourceOrders s).sup
      (schwartzSeminormFamily ℂ ℝ ℂ) (E.right r) ≤ B)
    (hslot : ∀ j, (CanonicalLogProfiles.sourceOrders s).sup
      (schwartzSeminormFamily ℂ ℝ ℂ) (E.slot j) ≤ B) :
    let T := E.scalarFreeBalancedSecondInput (σ := σ) b P R
      power firstFixed poolFixed unitFixed firstElement poolElement unitElement
      hfirst hpool hunit δ₁ δ₂ hcompact hpositive
    let bound := B + B * CanonicalLogProfiles.shapeCoefficient window hcompact hpositive
      (CanonicalLiteralProfileScalars.exponent δ₁ δ₂) s *
        (1 + CanonicalLiteralBalancedSchwartz.factor d b δ₁ δ₂ r)
    s.sup (schwartzSeminormFamily ℂ ℝ ℂ) (T.left r) ≤ bound ∧
      s.sup (schwartzSeminormFamily ℂ ℝ ℂ) (T.right r) ≤ bound ∧
      ∀ j, s.sup (schwartzSeminormFamily ℂ ℝ ℂ) (T.slot j) ≤ bound := by
  sorry

end CanonicalLiteralRectangles.Atoms.ProfileData.SchwartzModel
end HeckeSkeleton.Moments.EngineStepV2

end

set_option quotPrecheck false

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

namespace HeckeSkeleton.Moments.EngineStepV2

open HeckeSkeleton.Moments.EngineStep

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
    firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂).scale outer⁻¹).balancePlain (CanonicalLiteralBalancedSchwartz.balance d b δ₁ δ₂)

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
    0 ≤ T.rawCoefficient hcompact hpositive firstSign rectangle := by
  sorry

def coefficient (Z : ℝ) (parameters : RealParameters)
    (hcompact : IsCompact window) (hpositive : window ⊆ Set.Ioi 0)
    (firstSign : ℝ) (rectangle : Bool) : ℝ :=
  CanonicalLiteralAllSideClipping.cost Z parameters s *
    (1 + T.rawCoefficient hcompact hpositive firstSign rectangle)

theorem coefficient_nonneg (Z : ℝ) (parameters : RealParameters) (hZ : 1 ≤ Z)
    (hcompact : IsCompact window) (hpositive : window ⊆ Set.Ioi 0)
    (firstSign : ℝ) (rectangle : Bool) :
    0 ≤ T.coefficient Z parameters hcompact hpositive firstSign rectangle := by
  sorry

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
  sorry

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
      ((HeckeSkeleton.Moments.EngineStepV2.CompleteMovingRowRecipe.literalOriginalAtoms Q) ξ recipe a Z t Y₁ Y₂ centered hZ hY₁ hY₂).plain₁
      ((HeckeSkeleton.Moments.EngineStepV2.CompleteMovingRowRecipe.literalOriginalAtoms Q) ξ recipe a Z t Y₁ Y₂ centered hZ hY₁ hY₂).plain₂
      ((HeckeSkeleton.Moments.EngineStepV2.CompleteMovingRowRecipe.literalOriginalAtoms Q) ξ recipe a Z t Y₁ Y₂ centered hZ hY₁ hY₂).slots support)
    (power firstFixed poolFixed unitFixed : A.Exterior)
    (firstElement poolElement unitElement : A.R)
    (hfirst : A.Generates firstFixed firstElement)
    (hpool : A.Generates poolFixed poolElement)
    (hunit : A.Generates unitFixed unitElement)
    (δ₁ δ₂ : ℝ) (hδhi : δ₁ + δ₂ ≤ 1 / 2) :
    let W := (HeckeSkeleton.Moments.EngineStepV2.CompleteMovingRowRecipe.literalOriginalProfileDataOfWindow Q) ξ recipe a Z t Y₁ Y₂ centered
      hZ hY₁ hY₂ reference href original hreference ht hpositive
    let d := (HeckeSkeleton.Moments.EngineStepV2.CompleteMovingRowRecipe.literalOriginalAtoms Q) ξ recipe a Z t Y₁ Y₂ centered hZ hY₁ hY₂
    let outer := d.commonScalar b * (((A.exteriorNorm power ^ δ₁ : ℝ) : ℂ) *
      actualIdealResidue (A := A) (σ := σ) power.val firstElement)
    CanonicalLiteralFullKappaInput.ComputedProfiles
      (((W.secondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
        firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂).scale outer⁻¹).balancePlain (CanonicalLiteralBalancedSchwartz.balance d b δ₁ δ₂)) window s B := by
  let E := (HeckeSkeleton.Moments.EngineStepV2.CompleteMovingRowRecipe.literalOriginalSchwartzModel Q) ξ recipe a Z t Y₁ Y₂ centered
    hZ hY₁ hY₂ reference href original hreference ht hpositive hcompact.isClosed
  have hb := (HeckeSkeleton.Moments.EngineStepV2.CompleteMovingRowRecipe.literalOriginalSchwartzModel_bound Q) ξ recipe a Z t Y₁ Y₂ centered
    hZ hY₁ hY₂ reference href original hreference ht hpositive hcompact.isClosed hB
  exact CanonicalLiteralFullKappaInput.scalarFreeBalanced (σ := σ) E b P R power firstFixed
    poolFixed unitFixed firstElement poolElement unitElement hfirst hpool hunit
    δ₁ δ₂ hcompact hpositive s B hB hδhi hb.1 hb.2.1 hb.2.2 hprime

end CompleteMovingRowRecipe
end HeckeSkeleton.Moments.EngineStepV2

end

