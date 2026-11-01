import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralProfileScalars
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralActualProfiles
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPlainBalance

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

namespace HeckeSkeleton.Moments.EngineStep

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
      c * (φ y * (y ^ exponent : ℂ)) := by
  simp only [powerSchwartz, SchwartzMap.smul_apply, smul_eq_mul,
    CanonicalLogProfiles.Atom.schwartz_apply, CanonicalLogProfiles.Atom.multiplier,
    powerAtom, one_mul, jointPhase, inner_zero_left, AddChar.map_zero_eq_one,
    Circle.coe_one, mul_one]

theorem powerSchwartz_support (window : Set ℝ) (hcompact : IsCompact window)
    (hpositive : window ⊆ Set.Ioi 0) (c : ℂ) (exponent : ℝ)
    (φ : 𝓢(ℝ, ℂ)) (hsupport : tsupport φ ⊆ window) :
    tsupport (powerSchwartz window hcompact hpositive c exponent φ hsupport) ⊆ window := by
  have he : (powerSchwartz window hcompact hpositive c exponent φ hsupport : ℝ → ℂ) =
      fun y => φ y * (c * (y ^ exponent : ℂ)) := by
    funext y
    rw [powerSchwartz_apply]
    ring
  rw [he]
  exact tsupport_mul_subset_left.trans hsupport

/-- Its coefficient and required original orders are fixed by the
annulus, real power and target orders before the original profile. -/
theorem powerSchwartz_finset_bound (window : Set ℝ) (hcompact : IsCompact window)
    (hpositive : window ⊆ Set.Ioi 0) (c : ℂ) (exponent : ℝ)
    (s : Finset (ℕ × ℕ)) (φ : 𝓢(ℝ, ℂ)) (hsupport : tsupport φ ⊆ window) :
    s.sup (schwartzSeminormFamily ℂ ℝ ℂ)
        (powerSchwartz window hcompact hpositive c exponent φ hsupport) ≤
      ‖c‖ * CanonicalLogProfiles.shapeCoefficient window hcompact hpositive exponent s *
        (CanonicalLogProfiles.sourceOrders s).sup (schwartzSeminormFamily ℂ ℝ ℂ) φ := by
  have h := (powerAtom exponent).schwartz_finset_bound
    window hcompact hpositive s 0 φ hsupport
  simp only [CanonicalLogProfiles.Atom.profileCoefficient, powerAtom, norm_zero,
    Real.one_rpow, mul_zero, add_zero, one_pow, mul_one] at h
  rw [powerSchwartz, map_smul_eq_mul]
  exact (mul_le_mul_of_nonneg_left h (norm_nonneg c)).trans_eq (by ring)

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
      ‖(c r : ℂ)‖ * s.sup (schwartzSeminormFamily ℂ ℝ ℂ) (E.left r) :=
  map_smul_eq_mul _ _ _

theorem balancePlain_right_seminorm (c : Bool → ℝ) (r : Bool) (s : Finset (ℕ × ℕ)) :
    s.sup (schwartzSeminormFamily ℂ ℝ ℂ) ((E.balancePlain c).right r) =
      ‖(c r : ℂ)⁻¹‖ * s.sup (schwartzSeminormFamily ℂ ℝ ℂ) (E.right r) :=
  map_smul_eq_mul _ _ _

/-- A transport for literal individual profile identities. The
following `secondInput` constructor supplies these identities from the
actual original operations. -/
def powerProfiles {d' : CanonicalLiteralRectangles.Atoms (K := K) k}
    (W' : d'.ProfileData) (hcompact : IsCompact window)
    (hpositive : window ⊆ Set.Ioi 0) (exponent : ℝ)
    (leftScalar rightScalar : Bool → ℂ) (slotScalar : Fin k → ℂ)
    (hleft : ∀ r u t y, 0 < y →
      (W'.left r).profile u t y = leftScalar r * ((W.left r).profile u t y * (y ^ exponent : ℂ)))
    (hright : ∀ r u t y, 0 < y →
      (W'.right r).profile u t y = rightScalar r * ((W.right r).profile u t y * (y ^ exponent : ℂ)))
    (hslot : ∀ j t y, 0 < y →
      (W'.slot j).profile t y = slotScalar j * ((W.slot j).profile t y * (y ^ exponent : ℂ))) :
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
        (CanonicalLogProfiles.sourceOrders s).sup (schwartzSeminormFamily ℂ ℝ ℂ) (E.left r) :=
  CanonicalLiteralSchwartzProfiles.powerSchwartz_finset_bound
    window hcompact hpositive _ _ s _ (E.left_support r)

theorem secondInput_right_seminorm_le (hcompact : IsCompact window)
    (hpositive : window ⊆ Set.Ioi 0) (r : Bool) (s : Finset (ℕ × ℕ)) :
    s.sup (schwartzSeminormFamily ℂ ℝ ℂ)
      ((E.secondInput (σ := σ) b P R power firstFixed poolFixed unitFixed
        firstElement poolElement unitElement hfirst hpool hunit δ₁ δ₂ hcompact hpositive).right r) ≤
      ‖(CanonicalLiteralProfileScalars.plainFactor
        ((d.extract b).scale₂ false) ((d.extract b).scale₂ r) δ₁ δ₂ : ℂ)‖ *
        CanonicalLogProfiles.shapeCoefficient window hcompact hpositive
          (CanonicalLiteralProfileScalars.exponent δ₁ δ₂) s *
        (CanonicalLogProfiles.sourceOrders s).sup (schwartzSeminormFamily ℂ ℝ ℂ) (E.right r) :=
  CanonicalLiteralSchwartzProfiles.powerSchwartz_finset_bound
    window hcompact hpositive _ _ s _ (E.right_support r)

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
          (E.slot (SlotRestriction.index b.keep j)) :=
  CanonicalLiteralSchwartzProfiles.powerSchwartz_finset_bound
    window hcompact hpositive _ _ s _ (E.slot_support (SlotRestriction.index b.keep j))

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
    (Q.literalOriginalProfileDataOfWindow ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
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
    let E := Q.literalOriginalSchwartzModel ξ W a Z t Y₁ Y₂ centered hZ hY₁ hY₂
      reference href original hreference ht hwindow hclosed
    (∀ r, seminorms.sup (schwartzSeminormFamily ℂ ℝ ℂ) (E.left r) ≤ bound) ∧
      (∀ r, seminorms.sup (schwartzSeminormFamily ℂ ℝ ℂ) (E.right r) ≤ bound) ∧
      (∀ j, seminorms.sup (schwartzSeminormFamily ℂ ℝ ℂ) (E.slot j) ≤ bound) := by
  refine ⟨?_, ?_, ?_⟩
  · intro r
    change seminorms.sup (schwartzSeminormFamily ℂ ℝ ℂ)
      (if r && !centered then 0 else original.leftRep reference t) ≤ bound
    split_ifs
    · simpa only [map_zero] using hbound
    · exact original.left_bound reference hreference t ht
  · intro r
    exact original.right_bound reference hreference t ht
  · intro j
    exact original.prime_bound j t ht

end CompleteMovingRowRecipe
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralSchwartzProfiles.powerSchwartz_finset_bound
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.ProfileData.SchwartzModel.balancePlain
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.ProfileData.SchwartzModel.secondInput
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.ProfileData.SchwartzModel.secondInput_left_seminorm_le
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.ProfileData.SchwartzModel.secondInput_right_seminorm_le
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.ProfileData.SchwartzModel.secondInput_slot_seminorm_le
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalOriginalSchwartzModel
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.literalOriginalSchwartzModel_bound
