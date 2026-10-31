import HeckeSkeleton.Moments.MOM_BASE.PairedPhases
import HeckeGeneral.Analysis.MomentInputs

/-!
# The paired-phase invariant on the repository's actual polynomials

The original live character and its relative slot coefficient are connected
to `ConditionalMoments.primePolynomial`.  The support and common-mask
functions are used literally.  Background unramifiedness is needed only
where the original common mask is nonzero; row ramification is allowed.

The conjugation identities include the repository's normalization, tests,
and masks.  Whole-row orientation and a single reflected plain factor are
separate operations, so a centered difference never has just one of its
two comparison rectangles changed.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.MOM_BASE.Paired

open NumberField IsDedekindDomain
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open scoped Classical BigOperators ComplexConjugate nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable {ω ψ : HeckeCharacter K}

/-- A prime polynomial before cancelling its live whole-product background. -/
def originalPairedPrimePolynomial (d : MomentData K ω ψ)
    (i : Fin d.geometry.slotCount) (u : NonzeroIdeal K) (Z t : ℝ) : ℂ :=
  let P := Z ^ (d.geometry.slots i).length
  (Real.sqrt P : ℂ)⁻¹ * ∑ p ∈ (d.geometry.slots i).support t P,
    (primeCoefficient K (d.plainBackground * d.rowCharacter u) p *
      ((primeCoefficient K d.plainBackground p)⁻¹ * primeCoefficient K (d.slotCoefficient i) p)) *
      (d.geometry.slots i).profile t ((Ideal.absNorm p.asIdeal : ℝ) / P) *
      maskValue d u p.asIdeal

/-- The same polynomial with the original finite-character presentation
mask displayed, even when the two finite factors ramify and cancel. -/
theorem originalPairedPrimePolynomial_eq_masked (d : MomentData K ω ψ)
    (i : Fin d.geometry.slotCount) (u : NonzeroIdeal K) (Z t : ℝ)
    (hω : ∀ p ∈ (d.geometry.slots i).support t (Z ^ (d.geometry.slots i).length),
      d.commonMask u p.asIdeal = true → UnramifiedAt K d.plainBackground p) :
    originalPairedPrimePolynomial K d i u Z t =
      (Real.sqrt (Z ^ (d.geometry.slots i).length) : ℂ)⁻¹ *
        ∑ p ∈ (d.geometry.slots i).support t (Z ^ (d.geometry.slots i).length),
          (primeCoefficient K (d.rowCharacter u * d.slotCoefficient i) p *
            originalPrimeMask K (d.rowCharacter u) (d.slotCoefficient i) p) *
            (d.geometry.slots i).profile t
              ((Ideal.absNorm p.asIdeal : ℝ) / (Z ^ (d.geometry.slots i).length)) *
            maskValue d u p.asIdeal := by
  unfold originalPairedPrimePolynomial
  dsimp only
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  cases hm : d.commonMask u p.asIdeal with
  | false => simp [maskValue, hm]
  | true => rw [paired_primeCoefficient K d.plainBackground (d.rowCharacter u)
      (d.slotCoefficient i) p (hω p hp hm)]

/-- The actual source bridge.  A finite-ray slot unramified at the retained
prime gives exactly the existing `primePolynomial`, with all common zeros
and all profiles unchanged. -/
theorem originalPairedPrimePolynomial_eq (d : MomentData K ω ψ)
    (i : Fin d.geometry.slotCount) (u : NonzeroIdeal K) (Z t : ℝ)
    (hω : ∀ p ∈ (d.geometry.slots i).support t (Z ^ (d.geometry.slots i).length),
      d.commonMask u p.asIdeal = true → UnramifiedAt K d.plainBackground p)
    (hθ : ∀ p ∈ (d.geometry.slots i).support t (Z ^ (d.geometry.slots i).length),
      d.commonMask u p.asIdeal = true → UnramifiedAt K (d.slotCoefficient i) p) :
    originalPairedPrimePolynomial K d i u Z t = primePolynomial d i u Z t := by
  unfold originalPairedPrimePolynomial primePolynomial
  dsimp only
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  cases hm : d.commonMask u p.asIdeal with
  | false => simp [maskValue, hm]
  | true => rw [paired_primeCoefficient_unramified_slot K d.plainBackground (d.rowCharacter u)
      (d.slotCoefficient i) p (hω p hp hm) (hθ p hp hm)]

theorem primePolynomial_character_finite (d : MomentData K ω ψ)
    (i : Fin d.geometry.slotCount) (u : NonzeroIdeal K)
    (hθ : FiniteOrder (d.slotCoefficient i)) :
    FiniteOrder (d.rowCharacter u * d.slotCoefficient i) :=
  (d.rowCharacter_finite u).mul hθ

/-- Conjugation of a test leaves its exact finite support unchanged. -/
def conjugateIdealTest (W : IdealTest K) : IdealTest K where
  profile u t y := conj (W.profile u t y)
  support := W.support
  support_spec u t D I := by
    rw [W.support_spec]
    simp only [map_ne_zero]

/-- The conjugated plain sum uses the inverse of its entire character,
the conjugated test, the same ideal support, and the same original mask. -/
def conjugatePlainPolynomial (d : MomentData K ω ψ) (W : IdealTest K)
    (u : NonzeroIdeal K) (N t : ℝ) : ℂ :=
  (Real.sqrt N : ℂ)⁻¹ * ∑ I ∈ (conjugateIdealTest K W).support u t N,
    heckeIdealCoefficient K (d.plainBackground * d.rowCharacter u)⁻¹ I *
      (conjugateIdealTest K W).profile u t (idealNorm K I / N) * maskValue d u I.val

@[simp] theorem maskValue_conjugate (d : MomentData K ω ψ)
    (u : NonzeroIdeal K) (I : Ideal (𝓞 K)) :
    conj (maskValue d u I) = maskValue d u I := by
  unfold maskValue
  split_ifs <;> simp

theorem conjugatePlainPolynomial_eq (d : MomentData K ω ψ) (W : IdealTest K)
    (u : NonzeroIdeal K) (N t : ℝ) :
    conjugatePlainPolynomial K d W u N t = conj (plainPolynomial d W u N t) := by
  simp only [conjugatePlainPolynomial, conjugateIdealTest, plainPolynomial, map_mul,
    map_sum, map_inv₀, Complex.conj_ofReal, heckeIdealCoefficient_inv, maskValue_conjugate]

/-- Prime slots are conjugated with their finite character and test, while
the original common mask and full analytic support stay in place. -/
def conjugatePrimePolynomial (d : MomentData K ω ψ) (i : Fin d.geometry.slotCount)
    (u : NonzeroIdeal K) (Z t : ℝ) : ℂ :=
  let P := Z ^ (d.geometry.slots i).length
  (Real.sqrt P : ℂ)⁻¹ * ∑ p ∈ (d.geometry.slots i).support t P,
    primeCoefficient K (d.rowCharacter u * d.slotCoefficient i)⁻¹ p *
      conj ((d.geometry.slots i).profile t ((Ideal.absNorm p.asIdeal : ℝ) / P)) *
      maskValue d u p.asIdeal

theorem conjugatePrimePolynomial_eq (d : MomentData K ω ψ) (i : Fin d.geometry.slotCount)
    (u : NonzeroIdeal K) (Z t : ℝ) :
    conjugatePrimePolynomial K d i u Z t = conj (primePolynomial d i u Z t) := by
  simp only [conjugatePrimePolynomial, primePolynomial, map_mul, map_sum,
    map_inv₀, Complex.conj_ofReal, primeCoefficient_inv, maskValue_conjugate]

def conjugateSlotProduct (d : MomentData K ω ψ) (u : NonzeroIdeal K) (Z t : ℝ) : ℂ :=
  ∏ i, conjugatePrimePolynomial K d i u Z t

theorem conjugateSlotProduct_eq (d : MomentData K ω ψ) (u : NonzeroIdeal K) (Z t : ℝ) :
    conjugateSlotProduct K d u Z t = conj (slotProduct d u Z t) := by
  simp only [conjugateSlotProduct, slotProduct, conjugatePrimePolynomial_eq, map_prod]

/-- One reflected plain factor can be restored inside the uncentered
product absolute square, with all the other source factors fixed. -/
theorem reflected_plain_product_norm_square (d : MomentData K ω ψ) (W : IdealTest K)
    (u : NonzeroIdeal K) (N t : ℝ) (B Q : ℂ) :
    ‖conjugatePlainPolynomial K d W u N t * B * Q‖ ^ 2 =
      ‖plainPolynomial d W u N t * B * Q‖ ^ 2 := by
  rw [conjugatePlainPolynomial_eq]
  exact one_plain_conjugation_norm_square _ B Q

/-- The literal paired-fourth-moment summand is invariant under simultaneous
orientation reversal of both plain columns and every prime slot. -/
theorem paired_polynomial_orientation (d : MomentData K ω ψ)
    (u : NonzeroIdeal K) (N₁ N₂ Z t : ℝ) :
    ‖conjugatePlainPolynomial K d d.plainTest₁ u N₁ t *
        conjugatePlainPolynomial K d d.plainTest₂ u N₂ t *
        conjugateSlotProduct K d u Z t‖ ^ 2 =
      ‖plainPolynomial d d.plainTest₁ u N₁ t *
        plainPolynomial d d.plainTest₂ u N₂ t * slotProduct d u Z t‖ ^ 2 := by
  rw [conjugatePlainPolynomial_eq, conjugatePlainPolynomial_eq, conjugateSlotProduct_eq,
    ← map_mul, ← map_mul, Complex.norm_conj]

/-- Both rectangles keep the same row, tests and slots while orientation is
reversed.  No independent conjugation of one centered rectangle is used. -/
theorem centered_polynomial_orientation (d : MomentData K ω ψ)
    (W₁ W₂ : IdealTest K) (u : NonzeroIdeal K) (X₁ X₂ Y₁ Y₂ Z t : ℝ) :
    ‖conjugatePlainPolynomial K d W₁ u X₁ t *
          conjugatePlainPolynomial K d W₂ u X₂ t * conjugateSlotProduct K d u Z t -
        conjugatePlainPolynomial K d W₁ u Y₁ t *
          conjugatePlainPolynomial K d W₂ u Y₂ t * conjugateSlotProduct K d u Z t‖ ^ 2 =
      ‖plainPolynomial d W₁ u X₁ t * plainPolynomial d W₂ u X₂ t * slotProduct d u Z t -
        plainPolynomial d W₁ u Y₁ t * plainPolynomial d W₂ u Y₂ t * slotProduct d u Z t‖ ^ 2 := by
  simp only [conjugatePlainPolynomial_eq, conjugateSlotProduct_eq]
  exact centered_orientation_norm_square _ _ _ _ _

end HeckeSkeleton.Moments.MOM_BASE.Paired
