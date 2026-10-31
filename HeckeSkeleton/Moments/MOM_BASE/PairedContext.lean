import HeckeSkeleton.Moments.MOM_BASE.PairedPolynomials
import HeckeSkeleton.Base

/-!
# The paired-phase invariant for the actual target context

`TargetContext` supplies the exclusion set and its actual unramified target.
Consequently each of the three permitted plain backgrounds is unramified
on every exterior prime and has norm one on every exterior ideal.  These
facts discharge the background hypotheses in the whole-product identities.

The final polynomial bridge uses the literal original common-mask formula:
fixed exterior and away-six exclusions, and the original row coprimality
condition.  There is no extra moving mask or target-dependent profile.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.MOM_BASE.Paired

open NumberField IsDedekindDomain
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton
open scoped Classical BigOperators ComplexConjugate nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]

/-- Every allowed whole-product plain background is unramified outside the
actual exclusion set chosen for this target. -/
theorem context_background_unramified (c : TargetContext K) (β : HeckeCharacter K)
    (hβ : β = 1 ∨ β = targetCharacter K c ∨ β = (targetCharacter K c)⁻¹)
    (p : HeightOneSpectrum (𝓞 K)) (hp : p ∉ places K c) :
    UnramifiedAt K β p := by
  rcases hβ with rfl | rfl | rfl
  · exact unramifiedAt_one K p
  · exact target_unramified_outside K c p hp
  · exact (target_unramified_outside K c p hp).inv K

theorem context_plainBackground_unramified (c : TargetContext K)
    (d : MomentData K c.family.omega (targetCharacter K c))
    (p : HeightOneSpectrum (𝓞 K)) (hp : p ∉ places K c) :
    UnramifiedAt K d.plainBackground p :=
  context_background_unramified K c d.plainBackground d.plain_background_spec p hp

/-- The actual context needs no assumed cancellation law.  The inverse
background is the one belonging to this very same plain background. -/
theorem context_prime_pairing (c : TargetContext K)
    (d : MomentData K c.family.omega (targetCharacter K c))
    (u : NonzeroIdeal K) (i : Fin d.geometry.slotCount)
    (p : ExteriorPrime K (places K c)) :
    primeCoefficient K (d.plainBackground * d.rowCharacter u) p.val *
        primeCoefficient K (d.plainBackground⁻¹ * d.slotCoefficient i) p.val =
      primeCoefficient K (d.rowCharacter u * d.slotCoefficient i) p.val *
        originalPrimeMask K (d.rowCharacter u) (d.slotCoefficient i) p.val :=
  paired_relativeCoefficient K d.plainBackground (d.rowCharacter u) (d.slotCoefficient i)
    p.val (context_plainBackground_unramified K c d p.val p.property)

/-- The finite character left in the prime slot is accompanied by the
literal zero-preserving coefficient identity for this target. -/
theorem context_finite_prime_pairing (c : TargetContext K)
    (d : MomentData K c.family.omega (targetCharacter K c))
    (u : NonzeroIdeal K) (i : Fin d.geometry.slotCount)
    (hθ : FiniteOrder (d.slotCoefficient i)) (p : ExteriorPrime K (places K c)) :
    FiniteOrder (d.rowCharacter u * d.slotCoefficient i) ∧
      primeCoefficient K (d.plainBackground * d.rowCharacter u) p.val *
          primeCoefficient K (d.plainBackground⁻¹ * d.slotCoefficient i) p.val =
        primeCoefficient K (d.rowCharacter u * d.slotCoefficient i) p.val *
          originalPrimeMask K (d.rowCharacter u) (d.slotCoefficient i) p.val :=
  ⟨(d.rowCharacter_finite u).mul hθ, context_prime_pairing K c d u i p⟩

/-- The complete live-background character on an exterior ideal is a unit,
even when the background has infinite order. -/
theorem context_background_norm (c : TargetContext K) (β : HeckeCharacter K)
    (hβ : β = 1 ∨ β = targetCharacter K c ∨ β = (targetCharacter K c)⁻¹)
    (I : ExteriorIdeal K (places K c)) :
    ‖heckeIdealCoefficient K β I.val‖ = 1 :=
  norm_idealCoefficient_of_unramified K β I.val
    (fun p hp => context_background_unramified K c β hβ p (I.property p hp))

/-- Whole-product extraction for an actual ideal-indexed `MomentData` row.  The finite row
coefficient retains all its zeros; it need not be unramified on the index. -/
theorem context_plain_coefficient (c : TargetContext K)
    (d : MomentData K c.family.omega (targetCharacter K c))
    (u : NonzeroIdeal K) (I : ExteriorIdeal K (places K c)) :
    heckeIdealCoefficient K (d.plainBackground * d.rowCharacter u) I.val =
      heckeIdealCoefficient K d.plainBackground I.val *
        heckeIdealCoefficient K (d.rowCharacter u) I.val := by
  rw [mul_comm d.plainBackground (d.rowCharacter u),
    idealCoefficient_character_mul K (d.rowCharacter u) d.plainBackground I.val
      (fun p hp => context_plainBackground_unramified K c d p (I.property p hp)), mul_comm]

/-- The common whole-product background cancels on the actual exterior
common factor.  The remaining factors may contain original ramified zeros. -/
theorem context_common_cancellation (c : TargetContext K)
    (d : MomentData K c.family.omega (targetCharacter K c))
    (A₁ A₂ U₁ U₂ : NonzeroIdeal K) (C : ExteriorIdeal K (places K c)) :
    heckeIdealCoefficient K d.plainBackground (A₁ * C.val * U₁) *
        conj (heckeIdealCoefficient K d.plainBackground (A₂ * C.val * U₂)) =
      (heckeIdealCoefficient K d.plainBackground A₁ *
        conj (heckeIdealCoefficient K d.plainBackground A₂)) *
      (heckeIdealCoefficient K d.plainBackground U₁ *
        conj (heckeIdealCoefficient K d.plainBackground U₂)) :=
  whole_product_common_cancellation K d.plainBackground A₁ A₂ C.val U₁ U₂
    (fun p hp => context_plainBackground_unramified K c d p (C.property p hp))

/-- Freezing an exterior background factor preserves the source absolute
square, with the residual whole-product background still present. -/
theorem context_frozen_background (c : TargetContext K)
    (d : MomentData K c.family.omega (targetCharacter K c))
    (D : ExteriorIdeal K (places K c)) (A : NonzeroIdeal K) (z : ℂ) :
    ‖heckeIdealCoefficient K d.plainBackground (D.val * A) * z‖ ^ 2 =
      ‖heckeIdealCoefficient K d.plainBackground A * z‖ ^ 2 :=
  frozen_background_norm_square K d.plainBackground D.val A
    (fun p hp => context_plainBackground_unramified K c d p (D.property p hp)) z

/-- The literal formula of the original common mask used by the moments.
This local name avoids importing the moment-bound obligations. -/
def contextOriginalMask (c : TargetContext K) (u : NonzeroIdeal K)
    (I : Ideal (𝓞 K)) : Bool :=
  if (∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I →
      p ∉ places K c ∧ (6 : 𝓞 K) ∉ p.asIdeal) ∧ IsCoprime I u.val then true else false

theorem contextOriginalMask_exterior (c : TargetContext K) (u : NonzeroIdeal K)
    (p : HeightOneSpectrum (𝓞 K))
    (hm : contextOriginalMask K c u p.asIdeal = true) : p ∉ places K c := by
  unfold contextOriginalMask at hm
  split_ifs at hm with h
  · exact (h.1 p dvd_rfl).1
  · cases hm

/-- The exact source prime polynomial after cancelling the actual target
background.  Its common mask, profile and analytic support are unchanged.
The finite-factor presentation mask remains explicit if a slot ramifies. -/
theorem context_originalPrimePolynomial_eq_masked (c : TargetContext K)
    (d : MomentData K c.family.omega (targetCharacter K c))
    (i : Fin d.geometry.slotCount) (u : NonzeroIdeal K) (Z t : ℝ)
    (hmask : ∀ I, d.commonMask u I = contextOriginalMask K c u I) :
    originalPairedPrimePolynomial K d i u Z t =
      (Real.sqrt (Z ^ (d.geometry.slots i).length) : ℂ)⁻¹ *
        ∑ p ∈ (d.geometry.slots i).support t (Z ^ (d.geometry.slots i).length),
          (primeCoefficient K (d.rowCharacter u * d.slotCoefficient i) p *
            originalPrimeMask K (d.rowCharacter u) (d.slotCoefficient i) p) *
            (d.geometry.slots i).profile t
              ((Ideal.absNorm p.asIdeal : ℝ) / (Z ^ (d.geometry.slots i).length)) *
            maskValue d u p.asIdeal := by
  apply originalPairedPrimePolynomial_eq_masked
  intro p _hp hm
  apply context_plainBackground_unramified K c d p
  apply contextOriginalMask_exterior K c u p
  rw [← hmask]
  exact hm

/-- For the fixed finite-ray slots supported outside the same exclusion
set, the exact bridge lands in the repository's existing prime polynomial. -/
theorem context_originalPrimePolynomial_eq (c : TargetContext K)
    (d : MomentData K c.family.omega (targetCharacter K c))
    (i : Fin d.geometry.slotCount) (u : NonzeroIdeal K) (Z t : ℝ)
    (hmask : ∀ I, d.commonMask u I = contextOriginalMask K c u I)
    (hθ : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ places K c →
      UnramifiedAt K (d.slotCoefficient i) p) :
    originalPairedPrimePolynomial K d i u Z t = primePolynomial d i u Z t := by
  have hpout : ∀ p : HeightOneSpectrum (𝓞 K), d.commonMask u p.asIdeal = true →
      p ∉ places K c := by
    intro p hm
    apply contextOriginalMask_exterior K c u p
    rw [← hmask]
    exact hm
  apply originalPairedPrimePolynomial_eq
  · intro p _hp hm
    exact context_plainBackground_unramified K c d p (hpout p hm)
  · intro p _hp hm
    exact hθ p (hpout p hm)

end HeckeSkeleton.Moments.MOM_BASE.Paired
