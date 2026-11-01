import HeckeSkeleton.Moments.MOM_PRIME.ExceptionalMomentBridge

/-!
# Ordinary normalized mask deletion

The divisor identity in manuscript §4.6 is an identity of the actual finite
ideal sums.  Normalizing by `sqrt X` produces precisely the coefficient
`μ(D) χ(D) / sqrt(N D)` and the shorter scale `X / N D`.  The same argument
also retains an independent norm phase.  No reflection or volume estimate
is required for this identity.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_PRIME

open NumberField UniqueFactorizationMonoid DedekindZetaZeroFree.LargeSieve
open HeckeGeneral.Characters HeckeGeneral.Arithmetic HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.CenteredMomentMask HeckePort.Moments.Twist
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]

/-- The normalized genuine Hecke ideal sum with its original common mask. -/
def normalizedHeckeSum (χ : HeckeCharacter K) (R : Ideal (𝓞 K))
    (W : ℝ → ℂ) (t X : ℝ) : ℂ :=
  (Real.sqrt X : ℂ)⁻¹ * heckeExceptionalSum K χ R W t X

/-- A norm phase remains on each divisor; the main scale decreases by its
actual ideal norm.  At `t = 0` this is the ordinary plain mask identity. -/
theorem normalizedHeckeSum_mask_deletion (χ : HeckeCharacter K)
    (R : Ideal (𝓞 K)) (hR : R ≠ ⊥) (W : ℝ → ℂ)
    (b t X : ℝ) (hX : 0 < X) (hs : Function.support W ⊆ Set.Iic b) :
    normalizedHeckeSum K χ R W t X =
      ∑ D ∈ idealDivisors R,
        ((moebius D : ℂ) * heckeExceptionalCharacter K χ D *
          (Ideal.absNorm D : ℂ) ^ (Complex.I * t) *
          (Real.sqrt (Ideal.absNorm D : ℝ) : ℂ)⁻¹) *
            normalizedHeckeSum K χ ⊤ W t (X / Ideal.absNorm D) := by
  unfold normalizedHeckeSum
  change (Real.sqrt X : ℂ)⁻¹ *
    twistedMaskedSum (heckeExceptionalCharacter K χ) R W t X = _
  rw [twisted_mask_deletion (heckeExceptionalCharacter K χ) R hR W b t X hX hs,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro D hD
  have hD0 : D ≠ ⊥ := ne_zero_of_dvd_ne_zero hR ((mem_idealDivisors hR).mp hD)
  have hq : 0 < (Ideal.absNorm D : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero
      (fun hz => hD0 (Ideal.absNorm_eq_zero_iff.mp hz))
  have hmul : (Ideal.absNorm D : ℝ) * (X / Ideal.absNorm D) = X := by
    field_simp [hq.ne']
  have hsqrt : (Real.sqrt X : ℂ) =
      (Real.sqrt (Ideal.absNorm D : ℝ) : ℂ) *
        (Real.sqrt (X / Ideal.absNorm D) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.sqrt_mul hq.le, hmul]
  have hnatural : heckeExceptionalSum K χ ⊤ W t (X / Ideal.absNorm D) =
      ∑' I : Ideal (𝓞 K), heckeExceptionalCharacter K χ I *
        (Ideal.absNorm I : ℂ) ^ (Complex.I * t) *
          W ((Ideal.absNorm I : ℝ) / (X / Ideal.absNorm D)) := by
    simp [heckeExceptionalSum, twistedMaskedSum, Ideal.isCoprime_iff_sup_eq]
  rw [hnatural, hsqrt, mul_inv_rev]
  ring

/-- The exact normalized divisor expansion used for ordinary reflection. -/
theorem normalizedHeckeSum_mask_deletion_zero (χ : HeckeCharacter K)
    (R : Ideal (𝓞 K)) (hR : R ≠ ⊥) (W : ℝ → ℂ)
    (b X : ℝ) (hX : 0 < X) (hs : Function.support W ⊆ Set.Iic b) :
    normalizedHeckeSum K χ R W 0 X =
      ∑ D ∈ idealDivisors R,
        ((moebius D : ℂ) * heckeExceptionalCharacter K χ D *
          (Real.sqrt (Ideal.absNorm D : ℝ) : ℂ)⁻¹) *
            normalizedHeckeSum K χ ⊤ W 0 (X / Ideal.absNorm D) := by
  simpa only [Complex.ofReal_zero, mul_zero, Complex.cpow_zero, mul_one] using
    normalizedHeckeSum_mask_deletion K χ R hR W b 0 X hX hs

/-- The same divisor expansion for the literal source `plainPolynomial`.
The hypotheses identify the actual common mask and actual test profile;
the natural sums preserve all Hecke ramification zeros. -/
theorem plainPolynomial_divisor_mask_deletion {ω ψ : HeckeCharacter K}
    (d : MomentData K ω ψ) (W : IdealTest K) (u : NonzeroIdeal K)
    (R : Ideal (𝓞 K)) (hR : R ≠ ⊥) (w : ℝ → ℂ)
    (b X : ℝ) (hX : 0 < X) (hs : Function.support w ⊆ Set.Iic b)
    (hmask : ∀ I : NonzeroIdeal K,
      maskValue d u I.val = if IsCoprime I.val R then (1 : ℂ) else 0)
    (hprofile : ∀ y, W.profile u 0 y = w y) :
    plainPolynomial d W u X 0 =
      ∑ D ∈ idealDivisors R,
        ((moebius D : ℂ) *
          heckeExceptionalCharacter K (d.plainBackground * d.rowCharacter u) D *
          (Real.sqrt (Ideal.absNorm D : ℝ) : ℂ)⁻¹) *
            normalizedHeckeSum K (d.plainBackground * d.rowCharacter u) ⊤ w 0
              (X / Ideal.absNorm D) := by
  rw [← plainPolynomial_exceptional_bridge K d W u R w X hX hmask hprofile]
  exact normalizedHeckeSum_mask_deletion_zero K
    (d.plainBackground * d.rowCharacter u) R hR w b X hX hs

end HeckeSkeleton.Moments.MOM_PRIME
