import HeckeSkeleton.Moments.MOM_PRIME.OrdinaryMasks

/-!
# The coefficient mass in normalized ordinary mask deletion

The coefficients are exactly those in `normalizedHeckeSum_mask_deletion`:
the ideal Möbius coefficient, the genuine Hecke coefficient, the unchanged
norm phase, and the inverse square root of the divisor norm. Each nonzero
divisor has norm at least one, so the coefficient norm is at most one.

Summing this estimate costs only the actual number of ideal divisors.
The existing divisor estimate then supplies a single `C * Z^ε` bound,
chosen before the character, mask, height, and external scale. No
functional equation or reflected moment estimate is assumed.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_PRIME

open NumberField UniqueFactorizationMonoid DedekindZetaZeroFree.LargeSieve
open HeckeGeneral.Characters
open HeckePort.IdealMobiusDivisorSum HeckePort.CenteredMomentMask
open HeckePort.Moments.Twist
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]

/-- The literal coefficient in normalized divisor mask deletion. -/
def ordinaryMaskCoefficient (χ : HeckeCharacter K) (D : Ideal (𝓞 K)) (t : ℝ) : ℂ :=
  (moebius D : ℂ) * heckeExceptionalCharacter K χ D *
    (Ideal.absNorm D : ℂ) ^ (Complex.I * t) *
    (Real.sqrt (Ideal.absNorm D : ℝ) : ℂ)⁻¹

/-- The actual finite ℓ¹ mass of the normalized mask coefficients. -/
def ordinaryMaskMass (χ : HeckeCharacter K) (R : Ideal (𝓞 K)) (t : ℝ) : ℝ :=
  ∑ D ∈ idealDivisors R, ‖ordinaryMaskCoefficient K χ D t‖

/-- The norm phase is unitary, the Möbius and Hecke coefficients have norm
at most one, and a nonzero integral ideal has norm at least one. -/
theorem ordinaryMaskCoefficient_norm_le_one (χ : HeckeCharacter K)
    (D : Ideal (𝓞 K)) (hD : D ≠ ⊥) (t : ℝ) :
    ‖ordinaryMaskCoefficient K χ D t‖ ≤ 1 := by
  have hnNat : 1 ≤ Ideal.absNorm D := Nat.one_le_iff_ne_zero.mpr
    (fun hz => hD (Ideal.absNorm_eq_zero_iff.mp hz))
  have hn : (1 : ℝ) ≤ (Ideal.absNorm D : ℝ) := by exact_mod_cast hnNat
  have hsqrt : 1 ≤ Real.sqrt (Ideal.absNorm D : ℝ) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hn
  have hphase : ‖(Ideal.absNorm D : ℂ) ^ (Complex.I * t)‖ = 1 := by
    simpa only [Complex.ofReal_natCast] using
      norm_real_imaginary_power (Ideal.absNorm D : ℝ) t (zero_lt_one.trans_le hn)
  have hinv : ‖(Real.sqrt (Ideal.absNorm D : ℝ) : ℂ)⁻¹‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_of_nonneg (Real.sqrt_nonneg _)]
    exact inv_le_one_of_one_le₀ hsqrt
  have hcoeff : ‖(moebius D : ℂ) * heckeExceptionalCharacter K χ D‖ ≤ 1 := by
    rw [norm_mul]
    exact (mul_le_mul (norm_ideal_moebius_le_one D)
      (norm_heckeExceptionalCharacter_le_one K χ D)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  rw [ordinaryMaskCoefficient, norm_mul, norm_mul, hphase, mul_one]
  exact (mul_le_mul hcoeff hinv (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

/-- The coefficient mass is bounded by the actual divisor count, with
every original coefficient and its norm phase retained. -/
theorem ordinaryMaskMass_le_card (χ : HeckeCharacter K)
    (R : Ideal (𝓞 K)) (hR : R ≠ ⊥) (t : ℝ) :
    ordinaryMaskMass K χ R t ≤ ((idealDivisors R).card : ℝ) := by
  unfold ordinaryMaskMass
  calc
    _ ≤ ∑ _D ∈ idealDivisors R, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro D hD
      exact ordinaryMaskCoefficient_norm_le_one K χ D
        (ne_zero_of_dvd_ne_zero hR ((mem_idealDivisors hR).mp hD)) t
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, mul_one]

/-- A common constant bounds the ordinary mask loss by `Z^ε`. The
character, common mask, height, and scale are all chosen afterwards. -/
theorem exists_ordinaryMaskMass_bound (ε B : ℝ) (hε : 0 < ε) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ (χ : HeckeCharacter K) (R : Ideal (𝓞 K)) (t Z : ℝ),
      R ≠ ⊥ → 1 ≤ Z → (Ideal.absNorm R : ℝ) ≤ Z ^ B →
      ordinaryMaskMass K χ R t ≤ C * Z ^ ε := by
  obtain ⟨C, hC, hdiv⟩ := polynomial_mask_divisor_bound (K := K) ε B hε hB
  refine ⟨C, hC, ?_⟩
  intro χ R t Z hR hZ hnorm
  exact (ordinaryMaskMass_le_card K χ R hR t).trans (hdiv Z hZ R hR hnorm)

end HeckeSkeleton.Moments.MOM_PRIME
