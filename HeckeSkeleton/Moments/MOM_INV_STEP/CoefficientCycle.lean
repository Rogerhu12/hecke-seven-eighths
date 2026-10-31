import HeckeGeneral.Analysis.LocalThetaInput
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring

/-!
# The calibrated coefficient cycle

The only theta input is the explicit `ThetaCalibrationInput` belonging to
MOM_BASE. All coefficients below are the actual Hecke ideal coefficients
and normalized finite Gauss sums. In particular, the inverse coefficient
is not defined to make the second transform succeed. The two identities
are consequences of the given arithmetic calibration, with their finite
order twists and conjugations shown explicitly.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.CoefficientCycle

open NumberField IsDedekindDomain UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton
open scoped Classical BigOperators ComplexConjugate nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

/-- Unramified unitary characters have norm one on every exterior ideal,
not merely norm at most one. -/
theorem exterior_heckeCoefficient_norm (χ : HeckeCharacter K)
    (hχ : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K χ p)
    (I : ExteriorIdeal K S) : ‖heckeIdealCoefficient K χ I.val‖ = 1 := by
  unfold heckeIdealCoefficient nonzeroIdealCoefficient idealCoefficient
  have hI : I.val.val ≠ ⊥ := by
    simpa only [Ideal.zero_eq_bot] using nonZeroDivisors.coe_ne_zero I.val
  rw [if_neg hI, Multiset.norm_prod_map]
  apply Multiset.prod_eq_one
  intro r hr
  obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.mp hr
  have hp : Prime P := prime_of_normalized_factor P hP
  let p : HeightOneSpectrum (𝓞 K) := HeightOneSpectrum.ofPrime hp
  have hpd : p.asIdeal ∣ I.val.val := dvd_of_mem_normalizedFactors hP
  have hu := hχ p (I.property p hpd)
  simp only [primeIdealValue, dif_pos hp]
  rw [primeCoefficient_of_unramified K χ p hu]
  simp

theorem squarefree_moebius_norm (I : ExteriorIdeal K S) (hI : Squarefree I.val.val) :
    ‖(moebius I.val.val : ℂ)‖ = 1 := by
  rw [hI.moebius_eq, Int.cast_pow, Int.cast_neg, Int.cast_one, norm_pow]
  simp

def canonicalCoefficient (Λ : HeckeCharacter K) (I : ExteriorIdeal K S) : ℂ :=
  conj (heckeIdealCoefficient K Λ I.val) * thetaGamma K S D I 2

variable {K S D}
variable {Λ G : HeckeCharacter K}

theorem thetaGamma_two_norm (hcal : ThetaCalibrationInput K S D Λ G)
    (I : ExteriorIdeal K S) (hI : Squarefree I.val.val) :
    ‖thetaGamma K S D I 2‖ = 1 := by
  have h := congrArg norm (hcal.cube_calibration I hI)
  rw [norm_pow, norm_mul, squarefree_moebius_norm K S I hI,
    exterior_heckeCoefficient_norm K S Λ hcal.lambda_unramified I, one_mul] at h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by decide : (3 : ℕ) ≠ 0)).mp h

theorem canonicalCoefficient_norm (hcal : ThetaCalibrationInput K S D Λ G)
    (I : ExteriorIdeal K S) (hI : Squarefree I.val.val) :
    ‖canonicalCoefficient K S D Λ I‖ = 1 := by
  rw [canonicalCoefficient, norm_mul, Complex.norm_conj,
    exterior_heckeCoefficient_norm K S Λ hcal.lambda_unramified I,
    thetaGamma_two_norm hcal I hI, one_mul]

/-- The first primitive transform returns a Moebius coefficient with
the actual finite-order Hecke twist G. -/
theorem first_cycle (hcal : ThetaCalibrationInput K S D Λ G)
    (I : ExteriorIdeal K S) (hI : Squarefree I.val.val) :
    canonicalCoefficient K S D Λ I * thetaGamma K S D I 1 =
      (moebius I.val.val : ℂ) * heckeIdealCoefficient K G I.val :=
  hcal.mixed_calibration I hI

theorem thetaGamma_one_norm (hcal : ThetaCalibrationInput K S D Λ G)
    (I : ExteriorIdeal K S) (hI : Squarefree I.val.val) :
    ‖thetaGamma K S D I 1‖ = 1 := by
  have h := congrArg norm (first_cycle hcal I hI)
  simpa only [norm_mul, canonicalCoefficient_norm hcal I hI,
    squarefree_moebius_norm K S I hI,
    exterior_heckeCoefficient_norm K S G hcal.G_unramified I, one_mul] using h

/-- The second primitive transform returns the same canonical a₀,
with the conjugate of the actual finite-order twist. -/
theorem second_cycle (hcal : ThetaCalibrationInput K S D Λ G)
    (I : ExteriorIdeal K S) (hI : Squarefree I.val.val) :
    (moebius I.val.val : ℂ) * conj (thetaGamma K S D I 1) =
      canonicalCoefficient K S D Λ I * conj (heckeIdealCoefficient K G I.val) := by
  have hγ : thetaGamma K S D I 1 * conj (thetaGamma K S D I 1) = 1 := by
    rw [Complex.mul_conj', thetaGamma_one_norm hcal I hI]
    norm_num
  have hG : heckeIdealCoefficient K G I.val * conj (heckeIdealCoefficient K G I.val) = 1 := by
    rw [Complex.mul_conj', exterior_heckeCoefficient_norm K S G hcal.G_unramified I]
    norm_num
  calc
    _ = ((moebius I.val.val : ℂ) * heckeIdealCoefficient K G I.val) *
        conj (thetaGamma K S D I 1) * conj (heckeIdealCoefficient K G I.val) := by
      calc
        _ = (moebius I.val.val : ℂ) * conj (thetaGamma K S D I 1) *
            (heckeIdealCoefficient K G I.val * conj (heckeIdealCoefficient K G I.val)) := by
          rw [hG, mul_one]
        _ = _ := by ring
    _ = _ := by
      rw [← first_cycle hcal I hI]
      calc
        _ = canonicalCoefficient K S D Λ I *
            (thetaGamma K S D I 1 * conj (thetaGamma K S D I 1)) *
            conj (heckeIdealCoefficient K G I.val) := by ring
        _ = _ := by rw [hγ, mul_one]

/-- Live backgrounds stay on their original column throughout the first
calibration. They may include a separately supplied fixed finite twist. -/
theorem first_cycle_background (hcal : ThetaCalibrationInput K S D Λ G)
    (I : ExteriorIdeal K S) (hI : Squarefree I.val.val) (ν : ℂ) :
    canonicalCoefficient K S D Λ I * ν * thetaGamma K S D I 1 =
      (moebius I.val.val : ℂ) * ν * heckeIdealCoefficient K G I.val := by
  calc
    _ = (canonicalCoefficient K S D Λ I * thetaGamma K S D I 1) * ν := by ring
    _ = _ := by rw [first_cycle hcal I hI]; ring

theorem second_cycle_background (hcal : ThetaCalibrationInput K S D Λ G)
    (I : ExteriorIdeal K S) (hI : Squarefree I.val.val) (ν : ℂ) :
    (moebius I.val.val : ℂ) * ν * conj (thetaGamma K S D I 1) =
      canonicalCoefficient K S D Λ I * ν * conj (heckeIdealCoefficient K G I.val) := by
  calc
    _ = ((moebius I.val.val : ℂ) * conj (thetaGamma K S D I 1)) * ν := by ring
    _ = _ := by rw [second_cycle hcal I hI]; ring

/-- A common unramified background cancels in a squared pair. No
multiplicative choice of ideal generators is used. -/
theorem background_common_factor (ν : HeckeCharacter K)
    (hν : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K ν p)
    (C A B : ExteriorIdeal K S) :
    heckeIdealCoefficient K ν (C.val * A.val) *
        conj (heckeIdealCoefficient K ν (C.val * B.val)) =
      heckeIdealCoefficient K ν A.val * conj (heckeIdealCoefficient K ν B.val) := by
  rw [heckeIdealCoefficient_mul, heckeIdealCoefficient_mul, map_mul]
  calc
    _ = (heckeIdealCoefficient K ν C.val * conj (heckeIdealCoefficient K ν C.val)) *
        (heckeIdealCoefficient K ν A.val * conj (heckeIdealCoefficient K ν B.val)) := by ring
    _ = _ := by
      rw [Complex.mul_conj', exterior_heckeCoefficient_norm K S ν hν C]
      norm_num

end HeckeSkeleton.Moments.MOM_INV_STEP.CoefficientCycle

end
