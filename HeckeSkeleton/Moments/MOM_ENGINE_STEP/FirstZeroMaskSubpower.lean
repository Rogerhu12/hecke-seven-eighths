import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstZeroAmplitude
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalMaskCardinality

/-!
# Original zero-frequency mask weights have a small-power cost

The genuine mask-dilated radius is at least the original radius, so
each original divisor weight costs at most the inverse original radius.
Its finite carrier is counted by the divisor count of the actual ideal
identified by its primes. The constant is fixed before the moving
mask, radius, original profile, or normalization scale.

This supplies the individual profile normalization used by the true
first-zero calibration. It does not assume a zero-frequency sum bound
or replace the first divisor by a second-transform label.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis

variable {K : Type} [Field K] [NumberField K]
variable {S : Finset (HeightOneSpectrum (𝓞 K))}
local notation "OS" => Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K
variable [IsPrincipalIdealRing OS]

theorem firstZeroDivisorWeight_le_inverseRadius
    (radius : {r : ℝ // 0 < r}) (D : Finset (HeightOneSpectrum OS)) :
    firstZeroDivisorWeight radius D ≤ radius.val⁻¹ := by
  let δ := sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D
  let ρ := sIntegerMaskDilationRadius K S radius δ
  have hμ : ‖(moebius (IdealMobiusMask.primeProduct D) : ℂ)‖ ≤ 1 := by
    unfold moebius
    split_ifs <;> simp
  have hρ : radius.val ≤ ρ.val :=
    (mul_one radius.val).symm.trans_le
      (mul_le_mul_of_nonneg_left
        (one_le_sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K))) δ)
        radius.property.le)
  have hi : ρ.val⁻¹ ≤ radius.val⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le radius.property hρ
  change ‖(moebius (IdealMobiusMask.primeProduct D) : ℂ)‖ * ρ.val⁻¹ ≤ _
  exact (mul_le_mul_of_nonneg_right hμ (inv_nonneg.mpr ρ.property.le)).trans
    (by simpa only [one_mul] using hi)

theorem firstZeroDivisorSum_le_card
    (radius : {r : ℝ // 0 < r}) (M : Finset (HeightOneSpectrum OS)) :
    (∑ D ∈ M.powerset, firstZeroDivisorWeight radius D) ≤
      (M.powerset.card : ℝ) * radius.val⁻¹ := by
  calc
    _ ≤ ∑ _D ∈ M.powerset, radius.val⁻¹ :=
      Finset.sum_le_sum (fun D _ => firstZeroDivisorWeight_le_inverseRadius radius D)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]

/-- The ideal-prime dictionary, not a bound on an arbitrary Boolean
carrier, pays the original mask count. -/
theorem first_zero_mask_sum_uniform (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Z : ℝ), 1 ≤ Z →
    ∀ (radius : {r : ℝ // 0 < r}) (M : Finset (HeightOneSpectrum OS))
      (R : Ideal (𝓞 K)), R ≠ 0 → (Ideal.absNorm R : ℝ) ≤ Z ^ B →
      OriginalMaskPrimeData M R →
      (∑ D ∈ M.powerset, firstZeroDivisorWeight radius D) ≤
        C * Z ^ ε * radius.val⁻¹ := by
  obtain ⟨C, hC, hc⟩ := original_mask_labels_subpower (K := K) B ε hB hε
  refine ⟨C, hC, ?_⟩
  intro Z hZ radius M R hR hN W
  exact (firstZeroDivisorSum_le_card radius M).trans
    (mul_le_mul_of_nonneg_right (hc Z hZ M R hR hN W) (inv_nonneg.mpr radius.property.le))

/-- The original per-profile seminorm and inverse radius give the
literal zeroAmplitude normalization, with its full central square root.
The controlling constant is fixed before the profile and all exponents. -/
theorem first_zero_profile_normalization_uniform (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Z : ℝ), 1 ≤ Z →
    ∀ (radius : {r : ℝ // 0 < r}) (M : Finset (HeightOneSpectrum OS))
      (R : Ideal (𝓞 K)), R ≠ 0 → (Ideal.absNorm R : ℝ) ≤ Z ^ B →
      OriginalMaskPrimeData M R →
    ∀ (profile profileBound profileExponent inverseRadiusExponent productExponent : ℝ),
      0 ≤ profile → 0 ≤ profileBound →
      profile ≤ profileBound * Z ^ profileExponent →
      radius.val⁻¹ ≤ Z ^ inverseRadiusExponent →
      profile * (∑ D ∈ M.powerset, firstZeroDivisorWeight radius D) ≤
        (C * profileBound *
          Z ^ (profileExponent + inverseRadiusExponent + ε + productExponent / 2)) /
            Real.sqrt (Z ^ productExponent) := by
  obtain ⟨C, hC, hm⟩ := first_zero_mask_sum_uniform (S := S) B ε hB hε
  refine ⟨C, hC, ?_⟩
  intro Z hZ radius M R hR hN W profile profileBound profileExponent inverseRadiusExponent
    productExponent hp hP hprofile hradius
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  have hmask := (hm Z hZ radius M R hR hN W).trans
    (mul_le_mul_of_nonneg_left hradius (mul_nonneg hC.le (Real.rpow_nonneg hz.le _)))
  have hpair := mul_le_mul hprofile hmask
    (Finset.sum_nonneg (fun D _ => firstZeroDivisorWeight_nonneg radius D))
    (mul_nonneg hP (Real.rpow_nonneg hz.le _))
  have hsqrt : Real.sqrt (Z ^ productExponent) = Z ^ (productExponent / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hz.le]
    congr 1
    ring
  have hnormalization :
      (C * profileBound *
        Z ^ (profileExponent + inverseRadiusExponent + ε + productExponent / 2)) /
          Real.sqrt (Z ^ productExponent) =
        C * profileBound * Z ^ (profileExponent + inverseRadiusExponent + ε) := by
    rw [hsqrt, mul_div_assoc, ← Real.rpow_sub hz]
    rw [show (profileExponent + inverseRadiusExponent + ε + productExponent / 2) -
      productExponent / 2 = profileExponent + inverseRadiusExponent + ε by ring]
  calc
    _ ≤ (profileBound * Z ^ profileExponent) *
        (C * Z ^ ε * Z ^ inverseRadiusExponent) := hpair
    _ = C * profileBound * Z ^ (profileExponent + inverseRadiusExponent + ε) := by
      rw [Real.rpow_add hz, Real.rpow_add hz]
      ring
    _ = _ := hnormalization.symm

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.first_zero_mask_sum_uniform
#print axioms HeckeSkeleton.Moments.EngineStep.first_zero_profile_normalization_uniform
