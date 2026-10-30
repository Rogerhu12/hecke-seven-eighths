import DedekindZetaZeroFree.Theta.Profiles.ThirdBesselMellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
Fixed angular weight and radial twist at one complex place.

The Bessel function in this file is the actual `KThird` from Axiom.  Its base
Mellin integral is imported as a proved theorem, not as a hypothesis.  All
general weights are obtained by the Mellin power-shift identity.

This module concerns the radial profiles.  The actual derived Whittaker
vectors and their Weyl interchange are treated in `ComplexRootPowers` and
`ComplexWeylPowers`.
-/

noncomputable section

namespace HeckeSkeleton.ThetaLocal

open MeasureTheory Set Complex

/-- The radial exponent belonging to angular weight `m`. -/
def archWeight (m : ℤ) : ℝ := ((m.natAbs : ℝ) + 1) / 2

/-- The positive Bessel scale in Mellin coordinates. -/
def archScale (c : ℝ) : ℝ := 4 / c ^ 2

theorem archScale_pos (c : ℝ) (hc : 0 < c) : 0 < archScale c := by
  unfold archScale
  positivity

theorem archWeight_ge_half (m : ℤ) : (1 / 2 : ℝ) ≤ archWeight m := by
  unfold archWeight
  have h : (0 : ℝ) ≤ (m.natAbs : ℝ) := Nat.cast_nonneg _
  linarith

/-- The exponent before taking the Mellin transform. -/
def archExponent (m : ℤ) (τ : ℝ) : ℂ :=
  (archWeight m : ℂ) - (τ : ℂ) * I

/-- The direct profile, expressed through Axiom's genuine Bessel profile. -/
def archDirectProfile (c : ℝ) (m : ℤ) (τ : ℝ) (t : ℝ) : ℂ :=
  (t : ℂ) ^ (archExponent m τ - 1) *
    (DedekindZetaZeroFree.thirdBesselRadialProfile c t : ℂ)

/-- The reflected radial profile has the opposite radial twist. -/
def archReflectedProfile (c : ℝ) (m : ℤ) (τ : ℝ) : ℝ → ℂ :=
  archDirectProfile c m (-τ)

/-- The two Gamma factors at one complex place. -/
def archGammaPair (z : ℂ) : ℂ :=
  Gamma (z - 1 / 6) * Gamma (z + 1 / 6)

/-- The explicit constant `C₋ = 1/2 * A^(a-iτ)`. -/
def archDirectConstant (c : ℝ) (m : ℤ) (τ : ℝ) : ℂ :=
  (1 / 2 : ℂ) * (archScale c : ℂ) ^ archExponent m τ

/-- The explicit constant `C₊ = 1/2 * A^(a+iτ)`. -/
def archReflectedConstant (c : ℝ) (m : ℤ) (τ : ℝ) : ℂ :=
  archDirectConstant c m (-τ)

/-- The fixed phase which occurs when the raw profiles are used. -/
def archReflectionPhase (c τ : ℝ) : ℂ :=
  (archScale c : ℂ) ^ ((2 : ℂ) * (τ : ℂ) * I)

theorem archExponent_re (m : ℤ) (τ : ℝ) :
    (archExponent m τ).re = archWeight m := by
  simp [archExponent]

theorem archExponent_neg (m : ℤ) (τ : ℝ) :
    archExponent m (-τ) = (archWeight m : ℂ) + (τ : ℂ) * I := by
  simp [archExponent]

/-- The power-shift definition is the literal Bessel profile on the positive axis. -/
theorem archDirectProfile_eq (c : ℝ) (m : ℤ) (τ t : ℝ) (ht : 0 < t) :
    archDirectProfile c m τ t =
      (t : ℂ) ^ archExponent m τ *
        (DedekindZetaZeroFree.KThird (c * Real.sqrt t) : ℂ) := by
  have ht₀ : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  unfold archDirectProfile DedekindZetaZeroFree.thirdBesselRadialProfile
  push_cast
  calc
    _ = ((t : ℂ) ^ (archExponent m τ - 1) * (t : ℂ) ^ (1 : ℂ)) *
        (DedekindZetaZeroFree.KThird (c * Real.sqrt t) : ℂ) := by
      rw [Complex.cpow_one]
      ring
    _ = _ := by rw [← Complex.cpow_add _ _ ht₀, sub_add_cancel]

theorem archReflectedProfile_eq (c : ℝ) (m : ℤ) (τ t : ℝ) (ht : 0 < t) :
    archReflectedProfile c m τ t =
      (t : ℂ) ^ ((archWeight m : ℂ) + (τ : ℂ) * I) *
        (DedekindZetaZeroFree.KThird (c * Real.sqrt t) : ℂ) := by
  rw [archReflectedProfile, archDirectProfile_eq c m (-τ) t ht, archExponent_neg]

theorem archScale_four_pi : archScale (4 * Real.pi) = 1 / (4 * Real.pi ^ 2) := by
  unfold archScale
  field_simp [Real.pi_ne_zero]

private theorem base_integrand_eq (c t : ℝ) (s : ℂ) (ht : 0 < t) :
    (t : ℂ) ^ (s - 1) *
        (DedekindZetaZeroFree.thirdBesselRadialProfile c t : ℂ) =
      (DedekindZetaZeroFree.thirdBesselRadialProfile c t : ℂ) *
        (t : ℂ) ^ s / (t : ℂ) := by
  rw [Complex.cpow_sub _ _ (Complex.ofReal_ne_zero.mpr ht.ne'), Complex.cpow_one]
  ring

/-- Adapter from Axiom's `dt/t` integral to mathlib's `HasMellin`. -/
theorem thirdBessel_hasMellin (c : ℝ) (hc : 0 < c) (s : ℂ)
    (hs : -(5 / 6 : ℝ) < s.re) :
    HasMellin (fun t =>
      (DedekindZetaZeroFree.thirdBesselRadialProfile c t : ℂ)) s
      (((2 / c ^ 2 : ℝ) : ℂ) * (archScale c : ℂ) ^ s *
        Gamma (s + 5 / 6) * Gamma (s + 7 / 6)) := by
  constructor
  · have h := DedekindZetaZeroFree.radial_integrable c hc s hs
    change IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) *
      (DedekindZetaZeroFree.thirdBesselRadialProfile c t : ℂ)) (Ioi 0)
    apply h.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (base_integrand_eq c t s ht).symm
  · unfold mellin
    simp only [smul_eq_mul]
    calc
      _ = ∫ t : ℝ in Ioi 0,
          (DedekindZetaZeroFree.thirdBesselRadialProfile c t : ℂ) *
            (t : ℂ) ^ s / (t : ℂ) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        exact base_integrand_eq c t s ht
      _ = _ := DedekindZetaZeroFree.thirdBesselRadialProfile_mellin c hc s hs

private theorem shifted_gamma_value (c : ℝ) (hc : 0 < c)
    (m : ℤ) (τ : ℝ) (s : ℂ) :
    ((2 / c ^ 2 : ℝ) : ℂ) *
        (archScale c : ℂ) ^ (s + (archExponent m τ - 1)) *
        Gamma (s + (archExponent m τ - 1) + 5 / 6) *
        Gamma (s + (archExponent m τ - 1) + 7 / 6) =
      archDirectConstant c m τ * (archScale c : ℂ) ^ s *
        archGammaPair (archExponent m τ + s) := by
  have hA : (archScale c : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (archScale_pos c hc).ne'
  have hcoef : ((2 / c ^ 2 : ℝ) : ℂ) =
      (1 / 2 : ℂ) * (archScale c : ℂ) := by
    unfold archScale
    push_cast
    ring
  have hpow : (archScale c : ℂ) *
      (archScale c : ℂ) ^ (s + (archExponent m τ - 1)) =
        (archScale c : ℂ) ^ archExponent m τ * (archScale c : ℂ) ^ s := by
    calc
      _ = (archScale c : ℂ) ^ (1 : ℂ) *
          (archScale c : ℂ) ^ (s + (archExponent m τ - 1)) := by
        rw [Complex.cpow_one]
      _ = (archScale c : ℂ) ^ (1 + (s + (archExponent m τ - 1))) :=
        (Complex.cpow_add _ _ hA).symm
      _ = (archScale c : ℂ) ^ (archExponent m τ + s) := by
        congr 1
        ring
      _ = _ := Complex.cpow_add _ _ hA
  have hm : s + (archExponent m τ - 1) + 5 / 6 =
      archExponent m τ + s - 1 / 6 := by ring
  have hp : s + (archExponent m τ - 1) + 7 / 6 =
      archExponent m τ + s + 1 / 6 := by ring
  rw [hcoef, hm, hp]
  unfold archDirectConstant archGammaPair
  linear_combination (1 / 2 : ℂ) *
    Gamma (archExponent m τ + s - 1 / 6) *
    Gamma (archExponent m τ + s + 1 / 6) * hpow

/-- The genuine Mellin transform for every fixed integer angular weight and real twist. -/
theorem arch_direct_hasMellin (c : ℝ) (hc : 0 < c)
    (m : ℤ) (τ : ℝ) (s : ℂ)
    (hs : (1 / 6 : ℝ) - archWeight m < s.re) :
    HasMellin (archDirectProfile c m τ) s
      (archDirectConstant c m τ * (archScale c : ℂ) ^ s *
        archGammaPair (archExponent m τ + s)) := by
  have hs₀ : -(5 / 6 : ℝ) < (s + (archExponent m τ - 1)).re := by
    simp only [Complex.add_re, Complex.sub_re, archExponent_re, Complex.one_re]
    linarith
  have hbase := thirdBessel_hasMellin c hc (s + (archExponent m τ - 1)) hs₀
  constructor
  · change MellinConvergent (fun t : ℝ =>
      (t : ℂ) ^ (archExponent m τ - 1) *
        (DedekindZetaZeroFree.thirdBesselRadialProfile c t : ℂ)) s
    simpa only [smul_eq_mul] using
      (MellinConvergent.cpow_smul (f := fun t =>
        (DedekindZetaZeroFree.thirdBesselRadialProfile c t : ℂ))
        (s := s) (a := archExponent m τ - 1)).mpr hbase.1
  · calc
      mellin (archDirectProfile c m τ) s =
          mellin (fun t =>
            (DedekindZetaZeroFree.thirdBesselRadialProfile c t : ℂ))
            (s + (archExponent m τ - 1)) := by
        change mellin (fun t : ℝ =>
            (t : ℂ) ^ (archExponent m τ - 1) *
              (DedekindZetaZeroFree.thirdBesselRadialProfile c t : ℂ)) s =
          mellin (fun t : ℝ =>
            (DedekindZetaZeroFree.thirdBesselRadialProfile c t : ℂ))
            (s + (archExponent m τ - 1))
        simpa only [smul_eq_mul] using
          mellin_cpow_smul (fun t =>
            (DedekindZetaZeroFree.thirdBesselRadialProfile c t : ℂ))
            s (archExponent m τ - 1)
      _ = _ := hbase.2.trans (shifted_gamma_value c hc m τ s)

theorem arch_reflected_hasMellin (c : ℝ) (hc : 0 < c)
    (m : ℤ) (τ : ℝ) (s : ℂ)
    (hs : (1 / 6 : ℝ) - archWeight m < s.re) :
    HasMellin (archReflectedProfile c m τ) s
      (archReflectedConstant c m τ * (archScale c : ℂ) ^ s *
        archGammaPair (archExponent m (-τ) + s)) :=
  arch_direct_hasMellin c hc m (-τ) s hs

theorem archGammaPair_ne_zero (z : ℂ) (hz : (1 / 6 : ℝ) < z.re) :
    archGammaPair z ≠ 0 := by
  unfold archGammaPair
  apply mul_ne_zero
  · apply Complex.Gamma_ne_zero_of_re_pos
    have h : 0 < z.re - (1 / 6 : ℝ) := by linarith
    simpa using h
  · apply Complex.Gamma_ne_zero_of_re_pos
    have h : 0 < z.re + (1 / 6 : ℝ) := by linarith
    simpa using h

theorem archReflectedConstant_eq (c : ℝ) (hc : 0 < c) (m : ℤ) (τ : ℝ) :
    archReflectedConstant c m τ =
      archDirectConstant c m τ * archReflectionPhase c τ := by
  have hA : (archScale c : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (archScale_pos c hc).ne'
  unfold archReflectedConstant archDirectConstant archReflectionPhase
  rw [mul_assoc, ← Complex.cpow_add _ _ hA]
  congr 2
  simp only [archExponent, Complex.ofReal_neg]
  ring

theorem archDirectConstant_ne_zero (c : ℝ) (hc : 0 < c) (m : ℤ) (τ : ℝ) :
    archDirectConstant c m τ ≠ 0 := by
  apply mul_ne_zero (by norm_num : (1 / 2 : ℂ) ≠ 0)
  apply Complex.cpow_ne_zero_iff.mpr
  exact Or.inl (Complex.ofReal_ne_zero.mpr (archScale_pos c hc).ne')

theorem archReflectionPhase_ne_zero (c τ : ℝ) (hc : 0 < c) :
    archReflectionPhase c τ ≠ 0 := by
  apply Complex.cpow_ne_zero_iff.mpr
  exact Or.inl (Complex.ofReal_ne_zero.mpr (archScale_pos c hc).ne')

theorem archReflectionPhase_norm (c τ : ℝ) (hc : 0 < c) :
    ‖archReflectionPhase c τ‖ = 1 := by
  rw [archReflectionPhase, Complex.norm_cpow_eq_rpow_re_of_pos (archScale_pos c hc)]
  simp

/-- Exact reflection for the raw local profiles, including the fixed phase. -/
theorem arch_reflected_mellin (c : ℝ) (hc : 0 < c)
    (m : ℤ) (τ : ℝ) (s : ℂ)
    (hleft : (1 / 6 : ℝ) - archWeight m < s.re)
    (hright : s.re < archWeight m - (1 / 6 : ℝ)) :
    mellin (archReflectedProfile c m τ) s =
      mellin (archDirectProfile c m τ) (-s) *
        (archScale c : ℂ) ^ (2 * s) * archReflectionPhase c τ *
        (archGammaPair (archExponent m (-τ) + s) /
          archGammaPair (archExponent m τ + (-s))) := by
  have hneg : (1 / 6 : ℝ) - archWeight m < (-s).re := by
    simp only [Complex.neg_re]
    linarith
  have hden : archGammaPair (archExponent m τ + (-s)) ≠ 0 := by
    apply archGammaPair_ne_zero
    simp only [Complex.add_re, archExponent_re, Complex.neg_re]
    linarith
  have hA : (archScale c : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (archScale_pos c hc).ne'
  have hpow : (archScale c : ℂ) ^ (-s) * (archScale c : ℂ) ^ (2 * s) =
      (archScale c : ℂ) ^ s := by
    rw [← Complex.cpow_add _ _ hA]
    congr 1
    ring
  rw [(arch_reflected_hasMellin c hc m τ s hleft).2,
    (arch_direct_hasMellin c hc m τ (-s) hneg).2,
    archReflectedConstant_eq c hc m τ]
  calc
    archDirectConstant c m τ * archReflectionPhase c τ *
        (archScale c : ℂ) ^ s * archGammaPair (archExponent m (-τ) + s) =
      archDirectConstant c m τ * archReflectionPhase c τ *
        ((archScale c : ℂ) ^ (-s) * (archScale c : ℂ) ^ (2 * s)) *
        archGammaPair (archExponent m (-τ) + s) := by rw [hpow]
    _ = _ := by field_simp [hden]

/-- Optional normalization which removes only the fixed unit-modulus phase. -/
def archNormalizedReflectedProfile (c : ℝ) (m : ℤ) (τ : ℝ) (t : ℝ) : ℂ :=
  (archReflectionPhase c τ)⁻¹ * archReflectedProfile c m τ t

/-- The phase-free version uses the explicitly normalized reflected profile. -/
theorem arch_normalized_reflected_mellin (c : ℝ) (hc : 0 < c)
    (m : ℤ) (τ : ℝ) (s : ℂ)
    (hleft : (1 / 6 : ℝ) - archWeight m < s.re)
    (hright : s.re < archWeight m - (1 / 6 : ℝ)) :
    mellin (archNormalizedReflectedProfile c m τ) s =
      mellin (archDirectProfile c m τ) (-s) * (archScale c : ℂ) ^ (2 * s) *
        (archGammaPair (archExponent m (-τ) + s) /
          archGammaPair (archExponent m τ + (-s))) := by
  have hphase := archReflectionPhase_ne_zero c τ hc
  have hM : mellin (archNormalizedReflectedProfile c m τ) s =
      (archReflectionPhase c τ)⁻¹ * mellin (archReflectedProfile c m τ) s := by
    change mellin (fun t : ℝ =>
        (archReflectionPhase c τ)⁻¹ * archReflectedProfile c m τ t) s =
      (archReflectionPhase c τ)⁻¹ * mellin (archReflectedProfile c m τ) s
    simpa only [smul_eq_mul] using
      mellin_const_smul (archReflectedProfile c m τ) s (archReflectionPhase c τ)⁻¹
  rw [hM, arch_reflected_mellin c hc m τ s hleft hright]
  calc
    _ = ((archReflectionPhase c τ)⁻¹ * archReflectionPhase c τ) *
      (mellin (archDirectProfile c m τ) (-s) * (archScale c : ℂ) ^ (2 * s) *
        (archGammaPair (archExponent m (-τ) + s) /
          archGammaPair (archExponent m τ + (-s)))) := by ring
    _ = _ := by rw [inv_mul_cancel₀ hphase, one_mul]

#print axioms thirdBessel_hasMellin
#print axioms arch_direct_hasMellin
#print axioms arch_reflected_hasMellin
#print axioms arch_reflected_mellin
#print axioms arch_normalized_reflected_mellin

end HeckeSkeleton.ThetaLocal
