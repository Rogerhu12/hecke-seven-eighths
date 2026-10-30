import HeckeSkeleton.ThetaLocal.ArchimedeanMellin
import HeckeSkeleton.ThetaLocal.ComplexWeylPowers

/-! Identification of the actual local Whittaker vectors with the two
Mellin profiles, including both signs of the fixed radial character. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace HeckeSkeleton.ThetaLocal

open DedekindZetaZeroFree
open KPCplxCharacterHaar KPCplxActualImage KPCplxRootDerivativeVectors KPCplxBessel

/-- Axiom's two integral realizations of the same order-one-third Bessel function. -/
theorem besselKThird_eq_KThird (x : ℝ) (hx : 0 < x) :
    besselKThird x = KThird x := by
  have hK : KThird x = modifiedBesselK (1 / 3) x := by
    rw [KThird_eq_integral x hx]
    unfold modifiedBesselK thirdBesselSchlafliIntegrand
    congr 1
    funext t
    congr 2
    ring
  rw [hK]
  exact besselKThird_eq_modifiedBesselK x hx

/-- The complex norm is the square of the ordinary radius. -/
theorem archDirectProfile_radius (c : ℝ) (m : ℤ) (τ r : ℝ) (hr : 0 < r) :
    archDirectProfile c m τ (r ^ 2) =
      (r : ℂ) ^ (m.natAbs + 1) *
        ((r ^ 2 : ℝ) : ℂ) ^ (-(τ : ℂ) * Complex.I) *
        (KThird (c * r) : ℂ) := by
  rw [archDirectProfile_eq c m τ (r ^ 2) (sq_pos_of_pos hr),
    Real.sqrt_sq_eq_abs, abs_of_pos hr]
  have he : archExponent m τ =
      (archWeight m : ℂ) + (-(τ : ℂ) * Complex.I) := by
    unfold archExponent
    ring
  rw [he, Complex.cpow_add _ _
    (Complex.ofReal_ne_zero.mpr (sq_pos_of_pos hr).ne')]
  have hp : ((r ^ 2 : ℝ) : ℂ) ^ (archWeight m : ℂ) =
      (r : ℂ) ^ (m.natAbs + 1) := by
    have h := Complex.cpow_mul_ofReal_nonneg hr.le (2 : ℝ) (archWeight m : ℂ)
    have harg : ((2 : ℝ) : ℂ) * (archWeight m : ℂ) =
        ((m.natAbs + 1 : ℕ) : ℂ) := by
      unfold archWeight
      push_cast
      ring
    rw [harg, Complex.cpow_natCast] at h
    simpa only [Real.rpow_two] using h.symm
  rw [hp]

/-- Removing the direct angular character and retaining the inverse radial character. -/
theorem direct_profile_from_whittaker (c : ℝ) (hc : 0 < c)
    (β : ℂˣ) (hβ : (β : ℂ) = (c : ℂ)) (m : ℤ) (τ : ℝ) (y : ℂˣ) :
    whittakerValue β (archRootVector c β m) y * omegaPlus y ^ (-m) *
      ((radius y ^ 2 : ℝ) : ℂ) ^ (-(τ : ℂ) * Complex.I) =
        archDirectProfile c m τ (radius y ^ 2) := by
  have hr : 0 < radius y := norm_pos_iff.mpr (Units.ne_zero y)
  have hr₀ : (radius y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hω : omegaPlus y ≠ 0 := div_ne_zero (Units.ne_zero y) hr₀
  have hcancel : omegaPlus y ^ m * omegaPlus y ^ (-m) = 1 := by
    rw [zpow_neg, mul_inv_cancel₀ (zpow_ne_zero _ hω)]
  rw [whittaker_archRootVector c hc β hβ m y,
    besselKThird_eq_KThird _ (mul_pos hc hr), archDirectProfile_radius c m τ (radius y) hr]
  push_cast
  calc
    _ = ((radius y : ℂ) ^ (m.natAbs + 1) *
        ((radius y : ℂ) ^ 2) ^ (-(τ : ℂ) * Complex.I) *
        (KThird (c * radius y) : ℂ)) *
        (omegaPlus y ^ m * omegaPlus y ^ (-m)) := by ring
    _ = _ := by rw [hcancel, mul_one]

/-- The actual Weyl translate gives the reflected profile and the positive radial twist. -/
theorem reflected_profile_from_whittaker (c : ℝ) (hc : 0 < c)
    (β : ℂˣ) (hβ : (β : ℂ) = (c : ℂ)) (m : ℤ) (τ : ℝ) (y : ℂˣ) :
    whittakerValue β
        (imageAction β (Matrix.ProjGenLinGroup.mk weyl) (archRootVector c β m)) y *
      omegaPlus y ^ m * ((radius y ^ 2 : ℝ) : ℂ) ^ ((τ : ℂ) * Complex.I) =
        archReflectedProfile c m τ (radius y ^ 2) := by
  rw [weyl_archRootVector]
  simpa [archReflectedProfile, archDirectProfile, archExponent, archWeight] using
    direct_profile_from_whittaker c hc β hβ (-m) (-τ) y

#print axioms besselKThird_eq_KThird
#print axioms direct_profile_from_whittaker
#print axioms reflected_profile_from_whittaker

end HeckeSkeleton.ThetaLocal
