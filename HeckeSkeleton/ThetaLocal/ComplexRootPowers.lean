import DedekindZetaZeroFree.Theta.Whittaker.ComplexRootDerivativeVectors
import HeckeSkeleton.ThetaLocal.RootIterates

/-!
Actual repeated upper-root vectors in Axiom's complex local theta model.

The Whittaker formulas below use Axiom's genuine derived representation.  This
file proves the values of both strings of root vectors.  `ComplexWeylPowers`
proves their Weyl interchange through the explicit highest and lowest
harmonics; `RootIterates` also records the general operator-algebra argument.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace HeckeSkeleton.ThetaLocal

open DedekindZetaZeroFree
open KPCplxActualImage KPCplxRootDerivativeVectors KPCplxBessel

/-- Normalize the holomorphic root so its Whittaker multiplier is `y`. -/
def normalizedRootPlus (c : ℝ) (β : ℂˣ) (h : Theta β) : Theta β :=
  (2 / (Complex.I * (c : ℂ))) • dPiComplexUpperRoot β Z_plus h

/-- Normalize the antiholomorphic root so its Whittaker multiplier is `conj y`. -/
def normalizedRootMinus (c : ℝ) (β : ℂˣ) (h : Theta β) : Theta β :=
  (2 / (Complex.I * (c : ℂ))) • dPiComplexUpperRoot β Z_minus h

/-- The actual vector `E^n φ°`. -/
def higherPlus (c : ℝ) (β : ℂˣ) (n : ℕ) : Theta β :=
  rootIterate (normalizedRootPlus c β) n (vZero c β)

/-- The actual vector `Ebar^n φ°`. -/
def higherMinus (c : ℝ) (β : ℂˣ) (n : ℕ) : Theta β :=
  rootIterate (normalizedRootMinus c β) n (vZero c β)

private theorem local_whittaker_smul (β : ℂˣ) (a : ℂ) (h : Theta β) (y : ℂˣ) :
    whittakerValue β (a • h) y = a * whittakerValue β h y := by
  simp [whittakerValue, imageAction_smul]

theorem whittaker_normalizedRootPlus (c : ℝ) (hc : 0 < c)
    (β : ℂˣ) (hβ : (β : ℂ) = (c : ℂ)) (h : Theta β) (y : ℂˣ) :
    whittakerValue β (normalizedRootPlus c β h) y =
      (y : ℂ) * whittakerValue β h y := by
  rw [normalizedRootPlus, local_whittaker_smul,
    (whittaker_complexUpperRootDerivatives c hc β hβ h y).1]
  have hc₀ : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  field_simp [hc₀, Complex.I_ne_zero] <;> ring

theorem whittaker_normalizedRootMinus (c : ℝ) (hc : 0 < c)
    (β : ℂˣ) (hβ : (β : ℂ) = (c : ℂ)) (h : Theta β) (y : ℂˣ) :
    whittakerValue β (normalizedRootMinus c β h) y =
      star (y : ℂ) * whittakerValue β h y := by
  rw [normalizedRootMinus, local_whittaker_smul,
    (whittaker_complexUpperRootDerivatives c hc β hβ h y).2]
  have hc₀ : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  field_simp [hc₀, Complex.I_ne_zero] <;> ring

theorem whittaker_higherPlus (c : ℝ) (hc : 0 < c)
    (β : ℂˣ) (hβ : (β : ℂ) = (c : ℂ)) (n : ℕ) (y : ℂˣ) :
    whittakerValue β (higherPlus c β n) y =
      (y : ℂ) ^ n *
        ((radius y * besselKThird (c * radius y) : ℝ) : ℂ) := by
  unfold higherPlus
  induction n with
  | zero =>
    simpa only [rootIterate, pow_zero, one_mul] using whittaker_vZero c hc β hβ y
  | succ n ih =>
    rw [rootIterate, whittaker_normalizedRootPlus c hc β hβ, ih, pow_succ]
    ring

theorem whittaker_higherMinus (c : ℝ) (hc : 0 < c)
    (β : ℂˣ) (hβ : (β : ℂ) = (c : ℂ)) (n : ℕ) (y : ℂˣ) :
    whittakerValue β (higherMinus c β n) y =
      star (y : ℂ) ^ n *
        ((radius y * besselKThird (c * radius y) : ℝ) : ℂ) := by
  unfold higherMinus
  induction n with
  | zero =>
    simpa only [rootIterate, pow_zero, one_mul] using whittaker_vZero c hc β hβ y
  | succ n ih =>
    rw [rootIterate, whittaker_normalizedRootMinus c hc β hβ, ih, pow_succ]
    ring

theorem whittaker_higherPlus_polar (c : ℝ) (hc : 0 < c)
    (β : ℂˣ) (hβ : (β : ℂ) = (c : ℂ)) (n : ℕ) (y : ℂˣ) :
    whittakerValue β (higherPlus c β n) y =
      ((radius y ^ (n + 1) : ℝ) : ℂ) * omegaPlus y ^ n *
        (besselKThird (c * radius y) : ℂ) := by
  rw [whittaker_higherPlus c hc β hβ n y]
  have hr : (radius y : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (Units.ne_zero y))
  have he : (y : ℂ) = (radius y : ℂ) * omegaPlus y := by
    unfold omegaPlus
    field_simp [hr]
  rw [he, mul_pow]
  push_cast
  rw [pow_succ]
  ring

theorem whittaker_higherMinus_polar (c : ℝ) (hc : 0 < c)
    (β : ℂˣ) (hβ : (β : ℂ) = (c : ℂ)) (n : ℕ) (y : ℂˣ) :
    whittakerValue β (higherMinus c β n) y =
      ((radius y ^ (n + 1) : ℝ) : ℂ) * omegaMinus y ^ n *
        (besselKThird (c * radius y) : ℂ) := by
  rw [whittaker_higherMinus c hc β hβ n y]
  have hr : (radius y : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (Units.ne_zero y))
  have he : star (y : ℂ) = (radius y : ℂ) * omegaMinus y := by
    unfold omegaMinus
    field_simp [hr]
  rw [he, mul_pow]
  push_cast
  rw [pow_succ]
  ring

theorem omegaMinus_eq_inv (y : ℂˣ) : omegaMinus y = (omegaPlus y)⁻¹ := by
  have hr : (radius y : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (Units.ne_zero y))
  have hp : omegaPlus y ≠ 0 := div_ne_zero (Units.ne_zero y) hr
  have hm : omegaPlus y * omegaMinus y = 1 := by
    unfold omegaPlus omegaMinus
    field_simp [hr]
    simpa only [radius, Complex.star_def] using Complex.mul_conj' (y : ℂ)
  apply mul_left_cancel₀ hp
  rw [hm, mul_inv_cancel₀ hp]

#print axioms whittaker_normalizedRootPlus
#print axioms whittaker_normalizedRootMinus
#print axioms whittaker_higherPlus
#print axioms whittaker_higherMinus
#print axioms whittaker_higherPlus_polar
#print axioms whittaker_higherMinus_polar

end HeckeSkeleton.ThetaLocal
