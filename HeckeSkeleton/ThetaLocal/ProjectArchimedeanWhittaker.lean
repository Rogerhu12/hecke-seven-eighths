import HeckeSkeleton.ThetaLocal.ProjectArchimedean
import HeckeSkeleton.ThetaLocal.ComplexProfileBridge

/-!
# Actual Hecke parameters in the complex Whittaker model

The vectors are the existing `archRootVector` in Axiom's concrete complex
representation. The Weyl equality is a vector equality, and the two profile
identifications are specializations of the previously proved Whittaker formulas.
The radial exponents are written using the project's `archRadial`, so their
opposite signs are visible at the point where the actual vectors enter Mellin
reflection. This file does not construct a global theta representation.
-/

noncomputable section
set_option autoImplicit false

namespace HeckeSkeleton.ThetaLocal.Project

open NumberField HeckeGeneral.Characters HeckeGeneral.ThetaSkeleton.Global
open DedekindZetaZeroFree
open KPCplxCharacterHaar KPCplxActualImage KPCplxRootDerivativeVectors KPCplxBessel

variable (K : Type) [Field K] [NumberField K]

/-- The inverse actual radial character has exponent `I * archRadial`. -/
theorem inverse_actual_radial_character (θ : HeckeCharacter K)
    (v : {v : InfinitePlace K // v.IsComplex}) (t : ℝ) (ht : 0 < t) :
    ((Circle.exp (heckeComplexParameter K v.val v.property θ * Real.log t) : Circle) : ℂ)⁻¹ =
      (t : ℂ) ^ (Complex.I * archRadial K θ v) := by
  rw [Circle.coe_exp, ← Complex.exp_neg,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr ht.ne'),
    ← Complex.ofReal_log ht.le]
  congr 1
  unfold archRadial
  push_cast
  ring

/-- The actual local Hecke character, including its angular factor, in inverse form. -/
theorem inverse_actual_complex_character (θ : HeckeCharacter K)
    (v : {v : InfinitePlace K // v.IsComplex}) (y : ℂˣ) :
    ((complexHeckeComponent K v.val v.property θ y : Circle) : ℂ)⁻¹ =
      omegaPlus y ^ (-heckeComplexWeight K v.val v.property θ) *
        ((radius y ^ 2 : ℝ) : ℂ) ^ (Complex.I * archRadial K θ v) := by
  have hr : 0 < radius y := norm_pos_iff.mpr (Units.ne_zero y)
  rw [heckeComplexComponent_formula, Circle.coe_mul, Circle.coe_zpow, mul_inv_rev]
  change
    (((Circle.exp (heckeComplexParameter K v.val v.property θ *
      Real.log (radius y ^ 2)) : Circle) : ℂ)⁻¹) *
        (((complexPhase y : Circle) : ℂ) ^ heckeComplexWeight K v.val v.property θ)⁻¹ =
      omegaPlus y ^ (-heckeComplexWeight K v.val v.property θ) *
        ((radius y ^ 2 : ℝ) : ℂ) ^ (Complex.I * archRadial K θ v)
  rw [inverse_actual_radial_character K θ v (radius y ^ 2) (sq_pos_of_pos hr)]
  rw [← zpow_neg]
  simp only [complexPhase_val, omegaPlus, radius]
  ring

/-- The positive form follows from the actual inverse-character identity. -/
theorem actual_complex_character (θ : HeckeCharacter K)
    (v : {v : InfinitePlace K // v.IsComplex}) (y : ℂˣ) :
    ((complexHeckeComponent K v.val v.property θ y : Circle) : ℂ) =
      omegaPlus y ^ heckeComplexWeight K v.val v.property θ *
        ((radius y ^ 2 : ℝ) : ℂ) ^ (-Complex.I * archRadial K θ v) := by
  have h := inverse_actual_complex_character K θ⁻¹ v y
  have hinv : complexHeckeComponent K v.val v.property θ⁻¹ y =
      (complexHeckeComponent K v.val v.property θ y)⁻¹ := rfl
  rw [hinv, Circle.coe_inv, inv_inv] at h
  simpa only [heckeComplexWeight_inv, neg_neg, archRadial_inv,
    Complex.ofReal_neg, mul_neg, neg_mul] using h

/-- The Weyl translate of the actual-weight root vector has the inverse-character weight. -/
theorem actualHeckeRootVector_weyl (θ : HeckeCharacter K)
    (v : {v : InfinitePlace K // v.IsComplex}) (c : ℝ) (β : ℂˣ) :
    imageAction β (Matrix.ProjGenLinGroup.mk weyl)
        (archRootVector c β (heckeComplexWeight K v.val v.property θ)) =
      archRootVector c β (heckeComplexWeight K v.val v.property θ⁻¹) := by
  rw [heckeComplexWeight_inv]
  exact weyl_archRootVector c β _

/-- Removing the direct angular character leaves exactly the actual direct profile. -/
theorem directProfile_from_actual_whittaker (θ : HeckeCharacter K)
    (v : {v : InfinitePlace K // v.IsComplex}) (c : ℝ) (hc : 0 < c)
    (β : ℂˣ) (hβ : (β : ℂ) = (c : ℂ)) (y : ℂˣ) :
    whittakerValue β (archRootVector c β (heckeComplexWeight K v.val v.property θ)) y *
        omegaPlus y ^ (-heckeComplexWeight K v.val v.property θ) *
        ((radius y ^ 2 : ℝ) : ℂ) ^ (Complex.I * archRadial K θ v) =
      directProfile K θ v c (radius y ^ 2) := by
  have hexp : Complex.I * (archRadial K θ v : ℂ) =
      -(heckeComplexParameter K v.val v.property θ : ℂ) * Complex.I := by
    simp only [archRadial, Complex.ofReal_neg]
    ring
  rw [hexp]
  exact direct_profile_from_whittaker c hc β hβ
    (heckeComplexWeight K v.val v.property θ)
    (heckeComplexParameter K v.val v.property θ) y

/-- The actual Weyl translate gives the reflected profile with the opposite radial sign. -/
theorem reflectedProfile_from_actual_whittaker (θ : HeckeCharacter K)
    (v : {v : InfinitePlace K // v.IsComplex}) (c : ℝ) (hc : 0 < c)
    (β : ℂˣ) (hβ : (β : ℂ) = (c : ℂ)) (y : ℂˣ) :
    whittakerValue β
        (imageAction β (Matrix.ProjGenLinGroup.mk weyl)
          (archRootVector c β (heckeComplexWeight K v.val v.property θ))) y *
        omegaPlus y ^ heckeComplexWeight K v.val v.property θ *
        ((radius y ^ 2 : ℝ) : ℂ) ^ (-Complex.I * archRadial K θ v) =
      reflectedProfile K θ v c (radius y ^ 2) := by
  have h := reflected_profile_from_whittaker c hc β hβ
    (heckeComplexWeight K v.val v.property θ)
    (heckeComplexParameter K v.val v.property θ) y
  simpa only [reflectedProfile, archRadial, Complex.ofReal_neg, neg_mul_neg, mul_comm]
    using h

/-- Direct Whittaker value times the inverse actual local Hecke character. -/
theorem directProfile_from_whittaker_character (θ : HeckeCharacter K)
    (v : {v : InfinitePlace K // v.IsComplex}) (c : ℝ) (hc : 0 < c)
    (β : ℂˣ) (hβ : (β : ℂ) = (c : ℂ)) (y : ℂˣ) :
    whittakerValue β (archRootVector c β (heckeComplexWeight K v.val v.property θ)) y *
        ((complexHeckeComponent K v.val v.property θ y : Circle) : ℂ)⁻¹ =
      directProfile K θ v c (radius y ^ 2) := by
  rw [inverse_actual_complex_character, ← mul_assoc]
  exact directProfile_from_actual_whittaker K θ v c hc β hβ y

/-- The Weyl translate times the actual local Hecke character gives the reflected profile. -/
theorem reflectedProfile_from_whittaker_character (θ : HeckeCharacter K)
    (v : {v : InfinitePlace K // v.IsComplex}) (c : ℝ) (hc : 0 < c)
    (β : ℂˣ) (hβ : (β : ℂ) = (c : ℂ)) (y : ℂˣ) :
    whittakerValue β
        (imageAction β (Matrix.ProjGenLinGroup.mk weyl)
          (archRootVector c β (heckeComplexWeight K v.val v.property θ))) y *
        ((complexHeckeComponent K v.val v.property θ y : Circle) : ℂ) =
      reflectedProfile K θ v c (radius y ^ 2) := by
  rw [actual_complex_character, ← mul_assoc]
  exact reflectedProfile_from_actual_whittaker K θ v c hc β hβ y


end HeckeSkeleton.ThetaLocal.Project
