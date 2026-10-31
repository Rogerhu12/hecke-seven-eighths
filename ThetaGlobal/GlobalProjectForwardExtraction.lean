import ThetaGlobal.GlobalProjectDigitProduct
import DedekindZetaZeroFree.Theta.Whittaker.RationalDiagonalFactorization

/-!
# Actual forward extraction for an arbitrary frozen tensor

The rational diagonal is split in the restricted product itself.  The
exterior reference vector contributes its genuine spherical factors;
the S-background is the Fourier coefficient of the same frozen tensor.
The diagonal Hilbert factor is retained until the actual support of the
S-profile forces it to be one.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section

namespace ThetaGlobal.GlobalProjectForwardExtraction

open NumberField MeasureTheory DedekindZetaZeroFree DedekindZetaZeroFree.MomentSources
open DedekindZetaZeroFree.OrbitExpansion
open ThetaGlobal.GlobalProjectExterior
open scoped NumberField Classical BigOperators

variable {F : Type} [Field F] [NumberField F]
  {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
  (R : PrincipalMellin.ActualRecipe S η)
  {Q : AdmissibleFlatSources R} {T : Realization R Q}
  (D : SourceFactorization R Q T)

local notation "V" => actualLocal R D.finiteData
local notation "k" => QuotientGroup.mk' R.A.sixthPowers

def directProfile (seed : ∀ p : D.bad, V p) (y : R.A.G) : ℂ :=
  fourier R Q.dq (badVector R D seed).val (diagonal R y)

theorem rational_diagonal (seed : ∀ p : D.bad, V p) (x : Fˣ) (y : R.A.G) :
    Function.HasFiniteMulSupport (D.exteriorValue R · x) ∧
    fourier R Q.dq (badVector R D seed).val
      (KPRationalAdelicSplitting.pglA F R.A.zeta12 R.A.primitive_zeta12
        (Units.map (algebraMap F (KPAdeles F)).toMonoidHom x) * diagonal R y) =
      (∏ᶠ p : ThetaBranch.ExteriorPrime R.A, D.exteriorValue R p x) *
        fourier R Q.dq (badVector R D seed).val
          (diagonal R (R.A.diagonal x) * diagonal R y) := by
  let b := KPRationalAdelicSplitting.ATuple F R.A.zeta12 R.A.primitive_zeta12
    (Units.map (algebraMap F (KPAdeles F)).toMonoidHom x) * sDiagonalTuple R y
  let a := exteriorRestriction R b
  let g := sRestriction R b
  obtain ⟨P, hP⟩ := exterior_tuple_finite_exceptional R a
  have h := GlobalProjectExteriorExtraction.fourier_exterior_tuple R D seed a g
    (by intro p; simp [g, sRestriction, p.property])
    (by intro w hw; exact if_neg hw) P hP
  have he (p : ThetaBranch.ExteriorPrime R.A) :
      exteriorSlotValue R D p.val (a (Sum.inr p.val)) = D.exteriorValue R p x := by
    have ha : a (Sum.inr p.val) = b (Sum.inr p.val) := by simp [a, p.property]
    rw [ha]
    dsimp only [b]
    rw [RestrictedProduct.mul_apply, sDiagonal_exterior R y p.val p.property,
      mul_one, rationalATuple_eval]
    exact OrbitFrequencies.exterior_diagonal_slot R D p x
  simp_rw [he] at h
  refine ⟨h.1, ?_⟩
  have hb := congrArg (restrictedLift R) (splitTuple R b)
  rw [map_mul] at hb
  change fourier R Q.dq (badVector R D seed).val (restrictedLift R b) = _
  rw [hb, h.2]
  congr 1
  dsimp only [g, b]
  rw [map_mul, sRestriction_rational, sRestriction_diagonal, map_mul]
  rfl

theorem forward_single (hR : RootAligned R) (seed : ∀ p : D.bad, V p)
    (x : Fˣ) (y : R.A.G) :
    GlobalCoreSource.rationalPeriod T (badVector R D seed) (x : F) (diagonal R y) =
      (∏ᶠ p : ThetaBranch.ExteriorPrime R.A, D.exteriorValue R p x) *
        GlobalProjectConvention.paperHilbert R (k (R.A.diagonal x)) (k y) ^ 2 *
          directProfile R D seed (R.A.diagonal x * y) := by
  rw [GlobalProjectRationalDilation.rationalPeriod_eq_fourier R,
    (rational_diagonal R D seed x y).2]
  have h := GlobalProjectCoreEquivariance.fourier_diagonal_mul R hR
    (badVector R D seed) (R.A.diagonal x) y 1
  simp only [mul_one] at h
  rw [h, GlobalProjectConvention.paperHilbert_on_representatives]
  simp only [inv_pow, directProfile, mul_assoc]

theorem forward_average (hR : RootAligned R) (seed : ∀ p : D.bad, V p)
    (m : ThetaReflectionData.Row R.A)
    (c : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property) → ℂ)
    (x : Fˣ) (y : R.A.G) :
    (∑ d, c d * GlobalCoreSource.rationalPeriod T (badVector R D seed) (x : F)
      (signedArgument R m true y d)) =
      (GlobalProjectDigitProduct.forwardCoefficient R m c x *
        ∏ᶠ p : ThetaBranch.ExteriorPrime R.A, D.exteriorValue R p x) *
        GlobalProjectConvention.paperHilbert R (k (R.A.diagonal x)) (k y) ^ 2 *
          directProfile R D seed (R.A.diagonal x * y) := by
  rw [GlobalProjectCoreEquivariance.forward_digit_average R,
    forward_single R D hR seed]
  simp only [GlobalProjectDigitProduct.forwardCoefficient, mul_assoc]

/-- A profile supported on the identity sixth-power class kills the
forward cocycle.  This is the support supplied by the actual finite
cutoff vectors; no isotropy convention is silently imposed. -/
theorem hilbert_mul_of_class_support (f : R.A.G → ℂ)
    (hf : ∀ z, k z ≠ 1 → f z = 0) (a y : R.A.G) :
    GlobalProjectConvention.paperHilbert R (k a) (k y) ^ 2 * f (a * y) =
      f (a * y) := by
  by_cases hz : k (a * y) = 1
  · have hy : k y = (k a)⁻¹ := by
      apply eq_inv_of_mul_eq_one_right
      simpa only [map_mul] using hz
    rw [hy, GlobalProjectConvention.paperHilbert, map_inv,
      R.A.H_S6_alternating]
    simp
  · rw [hf (a * y) hz, mul_zero]

theorem forward_weighted_average (hR : RootAligned R) (seed : ∀ p : D.bad, V p)
    (hsupport : ∀ z, k z ≠ 1 → directProfile R D seed z = 0)
    (m : ThetaReflectionData.Row R.A)
    (c : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property) → ℂ)
    (L : R.A.G →* ℂ) (B : Subgroup R.A.V) (x : Fˣ) (y : R.A.G) :
    GlobalProjectUnfolding.weight R L B y *
      (∑ d, c d * GlobalCoreSource.rationalPeriod T (badVector R D seed) (x : F)
        (signedArgument R m true y d)) =
      (GlobalProjectDigitProduct.forwardCoefficient R m c x *
        ∏ᶠ p : ThetaBranch.ExteriorPrime R.A, D.exteriorValue R p x) *
        GlobalProjectUnfolding.weight R L B y *
          directProfile R D seed (R.A.diagonal x * y) := by
  rw [forward_average R D hR seed]
  rw [mul_assoc _ (GlobalProjectConvention.paperHilbert R _ _ ^ 2),
    hilbert_mul_of_class_support R _ hsupport]
  ring

end ThetaGlobal.GlobalProjectForwardExtraction
