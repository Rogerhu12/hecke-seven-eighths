import ThetaGlobal.GlobalProjectCoreEquivariance
import ThetaGlobal.GlobalProjectExteriorExtraction
import ThetaGlobal.GlobalProjectUnfolding
import DedekindZetaZeroFree.Theta.Periods.ExteriorDigitExtraction

/-!
# Actual signed digit extraction for the replacement tensor

This is the pointwise source identity preceding arithmetic reindexing.
The local factors are the exact exterior reference-vector periods from
the repository.  The S-background is the Fourier coefficient of the
same arbitrary frozen pure tensor.  All digit weights are independent of
the auxiliary row's exponents, so marks and punctures may be inserted
without modifying that row or the arithmetic choice.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4000
noncomputable section

namespace ThetaGlobal.GlobalProjectSignedExtraction

open NumberField MeasureTheory DedekindZetaZeroFree DedekindZetaZeroFree.MomentSources
open DedekindZetaZeroFree.OrbitExpansion
open ThetaGlobal.GlobalProjectExterior
open scoped NumberField Classical BigOperators

variable {F : Type} [Field F] [NumberField F]
  {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
  (R : PrincipalMellin.ActualRecipe S η)
  {Q : AdmissibleFlatSources R} {T : Realization R Q}

theorem sReverseTuple_period (f : sameResidueModule T)
    (hf : FullExteriorInvariant R f.val)
    (x : Fˣ) (y : R.A.G) (m : ThetaReflectionData.Row R.A)
    (d : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property)) :
    fourier R Q.dq f.val (restrictedLift R (sRestriction R (reverseTuple R x y m d))) =
      fourier R Q.dq f.val
        (diagonal R (R.A.diagonal x) * KPRationalAdelicSplitting.pglW F R.A.zeta12
          R.A.primitive_zeta12 * diagonal R y) := by
  rw [sReverseTuple_eq, map_mul, map_mul]
  have hW : KPRationalAdelicSplitting.WTuple F R.A.zeta12 R.A.primitive_zeta12 =
      sWeylTuple R * exteriorWeylTuple R := by simp [exteriorWeylTuple]
  have hc := (exteriorWeyl_commute_diagonal R y).map (restrictedLift R)
  have he : diagonal R (R.A.diagonal x) *
      KPRationalAdelicSplitting.pglW F R.A.zeta12 R.A.primitive_zeta12 * diagonal R y =
      (restrictedLift R (sDiagonalTuple R (R.A.diagonal x)) *
        restrictedLift R (sWeylTuple R) * restrictedLift R (sDiagonalTuple R y)) *
          restrictedLift R (exteriorWeylTuple R) := by
    change restrictedLift R (sDiagonalTuple R (R.A.diagonal x)) *
      restrictedLift R (KPRationalAdelicSplitting.WTuple F R.A.zeta12 R.A.primitive_zeta12) *
        restrictedLift R (sDiagonalTuple R y) = _
    rw [hW, map_mul, mul_assoc, mul_assoc, hc.eq, ← mul_assoc, ← mul_assoc]
  rw [he]
  symm
  unfold MomentSources.fourier
  apply integral_congr_ae
  filter_upwards [] with q
  rw [← mul_assoc]
  exact congrArg (fun z : ℂ => z * star (adelicTraceQuotientCharacter F q : ℂ))
    (hf (exteriorWeylTuple R) (exteriorWeylTuple_mem R) _)

variable (D : SourceFactorization R Q T)
local notation "V" => actualLocal R D.finiteData

theorem reverseTuple_period (seed : ∀ p : D.bad, V p)
    (x : Fˣ) (y : R.A.G) (m : ThetaReflectionData.Row R.A)
    (d : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property)) :
    Function.HasFiniteMulSupport (OrbitFrequencies.exteriorDigitValue R D m x d) ∧
    fourier R Q.dq (badVector R D seed).val (restrictedLift R (reverseTuple R x y m d)) =
      (∏ᶠ p, OrbitFrequencies.exteriorDigitValue R D m x d p) *
      fourier R Q.dq (badVector R D seed).val
        (diagonal R (R.A.diagonal x) *
          KPRationalAdelicSplitting.pglW F R.A.zeta12 R.A.primitive_zeta12 * diagonal R y) := by
  let b := reverseTuple R x y m d
  let a := exteriorRestriction R b
  let g := sRestriction R b
  obtain ⟨P, hP⟩ := exterior_tuple_finite_exceptional R a
  have h := GlobalProjectExteriorExtraction.fourier_exterior_tuple R D seed a g
    (by intro p; simp [g, sRestriction, p.property])
    (by intro w hw; exact ite_eq_right hw) P hP
  have he (p : ThetaBranch.ExteriorPrime R.A) :
      exteriorSlotValue R D p.val (a (Sum.inr p.val)) =
        OrbitFrequencies.exteriorDigitValue R D m x d p := by
    have ha : a (Sum.inr p.val) = b (Sum.inr p.val) := by simp [a, p.property]
    rw [ha]
    dsimp only [b, OrbitFrequencies.exteriorDigitValue]
    rw [reverseTuple_exterior, reverseTuple_exterior]
  simp_rw [he] at h
  refine ⟨h.1, ?_⟩
  have hb := congrArg (restrictedLift R) (splitTuple R b)
  rw [map_mul] at hb
  rw [hb, h.2]
  congr 1
  exact sReverseTuple_period R (badVector R D seed)
    (badVector_fullExteriorInvariant R D seed) x y m d

def reverseCoefficient (m : ThetaReflectionData.Row R.A)
    (c : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property) → ℂ)
    (x : Fˣ) : ℂ :=
  ∑ d, c d * ∏ᶠ p, OrbitFrequencies.exteriorDigitValue R D m x d p

def reflectedProfile (seed : ∀ p : D.bad, V p) (y : R.A.G) : ℂ :=
  fourier R Q.dq (badVector R D seed).val
    (diagonal R y * KPRationalAdelicSplitting.pglW F R.A.zeta12 R.A.primitive_zeta12)

theorem reverse_single (hR : RootAligned R) (seed : ∀ p : D.bad, V p)
    (x : Fˣ) (y : R.A.G) (m : ThetaReflectionData.Row R.A)
    (d : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property)) :
    GlobalCoreSource.rationalPeriod T (badVector R D seed) (x : F)
      (signedArgument R m false y d) =
      (∏ᶠ p, OrbitFrequencies.exteriorDigitValue R D m x d p) *
        GlobalProjectConvention.paperHilbert R
          (QuotientGroup.mk' R.A.sixthPowers (R.A.diagonal x))
          (QuotientGroup.mk' R.A.sixthPowers y⁻¹) ^ 2 *
            reflectedProfile R D seed (R.A.diagonal x / y) := by
  rw [GlobalProjectRationalDilation.rationalPeriod_eq_fourier R]
  change fourier R Q.dq (badVector R D seed).val
    (restrictedLift R (reverseTuple R x y m d)) = _
  rw [(reverseTuple_period R D seed x y m d).2,
    mul_assoc, globalWeyl_diagonal, ← mul_assoc,
    GlobalProjectCoreEquivariance.fourier_diagonal_mul R hR]
  rw [GlobalProjectConvention.paperHilbert_on_representatives]
  simp only [inv_pow, div_eq_mul_inv, reflectedProfile, mul_assoc]

/-- The finite average is evaluated on the exact same global vector on
both sides.  `reverseCoefficient` contains only actual exterior local
periods and the explicitly supplied finite digit weights. -/
theorem reverse_average (hR : RootAligned R) (seed : ∀ p : D.bad, V p)
    (m : ThetaReflectionData.Row R.A)
    (c : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property) → ℂ)
    (x : Fˣ) (y : R.A.G) :
    (∑ d, c d * GlobalCoreSource.rationalPeriod T (badVector R D seed) (x : F)
      (signedArgument R m false y d)) =
      reverseCoefficient R D m c x *
        GlobalProjectConvention.paperHilbert R
          (QuotientGroup.mk' R.A.sixthPowers (R.A.diagonal x))
          (QuotientGroup.mk' R.A.sixthPowers y⁻¹) ^ 2 *
            reflectedProfile R D seed (R.A.diagonal x / y) := by
  simp_rw [reverse_single R D hR seed]
  simp only [reverseCoefficient, Finset.sum_mul, mul_assoc]

theorem reverse_weighted_average (hR : RootAligned R) (seed : ∀ p : D.bad, V p)
    (m : ThetaReflectionData.Row R.A)
    (c : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property) → ℂ)
    (L : R.A.G →* ℂ) (B : Subgroup R.A.V) (x : Fˣ) (y : R.A.G) :
    GlobalProjectUnfolding.weight R L B y *
      (∑ d, c d * GlobalCoreSource.rationalPeriod T (badVector R D seed) (x : F)
        (signedArgument R m false y d)) =
      reverseCoefficient R D m c x *
        GlobalProjectUnfolding.reverseWeight R L B
          (QuotientGroup.mk' R.A.sixthPowers (R.A.diagonal x)) y *
            reflectedProfile R D seed (R.A.diagonal x / y) := by
  rw [reverse_average R D hR seed]
  unfold GlobalProjectUnfolding.reverseWeight
  ring

end ThetaGlobal.GlobalProjectSignedExtraction
