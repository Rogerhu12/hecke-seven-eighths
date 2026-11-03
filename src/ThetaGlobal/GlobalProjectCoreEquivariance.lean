import ThetaGlobal.GlobalProjectRationalDilation
import ThetaGlobal.GlobalProjectConvention
import DedekindZetaZeroFree.Metaplectic.Torus.DiagonalFourierPhases
import DedekindZetaZeroFree.Theta.Digits.ForwardMaskInversion

/-!
# Exact phase laws for every vector of the residual core

The global character, diagonal cocycle and rational additive frequency
are retained literally.  None of these identities uses the selected
Gaussian vector.  Root alignment is the already chosen arithmetic
embedding condition, and the remaining statements follow from membership
in the actual residual module and its compact additive period.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace ThetaGlobal.GlobalProjectCoreEquivariance

open NumberField MeasureTheory DedekindZetaZeroFree DedekindZetaZeroFree.MomentSources
open DedekindZetaZeroFree.OrbitExpansion
open scoped NumberField Classical BigOperators

variable {F : Type} [Field F] [NumberField F]
  {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
  (R : PrincipalMellin.ActualRecipe S η)
  {Q : AdmissibleFlatSources R} {T : Realization R Q}

theorem core_rational_root (f : sameResidueModule T) (t : F) (g : Group R) :
    f.val (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12
      (algebraMap F (KPAdeles F) t) * g) = f.val g := by
  rw [← KPLiteralExceptionalResidue.rationalLift_unipotent]
  exact f.property.2.2.1 _ _

theorem fourier_left_central (f : sameResidueModule T)
    (e : rootsOfUnity 3 F) (g : Group R) :
    fourier R Q.dq f.val
      (KPAdelicCoverRestrictedProduct.pglCentralInjection F R.A.zeta12
        R.A.primitive_zeta12 e * g) =
      (KPGlobalTorusFunctionData.iota F R.A.zeta12 R.A.primitive_zeta12 e : ℂ) *
        fourier R Q.dq f.val g := by
  have hc (a : Group R) : Commute a
      (KPAdelicCoverRestrictedProduct.pglCentralInjection F R.A.zeta12 R.A.primitive_zeta12 e) :=
    (Subgroup.mem_center_iff.mp
      (KPAdelicCoverRestrictedProduct.pglCentralInjection_central
        F R.A.zeta12 R.A.primitive_zeta12 ⟨e, rfl⟩)) a
  unfold MomentSources.fourier
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with q
  rw [← mul_assoc, (hc _).eq, mul_assoc, f.property.2.2.2, mul_assoc]

theorem sDiagonalDefect_scalar (hR : RootAligned R) (x y : R.A.G) :
    (KPGlobalTorusFunctionData.iota F R.A.zeta12 R.A.primitive_zeta12
      (KPAdelicCoverRestrictedProduct.centralProduct F (sDiagonalDefect R x y)) : ℂ) =
      (R.σ ((R.A.H_S x y : Fˣ) : F) ^ 2)⁻¹ := by
  have hp : KPAdelicCoverRestrictedProduct.centralProduct F (sDiagonalDefect R x y) =
      ∏ p : R.A.Sf, KPHilbert.B3 F R.A.zeta12 R.A.primitive_zeta12
        (Sum.inr p.val) (x.2 p) (y.2 p) ^ 2 := by
    unfold sDiagonalDefect
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro p _
    exact KPAdelicCoverCertificatesRaw.centralProduct_single F _ _
  rw [hp, map_prod, Units.coe_prod]
  change (∏ p : R.A.Sf, KPSourceConvention.sourceC F R.A.zeta12
    R.A.primitive_zeta12 (Sum.inr p.val) (x.2 p) (y.2 p)) = _
  rw [KPSourceConvention.prod_sourceC_arithmetic]
  have he : KPLocalCover.coefficientEmbedding F R.A.zeta12 R.A.primitive_zeta12 =
      KPLocalCover.coefficientEmbedding F S.zeta12 S.primitive_zeta12 := by
    congr 1
    exact R.sameRoot
  rw [he, ← hR (R.A.H_S x y)]
  simp only [zpow_neg, zpow_ofNat]

theorem fourier_diagonal_mul (hR : RootAligned R) (f : sameResidueModule T)
    (x y : R.A.G) (g : Group R) :
    fourier R Q.dq f.val (diagonal R x * diagonal R y * g) =
      (R.σ ((R.A.H_S x y : Fˣ) : F) ^ 2)⁻¹ *
        fourier R Q.dq f.val (diagonal R (x * y) * g) := by
  have he := congrArg (restrictedLift R) (sDiagonalTuple_mul R x y)
  simp only [map_mul, restrictedLift_centralTuple] at he
  change diagonal R x * diagonal R y =
    KPAdelicCoverRestrictedProduct.pglCentralInjection F R.A.zeta12 R.A.primitive_zeta12
      (KPAdelicCoverRestrictedProduct.centralProduct F (sDiagonalDefect R x y)) *
        diagonal R (x * y) at he
  rw [he, mul_assoc, fourier_left_central R f, sDiagonalDefect_scalar R hR]

theorem rationalPeriod_left_root (f : sameResidueModule T)
    (a : Fˣ) (g : Group R) (t : KPAdeles F) :
    GlobalCoreSource.rationalPeriod T f (a : F)
      (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 t * g) =
      (adelicTraceCharacter F (algebraMap F (KPAdeles F) (a : F) * t) : ℂ) *
        GlobalCoreSource.rationalPeriod T f (a : F) g := by
  let A := KPRationalAdelicSplitting.pglA F R.A.zeta12 R.A.primitive_zeta12
    (Units.map (algebraMap F (KPAdeles F)).toMonoidHom a)
  have hc := KPRationalAdelicSplitting.quotient_upper_diagonal F R.A.zeta12
    R.A.primitive_zeta12 (algebraMap F (KPAdeles F) (a : F) * t)
    (Units.map (algebraMap F (KPAdeles F)).toMonoidHom a)
  have he : (algebraMap F (KPAdeles F) (a : F) * t) *
      algebraMap F (KPAdeles F) (a⁻¹ : Fˣ) = t := by
    rw [mul_right_comm, ← map_mul, Units.mul_inv, map_one, one_mul]
  change KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12
    (algebraMap F (KPAdeles F) (a : F) * t) * A = A *
      KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12
        ((algebraMap F (KPAdeles F) (a : F) * t) *
          algebraMap F (KPAdeles F) (a⁻¹ : Fˣ)) at hc
  rw [he] at hc
  rw [GlobalProjectRationalDilation.rationalPeriod_eq_fourier R f,
    ← mul_assoc, ← hc, mul_assoc]
  letI := Q.quotientHaar
  rw [ExteriorWhittakerValues.StoredWhittaker.fourier_left_root R Q.dq f.val
    (core_rational_root R f) _ (A * g)
    (FourierContinuation.sameResidue_period_integrable T f.property (A * g))]
  exact congrArg (fun z : ℂ =>
    (adelicTraceCharacter F (algebraMap F (KPAdeles F) (a : F) * t) : ℂ) * z)
    (GlobalProjectRationalDilation.rationalPeriod_eq_fourier R f a g).symm

theorem forward_digit_average (f : sameResidueModule T)
    (m : ThetaReflectionData.Row R.A)
    (c : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property) → ℂ)
    (a : Fˣ) (y : R.A.G) :
    (∑ d, c d * GlobalCoreSource.rationalPeriod T f (a : F)
      (signedArgument R m true y d)) =
      (∑ d, c d * (adelicTraceCharacter F
        (algebraMap F (KPAdeles F) (a : F) * digitParameter R m d) : ℂ)) *
        GlobalCoreSource.rationalPeriod T f (a : F) (diagonal R y) := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d _
  simp only [signedArgument, Bool.true_eq, ↓reduceIte, one_mul]
  have hc : diagonal R y * KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12
      (digitParameter R m d) = KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12
        (digitParameter R m d) * diagonal R y := (diagonal_commute_digit_root R y m d).eq
  have h2 := rationalPeriod_left_root R f a (diagonal R y) (digitParameter R m d)
  rw [← hc] at h2
  exact (congrArg (c d * ·) h2).trans (mul_assoc _ _ _).symm

end ThetaGlobal.GlobalProjectCoreEquivariance
