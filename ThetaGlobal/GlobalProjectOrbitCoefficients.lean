import ThetaGlobal.GlobalProjectWeightedDigits
import ThetaGlobal.GlobalProjectSignedExtraction
import DedekindZetaZeroFree.Theta.Digits.Exterior.GammaInvariantCoefficients
import DedekindZetaZeroFree.Theta.Digits.SphericalValueBounds
import DedekindZetaZeroFree.Theta.Unfolding.ForwardFiberSupport

/-!
# Actual exterior coefficients are invariant under sixth S-units

This repeats the local compact-right-correction argument for an arbitrary
actual factorization and an arbitrary reindex-invariant digit weight.
The auxiliary row exponents never determine the digit weights.
-/

set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 5000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace ThetaGlobal.GlobalProjectOrbitCoefficients

open NumberField MeasureTheory DedekindZetaZeroFree DedekindZetaZeroFree.MomentSources
open DedekindZetaZeroFree.OrbitExpansion
open scoped Classical NumberField BigOperators
open _root_.DedekindZetaZeroFree.KPRationalAdelicSplitting renaming eval_rationalUnit → eval_rationalUnit

variable {F : Type} [Field F] [NumberField F]
  {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
  (R : PrincipalMellin.ActualRecipe S η)
  {Q : AdmissibleFlatSources R} {T : Realization R Q}
  (D : SourceFactorization R Q T)

private theorem value_right_fixed {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (ell : V →ₗ[ℂ] ℂ) (r : V) (a b k : G)
    (h : a = b * k) (hk : ρ k r = r) : ell (ρ a r) = ell (ρ b r) := by
  rw [h, map_mul, Module.End.mul_apply, hk]

theorem exteriorDigitValue_reindex
    (m : ThetaReflectionData.Row R.A) (x : Fˣ) (u : R.A.U)
    (d : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property))
    (p : ThetaBranch.ExteriorPrime R.A) :
    OrbitFrequencies.exteriorDigitValue R D m (u.val ^ 6 * x) (DigitMasks.digitReindex R m u d) p =
      OrbitFrequencies.exteriorDigitValue R D m x d p := by
  rw [OrbitFrequencies.exteriorDigitValue_eq_slot, OrbitFrequencies.exteriorDigitValue_eq_slot]
  let v : KPHilbert.Place F := Sum.inr p.val
  let a := Units.map (algebraMap F (p.val.adicCompletion F)).toMonoidHom x
  let b := Units.map (algebraMap F (p.val.adicCompletion F)).toMonoidHom u.val
  let n := KPAdelicCoverRestrictedProduct.adeleEval F v (digitParameter R m d)
  let n' := KPAdelicCoverRestrictedProduct.adeleEval F v (digitParameter R m (DigitMasks.digitReindex R m u d))
  let k := DigitMasks.digitRightTuple R m u (1 : R.A.G) d v
  let P := KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 v
  let A := fun z => KPPGLLocalCover.A F R.A.zeta12 R.A.primitive_zeta12 v z
  let W := KPPGLLocalCover.W F R.A.zeta12 R.A.primitive_zeta12 v
  let N := fun z => KPPGLLocalCover.N F R.A.zeta12 R.A.primitive_zeta12 v z
  have hk : P k = (N n')⁻¹ * A (b ^ 6) * N n := by
    change P (DigitMasks.digitRightTuple R m u 1 d (Sum.inr p.val)) = _
    unfold DigitMasks.digitRightTuple
    rw [RestrictedProduct.mul_apply, RestrictedProduct.mul_apply, RestrictedProduct.inv_apply,
      RestrictedProduct.mul_apply, RestrictedProduct.mul_apply]
    unfold DigitMasks.diagonalTuple
    rw [sDiagonal_exterior R _ p.val p.property, sDiagonal_exterior R _ p.val p.property]
    simp only [one_mul, map_mul, map_inv]
    congr 2
    change P (KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 v _) = _
    have he := eval_rationalUnit F v (u.val ^ 6)
    change Units.map (KPAdelicCoverRestrictedProduct.adeleEval F (Sum.inr p.val)).toMonoidHom
      (Units.map (algebraMap F (KPAdeles F)).toMonoidHom (u.val ^ 6)) = _ at he
    have he' := congrArg (fun z => P (KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 v z)) he
    exact he'.trans (congrArg A (map_pow _ u.val 6))
  have hA (z : (p.val.adicCompletion F)ˣ) : A (b ^ 6 * z) = A (b ^ 6) * A z := by
    change KPPGLLocalCover.A F R.A.zeta12 R.A.primitive_zeta12 v _ = _
    unfold KPPGLLocalCover.A
    rw [DigitMasks.local_A_pow_six_mul, map_mul]
    rfl
  have hcomm : A (b ^ 6) * A a = A a * A (b ^ 6) := by
    rw [← hA]
    change A _ = A a * A (b ^ 6)
    rw [mul_comm (b ^ 6) a, KPPGLLocalCover.A_mul]
    have hh := ((KPHilbert.B3_laws F R.A.zeta12 R.A.primitive_zeta12 v).2.2.2.2.1 a (b ^ 2)).2
    rw [← pow_mul] at hh
    norm_num only at hh
    rw [hh, one_pow, map_one, one_mul]
  have hW : A (b ^ 6) * W = W * A ((b ^ 6)⁻¹) := by
    have h := KPCorrectedBruhatLifts.quotient_weyl_diagonal F R.A.zeta12 R.A.primitive_zeta12 v (b ^ 6)⁻¹
    simpa only [inv_inv] using h.symm
  have hInv : A ((b ^ 6)⁻¹) = (A (b ^ 6))⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    rw [← hA, mul_inv_cancel]
    exact congrArg P (KPStandardLocalRootLifts.A_one F R.A.zeta12 R.A.primitive_zeta12 v)
  have he : A (b ^ 6 * a) * W * N n' = (A a * W * N n) * P k⁻¹ := by
    rw [hA, hcomm, mul_assoc (A a) (A (b ^ 6)) W, hW, hInv, map_inv, hk]
    generalize A a = aa, W = ww, A (b ^ 6) = bb, N n = nn, N n' = mm
    group
  let ρ := KPRankOneShellRepair.actualCanonicalImageRepresentation F R.A.zeta12 R.A.primitive_zeta12
    p.val (D.finiteData p.val).inducing (D.finiteData p.val).inducing.polarization
    (D.finiteData p.val).haar (D.finiteData p.val).haar_integer
  have hfix : ρ (P k⁻¹) (D.references v) = D.references v :=
    (D.spherical_reference p.val p.property).2 _
      (DigitMasks.exteriorFactor_le_compact R v ((DigitMasks.exteriorFactor R v).inv_mem
        (DigitMasks.digitRightTuple_exterior R m u 1 d p.val p.property)))
  have hv := value_right_fixed ρ (D.ell v) (D.references v)
    (A (b ^ 6 * a) * W * N n') (A a * W * N n) (P k⁻¹) he hfix
  have hl : P (KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 v
      (Units.map (algebraMap F (p.val.adicCompletion F)).toMonoidHom (u.val ^ 6 * x)) *
      KPStandardLocalRootLifts.W F R.A.zeta12 R.A.primitive_zeta12 v *
      KPStandardLocalRootLifts.N F R.A.zeta12 R.A.primitive_zeta12 v n') = A (b ^ 6 * a) * W * N n' := by
    rw [map_mul, map_mul, map_mul, map_pow]
    rfl
  have hr : P (KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 v a *
      KPStandardLocalRootLifts.W F R.A.zeta12 R.A.primitive_zeta12 v *
      KPStandardLocalRootLifts.N F R.A.zeta12 R.A.primitive_zeta12 v n) = A a * W * N n := by
    rw [map_mul, map_mul]
    rfl
  exact (congrArg (fun g => D.ell v (ρ g (D.references v))) hl).trans
    (hv.trans (congrArg (fun g => D.ell v (ρ g (D.references v))) hr).symm)


theorem reverseCoefficient_sixth (m : ThetaReflectionData.Row R.A)
    (c : GlobalProjectWeightedDigits.Digits R m → ℂ)
    (hc : GlobalProjectWeightedDigits.ReindexInvariant R m c)
    (x : Fˣ) (u : R.A.U) :
    GlobalProjectSignedExtraction.reverseCoefficient R D m c (u.val ^ 6 * x) =
      GlobalProjectSignedExtraction.reverseCoefficient R D m c x := by
  unfold GlobalProjectSignedExtraction.reverseCoefficient
  rw [← (DigitMasks.digitReindex R m u).sum_comp]
  simp_rw [hc, exteriorDigitValue_reindex]

theorem reverseCoefficient_gamma (m : ThetaReflectionData.Row R.A)
    (c : GlobalProjectWeightedDigits.Digits R m → ℂ)
    (hc : GlobalProjectWeightedDigits.ReindexInvariant R m c)
    (x : Fˣ) (γ : ThetaReflectionData.rationalGamma R.A) :
    GlobalProjectSignedExtraction.reverseCoefficient R D m c (γ.val * x) =
      GlobalProjectSignedExtraction.reverseCoefficient R D m c x := by
  obtain ⟨u, hu, he⟩ := Subgroup.mem_map.mp γ.property
  rw [← he]
  exact reverseCoefficient_sixth R D m c hc x ⟨u, hu⟩

theorem exteriorValue_gamma (E : ExteriorCoefficients R Q T D)
    (p : ThetaBranch.ExteriorPrime R.A) (x : Fˣ)
    (γ : ThetaReflectionData.rationalGamma R.A) :
    D.exteriorValue R p (γ.val * x) = D.exteriorValue R p x := by
  rw [E.rational_exact, E.rational_exact]
  simpa only [mul_comm γ.val x] using sphericalFactor_gamma R p x γ

theorem exteriorProduct_gamma (E : ExteriorCoefficients R Q T D)
    (x : Fˣ) (γ : ThetaReflectionData.rationalGamma R.A) :
    (∏ᶠ p : ThetaBranch.ExteriorPrime R.A, D.exteriorValue R p (γ.val * x)) =
      ∏ᶠ p : ThetaBranch.ExteriorPrime R.A, D.exteriorValue R p x := by
  apply finprod_congr
  intro p
  exact exteriorValue_gamma R D E p x γ

end ThetaGlobal.GlobalProjectOrbitCoefficients
