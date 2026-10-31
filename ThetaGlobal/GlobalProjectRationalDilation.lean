import ThetaGlobal.GlobalProjectDigitDescent
import DedekindZetaZeroFree.Theta.Whittaker.RationalFrequencyDilation

/-! The exact rational-frequency to standard Whittaker-period dictionary
for every vector of the same residual core, with the original additive
Haar measure and trace-character convention. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace ThetaGlobal.GlobalProjectRationalDilation

open NumberField MeasureTheory DedekindZetaZeroFree DedekindZetaZeroFree.MomentSources
open scoped NumberField Classical

variable {F : Type} [Field F] [NumberField F]
  {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
  (R : PrincipalMellin.ActualRecipe S η)
  {Q : AdmissibleFlatSources R} {T : Realization R Q}

theorem rationalPeriod_eq_fourier (f : sameResidueModule T) (a : Fˣ) (g : Group R) :
    GlobalCoreSource.rationalPeriod T f (a : F) g =
      fourier R Q.dq f.val
        (KPRationalAdelicSplitting.pglA F R.A.zeta12 R.A.primitive_zeta12
          (Units.map (algebraMap F (KPAdeles F)).toMonoidHom a) * g) := by
  let E := KPAdditiveRationalDilation.quotientDilation F a
  let A := KPRationalAdelicSplitting.pglA F R.A.zeta12 R.A.primitive_zeta12
    (Units.map (algebraMap F (KPAdeles F)).toMonoidHom a)
  let φ : KPAdditiveQuotient F → ℂ := fun q => GlobalCoreSource.fiber T f (A * g) q *
    star (adelicTraceQuotientCharacter F q : ℂ)
  letI := Q.quotientHaar
  letI : IsProbabilityMeasure Q.dq := ⟨Q.probability⟩
  have hmp := KPAdditiveRationalDilation.quotientDilation_measurePreserving F a Q.dq
  obtain ⟨e, he⟩ := KPAdditiveRationalDilation.quotientDilation_is_additive_homeomorphism F a
  have hme : MeasurableEmbedding E := by
    have hef : (e : _ → _) = E := funext he
    rw [← hef]
    exact e.toHomeomorph.measurableEmbedding
  have htransform (q : KPAdditiveQuotient F) : φ (E q) =
      GlobalCoreSource.fiber T f g q *
        star (adelicRationalFrequencyQuotientCharacter F (a : F) q : ℂ) := by
    let x := Quotient.out q
    have hq : (QuotientAddGroup.mk x : KPAdditiveQuotient F) = q := Quotient.out_eq q
    have hd : E q = QuotientAddGroup.mk (algebraMap F (KPAdeles F) (a : F) * x) := by
      rw [← hq]
      rfl
    unfold φ
    have hmk : ∀ y : KPAdeles F, (QuotientAddGroup.mk y : KPAdditiveQuotient F) =
        QuotientAddGroup.mk' (AdeleRing.principalSubgroup (𝓞 F) F) y := fun _ => rfl
    rw [hd, GlobalCoreSource.fiber_mk, hmk, adelicTraceQuotientCharacter_mk,
      OrbitExpansion.rationalCharacter_out]
    congr 1
    rw [← mul_assoc]
    have hc := KPRationalAdelicSplitting.quotient_upper_diagonal F R.A.zeta12 R.A.primitive_zeta12
      (algebraMap F (KPAdeles F) (a : F) * x)
      (Units.map (algebraMap F (KPAdeles F)).toMonoidHom a)
    change KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12
      (algebraMap F (KPAdeles F) (a : F) * x) * A = A *
        KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12
          ((algebraMap F (KPAdeles F) (a : F) * x) * algebraMap F (KPAdeles F) (a⁻¹ : Fˣ)) at hc
    have hx : (algebraMap F (KPAdeles F) (a : F) * x) *
        algebraMap F (KPAdeles F) (a⁻¹ : Fˣ) = x := by
      rw [mul_right_comm, ← map_mul, Units.mul_inv, map_one, one_mul]
    rw [hx] at hc
    rw [hc, mul_assoc, GlobalProjectDigitDescent.core_rationalDiagonalInvariant R f]
    rfl
  have h := hmp.integral_comp hme φ
  change (∫ q, φ (E q) ∂Q.dq) = _ at h
  simp only [htransform] at h
  simpa only [GlobalCoreSource.rationalPeriod,
    MomentSources.fourier, φ, A, GlobalCoreSource.fiber] using h

end ThetaGlobal.GlobalProjectRationalDilation
