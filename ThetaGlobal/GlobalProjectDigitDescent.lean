import ThetaGlobal.GlobalProjectExterior
import ThetaGlobal.GlobalProjectUnfolding
import DedekindZetaZeroFree.Theta.Periods.CompactDigitContinuity
import DedekindZetaZeroFree.Theta.Digits.CompactQuotientWeights

/-!
# Actual target-character digit descent and quotient integrability

The exterior reference condition is explicit and is proved for every
pure tensor supported on the fixed bad places in `GlobalProjectExterior`.
Rational automorphy and the actual digit reindexing then give descent to
the sixth-unit quotient.  Compactness of a fundamental domain supplies
integrability of the averaged theta function and its constant term.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section

namespace ThetaGlobal.GlobalProjectDigitDescent

open NumberField DedekindZetaZeroFree DedekindZetaZeroFree.MomentSources
open DedekindZetaZeroFree.ThetaProfileHaarSheets
open DedekindZetaZeroFree.ThetaSheetExactUnfolding
open MeasureTheory
open scoped NumberField Classical Topology BigOperators

variable {F : Type} [Field F] [NumberField F]
  {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
  (R : PrincipalMellin.ActualRecipe S η)
  {Q : AdmissibleFlatSources R} {T : Realization R Q}

def RationalDiagonalInvariant (f : Functions R) : Prop :=
  ∀ (a : Fˣ) (g : Group R),
    f (KPRationalAdelicSplitting.pglA F R.A.zeta12 R.A.primitive_zeta12
      (Units.map (algebraMap F (KPAdeles F)).toMonoidHom a) * g) = f g

theorem core_rationalDiagonalInvariant (f : sameResidueModule T) :
    RationalDiagonalInvariant R f.val := by
  intro a g
  rw [DigitMasks.pglA_rational R]
  exact f.property.2.2.1 _ g

theorem core_upper_rationalDiagonalInvariant (f : sameResidueModule T) :
    RationalDiagonalInvariant R (upper R Q.dq f.val) := by
  intro a g
  letI : Q.dq.IsAddHaarMeasure := Q.quotientHaar
  letI : IsProbabilityMeasure Q.dq := ⟨Q.probability⟩
  let E := ThetaDigitDescent.scale (F := F) (a : F)
  have hc : Continuous E := ThetaDigitDescent.scale_continuous _
  have hsurj : Function.Surjective E := by
    intro z
    exact ⟨ThetaDigitDescent.scale (F := F) (a⁻¹ : Fˣ) z,
      ThetaDigitDescent.scale_inverse a⁻¹ z⟩
  have hinj : Function.Injective E :=
    Function.LeftInverse.injective (ThetaDigitDescent.scale_inverse a)
  have hmp : MeasurePreserving E Q.dq Q.dq := E.measurePreserving hc hsurj rfl
  let A := KPRationalAdelicSplitting.pglA F R.A.zeta12 R.A.primitive_zeta12
    (Units.map (algebraMap F (KPAdeles F)).toMonoidHom a)
  let h := fun q : KPAdditiveQuotient F => f.val
    (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out q) * (A * g))
  have htrans (q : KPAdditiveQuotient F) : h (E q) = f.val
      (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 (Quotient.out q) * g) := by
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
    simp only [h, E, ThetaDigitDescent.scale_mk,
      RootDerivatives.integrand_mk R f.val f.property.2.2.1]
    change f.val (KPRationalAdelicSplitting.pglN F R.A.zeta12 R.A.primitive_zeta12
      (algebraMap F (KPAdeles F) (a : F) * x) * (A * g)) = _
    rw [← mul_assoc, KPRationalAdelicSplitting.quotient_upper_diagonal, mul_assoc]
    have he : (algebraMap F (KPAdeles F) (a : F) * x) *
        (((Units.map (algebraMap F (KPAdeles F)).toMonoidHom a)⁻¹ : (KPAdeles F)ˣ) : KPAdeles F) = x := by
      change (algebraMap F (KPAdeles F) (a : F) * x) *
        algebraMap F (KPAdeles F) ((a⁻¹ : Fˣ) : F) = x
      rw [mul_right_comm, ← map_mul, Units.mul_inv, map_one, one_mul]
    rw [he, core_rationalDiagonalInvariant R f]
    rfl
  have hi := (hc.isClosedEmbedding hinj).integral_map (μ := Q.dq) h
  rw [hmp.map_eq] at hi
  simp_rw [htrans] at hi
  exact hi

theorem signed_term_reindex (f : Functions R)
    (hr : RationalDiagonalInvariant R f)
    (hext : GlobalProjectExterior.FullExteriorInvariant R f)
    (m : ThetaReflectionData.Row R.A) (u : R.A.U) (b : Bool) (y : R.A.G)
    (d : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property)) :
    f (signedArgument R m b (R.A.diagonal (u.val ^ 6) * y)
      (ThetaExpansion.QuotientDescent.digitReindex R m u d)) =
      f (signedArgument R m b y d) := by
  have hright (g : Group R) : f (g * (DigitMasks.digitRight R m u y d)⁻¹) = f g := by
    have hk : ∀ w, (DigitMasks.digitRightTuple R m u y d)⁻¹ w ∈
        DigitMasks.exteriorFactor R w := by
      intro w
      rw [RestrictedProduct.inv_apply]
      exact (DigitMasks.exteriorFactor R w).inv_mem
        (DigitMasks.digitRightTuple_mem R m u y d w)
    have hh := hext (DigitMasks.digitRightTuple R m u y d)⁻¹ hk g
    simpa only [DigitMasks.digitRight, map_inv] using hh
  cases b
  · rw [DigitMasks.signedArgument_reindex_false, hright]
    simpa only [map_inv] using hr ((u.val ^ 6)⁻¹) (signedArgument R m false y d)
  · rw [DigitMasks.signedArgument_reindex_true, hright]
    exact hr (u.val ^ 6) (signedArgument R m true y d)

def digitAverage (f : Functions R) (m : ThetaReflectionData.Row R.A)
    (b : Bool) (y : R.A.G) : ℂ :=
  ∑ d : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property),
    digitWeight R m d * f (signedArgument R m b y d)

theorem digitAverage_gamma (f : Functions R)
    (hr : RationalDiagonalInvariant R f)
    (hext : GlobalProjectExterior.FullExteriorInvariant R f)
    (m : ThetaReflectionData.Row R.A) (b : Bool) (γ : R.A.Gamma1) (y : R.A.G) :
    digitAverage R f m b (γ.val.val * y) = digitAverage R f m b y := by
  let δ : R.A.Gamma := ⟨γ.val.val, γ.property⟩
  obtain ⟨q, ⟨ε, hε, rfl⟩, hq⟩ := δ.property
  let u : R.A.U := ⟨ε, hε⟩
  have hγ : γ.val.val = R.A.diagonal (u.val ^ 6) := hq.symm
  rw [hγ]
  unfold digitAverage
  rw [← Equiv.sum_comp (ThetaExpansion.QuotientDescent.digitReindex R m u)]
  apply Finset.sum_congr rfl
  intro d _
  rw [ThetaExpansion.QuotientDescent.digitWeight_reindex,
    signed_term_reindex R f hr hext]

theorem digitAverage_continuous (f : Functions R) (hf : Continuous f)
    (m : ThetaReflectionData.Row R.A) (b : Bool) :
    Continuous (digitAverage R f m b) := by
  apply continuous_finset_sum
  intro d _
  exact continuous_const.mul (hf.comp (DigitMasks.signedArgument_continuous R m b d))

theorem core_upper_continuous (f : sameResidueModule T) :
    Continuous (upper R Q.dq f.val) := by
  letI : IsProbabilityMeasure Q.dq := ⟨Q.probability⟩
  apply continuousOn_univ.mp
  exact continuousOn_integral_of_compact_support (k := Set.univ) isCompact_univ
    (GlobalProjectRadial.upper_integrand_joint_continuous R f.val
      f.property.2.1 f.property.2.2.1).continuousOn (by simp)

def quotientAverage (L : R.A.G →* ℂ) (f : Functions R)
    (m : ThetaReflectionData.Row R.A) (b : Bool)
    (l : PositiveAxis) (q : SheetQuotient R.A l) : ℂ :=
  GlobalProjectUnfolding.weight R L R.probe.correction.B (Quotient.out q).val *
    digitAverage R f m b (Quotient.out q).val

theorem quotientAverage_projection (L : R.A.G →* ℂ)
    (hL : ∀ γ : R.A.Gamma1, L γ.val.val = 1)
    (f : Functions R) (hr : RationalDiagonalInvariant R f)
    (hext : GlobalProjectExterior.FullExteriorInvariant R f)
    (m : ThetaReflectionData.Row R.A) (b : Bool)
    (l : PositiveAxis) (y : Sheet R.A l) :
    quotientAverage R L f m b l (sheetProjection R.A l y) =
      GlobalProjectUnfolding.weight R L R.probe.correction.B y.val *
        digitAverage R f m b y.val := by
  have he := Quotient.exact (Quotient.out_eq (sheetProjection R.A l y))
  obtain ⟨γ, hγ⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp he)
  have hv := congrArg Subtype.val hγ
  change γ.val.val * y.val = (Quotient.out (sheetProjection R.A l y)).val at hv
  unfold quotientAverage
  rw [← hv, GlobalProjectUnfolding.weight_gamma R L R.probe.correction.B hL,
    digitAverage_gamma R f hr hext]

theorem quotientAverage_integrable (w : InfinitePlace F) (μG : Measure R.A.G)
    [μG.IsHaarMeasure] (L : R.A.G →* ℂ)
    (hL : ∀ γ : R.A.Gamma1, L γ.val.val = 1)
    (hLm : Measurable L) (hLn : ∀ y, ‖L y‖ = 1)
    (f : Functions R) (hf : Continuous f) (hr : RationalDiagonalInvariant R f)
    (hext : GlobalProjectExterior.FullExteriorInvariant R f)
    (m : ThetaReflectionData.Row R.A) (b : Bool) (l : PositiveAxis) :
    Integrable (quotientAverage R L f m b l) (sheetQuotientHaar R.A w μG l) := by
  apply DigitMasks.quotient_integrable_of_continuous_bdd_weight R.A w μG l
    (digitAverage R f m b) (GlobalProjectUnfolding.weight R L R.probe.correction.B)
    (quotientAverage R L f m b l) (digitAverage_continuous R f hf m b)
  · exact (DigitMasks.finite_class_measurable R.A
      (fun κ => if κ ∈ R.probe.correction.B then (1 : ℂ) else 0)).mul hLm.inv
  · intro y
    unfold GlobalProjectUnfolding.weight
    rw [norm_mul, norm_inv, hLn, inv_one, mul_one]
    split_ifs <;> simp
  · exact quotientAverage_projection R L hL f hr hext m b l

end ThetaGlobal.GlobalProjectDigitDescent
