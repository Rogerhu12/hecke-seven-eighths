import DedekindZetaZeroFree.Theta.Digits.AbsoluteFourierReconstruction
import DedekindZetaZeroFree.Theta.Periods.IntegrabilityAndResidueLimits
import DedekindZetaZeroFree.Theta.Digits.WeightedDescentAndZeroDigits

/-!
# Fourier reconstruction and rational Weyl symmetry for every residual core vector

The upstream principal-character construction already embeds arbitrary finite
restricted tensors into `sameResidueModule T`.  Its selected Gaussian vector
is not needed for the automorphy or Fourier reconstruction in this file.
Consequently a high K-type replacement can use the *same* residual realization,
the same recipe, and the same arithmetic data.

This project-facing module is separate from the Mathlib-only checked modules.
It imports upstream dependencies omitted from the supplied source bundle; its
compilation status is recorded explicitly in the delivery report.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace ThetaGlobal.GlobalCoreSource

open DedekindZetaZeroFree DedekindZetaZeroFree.MomentSources
open NumberField MeasureTheory
open scoped NumberField Classical Topology BigOperators

variable {F : Type} [Field F] [NumberField F]
  {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
  {R : PrincipalMellin.ActualRecipe S η} {Q : AdmissibleFlatSources R}
  (T : Realization R Q)

/-- The actual additive-quotient fiber of a vector in the residual module. -/
def fiber (f : sameResidueModule T) (g : Group R) (q : KPAdditiveQuotient F) : ℂ :=
  f.val (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12
    (Quotient.out q) * g)

theorem fiber_mk (f : sameResidueModule T) (g : Group R) (x : KPAdeles F) :
    fiber T f g (QuotientAddGroup.mk x) =
      f.val (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 x * g) := by
  obtain ⟨r, he⟩ := QuotientAddGroup.mk_out_eq_add
    (AdeleRing.principalSubgroup (𝓞 F) F) x
  obtain ⟨t, ht⟩ := r.property
  change f.val (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12
    (Quotient.out (QuotientAddGroup.mk x : KPAdditiveQuotient F)) * g) = _
  rw [he, ← ht, add_comm, KPGlobalTorusFunctionData.N_add, mul_assoc,
    ← KPLiteralExceptionalResidue.rationalLift_unipotent, f.property.2.2.1]

theorem fiber_zero (f : sameResidueModule T) (g : Group R) :
    fiber T f g 0 = f.val g := by
  have hn : KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12 0 = 1 :=
    (KPGlobalTorusFunctionData.Nhom F R.A.zeta12 R.A.primitive_zeta12).map_one
  simpa only [QuotientAddGroup.mk_zero, hn, one_mul] using fiber_mk T f g 0

theorem fiber_continuous (f : sameResidueModule T) (g : Group R) :
    Continuous (fiber T f g) :=
  FourierContinuation.sameResidue_orbit_continuous T f.property g

/-- Rational Fourier coefficients use the original trace character. -/
def rationalPeriod (f : sameResidueModule T) (a : F) (g : Group R) : ℂ :=
  ∫ q, fiber T f g q *
    star (adelicRationalFrequencyQuotientCharacter F a q : ℂ) ∂Q.dq

theorem rationalPeriod_integrable (f : sameResidueModule T) (a : F) (g : Group R) :
    Integrable (fun q => fiber T f g q *
      star (adelicRationalFrequencyQuotientCharacter F a q : ℂ)) Q.dq := by
  letI : IsProbabilityMeasure Q.dq := ⟨Q.probability⟩
  have hc : Continuous (fun q : KPAdditiveQuotient F =>
      star (adelicRationalFrequencyQuotientCharacter F a q : ℂ)) :=
    (continuous_subtype_val.comp
      (continuous_adelicRationalFrequencyQuotientCharacter F a)).star
  exact ((fiber_continuous T f g).mul hc).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem rationalPeriod_zero (f : sameResidueModule T) (g : Group R) :
    rationalPeriod T f 0 g = upper R Q.dq f.val g := by
  unfold rationalPeriod upper fiber
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun q => by
    simp [OrbitExpansion.rationalCharacter_out]

/-- Absolute Fourier reconstruction is valid for every core vector; the
summability hypothesis is analytic and does not contain a reflection identity. -/
theorem rationalPeriod_hasSum_of_norm_summable
    (f : sameResidueModule T) (g : Group R)
    (hs : Summable (fun a : F => ‖rationalPeriod T f a g‖)) :
    HasSum (fun a : F => rationalPeriod T f a g) (f.val g) := by
  letI : Q.dq.IsAddHaarMeasure := Q.quotientHaar
  letI : IsProbabilityMeasure Q.dq := ⟨Q.probability⟩
  have he (a : F) :
      (∫ q, fiber T f g q *
        ThetaRationalFourierSummation.freq F (PrincipalOfKP.standardCharacter F) a q
        ∂Q.dq) = rationalPeriod T f a g := by
    simp only [OrbitExpansion.negativeFrequency_eq_star_rationalCharacter, rationalPeriod]
  have h := ThetaRationalFourierSummation.hasSum_of_summable_coefficients F
    (PrincipalOfKP.standardCharacter F) (PrincipalOfKP.standardCharacter_nontrivial F)
    Q.dq (fiber T f g) (fiber_continuous T f g) (by simpa only [he] using hs)
  simpa only [he, fiber_zero] using h

theorem nonzero_rationalPeriod_hasSum
    (f : sameResidueModule T) (g : Group R)
    (hs : Summable (fun a : F => ‖rationalPeriod T f a g‖)) :
    HasSum (fun a : Fˣ => rationalPeriod T f (a : F) g)
      (f.val g - upper R Q.dq f.val g) := by
  have ht := hasSum_ite_sub_hasSum
    (rationalPeriod_hasSum_of_norm_summable T f g hs) (0 : F)
  have hsupport : Function.support (fun a : F =>
      if a = 0 then 0 else rationalPeriod T f a g) ⊆ {a : F | a ≠ 0} := by
    intro a ha
    by_contra h
    simp only [Set.mem_setOf_eq, not_not] at h
    subst a
    simpa using ha
  have ht' := (hasSum_subtype_iff_of_support_subset hsupport).mpr ht
  have ht'' := (unitsEquivNeZero.hasSum_iff).mpr ht'
  rw [rationalPeriod_zero] at ht''
  convert ht'' using 1
  funext a
  change rationalPeriod T f (a : F) g =
    if (a : F) = 0 then 0 else rationalPeriod T f (a : F) g
  rw [if_neg a.ne_zero]

/-- Rational Weyl invariance comes from membership in the original residual
module, including for high K-type tensors and finite local translates. -/
theorem weyl (f : sameResidueModule T) (g : Group R) :
    f.val (KPRationalAdelicSplitting.pglW F R.A.zeta12 R.A.primitive_zeta12 * g) =
      f.val g := by
  have h := f.property.2.2.1
    (Matrix.ProjGenLinGroup.mk (KPStandardLocalRootLifts.weylSwap F)) g
  rw [KPLiteralPeriod.raw_rationalLift_mk] at h
  change f.val
    (KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
      (KPAdelicCoverRestrictedProduct.rationalSection F R.A.zeta12 R.A.primitive_zeta12
        (KPStandardLocalRootLifts.weylSwap F)) * g) = f.val g at h
  simpa only [KPRationalAdelicSplitting.pglW,
    KPRationalAdelicSplitting.W_rational] using h

theorem finite_average_weyl {E : Type*} [Fintype E]
    (f : sameResidueModule T) (c : E → ℂ) (g : E → Group R) :
    (∑ d, c d * f.val
      (KPRationalAdelicSplitting.pglW F R.A.zeta12 R.A.primitive_zeta12 * g d)) =
      ∑ d, c d * f.val (g d) := by
  apply Finset.sum_congr rfl
  intro d _
  rw [weyl]

theorem finite_average_nonzero_hasSum {E : Type*} [Fintype E]
    (f : sameResidueModule T) (c : E → ℂ) (g : E → Group R)
    (hs : ∀ d, Summable (fun a : F => ‖rationalPeriod T f a (g d)‖)) :
    HasSum (fun a : Fˣ => ∑ d, c d * rationalPeriod T f (a : F) (g d))
      (∑ d, c d * (f.val (g d) - upper R Q.dq f.val (g d))) := by
  exact hasSum_sum (s := Finset.univ) fun d _ =>
    (nonzero_rationalPeriod_hasSum T f (g d) (hs d)).mul_left (c d)

/-- The fixed `SourceFactorization` supplies the required residual vector
without selecting new arithmetic data or an unrelated theta realization. -/
def coreVector (D : SourceFactorization R Q T)
    (x : RestrictedTensorSimple.Core (actualLocal R D.finiteData) D.references D.bad) :
    sameResidueModule T :=
  ⟨D.coreMap x, D.core_same_residue x⟩

theorem core_weyl (D : SourceFactorization R Q T)
    (x : RestrictedTensorSimple.Core (actualLocal R D.finiteData) D.references D.bad)
    (g : Group R) :
    D.coreMap x
      (KPRationalAdelicSplitting.pglW F R.A.zeta12 R.A.primitive_zeta12 * g) =
      D.coreMap x g :=
  weyl T (coreVector T D x) g

end ThetaGlobal.GlobalCoreSource
