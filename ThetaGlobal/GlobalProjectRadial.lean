import ThetaGlobal.GlobalAngular
import ThetaGlobal.GlobalCompactPeriod
import DedekindZetaZeroFree.RepresentationTheory.Smooth.RightDerivativeCyclicSpan
import DedekindZetaZeroFree.Theta.Periods.UpperCurveDifferentiation
import DedekindZetaZeroFree.Theta.Periods.ComplexRotationOddness

/-!
# Radial constant terms throughout the actual residual core

The selected residual constant-term formula extends to every vector in
`hcHeckeSpan T`, hence to every image of `SourceFactorization.coreMap`.
The extension is proved here, not assumed as a new local or global input.

The analytic step is differentiation of a compact additive-quotient
period.  Smoothness of all actual Lie words is already an upstream
theorem.  Joint continuity descends from the adelic cover through its
open quotient map, and `GlobalCompactPeriod` supplies the dominated
differentiation argument.  Right translations and the finite linear
span are then elementary.

This project-facing file is source-audited; its upstream dependency
closure has a separate compilation status.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace ThetaGlobal.GlobalProjectRadial

open DedekindZetaZeroFree DedekindZetaZeroFree.MomentSources
open NumberField MeasureTheory
open scoped NumberField Classical Topology

variable {F : Type} [Field F] [NumberField F]
  {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
  (R : PrincipalMellin.ActualRecipe S η)

local notation "W" =>
  KPContActualSphericalRightFieldIdentification.actualRightWord
    F R.A.zeta12 R.A.primitive_zeta12
local notation "D" =>
  KPContActualSphericalRightFieldIdentification.actualRight
    F R.A.zeta12 R.A.primitive_zeta12
local notation "B" => Fin (AdelicRightLieWords.groupDimension F)
local notation "ρ" => KPLiteralRaw.rightAction F R.A.zeta12 R.A.primitive_zeta12

theorem actualRightWord_eq_adelic (word : List B) (f : Functions R) :
    W word f = AdelicRightLieWords.actualRightWord
      F R.A.zeta12 R.A.primitive_zeta12 word f := by
  induction word with
  | nil => rfl
  | cons b word ih =>
    simp only [KPContActualSphericalRightFieldIdentification.actualRightWord,
      AdelicRightLieWords.actualRightWord]
    rw [ih]
    rfl

theorem actualRightWord_eq_native (word : List B) (f : Functions R) :
    W word f = GlobalAngular.rightWord
      (RootDerivatives.nativeCurve F R.A.zeta12 R.A.primitive_zeta12) word f := by
  induction word with
  | nil => rfl
  | cons b word ih =>
    simp only [KPContActualSphericalRightFieldIdentification.actualRightWord,
      GlobalAngular.rightWord]
    rw [RootDerivatives.actualRight_nativeCurve, ih]
    rfl

theorem actualRightWord_covariant (a : Group R) (c : ℂ) (f : Functions R)
    (hf : f ∈ GlobalAngular.covariantFunctions a c) (word : List B) :
    W word f ∈ GlobalAngular.covariantFunctions a c := by
  rw [actualRightWord_eq_native]
  exact GlobalAngular.rightWord_covariant a c _ f hf word

theorem actualRightWord_rational (f : Functions R)
    (hr : ∀ γ g, f (KPLiteralRaw.rationalLift F R.A.zeta12 R.A.primitive_zeta12 γ * g) = f g)
    (word : List B) :
    ∀ γ g, W word f
      (KPLiteralRaw.rationalLift F R.A.zeta12 R.A.primitive_zeta12 γ * g) = W word f g := by
  intro γ g
  have h := actualRightWord_covariant R
    (KPLiteralRaw.rationalLift F R.A.zeta12 R.A.primitive_zeta12 γ) 1 f
    (by intro x; simpa only [one_mul] using hr γ x) word g
  simpa only [one_mul] using h

theorem hcHeckeSpan_rational {Q : AdmissibleFlatSources R} (T : Realization R Q)
    {f : Functions R} (hf : f ∈ hcHeckeSpan T) :
    ∀ γ g, f (KPLiteralRaw.rationalLift F R.A.zeta12 R.A.primitive_zeta12 γ * g) = f g := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨v, a, word, rfl⟩ := hf
    intro γ g
    change AdelicRightLieWords.actualRightWord F R.A.zeta12 R.A.primitive_zeta12 word
      (T.theta v) ((KPLiteralRaw.rationalLift F R.A.zeta12 R.A.primitive_zeta12 γ * g) * a) =
      AdelicRightLieWords.actualRightWord F R.A.zeta12 R.A.primitive_zeta12 word
        (T.theta v) (g * a)
    simpa only [← actualRightWord_eq_adelic, mul_assoc] using
      actualRightWord_rational R (T.theta v) (T.automorphic v).2.1 word γ (g * a)
  | zero => intros; rfl
  | add f g hf hg ihf ihg =>
    intro γ x
    simp only [Pi.add_apply, ihf, ihg]
  | smul c f hf ih =>
    intro γ x
    simp only [Pi.smul_apply, ih]

/-- Joint continuity of the unweighted upper integrand; the quotient
representative itself need not be continuous. -/
theorem upper_integrand_joint_continuous (f : Functions R) (hf : Continuous f)
    (hr : ∀ γ g, f (KPLiteralRaw.rationalLift F R.A.zeta12 R.A.primitive_zeta12 γ * g) = f g) :
    Continuous (fun p : Group R × KPAdditiveQuotient F =>
      f (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12
        (Quotient.out p.2) * p.1)) := by
  letI : IsTopologicalGroup (Group R) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover
      F R.A.zeta12 R.A.primitive_zeta12).2.2.1
  apply ((IsOpenQuotientMap.id (X := Group R)).prodMap
    (QuotientAddGroup.isOpenQuotientMap_mk
      (N := AdeleRing.principalSubgroup (𝓞 F) F))).continuous_comp_iff.mp
  convert hf.comp (((KPWildIndependentGenericity.NonzeroPeriod.actual_upper_root_continuous
    F R.A.zeta12 R.A.primitive_zeta12).comp continuous_snd).mul continuous_fst) using 1
  funext p
  exact RootDerivatives.integrand_mk R f hr p.2 p.1

theorem upper_integrable (dq : Measure (KPAdditiveQuotient F)) [IsFiniteMeasure dq]
    (f : Functions R) (hf : Continuous f)
    (hr : ∀ γ g, f (KPLiteralRaw.rationalLift F R.A.zeta12 R.A.primitive_zeta12 γ * g) = f g)
    (g : Group R) :
    Integrable (fun q => f (KPGlobalTorusFunctionData.N F R.A.zeta12
      R.A.primitive_zeta12 (Quotient.out q) * g)) dq :=
  (RootDerivatives.integrand_continuous R f hf hr g).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- The genuine derivative-period interchange for every actual native
Lie direction and every smooth rationally invariant function. -/
theorem upper_nativeCurve_hasDeriv
    (dq : Measure (KPAdditiveQuotient F)) [IsFiniteMeasure dq]
    (f : Functions R) (hf : KPLiteralRaw.Smooth F R.A.zeta12 R.A.primitive_zeta12 f)
    (hr : ∀ γ g, f (KPLiteralRaw.rationalLift F R.A.zeta12 R.A.primitive_zeta12 γ * g) = f g)
    (b : B) (g : Group R) :
    HasDerivAt (fun t => upper R dq f
      (g * RootDerivatives.nativeCurve F R.A.zeta12 R.A.primitive_zeta12 b t))
      (upper R dq (D b f) g) 0 := by
  letI : IsTopologicalGroup (Group R) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover
      F R.A.zeta12 R.A.primitive_zeta12).2.2.1
  let flow := RootDerivatives.nativeCurve F R.A.zeta12 R.A.primitive_zeta12 b
  let P : ℝ → KPAdditiveQuotient F → ℂ := fun t q =>
    f ((KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12
      (Quotient.out q) * g) * flow t)
  let P' : ℝ → KPAdditiveQuotient F → ℂ := fun t q =>
    D b f ((KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12
      (Quotient.out q) * g) * flow t)
  have hD : KPLiteralRaw.Smooth F R.A.zeta12 R.A.primitive_zeta12 (D b f) :=
    SharedSource.actualRightWord_smooth f hf [b]
  have hDr : ∀ γ x, D b f
      (KPLiteralRaw.rationalLift F R.A.zeta12 R.A.primitive_zeta12 γ * x) = D b f x :=
    actualRightWord_rational R f hr [b]
  have hpair : Continuous (fun p : ℝ × KPAdditiveQuotient F => (g * flow p.1, p.2)) :=
    (continuous_const.mul ((RootDerivatives.nativeCurve_continuous
      F R.A.zeta12 R.A.primitive_zeta12 b).comp continuous_fst)).prodMk continuous_snd
  have hP : Continuous (Function.uncurry P) := by
    convert (upper_integrand_joint_continuous R f hf.1 hr).comp hpair using 1
    funext p
    simp only [Function.uncurry, Function.comp_def, P, mul_assoc]
  have hP' : Continuous (Function.uncurry P') := by
    convert (upper_integrand_joint_continuous R (D b f) hD.1 hDr).comp hpair using 1
    funext p
    simp only [Function.uncurry, Function.comp_def, P', mul_assoc]
  have hd (t : ℝ) (q : KPAdditiveQuotient F) :
      HasDerivAt (fun s => P s q) (P' t q) t :=
    RootDerivatives.nativeCurve_hasDerivAt F R.A.zeta12 R.A.primitive_zeta12 b f hf _ t
  have hi := GlobalCompactPeriod.hasDerivAt_integral_of_joint_continuous
    dq P P' hP hP' hd 0
  convert hi using 1
  · funext t
    simp only [upper, P, mul_assoc]
    rfl
  · simp only [upper, P', flow, RootDerivatives.nativeCurve_zero, mul_one]

theorem upper_actualRight
    (dq : Measure (KPAdditiveQuotient F)) [IsFiniteMeasure dq]
    (f : Functions R) (hf : KPLiteralRaw.Smooth F R.A.zeta12 R.A.primitive_zeta12 f)
    (hr : ∀ γ g, f (KPLiteralRaw.rationalLift F R.A.zeta12 R.A.primitive_zeta12 γ * g) = f g)
    (b : B) :
    upper R dq (D b f) = D b (upper R dq f) := by
  rw [RootDerivatives.actualRight_nativeCurve
    F R.A.zeta12 R.A.primitive_zeta12 b (upper R dq f)]
  funext g
  exact (upper_nativeCurve_hasDeriv R dq f hf hr b g).deriv.symm

theorem upper_actualRightWord
    (dq : Measure (KPAdditiveQuotient F)) [IsFiniteMeasure dq]
    (f : Functions R) (hf : KPLiteralRaw.Smooth F R.A.zeta12 R.A.primitive_zeta12 f)
    (hr : ∀ γ g, f (KPLiteralRaw.rationalLift F R.A.zeta12 R.A.primitive_zeta12 γ * g) = f g)
    (word : List B) :
    upper R dq (W word f) = W word (upper R dq f) := by
  induction word with
  | nil => rfl
  | cons b word ih =>
    simp only [KPContActualSphericalRightFieldIdentification.actualRightWord]
    rw [upper_actualRight R dq _ (SharedSource.actualRightWord_smooth f hf word)
      (actualRightWord_rational R f hr word), ih]

theorem upper_rightAction (dq : Measure (KPAdditiveQuotient F))
    (f : Functions R) (a : Group R) :
    upper R dq (ρ a f) = fun g => upper R dq f (g * a) := by
  funext g
  simp only [upper, KPLiteralRaw.rightAction]
  refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
  exact congrArg f (mul_assoc _ _ _)

theorem hcHeckeSpan_upper_integrable {Q : AdmissibleFlatSources R} (T : Realization R Q)
    {f : Functions R} (hf : f ∈ hcHeckeSpan T) (g : Group R) :
    Integrable (fun q => f (KPGlobalTorusFunctionData.N F R.A.zeta12
      R.A.primitive_zeta12 (Quotient.out q) * g)) Q.dq := by
  letI : IsProbabilityMeasure Q.dq := ⟨Q.probability⟩
  exact upper_integrable R Q.dq f (RootDerivatives.hcHeckeSpan_smooth R T hf).1
    (hcHeckeSpan_rational R T hf) g

/-- The exact selected covariance extends to the whole residual Lie-word
and translation span.  This is stronger than needed for a fixed core tensor. -/
theorem hcHeckeSpan_upper_covariant {Q : AdmissibleFlatSources R} (T : Realization R Q)
    (a : Group R) (c : ℂ)
    (hselected : ∀ v, upper R Q.dq (T.theta v) ∈ GlobalAngular.covariantFunctions a c)
    {f : Functions R} (hf : f ∈ hcHeckeSpan T) :
    upper R Q.dq f ∈ GlobalAngular.covariantFunctions a c := by
  letI : IsProbabilityMeasure Q.dq := ⟨Q.probability⟩
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨v, r, word, rfl⟩ := hf
    rw [upper_rightAction, ← actualRightWord_eq_adelic,
      upper_actualRightWord R Q.dq (T.theta v) (T.automorphic v).1 (T.automorphic v).2.1]
    exact GlobalAngular.rightTranslate_covariant a r c _
      (actualRightWord_covariant R a c _ (hselected v) word)
  | zero =>
    change (fun _ => ∫ _, (0 : ℂ) ∂Q.dq) ∈ GlobalAngular.covariantFunctions a c
    simp only [integral_zero]
    exact (GlobalAngular.covariantFunctions a c).zero_mem
  | add f g hf hg ihf ihg =>
    have he : upper R Q.dq (f + g) = upper R Q.dq f + upper R Q.dq g := by
      funext x
      exact integral_add (hcHeckeSpan_upper_integrable R T hf x)
        (hcHeckeSpan_upper_integrable R T hg x)
    rw [he]
    exact (GlobalAngular.covariantFunctions a c).add_mem ihf ihg
  | smul c' f hf ih =>
    have he : upper R Q.dq (c' • f) = c' • upper R Q.dq f := by
      funext x
      exact integral_smul c' _
    rw [he]
    exact (GlobalAngular.covariantFunctions a c).smul_mem c' ih

theorem hcHeckeSpan_upper_radial {Q : AdmissibleFlatSources R} {T : Realization R Q}
    (C : ResidualConstantTerm R Q T) {f : Functions R} (hf : f ∈ hcHeckeSpan T)
    (w : InfinitePlace F) (z : w.Completionˣ) (g : Group R) :
    upper R Q.dq f
      (KPRationalAdelicSplitting.pglA F R.A.zeta12 R.A.primitive_zeta12
        (KPRationalAdelicSplitting.localIdele F (Sum.inl w) z) * g) =
      (Real.rpow (‖(z : w.Completion)‖ ^ 2) (1 / 3) : ℂ) * upper R Q.dq f g :=
  hcHeckeSpan_upper_covariant R T _ _ (fun v => C.radial v w z) hf g

theorem sameResidue_upper_radial {Q : AdmissibleFlatSources R} {T : Realization R Q}
    (C : ResidualConstantTerm R Q T) (f : sameResidueModule T)
    (w : InfinitePlace F) (z : w.Completionˣ) (g : Group R) :
    upper R Q.dq f.val
      (KPRationalAdelicSplitting.pglA F R.A.zeta12 R.A.primitive_zeta12
        (KPRationalAdelicSplitting.localIdele F (Sum.inl w) z) * g) =
      (Real.rpow (‖(z : w.Completion)‖ ^ 2) (1 / 3) : ℂ) * upper R Q.dq f.val g :=
  hcHeckeSpan_upper_radial R C f.property.1 w z g

/-- Pointwise rotation invariance of the constant term for every actual
core vector, on both Weyl sides and before any digit average. -/
theorem sameResidue_upper_signedArgument_rotation
    {Q : AdmissibleFlatSources R} {T : Realization R Q}
    (C : ResidualConstantTerm R Q T) (f : sameResidueModule T)
    (m : ThetaReflectionData.Row R.A) (b : Bool) (w : InfinitePlace F)
    (z : w.Completionˣ) (hz : ‖(z : w.Completion)‖ = 1) (y : R.A.G)
    (d : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property)) :
    upper R Q.dq f.val
      (signedArgument R m b (IdeleInsertion.infiniteInsertion R.A w z * y) d) =
    upper R Q.dq f.val (signedArgument R m b y d) := by
  cases b
  · simp only [signedArgument, Bool.false_eq_true, if_false,
      IdeleInsertion.diagonal_insertion]
    rw [← mul_assoc, KPRationalAdelicSplitting.quotient_weyl_diagonal]
    simp only [mul_assoc]
    have he : (KPRationalAdelicSplitting.localIdele F (Sum.inl w) z)⁻¹ =
        KPRationalAdelicSplitting.localIdele F (Sum.inl w) z⁻¹ := by
      simp [KPRationalAdelicSplitting.localIdele]
    rw [he, sameResidue_upper_radial R C f]
    simp [Units.val_inv_eq_inv_val, norm_inv, hz]
  · simp only [signedArgument, if_true, one_mul, IdeleInsertion.diagonal_insertion, mul_assoc]
    rw [sameResidue_upper_radial R C f]
    simp [hz]

end ThetaGlobal.GlobalProjectRadial
