import ThetaGlobal.GlobalProjectDigitDescent
import ThetaGlobal.GlobalProjectDescent
import ThetaGlobal.GlobalProjectUniformFourier

/-!
# Actual rational-frequency reflection on a compact norm-sheet domain

This is the integrated automorphic identity before local Whittaker
evaluation and ideal-frequency reindexing.  Its theta vector is an
actual vector in the fixed residual realization.  The period is the
actual target Hecke S-character, including its unit sector.

All constant terms are removed by the proved radial law and the explicit
rotation of a nonzero angular weight.  Individual Fourier coefficients
are integrated on a measurable fundamental domain in the actual sheet;
no measurability of an arbitrary `Quotient.out` section is assumed.
Both pointwise and integrated absolute Fourier convergence are proved
from the smoothness of the actual core vector and compactness of the
chosen fundamental domain.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section

namespace ThetaGlobal.GlobalProjectSheetReflection

open NumberField DedekindZetaZeroFree DedekindZetaZeroFree.MomentSources
open DedekindZetaZeroFree.ThetaProfileHaarSheets
open DedekindZetaZeroFree.ThetaSheetExactUnfolding
open HeckeGeneral.Characters MeasureTheory
open scoped NumberField Classical Topology BigOperators

variable {F : Type} [Field F] [NumberField F]
  {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
  (R : PrincipalMellin.ActualRecipe S η)
  {Q : AdmissibleFlatSources R} {T : Realization R Q}

open GlobalProjectDigitDescent

theorem rationalPeriod_continuous (f : sameResidueModule T) (a : F) :
    Continuous (GlobalCoreSource.rationalPeriod T f a) := by
  letI : IsProbabilityMeasure Q.dq := ⟨Q.probability⟩
  have hc : Continuous (fun p : Group R × KPAdditiveQuotient F =>
      f.val (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12
        (Quotient.out p.2) * p.1) *
      star (adelicRationalFrequencyQuotientCharacter F a p.2 : ℂ)) :=
    (GlobalProjectRadial.upper_integrand_joint_continuous R f.val
      f.property.2.1 f.property.2.2.1).mul
      ((continuous_subtype_val.comp
        (continuous_adelicRationalFrequencyQuotientCharacter F a)).star.comp continuous_snd)
  apply continuousOn_univ.mp
  exact continuousOn_integral_of_compact_support (k := Set.univ) isCompact_univ
    hc.continuousOn (by simp)

theorem fundamental_average_integrable
    (w : InfinitePlace F) (μG : Measure R.A.G) [μG.IsHaarMeasure]
    (l : PositiveAxis) (Ω : Set (Sheet R.A l))
    (hΩ : IsFundamentalDomain R.A.Gamma1 Ω (sheetHaar R.A w μG l))
    (L : R.A.G →* ℂ) (hL : ∀ γ : R.A.Gamma1, L γ.val.val = 1)
    (hLm : Measurable L) (hLn : ∀ y, ‖L y‖ = 1)
    (f : Functions R) (hf : Continuous f) (hr : RationalDiagonalInvariant R f)
    (hext : GlobalProjectExterior.FullExteriorInvariant R f)
    (m : ThetaReflectionData.Row R.A) (b : Bool) :
    Integrable (fun y : Sheet R.A l =>
      GlobalProjectUnfolding.weight R L R.probe.correction.B y.val *
        digitAverage R f m b y.val) ((sheetHaar R.A w μG l).restrict Ω) := by
  have hi := quotientAverage_integrable R w μG L hL hLm hLn f hf hr hext m b l
  have hmp := sheetProjection_measurePreserving R.A w μG l Ω hΩ
  apply (hmp.integrable_comp_of_integrable hi).congr
  filter_upwards [] with y
  exact quotientAverage_projection R L hL f hr hext m b l y

theorem fundamental_average_integral
    (w : InfinitePlace F) (μG : Measure R.A.G) [μG.IsHaarMeasure]
    (l : PositiveAxis) (Ω : Set (Sheet R.A l))
    (hΩ : IsFundamentalDomain R.A.Gamma1 Ω (sheetHaar R.A w μG l))
    (L : R.A.G →* ℂ) (hL : ∀ γ : R.A.Gamma1, L γ.val.val = 1)
    (hLm : Measurable L) (hLn : ∀ y, ‖L y‖ = 1)
    (f : Functions R) (hf : Continuous f) (hr : RationalDiagonalInvariant R f)
    (hext : GlobalProjectExterior.FullExteriorInvariant R f)
    (m : ThetaReflectionData.Row R.A) (b : Bool) :
    (∫ y in Ω, GlobalProjectUnfolding.weight R L R.probe.correction.B y.val *
      digitAverage R f m b y.val ∂sheetHaar R.A w μG l) =
      ∫ q, quotientAverage R L f m b l q ∂sheetQuotientHaar R.A w μG l := by
  have hi := quotientAverage_integrable R w μG L hL hLm hLn f hf hr hext m b l
  have hmp := sheetProjection_measurePreserving R.A w μG l Ω hΩ
  calc
    _ = ∫ y in Ω, quotientAverage R L f m b l (sheetProjection R.A l y)
        ∂sheetHaar R.A w μG l := by
      apply integral_congr_ae
      filter_upwards [] with y
      exact (quotientAverage_projection R L hL f hr hext m b l y).symm
    _ = ∫ q, quotientAverage R L f m b l q ∂Measure.map (sheetProjection R.A l)
        ((sheetHaar R.A w μG l).restrict Ω) :=
      (integral_map hmp.measurable.aemeasurable
        (by simpa only [hmp.map_eq] using hi.aestronglyMeasurable)).symm
    _ = _ := by rw [hmp.map_eq]

/-- Angular cancellation for the arbitrary target infinity type, on the
actual compact quotient and for every exterior-spherical residual vector. -/
theorem target_quotient_upper_zero
    (C : ResidualConstantTerm R Q T) (f : sameResidueModule T)
    (hext : GlobalProjectExterior.FullExteriorInvariant R f.val)
    (θ : HeckeCharacter F) (hS : conductorPlaces F θ ⊆ R.A.Sf)
    (u : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A) (b : Bool)
    (w : InfinitePlace F)
    (hk : heckeComplexWeight F w (R.A.complex_place w) θ ≠ 0)
    (μG : Measure R.A.G) [μG.IsHaarMeasure] (l : PositiveAxis) :
    (∫ q, quotientAverage R (GlobalTargetPeriod.period R θ u)
      (upper R Q.dq f.val) m b l q ∂sheetQuotientHaar R.A w μG l) = 0 := by
  let L := GlobalTargetPeriod.period R θ u
  let z := GlobalProjectAngular.complexRotation θ w (R.A.complex_place w)
  have hL := GlobalTargetPeriod.period_gamma R θ hS u
  have hext' := GlobalProjectExterior.upper_fullExteriorInvariant R f.val hext
  have hr := core_upper_rationalDiagonalInvariant R f
  have hi := quotientAverage_integrable R w μG L hL
    (GlobalTargetPeriod.period_measurable R θ u) (GlobalTargetPeriod.period_norm R θ u)
    (upper R Q.dq f.val) (core_upper_continuous R f) hr hext' m b l
  apply GlobalProjectAngular.quotient_weighted_constantTerm_zero R w μG l
    L R.probe.correction.B z (GlobalProjectAngular.complexRotation_norm θ w _)
    (GlobalTargetPeriod.period_rotation R θ u w _ hk)
    (digitAverage R (upper R Q.dq f.val) m b)
    (quotientAverage R L (upper R Q.dq f.val) m b l) hi
  · exact quotientAverage_projection R L hL (upper R Q.dq f.val) hr hext' m b l
  · intro y
    unfold digitAverage
    apply Finset.sum_congr rfl
    intro d _
    rw [GlobalProjectRadial.sameResidue_upper_signedArgument_rotation R C f m b w z
      (GlobalProjectAngular.complexRotation_norm θ w _) y d]

theorem target_fundamental_upper_zero
    (C : ResidualConstantTerm R Q T) (f : sameResidueModule T)
    (hext : GlobalProjectExterior.FullExteriorInvariant R f.val)
    (θ : HeckeCharacter F) (hS : conductorPlaces F θ ⊆ R.A.Sf)
    (u : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A) (b : Bool)
    (w : InfinitePlace F)
    (hk : heckeComplexWeight F w (R.A.complex_place w) θ ≠ 0)
    (μG : Measure R.A.G) [μG.IsHaarMeasure] (l : PositiveAxis)
    (Ω : Set (Sheet R.A l))
    (hΩ : IsFundamentalDomain R.A.Gamma1 Ω (sheetHaar R.A w μG l)) :
    (∫ y in Ω, GlobalProjectUnfolding.weight R (GlobalTargetPeriod.period R θ u)
      R.probe.correction.B y.val * digitAverage R (upper R Q.dq f.val) m b y.val
      ∂sheetHaar R.A w μG l) = 0 := by
  rw [fundamental_average_integral R w μG l Ω hΩ
    (GlobalTargetPeriod.period R θ u) (GlobalTargetPeriod.period_gamma R θ hS u)
    (GlobalTargetPeriod.period_measurable R θ u) (GlobalTargetPeriod.period_norm R θ u)
    (upper R Q.dq f.val) (core_upper_continuous R f)
    (core_upper_rationalDiagonalInvariant R f)
    (GlobalProjectExterior.upper_fullExteriorInvariant R f.val hext) m b]
  exact target_quotient_upper_zero R C f hext θ hS u m b w hk μG l

theorem weighted_coefficient_integrable
    (w : InfinitePlace F) (μG : Measure R.A.G) [μG.IsHaarMeasure]
    (l : PositiveAxis) (Ω : Set (Sheet R.A l)) (hΩ : IsCompact (closure Ω))
    (θ : HeckeCharacter F) (u : R.A.UnitQuotient)
    (f : sameResidueModule T) (m : ThetaReflectionData.Row R.A) (b : Bool) (a : F) :
    Integrable (fun y : Sheet R.A l =>
      GlobalProjectUnfolding.weight R (GlobalTargetPeriod.period R θ u) R.probe.correction.B y.val *
      ∑ d, digitWeight R m d * GlobalCoreSource.rationalPeriod T f a
        (signedArgument R m b y.val d)) ((sheetHaar R.A w μG l).restrict Ω) := by
  have hc : Continuous (fun y : R.A.G => ∑ d, digitWeight R m d *
      GlobalCoreSource.rationalPeriod T f a (signedArgument R m b y d)) := by
    apply continuous_finset_sum
    intro d _
    exact continuous_const.mul
      ((rationalPeriod_continuous R f a).comp (DigitMasks.signedArgument_continuous R m b d))
  have hi : IntegrableOn (fun y : Sheet R.A l => ∑ d, digitWeight R m d *
      GlobalCoreSource.rationalPeriod T f a (signedArgument R m b y.val d))
      Ω (sheetHaar R.A w μG l) :=
    ((hc.comp continuous_subtype_val).continuousOn.integrableOn_compact hΩ).mono_set subset_closure
  have hw : Measurable (GlobalProjectUnfolding.weight R
      (GlobalTargetPeriod.period R θ u) R.probe.correction.B) :=
    (DigitMasks.finite_class_measurable R.A
      (fun κ => if κ ∈ R.probe.correction.B then (1 : ℂ) else 0)).mul
      (GlobalTargetPeriod.period_measurable R θ u).inv
  apply hi.bdd_mul (hw.comp measurable_subtype_coe).stronglyMeasurable.aestronglyMeasurable (c := 1)
  filter_upwards [] with y
  unfold GlobalProjectUnfolding.weight
  rw [norm_mul, norm_inv, GlobalTargetPeriod.period_norm, inv_one, mul_one]
  split_ifs <;> simp

/-- The integral-norm sum follows from a common summable Fourier
majorant on the compact closure of the actual fundamental domain. -/
theorem weighted_coefficient_norm_integrals_summable
    (w : InfinitePlace F) (μG : Measure R.A.G) [μG.IsHaarMeasure]
    (l : PositiveAxis) (Ω : Set (Sheet R.A l))
    (hΩm : NullMeasurableSet Ω (sheetHaar R.A w μG l))
    (hΩc : IsCompact (closure Ω))
    (θ : HeckeCharacter F) (u : R.A.UnitQuotient)
    (f : sameResidueModule T) (m : ThetaReflectionData.Row R.A) (b : Bool) :
    Summable (fun a : Fˣ => ∫ y in Ω,
      ‖GlobalProjectUnfolding.weight R (GlobalTargetPeriod.period R θ u) R.probe.correction.B y.val *
        ∑ d, digitWeight R m d * GlobalCoreSource.rationalPeriod T f (a : F)
          (signedArgument R m b y.val d)‖ ∂sheetHaar R.A w μG l) := by
  let μ := sheetHaar R.A w μG l
  let P := closure Ω
  letI : CompactSpace P := isCompact_iff_compactSpace.mp hΩc
  letI : IsFiniteMeasure (μ.restrict Ω) :=
    isFiniteMeasure_restrict.mpr
      (lt_of_le_of_lt (measure_mono subset_closure) hΩc.measure_lt_top).ne
  have hd (d : ThetaDigitAverage.Dig (ThetaDigitAverage.rowPrimes R.A m.val m.property)) :
      ∃ B : F → ℝ, Summable B ∧ (∀ a, 0 ≤ B a) ∧
        ∀ p : P, ∀ a, ‖GlobalCoreSource.rationalPeriod T f a
          (signedArgument R m b p.val.val d)‖ ≤ B a :=
    GlobalProjectUniformFourier.compact_rationalPeriod_majorant R f
      (fun p : P => signedArgument R m b p.val.val d)
      ((DigitMasks.signedArgument_continuous R m b d).comp
        (continuous_subtype_val.comp continuous_subtype_val))
  choose B hBs hBpos hBbound using hd
  let M : F → ℝ := fun a => ∑ d, ‖digitWeight R m d‖ * B d a
  have hMs : Summable M :=
    (hasSum_sum (s := Finset.univ)
      (fun d _ => ((hBs d).mul_left ‖digitWeight R m d‖).hasSum)).summable
  have hbound (a : F) (y : Sheet R.A l) (hy : y ∈ Ω) :
      ‖GlobalProjectUnfolding.weight R (GlobalTargetPeriod.period R θ u) R.probe.correction.B y.val *
        ∑ d, digitWeight R m d * GlobalCoreSource.rationalPeriod T f a
          (signedArgument R m b y.val d)‖ ≤ M a := by
    have hw : ‖GlobalProjectUnfolding.weight R (GlobalTargetPeriod.period R θ u)
        R.probe.correction.B y.val‖ ≤ 1 := by
      unfold GlobalProjectUnfolding.weight
      rw [norm_mul, norm_inv, GlobalTargetPeriod.period_norm, inv_one, mul_one]
      split_ifs <;> simp
    calc
      _ ≤ ‖∑ d, digitWeight R m d * GlobalCoreSource.rationalPeriod T f a
          (signedArgument R m b y.val d)‖ := by
        rw [norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) hw
      _ ≤ ∑ d, ‖digitWeight R m d * GlobalCoreSource.rationalPeriod T f a
          (signedArgument R m b y.val d)‖ := norm_sum_le _ _
      _ = ∑ d, ‖digitWeight R m d‖ * ‖GlobalCoreSource.rationalPeriod T f a
          (signedArgument R m b y.val d)‖ := by simp only [norm_mul]
      _ ≤ M a := by
        apply Finset.sum_le_sum
        intro d _
        exact mul_le_mul_of_nonneg_left
          (hBbound d ⟨y, subset_closure hy⟩ a) (norm_nonneg _)
  have hs : Summable (fun a : F => ∫ y in Ω,
      ‖GlobalProjectUnfolding.weight R (GlobalTargetPeriod.period R θ u) R.probe.correction.B y.val *
        ∑ d, digitWeight R m d * GlobalCoreSource.rationalPeriod T f a
          (signedArgument R m b y.val d)‖ ∂μ) := by
    apply (hMs.mul_left ((μ.restrict Ω).real Set.univ)).of_nonneg_of_le
      (fun a => integral_nonneg (fun _ => norm_nonneg _))
    intro a
    calc
      _ ≤ ∫ _ : Sheet R.A l, M a ∂μ.restrict Ω := by
        apply integral_mono_of_nonneg
          (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) (integrable_const (M a))
        filter_upwards [ae_restrict_mem₀ hΩm] with y hy
        exact hbound a y hy
      _ = _ := by rw [integral_const, smul_eq_mul]
  exact hs.comp_injective Units.val_injective

/-- The actual rational-frequency identity used for the fixed-profile
seed.  Pointwise and integrated absolute Fourier convergence, theta and
constant-term integrability, and angular exclusion are all discharged.
The coefficients remain the actual rational periods, ready for local
evaluation and arithmetic reindexing. -/
theorem target_sheet_fourier_identity
    (C : ResidualConstantTerm R Q T) (f : sameResidueModule T)
    (hext : GlobalProjectExterior.FullExteriorInvariant R f.val)
    (θ : HeckeCharacter F) (hS : conductorPlaces F θ ⊆ R.A.Sf)
    (u : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A)
    (w : InfinitePlace F)
    (hk : heckeComplexWeight F w (R.A.complex_place w) θ ≠ 0)
    (μG : Measure R.A.G) [μG.IsHaarMeasure] (l : PositiveAxis)
    (Ω : Set (Sheet R.A l))
    (hΩ : IsFundamentalDomain R.A.Gamma1 Ω (sheetHaar R.A w μG l))
    (hΩc : IsCompact (closure Ω)) :
    (∑' a : Fˣ, ∫ y in Ω,
      GlobalProjectUnfolding.weight R (GlobalTargetPeriod.period R θ u) R.probe.correction.B y.val *
        ∑ d, digitWeight R m d * GlobalCoreSource.rationalPeriod T f (a : F)
          (signedArgument R m true y.val d) ∂sheetHaar R.A w μG l) =
    ∑' a : Fˣ, ∫ y in Ω,
      GlobalProjectUnfolding.weight R (GlobalTargetPeriod.period R θ u) R.probe.correction.B y.val *
        ∑ d, digitWeight R m d * GlobalCoreSource.rationalPeriod T f (a : F)
          (signedArgument R m false y.val d) ∂sheetHaar R.A w μG l := by
  let L := GlobalTargetPeriod.period R θ u
  have hs (b) (d) (y : Sheet R.A l) : Summable (fun a : F =>
      ‖GlobalCoreSource.rationalPeriod T f a (signedArgument R m b y.val d)‖) :=
    GlobalProjectFourierSmooth.rationalPeriod_norm_summable R f _
  have habs (b) := weighted_coefficient_norm_integrals_summable R w μG l Ω
    hΩ.nullMeasurableSet hΩc θ u f m b
  have hL := GlobalTargetPeriod.period_gamma R θ hS u
  have hLm := GlobalTargetPeriod.period_measurable R θ u
  have hLn := GlobalTargetPeriod.period_norm R θ u
  have hg (d) (y : Sheet R.A l) :
      KPRationalAdelicSplitting.pglW F R.A.zeta12 R.A.primitive_zeta12 *
        signedArgument R m true y.val d = signedArgument R m false y.val d := by
    simp only [signedArgument, if_true, Bool.false_eq_true, if_false, one_mul, mul_assoc]
  have hθ := fundamental_average_integrable R w μG l Ω hΩ L hL hLm hLn
    f.val f.property.2.1 (core_rationalDiagonalInvariant R f) hext m true
  have hc (b : Bool) := fundamental_average_integrable R w μG l Ω hΩ L hL hLm hLn
    (upper R Q.dq f.val) (core_upper_continuous R f)
    (core_upper_rationalDiagonalInvariant R f)
    (GlobalProjectExterior.upper_fullExteriorInvariant R f.val hext) m b
  have hz (b : Bool) := target_fundamental_upper_zero R C f hext θ hS u m b w hk μG l Ω hΩ
  have h := GlobalProjectDescent.actual_rational_fourier_descent T
    ((sheetHaar R.A w μG l).restrict Ω) f
    (fun y => GlobalProjectUnfolding.weight R L R.probe.correction.B y.val)
    (digitWeight R m) (fun d y => signedArgument R m true y.val d)
    (hs true) (by intro d y; simpa only [hg] using hs false d y)
    (fun a => weighted_coefficient_integrable R w μG l Ω hΩc θ u f m true a)
    (habs true)
    (by intro a; simpa only [hg] using
      weighted_coefficient_integrable R w μG l Ω hΩc θ u f m false a)
    (by simpa only [hg] using habs false)
    hθ (hc true) (by simpa only [hg] using hc false)
    (hz true) (by simpa only [hg] using hz false)
  simpa only [GlobalProjectDescent.coefficientIntegral, hg] using h

end ThetaGlobal.GlobalProjectSheetReflection
