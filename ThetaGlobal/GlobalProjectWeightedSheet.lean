import ThetaGlobal.GlobalProjectWeightedDigits
import ThetaGlobal.GlobalProjectSheetReflection

/-!
# Actual sheet reflection for arbitrary ordinary and marked digit weights

The row here is an auxiliary support row.  The weight c is independent of
its exponents.  `tensorWeight_reindexInvariant` supplies the only finite
algebraic premise for ordinary α_j, punctured α_0, and marked 1/q weights.
All absolute convergence and constant-term cancellation are proved.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section

namespace ThetaGlobal.GlobalProjectWeightedSheet

open NumberField DedekindZetaZeroFree DedekindZetaZeroFree.MomentSources
open DedekindZetaZeroFree.ThetaProfileHaarSheets
open DedekindZetaZeroFree.ThetaSheetExactUnfolding
open HeckeGeneral.Characters MeasureTheory
open scoped NumberField Classical Topology BigOperators

variable {F : Type} [Field F] [NumberField F]
  {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
  (R : PrincipalMellin.ActualRecipe S η)
  {Q : AdmissibleFlatSources R} {T : Realization R Q}
  (m : ThetaReflectionData.Row R.A)
  (c : GlobalProjectWeightedDigits.Digits R m → ℂ)

open GlobalProjectDigitDescent
open GlobalProjectWeightedDigits renaming average → average
open GlobalProjectWeightedDigits renaming ReindexInvariant → ReindexInvariant

theorem fundamental_integrable (hc : ReindexInvariant R m c)
    (w : InfinitePlace F) (μG : Measure R.A.G) [μG.IsHaarMeasure]
    (l : PositiveAxis) (Ω : Set (Sheet R.A l))
    (hΩ : IsFundamentalDomain R.A.Gamma1 Ω (sheetHaar R.A w μG l))
    (L : R.A.G →* ℂ) (hL : ∀ γ : R.A.Gamma1, L γ.val.val = 1)
    (hLm : Measurable L) (hLn : ∀ y, ‖L y‖ = 1)
    (f : Functions R) (hf : Continuous f) (hr : RationalDiagonalInvariant R f)
    (hext : GlobalProjectExterior.FullExteriorInvariant R f) (b : Bool) :
    Integrable (fun y : Sheet R.A l =>
      GlobalProjectUnfolding.weight R L R.probe.correction.B y.val *
        average R m c f b y.val) ((sheetHaar R.A w μG l).restrict Ω) := by
  have hi := GlobalProjectWeightedDigits.quotientAverage_integrable R w μG
    L hL hLm hLn m c hc f hf hr hext b l
  have hmp := sheetProjection_measurePreserving R.A w μG l Ω hΩ
  apply (hmp.integrable_comp_of_integrable hi).congr
  filter_upwards [] with y
  exact GlobalProjectWeightedDigits.quotientAverage_projection R L hL m c hc f hr hext b l y

theorem fundamental_integral (hc : ReindexInvariant R m c)
    (w : InfinitePlace F) (μG : Measure R.A.G) [μG.IsHaarMeasure]
    (l : PositiveAxis) (Ω : Set (Sheet R.A l))
    (hΩ : IsFundamentalDomain R.A.Gamma1 Ω (sheetHaar R.A w μG l))
    (L : R.A.G →* ℂ) (hL : ∀ γ : R.A.Gamma1, L γ.val.val = 1)
    (hLm : Measurable L) (hLn : ∀ y, ‖L y‖ = 1)
    (f : Functions R) (hf : Continuous f) (hr : RationalDiagonalInvariant R f)
    (hext : GlobalProjectExterior.FullExteriorInvariant R f) (b : Bool) :
    (∫ y in Ω, GlobalProjectUnfolding.weight R L R.probe.correction.B y.val *
      average R m c f b y.val ∂sheetHaar R.A w μG l) =
      ∫ q, GlobalProjectWeightedDigits.quotientAverage R L m c f b l q
        ∂sheetQuotientHaar R.A w μG l := by
  have hi := GlobalProjectWeightedDigits.quotientAverage_integrable R w μG
    L hL hLm hLn m c hc f hf hr hext b l
  have hmp := sheetProjection_measurePreserving R.A w μG l Ω hΩ
  calc
    _ = ∫ y in Ω, GlobalProjectWeightedDigits.quotientAverage R L m c f b l
        (sheetProjection R.A l y) ∂sheetHaar R.A w μG l := by
      apply integral_congr_ae
      filter_upwards [] with y
      exact (GlobalProjectWeightedDigits.quotientAverage_projection
        R L hL m c hc f hr hext b l y).symm
    _ = ∫ q, GlobalProjectWeightedDigits.quotientAverage R L m c f b l q
        ∂Measure.map (sheetProjection R.A l) ((sheetHaar R.A w μG l).restrict Ω) :=
      (integral_map hmp.measurable.aemeasurable
        (by simpa only [hmp.map_eq] using hi.aestronglyMeasurable)).symm
    _ = _ := by rw [hmp.map_eq]

theorem upper_zero (hc : ReindexInvariant R m c)
    (C : ResidualConstantTerm R Q T) (f : sameResidueModule T)
    (hext : GlobalProjectExterior.FullExteriorInvariant R f.val)
    (θ : HeckeCharacter F) (hS : conductorPlaces F θ ⊆ R.A.Sf)
    (u : R.A.UnitQuotient) (b : Bool) (w : InfinitePlace F)
    (hk : heckeComplexWeight F w (R.A.complex_place w) θ ≠ 0)
    (μG : Measure R.A.G) [μG.IsHaarMeasure] (l : PositiveAxis)
    (Ω : Set (Sheet R.A l))
    (hΩ : IsFundamentalDomain R.A.Gamma1 Ω (sheetHaar R.A w μG l)) :
    (∫ y in Ω, GlobalProjectUnfolding.weight R (GlobalTargetPeriod.period R θ u)
      R.probe.correction.B y.val * average R m c (upper R Q.dq f.val) b y.val
      ∂sheetHaar R.A w μG l) = 0 := by
  let L := GlobalTargetPeriod.period R θ u
  let z := GlobalProjectAngular.complexRotation θ w (R.A.complex_place w)
  have hL := GlobalTargetPeriod.period_gamma R θ hS u
  have hext' := GlobalProjectExterior.upper_fullExteriorInvariant R f.val hext
  have hr := core_upper_rationalDiagonalInvariant R f
  have hcont := core_upper_continuous R f
  have hi := GlobalProjectWeightedDigits.quotientAverage_integrable R w μG L hL
    (GlobalTargetPeriod.period_measurable R θ u) (GlobalTargetPeriod.period_norm R θ u)
    m c hc (upper R Q.dq f.val) hcont hr hext' b l
  rw [fundamental_integral R m c hc w μG l Ω hΩ L hL
    (GlobalTargetPeriod.period_measurable R θ u) (GlobalTargetPeriod.period_norm R θ u)
    (upper R Q.dq f.val) hcont hr hext' b]
  apply GlobalProjectAngular.quotient_weighted_constantTerm_zero R w μG l
    L R.probe.correction.B z (GlobalProjectAngular.complexRotation_norm θ w _)
    (GlobalTargetPeriod.period_rotation R θ u w _ hk)
    (average R m c (upper R Q.dq f.val) b)
    (GlobalProjectWeightedDigits.quotientAverage R L m c (upper R Q.dq f.val) b l) hi
  · exact GlobalProjectWeightedDigits.quotientAverage_projection
      R L hL m c hc (upper R Q.dq f.val) hr hext' b l
  · intro y
    unfold average
    apply Finset.sum_congr rfl
    intro d _
    rw [GlobalProjectRadial.sameResidue_upper_signedArgument_rotation R C f m b w z
      (GlobalProjectAngular.complexRotation_norm θ w _) y d]

theorem coefficient_integrable
    (w : InfinitePlace F) (μG : Measure R.A.G) [μG.IsHaarMeasure]
    (l : PositiveAxis) (Ω : Set (Sheet R.A l)) (hΩ : IsCompact (closure Ω))
    (θ : HeckeCharacter F) (u : R.A.UnitQuotient)
    (f : sameResidueModule T) (b : Bool) (a : F) :
    Integrable (fun y : Sheet R.A l =>
      GlobalProjectUnfolding.weight R (GlobalTargetPeriod.period R θ u) R.probe.correction.B y.val *
      ∑ d, c d * GlobalCoreSource.rationalPeriod T f a (signedArgument R m b y.val d))
        ((sheetHaar R.A w μG l).restrict Ω) := by
  have hf : Continuous (fun y : R.A.G => ∑ d, c d *
      GlobalCoreSource.rationalPeriod T f a (signedArgument R m b y d)) := by
    apply continuous_finset_sum
    intro d _
    exact continuous_const.mul
      ((GlobalProjectSheetReflection.rationalPeriod_continuous R f a).comp
        (DigitMasks.signedArgument_continuous R m b d))
  have hi : IntegrableOn (fun y : Sheet R.A l => ∑ d, c d *
      GlobalCoreSource.rationalPeriod T f a (signedArgument R m b y.val d))
      Ω (sheetHaar R.A w μG l) :=
    ((hf.comp continuous_subtype_val).continuousOn.integrableOn_compact hΩ).mono_set subset_closure
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

theorem coefficient_abs_summable
    (w : InfinitePlace F) (μG : Measure R.A.G) [μG.IsHaarMeasure]
    (l : PositiveAxis) (Ω : Set (Sheet R.A l))
    (hΩm : NullMeasurableSet Ω (sheetHaar R.A w μG l))
    (hΩc : IsCompact (closure Ω))
    (θ : HeckeCharacter F) (u : R.A.UnitQuotient) (f : sameResidueModule T) (b : Bool) :
    Summable (fun a : Fˣ => ∫ y in Ω,
      ‖GlobalProjectUnfolding.weight R (GlobalTargetPeriod.period R θ u) R.probe.correction.B y.val *
        ∑ d, c d * GlobalCoreSource.rationalPeriod T f (a : F)
          (signedArgument R m b y.val d)‖ ∂sheetHaar R.A w μG l) := by
  let μ := sheetHaar R.A w μG l
  let P := closure Ω
  letI : CompactSpace P := isCompact_iff_compactSpace.mp hΩc
  letI : IsFiniteMeasure (μ.restrict Ω) :=
    isFiniteMeasure_restrict.mpr
      (lt_of_le_of_lt (measure_mono subset_closure) hΩc.measure_lt_top).ne
  have hd (d : GlobalProjectWeightedDigits.Digits R m) :
      ∃ B : F → ℝ, Summable B ∧ (∀ a, 0 ≤ B a) ∧
        ∀ p : P, ∀ a, ‖GlobalCoreSource.rationalPeriod T f a
          (signedArgument R m b p.val.val d)‖ ≤ B a :=
    GlobalProjectUniformFourier.compact_rationalPeriod_majorant R f
      (fun p : P => signedArgument R m b p.val.val d)
      ((DigitMasks.signedArgument_continuous R m b d).comp
        (continuous_subtype_val.comp continuous_subtype_val))
  choose B hBs hBpos hBbound using hd
  let M : F → ℝ := fun a => ∑ d, ‖c d‖ * B d a
  have hMs : Summable M :=
    (hasSum_sum (s := Finset.univ) (fun d _ => ((hBs d).mul_left ‖c d‖).hasSum)).summable
  have hbound (a : F) (y : Sheet R.A l) (hy : y ∈ Ω) :
      ‖GlobalProjectUnfolding.weight R (GlobalTargetPeriod.period R θ u) R.probe.correction.B y.val *
        ∑ d, c d * GlobalCoreSource.rationalPeriod T f a (signedArgument R m b y.val d)‖ ≤ M a := by
    have hw : ‖GlobalProjectUnfolding.weight R (GlobalTargetPeriod.period R θ u)
        R.probe.correction.B y.val‖ ≤ 1 := by
      unfold GlobalProjectUnfolding.weight
      rw [norm_mul, norm_inv, GlobalTargetPeriod.period_norm, inv_one, mul_one]
      split_ifs <;> simp
    calc
      _ ≤ ‖∑ d, c d * GlobalCoreSource.rationalPeriod T f a (signedArgument R m b y.val d)‖ := by
        rw [norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) hw
      _ ≤ ∑ d, ‖c d * GlobalCoreSource.rationalPeriod T f a (signedArgument R m b y.val d)‖ := norm_sum_le _ _
      _ = ∑ d, ‖c d‖ * ‖GlobalCoreSource.rationalPeriod T f a (signedArgument R m b y.val d)‖ := by
        simp only [norm_mul]
      _ ≤ M a := Finset.sum_le_sum (fun d _ => mul_le_mul_of_nonneg_left
          (hBbound d ⟨y, subset_closure hy⟩ a) (norm_nonneg _))
  have hs : Summable (fun a : F => ∫ y in Ω,
      ‖GlobalProjectUnfolding.weight R (GlobalTargetPeriod.period R θ u) R.probe.correction.B y.val *
        ∑ d, c d * GlobalCoreSource.rationalPeriod T f a (signedArgument R m b y.val d)‖ ∂μ) := by
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

/-- Fixed-profile reflection for arbitrary invariant finite digit weights,
including simultaneous ordinary, punctured, and marked places. -/
theorem target_sheet_fourier_identity (hc : ReindexInvariant R m c)
    (C : ResidualConstantTerm R Q T) (f : sameResidueModule T)
    (hext : GlobalProjectExterior.FullExteriorInvariant R f.val)
    (θ : HeckeCharacter F) (hS : conductorPlaces F θ ⊆ R.A.Sf)
    (u : R.A.UnitQuotient) (w : InfinitePlace F)
    (hk : heckeComplexWeight F w (R.A.complex_place w) θ ≠ 0)
    (μG : Measure R.A.G) [μG.IsHaarMeasure] (l : PositiveAxis)
    (Ω : Set (Sheet R.A l))
    (hΩ : IsFundamentalDomain R.A.Gamma1 Ω (sheetHaar R.A w μG l))
    (hΩc : IsCompact (closure Ω)) :
    (∑' a : Fˣ, ∫ y in Ω,
      GlobalProjectUnfolding.weight R (GlobalTargetPeriod.period R θ u) R.probe.correction.B y.val *
        ∑ d, c d * GlobalCoreSource.rationalPeriod T f (a : F)
          (signedArgument R m true y.val d) ∂sheetHaar R.A w μG l) =
    ∑' a : Fˣ, ∫ y in Ω,
      GlobalProjectUnfolding.weight R (GlobalTargetPeriod.period R θ u) R.probe.correction.B y.val *
        ∑ d, c d * GlobalCoreSource.rationalPeriod T f (a : F)
          (signedArgument R m false y.val d) ∂sheetHaar R.A w μG l := by
  let L := GlobalTargetPeriod.period R θ u
  have hL := GlobalTargetPeriod.period_gamma R θ hS u
  have hLm := GlobalTargetPeriod.period_measurable R θ u
  have hLn := GlobalTargetPeriod.period_norm R θ u
  have hs (b) (d) (y : Sheet R.A l) : Summable (fun a : F =>
      ‖GlobalCoreSource.rationalPeriod T f a (signedArgument R m b y.val d)‖) :=
    GlobalProjectFourierSmooth.rationalPeriod_norm_summable R f _
  have habs (b) := coefficient_abs_summable R m c w μG l Ω hΩ.nullMeasurableSet hΩc θ u f b
  have hg (d) (y : Sheet R.A l) :
      KPRationalAdelicSplitting.pglW F R.A.zeta12 R.A.primitive_zeta12 *
        signedArgument R m true y.val d = signedArgument R m false y.val d := by
    simp only [signedArgument, if_true, Bool.false_eq_true, if_false, one_mul, mul_assoc]
  have hθ := fundamental_integrable R m c hc w μG l Ω hΩ L hL hLm hLn
    f.val f.property.2.1 (core_rationalDiagonalInvariant R f) hext true
  have hu (b : Bool) := fundamental_integrable R m c hc w μG l Ω hΩ L hL hLm hLn
    (upper R Q.dq f.val) (core_upper_continuous R f) (core_upper_rationalDiagonalInvariant R f)
    (GlobalProjectExterior.upper_fullExteriorInvariant R f.val hext) b
  have hz (b : Bool) := upper_zero R m c hc C f hext θ hS u b w hk μG l Ω hΩ
  have h := GlobalProjectDescent.actual_rational_fourier_descent T
    ((sheetHaar R.A w μG l).restrict Ω) f
    (fun y => GlobalProjectUnfolding.weight R L R.probe.correction.B y.val)
    c (fun d y => signedArgument R m true y.val d)
    (hs true) (by intro d y; simpa only [hg] using hs false d y)
    (fun a => coefficient_integrable R m c w μG l Ω hΩc θ u f true a)
    (habs true)
    (by intro a; simpa only [hg] using coefficient_integrable R m c w μG l Ω hΩc θ u f false a)
    (by simpa only [hg] using habs false)
    hθ (hu true) (by simpa only [hg] using hu false)
    (hz true) (by simpa only [hg] using hz false)
  simpa only [GlobalProjectDescent.coefficientIntegral, hg] using h

end ThetaGlobal.GlobalProjectWeightedSheet
