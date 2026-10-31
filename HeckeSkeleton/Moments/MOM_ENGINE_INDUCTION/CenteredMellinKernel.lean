import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.PlainMellinProfiles
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.RowIntegralKernel
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Whole-centered Mellin separation on the original rows

Only the two plain tests are replaced.  Every prime profile and its exact
support stay literal.  One pair of Mellin coefficients multiplies both
rectangles, before the absolute square is taken.  A common positive
two-dimensional kernel then removes the row-dependent coefficients,
without any factor counting the arithmetic rows.

This is an internal same-geometry preprocessing inequality.  It is not a
recursive call, and supplies no earlier-state or canonical-source proof.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField MeasureTheory Set Filter
open HeckeGeneral.Analysis HeckeGeneral.Characters
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global HeckeSkeleton.ThetaKernel
open scoped Classical BigOperators Topology

variable {K : Type} [Field K] [NumberField K]
variable {omegaCharacter psiCharacter : HeckeCharacter K}

/-- Fixed row-independent plain windows at a common frequency pair.
All prime profiles and all arithmetic fields are the original fields. -/
def mellinPlainData (d : MomentData K omegaCharacter psiCharacter)
    (B₁ B₂ : SmoothAnnularTest) (frequency : ℝ × ℝ) :
    MomentData K omegaCharacter psiCharacter :=
  { d with
    plainTest₁ := (annularMellinIdealTest K B₁).freezeTwist
      (fun _ => frequency.1) (fun _ => 0)
    plainTest₂ := (annularMellinIdealTest K B₂).freezeTwist
      (fun _ => frequency.2) (fun _ => 0) }

/-- The actual centered flag and both equal-product rectangles are retained. -/
def Node.mellinPlain (n : Node K omegaCharacter psiCharacter)
    (B₁ B₂ : SmoothAnnularTest) (frequency : ℝ × ℝ) : Node K omegaCharacter psiCharacter :=
  { n with data := mellinPlainData n.data B₁ B₂ frequency }

theorem Node.mellinPlain_invariants (n : Node K omegaCharacter psiCharacter)
    (B₁ B₂ : SmoothAnnularTest) (frequency : ℝ × ℝ) (U time : ℝ) :
    (n.mellinPlain B₁ B₂ frequency).parameters = n.parameters ∧
    (n.mellinPlain B₁ B₂ frequency).width = n.width ∧
    (n.mellinPlain B₁ B₂ frequency).centered = n.centered ∧
    (n.mellinPlain B₁ B₂ frequency).data.geometry = n.data.geometry ∧
    (n.mellinPlain B₁ B₂ frequency).data.commonMask = n.data.commonMask ∧
    (n.mellinPlain B₁ B₂ frequency).data.rowCharacter = n.data.rowCharacter ∧
    pairedRows (n.mellinPlain B₁ B₂ frequency).data n.parameters U =
      pairedRows n.data n.parameters U ∧
    (∀ u, slotProduct (n.mellinPlain B₁ B₂ frequency).data u U time =
      slotProduct n.data u U time) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩

private theorem mellinPlain_left (d : MomentData K omegaCharacter psiCharacter)
    (B₁ B₂ : SmoothAnnularTest) (frequency : ℝ × ℝ)
    (u : NonzeroIdeal K) (N time : ℝ) :
    plainPolynomial (mellinPlainData d B₁ B₂ frequency)
      (mellinPlainData d B₁ B₂ frequency).plainTest₁ u N time =
        annularMellinPlainColumn d B₁ u N frequency.1 := by
  simp only [plainPolynomial, mellinPlainData, IdealTest.freezeTwist,
    profilePower_zero, mul_one, annularMellinPlainColumn, maskValue]

private theorem mellinPlain_right (d : MomentData K omegaCharacter psiCharacter)
    (B₁ B₂ : SmoothAnnularTest) (frequency : ℝ × ℝ)
    (u : NonzeroIdeal K) (N time : ℝ) :
    plainPolynomial (mellinPlainData d B₁ B₂ frequency)
      (mellinPlainData d B₁ B₂ frequency).plainTest₂ u N time =
        annularMellinPlainColumn d B₂ u N frequency.2 := by
  simp only [plainPolynomial, mellinPlainData, IdealTest.freezeTwist,
    profilePower_zero, mul_one, annularMellinPlainColumn, maskValue]

/-- Literal common-frequency row amplitude, with every original slot. -/
def mellinPlainRow (n : Node K omegaCharacter psiCharacter)
    (B₁ B₂ : SmoothAnnularTest) (U time : ℝ) (u : NonzeroIdeal K)
    (frequency : ℝ × ℝ) : ℂ :=
  (n.mellinPlain B₁ B₂ frequency).plainPair u U time * slotProduct n.data u U time

private theorem mellinPlainRow_eq (n : Node K omegaCharacter psiCharacter)
    (B₁ B₂ : SmoothAnnularTest) (U time : ℝ) (u : NonzeroIdeal K)
    (frequency : ℝ × ℝ) :
    mellinPlainRow n B₁ B₂ U time u frequency =
      (annularMellinPlainColumn n.data B₁ u (U ^ n.parameters.n₁) frequency.1 *
        annularMellinPlainColumn n.data B₂ u (U ^ n.parameters.n₂) frequency.2 -
        if n.centered then
          annularMellinPlainColumn n.data B₁ u (U ^ n.comparison₁) frequency.1 *
            annularMellinPlainColumn n.data B₂ u (U ^ n.comparison₂) frequency.2
        else 0) * slotProduct n.data u U time := by
  unfold mellinPlainRow Node.plainPair Node.mellinPlain
  rw [mellinPlain_left, mellinPlain_right, mellinPlain_left, mellinPlain_right]

theorem continuous_mellinPlainRow (n : Node K omegaCharacter psiCharacter)
    (B₁ B₂ : SmoothAnnularTest) (U time : ℝ) (u : NonzeroIdeal K) :
    Continuous (mellinPlainRow n B₁ B₂ U time u) := by
  change Continuous (fun frequency : ℝ × ℝ => mellinPlainRow n B₁ B₂ U time u frequency)
  simp_rw [mellinPlainRow_eq]
  have hprimary := ((continuous_annularMellinPlainColumn n.data B₁ u
    (U ^ n.parameters.n₁)).comp continuous_fst).mul
      ((continuous_annularMellinPlainColumn n.data B₂ u
        (U ^ n.parameters.n₂)).comp continuous_snd)
  have hcomparison := ((continuous_annularMellinPlainColumn n.data B₁ u
    (U ^ n.comparison₁)).comp continuous_fst).mul
      ((continuous_annularMellinPlainColumn n.data B₂ u
        (U ^ n.comparison₂)).comp continuous_snd)
  by_cases hc : n.centered = true
  · simpa only [hc, ite_true] using (hprimary.sub hcomparison).mul continuous_const
  · simpa only [hc, ite_false, sub_zero] using hprimary.mul continuous_const

theorem mellinPlainRow_bounded (n : Node K omegaCharacter psiCharacter)
    (B₁ B₂ : SmoothAnnularTest) (U time : ℝ) (u : NonzeroIdeal K) :
    ∃ C : ℝ, ∀ frequency : ℝ × ℝ, ‖mellinPlainRow n B₁ B₂ U time u frequency‖ ≤ C := by
  obtain ⟨C₁, hC₁⟩ := annularMellinPlainColumn_bounded n.data B₁ u (U ^ n.parameters.n₁)
  obtain ⟨C₂, hC₂⟩ := annularMellinPlainColumn_bounded n.data B₂ u (U ^ n.parameters.n₂)
  obtain ⟨D₁, hD₁⟩ := annularMellinPlainColumn_bounded n.data B₁ u (U ^ n.comparison₁)
  obtain ⟨D₂, hD₂⟩ := annularMellinPlainColumn_bounded n.data B₂ u (U ^ n.comparison₂)
  have hC₁n : 0 ≤ C₁ := (norm_nonneg _).trans (hC₁ 0)
  have hC₂n : 0 ≤ C₂ := (norm_nonneg _).trans (hC₂ 0)
  have hD₁n : 0 ≤ D₁ := (norm_nonneg _).trans (hD₁ 0)
  have hD₂n : 0 ≤ D₂ := (norm_nonneg _).trans (hD₂ 0)
  refine ⟨(C₁ * C₂ + D₁ * D₂) * ‖slotProduct n.data u U time‖, fun frequency => ?_⟩
  rw [mellinPlainRow_eq, norm_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply (norm_sub_le _ _).trans
  apply add_le_add
  · rw [norm_mul]
    exact mul_le_mul (hC₁ frequency.1) (hC₂ frequency.2) (norm_nonneg _) hC₁n
  · by_cases hc : n.centered = true
    · rw [if_pos hc, norm_mul]
      exact mul_le_mul (hD₁ frequency.1) (hD₂ frequency.2) (norm_nonneg _) hD₁n
    · rw [if_neg hc, norm_zero]
      exact mul_nonneg hD₁n hD₂n

theorem mellinPlainRow_memLp (n : Node K omegaCharacter psiCharacter)
    (B₁ B₂ : SmoothAnnularTest) (U time : ℝ) (u : NonzeroIdeal K)
    (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ] :
    MemLp (mellinPlainRow n B₁ B₂ U time u) 2 μ := by
  obtain ⟨C, hC⟩ := mellinPlainRow_bounded n B₁ B₂ U time u
  exact MemLp.of_bound (continuous_mellinPlainRow n B₁ B₂ U time u).aestronglyMeasurable C
    (Filter.Eventually.of_forall hC)

/-- The product of the two original Mellin coefficients, common to both
rectangles and independent of every plain length. -/
def mellinPairCoefficient (V₁ V₂ : SmoothAnnularTest) (frequency : ℝ × ℝ) : ℂ :=
  annularMellinCoefficient V₁ frequency.1 * annularMellinCoefficient V₂ frequency.2

theorem integrable_mellinPairCoefficient_row
    (n : Node K omegaCharacter psiCharacter) (B₁ B₂ V₁ V₂ : SmoothAnnularTest)
    (U time : ℝ) (u : NonzeroIdeal K) :
    Integrable (fun frequency : ℝ × ℝ =>
      mellinPairCoefficient V₁ V₂ frequency * mellinPlainRow n B₁ B₂ U time u frequency)
      ((volume : Measure ℝ).prod volume) := by
  obtain ⟨C, hC⟩ := mellinPlainRow_bounded n B₁ B₂ U time u
  exact ((integrable_annularMellinCoefficient V₁).mul_prod
    (integrable_annularMellinCoefficient V₂)).mul_bdd
      (continuous_mellinPlainRow n B₁ B₂ U time u).aestronglyMeasurable
      (Filter.Eventually.of_forall hC)

private theorem plainPair_product_mellin
    (d : MomentData K omegaCharacter psiCharacter) (u : NonzeroIdeal K)
    (time : ℝ) (B₁ B₂ V₁ V₂ : SmoothAnnularTest)
    (hV₁ : V₁.toFun = d.plainTest₁.profile u time)
    (hV₂ : V₂.toFun = d.plainTest₂.profile u time)
    (hB₁ : ∀ y, V₁.toFun y ≠ 0 → B₁.toFun y = 1)
    (hB₂ : ∀ y, V₂.toFun y ≠ 0 → B₂.toFun y = 1)
    {N₁ N₂ : ℝ} (hN₁ : 0 < N₁) (hN₂ : 0 < N₂) :
    plainPolynomial d d.plainTest₁ u N₁ time * plainPolynomial d d.plainTest₂ u N₂ time =
      ∫ frequency : ℝ × ℝ, mellinPairCoefficient V₁ V₂ frequency *
        (annularMellinPlainColumn d B₁ u N₁ frequency.1 *
          annularMellinPlainColumn d B₂ u N₂ frequency.2)
          ∂((volume : Measure ℝ).prod volume) := by
  rw [plainPolynomial_annularMellin_separation d d.plainTest₁ u time B₁ V₁ hV₁ hB₁ hN₁,
    plainPolynomial_annularMellin_separation d d.plainTest₂ u time B₂ V₂ hV₂ hB₂ hN₂,
    ← integral_prod_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun frequency => by
    unfold mellinPairCoefficient
    ring

/-- A genuine two-variable Fubini identity for the entire original
centered row.  It includes all prime factors without separating them. -/
theorem Node.mellinPlain_row_identity (n : Node K omegaCharacter psiCharacter)
    (u : NonzeroIdeal K) (U time : ℝ) (hU : 0 < U)
    (B₁ B₂ V₁ V₂ : SmoothAnnularTest)
    (hV₁ : V₁.toFun = n.data.plainTest₁.profile u time)
    (hV₂ : V₂.toFun = n.data.plainTest₂.profile u time)
    (hB₁ : ∀ y, V₁.toFun y ≠ 0 → B₁.toFun y = 1)
    (hB₂ : ∀ y, V₂.toFun y ≠ 0 → B₂.toFun y = 1) :
    n.plainPair u U time * slotProduct n.data u U time =
      ∫ frequency : ℝ × ℝ, mellinPairCoefficient V₁ V₂ frequency *
        mellinPlainRow n B₁ B₂ U time u frequency
        ∂((volume : Measure ℝ).prod volume) := by
  let primary : ℝ × ℝ → ℂ := fun frequency =>
    (annularMellinCoefficient V₁ frequency.1 *
      annularMellinPlainColumn n.data B₁ u (U ^ n.parameters.n₁) frequency.1) *
    (annularMellinCoefficient V₂ frequency.2 *
      annularMellinPlainColumn n.data B₂ u (U ^ n.parameters.n₂) frequency.2)
  let comparison : ℝ × ℝ → ℂ := fun frequency =>
    (annularMellinCoefficient V₁ frequency.1 *
      annularMellinPlainColumn n.data B₁ u (U ^ n.comparison₁) frequency.1) *
    (annularMellinCoefficient V₂ frequency.2 *
      annularMellinPlainColumn n.data B₂ u (U ^ n.comparison₂) frequency.2)
  have hprimary : Integrable primary ((volume : Measure ℝ).prod volume) :=
    (integrable_annularMellinCoefficient_plainColumn n.data B₁ V₁ u _).mul_prod
      (integrable_annularMellinCoefficient_plainColumn n.data B₂ V₂ u _)
  have hcomparison : Integrable comparison ((volume : Measure ℝ).prod volume) :=
    (integrable_annularMellinCoefficient_plainColumn n.data B₁ V₁ u _).mul_prod
      (integrable_annularMellinCoefficient_plainColumn n.data B₂ V₂ u _)
  have hp : plainPolynomial n.data n.data.plainTest₁ u (U ^ n.parameters.n₁) time *
      plainPolynomial n.data n.data.plainTest₂ u (U ^ n.parameters.n₂) time =
        ∫ frequency, primary frequency ∂((volume : Measure ℝ).prod volume) := by
    rw [plainPolynomial_annularMellin_separation n.data n.data.plainTest₁ u time
        B₁ V₁ hV₁ hB₁ (Real.rpow_pos_of_pos hU _),
      plainPolynomial_annularMellin_separation n.data n.data.plainTest₂ u time
        B₂ V₂ hV₂ hB₂ (Real.rpow_pos_of_pos hU _)]
    exact (integral_prod_mul _ _).symm
  have hq : plainPolynomial n.data n.data.plainTest₁ u (U ^ n.comparison₁) time *
      plainPolynomial n.data n.data.plainTest₂ u (U ^ n.comparison₂) time =
        ∫ frequency, comparison frequency ∂((volume : Measure ℝ).prod volume) := by
    rw [plainPolynomial_annularMellin_separation n.data n.data.plainTest₁ u time
        B₁ V₁ hV₁ hB₁ (Real.rpow_pos_of_pos hU _),
      plainPolynomial_annularMellin_separation n.data n.data.plainTest₂ u time
        B₂ V₂ hV₂ hB₂ (Real.rpow_pos_of_pos hU _)]
    exact (integral_prod_mul _ _).symm
  unfold Node.plainPair
  by_cases hc : n.centered = true
  · rw [if_pos hc, hp, hq, ← integral_sub hprimary hcomparison, ← integral_mul_const]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun frequency => by
      rw [mellinPlainRow_eq, if_pos hc]
      dsimp only [primary, comparison, mellinPairCoefficient]
      ring
  · rw [if_neg hc, sub_zero, hp, ← integral_mul_const]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun frequency => by
      rw [mellinPlainRow_eq, if_neg hc, sub_zero]
      dsimp only [primary, mellinPairCoefficient]
      ring

/-- Any proved common coefficient envelope gives an actual energy kernel.
The hypotheses below are numerical integrability/envelope facts only;
the parent identity and child L2 are proved from the actual polynomials. -/
theorem Node.energy_le_mellinPlain_kernel (n : Node K omegaCharacter psiCharacter)
    (B₁ B₂ : SmoothAnnularTest) (V₁ V₂ : NonzeroIdeal K → SmoothAnnularTest)
    (U time : ℝ) (hU : 0 < U)
    (hV₁ : ∀ u ∈ pairedRows n.data n.parameters U,
      (V₁ u).toFun = n.data.plainTest₁.profile u time)
    (hV₂ : ∀ u ∈ pairedRows n.data n.parameters U,
      (V₂ u).toFun = n.data.plainTest₂.profile u time)
    (hB₁ : ∀ u ∈ pairedRows n.data n.parameters U,
      ∀ y, (V₁ u).toFun y ≠ 0 → B₁.toFun y = 1)
    (hB₂ : ∀ u ∈ pairedRows n.data n.parameters U,
      ∀ y, (V₂ u).toFun y ≠ 0 → B₂.toFun y = 1)
    (weight : ℝ × ℝ → ℝ) (hwmeas : Measurable weight)
    (hwnonneg : ∀ frequency, 0 ≤ weight frequency)
    (hweight : Integrable weight ((volume : Measure ℝ).prod volume))
    (hcoeff : ∀ u ∈ pairedRows n.data n.parameters U, ∀ frequency,
      ‖mellinPairCoefficient (V₁ u) (V₂ u) frequency‖ ≤ weight frequency) :
    n.energy U time ≤ ∫ frequency : ℝ × ℝ,
      (n.mellinPlain B₁ B₂ frequency).energy U time
      ∂rowEnergyKernel ((volume : Measure ℝ).prod volume) weight := by
  let μ : Measure (ℝ × ℝ) := (volume : Measure ℝ).prod volume
  letI : IsFiniteMeasure (kernelWeightedMeasure μ weight) :=
    kernelWeightedMeasure_finite μ hwnonneg hweight
  have h := finite_rows_energy_le_rowEnergyKernel μ (pairedRows n.data n.parameters U)
    hwmeas hwnonneg hweight (fun u => mellinPairCoefficient (V₁ u) (V₂ u))
    (mellinPlainRow n B₁ B₂ U time)
    (fun u _ => mellinPlainRow_memLp n B₁ B₂ U time u _)
    (fun u _ => integrable_mellinPairCoefficient_row n B₁ B₂ (V₁ u) (V₂ u) U time u)
    (fun u hu => Filter.Eventually.of_forall (hcoeff u hu))
  have hleft : n.energy U time =
      ∑ u ∈ pairedRows n.data n.parameters U,
        ‖∫ frequency, mellinPairCoefficient (V₁ u) (V₂ u) frequency *
          mellinPlainRow n B₁ B₂ U time u frequency ∂μ‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro u hu
    rw [n.mellinPlain_row_identity u U time hU B₁ B₂ (V₁ u) (V₂ u)
      (hV₁ u hu) (hV₂ u hu) (hB₁ u hu) (hB₂ u hu)]
  rw [hleft]
  apply h.trans_eq
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun frequency => rfl

end HeckeSkeleton.Moments.EngineInduction
