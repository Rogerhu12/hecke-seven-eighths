import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.MellinSeparationMass
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.RankedProfileControl

/-!
# A genuine same-geometry front end for a strict moment step

The actual parent, including a whole centered difference, is bounded by
the energies of literal row-independent plain-window models in one
positive measure on `ℝ × ℝ`.  Original prime supports, every common zero
mask, the arithmetic rows and both rectangles remain unchanged.  The
original evaluation time is first frozen, so the produced actual tests
are time-independent, not merely controlled at evaluation time zero.

All kernel and profile constants precede the parent budget, moving model,
row and scale.  The annulus expands explicitly from `[a,b]` to
`[a/2,2*b]`.  No canonical mixed Gram chart or recursive-call permission
is inferred from this preprocessing inequality.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField MeasureTheory Set Filter
open HeckeGeneral.Analysis HeckeGeneral.Characters
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global HeckeSkeleton.ThetaKernel
open HeckeSkeleton.Moments.UniformAmplify
open scoped Classical BigOperators Topology

variable {K : Type} [Field K] [NumberField K]
variable {omegaCharacter psiCharacter : HeckeCharacter K}

/-- Numerical child energy integrability comes from the actual finite
polynomials, without a measurable space on the type of whole models. -/
theorem normalizedMellinPlain_energy_integrable
    (n : Node K omegaCharacter psiCharacter) (B₁ B₂ : SmoothAnnularTest)
    (P : ℝ) (hP : 1 ≤ P) (E : ℝ) (hE : 1 ≤ E) (J : ℕ) (U time : ℝ)
    (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ] :
    Integrable (fun frequency : ℝ × ℝ =>
      (n.normalizedMellinPlain B₁ B₂ P hP E hE J frequency).energy U time) μ := by
  have he (frequency : ℝ × ℝ) :
      (n.normalizedMellinPlain B₁ B₂ P hP E hE J frequency).energy U time =
        ∑ u ∈ pairedRows n.data n.parameters U,
          ‖normalizedMellinPlainRow n B₁ B₂ P E J U time u frequency‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro u hu
    rw [normalizedMellinPlainRow_eq n B₁ B₂ P hP E hE J U time u frequency]
  simp_rw [he]
  exact integrable_finsetSum _ (fun u _ =>
    (normalizedMellinPlainRow_memLp n B₁ B₂ P hP E hE J U time u μ).norm.integrable_sq)

/-- All quantitative premises concern the original profiles only.
The integral identity, normalized child L2 and positive measure are
constructed from the literal parent and its actual finite rows. -/
theorem Node.energy_le_normalizedMellinPlain_kernel
    (n : Node K omegaCharacter psiCharacter) (cap J : ℕ)
    (hcap : n.data.geometry.slotCount ≤ cap) (B₁ B₂ : SmoothAnnularTest)
    (V₁ V₂ : NonzeroIdeal K → SmoothAnnularTest)
    (P : ℝ) (hP : 1 ≤ P) (E : ℝ) (hE : 1 ≤ E)
    (U time : ℝ) (hU : 0 < U)
    (hV₁ : ∀ u ∈ pairedRows n.data n.parameters U,
      (V₁ u).toFun = n.data.plainTest₁.profile u time)
    (hV₂ : ∀ u ∈ pairedRows n.data n.parameters U,
      (V₂ u).toFun = n.data.plainTest₂.profile u time)
    (hB₁ : ∀ u ∈ pairedRows n.data n.parameters U,
      ∀ y, (V₁ u).toFun y ≠ 0 → B₁.toFun y = 1)
    (hB₂ : ∀ u ∈ pairedRows n.data n.parameters U,
      ∀ y, (V₂ u).toFun y ≠ 0 → B₂.toFun y = 1)
    (hS₁ : ∀ u ∈ pairedRows n.data n.parameters U,
      testSeminorm (V₁ u).toFun (J + 2) 0 ≤ P)
    (hS₂ : ∀ u ∈ pairedRows n.data n.parameters U,
      testSeminorm (V₂ u).toFun (J + 2) 0 ≤ P) :
    n.energy U time ≤ ∫ frequency : ℝ × ℝ,
      (n.normalizedMellinPlain B₁ B₂ P hP E hE J frequency).energy U time
      ∂rowEnergyKernel ((volume : Measure ℝ).prod volume) (mellinPairEnvelope cap J P E) := by
  let μ : Measure (ℝ × ℝ) := (volume : Measure ℝ).prod volume
  let weight := mellinPairEnvelope cap J P E
  let coefficient := fun u frequency =>
    (mellinNormalizationAmplitude n.data.geometry.slotCount P E J frequency : ℂ) *
      mellinPairCoefficient (V₁ u) (V₂ u) frequency
  let row := normalizedMellinPlainRow n B₁ B₂ P E J U time
  have hw : ∀ frequency, 0 ≤ weight frequency :=
    mellinPairEnvelope_nonneg cap J (P := P) (E := E) (zero_le_one.trans hP)
  have hi := integrable_mellinPairEnvelope cap J P E
  letI : IsFiniteMeasure (kernelWeightedMeasure μ weight) :=
    kernelWeightedMeasure_finite μ hw hi
  have hint (u : NonzeroIdeal K) : Integrable (fun frequency => coefficient u frequency *
      row u frequency) μ := by
    apply (integrable_mellinPairCoefficient_row n B₁ B₂ (V₁ u) (V₂ u) U time u).congr
    exact Filter.Eventually.of_forall fun frequency =>
      (normalizedMellinPlainRow_integrand n B₁ B₂ (V₁ u) (V₂ u) P hP E hE
        J U time u frequency).symm
  have hrow (u : NonzeroIdeal K) (hu : u ∈ pairedRows n.data n.parameters U) :
      n.plainPair u U time * slotProduct n.data u U time =
        ∫ frequency, coefficient u frequency * row u frequency ∂μ := by
    rw [n.mellinPlain_row_identity u U time hU B₁ B₂ (V₁ u) (V₂ u)
      (hV₁ u hu) (hV₂ u hu) (hB₁ u hu) (hB₂ u hu)]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun frequency =>
      (normalizedMellinPlainRow_integrand n B₁ B₂ (V₁ u) (V₂ u) P hP E hE
        J U time u frequency).symm
  have h := finite_rows_energy_le_rowEnergyKernel μ (pairedRows n.data n.parameters U)
    (measurable_mellinPairEnvelope cap J P E) hw hi coefficient row
    (fun u _ => normalizedMellinPlainRow_memLp n B₁ B₂ P hP E hE J U time u _)
    (fun u _ => hint u) (fun u hu => Filter.Eventually.of_forall
      (normalizedMellinPairCoefficient_bound cap J n.data.geometry.slotCount hcap hP hE
        (V₁ u) (V₂ u) (hS₁ u hu) (hS₂ u hu)))
  have hleft : n.energy U time = ∑ u ∈ pairedRows n.data n.parameters U,
      ‖∫ frequency, coefficient u frequency * row u frequency ∂μ‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro u hu
    rw [hrow u hu]
  rw [hleft]
  apply h.trans_eq
  apply integral_congr_ae
  filter_upwards [] with frequency
  apply Finset.sum_congr rfl
  intro u hu
  dsimp only [row]
  rw [normalizedMellinPlainRow_eq n B₁ B₂ P hP E hE J U time u frequency]

/-- A complete local frontend with constants chosen before all moving
profiles.  The original profile bound is paid to exactly the fixed
power `2*(cap+2)`; the factor two from removing the A-weight is explicit.
The actual output has fixed row-independent plain profiles and retains
the original prime windows, scaled by a single positive constant. -/
theorem exists_centeredMellin_preprocessing (cap J : ℕ) (A a b : ℝ)
    (hA : 0 ≤ A) (ha : 0 < a) (hab : a ≤ b) :
    ∃ E : ℝ, ∃ hE : 1 ≤ E, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (P : ℝ) (hP : 1 ≤ P),
      let hP₂ : 1 ≤ 2 * P := by linarith
      let B := annularPlateau a b ha hab
      let μ := rowEnergyKernel ((volume : Measure ℝ).prod volume)
        (mellinPairEnvelope cap J (2 * P) E)
      ∀ (n : Node K omegaCharacter psiCharacter) (U : ℝ), 0 < U →
        n.data.geometry.slotCount ≤ cap →
        ModelProfileControl n.data (J + 2) A P 0 a b 0 →
        IsFiniteMeasure μ ∧ μ.real Set.univ = C * P ^ (2 * (cap + 2)) ∧
        (∀ frequency : ℝ × ℝ,
          ProfileTimeIndependent
            ((n.freezeTime 0).normalizedMellinPlain B B (2 * P) hP₂ E hE J frequency).data ∧
          ModelProfileControl
            ((n.freezeTime 0).normalizedMellinPlain B B (2 * P) hP₂ E hE J frequency).data
              J A 1 0 (a / 2) (2 * b) 0) ∧
        Integrable (fun frequency : ℝ × ℝ =>
          ((n.freezeTime 0).normalizedMellinPlain B B (2 * P) hP₂ E hE J frequency).energy U 0) μ ∧
        n.energy U 0 ≤ ∫ frequency : ℝ × ℝ,
          ((n.freezeTime 0).normalizedMellinPlain B B (2 * P) hP₂ E hE J frequency).energy U 0 ∂μ := by
  let B := annularPlateau a b ha hab
  obtain ⟨E, hE, hcontrol⟩ := exists_normalizedMellinPlain_control
    (K := K) (omegaCharacter := omegaCharacter) (psiCharacter := psiCharacter) B B J A
  let C := mellinKernelMassConstant J E * 2 ^ (2 * (cap + 2))
  have hC : 0 ≤ C := mul_nonneg (by unfold mellinKernelMassConstant; positivity) (by positivity)
  refine ⟨E, hE, C, hC, ?_⟩
  intro P hP
  dsimp only
  intro n U hU hcap hprofile
  have hP₂ : 1 ≤ 2 * P := by linarith
  let nf := n.freezeTime 0
  have hf : ModelProfileControl nf.data (J + 2) A P 0 a b 0 :=
    freezeMomentTime_zero_control hprofile
  have hz := modelProfileControl_weight_zero hf hA ha hab
  let V₁ : NonzeroIdeal K → SmoothAnnularTest := fun u =>
    sliceControlAnnularTest (modelProfileControl_plain₁ hz u) ha hab
  let V₂ : NonzeroIdeal K → SmoothAnnularTest := fun u =>
    sliceControlAnnularTest (modelProfileControl_plain₂ hz u) ha hab
  have hB₁ (u : NonzeroIdeal K) (y : ℝ) (hy : (V₁ u).toFun y ≠ 0) : B.toFun y = 1 :=
    annularPlateau_eq_one a b ha hab ((modelProfileControl_plain₁ hz u).2.1 y hy)
  have hB₂ (u : NonzeroIdeal K) (y : ℝ) (hy : (V₂ u).toFun y ≠ 0) : B.toFun y = 1 :=
    annularPlateau_eq_one a b ha hab ((modelProfileControl_plain₂ hz u).2.1 y hy)
  have hS₁ (u : NonzeroIdeal K) : testSeminorm (V₁ u).toFun (J + 2) 0 ≤ 2 * P := by
    change testSeminorm (nf.data.plainTest₁.profile u 0) (J + 2) 0 ≤ 2 * P
    simpa only [Real.rpow_zero, mul_one] using (modelProfileControl_plain₁ hz u).2.2
  have hS₂ (u : NonzeroIdeal K) : testSeminorm (V₂ u).toFun (J + 2) 0 ≤ 2 * P := by
    change testSeminorm (nf.data.plainTest₂.profile u 0) (J + 2) 0 ≤ 2 * P
    simpa only [Real.rpow_zero, mul_one] using (modelProfileControl_plain₂ hz u).2.2
  have hparent : ModelProfileControl nf.data J A (2 * P) 0 (a / 2) (2 * b) 0 := by
    have hj := modelProfileControl_mono_order hf (show J ≤ J + 2 by omega)
    intro q
    refine ⟨(hj q).1, ?_, ?_⟩
    · intro y hy
      have hs := (hj q).2.1 y hy
      constructor <;> linarith
    · have hn := (hj q).2.2
      simp only [Real.rpow_zero, mul_one] at hn ⊢
      linarith
  let μ := rowEnergyKernel ((volume : Measure ℝ).prod volume)
    (mellinPairEnvelope cap J (2 * P) E)
  have hfinite : IsFiniteMeasure μ := rowEnergyKernel_finite _
    (mellinPairEnvelope_nonneg cap J (by linarith : 0 ≤ 2 * P))
    (integrable_mellinPairEnvelope cap J (2 * P) E)
  letI : IsFiniteMeasure μ := hfinite
  refine ⟨hfinite, ?_, ?_, ?_, ?_⟩
  · rw [mellinPairEnvelope_kernel_mass cap J (by linarith : 0 ≤ 2 * P), mul_pow]
    dsimp only [C]
    ring
  · intro frequency
    refine ⟨normalizedMellinPlainData_timeIndependent nf.data
      (profileTimeIndependent_freezeMomentTime n.data 0) B B (2 * P) hP₂ E hE J frequency, ?_⟩
    exact hcontrol nf.data (2 * P) hP₂ (a / 2) (2 * b) hparent B.support B.support frequency
  · exact normalizedMellinPlain_energy_integrable nf B B (2 * P) hP₂ E hE J U 0 μ
  · have h := nf.energy_le_normalizedMellinPlain_kernel cap J hcap B B V₁ V₂
      (2 * P) hP₂ E hE U 0 hU (fun _ _ => rfl) (fun _ _ => rfl)
      (fun u _ => hB₁ u) (fun u _ => hB₂ u) (fun u _ => hS₁ u) (fun u _ => hS₂ u)
    simpa only [nf, Node.freezeTime_energy] using h

end HeckeSkeleton.Moments.EngineInduction
