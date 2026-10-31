import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.CenteredMellinKernel
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.AnnularMellinWindowControl
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.ProfileTimeIndependent

/-!
# Separate normalization of the two Mellin windows and original slots

Each fixed plain window is divided by its own genuine frequency envelope.
The original inverse and every original prime test are divided by the
same positive parent profile bound `P`.  Prime supports are unchanged.
The exact removed row amplitude is `E(t₁) E(t₂) P^slotCount`.

The entire centered row is scaled by that one amplitude, so its common
Mellin coefficient is still the same for both rectangles.  No derivative
bound for an arbitrary Fourier frequency is postulated.
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

/-- Separate positive normalizers avoid charging the parent profile
bound a second time to the two new row-independent windows. -/
def normalizedMellinPlainData (d : MomentData K omegaCharacter psiCharacter)
    (B₁ B₂ : SmoothAnnularTest) (P : ℝ) (hP : 1 ≤ P)
    (E : ℝ) (hE : 1 ≤ E) (J : ℕ) (frequency : ℝ × ℝ) :
    MomentData K omegaCharacter psiCharacter :=
  { d with
    inverseTest := scaledIdealTest d.inverseTest P⁻¹
      (inv_pos.mpr (zero_lt_one.trans_le hP))
    plainTest₁ := scaledIdealTest (mellinPlainData d B₁ B₂ frequency).plainTest₁
      (ordinaryProfileEnvelope E J frequency.1)⁻¹
      (inv_pos.mpr (zero_lt_one.trans_le (one_le_ordinaryProfileEnvelope hE J frequency.1)))
    plainTest₂ := scaledIdealTest (mellinPlainData d B₁ B₂ frequency).plainTest₂
      (ordinaryProfileEnvelope E J frequency.2)⁻¹
      (inv_pos.mpr (zero_lt_one.trans_le (one_le_ordinaryProfileEnvelope hE J frequency.2)))
    geometry := scaledGeometry d.geometry P⁻¹
      (inv_pos.mpr (zero_lt_one.trans_le hP)) }

def Node.normalizedMellinPlain (n : Node K omegaCharacter psiCharacter)
    (B₁ B₂ : SmoothAnnularTest) (P : ℝ) (hP : 1 ≤ P)
    (E : ℝ) (hE : 1 ≤ E) (J : ℕ) (frequency : ℝ × ℝ) :
    Node K omegaCharacter psiCharacter :=
  { n with data := normalizedMellinPlainData n.data B₁ B₂ P hP E hE J frequency }

theorem normalizedMellinPlainData_timeIndependent
    (d : MomentData K omegaCharacter psiCharacter) (hd : ProfileTimeIndependent d)
    (B₁ B₂ : SmoothAnnularTest) (P : ℝ) (hP : 1 ≤ P)
    (E : ℝ) (hE : 1 ≤ E) (J : ℕ) (frequency : ℝ × ℝ) :
    ProfileTimeIndependent (normalizedMellinPlainData d B₁ B₂ P hP E hE J frequency) := by
  constructor
  · intro u time
    funext y
    exact congrArg (fun z : ℂ => ((P⁻¹ : ℝ) : ℂ) * z) (congrFun (hd.inverse u time) y)
  · intro u time
    rfl
  · intro u time
    rfl
  · intro i time
    funext y
    exact congrArg (fun z : ℂ => ((P⁻¹ : ℝ) : ℂ) * z) (congrFun (hd.prime i time) y)

/-- No arithmetic geometry or prime support is enlarged by normalization. -/
theorem normalizedMellinPlainData_invariants
    (d : MomentData K omegaCharacter psiCharacter) (B₁ B₂ : SmoothAnnularTest)
    (P : ℝ) (hP : 1 ≤ P) (E : ℝ) (hE : 1 ≤ E) (J : ℕ) (frequency : ℝ × ℝ) :
    (normalizedMellinPlainData d B₁ B₂ P hP E hE J frequency).commonMask = d.commonMask ∧
    (normalizedMellinPlainData d B₁ B₂ P hP E hE J frequency).rows = d.rows ∧
    (normalizedMellinPlainData d B₁ B₂ P hP E hE J frequency).rowCharacter = d.rowCharacter ∧
    (normalizedMellinPlainData d B₁ B₂ P hP E hE J frequency).geometry.slotCount =
      d.geometry.slotCount ∧
    (∀ i, ((normalizedMellinPlainData d B₁ B₂ P hP E hE J frequency).geometry.slots i).length =
      (d.geometry.slots i).length) ∧
    (∀ i, ((normalizedMellinPlainData d B₁ B₂ P hP E hE J frequency).geometry.slots i).support =
      (d.geometry.slots i).support) :=
  ⟨rfl, rfl, rfl, rfl, fun _ => rfl, fun _ => rfl⟩

/-- The exact scalar moved into the common Mellin density. -/
def mellinNormalizationAmplitude (slots : ℕ) (P E : ℝ) (J : ℕ)
    (frequency : ℝ × ℝ) : ℝ :=
  ordinaryProfileEnvelope E J frequency.1 * ordinaryProfileEnvelope E J frequency.2 * P ^ slots

theorem one_le_mellinNormalizationAmplitude (slots : ℕ) {P E : ℝ}
    (hP : 1 ≤ P) (hE : 1 ≤ E) (J : ℕ) (frequency : ℝ × ℝ) :
    1 ≤ mellinNormalizationAmplitude slots P E J frequency :=
  one_le_mul (one_le_mul (one_le_ordinaryProfileEnvelope hE J frequency.1)
    (one_le_ordinaryProfileEnvelope hE J frequency.2)) (one_le_pow₀ hP)

/-- The numerical normalized row is defined by the exact scalar, before
the identity with the actual normalized moment data is proved. -/
def normalizedMellinPlainRow (n : Node K omegaCharacter psiCharacter)
    (B₁ B₂ : SmoothAnnularTest) (P E : ℝ) (J : ℕ) (U time : ℝ)
    (u : NonzeroIdeal K) (frequency : ℝ × ℝ) : ℂ :=
  (mellinNormalizationAmplitude n.data.geometry.slotCount P E J frequency : ℂ)⁻¹ *
    mellinPlainRow n B₁ B₂ U time u frequency

/-- Both rectangles and all prime slots have exactly the same extracted
amplitude.  This is a literal polynomial identity, without an energy bound. -/
theorem normalizedMellinPlainRow_eq (n : Node K omegaCharacter psiCharacter)
    (B₁ B₂ : SmoothAnnularTest) (P : ℝ) (hP : 1 ≤ P)
    (E : ℝ) (hE : 1 ≤ E) (J : ℕ) (U time : ℝ)
    (u : NonzeroIdeal K) (frequency : ℝ × ℝ) :
    normalizedMellinPlainRow n B₁ B₂ P E J U time u frequency =
      (n.normalizedMellinPlain B₁ B₂ P hP E hE J frequency).plainPair u U time *
        slotProduct (n.normalizedMellinPlain B₁ B₂ P hP E hE J frequency).data u U time := by
  let e₁ := ordinaryProfileEnvelope E J frequency.1
  let e₂ := ordinaryProfileEnvelope E J frequency.2
  have he₁ : 0 < e₁ := zero_lt_one.trans_le (one_le_ordinaryProfileEnvelope hE J frequency.1)
  have he₂ : 0 < e₂ := zero_lt_one.trans_le (one_le_ordinaryProfileEnvelope hE J frequency.2)
  have hPn : (P : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (zero_lt_one.trans_le hP).ne'
  have he₁n : (e₁ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr he₁.ne'
  have he₂n : (e₂ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr he₂.ne'
  have hleft (N : ℝ) :
      plainPolynomial (normalizedMellinPlainData n.data B₁ B₂ P hP E hE J frequency)
        (normalizedMellinPlainData n.data B₁ B₂ P hP E hE J frequency).plainTest₁ u N time =
      ((e₁⁻¹ : ℝ) : ℂ) * plainPolynomial (mellinPlainData n.data B₁ B₂ frequency)
        (mellinPlainData n.data B₁ B₂ frequency).plainTest₁ u N time :=
    plainPolynomial_scaledMomentProfiles (mellinPlainData n.data B₁ B₂ frequency)
      (mellinPlainData n.data B₁ B₂ frequency).plainTest₁ e₁⁻¹ (inv_pos.mpr he₁) u N time
  have hright (N : ℝ) :
      plainPolynomial (normalizedMellinPlainData n.data B₁ B₂ P hP E hE J frequency)
        (normalizedMellinPlainData n.data B₁ B₂ P hP E hE J frequency).plainTest₂ u N time =
      ((e₂⁻¹ : ℝ) : ℂ) * plainPolynomial (mellinPlainData n.data B₁ B₂ frequency)
        (mellinPlainData n.data B₁ B₂ frequency).plainTest₂ u N time :=
    plainPolynomial_scaledMomentProfiles (mellinPlainData n.data B₁ B₂ frequency)
      (mellinPlainData n.data B₁ B₂ frequency).plainTest₂ e₂⁻¹ (inv_pos.mpr he₂) u N time
  have hslots :
      slotProduct (normalizedMellinPlainData n.data B₁ B₂ P hP E hE J frequency) u U time =
        ((P⁻¹ : ℝ) : ℂ) ^ n.data.geometry.slotCount * slotProduct n.data u U time :=
    slotProduct_scaledMomentProfiles n.data P⁻¹ (inv_pos.mpr (zero_lt_one.trans_le hP)) u U time
  unfold normalizedMellinPlainRow mellinPlainRow Node.plainPair Node.mellinPlain
    Node.normalizedMellinPlain
  rw [hleft, hright, hleft, hright, hslots]
  change ((e₁ * e₂ * P ^ n.data.geometry.slotCount : ℝ) : ℂ)⁻¹ * _ = _
  by_cases hc : n.centered = true <;>
    simp only [hc, ite_true, ite_false, sub_zero, Complex.ofReal_mul,
      Complex.ofReal_pow, Complex.ofReal_inv] <;>
    field_simp [hPn, he₁n, he₂n] <;> ring

theorem continuous_normalizedMellinPlainRow (n : Node K omegaCharacter psiCharacter)
    (B₁ B₂ : SmoothAnnularTest) (P : ℝ) (hP : 1 ≤ P)
    (E : ℝ) (hE : 1 ≤ E) (J : ℕ) (U time : ℝ) (u : NonzeroIdeal K) :
    Continuous (normalizedMellinPlainRow n B₁ B₂ P E J U time u) := by
  have hwindow : Continuous (ordinaryProfileEnvelope E J) :=
    continuous_const.mul ((continuous_const.add continuous_abs).pow J)
  have hamp : Continuous (mellinNormalizationAmplitude n.data.geometry.slotCount P E J) :=
    ((hwindow.comp continuous_fst).mul (hwindow.comp continuous_snd)).mul continuous_const
  have hn (frequency : ℝ × ℝ) :
      (mellinNormalizationAmplitude n.data.geometry.slotCount P E J frequency : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (zero_lt_one.trans_le
      (one_le_mellinNormalizationAmplitude _ hP hE J frequency)).ne'
  exact ((Complex.continuous_ofReal.comp hamp).inv₀ hn).mul
    (continuous_mellinPlainRow n B₁ B₂ U time u)

theorem normalizedMellinPlainRow_memLp (n : Node K omegaCharacter psiCharacter)
    (B₁ B₂ : SmoothAnnularTest) (P : ℝ) (hP : 1 ≤ P)
    (E : ℝ) (hE : 1 ≤ E) (J : ℕ) (U time : ℝ) (u : NonzeroIdeal K)
    (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ] :
    MemLp (normalizedMellinPlainRow n B₁ B₂ P E J U time u) 2 μ := by
  obtain ⟨C, hC⟩ := mellinPlainRow_bounded n B₁ B₂ U time u
  apply MemLp.of_bound
    (continuous_normalizedMellinPlainRow n B₁ B₂ P hP E hE J U time u).aestronglyMeasurable C
  exact Filter.Eventually.of_forall fun frequency => by
    rw [normalizedMellinPlainRow, norm_mul, norm_inv,
      Complex.norm_of_nonneg (zero_le_one.trans
        (one_le_mellinNormalizationAmplitude _ hP hE J frequency))]
    exact ((mul_le_mul_of_nonneg_right (inv_le_one_of_one_le₀
      (one_le_mellinNormalizationAmplitude _ hP hE J frequency)) (norm_nonneg _)).trans
        (by simpa only [one_mul] using hC frequency))

/-- Normalization cancels in the complex integrand itself. -/
theorem normalizedMellinPlainRow_integrand (n : Node K omegaCharacter psiCharacter)
    (B₁ B₂ V₁ V₂ : SmoothAnnularTest) (P : ℝ) (hP : 1 ≤ P)
    (E : ℝ) (hE : 1 ≤ E) (J : ℕ) (U time : ℝ) (u : NonzeroIdeal K)
    (frequency : ℝ × ℝ) :
    ((mellinNormalizationAmplitude n.data.geometry.slotCount P E J frequency : ℂ) *
      mellinPairCoefficient V₁ V₂ frequency) *
        normalizedMellinPlainRow n B₁ B₂ P E J U time u frequency =
      mellinPairCoefficient V₁ V₂ frequency * mellinPlainRow n B₁ B₂ U time u frequency := by
  have hn : (mellinNormalizationAmplitude n.data.geometry.slotCount P E J frequency : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (zero_lt_one.trans_le
      (one_le_mellinNormalizationAmplitude _ hP hE J frequency)).ne'
  unfold normalizedMellinPlainRow
  field_simp [hn]

private theorem sliceControl_divide {f : ℝ → ℂ} {J : ℕ} {A P a b : ℝ}
    (hP : 0 < P) (h : SliceControl J A P 0 a b 0 f) :
    SliceControl J A 1 0 a b 0 (fun y => ((P⁻¹ : ℝ) : ℂ) * f y) := by
  have hs := sliceControl_const_mul h ((P⁻¹ : ℝ) : ℂ)
  simpa only [Complex.norm_of_nonneg (inv_nonneg.mpr hP.le),
    inv_mul_cancel₀ hP.ne'] using hs

/-- The same envelope works before all moving original profiles and
parent bounds. Only explicit support inclusion in the new annulus is
used, never an unstated recursive support-preservation assertion. -/
theorem exists_normalizedMellinPlain_control (B₁ B₂ : SmoothAnnularTest) (J : ℕ) (A : ℝ) :
    ∃ E : ℝ, ∃ hE : 1 ≤ E,
      ∀ (d : MomentData K omegaCharacter psiCharacter) (P : ℝ) (hP : 1 ≤ P)
        (a b : ℝ), ModelProfileControl d J A P 0 a b 0 →
      Function.support B₁.toFun ⊆ Icc a b → Function.support B₂.toFun ⊆ Icc a b →
      ∀ frequency : ℝ × ℝ,
        ModelProfileControl (normalizedMellinPlainData d B₁ B₂ P hP E hE J frequency)
          J A 1 0 a b 0 := by
  obtain ⟨C₁, hC₁, hb₁⟩ := annularMellinWindow_testSeminorm_bound B₁ J A
  obtain ⟨C₂, hC₂, hb₂⟩ := annularMellinWindow_testSeminorm_bound B₂ J A
  let E := max 1 (max C₁ C₂)
  have hE : 1 ≤ E := le_max_left _ _
  have hC₁E : C₁ ≤ E := (le_max_left _ _).trans (le_max_right _ _)
  have hC₂E : C₂ ≤ E := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨E, hE, ?_⟩
  intro d P hP a b hparent hs₁ hs₂ frequency q
  have hwindow (B : SmoothAnnularTest) (C t : ℝ)
      (hCE : C ≤ E) (hs : Function.support B.toFun ⊆ Icc a b)
      (hb : testSeminorm (annularMellinWindow B t) J A ≤ C * (1 + |t|) ^ J) :
      SliceControl J A 1 0 a b 0
        (fun y => (((ordinaryProfileEnvelope E J t)⁻¹ : ℝ) : ℂ) * annularMellinWindow B t y) := by
    apply sliceControl_divide
      (zero_lt_one.trans_le (one_le_ordinaryProfileEnvelope hE J t))
    refine ⟨annularMellinWindow_smooth B t, ?_, ?_⟩
    · intro y hy
      apply hs
      rw [← annularMellinWindow_support B t]
      exact hy
    · simpa only [Real.rpow_zero, mul_one, ordinaryProfileEnvelope] using
        hb.trans (mul_le_mul_of_nonneg_right hCE (by positivity))
  cases q with
  | inverse u =>
      exact sliceControl_divide (zero_lt_one.trans_le hP) (modelProfileControl_inverse hparent u)
  | plain₁ u =>
      simpa only [modelProfile, normalizedMellinPlainData, scaledIdealTest,
        mellinPlainData, IdealTest.freezeTwist, annularMellinIdealTest,
        profilePower_zero, mul_one] using hwindow B₁ C₁ frequency.1 hC₁E hs₁ (hb₁ frequency.1)
  | plain₂ u =>
      simpa only [modelProfile, normalizedMellinPlainData, scaledIdealTest,
        mellinPlainData, IdealTest.freezeTwist, annularMellinIdealTest,
        profilePower_zero, mul_one] using hwindow B₂ C₂ frequency.2 hC₂E hs₂ (hb₂ frequency.2)
  | prime i =>
      exact sliceControl_divide (zero_lt_one.trans_le hP) (modelProfileControl_prime hparent i)

end HeckeSkeleton.Moments.EngineInduction
