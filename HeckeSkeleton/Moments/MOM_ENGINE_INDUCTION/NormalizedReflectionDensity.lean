import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.OrdinaryProfileNormalization
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.OrdinaryReflectionDensity

/-!
# The actual density after child-profile normalization

All profiles of a reflected child are divided by the same positive
frequency envelope.  The exact amplitude removed from that child is
inserted into the original complex reflection density.  A sufficiently
high, finitely chosen Euler order of the original profile pays this
polynomial frequency cost.  The resulting envelope is shared by every
arithmetic row and has a genuine finite L1 mass.

The higher source Euler order is selected before the original profile,
row, conductor, deleted set, physical scales and frequency.  It is not
identified with the requested child order.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField MeasureTheory Set Filter
open HeckeGeneral.Analysis HeckeGeneral.Characters
open HeckeGeneral.ThetaSkeleton.Global HeckeSkeleton.ThetaKernel
open HeckeSkeleton.Moments.UniformAmplify HeckePort.Moments
open scoped Classical BigOperators

/-- A single fixed weight exponent controls every smaller nonnegative
one.  The comparison uses the actual, integrable Euler integrals of the
smooth annular test. -/
theorem smoothAnnular_testSeminorm_weight_le (V : SmoothAnnularTest) (J : ℕ)
    {δ A : ℝ} (hδ : 0 ≤ δ) (hδA : δ ≤ A) :
    testSeminorm V.toFun J δ ≤ 2 * testSeminorm V.toFun J A := by
  apply testSeminorm_le_of_integrals V.toFun J δ _
    (mul_nonneg (by norm_num) (testSeminorm_nonneg V.toFun J A))
  intro j hj
  rw [← Iint_add_eq V j δ]
  have hleft := Iint_left_le V j J hj A
  have hright : Iint V j δ ≤ testSeminorm V.toFun J A := by
    apply (Iint_strip_le V j (σ := δ) (σ1 := -1 / 4) (σ2 := A) (by linarith) hδA).trans
    rw [Iint_add_eq]
    exact testIntegral_le_testSeminorm V.toFun A hj
  linarith

variable (K : Type) [Field K] [NumberField K]

/-- The exact scalar factor removed from all actual child profiles is
charged to the original complex density, before weighted Cauchy. -/
def normalizedOrdinaryReflectionDensity (E0 : ℝ) (J slots : ℕ)
    (χ : HeckeCharacter K) (V : SmoothAnnularTest)
    (a ai : Ideal (𝓞 K) → ℂ) (S : Finset (Ideal (𝓞 K)))
    (Q X N σ t : ℝ) : ℂ :=
  ((ordinaryProfileEnvelope E0 J t ^ (slots + 2) : ℝ) : ℂ) *
    ordinaryReflectionDensity K χ V a ai S Q X N σ t

/-- Actual absolute integrability follows from rapid Mellin decay and
the proved absolute restoration Fubini theorem. -/
theorem integrable_normalizedOrdinaryReflectionDensity
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (χ : HeckeCharacter K) (V : SmoothAnnularTest)
    {E0 δ Q X N σ : ℝ} (hE0 : 1 ≤ E0) (hδ : 0 < δ)
    (J slots : ℕ) {a ai : Ideal (𝓞 K) → ℂ}
    (ha : IdealCoeff a) (hai : IdealCoeff ai)
    (S : Finset (Ideal (𝓞 K))) (hS : ∀ P ∈ S, Prime P)
    (hQ : 0 < Q) (hX : 0 < X) (hN : 0 < N)
    (hlo : 1 / 4 ≤ σ) (hhi : σ ≤ 3 / 4) :
    Integrable (normalizedOrdinaryReflectionDensity K E0 J slots χ V a ai S Q X N σ) := by
  obtain ⟨L, C, hC, hbound⟩ := ordinaryMellinGamma_weighted_uniform K hcomplex χ
    hδ (V.lower_pos.trans_le V.upper_ge) (J * (slots + 2))
  have hline : σ ∈ Icc (-δ) (3 / 4) := ⟨by linarith, hhi⟩
  have hint := (hbound V le_rfl σ hline).2.1
  have hc : Continuous (fun t : ℝ =>
      ((ordinaryProfileEnvelope E0 J t ^ (slots + 2) : ℝ) : ℂ) *
        ordinaryMellinGamma K χ V σ t) := by
    have he : Continuous (ordinaryProfileEnvelope E0 J) :=
      continuous_const.mul ((continuous_const.add continuous_abs).pow J)
    exact (Complex.continuous_ofReal.comp (he.pow (slots + 2))).mul
      (continuous_ordinaryMellinGamma K χ V (by linarith))
  have hf : Integrable (fun t : ℝ =>
      ((ordinaryProfileEnvelope E0 J t ^ (slots + 2) : ℝ) : ℂ) *
        ordinaryMellinGamma K χ V σ t) := by
    apply (hint.const_mul (E0 ^ (slots + 2))).mono' hc.aestronglyMeasurable
    filter_upwards [] with t
    rw [norm_mul, Complex.norm_of_nonneg
      (pow_nonneg (zero_le_one.trans (one_le_ordinaryProfileEnvelope hE0 J t)) _)]
    change ordinaryProfileEnvelope E0 J t ^ (slots + 2) *
      ‖ordinaryMellinGamma K χ V σ t‖ ≤
      E0 ^ (slots + 2) * ((1 + |t|) ^ (J * (slots + 2)) *
        ‖ordinaryMellinGamma K χ V σ t‖)
    rw [ordinaryProfileEnvelope, mul_pow, ← pow_mul]
    exact le_of_eq (mul_assoc _ _ _)
  have hF := (ordinaryRestorationPhase_fubini ha hai (β := 1 / 4) (by norm_num)
    S hS hQ hX hN hlo (by linarith) (hf.const_mul ((2 * (Real.pi : ℂ))⁻¹))).1
  exact hF.congr (Eventually.of_forall (fun t => by
    dsimp only [normalizedOrdinaryReflectionDensity, ordinaryReflectionDensity]
    ring))

/-- A requested child order and slot cap determine a higher source order
and one row-independent envelope.  The same fixed weight A can be used
at every stage of the finite backward Euler-order schedule. -/
theorem normalizedOrdinaryReflectionDensity_uniform
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (background : HeckeCharacter K) {δ A B ε E0 : ℝ}
    (hδ : 0 < δ) (hδA : δ ≤ A) (hB : 0 < B) (hε : 0 < ε)
    (hE0 : 1 ≤ E0) (J cap : ℕ) :
    ∃ L : ℕ, J ≤ L ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ (row : HeckeCharacter K), FiniteOrder row →
      ∀ (V : SmoothAnnularTest), V.upper ≤ B →
      ∀ (a ai : Ideal (𝓞 K) → ℂ), IdealCoeff a → IdealCoeff ai →
      ∀ (S : Finset (Ideal (𝓞 K))) (hS : ∀ P ∈ S, Prime P)
      (slots : ℕ), slots ≤ cap → ∀ (Q X N σ : ℝ),
      0 < Q → 0 < X → 0 < N → 1 / 4 ≤ σ → σ ≤ 3 / 4 →
      ∀ t : ℝ,
      ‖normalizedOrdinaryReflectionDensity K E0 J slots
        (background * row) V a ai S Q X N σ t‖ ≤
        C * testSeminorm V.toFun L A * (N * X / Q) ^ (σ - 1 / 2) *
          (Ideal.absNorm (∏ P ∈ S, P) : ℝ) ^ ε * (1 + |t|) ^ (-(2 : ℝ)) := by
  obtain ⟨L0, C0, hC0, hbound⟩ := ordinaryReflectionDensity_finiteRows_uniform
    K hcomplex background hδ hB hε (J * (cap + 2))
  let L := max J L0
  let C := E0 ^ (cap + 2) * C0 * 2
  have hE : 0 ≤ E0 := zero_le_one.trans hE0
  refine ⟨L, le_max_left _ _, C, by dsimp [C]; positivity, ?_⟩
  intro row hrow V hupper a ai ha hai S hS slots hslots Q X N σ hQ hX hN hlo hhi t
  have hs : testSeminorm V.toFun L0 δ ≤ 2 * testSeminorm V.toFun L A :=
    (smoothAnnular_testSeminorm_weight_le V L0 hδ.le hδA).trans
      (mul_le_mul_of_nonneg_left (testSeminorm_mono_order V.toFun A
        (le_max_right J L0)) (by norm_num))
  have hd := hbound row hrow V hupper a ai ha hai S hS Q X N σ hQ hX hN hlo hhi t
  have hratio : 0 ≤ (N * X / Q) ^ (σ - 1 / 2) := Real.rpow_nonneg (by positivity) _
  have hdeleted : 0 ≤ (Ideal.absNorm (∏ P ∈ S, P) : ℝ) ^ ε :=
    Real.rpow_nonneg (by positivity) _
  have hdecay : 0 ≤ (1 + |t|) ^ (-(2 : ℝ)) := Real.rpow_nonneg (by positivity) _
  rw [normalizedOrdinaryReflectionDensity, norm_mul, Complex.norm_of_nonneg
    (pow_nonneg (zero_le_one.trans (one_le_ordinaryProfileEnvelope hE0 J t)) _)]
  calc
    _ ≤ (E0 ^ (cap + 2) * (1 + |t|) ^ (J * (cap + 2))) *
        ‖ordinaryReflectionDensity K (background * row) V a ai S Q X N σ t‖ :=
      mul_le_mul_of_nonneg_right
        (ordinaryProfileEnvelope_amplitude_bound hE0 J slots cap hslots t) (norm_nonneg _)
    _ = E0 ^ (cap + 2) * ((1 + |t|) ^ (J * (cap + 2)) *
        ‖ordinaryReflectionDensity K (background * row) V a ai S Q X N σ t‖) := by ring
    _ ≤ E0 ^ (cap + 2) * (C0 * testSeminorm V.toFun L0 δ *
        (N * X / Q) ^ (σ - 1 / 2) * (Ideal.absNorm (∏ P ∈ S, P) : ℝ) ^ ε *
          (1 + |t|) ^ (-(2 : ℝ))) :=
      mul_le_mul_of_nonneg_left hd (pow_nonneg hE _)
    _ ≤ E0 ^ (cap + 2) * (C0 * (2 * testSeminorm V.toFun L A) *
        (N * X / Q) ^ (σ - 1 / 2) * (Ideal.absNorm (∏ P ∈ S, P) : ℝ) ^ ε *
          (1 + |t|) ^ (-(2 : ℝ))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hs hC0) hratio) hdeleted) hdecay)
        (pow_nonneg hE _)
    _ = _ := by dsimp [C]; ring

/-- The shared positive envelope. Its parameters are family-level bounds,
not suprema of a row-dependent measure. -/
def ordinaryReflectionEnvelope (C profileBound deletionBound t : ℝ) : ℝ :=
  C * profileBound * deletionBound * (1 + |t|) ^ (-(2 : ℝ))

/-- Measurability, positivity and the exact finite mass of the envelope
are proved once, before any moving row or original finite support. -/
theorem ordinaryReflectionEnvelope_data {C profileBound deletionBound : ℝ}
    (hC : 0 ≤ C) (hprofile : 0 ≤ profileBound) (hdeletion : 0 ≤ deletionBound) :
    Measurable (ordinaryReflectionEnvelope C profileBound deletionBound) ∧
      (∀ t, 0 ≤ ordinaryReflectionEnvelope C profileBound deletionBound t) ∧
      Integrable (ordinaryReflectionEnvelope C profileBound deletionBound) ∧
      (∫ t : ℝ, ordinaryReflectionEnvelope C profileBound deletionBound t) =
        C * profileBound * deletionBound * ∫ t : ℝ, (1 + |t|) ^ (-(2 : ℝ)) := by
  have hi : Integrable (ordinaryReflectionEnvelope C profileBound deletionBound) :=
    (integrable_one_add_abs_rpow_neg (e := 2) (by norm_num)).const_mul _
  have hc : Continuous (ordinaryReflectionEnvelope C profileBound deletionBound) := by
    apply continuous_const.mul
    exact (continuous_const.add continuous_abs).rpow_const
      (fun t => Or.inl (ne_of_gt (by positivity : 0 < (1 : ℝ) + |t|)))
  exact ⟨hc.measurable, (fun t => by dsimp [ordinaryReflectionEnvelope]; positivity),
    hi, integral_const_mul _ _⟩

/-- Choosing one of the two fixed lines removes the norm-ratio cost.
The envelope and its L1 bound are then uniform in every actual row,
conductor and dyadic scale, after the stated primitive profile and
deleted-ideal bounds. -/
theorem normalizedOrdinaryReflectionDensity_L1_uniform
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (background : HeckeCharacter K) {δ A B ε E0 : ℝ}
    (hδ : 0 < δ) (hδA : δ ≤ A) (hB : 0 < B) (hε : 0 < ε)
    (hE0 : 1 ≤ E0) (J cap : ℕ) :
    ∃ L : ℕ, J ≤ L ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ (profileBound deletionBound : ℝ), 0 ≤ profileBound → 0 ≤ deletionBound →
      ∀ (row : HeckeCharacter K), FiniteOrder row →
      ∀ (V : SmoothAnnularTest), V.upper ≤ B → testSeminorm V.toFun L A ≤ profileBound →
      ∀ (a ai : Ideal (𝓞 K) → ℂ), IdealCoeff a → IdealCoeff ai →
      ∀ (S : Finset (Ideal (𝓞 K))) (hS : ∀ P ∈ S, Prime P),
      (Ideal.absNorm (∏ P ∈ S, P) : ℝ) ^ ε ≤ deletionBound →
      ∀ (slots : ℕ), slots ≤ cap → ∀ (Q X N : ℝ), 0 < Q → 0 < X → 0 < N →
      let density := normalizedOrdinaryReflectionDensity K E0 J slots
        (background * row) V a ai S Q X N (ordinaryReflectionLine (N * X / Q))
      (∀ t, ‖density t‖ ≤ ordinaryReflectionEnvelope C profileBound deletionBound t) ∧
      Integrable density ∧
      (∫ t : ℝ, ‖density t‖) ≤
        C * profileBound * deletionBound * ∫ t : ℝ, (1 + |t|) ^ (-(2 : ℝ)) := by
  obtain ⟨L, hJL, C, hC, hbound⟩ := normalizedOrdinaryReflectionDensity_uniform
    K hcomplex background hδ hδA hB hε hE0 J cap
  refine ⟨L, hJL, C, hC, ?_⟩
  intro profileBound deletionBound hprofile hdeletion row hrow V hupper hV
    a ai ha hai S hS hdeleted slots hslots Q X N hQ hX hN
  dsimp only
  have hline := ordinaryReflectionLine_bound (div_pos (mul_pos hN hX) hQ)
  have hi := integrable_normalizedOrdinaryReflectionDensity K hcomplex (background * row) V
    hE0 hδ J slots ha hai S hS hQ hX hN hline.2.1 hline.2.2.1
  have hpoint (t : ℝ) :
      ‖normalizedOrdinaryReflectionDensity K E0 J slots (background * row) V a ai S Q X N
        (ordinaryReflectionLine (N * X / Q)) t‖ ≤
        ordinaryReflectionEnvelope C profileBound deletionBound t := by
    apply (hbound row hrow V hupper a ai ha hai S hS slots hslots Q X N _
      hQ hX hN hline.2.1 hline.2.2.1 t).trans
    have hS0 := testSeminorm_nonneg V.toFun L A
    have hP0 : 0 ≤ (Ideal.absNorm (∏ P ∈ S, P) : ℝ) ^ ε :=
      Real.rpow_nonneg (by positivity) _
    have hs : C * testSeminorm V.toFun L A *
        (N * X / Q) ^ (ordinaryReflectionLine (N * X / Q) - 1 / 2) ≤ C * profileBound := by
      calc
        _ ≤ C * testSeminorm V.toFun L A * 1 :=
          mul_le_mul_of_nonneg_left hline.2.2.2 (mul_nonneg hC hS0)
        _ ≤ C * profileBound := by
          rw [mul_one]
          exact mul_le_mul_of_nonneg_left hV hC
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul hs hdeleted hP0 (mul_nonneg hC hprofile))
      (Real.rpow_nonneg (by positivity) _)
  refine ⟨hpoint, hi, ?_⟩
  have he := ordinaryReflectionEnvelope_data hC hprofile hdeletion
  rw [← he.2.2.2]
  exact integral_mono hi.norm he.2.2.1 hpoint

end HeckeSkeleton.Moments.EngineInduction
