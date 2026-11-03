import ActualAdditiveGramFreeOrbitalAssembly
import ActualGramRowBallOrbitalMajorant
import ActualGramDiagonalBound
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
UNCOMPILED / native0. Actual free-test zero correction: the full finite
ideal-pair sum is the genuine unit-count diagonal minus the original zero
row square. The constructed row-ball test has original tensor zero equal
one. Its dual zero is a real nonnegative ACTUAL Haar integral, not one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeGeneral.ThetaSkeleton.Physical.ActualGramFreeZeroDraft

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Bridge HeckeGeneral.ThetaSkeleton.Global
open ActualAdditiveGramDraft ActualAdditiveGramFreeDraft ActualGramMajorantDraft
open scoped Classical BigOperators ComplexConjugate

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "SF" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer SF K
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "Γ" => sixthPowerUnits K SF

local instance freeZero_sixthUnits_finiteIndex : Subgroup.FiniteIndex Γ :=
  sUnit_power_range_finiteIndex K SF 6 (by decide)

variable [∀ v : HeightOneSpectrum (𝓞 K), MeasurableSpace (v.adicCompletion K)]
  [∀ v : HeightOneSpectrum (𝓞 K), BorelSpace (v.adicCompletion K)]
variable (μv : ∀ v : HeightOneSpectrum (𝓞 K), Measure (v.adicCompletion K))
  [∀ v, (μv v).IsAddHaarMeasure]

/-- No positivity or convergence assertion is needed for the exact finite
pair identity. The free test occurs only through its two actual zero values. -/
theorem sum_freeAdditiveGramPairZeroCorrection_eq_diagonal_sub_zeroRow
    (P : ProbeData K SF) (c : ExteriorIdeal K SF → ℂ) (W : SmoothAnnularTest)
    (Y ν : ℝ) (hY : 0 < Y) (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (r : {r : ℝ // 0 < r}) :
    ((Y ^ (-3 : ℝ) : ℝ) : ℂ) *
        (∑ I ∈ additiveGramIdealSupport K SF W Y,
          ∑ J ∈ additiveGramIdealSupport K SF W Y,
            actualAdditiveGramPairCoefficient K SF c W Y ν I J *
              freeAdditiveGramPairZeroCorrection K S μv P I J φ h r) =
      ((r.val : ℂ)⁻¹ * ((Y ^ (-3 : ℝ) : ℝ) : ℂ) * additiveGramPoissonFieldFactor K) *
        sIntegerDualTensorTerm K μv S (traceSchwartzToMixed K φ)
          h 0 *
        (∑ I ∈ additiveGramIdealSupport K SF W Y,
          actualAdditiveGramPairCoefficient K SF c W Y ν I I *
            (additiveGramDiagonalUnitCount K S P I : ℂ)) -
      ((‖actualAdditiveGramAmplitude K SF P c W Y ν (0 : OS)‖ ^ 2 : ℝ) : ℂ) *
        sIntegerTensorTerm K S (traceSchwartzToMixed K φ)
          h 0 := by
  let F := additiveGramIdealSupport K SF W Y
  let a := actualAdditiveGramPairCoefficient K SF c W Y ν
  let z : ℂ := ((Y ^ (-3 : ℝ) : ℝ) : ℂ)
  let b : ℂ := (r.val : ℂ)⁻¹ * additiveGramPoissonFieldFactor K
  let d : ℂ := sIntegerDualTensorTerm K μv S
    (traceSchwartzToMixed K φ) h 0
  let t : ℂ := sIntegerTensorTerm K S
    (traceSchwartzToMixed K φ) h 0
  let g := fun I J : ExteriorIdeal K SF =>
    probeGauss K SF P I 0 * conj (probeGauss K SF P J 0)
  have hrow :
      z * (∑ I ∈ F, ∑ J ∈ F, a I J * g I J) =
        ((‖actualAdditiveGramAmplitude K SF P c W Y ν (0 : OS)‖ ^ 2 : ℝ) : ℂ) := by
    simpa only [z, F, a, g, actualAdditiveGramPairTerm,
      actualAdditiveGramPairCoefficient, neg_zero] using
      (actualAdditiveGramAmplitude_norm_sq_eq_double_sum K SF P c W Y ν hY (0 : OS)).symm
  have hrowt :
      z * ((∑ I ∈ F, ∑ J ∈ F, a I J * g I J) * t) =
        ((‖actualAdditiveGramAmplitude K SF P c W Y ν (0 : OS)‖ ^ 2 : ℝ) : ℂ) * t := by
    rw [← mul_assoc, hrow]
  have hsplit :
      (∑ I ∈ F, ∑ J ∈ F, a I J * freeAdditiveGramPairZeroCorrection K S μv P I J φ h r) =
        b * d * (∑ I ∈ F, ∑ J ∈ F, a I J * additiveGramFullCorrelation K S P I J 0) -
          (∑ I ∈ F, ∑ J ∈ F, a I J * g I J) * t := by
    simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro I hI
    apply Finset.sum_congr rfl
    intro J hJ
    change a I J * (b * (additiveGramFullCorrelation K S P I J 0 * d) - g I J * t) = _
    ring
  change z * (∑ I ∈ F, ∑ J ∈ F, a I J * freeAdditiveGramPairZeroCorrection K S μv P I J φ h r) = _
  rw [hsplit, sum_additiveGramFullCorrelation_zero K S P F a, mul_sub, hrowt]
  dsimp only [z, b, d, t, F, a]
  ring


/-- The actual central normalization of the full finite-pair zero correction. -/
def freeGramNormalizedZeroCorrection (P : ProbeData K SF)
    (c : ExteriorIdeal K SF → ℂ) (W : SmoothAnnularTest) (Y η : ℝ)
    (φ : SchwartzMap V ℂ)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletion K → ℂ)
    (r : {r : ℝ // 0 < r}) : ℂ :=
  ((Y ^ (-3 : ℝ) : ℝ) : ℂ) *
    ∑ I ∈ additiveGramIdealSupport K SF W Y,
      ∑ J ∈ additiveGramIdealSupport K SF W Y,
        actualAdditiveGramPairCoefficient K SF c W Y η I J *
          freeAdditiveGramPairZeroCorrection K S μv P I J φ h r

private theorem complex_eq_real_of_im_zero (z : ℂ) (hz : z.im = 0) :
    z = (z.re : ℂ) := by
  apply Complex.ext
  · rfl
  · simpa only [Complex.ofReal_im] using hz

private theorem integral_real_nonnegative {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℂ) (hf : ∀ x, (f x).im = 0 ∧ 0 ≤ (f x).re) :
    (∫ x, f x ∂μ).im = 0 ∧ 0 ≤ (∫ x, f x ∂μ).re := by
  have heq : f = fun x => ((f x).re : ℂ) :=
    funext fun x => complex_eq_real_of_im_zero _ (hf x).1
  rw [heq, integral_complex_ofReal]
  exact ⟨Complex.ofReal_im _, integral_nonneg fun x => (hf x).2⟩

private theorem complex_mul_real_nonnegative (z w : ℂ)
    (hz : z.im = 0 ∧ 0 ≤ z.re) (hw : w.im = 0 ∧ 0 ≤ w.re) :
    (z * w).im = 0 ∧ 0 ≤ (z * w).re := by
  constructor
  · rw [Complex.mul_im, hz.1, hw.1]
    ring
  · simpa only [Complex.mul_re, hz.1, hw.1, mul_zero, sub_zero] using
      mul_nonneg hz.2 hw.2

private theorem finset_product_real_nonnegative {ι : Type*} (F : Finset ι)
    (f : ι → ℂ) (hf : ∀ i ∈ F, (f i).im = 0 ∧ 0 ≤ (f i).re) :
    (∏ i ∈ F, f i).im = 0 ∧ 0 ≤ (∏ i ∈ F, f i).re := by
  have heq : (∏ i ∈ F, f i) = ((∏ i ∈ F, (f i).re : ℝ) : ℂ) := by
    push_cast
    exact Finset.prod_congr rfl fun i hi => complex_eq_real_of_im_zero _ (hf i hi).1
  rw [heq]
  exact ⟨Complex.ofReal_im _, Finset.prod_nonneg fun i hi => (hf i hi).2⟩

variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]

def rowBallDualTensorZero (B : ℝ) : ℂ :=
  sIntegerDualTensorTerm K μv S (traceSchwartzToMixed K (rowBallArchTest K S B))
    (rowBallFiniteFamily K S B) 0

theorem rowBall_original_tensor_zero (B : ℝ) :
    sIntegerTensorTerm K S (traceSchwartzToMixed K (rowBallArchTest K S B))
      (rowBallFiniteFamily K S B) 0 = 1 :=
  compactShapeMajorant_tensor_zero K S (rowBallCompactShape K S B)
    (isCompact_rowBallCompactShape K S B)

/-- Zero Fourier frequency is the actual mixed Lebesgue integral times
the normalized finite additive-Haar integrals. Their constants remain. -/
theorem rowBallDualTensorZero_eq_integrals (B : ℝ) :
    rowBallDualTensorZero K S μv B =
      (∫ x : mixedEmbedding.mixedSpace K,
        traceSchwartzToMixed K (rowBallArchTest K S B) x) *
      ∏ v ∈ S, (((μv v).real (v.adicCompletionIntegers K : Set (v.adicCompletion K)) : ℂ))⁻¹ *
        ∫ x, rowBallFiniteFamily K S B v x ∂μv v := by
  have harch : InfiniteAdeleRing.ringEquiv_mixedSpace K
      ((algebraMap K (AdeleRing (𝓞 K) K) (0 : K)).1) = 0 := by
    rw [map_zero]
    exact map_zero _
  have hfinite (v : HeightOneSpectrum (𝓞 K)) :
      ((algebraMap K (AdeleRing (𝓞 K) K) (0 : K)).2) v = 0 := by
    rw [map_zero] <;> rfl
  simp only [rowBallDualTensorZero, sIntegerDualTensorTerm, harch,
    sIntegerLocalFourierProduct, hfinite, NumberField.AdelicFourier.fourierIntegral,
    mul_zero, neg_zero, AddChar.map_zero_eq_one, one_mul]

/-- The free dual zero is real nonnegative, with its actual Haar
normalizations. It is neither assumed nor asserted to equal one. -/
theorem rowBallDualTensorZero_real_nonnegative (B : ℝ) :
    (rowBallDualTensorZero K S μv B).im = 0 ∧
      0 ≤ (rowBallDualTensorZero K S μv B).re := by
  rcases compactShapeMajorant_spec K S (rowBallCompactShape K S B)
    (isCompact_rowBallCompactShape K S B) with ⟨_, _, hrange, harch, _, _, _, _⟩
  have hi : (∫ x : mixedEmbedding.mixedSpace K,
      traceSchwartzToMixed K (rowBallArchTest K S B) x).im = 0 ∧
      0 ≤ (∫ x : mixedEmbedding.mixedSpace K,
        traceSchwartzToMixed K (rowBallArchTest K S B) x).re :=
    integral_real_nonnegative volume _ (fun x => harch ((traceToMixed K).symm x))
  have hf (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ S) :
      (∫ x, rowBallFiniteFamily K S B v x ∂μv v).im = 0 ∧
        0 ≤ (∫ x, rowBallFiniteFamily K S B v x ∂μv v).re := by
    apply integral_real_nonnegative
    intro x
    have hx : rowBallFiniteFamily K S B v x = 0 ∨ rowBallFiniteFamily K S B v x = 1 := by
      simpa only [rowBallFiniteFamily, compactShapeFiniteFamily,
        gramFiniteExtension, dif_pos hv] using hrange ⟨v, hv⟩ x
    rcases hx with hx | hx <;> simp only [hx] <;> norm_num
  rw [rowBallDualTensorZero_eq_integrals]
  apply complex_mul_real_nonnegative _ _ hi
  apply finset_product_real_nonnegative
  intro v hv
  apply complex_mul_real_nonnegative _ _ ?_ (hf v hv)
  constructor
  · simp only [← Complex.ofReal_inv, Complex.ofReal_im]
  · simpa only [← Complex.ofReal_inv, Complex.ofReal_re] using
      (inv_nonneg.mpr (measureReal_nonneg (μ := μv v)
        (s := (v.adicCompletionIntegers K : Set (v.adicCompletion K)))))

/-- Exact free row-ball zero correction, including the negative zero row. -/
theorem rowBall_freeZero_eq_diagonal_sub_zeroRow
    (B : ℝ) (P : ProbeData K SF) (c : ExteriorIdeal K SF → ℂ)
    (W : SmoothAnnularTest) (Y η : ℝ) (hY : 0 < Y) (r : {r : ℝ // 0 < r}) :
    freeGramNormalizedZeroCorrection K S μv P c W Y η
      (rowBallArchTest K S B) (rowBallFiniteFamily K S B) r =
    ((r.val : ℂ)⁻¹ * additiveGramPoissonFieldFactor K * rowBallDualTensorZero K S μv B) *
      (((Y ^ (-3 : ℝ) : ℝ) : ℂ) *
        ∑ I ∈ additiveGramIdealSupport K SF W Y,
          actualAdditiveGramPairCoefficient K SF c W Y η I I *
            (additiveGramDiagonalUnitCount K S P I : ℂ)) -
      ((‖actualAdditiveGramAmplitude K SF P c W Y η (0 : OS)‖ ^ 2 : ℝ) : ℂ) := by
  have h := sum_freeAdditiveGramPairZeroCorrection_eq_diagonal_sub_zeroRow
    K S μv P c W Y η hY (rowBallArchTest K S B) (rowBallFiniteFamily K S B) r
  rw [rowBall_original_tensor_zero, mul_one] at h
  unfold freeGramNormalizedZeroCorrection
  rw [h]
  dsimp only [rowBallDualTensorZero]
  ring

/-- The negative original zero row can now be discarded on real parts,
because its tensor value has actually been proved to be one. -/
theorem rowBall_freeZero_re_le_diagonal_norm
    (B : ℝ) (P : ProbeData K SF) (c : ExteriorIdeal K SF → ℂ)
    (W : SmoothAnnularTest) (Y η : ℝ) (hY : 0 < Y) (r : {r : ℝ // 0 < r}) :
    (freeGramNormalizedZeroCorrection K S μv P c W Y η
      (rowBallArchTest K S B) (rowBallFiniteFamily K S B) r).re ≤
    r.val⁻¹ * ‖additiveGramPoissonFieldFactor K‖ * ‖rowBallDualTensorZero K S μv B‖ *
      ‖((Y ^ (-3 : ℝ) : ℝ) : ℂ) *
        (∑ I ∈ additiveGramIdealSupport K SF W Y,
          actualAdditiveGramPairCoefficient K SF c W Y η I I *
            (additiveGramDiagonalUnitCount K S P I : ℂ))‖ := by
  rw [rowBall_freeZero_eq_diagonal_sub_zeroRow K S μv B P c W Y η hY r,
    Complex.sub_re, Complex.ofReal_re]
  calc
    _ ≤ (((r.val : ℂ)⁻¹ * additiveGramPoissonFieldFactor K * rowBallDualTensorZero K S μv B) *
        (((Y ^ (-3 : ℝ) : ℝ) : ℂ) *
          ∑ I ∈ additiveGramIdealSupport K SF W Y,
            actualAdditiveGramPairCoefficient K SF c W Y η I I *
              (additiveGramDiagonalUnitCount K S P I : ℂ))).re :=
      sub_le_self _ (sq_nonneg _)
    _ ≤ _ := (Complex.re_le_norm _).trans_eq (by
      simp only [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg r.property.le])

/-- O(1/(rY)) for the actual free zero correction. Its constant is chosen
before the arithmetic probe, coefficients, moving radius, Y and Mellin eta. -/
theorem exists_rowBall_freeZero_re_bound (B : ℝ) (W : SmoothAnnularTest) :
    ∃ C Y₀ : ℝ, 0 < C ∧ 1 ≤ Y₀ ∧
      ∀ (P : ProbeData K SF) (c : ExteriorIdeal K SF → ℂ),
        (∀ I, ‖c I‖ ≤ 1) → ∀ (r : {r : ℝ // 0 < r}) (Y η : ℝ), Y₀ ≤ Y →
        (freeGramNormalizedZeroCorrection K S μv P c W Y η
          (rowBallArchTest K S B) (rowBallFiniteFamily K S B) r).re ≤ C / (r.val * Y) := by
  obtain ⟨C₀, Y₀, hC₀, hY₀, hdiag⟩ := exists_actualGramNormalizedDiagonal_norm_bound K S W
  let A : ℝ := ‖additiveGramPoissonFieldFactor K‖ * ‖rowBallDualTensorZero K S μv B‖ * C₀
  refine ⟨1 + A, Y₀, by dsimp only [A]; positivity, hY₀, ?_⟩
  intro P c hc r Y η hY
  have hYpos : 0 < Y := zero_lt_one.trans_le (hY₀.trans hY)
  calc
    _ ≤ r.val⁻¹ * ‖additiveGramPoissonFieldFactor K‖ * ‖rowBallDualTensorZero K S μv B‖ *
        ‖((Y ^ (-3 : ℝ) : ℝ) : ℂ) *
          (∑ I ∈ additiveGramIdealSupport K SF W Y,
            actualAdditiveGramPairCoefficient K SF c W Y η I I *
              (additiveGramDiagonalUnitCount K S P I : ℂ))‖ :=
      rowBall_freeZero_re_le_diagonal_norm K S μv B P c W Y η hYpos r
    _ ≤ r.val⁻¹ * ‖additiveGramPoissonFieldFactor K‖ * ‖rowBallDualTensorZero K S μv B‖ *
        (C₀ / Y) := mul_le_mul_of_nonneg_left (hdiag P c hc Y η hY)
          (mul_nonneg (mul_nonneg (inv_nonneg.mpr r.property.le) (norm_nonneg _))
            (norm_nonneg _))
    _ = A / (r.val * Y) := by dsimp only [A]; simp only [div_eq_mul_inv, mul_inv_rev]; ring
    _ ≤ (1 + A) / (r.val * Y) :=
      div_le_div_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (mul_pos r.property hYpos).le

/-- At the original Poisson radius Q^(-1), the diagonal is O(Q/Y),
uniformly in the original Mellin parameter. -/
theorem exists_rowBall_freeZero_re_Q_div_Y_bound (B : ℝ) (W : SmoothAnnularTest) :
    ∃ C Y₀ : ℝ, 0 < C ∧ 1 ≤ Y₀ ∧
      ∀ (P : ProbeData K SF) (c : ExteriorIdeal K SF → ℂ),
        (∀ I, ‖c I‖ ≤ 1) → ∀ (Q Y η : ℝ) (hQ : 0 < Q), Y₀ ≤ Y →
        (freeGramNormalizedZeroCorrection K S μv P c W Y η
          (rowBallArchTest K S B) (rowBallFiniteFamily K S B)
          ⟨Q⁻¹, inv_pos.mpr hQ⟩).re ≤ C * Q / Y := by
  obtain ⟨C, Y₀, hC, hY₀, hbound⟩ := exists_rowBall_freeZero_re_bound K S μv B W
  refine ⟨C, Y₀, hC, hY₀, ?_⟩
  intro P c hc Q Y η hQ hY
  calc
    _ ≤ C / (Q⁻¹ * Y) := hbound P c hc ⟨Q⁻¹, inv_pos.mpr hQ⟩ Y η hY
    _ = C * Q / Y := by simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]; ring

/-- Exact real-part transport for the complete zero term as it occurs in
the free orbital assembly. The actual covolume is not normalized away. -/
theorem rowBall_fullZero_re_eq_covol_mul
    (B : ℝ) (P : ProbeData K SF) (c : ExteriorIdeal K SF → ℂ)
    (W : SmoothAnnularTest) (Y η : ℝ) (r : {r : ℝ // 0 < r}) :
    ((((Y ^ (-3 : ℝ) : ℝ) : ℂ) * ((sUnitHaarCovolume K SF Γ).toReal : ℂ)) *
      (∑ I ∈ additiveGramIdealSupport K SF W Y,
        ∑ J ∈ additiveGramIdealSupport K SF W Y,
          actualAdditiveGramPairCoefficient K SF c W Y η I J *
            freeAdditiveGramPairZeroCorrection K S μv P I J
              (rowBallArchTest K S B) (rowBallFiniteFamily K S B) r)).re =
    (sUnitHaarCovolume K SF Γ).toReal *
      (freeGramNormalizedZeroCorrection K S μv P c W Y η
        (rowBallArchTest K S B) (rowBallFiniteFamily K S B) r).re := by
  have heq :
      (((Y ^ (-3 : ℝ) : ℝ) : ℂ) * ((sUnitHaarCovolume K SF Γ).toReal : ℂ)) *
        (∑ I ∈ additiveGramIdealSupport K SF W Y,
          ∑ J ∈ additiveGramIdealSupport K SF W Y,
            actualAdditiveGramPairCoefficient K SF c W Y η I J *
              freeAdditiveGramPairZeroCorrection K S μv P I J
                (rowBallArchTest K S B) (rowBallFiniteFamily K S B) r) =
      ((sUnitHaarCovolume K SF Γ).toReal : ℂ) *
        freeGramNormalizedZeroCorrection K S μv P c W Y η
          (rowBallArchTest K S B) (rowBallFiniteFamily K S B) r := by
    unfold freeGramNormalizedZeroCorrection
    ring
  rw [heq]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

end HeckeGeneral.ThetaSkeleton.Physical.ActualGramFreeZeroDraft
