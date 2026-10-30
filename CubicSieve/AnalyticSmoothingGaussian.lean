import CubicSieve.AnalyticSmoothingKernel
import CubicSieve.ProfileLower
import DedekindZetaZeroFree.Theta.Profiles.MixedGaussian

/-!
The actual Gaussian supplies a uniform lower bound on the entire positive
norm ball. Its archimedean value increases under contraction; the section
does not change the finite unit-shell coordinates. Thus no sum of row
annuli, growing prime, or M-epsilon loss enters the full-cutoff majorization.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace CubicSieve.AnalyticSmoothing

open NumberField IsDedekindDomain MeasureTheory DedekindZetaZeroFree
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis
open CubicSieve.ExteriorKernel CubicSieve.OrbitRows CubicSieve.OrbitKernel
open DedekindZetaZeroFree.AbelianQuotient.Theta
open scoped Classical BigOperators

variable {K : Type} [Field K] [NumberField K] (A : SArithmeticData K)
local notation "S" => (A.Sf : Set (HeightOneSpectrum (𝓞 K)))
local notation "T₁" => sLocalNormOneGroup K S
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local instance : MeasurableSpace T₁ := borel _
local instance : BorelSpace T₁ := ⟨rfl⟩

def gaussianTest : sLocalMultiplicativeGroup K S → ℂ :=
  sLocalTensorTestFunction K S (traceGaussianSchwartz K) (Profile.finiteTest A)

def gaussianProfile (r : {r : ℝ // 0 < r}) : ℂ :=
  sUnitOrbitalProfile K S (gaussianTest A) r

theorem gaussian_apply_real (x : V) :
    traceGaussianSchwartz K x = (Real.exp (-Real.pi * ‖x‖ ^ 2) : ℂ) := by
  simp [traceGaussianSchwartz_apply, latticeGaussian]

theorem gaussian_contract (x : V) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    (traceGaussianSchwartz K x).re ≤ (traceGaussianSchwartz K (a • x)).re := by
  rw [gaussian_apply_real, gaussian_apply_real]
  simp only [Complex.ofReal_re, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha0, mul_pow]
  apply Real.exp_le_exp.mpr
  have haa : a ^ 2 ≤ 1 := by nlinarith
  have hx := sq_nonneg ‖x‖
  have hmul : a ^ 2 * ‖x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right haa hx
  exact mul_le_mul_of_nonpos_left hmul (neg_nonpos.mpr Real.pi_pos.le)

theorem gaussianTest_re_nonneg (x : sLocalMultiplicativeGroup K S) :
    0 ≤ (gaussianTest A x).re := by
  rw [gaussianTest, sLocalTensorTestFunction, gaussian_apply_real, Profile.finiteTest_eq_real]
  simp only [← Complex.ofReal_mul, Complex.ofReal_re]
  exact mul_nonneg (Real.exp_pos _).le (Profile.finiteReal_nonneg A _)

theorem gaussian_slice_integrable (r : {r : ℝ // 0 < r}) :
    Integrable (sLocalSchwartzSlice K S (traceGaussianSchwartz K) (Profile.finiteTest A) r)
      (sUnitHaarMeasure K S) :=
  integrable_sLocalSchwartzSlice K S (⊤ : Subgroup (Set.unit S K))
    (traceGaussianSchwartz K) (Profile.finiteTest A)
    (Profile.finiteTest_continuous A) (Profile.finiteTest_compactSupport A) r

theorem gaussianProfile_re_nonneg (r : {r : ℝ // 0 < r}) :
    0 ≤ (gaussianProfile A r).re := by
  change 0 ≤ RCLike.re (∫ x : T₁, sLocalSchwartzSlice K S
    (traceGaussianSchwartz K) (Profile.finiteTest A) r x ∂sUnitHaarMeasure K S)
  rw [← integral_re (gaussian_slice_integrable A r)]
  exact integral_nonneg (fun x => gaussianTest_re_nonneg A _)

/-- Literal pointwise contraction of the actual norm-one slice. -/
theorem gaussian_slice_contract (t : ℝ) (ht : t ≤ 0) (x : T₁) :
    (sLocalSchwartzSlice K S (traceGaussianSchwartz K) (Profile.finiteTest A)
      (sUnitExpRadius 0) x).re ≤
    (sLocalSchwartzSlice K S (traceGaussianSchwartz K) (Profile.finiteTest A)
      (sUnitExpRadius t) x).re := by
  rw [sLocalSchwartzSlice_exp_eq, sLocalSchwartzSlice_exp_eq,
    zero_div, Real.exp_zero, one_smul]
  simp only [Profile.finiteTest_eq_real, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  apply mul_le_mul_of_nonneg_right _ (Profile.finiteReal_nonneg A _)
  apply gaussian_contract
  · exact (Real.exp_pos _).le
  · apply Real.exp_le_one_iff.mpr
    exact div_nonpos_of_nonpos_of_nonneg ht (Nat.cast_nonneg _)

theorem gaussianProfile_ge_one (r : {r : ℝ // 0 < r}) (hr : r.val ≤ 1) :
    (gaussianProfile A ⟨1, zero_lt_one⟩).re ≤ (gaussianProfile A r).re := by
  have he : sUnitExpRadius (Real.log r.val) = r :=
    Subtype.ext (Real.exp_log r.property)
  have h0 : sUnitExpRadius 0 = (⟨1, zero_lt_one⟩ : {r : ℝ // 0 < r}) :=
    Subtype.ext Real.exp_zero
  change RCLike.re (∫ x : T₁, sLocalSchwartzSlice K S
    (traceGaussianSchwartz K) (Profile.finiteTest A) ⟨1, zero_lt_one⟩ x
      ∂sUnitHaarMeasure K S) ≤
    RCLike.re (∫ x : T₁, sLocalSchwartzSlice K S
      (traceGaussianSchwartz K) (Profile.finiteTest A) r x ∂sUnitHaarMeasure K S)
  rw [← integral_re (gaussian_slice_integrable A ⟨1, zero_lt_one⟩),
    ← integral_re (gaussian_slice_integrable A r)]
  apply integral_mono (gaussian_slice_integrable A _).re (gaussian_slice_integrable A _).re
  intro x
  change (sLocalSchwartzSlice K S (traceGaussianSchwartz K) (Profile.finiteTest A)
    ⟨1, zero_lt_one⟩ x).re ≤
      (sLocalSchwartzSlice K S (traceGaussianSchwartz K) (Profile.finiteTest A) r x).re
  simpa only [he, h0] using gaussian_slice_contract A (Real.log r.val)
    (Real.log_nonpos r.property.le hr) x

theorem gaussianProfile_one_pos : 0 < (gaussianProfile A ⟨1, zero_lt_one⟩).re := by
  have hc := continuous_sLocalSchwartzSlice K S (traceGaussianSchwartz K)
    (Profile.finiteTest A) (Profile.finiteTest_continuous A) ⟨1, zero_lt_one⟩
  change 0 < RCLike.re (∫ x : T₁, sLocalSchwartzSlice K S
    (traceGaussianSchwartz K) (Profile.finiteTest A) ⟨1, zero_lt_one⟩ x
      ∂sUnitHaarMeasure K S)
  rw [← integral_re (gaussian_slice_integrable A ⟨1, zero_lt_one⟩)]
  apply integral_pos_of_integrable_nonneg_nonzero (Complex.continuous_re.comp hc)
    (gaussian_slice_integrable A ⟨1, zero_lt_one⟩).re
  · intro x
    exact gaussianTest_re_nonneg A _
  · have h0 : (⟨1, zero_lt_one⟩ : {r : ℝ // 0 < r}) = sUnitExpRadius 0 :=
      Subtype.ext Real.exp_zero.symm
    show (sLocalSchwartzSlice K S (traceGaussianSchwartz K) (Profile.finiteTest A)
      ⟨1, zero_lt_one⟩ (1 : T₁)).re ≠ 0
    rw [h0, sLocalSchwartzSlice_exp_eq, zero_div, Real.exp_zero, one_smul,
      gaussian_apply_real, Profile.finiteTest_eq_real]
    have hfinite : Profile.finiteReal A
        (fun v : S => (((1 : T₁) : sLocalMultiplicativeGroup K S).2 v).val) = 1 := by
      unfold Profile.finiteReal
      apply Finset.prod_eq_one
      intro v hv
      apply ite_eq_left
      exact (TateFiniteShell.mem_unitShell_iff K v.val 1).mpr (by simp)
    rw [hfinite, Complex.ofReal_one, mul_one, Complex.ofReal_re]
    exact (Real.exp_pos _).ne'

theorem gaussian_uniform_ball_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ r : {r : ℝ // 0 < r}, r.val ≤ 1 →
      c ≤ (gaussianProfile A r).re :=
  ⟨_, gaussianProfile_one_pos A, fun r hr => gaussianProfile_ge_one A r hr⟩

variable (D : ThetaArithmeticData K (A.Sf : Set (HeightOneSpectrum (𝓞 K))))

/-- The actual Gaussian majorizes every squarefree row of the original full
cutoff. The complete orbital sum retains every sixth-unit sector. -/
theorem gaussian_majorizes_full_cutoff :
    ∃ c : ℝ, 0 < c ∧ ∀ (M : ℝ) (hM : 1 ≤ M),
      ∀ T : Finset (ExteriorIdeal K S), ∀ z : ExteriorIdeal K S → ℂ,
        c * (∑ I ∈ ExteriorSieve.cutoff K S M,
          ‖∑ J ∈ T, positiveKernel K S D I J * z J‖ ^ 2) ≤
            smoothEnergy K S D (traceGaussianSchwartz K) (Profile.finiteTest A)
              M (by linarith [hM]) T z := by
  obtain ⟨c, hc, hb⟩ := gaussian_uniform_ball_lower A
  refine ⟨c, hc, fun M hM T z => ?_⟩
  exact smooth_majorizes_cutoff K S D (traceGaussianSchwartz K) (Profile.finiteTest A)
    (Profile.finiteTest_continuous A) (Profile.finiteTest_compactSupport A)
    (gaussianProfile_re_nonneg A) c hc hb M 1 hM T z

end CubicSieve.AnalyticSmoothing
