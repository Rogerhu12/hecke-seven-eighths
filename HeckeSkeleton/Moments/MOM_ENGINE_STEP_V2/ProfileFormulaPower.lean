import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLogProfileBounds
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Topology.Algebra.Polynomial

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Uniform real powers on a fixed positive profile window

The real exponent ranges over a fixed compact interval. Its iterated
ordinary derivative is the descending Pochhammer polynomial times the
corresponding real power. Compactness bounds that explicit expression
before choosing the exponent. The existing zero-exponent log-phase
estimate then supplies the only moving-frequency factor.
-/

noncomputable section
open scoped Classical BigOperators ContDiff

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.ProfileFormulaProof

open EngineStep.CanonicalLogProfiles

private theorem complexPower_derivative_norm (δ y : ℝ) (hy : 0 < y) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun x : ℝ => ((x ^ δ : ℝ) : ℂ)) y‖ =
      ‖(descPochhammer ℝ n).eval δ * y ^ (δ - n)‖ := by
  have hf : ContDiffAt ℝ n (fun x : ℝ => x ^ δ) y :=
    Real.contDiffAt_rpow_const_of_ne hy.ne'
  have hcast : iteratedDeriv n (fun x : ℝ => ((x ^ δ : ℝ) : ℂ)) y =
      ((iteratedDeriv n (fun x : ℝ => x ^ δ) y : ℝ) : ℂ) := by
    simpa only [Complex.real_smul, mul_one] using
      (iteratedDeriv_smul_const (F := ℂ) hf (1 : ℂ))
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, hcast, Complex.norm_real,
    iteratedDeriv_eq_iterate, Real.iter_deriv_rpow_const]

private theorem complexPower_smoothAt (δ : ℝ) {y : ℝ} (hy : 0 < y) :
    ContDiffAt ℝ ∞ (fun x : ℝ => ((x ^ δ : ℝ) : ℂ)) y :=
  Complex.ofRealCLM.contDiff.contDiffAt.comp y
    (Real.contDiffAt_rpow_const_of_ne hy.ne')

private theorem complexPower_derivative_bound_uniform
    (window : Set ℝ) (hcompact : IsCompact window)
    (hpositive : window ⊆ Set.Ioi 0) (H : ℝ) (J : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ δ : ℝ, |δ| ≤ H →
      ∀ y ∈ window, ∀ n : ℕ, n ≤ J →
        ‖iteratedFDeriv ℝ n (fun x : ℝ => ((x ^ δ : ℝ) : ℂ)) y‖ ≤ C := by
  have hcompact' : IsCompact (Set.Icc (-H) H ×ˢ window) :=
    isCompact_Icc.prod hcompact
  have hsingle (n : ℕ) : ∃ b : ℝ, ∀ δ : ℝ, |δ| ≤ H →
      ∀ y ∈ window, ‖(descPochhammer ℝ n).eval δ * y ^ (δ - n)‖ ≤ b := by
    have hpoly : Continuous (fun z : ℝ × ℝ => (descPochhammer ℝ n).eval z.1) :=
      (descPochhammer ℝ n).continuous.comp continuous_fst
    have hpower : ContinuousOn (fun z : ℝ × ℝ => z.2 ^ (z.1 - (n : ℝ)))
        (Set.Icc (-H) H ×ˢ window) :=
      continuous_snd.continuousOn.rpow
        (continuous_fst.sub continuous_const).continuousOn
        (fun z hz => Or.inl (hpositive hz.2).ne')
    obtain ⟨b, hb⟩ := hcompact'.bddAbove_image (hpoly.continuousOn.mul hpower).norm
    refine ⟨b, fun δ hδ y hy => ?_⟩
    exact hb (Set.mem_image_of_mem _
      (show (δ, y) ∈ Set.Icc (-H) H ×ˢ window from ⟨abs_le.mp hδ, hy⟩))
  choose b hb using hsingle
  let C := 1 + ∑ n ∈ Finset.range (J + 1), max (b n) 0
  have hsum : 0 ≤ ∑ n ∈ Finset.range (J + 1), max (b n) 0 :=
    Finset.sum_nonneg (fun _ _ => le_max_right _ _)
  have hC : 1 ≤ C := by dsimp [C]; linarith
  refine ⟨C, hC, fun δ hδ y hy n hn => ?_⟩
  have hnC := Finset.single_le_sum
    (fun i (_ : i ∈ Finset.range (J + 1)) => le_max_right (b i) 0)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))
  have hbC : b n ≤ C := by dsimp [C]; linarith [le_max_left (b n) 0]
  rw [complexPower_derivative_norm δ y (hpositive hy) n]
  exact (hb n δ hδ y hy).trans hbC

/-- A single fixed constant controls every bounded real exponent and
all moving imaginary frequencies on the same positive compact window. -/
theorem normalShape_derivative_bound_uniform
    (window : Set ℝ) (hcompact : IsCompact window)
    (hpositive : window ⊆ Set.Ioi 0) (H : ℝ) (hH : 0 ≤ H) (J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ δ : ℝ, |δ| ≤ H → ∀ ν : ℝ,
      ∀ y ∈ window, ∀ n : ℕ, n ≤ J →
        ‖iteratedFDeriv ℝ n (EngineStep.CanonicalLogProfiles.normalShape δ ν) y‖ ≤
          C * (1 + |ν|) ^ J := by
  obtain ⟨R, hR, hrpow⟩ :=
    complexPower_derivative_bound_uniform window hcompact hpositive H J
  obtain ⟨P, hP, hphase⟩ :=
    normalShape_derivative_bound window hcompact hpositive 0 J
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have hΩ : IsOpen (Set.Ioi (0 : ℝ)) := isOpen_Ioi
  have hfactor (δ ν : ℝ) : normalShape δ ν =
      (fun y : ℝ => ((y ^ δ : ℝ) : ℂ) * normalShape 0 ν y) := by
    funext y
    simp only [normalShape, Real.rpow_zero, Complex.ofReal_one, one_mul]
  refine ⟨(2 : ℝ) ^ J * R * P,
    mul_nonneg (mul_nonneg (by positivity) hR0) hP,
    fun δ hδ ν y hy n hn => ?_⟩
  have hy0 : y ∈ Set.Ioi (0 : ℝ) := hpositive hy
  have hpon : ContDiffOn ℝ ∞ (fun x : ℝ => ((x ^ δ : ℝ) : ℂ)) (Set.Ioi 0) :=
    fun _ hx => (complexPower_smoothAt δ hx).contDiffWithinAt
  have hb := norm_iteratedFDerivWithin_mul_le hpon (normalShape_smoothOn 0 ν)
    hΩ.uniqueDiffOn hy0 (show (n : ℕ∞ω) ≤ ∞ by simp)
  rw [← hfactor δ ν] at hb
  rw [iteratedFDerivWithin_eq_iteratedFDeriv (s := Set.Ioi (0 : ℝ)) hΩ.uniqueDiffOn
    ((normalShape_smoothAt δ ν hy0).of_le (by simp)) hy0] at hb
  simp_rw [iteratedFDerivWithin_eq_iteratedFDeriv (s := Set.Ioi (0 : ℝ)) hΩ.uniqueDiffOn
      ((complexPower_smoothAt δ hy0).of_le (by simp)) hy0,
    iteratedFDerivWithin_eq_iteratedFDeriv (s := Set.Ioi (0 : ℝ)) hΩ.uniqueDiffOn
      ((normalShape_smoothAt 0 ν hy0).of_le (by simp)) hy0] at hb
  have hsum : (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) = (2 : ℝ) ^ n := by
    exact_mod_cast Nat.sum_range_choose n
  calc
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (fun x : ℝ => ((x ^ δ : ℝ) : ℂ)) y‖ *
        ‖iteratedFDeriv ℝ (n - i) (normalShape 0 ν) y‖ := hb
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * R *
        (P * (1 + |ν|) ^ J) := by
      apply Finset.sum_le_sum
      intro i hi
      have hin : i ≤ n := Finset.mem_range_succ_iff.mp hi
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hrpow δ hδ y hy i (hin.trans hn))
          (Nat.cast_nonneg _))
        (hphase ν y hy (n - i) ((Nat.sub_le n i).trans hn))
        (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hR0)
    _ = (2 : ℝ) ^ n * R * (P * (1 + |ν|) ^ J) := by
      rw [← Finset.sum_mul, ← Finset.sum_mul, hsum]
    _ ≤ (2 : ℝ) ^ J * R * (P * (1 + |ν|) ^ J) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hn) hR0)
        (mul_nonneg hP (pow_nonneg (by positivity) _))
    _ = ((2 : ℝ) ^ J * R * P) * (1 + |ν|) ^ J := by ring

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.ProfileFormulaProof

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.ProfileFormulaProof.normalShape_derivative_bound_uniform
