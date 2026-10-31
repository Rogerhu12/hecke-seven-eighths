import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Convert
import Lean.Elab.Tactic.NormCast
import Lean.Elab.Tactic.Omega

/-!
# Uniform logarithmic detector profiles

The scaled-composition estimate below replaces the missing coupled-factor
helper in the supplied reference.  It is uniform on the entire real line,
not only on a chosen logarithmic window.  The outer derivative decay cancels
the powers introduced by composing with R*exp(y).
-/

set_option autoImplicit false
noncomputable section

namespace ExpansionRecipe.LogProfile

open MeasureTheory
open scoped BigOperators Classical ContDiff FourierTransform SchwartzMap

lemma iteratedFDeriv_scaled_exp_norm (R : ℝ) (hR : 0 ≤ R) (n : ℕ) (y : ℝ) :
    ‖iteratedFDeriv ℝ n (fun z : ℝ => R * Real.exp z) y‖ = R * Real.exp y := by
  have he : iteratedDeriv n Real.exp = Real.exp := by
    simpa using iteratedDeriv_exp_const_mul n (1 : ℝ)
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_const_mul_field, he]
  exact Real.norm_of_nonneg (mul_nonneg hR (Real.exp_pos y).le)

/-- Pointwise cancellation of the entire scaling cost. -/
theorem scaled_derivatives_of_decay (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (K : ℕ) (CF : ℝ) (hCF : 0 ≤ CF)
    (hdecay : ∀ i ≤ K, ∀ u : ℝ, 0 ≤ u →
      (1 + u) ^ K * ‖iteratedFDeriv ℝ i F u‖ ≤ CF)
    (R : ℝ) (hR : 0 ≤ R) (j : ℕ) (hj : j ≤ K) (y : ℝ) :
    ‖iteratedFDeriv ℝ j (fun z => F (R * Real.exp z)) y‖ ≤
      (j.factorial : ℝ) * CF := by
  let u := R * Real.exp y
  have hu : 0 ≤ u := mul_nonneg hR (Real.exp_pos y).le
  have hb : 0 < 1 + u := by linarith
  have hb1 : 1 ≤ 1 + u := by linarith
  have hinner : ContDiff ℝ ∞ (fun z : ℝ => R * Real.exp z) := by fun_prop
  have hbnd := norm_iteratedFDeriv_comp_le hF hinner (by simp : (j : ℕ∞ω) ≤ ∞)
    y (C := CF / (1 + u) ^ K) (D := 1 + u) (by
      intro i hi
      apply (le_div_iff₀ (pow_pos hb K)).mpr
      simpa [mul_comm] using hdecay i (hi.trans hj) u hu) (by
      intro i hi _hi
      rw [iteratedFDeriv_scaled_exp_norm R hR i y]
      change u ≤ (1 + u) ^ i
      calc
        u ≤ 1 + u := by linarith
        _ = (1 + u) ^ (1 : ℕ) := (pow_one _).symm
        _ ≤ (1 + u) ^ i := pow_le_pow_right₀ hb1 hi)
  change ‖iteratedFDeriv ℝ j (fun z => F (R * Real.exp z)) y‖ ≤ _ at hbnd
  calc
    _ ≤ (j.factorial : ℝ) * (CF / (1 + u) ^ K) * (1 + u) ^ j := hbnd
    _ ≤ (j.factorial : ℝ) * (CF / (1 + u) ^ K) * (1 + u) ^ K :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hb1 hj) (by positivity)
    _ = (j.factorial : ℝ) * CF := by
      rw [mul_assoc, div_mul_cancel₀ _ (pow_ne_zero _ hb.ne')]

theorem scaled_schwartz_derivatives (F : SchwartzMap ℝ ℂ) (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 ≤ R → ∀ j ≤ K, ∀ y : ℝ,
      ‖iteratedFDeriv ℝ j (fun z => F (R * Real.exp z)) y‖ ≤ C := by
  let CF : ℝ := 2 ^ K * (Finset.Iic (K, K)).sup
    (fun p => SchwartzMap.seminorm ℝ p.1 p.2) F
  have hCF : 0 ≤ CF := by dsimp [CF]; positivity
  have hdecay : ∀ i ≤ K, ∀ u : ℝ, 0 ≤ u →
      (1 + u) ^ K * ‖iteratedFDeriv ℝ i F u‖ ≤ CF := by
    intro i hi u hu
    simpa [CF, Real.norm_of_nonneg hu] using
      (SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
        (m := (K, K)) le_rfl hi F u)
  refine ⟨(K.factorial : ℝ) * CF, by positivity, ?_⟩
  intro R hR j hj y
  exact (scaled_derivatives_of_decay F (F.smooth ⊤) K CF hCF hdecay R hR j hj y).trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.factorial_le hj) hCF)

def expNeg (x : ℝ) : ℂ := Complex.exp (-(x : ℂ))

lemma expNeg_smooth : ContDiff ℝ ∞ expNeg :=
  Complex.ofRealCLM.contDiff.neg.cexp

lemma expNeg_hasDerivAt (x : ℝ) : HasDerivAt expNeg (-expNeg x) x := by
  have h := ((Complex.ofRealCLM.hasDerivAt (x := x)).neg).cexp
  convert! h using 1; simp [expNeg]

lemma iteratedDeriv_expNeg (n : ℕ) :
    iteratedDeriv n expNeg = fun x => (-1 : ℂ) ^ n * expNeg x := by
  induction n with
  | zero => ext x; simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    rw [deriv_const_mul_field, (expNeg_hasDerivAt x).deriv, pow_succ]
    ring

lemma expNeg_derivative_norm (n : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ n expNeg x‖ = Real.exp (-x) := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_expNeg]
  simp [expNeg, norm_pow, Complex.norm_exp]

lemma expNeg_derivative_decay (n i : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    (1 + x) ^ n * ‖iteratedFDeriv ℝ i expNeg x‖ ≤
      (n.factorial : ℝ) * Real.exp 1 := by
  rw [expNeg_derivative_norm]
  have hf : 0 < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hp := (div_le_iff₀ hf).mp
    (Real.pow_div_factorial_le_exp (1 + x) (by linarith : 0 ≤ 1 + x) n)
  calc
    _ ≤ (Real.exp (1 + x) * (n.factorial : ℝ)) * Real.exp (-x) :=
      mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
    _ = _ := by
      rw [mul_right_comm, ← Real.exp_add, show (1 + x) + (-x) = 1 by ring]
      ring

theorem scaled_expNeg_derivatives (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 ≤ R → ∀ j ≤ K, ∀ y : ℝ,
      ‖iteratedFDeriv ℝ j (fun z => expNeg (R * Real.exp z)) y‖ ≤ C := by
  let CF := (K.factorial : ℝ) * Real.exp 1
  have hCF : 0 ≤ CF := by dsimp [CF]; positivity
  refine ⟨(K.factorial : ℝ) * CF, by positivity, ?_⟩
  intro R hR j hj y
  exact (scaled_derivatives_of_decay expNeg expNeg_smooth K CF hCF
    (fun i _ x hx => expNeg_derivative_decay K i x hx) R hR j hj y).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.factorial_le hj) hCF)

def logSourceFun (Ω V T : ℝ → ℂ) (A B C y : ℝ) : ℂ :=
  Ω y * (1 - V (A * Real.exp y)) * expNeg (B * Real.exp y) * T (C * Real.exp y)

lemma logSource_smooth (Ω V T : ℝ → ℂ) (hΩ : ContDiff ℝ ∞ Ω)
    (hV : ContDiff ℝ ∞ V) (hT : ContDiff ℝ ∞ T) (A B C : ℝ) :
    ContDiff ℝ ∞ (logSourceFun Ω V T A B C) := by
  unfold logSourceFun
  have hE := expNeg_smooth
  fun_prop

lemma logSource_compact (Ω V T : ℝ → ℂ) (hΩ : HasCompactSupport Ω)
    (A B C : ℝ) : HasCompactSupport (logSourceFun Ω V T A B C) :=
  ((hΩ.mul_right).mul_right).mul_right

def logSource (Ω V T : ℝ → ℂ) (hΩc : HasCompactSupport Ω)
    (hΩ : ContDiff ℝ ∞ Ω) (hV : ContDiff ℝ ∞ V) (hT : ContDiff ℝ ∞ T)
    (A B C : ℝ) : SchwartzMap ℝ ℂ :=
  (logSource_compact Ω V T hΩc A B C).toSchwartzMap
    (logSource_smooth Ω V T hΩ hV hT A B C)

lemma const_one_derivative_norm (j : ℕ) (y : ℝ) :
    ‖iteratedFDeriv ℝ j (fun _ : ℝ => (1 : ℂ)) y‖ ≤ 1 := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_const]
  split_ifs <;> simp

lemma complement_derivative_bound (F : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (C : ℝ) (j : ℕ) (y : ℝ) (hbound : ‖iteratedFDeriv ℝ j F y‖ ≤ C) :
    ‖iteratedFDeriv ℝ j (fun z => 1 - F z) y‖ ≤ 1 + C := by
  change ‖iteratedFDeriv ℝ j ((fun _ : ℝ => (1 : ℂ)) - F) y‖ ≤ _
  rw [iteratedFDeriv_sub contDiff_const (hF.of_le (by simp))]
  change ‖iteratedFDeriv ℝ j (fun _ : ℝ => (1 : ℂ)) y -
    iteratedFDeriv ℝ j F y‖ ≤ _
  exact (norm_sub_le _ _).trans (add_le_add (const_one_derivative_norm j y) hbound)

lemma product_derivative_bound (F G : ℝ → ℂ) (hF : ContDiff ℝ ∞ F)
    (hG : ContDiff ℝ ∞ G) (CF CG : ℝ) (hCF : 0 ≤ CF) (hCG : 0 ≤ CG)
    (K j : ℕ) (hj : j ≤ K) (y : ℝ)
    (hFb : ∀ i ≤ K, ‖iteratedFDeriv ℝ i F y‖ ≤ CF)
    (hGb : ∀ i ≤ K, ‖iteratedFDeriv ℝ i G y‖ ≤ CG) :
    ‖iteratedFDeriv ℝ j (fun z => F z * G z) y‖ ≤ (2 : ℝ) ^ K * CF * CG := by
  apply (norm_iteratedFDeriv_mul_le hF hG y (n := j) (by simp)).trans
  calc
    _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * CF * CG := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i ≤ j := by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hFb i (hi'.trans hj)) (by positivity))
        (hGb (j - i) ((Nat.sub_le j i).trans hj)) (norm_nonneg _) (by positivity)
    _ = (2 : ℝ) ^ j * CF * CG := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      congr 2
      exact_mod_cast Nat.sum_range_choose j
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj) hCF) hCG

theorem logSource_uniform_derivatives (Ω : ℝ → ℂ) (V T : SchwartzMap ℝ ℂ)
    (hΩc : HasCompactSupport Ω) (hΩ : ContDiff ℝ ∞ Ω) (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A B D : ℝ, 0 ≤ A → 0 ≤ B → 0 ≤ D →
      ∀ j ≤ K, ∀ y : ℝ,
        ‖iteratedFDeriv ℝ j (logSourceFun Ω V T A B D) y‖ ≤ C := by
  obtain ⟨CΩ, hCΩ, hbΩ⟩ := hΩc.exists_bound_iteratedFDeriv hΩ K
  obtain ⟨CV, hCV, hbV⟩ := scaled_schwartz_derivatives V K
  obtain ⟨CT, hCT, hbT⟩ := scaled_schwartz_derivatives T K
  obtain ⟨CE, hCE, hbE⟩ := scaled_expNeg_derivatives K
  let Q := (2 : ℝ) ^ K
  refine ⟨Q * (Q * (Q * CΩ * (1 + CV)) * CE) * CT, by dsimp [Q]; positivity, ?_⟩
  intro A B D hA hB hD j hj y
  let v : ℝ → ℂ := fun z => V (A * Real.exp z)
  let e : ℝ → ℂ := fun z => expNeg (B * Real.exp z)
  let t : ℝ → ℂ := fun z => T (D * Real.exp z)
  have hv : ContDiff ℝ ∞ v := (V.smooth ⊤).comp (by fun_prop)
  have he : ContDiff ℝ ∞ e := expNeg_smooth.comp (by fun_prop)
  have ht : ContDiff ℝ ∞ t := (T.smooth ⊤).comp (by fun_prop)
  have hcv : ContDiff ℝ ∞ (fun z => 1 - v z) := contDiff_const.sub hv
  have hcomp (i : ℕ) (hi : i ≤ K) :
      ‖iteratedFDeriv ℝ i (fun z => 1 - v z) y‖ ≤ 1 + CV :=
    complement_derivative_bound v hv CV i y (hbV A hA i hi y)
  have hfirst (i : ℕ) (hi : i ≤ K) :
      ‖iteratedFDeriv ℝ i (fun z => Ω z * (1 - v z)) y‖ ≤ Q * CΩ * (1 + CV) :=
    product_derivative_bound Ω _ hΩ hcv CΩ (1 + CV) hCΩ (by positivity) K i hi y
      (fun q hq => hbΩ q hq y) hcomp
  have hsecond (i : ℕ) (hi : i ≤ K) :
      ‖iteratedFDeriv ℝ i (fun z => Ω z * (1 - v z) * e z) y‖ ≤
        Q * (Q * CΩ * (1 + CV)) * CE :=
    product_derivative_bound _ e (hΩ.mul hcv) he _ CE (by dsimp [Q]; positivity) hCE
      K i hi y hfirst (fun q hq => hbE B hB q hq y)
  exact product_derivative_bound _ t ((hΩ.mul hcv).mul he) ht _ CT
    (by dsimp [Q]; positivity) hCT K j hj y hsecond (fun q hq => hbT D hD q hq y)

lemma logSource_support (Ω V T : ℝ → ℂ) (A B C : ℝ) :
    tsupport (logSourceFun Ω V T A B C) ⊆ tsupport Ω :=
  tsupport_mul_subset_left.trans (tsupport_mul_subset_left.trans tsupport_mul_subset_left)

theorem logSource_uniform_seminorm (Ω : ℝ → ℂ) (V T : SchwartzMap ℝ ℂ)
    (hΩc : HasCompactSupport Ω) (hΩ : ContDiff ℝ ∞ Ω)
    (L : ℝ) (hL : 0 ≤ L) (hwindow : tsupport Ω ⊆ Set.Icc (-L) L) (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A B D : ℝ, 0 ≤ A → 0 ≤ B → 0 ≤ D →
      ∀ k j : ℕ, j ≤ K →
      SchwartzMap.seminorm ℝ k j
        (logSource Ω V T hΩc hΩ (V.smooth ⊤) (T.smooth ⊤) A B D) ≤ L ^ k * C := by
  obtain ⟨C, hC, hb⟩ := logSource_uniform_derivatives Ω V T hΩc hΩ K
  refine ⟨C, hC, ?_⟩
  intro A B D hA hB hD k j hj
  apply SchwartzMap.seminorm_le_bound' ℝ k j _ (by positivity)
  intro y
  change ‖y‖ ^ k * ‖iteratedDeriv j (logSourceFun Ω V T A B D) y‖ ≤ L ^ k * C
  rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  by_cases hz : ‖iteratedFDeriv ℝ j (logSourceFun Ω V T A B D) y‖ = 0
  · rw [hz, mul_zero]; positivity
  have hys : y ∈ tsupport Ω := logSource_support Ω V T A B D
    ((support_iteratedFDeriv_subset j) (by simpa [Function.mem_support] using hz))
  have hy : |y| ≤ L := abs_le.mpr (hwindow hys)
  exact mul_le_mul (by simpa [Real.norm_eq_abs] using (pow_le_pow_left₀ (abs_nonneg y) hy k))
    (hb A B D hA hB hD j hj y) (norm_nonneg _) (pow_nonneg hL k)

end ExpansionRecipe.LogProfile

#print axioms ExpansionRecipe.LogProfile.scaled_derivatives_of_decay
#print axioms ExpansionRecipe.LogProfile.logSource_uniform_derivatives
#print axioms ExpansionRecipe.LogProfile.logSource_uniform_seminorm
