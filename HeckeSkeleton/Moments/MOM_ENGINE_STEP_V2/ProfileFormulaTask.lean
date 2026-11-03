import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.ProfileFormulaPower
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.ProfileFormulaTransforms

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# N5a: uniform original-profile log-phase and dilation control

Paper: 3043–3073. The finite input orders and all constants precede
both the actual original profile and every Fourier parameter. The
representative uses its prescribed dilation, conjugation, real power,
scalar, and translation, with equality on the whole real line.
-/

noncomputable section
open scoped Classical BigOperators SchwartzMap Topology ContDiff

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks

open HeckeGeneral.Analysis EngineStep.CanonicalLogProfiles ProfileFormulaProof

private theorem shapeSchwartz_seminorm_bound_uniform
    (window : Set ℝ) (hcompact : IsCompact window) (hpositive : window ⊆ Set.Ioi 0)
    (H : ℝ) (hH : 0 ≤ H) (K J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ δ : ℝ, |δ| ≤ H → ∀ (ν : ℝ) (φ : 𝓢(ℝ, ℂ))
      (hsupport : tsupport φ ⊆ window), ∀ k ≤ K, ∀ n ≤ J,
      SchwartzMap.seminorm ℂ k n (shapeSchwartz window hcompact hpositive δ ν φ hsupport) ≤
        C * (1 + |ν|) ^ J *
          (Finset.Iic (K, J)).sup (schwartzSeminormFamily ℂ ℝ ℂ) φ := by
  obtain ⟨D, hD, hshape⟩ :=
    normalShape_derivative_bound_uniform window hcompact hpositive H hH J
  refine ⟨(2 : ℝ) ^ J * D, mul_nonneg (by positivity) hD,
    fun δ hδ ν φ hsupport k hk n hn => ?_⟩
  let P := (Finset.Iic (K, J)).sup (schwartzSeminormFamily ℂ ℝ ℂ) φ
  let Q := D * (1 + |ν|) ^ J
  have hP : 0 ≤ P := apply_nonneg _ _
  have hQ : 0 ≤ Q := mul_nonneg hD (pow_nonneg (by positivity) _)
  have hfinal : 0 ≤ ((2 : ℝ) ^ J * D) * (1 + |ν|) ^ J * P := by positivity
  apply SchwartzMap.seminorm_le_bound ℂ k n _ hfinal
  intro y
  change ‖y‖ ^ k * ‖iteratedFDeriv ℝ n (shapeProduct δ ν φ) y‖ ≤ _
  by_cases hy : y ∈ tsupport φ
  · have hywindow := hsupport hy
    have hy0 := hpositive hywindow
    have hΩ : IsOpen (Set.Ioi (0 : ℝ)) := isOpen_Ioi
    have hb := norm_iteratedFDerivWithin_mul_le φ.smooth'.contDiffOn
      (normalShape_smoothOn δ ν) hΩ.uniqueDiffOn hy0
      (show (n : ℕ∞ω) ≤ ∞ by simp)
    change ‖iteratedFDerivWithin ℝ n (shapeProduct δ ν φ) (Set.Ioi 0) y‖ ≤ _ at hb
    rw [iteratedFDerivWithin_eq_iteratedFDeriv (s := Set.Ioi (0 : ℝ)) hΩ.uniqueDiffOn
      (((shapeProduct_smooth δ ν φ (hsupport.trans hpositive)).contDiffAt).of_le (by simp))
      hy0] at hb
    simp_rw [iteratedFDerivWithin_eq_iteratedFDeriv (s := Set.Ioi (0 : ℝ)) hΩ.uniqueDiffOn
        (φ.smooth'.contDiffAt.of_le (by simp)) hy0,
      iteratedFDerivWithin_eq_iteratedFDeriv (s := Set.Ioi (0 : ℝ)) hΩ.uniqueDiffOn
        ((normalShape_smoothAt δ ν hy0).of_le (by simp)) hy0] at hb
    have hweighted : ‖y‖ ^ k * ‖iteratedFDeriv ℝ n (shapeProduct δ ν φ) y‖ ≤
        ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          (‖y‖ ^ k * ‖iteratedFDeriv ℝ i φ y‖) *
          ‖iteratedFDeriv ℝ (n - i) (normalShape δ ν) y‖ := by
      apply (mul_le_mul_of_nonneg_left hb (pow_nonneg (norm_nonneg _) _)).trans_eq
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [show (φ.toFun : ℝ → ℂ) = ⇑φ from rfl]
      ring
    have hsum : (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) = (2 : ℝ) ^ n := by
      exact_mod_cast Nat.sum_range_choose n
    calc
      _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          (‖y‖ ^ k * ‖iteratedFDeriv ℝ i φ y‖) *
          ‖iteratedFDeriv ℝ (n - i) (normalShape δ ν) y‖ := hweighted
      _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * P * Q := by
        apply Finset.sum_le_sum
        intro i hi
        have hin : i ≤ n := Finset.mem_range_succ_iff.mp hi
        have hφ : ‖y‖ ^ k * ‖iteratedFDeriv ℝ i φ y‖ ≤ P :=
          (SchwartzMap.le_seminorm ℂ k i φ y).trans
            (Seminorm.le_finset_sup_apply (p := schwartzSeminormFamily ℂ ℝ ℂ)
              (Finset.mem_Iic.mpr (show (k, i) ≤ (K, J) from ⟨hk, hin.trans hn⟩)))
        exact mul_le_mul (mul_le_mul_of_nonneg_left hφ (Nat.cast_nonneg _))
          (hshape δ hδ ν y hywindow (n - i) ((Nat.sub_le n i).trans hn))
          (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hP)
      _ = (2 : ℝ) ^ n * P * Q := by
        rw [← Finset.sum_mul, ← Finset.sum_mul, hsum]
      _ ≤ (2 : ℝ) ^ J * P * Q :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hn) hP) hQ
      _ = ((2 : ℝ) ^ J * D) * (1 + |ν|) ^ J * P := by dsimp only [Q]; ring
  · have hz : iteratedFDeriv ℝ n (shapeProduct δ ν φ) y = 0 := by
      apply Function.notMem_support.mp
      intro h
      exact hy ((tsupport_shapeProduct_subset δ ν φ) (support_iteratedFDeriv_subset n h))
    rw [hz, norm_zero, mul_zero]
    exact hfinal

/-- A prescribed finite target set determines the finite original
orders and the frequency degree before any profile is supplied. -/
private theorem shapeSchwartz_finset_bound_uniform
    (window : Set ℝ) (hcompact : IsCompact window) (hpositive : window ⊆ Set.Ioi 0)
    (H : ℝ) (hH : 0 ≤ H) (s : Finset (ℕ × ℕ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ δ : ℝ, |δ| ≤ H → ∀ (ν : ℝ) (φ : 𝓢(ℝ, ℂ))
      (hsupport : tsupport φ ⊆ window),
      s.sup (schwartzSeminormFamily ℂ ℝ ℂ)
          (shapeSchwartz window hcompact hpositive δ ν φ hsupport) ≤
        C * (1 + |ν|) ^ (s.sup Prod.snd) *
          (Finset.Iic (s.sup Prod.fst, s.sup Prod.snd)).sup
            (schwartzSeminormFamily ℂ ℝ ℂ) φ := by
  obtain ⟨C, hC, hbound⟩ := shapeSchwartz_seminorm_bound_uniform window hcompact hpositive
    H hH (s.sup Prod.fst) (s.sup Prod.snd)
  refine ⟨C, hC, fun δ hδ ν φ hs => ?_⟩
  apply Seminorm.finset_sup_apply_le (by positivity)
  intro p hp
  exact hbound δ hδ ν φ hs p.1 (Finset.le_sup (f := Prod.fst) hp)
    p.2 (Finset.le_sup (f := Prod.snd) hp)


private def frequency (f : ProfileFormula) (ξ : EngineParameter) : ℝ :=
  2 * Real.pi * ProfileFormula.linear f.phase ξ

private def translationFrequency (f : ProfileFormula) (ξ : EngineParameter) : ℝ :=
  2 * Real.pi * ProfileFormula.linear f.translation ξ

private theorem phase_product (f : ProfileFormula) (ξ : EngineParameter) (x : ℝ) :
    traceRealMovingPhase (frequency f ξ) (Real.log x) *
        traceRealMovingPhase (translationFrequency f ξ) 1 =
      Complex.exp (((2 * Real.pi *
        (ProfileFormula.linear f.phase ξ * Real.log x +
          ProfileFormula.linear f.translation ξ) : ℝ) : ℂ) * Complex.I) := by
  simp only [traceRealMovingPhase, ← Complex.exp_add]
  congr 1
  dsimp only [frequency, translationFrequency]
  push_cast
  ring

private theorem normalShape_value (δ ν x : ℝ) :
    normalShape δ ν x = ((x ^ δ : ℝ) : ℂ) * traceRealMovingPhase ν (Real.log x) := by
  rfl

private def representative
    (window : Set ℝ) (hcompact : IsCompact window) (hpositive : window ⊆ Set.Ioi 0)
    (f : ProfileFormula) (hs : tsupport (inputProfile f) ⊆ window)
    (ξ : EngineParameter) : 𝓢(ℝ, ℂ) :=
  (f.scalar * traceRealMovingPhase (translationFrequency f ξ) 1) •
    shapeSchwartz window hcompact hpositive f.power (frequency f ξ) (inputProfile f) hs

private theorem representative_apply
    (window : Set ℝ) (hcompact : IsCompact window) (hpositive : window ⊆ Set.Ioi 0)
    (f : ProfileFormula) (hs : tsupport (inputProfile f) ⊆ window)
    (ξ : EngineParameter) (x : ℝ) :
    representative window hcompact hpositive f hs ξ x =
      (f.scalar * traceRealMovingPhase (translationFrequency f ξ) 1) *
        (inputProfile f x * normalShape f.power (frequency f ξ) x) := by
  rfl

private theorem representative_value
    (window : Set ℝ) (hcompact : IsCompact window) (hpositive : window ⊆ Set.Ioi 0)
    (f : ProfileFormula) (hs : tsupport (inputProfile f) ⊆ window)
    (lower upper : ℝ) (lower_pos : 0 < lower)
    (horiginal : Function.support f.original ⊆ Set.Icc lower upper)
    (ξ : EngineParameter) (x : ℝ) :
    representative window hcompact hpositive f hs ξ x = f.value ξ x := by
  by_cases hx : 0 < x
  · rw [representative_apply, normalShape_value, ProfileFormula.value, if_pos hx]
    calc
      _ = f.scalar * inputProfile f x * ((x ^ f.power : ℝ) : ℂ) *
          (traceRealMovingPhase (frequency f ξ) (Real.log x) *
            traceRealMovingPhase (translationFrequency f ξ) 1) := by ring
      _ = _ := by rw [phase_product, inputProfile_apply]
  · have hzero : inputProfile f x = 0 := by
      by_contra hn
      have hloc := inputProfile_support f lower upper horiginal hn
      exact hx ((div_pos lower_pos f.dilation_pos).trans_le hloc.1)
    rw [representative_apply, hzero, zero_mul, mul_zero, ProfileFormula.value, if_neg hx]

private theorem representative_support
    (window : Set ℝ) (hcompact : IsCompact window) (hpositive : window ⊆ Set.Ioi 0)
    (f : ProfileFormula) (hs : tsupport (inputProfile f) ⊆ window)
    (lower upper : ℝ) (horiginal : Function.support f.original ⊆ Set.Icc lower upper)
    (ξ : EngineParameter) :
    Function.support (representative window hcompact hpositive f hs ξ) ⊆
      f.window lower upper := by
  intro x hx
  apply inputProfile_support f lower upper horiginal
  change inputProfile f x ≠ 0
  intro hzero
  apply hx
  rw [representative_apply, hzero, zero_mul, mul_zero]

private theorem frequency_bound (shape : ProfileShape) (f : ProfileFormula)
    (hf : f.Bounded shape) (ξ : EngineParameter) :
    1 + |frequency f ξ| ≤
      (1 + 2 * Real.pi * shape.phaseBound) *
        ((1 + ‖(WithLp.ofLp ξ).1‖) * (1 + ‖(WithLp.ofLp ξ).2‖)) := by
  have hphase : |ProfileFormula.linear f.phase ξ| ≤
      shape.phaseBound * (|(WithLp.ofLp ξ).1| + |(WithLp.ofLp ξ).2|) := by
    unfold ProfileFormula.linear
    calc
      _ ≤ |f.phase.1 * (WithLp.ofLp ξ).1| +
          |f.phase.2 * (WithLp.ofLp ξ).2| := abs_add_le _ _
      _ = |f.phase.1| * |(WithLp.ofLp ξ).1| +
          |f.phase.2| * |(WithLp.ofLp ξ).2| := by rw [abs_mul, abs_mul]
      _ ≤ shape.phaseBound * |(WithLp.ofLp ξ).1| +
          shape.phaseBound * |(WithLp.ofLp ξ).2| :=
        add_le_add (mul_le_mul_of_nonneg_right hf.phase_first (abs_nonneg _))
          (mul_le_mul_of_nonneg_right hf.phase_second (abs_nonneg _))
      _ = _ := by ring
  have hpi : 0 ≤ 2 * Real.pi := by positivity
  have hfreq : |frequency f ξ| ≤
      (2 * Real.pi * shape.phaseBound) *
        (|(WithLp.ofLp ξ).1| + |(WithLp.ofLp ξ).2|) := by
    calc
      |frequency f ξ| = (2 * Real.pi) * |ProfileFormula.linear f.phase ξ| := by
        rw [frequency, abs_mul, abs_of_nonneg hpi]
      _ ≤ (2 * Real.pi) *
          (shape.phaseBound * (|(WithLp.ofLp ξ).1| + |(WithLp.ofLp ξ).2|)) :=
        mul_le_mul_of_nonneg_left hphase hpi
      _ = _ := by ring
  have hB : 0 ≤ 2 * Real.pi * shape.phaseBound :=
    mul_nonneg hpi shape.phaseBound_nonneg
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  nlinarith [abs_nonneg (WithLp.ofLp ξ).1, abs_nonneg (WithLp.ofLp ξ).2,
    mul_nonneg (abs_nonneg (WithLp.ofLp ξ).1) (abs_nonneg (WithLp.ofLp ξ).2),
    mul_nonneg hB (mul_nonneg (abs_nonneg (WithLp.ofLp ξ).1)
      (abs_nonneg (WithLp.ofLp ξ).2))]

private theorem frequency_power_bound (shape : ProfileShape) (f : ProfileFormula)
    (hf : f.Bounded shape) (ξ : EngineParameter) (J : ℕ) :
    (1 + |frequency f ξ|) ^ J ≤
      (1 + 2 * Real.pi * shape.phaseBound) ^ J *
        ((1 + ‖(WithLp.ofLp ξ).1‖) ^ J * (1 + ‖(WithLp.ofLp ξ).2‖) ^ J) := by
  exact (pow_le_pow_left₀ (by positivity) (frequency_bound shape f hf ξ) J).trans_eq
    (by rw [mul_pow, mul_pow])

private theorem inputProfile_common_support (shape : ProfileShape) (f : ProfileFormula)
    (hf : f.Bounded shape) (lower upper : ℝ) (lower_pos : 0 < lower)
    (horiginal : Function.support f.original ⊆ Set.Icc lower upper) :
    tsupport (inputProfile f) ⊆
      Set.Icc (lower / shape.dilationUpper) (upper / shape.dilationLower) := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  have hloc := inputProfile_support f lower upper horiginal hx
  have hxpos : 0 < x := (div_pos lower_pos f.dilation_pos).trans_le hloc.1
  have hlower : lower ≤ x * f.dilation := (div_le_iff₀ f.dilation_pos).mp hloc.1
  have hupper : x * f.dilation ≤ upper := (le_div_iff₀ f.dilation_pos).mp hloc.2
  constructor
  · apply (div_le_iff₀ (shape.dilationLower_pos.trans_le shape.dilation_interval)).mpr
    exact hlower.trans (mul_le_mul_of_nonneg_left hf.dilation_upper hxpos.le)
  · apply (le_div_iff₀ shape.dilationLower_pos).mpr
    exact (mul_le_mul_of_nonneg_left hf.dilation_lower hxpos.le).trans hupper

/-- Uniform global Schwartz control of the prescribed profile formula. -/
theorem profile_formula_control : ProfileFormulaTask := by
  intro shape lower upper lower_pos interval orders
  let window : Set ℝ :=
    Set.Icc (lower / shape.dilationUpper) (upper / shape.dilationLower)
  have hcompact : IsCompact window := isCompact_Icc
  have hpositive : window ⊆ Set.Ioi 0 := by
    intro x hx
    exact (div_pos lower_pos
      (shape.dilationLower_pos.trans_le shape.dilation_interval)).trans_le hx.1
  obtain ⟨D, hD, hshape⟩ := shapeSchwartz_finset_bound_uniform
    window hcompact hpositive shape.powerBound shape.powerBound_nonneg orders
  obtain ⟨inputOrders, C, hC, hinput⟩ := inputProfile_finset_bound shape
    (Finset.Iic (orders.sup Prod.fst, orders.sup Prod.snd))
  let J := orders.sup Prod.snd
  let F := (1 + 2 * Real.pi * shape.phaseBound) ^ J
  have hF : 0 ≤ F := by
    dsimp only [F]
    exact pow_nonneg (add_nonneg zero_le_one
      (mul_nonneg (by positivity : 0 ≤ 2 * Real.pi) shape.phaseBound_nonneg)) J
  let coefficient := 1 + D * C * F
  have hcoefficient : 0 < coefficient := by dsimp [coefficient]; positivity
  refine ⟨{
    inputOrders := inputOrders
    degree := J
    coefficient := coefficient
    coefficient_pos := hcoefficient
    control := ?_ }⟩
  intro f hf horiginal amplitude scalarBound hamp hscalar hampBound hscalarBound
  have hs : tsupport (inputProfile f) ⊆ window :=
    inputProfile_common_support shape f hf lower upper lower_pos horiginal
  refine ⟨{
    representative := representative window hcompact hpositive f hs
    value_eq := representative_value window hcompact hpositive f hs
      lower upper lower_pos horiginal
    support := representative_support window hcompact hpositive f hs lower upper horiginal
    bound := ?_ }⟩
  intro ξ
  have hinputBound :
      (Finset.Iic (orders.sup Prod.fst, orders.sup Prod.snd)).sup
        (schwartzSeminormFamily ℂ ℝ ℂ) (inputProfile f) ≤ C * amplitude :=
    (hinput f hf).trans (mul_le_mul_of_nonneg_left hampBound hC)
  have hshapeBound := (hshape f.power hf.power (frequency f ξ) (inputProfile f) hs).trans
    (mul_le_mul_of_nonneg_left hinputBound
      (mul_nonneg hD (pow_nonneg (by positivity) J)))
  let P := (1 + ‖(WithLp.ofLp ξ).1‖) ^ J * (1 + ‖(WithLp.ofLp ξ).2‖) ^ J
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hfreq : (1 + |frequency f ξ|) ^ J ≤ F * P :=
    frequency_power_bound shape f hf ξ J
  have hproduct := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfreq hD)
      (mul_nonneg hC hamp)) hscalar
  have hcoeff : D * C * F ≤ coefficient := by dsimp [coefficient]; linarith
  calc
    orders.sup (schwartzSeminormFamily ℂ ℝ ℂ)
        (representative window hcompact hpositive f hs ξ) =
      ‖f.scalar‖ * orders.sup (schwartzSeminormFamily ℂ ℝ ℂ)
        (shapeSchwartz window hcompact hpositive f.power (frequency f ξ) (inputProfile f) hs) := by
      rw [representative, map_smul_eq_mul, norm_mul, norm_traceRealMovingPhase, mul_one]
    _ ≤ scalarBound * (D * (1 + |frequency f ξ|) ^ J * (C * amplitude)) :=
      mul_le_mul hscalarBound hshapeBound (apply_nonneg _ _) hscalar
    _ ≤ scalarBound * (D * (F * P) * (C * amplitude)) := hproduct
    _ = (D * C * F * amplitude * scalarBound) * P := by ring
    _ ≤ (coefficient * amplitude * scalarBound) * P :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoeff hamp) hscalar) hP
    _ ≤ 1 + (coefficient * amplitude * scalarBound) * P := by linarith
    _ = EngineStep.polynomialProfileRadius (coefficient * amplitude * scalarBound)
        J J (WithLp.ofLp ξ) := rfl

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks.profile_formula_control
