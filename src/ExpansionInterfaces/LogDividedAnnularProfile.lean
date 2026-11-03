import PrimeCancellationLogProfile
import ExpansionInterfaces.AnnularMellinDecay

/-!
# Uniform finite-contour data for logarithmically divided annular windows

The smoothing window is fixed before the prime scale. Its divided profiles
`W(y)/log(P*y)` have one Mellin constant for all `P ≥ exp(4)`, all real parts
in a fixed compact strip, and arbitrary requested tail order. The constants
are obtained from the proved compact profile family, with no choice of a
separate contour constant after P is known.
-/

set_option autoImplicit false
noncomputable section
namespace ExpansionInterfaces.Mellin

open MeasureTheory Set
open scoped Classical BigOperators ContDiff

/-- The exact inverse-log window, with its actual smoothness and annular support. -/
def logDividedAnnularProfile (W : ℝ → ℂ) (hW : ContDiff ℝ ∞ W)
    (hs : Function.support W ⊆ Icc (1 : ℝ) 2) (P : ℝ) (hP : 2 ≤ P) :
    AnnularProfile where
  function := PrimeCancellationLogWindow.logWindow P W
  lower := 1
  upper := 2
  lower_pos := by norm_num
  lower_le_upper := by norm_num
  smooth := PrimeCancellationLogWindow.contDiff_logWindow hP hW hs
  supported := PrimeCancellationLogWindow.support_logWindow_subset_Icc P W hs

theorem two_le_exp_four : (2 : ℝ) ≤ Real.exp 4 := by
  have h := Real.add_one_le_exp (4 : ℝ)
  linarith

/-- The compact auxiliary family is the literal log-divided window at its
actual parameter `1/log(P)`, uniformly above the same explicit threshold. -/
theorem profile_eq_logDivided (W : ℝ → ℂ)
    (hs : Function.support W ⊆ Icc (1 : ℝ) 2)
    {P : ℝ} (hP : Real.exp 4 ≤ P) :
    PrimeCancellationLogProfile.profile W (1 / Real.log P) =
      PrimeCancellationLogWindow.logWindow P W := by
  have hPpos : 0 < P := (Real.exp_pos 4).trans_le hP
  have hlog : 4 ≤ Real.log P := by
    have h := Real.log_le_log (Real.exp_pos 4) hP
    simpa only [Real.log_exp] using h
  have hlog2nonneg : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hlog2le : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hlarge : 2 * (|Real.log (1 : ℝ)| + |Real.log (2 : ℝ)|) + 1 ≤
      Real.log P := by
    rw [Real.log_one, abs_zero, zero_add, abs_of_nonneg hlog2nonneg]
    linarith
  exact PrimeCancellationLogProfile.profile_eq_log_division W 1 2 P
    (by norm_num) hs hPpos hlarge

/-- Arbitrary-order pointwise Mellin decay, with its constant before P. -/
theorem uniform_logDivided_strip_decay (W : ℝ → ℂ) (hW : ContDiff ℝ ∞ W)
    (hs : Function.support W ⊆ Icc (1 : ℝ) 2) (lo hi : ℝ) (J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ P : ℝ, Real.exp 4 ≤ P → ∀ σ ∈ Icc lo hi, ∀ t : ℝ,
      (1 + |t|) ^ J *
        ‖mellin (PrimeCancellationLogWindow.logWindow P W) (vertical σ t)‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := PrimeCancellationLogProfile.uniform_mellin_decay
    W 1 2 (by norm_num) hs hW lo hi J
  refine ⟨C, hC.le, ?_⟩
  intro P hP σ hσ t
  have hlog : 4 ≤ Real.log P := by
    have h := Real.log_le_log (Real.exp_pos 4) hP
    simpa only [Real.log_exp] using h
  have hlogpos : 0 < Real.log P := by linarith
  have hA : (1 / Real.log P : ℝ) ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact (one_div_pos.mpr hlogpos).le
    · exact (div_le_one₀ hlogpos).mpr (by linarith)
  have h := hb (1 / Real.log P) hA σ hσ t
  rw [profile_eq_logDivided W hs hP] at h
  exact h

/-- Uniform integrable moments of the same exact divided profiles. -/
theorem uniform_logDivided_weighted_moment (W : ℝ → ℂ) (hW : ContDiff ℝ ∞ W)
    (hs : Function.support W ⊆ Icc (1 : ℝ) 2) (lo hi : ℝ) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ P : ℝ, Real.exp 4 ≤ P → ∀ σ ∈ Icc lo hi,
      Integrable (fun t : ℝ => |t| ^ N *
        ‖mellin (PrimeCancellationLogWindow.logWindow P W) (vertical σ t)‖) ∧
      (∫ t : ℝ, |t| ^ N *
        ‖mellin (PrimeCancellationLogWindow.logWindow P W) (vertical σ t)‖) ≤ C := by
  obtain ⟨C, hC, hb⟩ := uniform_logDivided_strip_decay W hW hs lo hi (N + 2)
  let I : ℝ := ∫ t : ℝ, (1 + |t|) ^ (-2 : ℝ)
  have hI : 0 ≤ I := integral_nonneg fun t => Real.rpow_nonneg (by positivity) _
  refine ⟨C * I, mul_nonneg hC hI, ?_⟩
  intro P hP σ hσ
  let V := logDividedAnnularProfile W hW hs P (two_le_exp_four.trans hP)
  have hpoint (t : ℝ) : |t| ^ N *
      ‖mellin (PrimeCancellationLogWindow.logWindow P W) (vertical σ t)‖ ≤
      C * (1 + |t|) ^ (-2 : ℝ) :=
    AnnularProfile.weighted_le_of_decay (norm_nonneg _) N (hb P hP σ hσ t)
  have hcont : Continuous (fun t : ℝ => |t| ^ N *
      ‖mellin (PrimeCancellationLogWindow.logWindow P W) (vertical σ t)‖) :=
    (continuous_abs.pow N).mul
      (V.mellin_differentiable.continuous.comp (by unfold vertical; fun_prop)).norm
  have hm := AnnularProfile.decayWeight_integrable.const_mul C
  have hi : Integrable (fun t : ℝ => |t| ^ N *
      ‖mellin (PrimeCancellationLogWindow.logWindow P W) (vertical σ t)‖) := by
    apply hm.mono' hcont.aestronglyMeasurable
    filter_upwards [] with t
    simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ |t| ^ N *
        ‖mellin (PrimeCancellationLogWindow.logWindow P W) (vertical σ t)‖)] using hpoint t
  refine ⟨hi, ?_⟩
  have hh := integral_mono hi hm hpoint
  simpa only [integral_const_mul, I] using hh

/-- Every finite-height tail has a uniform arbitrary polynomial order. -/
theorem uniform_logDivided_tail (W : ℝ → ℂ) (hW : ContDiff ℝ ∞ W)
    (hs : Function.support W ⊆ Icc (1 : ℝ) 2) (lo hi : ℝ) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ P : ℝ, Real.exp 4 ≤ P → ∀ σ ∈ Icc lo hi,
      ∀ H : ℝ, 0 < H →
        (∫ t : ℝ in {t | H < |t|},
          ‖mellin (PrimeCancellationLogWindow.logWindow P W) (vertical σ t)‖) ≤ C / H ^ N := by
  obtain ⟨C, hC, hb⟩ := uniform_logDivided_weighted_moment W hW hs lo hi N
  refine ⟨C, hC, ?_⟩
  intro P hP σ hσ H hH
  let V := logDividedAnnularProfile W hW hs P (two_le_exp_four.trans hP)
  have hm : MeasurableSet {t : ℝ | H < |t|} :=
    measurableSet_lt measurable_const continuous_abs.measurable
  apply (le_div_iff₀ (pow_pos hH N)).mpr
  calc
    _ = ∫ t : ℝ in {t | H < |t|}, H ^ N *
        ‖mellin (PrimeCancellationLogWindow.logWindow P W) (vertical σ t)‖ := by
      rw [integral_const_mul]
      ring
    _ ≤ ∫ t : ℝ in {t | H < |t|}, |t| ^ N *
        ‖mellin (PrimeCancellationLogWindow.logWindow P W) (vertical σ t)‖ :=
      setIntegral_mono_on ((V.vertical_norm_integrable σ).const_mul (H ^ N)).integrableOn
        (hb P hP σ hσ).1.integrableOn hm (fun t ht =>
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hH.le ht.le N) (norm_nonneg _))
    _ ≤ ∫ t : ℝ, |t| ^ N *
        ‖mellin (PrimeCancellationLogWindow.logWindow P W) (vertical σ t)‖ :=
      setIntegral_le_integral (hb P hP σ hσ).1 (ae_of_all _ fun t => by positivity)
    _ ≤ C := (hb P hP σ hσ).2

/-- The same constant controls the main Mellin integral, both horizontal
faces and the complementary initial tail. P, H and the vertical line are
all chosen after this constant and the explicit scale threshold. -/
theorem exists_uniform_logDivided_contour_data (W : ℝ → ℂ)
    (hW : ContDiff ℝ ∞ W) (hs : Function.support W ⊆ Icc (1 : ℝ) 2)
    (lo hi : ℝ) (order : ℕ) :
    ∃ P₀ C : ℝ, 2 ≤ P₀ ∧ 0 ≤ C ∧ ∀ P : ℝ, P₀ ≤ P → ∀ σ ∈ Icc lo hi,
      (∫ t : ℝ, ‖mellin (PrimeCancellationLogWindow.logWindow P W) (vertical σ t)‖) ≤ C ∧
      (∀ t : ℝ, (1 + |t|) ^ order *
        ‖mellin (PrimeCancellationLogWindow.logWindow P W) (vertical σ t)‖ ≤ C) ∧
      ∀ H : ℝ, 0 < H →
        (∫ t : ℝ in {t | H < |t|},
          ‖mellin (PrimeCancellationLogWindow.logWindow P W) (vertical σ t)‖) ≤ C / H ^ order := by
  obtain ⟨C₀, hC₀, h₀⟩ := uniform_logDivided_weighted_moment W hW hs lo hi 0
  obtain ⟨Cd, hCd, hd⟩ := uniform_logDivided_strip_decay W hW hs lo hi order
  obtain ⟨Ct, hCt, ht⟩ := uniform_logDivided_tail W hW hs lo hi order
  refine ⟨Real.exp 4, max C₀ (max Cd Ct), two_le_exp_four,
    hC₀.trans (le_max_left _ _), ?_⟩
  intro P hP σ hσ
  refine ⟨?_, (fun t => (hd P hP σ hσ t).trans
    ((le_max_left Cd Ct).trans (le_max_right _ _))), ?_⟩
  · have hh : (∫ t : ℝ,
        ‖mellin (PrimeCancellationLogWindow.logWindow P W) (vertical σ t)‖) ≤ C₀ := by
      simpa only [pow_zero, one_mul] using (h₀ P hP σ hσ).2
    exact hh.trans (le_max_left _ _)
  · intro H hH
    exact (ht P hP σ hσ H hH).trans (div_le_div_of_nonneg_right
      ((le_max_right Cd Ct).trans (le_max_right _ _)) (pow_nonneg hH.le order))

end ExpansionInterfaces.Mellin

#print axioms ExpansionInterfaces.Mellin.uniform_logDivided_strip_decay
#print axioms ExpansionInterfaces.Mellin.uniform_logDivided_weighted_moment
#print axioms ExpansionInterfaces.Mellin.uniform_logDivided_tail
#print axioms ExpansionInterfaces.Mellin.exists_uniform_logDivided_contour_data
