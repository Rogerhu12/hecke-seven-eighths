import HeckeGeneral.Analysis.IdealDyadicMobius

/-!
An analytic consumer of a precise compact-uniform estimate for the actual
finite Moebius--Hecke dyadic shells. Holomorphy and zero-freeness are not
assumptions. Deriving this estimate from theta/moment inputs is NOT done here.
In particular a separate pointwise BigO for each s does not supply this input.
-/

noncomputable section
namespace HeckeGeneral.Analysis.IdealDyadicMobius

open NumberField IsDedekindDomain HeckeGeneral.Characters
open scoped Topology

variable (K : Type) [Field K] [NumberField K]

/-- The constant is uniform in BOTH s in a compact set and all dyadic scales.
The tested function is the actual finite shell, with its N(I)^(-s) factor.
The exponent makes the numerical analytic-continuation obligation explicit.
This is a number-theoretic estimate to prove, not a holomorphy assumption. -/
def CompactShellGrowth (χ : HeckeCharacter K)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (b : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ Q : Set ℂ, IsCompact Q → Q ⊆ rightHalfPlane b →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : ℕ) (s : ℂ), s ∈ Q →
      ‖shell K χ S j s‖ ≤ C * ((2 : ℝ) ^ j) ^ (b + ε - s.re)

theorem re_lower_of_mem_closedBall {s w : ℂ} {r : ℝ}
    (hw : w ∈ Metric.closedBall s r) : s.re - r ≤ w.re := by
  have hn : ‖w - s‖ ≤ r := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hw
  have hr := (abs_le.mp ((Complex.abs_re_le_norm (w - s)).trans hn)).1
  simp only [Complex.sub_re] at hr
  linarith

theorem analyticAt_dyadicTotal_of_compact_growth (χ : HeckeCharacter K)
    (S : Finset (HeightOneSpectrum (𝓞 K))) {b : ℝ}
    (hG : CompactShellGrowth K χ S b) {s : ℂ} (hs : b < s.re) :
    AnalyticAt ℂ (dyadicTotal K χ S) s := by
  let ε : ℝ := (s.re - b) / 4
  let δ : ℝ := (s.re - b) / 2
  let q : ℝ := (2 : ℝ) ^ (-δ)
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hQ : Metric.closedBall s ε ⊆ rightHalfPlane b := by
    intro w hw
    have hr := re_lower_of_mem_closedBall hw
    change b < w.re
    dsimp [ε] at hr
    linarith
  obtain ⟨C, hC, hbound⟩ := hG ε hε (Metric.closedBall s ε)
    (isCompact_closedBall s ε) hQ
  have hq0 : 0 ≤ q := Real.rpow_nonneg (by norm_num) _
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg
    (by norm_num : (1 : ℝ) < 2) (neg_neg_of_pos hδ)
  have hsum : Summable (fun j : ℕ => C * q ^ j) :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left C
  have hdiff : DifferentiableOn ℂ (dyadicTotal K χ S) (Metric.ball s ε) := by
    change DifferentiableOn ℂ (fun w => ∑' j : ℕ, shell K χ S j w) (Metric.ball s ε)
    apply Complex.differentiableOn_tsum_of_summable_norm hsum
      (fun j => (differentiable_shell K χ S j).differentiableOn) Metric.isOpen_ball
    intro j w hw
    have hwQ : w ∈ Metric.closedBall s ε := Metric.ball_subset_closedBall hw
    have hr := re_lower_of_mem_closedBall hwQ
    have hexp : b + ε - w.re ≤ -δ := by dsimp [ε, δ] at *; linarith
    have hbase : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
    calc
      ‖shell K χ S j w‖ ≤ C * ((2 : ℝ) ^ j) ^ (b + ε - w.re) := hbound j w hwQ
      _ ≤ C * ((2 : ℝ) ^ j) ^ (-δ) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hbase hexp) hC
      _ = C * q ^ j := by dsimp [q]; rw [Real.rpow_pow_comm (by norm_num)]
  exact hdiff.analyticAt (Metric.ball_mem_nhds s hε)

theorem analyticOnNhd_dyadicTotal_of_compact_growth (χ : HeckeCharacter K)
    (S : Finset (HeightOneSpectrum (𝓞 K))) {b : ℝ}
    (hG : CompactShellGrowth K χ S b) :
    AnalyticOnNhd ℂ (dyadicTotal K χ S) (rightHalfPlane b) := by
  intro s hs
  exact analyticAt_dyadicTotal_of_compact_growth K χ S hG hs

/-- A genuine analytic reciprocal extension to Re(s)>11/12, conditional
only on the displayed actual-shell estimate. Its initial identity is proved. -/
theorem reciprocal_extension_eleven_twelfths (χ : HeckeCharacter K)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hG : CompactShellGrowth K χ S (11 / 12)) :
    AnalyticOnNhd ℂ (dyadicTotal K χ S) (rightHalfPlane (11 / 12)) ∧
      ∀ s : ℂ, 1 < s.re →
        dyadicTotal K χ S s = (heckeDeletedContinuation K χ S s)⁻¹ := by
  exact ⟨analyticOnNhd_dyadicTotal_of_compact_growth K χ S hG,
    fun _ hs => dyadicTotal_eq_reciprocal K χ S hs⟩

end HeckeGeneral.Analysis.IdealDyadicMobius
