import Mathlib.Analysis.Complex.Liouville
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
/-! A Cauchy estimate deriving a logarithmic-derivative bound from separate
function and reciprocal bounds. No logarithmic-derivative estimate is assumed. -/

noncomputable section
namespace HighBinVerified.NormForm

theorem logDerivative_norm_le_of_disc (f : ℂ → ℂ) (s : ℂ) (e M : ℝ)
    (he : 0 < e) (hf : DiffContOnCl ℂ f (Metric.ball s e))
    (hbound : ∀ z ∈ Metric.closedBall s e, ‖f z‖ + ‖(f z)⁻¹‖ ≤ M) :
    ‖deriv f s / f s‖ ≤ M ^ 2 / e := by
  have hd : ‖deriv f s‖ ≤ M / e :=
    Complex.norm_deriv_le_of_forall_mem_sphere_norm_le he hf (by
      intro z hz
      exact (le_add_of_nonneg_right (norm_nonneg ((f z)⁻¹))).trans
        (hbound z (Metric.mem_closedBall.mpr (Metric.mem_sphere.mp hz).le)))
  have hi : ‖(f s)⁻¹‖ ≤ M := by
    exact (le_add_of_nonneg_left (norm_nonneg (f s))).trans
      (hbound s (Metric.mem_closedBall.mpr (by simpa only [dist_self] using he.le)))
  rw [norm_div, div_eq_mul_inv, ← norm_inv]
  calc
    _ ≤ (M / e) * M :=
      mul_le_mul hd hi (norm_nonneg _) ((norm_nonneg _).trans hd)
    _ = M ^ 2 / e := by ring

/-- The complete closed Cauchy disc fits inside the strip used by actual
buffered control, including its enlarged imaginary-height window. -/
theorem closedBall_inside_buffered_strip (a H e : ℝ) (s z : ℂ)
    (he : 0 ≤ e) (hehalf : e ≤ 1 / 2)
    (hslo : a + 8 * e ≤ s.re) (hshi : s.re ≤ 3 / 2)
    (hheight : |s.im| ≤ H) (hz : z ∈ Metric.closedBall s e) :
    a + 6 * e ≤ z.re ∧ z.re ≤ 2 ∧ |z.im| ≤ H + e := by
  have hdist : ‖z - s‖ ≤ e := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
  have hre : |z.re - s.re| ≤ e := by
    simpa only [Complex.sub_re] using (Complex.abs_re_le_norm (z - s)).trans hdist
  have him : |z.im - s.im| ≤ e := by
    simpa only [Complex.sub_im] using (Complex.abs_im_le_norm (z - s)).trans hdist
  obtain ⟨hrlo, hrhi⟩ := abs_le.mp hre
  obtain ⟨hilo, hihi⟩ := abs_le.mp him
  obtain ⟨hsilo, hsihi⟩ := abs_le.mp hheight
  exact ⟨by linarith, by linarith, abs_le.mpr ⟨by linarith, by linarith⟩⟩

end HighBinVerified.NormForm

#print axioms HighBinVerified.NormForm.logDerivative_norm_le_of_disc
#print axioms HighBinVerified.NormForm.closedBall_inside_buffered_strip
