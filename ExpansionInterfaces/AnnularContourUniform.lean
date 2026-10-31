import ExpansionInterfaces.AnnularContourBound
import ExpansionInterfaces.AnnularMellinDecay

/-!
# One profile constant before every row and contour parameter

All Mellin-profile assumptions in the finite contour bound are discharged
from smooth annular support.  The remaining assumptions are the genuine
Dirichlet calibration and analytic L-function bounds on the chosen rectangle.
-/

noncomputable section
namespace ExpansionInterfaces.Mellin
open MeasureTheory Set
open scoped Classical BigOperators

namespace AnnularProfile

theorem uniform_contour_data (W : AnnularProfile) (lo hi : ℝ) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ ∈ Icc lo hi,
      (∫ t : ℝ, ‖mellin W.function (vertical σ t)‖) ≤ C ∧
      (∀ t : ℝ, (1 + |t|) ^ N * ‖mellin W.function (vertical σ t)‖ ≤ C) ∧
      ∀ H : ℝ, 0 < H →
        (∫ t : ℝ in {t | H < |t|}, ‖mellin W.function (vertical σ t)‖) ≤ C / H ^ N := by
  obtain ⟨C₀, hC₀, h₀⟩ := W.uniform_weighted_moment lo hi 0
  obtain ⟨Cd, hCd, hd⟩ := W.uniform_strip_decay lo hi N
  obtain ⟨Ct, hCt, ht⟩ := W.uniform_tail lo hi N
  refine ⟨max C₀ (max Cd Ct), hC₀.trans (le_max_left _ _), ?_⟩
  intro σ hσ
  refine ⟨?_, (fun t => (hd σ hσ t).trans ((le_max_left Cd Ct).trans (le_max_right _ _))), ?_⟩
  · have hh : (∫ t : ℝ, ‖mellin W.function (vertical σ t)‖) ≤ C₀ := by
      simpa only [pow_zero, one_mul] using (h₀ σ hσ).2
    exact hh.trans (le_max_left _ _)
  · intro H hH
    exact (ht σ hσ H hH).trans (div_le_div_of_nonneg_right
      ((le_max_right Cd Ct).trans (le_max_right _ _)) (pow_nonneg hH.le N))

def contourConstant (W : AnnularProfile) (lo hi : ℝ) (N : ℕ) : ℝ :=
  Classical.choose (W.uniform_contour_data lo hi N)

theorem contourConstant_spec (W : AnnularProfile) (lo hi : ℝ) (N : ℕ) :
    0 ≤ W.contourConstant lo hi N ∧ ∀ σ ∈ Icc lo hi,
      (∫ t : ℝ, ‖mellin W.function (vertical σ t)‖) ≤ W.contourConstant lo hi N ∧
      (∀ t : ℝ, (1 + |t|) ^ N * ‖mellin W.function (vertical σ t)‖ ≤ W.contourConstant lo hi N) ∧
      ∀ H : ℝ, 0 < H →
        (∫ t : ℝ in {t | H < |t|}, ‖mellin W.function (vertical σ t)‖) ≤
          W.contourConstant lo hi N / H ^ N :=
  Classical.choose_spec (W.uniform_contour_data lo hi N)

end AnnularProfile

/-- Sharp main term plus arbitrarily high finite-height decay.  The
constant is chosen from W, the fixed strip, and the requested tail order;
it is independent of coefficients, rows, L, X, s, and the height H. -/
theorem annular_polynomial_uniform_upper {ι : Type*} [Countable ι]
    (W : AnnularProfile) (lo hi : ℝ) (order : ℕ)
    (c : ι → ℂ) (norm : ι → ℝ) (hnorm : ∀ i, 0 < norm i)
    (L : ℂ → ℂ) (s : ℂ) {X a b H Mleft M : ℝ}
    (hX : 1 ≤ X) (hlo : lo ≤ a) (hab : a ≤ b) (hhi : b ≤ hi) (hH : 0 < H)
    (hMleft : 0 ≤ Mleft) (hM : 0 ≤ M)
    (hsum : Summable (fun i => ‖c i‖ * norm i ^ (-(s.re + b))))
    (hline : ∀ t, L (s + vertical b t) = dirichletSeries c norm (s + vertical b t))
    (hLdiff : DifferentiableOn ℂ (fun z => L (s + z)) (closedRectangle a b H))
    (hLrect : ∀ z ∈ closedRectangle a b H, ‖L (s + z)‖ ≤ M)
    (hLleft : ∀ t, |t| ≤ H → ‖L (s + vertical a t)‖ ≤ Mleft)
    (S : Finset ι) (hS : ∀ i, norm i ≤ W.upper * X → i ∈ S) :
    let C := W.contourConstant lo hi order
    let A := ∑' i, ‖c i‖ * norm i ^ (-(s.re + b))
    ‖∑ i ∈ S, smoothedTerm W c norm s X i‖ ≤ (1 / (2 * Real.pi)) *
      ((Mleft * X ^ a) * C +
        2 * (C / (1 + H) ^ order) * M * X ^ b * (b - a) +
          (A * X ^ b) * (C / H ^ order)) := by
  let C := W.contourConstant lo hi order
  let A := ∑' i, ‖c i‖ * norm i ^ (-(s.re + b))
  have hc := W.contourConstant_spec lo hi order
  have hC : 0 ≤ C := hc.1
  have hA : 0 ≤ A := tsum_nonneg (fun i =>
    mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (hnorm i).le _))
  have ha : a ∈ Icc lo hi := ⟨hlo, hab.trans hhi⟩
  have hb : b ∈ Icc lo hi := ⟨hlo.trans hab, hhi⟩
  have hpoint : ∀ x ∈ Icc a b, ∀ t : ℝ,
      ‖mellin W.function (vertical x t)‖ ≤ C / (1 + |t|) ^ order := by
    intro x hx t
    apply (le_div_iff₀ (pow_pos (by positivity : 0 < 1 + |t|) order)).mpr
    simpa only [mul_comm] using (hc.2 x ⟨hlo.trans hx.1, hx.2.trans hhi⟩).2.1 t
  have hWbot : ∀ x ∈ Icc a b,
      ‖mellin W.function (vertical x (-H))‖ ≤ C / (1 + H) ^ order := by
    intro x hx
    simpa only [abs_neg, abs_of_nonneg hH.le] using hpoint x hx (-H)
  have hWtop : ∀ x ∈ Icc a b,
      ‖mellin W.function (vertical x H)‖ ≤ C / (1 + H) ^ order := by
    intro x hx
    simpa only [abs_of_nonneg hH.le] using hpoint x hx H
  have hraw := annular_polynomial_upper_from_dirichlet_rectangle W c norm hnorm L s
    hX hab hH.le hMleft hM (div_nonneg hC (by positivity)) hsum hline hLdiff hLrect hLleft
    hWbot hWtop S hS
  have hfirst := mul_le_mul_of_nonneg_left (hc.2 a ha).1
    (mul_nonneg hMleft (Real.rpow_nonneg (zero_le_one.trans hX) a))
  have htail := mul_le_mul_of_nonneg_left ((hc.2 b hb).2.2 H hH)
    (mul_nonneg hA (Real.rpow_nonneg (zero_le_one.trans hX) b))
  apply hraw.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 1 / (2 * Real.pi))
  change (Mleft * X ^ a) * (∫ t : ℝ, ‖mellin W.function (vertical a t)‖) +
      2 * (C / (1 + H) ^ order) * M * X ^ b * (b - a) +
      (A * X ^ b) * (∫ t : ℝ in {t | H < |t|}, ‖mellin W.function (vertical b t)‖) ≤ _
  linarith

end ExpansionInterfaces.Mellin
