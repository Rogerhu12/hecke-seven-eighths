import ExpansionInterfaces.AnnularContourBound

/-!
# Finite contour bound from one uniform family constant

The constant is supplied once for a profile family, rather than chosen
separately for each member. This keeps scale-dependent logarithmic division
profiles compatible with constants chosen before the scale.
-/

noncomputable section
namespace ExpansionInterfaces.Mellin
open MeasureTheory Set
open scoped Classical BigOperators

theorem annular_polynomial_upper_with_contour_data {ι : Type*} [Countable ι]
    (W : AnnularProfile) (lo hi : ℝ) (order : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hc : ∀ σ ∈ Icc lo hi,
      (∫ t : ℝ, ‖mellin W.function (vertical σ t)‖) ≤ C ∧
      (∀ t : ℝ, (1 + |t|) ^ order * ‖mellin W.function (vertical σ t)‖ ≤ C) ∧
      ∀ H : ℝ, 0 < H →
        (∫ t : ℝ in {t | H < |t|}, ‖mellin W.function (vertical σ t)‖) ≤ C / H ^ order)
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
    let A := ∑' i, ‖c i‖ * norm i ^ (-(s.re + b))
    ‖∑ i ∈ S, smoothedTerm W c norm s X i‖ ≤ (1 / (2 * Real.pi)) *
      ((Mleft * X ^ a) * C +
        2 * (C / (1 + H) ^ order) * M * X ^ b * (b - a) +
          (A * X ^ b) * (C / H ^ order)) := by
  let A := ∑' i, ‖c i‖ * norm i ^ (-(s.re + b))
  have hA : 0 ≤ A := tsum_nonneg (fun i =>
    mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (hnorm i).le _))
  have ha : a ∈ Icc lo hi := ⟨hlo, hab.trans hhi⟩
  have hb : b ∈ Icc lo hi := ⟨hlo.trans hab, hhi⟩
  have hpoint : ∀ x ∈ Icc a b, ∀ t : ℝ,
      ‖mellin W.function (vertical x t)‖ ≤ C / (1 + |t|) ^ order := by
    intro x hx t
    apply (le_div_iff₀ (pow_pos (by positivity : 0 < 1 + |t|) order)).mpr
    simpa only [mul_comm] using (hc x ⟨hlo.trans hx.1, hx.2.trans hhi⟩).2.1 t
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
  have hfirst := mul_le_mul_of_nonneg_left (hc a ha).1
    (mul_nonneg hMleft (Real.rpow_nonneg (zero_le_one.trans hX) a))
  have htail := mul_le_mul_of_nonneg_left ((hc b hb).2.2 H hH)
    (mul_nonneg hA (Real.rpow_nonneg (zero_le_one.trans hX) b))
  apply hraw.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 1 / (2 * Real.pi))
  change (Mleft * X ^ a) * (∫ t : ℝ, ‖mellin W.function (vertical a t)‖) +
      2 * (C / (1 + H) ^ order) * M * X ^ b * (b - a) +
      (A * X ^ b) * (∫ t : ℝ in {t | H < |t|}, ‖mellin W.function (vertical b t)‖) ≤ _
  linarith


end ExpansionInterfaces.Mellin

#print axioms ExpansionInterfaces.Mellin.annular_polynomial_upper_with_contour_data
