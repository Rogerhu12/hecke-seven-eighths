import HeckeSkeleton.HighBinSupport.BoundaryBox
import Mathlib.Tactic.GCongr
/-!
External-height absorption and finite fixed-row summation. This module
keeps the derivative order outside the arithmetic mass: increasing the
profile seminorm order changes a constant, not a scale exponent.
-/

noncomputable section
namespace HighBinBoundary

open MeasureTheory Set Complex
open scoped BigOperators

/-- The entire s-shift has uniformly bounded width, and the w-line stays
inside the fixed gamma strip even at a=B=1. -/
theorem actual_contour_ranges {a B e : ℝ}
    (ha : 51 / 100 ≤ a) (haB : a ≤ B) (hB : B ≤ 1)
    (he : 0 ≤ e) (hesmall : e ≤ 1 / 10000) :
    a + 16 * e ≤ B + 20 * e ∧ B + 20 * e ≤ 2 ∧
      |(B + 20 * e) - (a + 16 * e)| < 1 / 2 ∧
      -(1 / 100 : ℝ) ≤ 1 - a - 6 * e ∧ 1 - a - 6 * e ≤ 1 / 2 := by
  have hnon : 0 ≤ (B + 20 * e) - (a + 16 * e) := by linarith
  rw [abs_of_nonneg hnon]
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- Two extra profile derivatives absorb the two-dimensional height box. -/
theorem height_volume_absorption (N : ℕ) {T H : ℝ}
    (hT : 1 ≤ T) (hTH : T ≤ H) :
    H ^ 2 / (1 + H) ^ (N + 2) ≤ T ^ (-(N : ℝ)) := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hH : 0 ≤ H := by linarith
  have hHpos : 0 < 1 + H := by linarith
  rw [Real.rpow_neg hTpos.le, Real.rpow_natCast, ← one_div]
  apply (div_le_div_iff₀ (pow_pos hHpos _) (pow_pos hTpos _)).mpr
  have h₁ : H ^ 2 ≤ (1 + H) ^ 2 :=
    pow_le_pow_left₀ hH (by linarith) 2
  have h₂ : T ^ N ≤ (1 + H) ^ N :=
    pow_le_pow_left₀ hTpos.le (by linarith) N
  calc
    H ^ 2 * T ^ N ≤ (1 + H) ^ 2 * (1 + H) ^ N :=
      mul_le_mul h₁ h₂ (pow_nonneg hTpos.le _) (pow_nonneg hHpos.le _)
    _ = 1 * (1 + H) ^ (N + 2) := by rw [pow_add]; ring

/-- A quantitative external T-tail for one original fixed row. -/
theorem coupled_box_external_tail
    (F : ℂ → ℝ × ℝ → ℂ) (g : ℝ → ℂ) (N : ℕ)
    (l r H T M D : ℝ) (hT : 1 ≤ T) (hTH : T ≤ H) (hM : 0 ≤ M)
    (hl : Integrable (fun p : ℝ × (ℝ × ℝ) => F ((l : ℂ) + p.1 * I) p.2)
      ((volume.restrict (Ioc (-H) H)).prod (twoHeightMeasure H)))
    (hr : Integrable (fun p : ℝ × (ℝ × ℝ) => F ((r : ℂ) + p.1 * I) p.2)
      ((volume.restrict (Ioc (-H) H)).prod (twoHeightMeasure H)))
    (hF : ∀ᵐ q ∂twoHeightMeasure H, DifferentiableOn ℂ (fun s => F s q)
      (uIcc l r ×ℂ uIcc (-H) H))
    (hg : ∀ y : ℝ, (1 + |y|) ^ (N + 2) * ‖g y‖ ≤ D)
    (hkernel : ∀ᵐ q ∂twoHeightMeasure H, ∀ σ ∈ uIcc l r, ∀ x : ℝ, |x| = H →
      ‖F ((σ : ℂ) + x * I) q‖ ≤
        M * (Real.exp (-((x + q.2) ^ 2)) * ‖g q.2‖)) :
    ‖parameterBox (twoHeightMeasure H) F r H -
      parameterBox (twoHeightMeasure H) F l H‖ ≤
        8 * M * gaussianMoment (N + 2) * D * |r - l| * T ^ (-(N : ℝ)) := by
  have hH : 0 ≤ H := by linarith
  have hD : 0 ≤ D := by
    have h := hg 0
    simp only [abs_zero, add_zero, one_pow, one_mul] at h
    exact (norm_nonneg _).trans h
  have hG : 0 ≤ gaussianMoment (N + 2) := (gaussianMoment_pos _).le
  apply (coupled_box_boundary_bound F g (N + 2) l r H M D hH hM hl hr hF hg hkernel).trans
  calc
    _ = (8 * M * gaussianMoment (N + 2) * D * |r - l|) *
        (H ^ 2 / (1 + H) ^ (N + 2)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (height_volume_absorption N hT hTH)
      (by positivity)

/-- Summing a fixed arithmetic family consumes only its preassigned mass.
The index set is fixed before any contour moves or amplitude subdivisions. -/
theorem fixed_family_external_tail {ι : Type*}
    (rows : Finset ι) (F : ι → ℂ → ℝ × ℝ → ℂ) (g : ι → ℝ → ℂ)
    (N : ℕ) (l r H M : ι → ℝ) (T D Q : ℝ) (hT : 1 ≤ T)
    (hM : ∀ u ∈ rows, 0 ≤ M u)
    (hTH : ∀ u ∈ rows, T ≤ H u)
    (hl : ∀ u ∈ rows,
      Integrable (fun p : ℝ × (ℝ × ℝ) => F u (((l u) : ℂ) + p.1 * I) p.2)
        ((volume.restrict (Ioc (-(H u)) (H u))).prod (twoHeightMeasure (H u))))
    (hr : ∀ u ∈ rows,
      Integrable (fun p : ℝ × (ℝ × ℝ) => F u (((r u) : ℂ) + p.1 * I) p.2)
        ((volume.restrict (Ioc (-(H u)) (H u))).prod (twoHeightMeasure (H u))))
    (hF : ∀ u ∈ rows, ∀ᵐ q ∂twoHeightMeasure (H u),
      DifferentiableOn ℂ (fun s => F u s q)
        (uIcc (l u) (r u) ×ℂ uIcc (-(H u)) (H u)))
    (hg : ∀ u ∈ rows, ∀ y : ℝ, (1 + |y|) ^ (N + 2) * ‖g u y‖ ≤ D)
    (hD : 0 ≤ D)
    (hkernel : ∀ u ∈ rows, ∀ᵐ q ∂twoHeightMeasure (H u),
      ∀ σ ∈ uIcc (l u) (r u), ∀ x : ℝ, |x| = H u →
        ‖F u ((σ : ℂ) + x * I) q‖ ≤
          M u * (Real.exp (-((x + q.2) ^ 2)) * ‖g u q.2‖))
    (hmass : (∑ u ∈ rows, M u * |r u - l u|) ≤ Q) :
    ‖∑ u ∈ rows,
      (parameterBox (twoHeightMeasure (H u)) (F u) (r u) (H u) -
       parameterBox (twoHeightMeasure (H u)) (F u) (l u) (H u))‖ ≤
      8 * gaussianMoment (N + 2) * D * Q * T ^ (-(N : ℝ)) := by
  classical
  have hG : 0 ≤ gaussianMoment (N + 2) := (gaussianMoment_pos _).le
  have hT0 : 0 ≤ T := zero_le_one.trans hT
  have hpiece (u : ι) (hu : u ∈ rows) := coupled_box_external_tail
    (F u) (g u) N (l u) (r u) (H u) T (M u) D hT (hTH u hu) (hM u hu)
    (hl u hu) (hr u hu) (hF u hu) (hg u hu) (hkernel u hu)
  calc
    _ ≤ ∑ u ∈ rows, ‖parameterBox (twoHeightMeasure (H u)) (F u) (r u) (H u) -
        parameterBox (twoHeightMeasure (H u)) (F u) (l u) (H u)‖ := norm_sum_le _ _
    _ ≤ ∑ u ∈ rows,
        8 * M u * gaussianMoment (N + 2) * D * |r u - l u| * T ^ (-(N : ℝ)) :=
      Finset.sum_le_sum hpiece
    _ = (8 * gaussianMoment (N + 2) * D * T ^ (-(N : ℝ))) *
        (∑ u ∈ rows, M u * |r u - l u|) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      ring
    _ ≤ (8 * gaussianMoment (N + 2) * D * T ^ (-(N : ℝ))) * Q :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = _ := by ring

#print axioms height_volume_absorption
#print axioms coupled_box_external_tail
#print axioms fixed_family_external_tail

end HighBinBoundary
