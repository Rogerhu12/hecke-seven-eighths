/-
Polynomial boundary bounds on a vertical strip with qualitative growth.

Adapted from Axiom DedekindZetaZeroFree snapshot
09afbb4ce6570c1615d58509dc197fc9f0956b7d:
Analysis/PhragmenLindelof/QuadraticGrowthStripBounds.lean and
Analysis/PhragmenLindelof/PolynomialBoundaryBounds.lean.
License: Apache-2.0; see sources/openai-math-LICENSE.txt.
Changes: merged the two source modules, adapted module/public syntax and
namespace, added an explicit tactic import, and enlarged the polynomial
wrapper's allowed delta from 1/10 to 1/4 (with the same constant).
Dependencies are Mathlib only.

The constants in qualitative growth can depend on the individual function.
The final bound depends only on the displayed common boundary constants.
No Hecke growth theorem or final high-bin estimate is postulated here.
-/
import Mathlib.Tactic
import Mathlib.Analysis.Complex.PhragmenLindelof



namespace HeckeSkeleton.HeckeStripPolynomial

open scoped Asymptotics Topology

theorem quadratic_exp_growth_isBigO_double_exp (a b : ℝ) (hab : a < b)
    (f : ℂ → ℂ)
    (hgrowth : ∃ M B : ℝ, 0 ≤ M ∧ 0 ≤ B ∧
      ∀ s : ℂ, a < s.re ∧ s.re < b →
        ‖f s‖ ≤ M * Real.exp (B * (1 + |s.im|) ^ 2)) :
    ∃ c : ℝ, c < Real.pi / (b - a) ∧ ∃ D : ℝ,
      f =O[Filter.comap (fun s : ℂ => |s.im|) Filter.atTop ⊓
        Filter.principal {s : ℂ | a < s.re ∧ s.re < b}]
        (fun s : ℂ => Real.exp (D * Real.exp (c * |s.im|))) := by
  obtain ⟨M, B, hM, hB, hg⟩ := hgrowth
  let c : ℝ := (Real.pi / (b - a)) / 2
  have hc : 0 < c := by dsimp [c]; positivity
  have hclt : c < Real.pi / (b - a) := by
    dsimp [c]
    linarith [div_pos Real.pi_pos (sub_pos.mpr hab)]
  let D : ℝ := (2 * B / c ^ 2) * Real.exp c
  have hpoly (t : ℝ) (ht : 0 ≤ t) :
      B * (1 + t) ^ 2 ≤ D * Real.exp (c * t) := by
    have hct : 0 ≤ c * (1 + t) := mul_nonneg hc.le (by linarith)
    have hquad := Real.quadratic_le_exp_of_nonneg hct
    have hsq : (1 + t) ^ 2 ≤ 2 * Real.exp (c * (1 + t)) / c ^ 2 := by
      apply (le_div_iff₀ (sq_pos_of_pos hc)).mpr
      nlinarith
    have hmul := mul_le_mul_of_nonneg_left hsq hB
    dsimp [D]
    calc
      B * (1 + t) ^ 2 ≤ B * (2 * Real.exp (c * (1 + t)) / c ^ 2) := hmul
      _ = (2 * B / c ^ 2 * Real.exp c) * Real.exp (c * t) := by
        rw [mul_add, mul_one, Real.exp_add]
        ring
  refine ⟨c, hclt, D, Asymptotics.IsBigO.of_bound M ?_⟩
  filter_upwards [Filter.eventually_inf_principal.mpr (Filter.Eventually.of_forall
    (fun s : ℂ => fun hs : a < s.re ∧ s.re < b => hs))] with s hs
  simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
    (hg s hs).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (hpoly |s.im| (abs_nonneg _))) hM)

theorem norm_le_on_closed_strip_of_quadratic_exp_growth (a b C : ℝ)
    (hab : a < b) (f : ℂ → ℂ)
    (hhol : DiffContOnCl ℂ f {s : ℂ | a < s.re ∧ s.re < b})
    (hgrowth : ∃ M B : ℝ, 0 ≤ M ∧ 0 ≤ B ∧
      ∀ s : ℂ, a < s.re ∧ s.re < b →
        ‖f s‖ ≤ M * Real.exp (B * (1 + |s.im|) ^ 2))
    (hleft : ∀ s : ℂ, s.re = a → ‖f s‖ ≤ C)
    (hright : ∀ s : ℂ, s.re = b → ‖f s‖ ≤ C) :
    ∀ s : ℂ, a ≤ s.re ∧ s.re ≤ b → ‖f s‖ ≤ C := by
  intro s hs
  exact PhragmenLindelof.vertical_strip hhol
    (quadratic_exp_growth_isBigO_double_exp a b hab f hgrowth)
    hleft hright hs.1 hs.2

end HeckeSkeleton.HeckeStripPolynomial




namespace HeckeSkeleton.HeckeStripPolynomial

theorem norm_le_on_closed_strip_of_polynomial_boundary
    (δ : ℝ) (hδpos : 0 < δ) (hδle : δ ≤ 1 / 4)
    (k : ℕ) (H : ℝ) (hH : 0 ≤ H) (f : ℂ → ℂ)
    (hhol : DiffContOnCl ℂ f {s : ℂ | -δ < s.re ∧ s.re < 1 + δ})
    (hgrowth : ∃ M B : ℝ, 0 ≤ M ∧ 0 ≤ B ∧
      ∀ s : ℂ, -δ < s.re ∧ s.re < 1 + δ →
        ‖f s‖ ≤ M * Real.exp (B * (1 + |s.im|) ^ 2))
    (hboundary : ∀ s : ℂ, (s.re = -δ ∨ s.re = 1 + δ) →
      ‖f s‖ ≤ H * (2 + |s.im|) ^ k) :
    ∀ s : ℂ, -δ ≤ s.re ∧ s.re ≤ 1 + δ →
      ‖f s‖ ≤ 6 ^ k * H * (2 + |s.im|) ^ k := by

  have hden : ∀ s : ℂ, -δ ≤ s.re → 1 ≤ ‖s + 2‖ := by
    intro s hs
    have h1 : (s + 2).re = s.re + 2 := by simp [Complex.add_re]
    have h2 : 1 ≤ (s + 2).re := by rw [h1]; linarith
    exact le_trans h2 (Complex.re_le_norm (s + 2))
  have hden_ne : ∀ s : ℂ, -δ ≤ s.re → (s + 2) ^ k ≠ 0 := by
    intro s hs
    refine pow_ne_zero k ?_
    exact norm_pos_iff.mp (lt_of_lt_of_le one_pos (hden s hs))
  have hcl : closure {s : ℂ | -δ < s.re ∧ s.re < 1 + δ} ⊆ {s : ℂ | -δ ≤ s.re} :=
    closure_minimal (fun s hs => le_of_lt hs.1) (isClosed_Ici.preimage Complex.continuous_re)
  set g : ℂ → ℂ := fun s => f s / (s + 2) ^ k with hgdef
  have hg_apply : ∀ s : ℂ, g s = f s / (s + 2) ^ k := fun s => by rw [hgdef]
  have hgdiff : DiffContOnCl ℂ g {s : ℂ | -δ < s.re ∧ s.re < 1 + δ} := by
    refine ⟨?_, ?_⟩
    · exact (hhol.1.div ((differentiableOn_id.add_const 2).pow k)
        (fun s hs => hden_ne s (le_of_lt hs.1)))
    · exact (hhol.2.div (((continuous_id.add continuous_const).pow k).continuousOn)
        (fun s hs => hden_ne s (hcl hs)))

  have hgrowth_g : ∃ M B : ℝ, 0 ≤ M ∧ 0 ≤ B ∧
      ∀ s : ℂ, -δ < s.re ∧ s.re < 1 + δ →
        ‖g s‖ ≤ M * Real.exp (B * (1 + |s.im|) ^ 2) := by
    obtain ⟨M, B, hM, hB, hgr⟩ := hgrowth
    refine ⟨M, B, hM, hB, ?_⟩
    intro s hs
    have hden1 : 1 ≤ ‖s + 2‖ := hden s (le_of_lt hs.1)
    have hdiv : ‖g s‖ ≤ ‖f s‖ := by
      rw [hg_apply, norm_div, norm_pow]
      exact div_le_self (norm_nonneg _) (one_le_pow₀ hden1)
    exact le_trans hdiv (hgr s hs)

  have hbound_g : ∀ s : ℂ, (s.re = -δ ∨ s.re = 1 + δ) → ‖g s‖ ≤ 3 ^ k * H := by
    intro s hs
    have hre : -δ ≤ s.re := by rcases hs with h | h <;> linarith
    have hden1 : 1 ≤ ‖s + 2‖ := hden s hre
    have him : |s.im| ≤ ‖s + 2‖ := by
      simpa using Complex.abs_im_le_norm (s + 2)
    have h3 : 2 + |s.im| ≤ 3 * ‖s + 2‖ := by
      have h2 : (2 : ℝ) ≤ 2 * ‖s + 2‖ := by linarith
      linarith [him, h2, norm_nonneg (s + 2)]
    have hfb := hboundary s hs
    have hpos : 0 < ‖s + 2‖ ^ k := pow_pos (lt_of_lt_of_le one_pos hden1) k
    rw [hg_apply, norm_div, norm_pow, div_le_iff₀ hpos]
    calc ‖f s‖ ≤ H * (2 + |s.im|) ^ k := hfb
      _ ≤ H * (3 * ‖s + 2‖) ^ k := by
          refine mul_le_mul_of_nonneg_left ?_ hH
          exact pow_le_pow_left₀ (by positivity) h3 k
      _ = 3 ^ k * H * ‖s + 2‖ ^ k := by rw [mul_pow]; ring
  have hab : -δ < 1 + δ := by linarith
  have hquad := norm_le_on_closed_strip_of_quadratic_exp_growth (-δ) (1 + δ) (3 ^ k * H)
    hab g hgdiff hgrowth_g
    (fun s hs => hbound_g s (Or.inl hs)) (fun s hs => hbound_g s (Or.inr hs))
  intro s hs
  have hgb : ‖g s‖ ≤ 3 ^ k * H := hquad s hs
  have hden1 : 1 ≤ ‖s + 2‖ := hden s hs.1
  have hnorm : ‖f s‖ = ‖g s‖ * ‖s + 2‖ ^ k := by
    have hne : (s + 2) ^ k ≠ 0 := hden_ne s hs.1
    have h2 : g s * (s + 2) ^ k = f s := by rw [hg_apply, div_mul_cancel₀ _ hne]
    calc ‖f s‖ = ‖g s * (s + 2) ^ k‖ := by rw [h2]
      _ = ‖g s‖ * ‖s + 2‖ ^ k := by rw [norm_mul, norm_pow]
  have h3 : ‖s + 2‖ ≤ 2 * (2 + |s.im|) := by
    have hnormle := Complex.norm_le_abs_re_add_abs_im (s + 2)
    have hre2 : (s + 2).re = s.re + 2 := by simp [Complex.add_re]
    have him2 : (s + 2).im = s.im := by simp [Complex.add_im]
    have hrepos : 0 ≤ s.re + 2 := by linarith [hs.1, hδpos]
    rw [hre2, him2, abs_of_nonneg hrepos] at hnormle
    have hle : s.re + 2 ≤ 3.25 := by linarith [hs.2, hδle]
    linarith [hnormle, hle, abs_nonneg s.im]
  calc ‖f s‖ = ‖g s‖ * ‖s + 2‖ ^ k := hnorm
    _ ≤ (3 ^ k * H) * (2 * (2 + |s.im|)) ^ k := by
        refine mul_le_mul hgb ?_ (by positivity) (by positivity)
        exact pow_le_pow_left₀ (norm_nonneg _) h3 k
    _ = 6 ^ k * H * (2 + |s.im|) ^ k := by
        have h36 : (3 : ℝ) ^ k * 2 ^ k = 6 ^ k := by rw [← mul_pow]; norm_num
        rw [mul_pow, ← h36]; ring

end HeckeSkeleton.HeckeStripPolynomial
