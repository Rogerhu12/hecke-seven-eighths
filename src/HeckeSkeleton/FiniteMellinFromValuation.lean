import HeckeGeneral.Analysis.GlobalThetaData
import Mathlib.Analysis.SpecificLimits.Normed

/-!
The `absolute_mellin` field follows from the two preceding valuation fields.
Only the actual cutoff and coefficient decay are hypotheses.  In particular,
there is no assumption about the Mellin sum or the final reflection bound.

This helper keeps the actual finite-place table fixed throughout.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeSkeleton.FiniteMellin

open NumberField IsDedekindDomain HeckeGeneral.ThetaSkeleton.Global
open scoped Classical

/-- A sequence with a lower valuation cutoff and decay arbitrarily close to
`q^(-k/3)` has an absolutely convergent Mellin series in `re(s) > -1/3`.
The negative half is finitely supported; the nonnegative half is bounded
by a geometric series with ratio `q^(-(δ + re(s))) < 1`. -/
theorem summable_mellin_of_valuation_cutoff_decay
    (q : ℕ) (hq : 1 < q) (a : ℤ → ℂ)
    (hcutoff : ∃ k₀ : ℤ, ∀ k, k < k₀ → a k = 0)
    (hdecay : ∀ δ : ℝ, δ < 1 / 3 → ∃ C : ℝ, 0 ≤ C ∧
      ∀ k : ℤ, 0 ≤ k → ‖a k‖ ≤ C * (q : ℝ) ^ (-(k : ℝ) * δ))
    (s : ℂ) (hs : -(1 / 3 : ℝ) < s.re) :
    Summable (fun k : ℤ => a k * (q : ℂ) ^ (-(k : ℂ) * s)) := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (lt_trans Nat.zero_lt_one hq)
  have hqone : (1 : ℝ) < q := by exact_mod_cast hq
  let δ : ℝ := (1 / 3 - s.re) / 2
  have hδ : δ < 1 / 3 := by dsimp [δ]; linarith
  have hδs : 0 < δ + s.re := by dsimp [δ]; linarith
  obtain ⟨C, hC, hbound⟩ := hdecay δ hδ
  have hgeom : Summable (fun n : ℕ => C * ((q : ℝ) ^ (-(δ + s.re))) ^ n) :=
    (summable_geometric_of_lt_one (Real.rpow_nonneg hqpos.le _)
      (Real.rpow_lt_one_of_one_lt_of_neg hqone (by linarith))).mul_left C
  apply summable_int_iff_summable_nat_and_neg.mpr
  constructor
  · apply hgeom.of_norm_bounded
    intro n
    have hre : (-(n : ℂ) * s).re = -(n : ℝ) * s.re := by simp
    have hn : ‖a (n : ℤ)‖ ≤ C * (q : ℝ) ^ (-(n : ℝ) * δ) := by
      simpa only [Int.cast_natCast] using hbound (n : ℤ) (by omega)
    calc
      ‖a (n : ℤ) * (q : ℂ) ^ (-((n : ℤ) : ℂ) * s)‖ =
          ‖a (n : ℤ)‖ * (q : ℝ) ^ (-(n : ℝ) * s.re) := by
        rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by omega)]
        simp only [Int.cast_natCast, hre]
      _ ≤ (C * (q : ℝ) ^ (-(n : ℝ) * δ)) *
          (q : ℝ) ^ (-(n : ℝ) * s.re) :=
        mul_le_mul_of_nonneg_right hn (Real.rpow_nonneg hqpos.le _)
      _ = C * ((q : ℝ) ^ (-(δ + s.re))) ^ n := by
        rw [mul_assoc, ← Real.rpow_add hqpos]
        rw [show -(n : ℝ) * δ + -(n : ℝ) * s.re =
          -(δ + s.re) * (n : ℝ) by ring]
        rw [Real.rpow_mul_natCast hqpos.le]
  · obtain ⟨k₀, hk₀⟩ := hcutoff
    obtain ⟨N, hN⟩ := exists_nat_gt (-k₀)
    apply summable_of_ne_finset_zero (s := Finset.range (N + 1))
    intro n hn
    have hNn : N + 1 ≤ n := by simpa only [Finset.mem_range, not_lt] using hn
    have hncut : -(n : ℤ) < k₀ := by omega
    simp only [hk₀ _ hncut, zero_mul]

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (F : FiniteMellinData K S)

/-- The exact finite-place Mellin target of `FiniteMellinAdmissible`, derived
from its cutoff and decay targets without choosing or changing the KP data. -/
theorem finite_absolute_mellin_of_valuation_cutoff_decay
    (hcutoff : ∃ k₀ : ℤ, ∀ u κ l p k, k < k₀ → F.coefficient u κ l p k = 0)
    (hdecay : ∀ δ : ℝ, δ < 1 / 3 → ∃ C : ℝ, 0 ≤ C ∧
      ∀ u κ l p k, 0 ≤ k →
        ‖F.coefficient u κ l p k‖ ≤ C *
          (p.val.asIdeal.absNorm : ℝ) ^ (-(k : ℝ) * δ)) :
    ∀ u κ l p s, -(1 / 3 : ℝ) < s.re →
      Summable (fun k : ℤ => F.coefficient u κ l p k *
        (p.val.asIdeal.absNorm : ℂ) ^ (-(k : ℂ) * s)) := by
  intro u κ l p s hs
  apply summable_mellin_of_valuation_cutoff_decay p.val.asIdeal.absNorm
    (NumberField.HeightOneSpectrum.one_lt_absNorm p.val)
    (F.coefficient u κ l p) ?_ ?_ s hs
  · obtain ⟨k₀, hk₀⟩ := hcutoff
    exact ⟨k₀, fun k hk => hk₀ u κ l p k hk⟩
  · intro δ hδ
    obtain ⟨C, hC, hbound⟩ := hdecay δ hδ
    exact ⟨C, hC, fun k hk => hbound u κ l p k hk⟩

/-- Once the two valuation inputs are established for the actual table,
there is no third independent finite-Mellin summability obligation. -/
theorem finiteMellinAdmissible_of_valuation_cutoff_decay
    (hcutoff : ∃ k₀ : ℤ, ∀ u κ l p k, k < k₀ → F.coefficient u κ l p k = 0)
    (hdecay : ∀ δ : ℝ, δ < 1 / 3 → ∃ C : ℝ, 0 ≤ C ∧
      ∀ u κ l p k, 0 ≤ k →
        ‖F.coefficient u κ l p k‖ ≤ C *
          (p.val.asIdeal.absNorm : ℝ) ^ (-(k : ℝ) * δ)) :
    FiniteMellinAdmissible K S F where
  valuation_cutoff := hcutoff
  valuation_decay := hdecay
  absolute_mellin := finite_absolute_mellin_of_valuation_cutoff_decay K S F hcutoff hdecay

end HeckeSkeleton.FiniteMellin

#print axioms HeckeSkeleton.FiniteMellin.finite_absolute_mellin_of_valuation_cutoff_decay
