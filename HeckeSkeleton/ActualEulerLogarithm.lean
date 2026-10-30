import HeckeGeneral.Analysis.HeckeContinuation
import HeckeGeneral.Analysis.IdealEulerIdentity
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Tactic

/-!
Actual Euler logarithms for arbitrary continuous unitary Hecke characters.

The local logarithm bounds and locally uniform convergence proof adapt
DedekindZetaZeroFree/LFunctions/Hecke/EulerLogarithm.lean from Axiom snapshot
09afbb4ce6570c1615d58509dc197fc9f0956b7d. License: Apache-2.0; see
sources/openai-math-LICENSE.txt. Changes: use this project's actual prime
coefficients, prime-ideal indices and unconditional Euler-product identity;
the actual character is unrestricted by finite-order or conductor hypotheses.

This constructs a bounded logarithm on Re(s)>1. It makes no assertion about
polynomial strip growth or a zero-free continuation to the left of one.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.ActualEulerLogarithm

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open Set
open scoped Classical Topology

variable (K : Type) [Field K] [NumberField K]

private theorem primeRatio_bound (a : HeightOneSpectrum (𝓞 K) → ℂ)
    (ha : ∀ p, ‖a p‖ ≤ 1) (σ : ℝ) (hσ : 1 < σ)
    (s : ℂ) (hs : σ ≤ s.re) (p : HeightOneSpectrum (𝓞 K)) :
    ‖primeIdealRatio K a s p‖ ≤ idealNorm K (primeNonzeroIdeal K p) ^ (-σ) ∧
      idealNorm K (primeNonzeroIdeal K p) ^ (-σ) ≤ 1 / 2 := by
  have hq : (2 : ℝ) ≤ idealNorm K (primeNonzeroIdeal K p) := by
    have hn : 2 ≤ p.asIdeal.absNorm := one_lt_primeIdeal_absNorm K p
    change (2 : ℝ) ≤ (p.asIdeal.absNorm : ℝ)
    exact_mod_cast hn
  have hq0 : 0 < idealNorm K (primeNonzeroIdeal K p) := by linarith
  have hq1 : 1 ≤ idealNorm K (primeNonzeroIdeal K p) := by linarith
  constructor
  · unfold primeIdealRatio
    rw [norm_mul]
    have hc : (p.asIdeal.absNorm : ℂ) =
        (idealNorm K (primeNonzeroIdeal K p) : ℂ) := by
      simp [idealNorm, primeNonzeroIdeal]
    rw [hc, Complex.norm_cpow_eq_rpow_re_of_pos hq0, Complex.neg_re]
    calc
      ‖a p‖ * idealNorm K (primeNonzeroIdeal K p) ^ (-s.re) ≤
          1 * idealNorm K (primeNonzeroIdeal K p) ^ (-s.re) :=
        mul_le_mul_of_nonneg_right (ha p) (Real.rpow_nonneg hq0.le _)
      _ ≤ idealNorm K (primeNonzeroIdeal K p) ^ (-σ) := by
        simpa only [one_mul] using
          Real.rpow_le_rpow_of_exponent_le hq1 (neg_le_neg hs)
  · calc
      idealNorm K (primeNonzeroIdeal K p) ^ (-σ) ≤
          idealNorm K (primeNonzeroIdeal K p) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
      _ = (idealNorm K (primeNonzeroIdeal K p))⁻¹ := Real.rpow_neg_one _
      _ ≤ 1 / 2 := by
        simpa only [one_div] using inv_anti₀ (by norm_num : (0 : ℝ) < 2) hq

private theorem primeLog_bound (a : HeightOneSpectrum (𝓞 K) → ℂ)
    (ha : ∀ p, ‖a p‖ ≤ 1) (σ : ℝ) (hσ : 1 < σ)
    (s : ℂ) (hs : σ ≤ s.re) (p : HeightOneSpectrum (𝓞 K)) :
    ‖-Complex.log (1 - primeIdealRatio K a s p)‖ ≤
      (3 / 2 : ℝ) * idealNorm K (primeNonzeroIdeal K p) ^ (-σ) := by
  have h := primeRatio_bound K a ha σ hσ s hs p
  rw [norm_neg]
  have hb := Complex.norm_log_one_add_half_le_self
    (z := -primeIdealRatio K a s p) (by simpa only [norm_neg] using h.1.trans h.2)
  simp only [norm_neg, ← sub_eq_add_neg] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left h.1 (by norm_num))

private theorem primeMajorant_summable (σ : ℝ) (hσ : 1 < σ) :
    Summable (fun p : HeightOneSpectrum (𝓞 K) =>
      (3 / 2 : ℝ) * idealNorm K (primeNonzeroIdeal K p) ^ (-σ)) :=
  ((summable_nonzeroIdeal_norm_rpow K hσ).comp_injective
    (primeNonzeroIdeal_injective K)).mul_left _

private theorem primeLog_summable_norm (a : HeightOneSpectrum (𝓞 K) → ℂ)
    (ha : ∀ p, ‖a p‖ ≤ 1) (σ : ℝ) (hσ : 1 < σ)
    (s : ℂ) (hs : σ ≤ s.re) :
    Summable (fun p : HeightOneSpectrum (𝓞 K) =>
      ‖-Complex.log (1 - primeIdealRatio K a s p)‖) :=
  (primeMajorant_summable K σ hσ).of_nonneg_of_le
    (fun _ => norm_nonneg _) (primeLog_bound K a ha σ hσ s hs)

private theorem primeRatio_differentiable (a : HeightOneSpectrum (𝓞 K) → ℂ)
    (p : HeightOneSpectrum (𝓞 K)) :
    Differentiable ℂ (fun s => primeIdealRatio K a s p) := by
  have hn : (p.asIdeal.absNorm : ℂ) ≠ 0 := by
    exact_mod_cast (lt_trans Nat.zero_lt_one (one_lt_primeIdeal_absNorm K p)).ne'
  exact ((differentiable_id (𝕜 := ℂ)).neg.const_cpow (Or.inl hn)).const_mul (a p)

private theorem primeLog_differentiable (a : HeightOneSpectrum (𝓞 K) → ℂ)
    (ha : ∀ p, ‖a p‖ ≤ 1) (σ : ℝ) (hσ : 1 < σ)
    (p : HeightOneSpectrum (𝓞 K)) :
    DifferentiableOn ℂ (fun s => -Complex.log (1 - primeIdealRatio K a s p))
      {s : ℂ | σ < s.re} := by
  apply DifferentiableOn.neg
  apply ((primeRatio_differentiable K a p).differentiableOn.const_sub 1).clog
  intro s hs
  have h := primeRatio_bound K a ha σ hσ s hs.le p
  have hb : ‖-primeIdealRatio K a s p‖ < 1 := by
    rw [norm_neg]
    linarith [h.1.trans h.2]
  simpa only [← sub_eq_add_neg] using Complex.mem_slitPlane_of_norm_lt_one hb

/-- The sum of the actual local Euler logarithms, with ramified zeros kept. -/
def idealEulerLog (a : HeightOneSpectrum (𝓞 K) → ℂ) (s : ℂ) : ℂ :=
  ∑' p : HeightOneSpectrum (𝓞 K), -Complex.log (1 - primeIdealRatio K a s p)

theorem idealEulerLog_differentiableOn (a : HeightOneSpectrum (𝓞 K) → ℂ)
    (ha : ∀ p, ‖a p‖ ≤ 1) :
    DifferentiableOn ℂ (idealEulerLog K a) {s : ℂ | 1 < s.re} := by
  intro s hs
  change 1 < s.re at hs
  let σ := (1 + s.re) / 2
  have hσ : 1 < σ := by dsimp [σ]; linarith
  have hsσ : σ < s.re := by dsimp [σ]; linarith
  have hopen : IsOpen {z : ℂ | σ < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hd : DifferentiableOn ℂ (idealEulerLog K a) {z : ℂ | σ < z.re} :=
    Complex.differentiableOn_tsum_of_summable_norm (primeMajorant_summable K σ hσ)
      (primeLog_differentiable K a ha σ hσ) hopen
      (fun p z hz => primeLog_bound K a ha σ hσ z hz.le p)
  exact (hd.differentiableAt (hopen.mem_nhds hsσ)).differentiableWithinAt

/-- The bound depends only on the field and the fixed right abscissa. -/
theorem idealEulerLog_norm_le (a : HeightOneSpectrum (𝓞 K) → ℂ)
    (ha : ∀ p, ‖a p‖ ≤ 1) (σ : ℝ) (hσ : 1 < σ)
    (s : ℂ) (hs : σ ≤ s.re) :
    ‖idealEulerLog K a s‖ ≤
      (3 / 2 : ℝ) * ∑' I : NonzeroIdeal K, idealNorm K I ^ (-σ) := by
  have hmaj := primeMajorant_summable K σ hσ
  have hn := primeLog_summable_norm K a ha σ hσ s hs
  apply (norm_tsum_le_tsum_norm hn).trans
  apply (hn.tsum_le_tsum (primeLog_bound K a ha σ hσ s hs) hmaj).trans
  rw [← tsum_mul_left]
  exact hmaj.tsum_le_tsum_of_inj (primeNonzeroIdeal K) (primeNonzeroIdeal_injective K)
    (fun I _ => mul_nonneg (by norm_num) (Real.rpow_nonneg (idealNorm_pos K I).le _))
    (fun _ => le_rfl) ((summable_nonzeroIdeal_norm_rpow K hσ).mul_left _)

theorem exp_idealEulerLog_eq_series (a : HeightOneSpectrum (𝓞 K) → ℂ)
    (ha : ∀ p, ‖a p‖ ≤ 1) (s : ℂ) (hs : 1 < s.re) :
    Complex.exp (idealEulerLog K a s) =
      idealDirichletSeries K (nonzeroIdealCoefficient a) s := by
  exact (idealDirichletSeries_eq_primeIdealEulerValue K a ha hs).symm

/-- A logarithm for the actual arbitrary unitary Hecke character. -/
def heckeEulerLog (χ : HeckeCharacter K) : ℂ → ℂ :=
  idealEulerLog K (primeCoefficient K χ)

theorem heckeEulerLog_differentiableOn (χ : HeckeCharacter K) :
    DifferentiableOn ℂ (heckeEulerLog K χ) {s : ℂ | 1 < s.re} :=
  idealEulerLog_differentiableOn K _ (norm_primeCoefficient_le_one K χ)

theorem exp_heckeEulerLog_eq_continuation (χ : HeckeCharacter K)
    (s : ℂ) (hs : 1 < s.re) :
    Complex.exp (heckeEulerLog K χ s) = heckeContinuation K χ s := by
  rw [heckeContinuation_eq_series K χ hs]
  exact exp_idealEulerLog_eq_series K _ (norm_primeCoefficient_le_one K χ) s hs

theorem heckeEulerLog_norm_le (χ : HeckeCharacter K) (σ : ℝ) (hσ : 1 < σ)
    (s : ℂ) (hs : σ ≤ s.re) :
    ‖heckeEulerLog K χ s‖ ≤
      (3 / 2 : ℝ) * ∑' I : NonzeroIdeal K, idealNorm K I ^ (-σ) :=
  idealEulerLog_norm_le K _ (norm_primeCoefficient_le_one K χ) σ hσ s hs

/-- One constant works for every unitary character and every height, on the
half-plane needed by the 49/100 Euler-log disk centered at Re(s)=2. -/
theorem exists_uniform_heckeEulerLog_bound :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (χ : HeckeCharacter K) (s : ℂ),
      151 / 100 ≤ s.re → ‖heckeEulerLog K χ s‖ ≤ A := by
  let A₀ : ℝ := (3 / 2 : ℝ) *
    ∑' I : NonzeroIdeal K, idealNorm K I ^ (-(151 / 100 : ℝ))
  refine ⟨max 1 A₀, le_max_left _ _, ?_⟩
  intro χ s hs
  exact (heckeEulerLog_norm_le K χ (151 / 100) (by norm_num) s hs).trans
    (le_max_right _ _)

end HeckeSkeleton.ActualEulerLogarithm
