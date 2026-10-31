import HeckeSkeleton.ThetaKernel.Gamma
import HeckeSkeleton.HeckeGammaReciprocal

/-!
# Ordinary Hecke Gamma ratios on arbitrary negative strips

The existing proved Gamma quotient bound applies to the ordinary ratio
with beta=a+1/2 and z=1/2-s-itau.  Its positive numerator argument allows
an arbitrary fixed left boundary; reciprocal Gamma values at poles are
retained.  The resulting polynomial degree is explicit and is independent
of the imaginary height.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField HeckeGeneral.Analysis HeckeGeneral.Characters HeckeGeneral.Bridge
open HeckeSkeleton.ThetaKernel HeckeSkeleton.HeckeGammaReciprocal
open scoped BigOperators Classical

private theorem ordinary_gammaC_strip_bound (A a τ : ℝ) (hA : 0 ≤ A) (ha : 0 ≤ a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, -A ≤ s.re → s.re ≤ 0 →
      ‖Complex.Gammaℂ (1 - s - (τ : ℂ) * Complex.I + (a : ℂ)) *
        (Complex.Gammaℂ (s + (τ : ℂ) * Complex.I + (a : ℂ)))⁻¹‖ ≤
          C * (1 + |s.im|) ^ (2 * Nat.ceil A + 2) := by
  obtain ⟨G, hG, hGbound⟩ := norm_Gamma_quot_complex_bound
    (β := a + 1 / 2) (σlo := 1 / 2) (Λ := 1 / 2 + A)
    (by linarith) (by linarith) (by linarith)
  let k : ℕ := 2 * Nat.ceil A + 2
  refine ⟨G * (1 + |τ|) ^ k, by positivity, ?_⟩
  intro s hslo hshi
  let z : ℂ := (1 / 2 : ℂ) - s - (τ : ℂ) * Complex.I
  let n : ℂ := 1 - s - (τ : ℂ) * Complex.I + (a : ℂ)
  let d : ℂ := s + (τ : ℂ) * Complex.I + (a : ℂ)
  have hzre : z.re = 1 / 2 - s.re := by simp [z]
  have hzim : z.im = -(s.im + τ) := by simp [z]; ring
  have hn : ((a + 1 / 2 : ℝ) : ℂ) + z = n := by dsimp [z, n]; push_cast; ring
  have hd : ((a + 1 / 2 : ℝ) : ℂ) - z = d := by dsimp [z, d]; push_cast; ring
  have hg : ‖Complex.Gamma n / Complex.Gamma d‖ ≤
      G * (1 + |s.im + τ|) ^ (1 - 2 * s.re) := by
    have h := hGbound z (by rw [hzre]; linarith) (by rw [hzre]; linarith)
    rw [hn, hd, hzre, hzim, abs_neg] at h
    convert h using 1 <;> congr 2 <;> ring
  have hk : 1 - 2 * s.re ≤ (k : ℝ) := by
    have hc := Nat.le_ceil A
    dsimp [k]
    push_cast
    linarith
  have hheight : 1 + |s.im + τ| ≤ (1 + |τ|) * (1 + |s.im|) := by
    nlinarith [abs_add_le s.im τ, mul_nonneg (abs_nonneg τ) (abs_nonneg s.im)]
  have hpow : (1 + |s.im + τ|) ^ (1 - 2 * s.re) ≤
      (1 + |τ|) ^ k * (1 + |s.im|) ^ k := by
    calc
      _ ≤ (1 + |s.im + τ|) ^ (k : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg (s.im + τ)]) hk
      _ = (1 + |s.im + τ|) ^ k := Real.rpow_natCast _ _
      _ ≤ ((1 + |τ|) * (1 + |s.im|)) ^ k :=
        pow_le_pow_left₀ (by positivity) hheight k
      _ = _ := mul_pow _ _ _
  have hbase : 0 < 2 * Real.pi := by positivity
  have hnorm : ‖Complex.Gammaℂ n * (Complex.Gammaℂ d)⁻¹‖ =
      ((2 * Real.pi) ^ (-n.re) / (2 * Real.pi) ^ (-d.re)) *
        ‖Complex.Gamma n / Complex.Gamma d‖ := by
    simp only [Complex.Gammaℂ_def, norm_mul, norm_inv, norm_div]
    have h1 : ‖(2 * (Real.pi : ℂ)) ^ (-n)‖ = (2 * Real.pi) ^ (-n.re) := by
      rw [show 2 * (Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_cpow_eq_rpow_re_of_pos hbase, Complex.neg_re]
    have h2 : ‖(2 * (Real.pi : ℂ)) ^ (-d)‖ = (2 * Real.pi) ^ (-d.re) := by
      rw [show 2 * (Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_cpow_eq_rpow_re_of_pos hbase, Complex.neg_re]
    rw [h1, h2]
    norm_num
    ring
  have hscale : (2 * Real.pi) ^ (-n.re) / (2 * Real.pi) ^ (-d.re) ≤ 1 := by
    rw [← Real.rpow_sub hbase]
    apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three])
    simp only [n, d, Complex.add_re, Complex.sub_re, Complex.one_re,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    linarith
  change ‖Complex.Gammaℂ n * (Complex.Gammaℂ d)⁻¹‖ ≤ _
  rw [hnorm]
  calc
    _ ≤ ‖Complex.Gamma n / Complex.Gamma d‖ :=
      mul_le_of_le_one_left (norm_nonneg _) hscale
    _ ≤ G * ((1 + |τ|) ^ k * (1 + |s.im|) ^ k) :=
      hg.trans (mul_le_mul_of_nonneg_left hpow hG)
    _ = _ := by ring

variable (K : Type) [Field K] [NumberField K]

/-- The ordinary multiplier in the actual Hecke functional equation. -/
def ordinaryGammaRatio (χ : HeckeCharacter K) (s : ℂ) : ℂ :=
  (canonicalHeckeGammaProfile K χ s)⁻¹ * canonicalHeckeGammaProfile K χ⁻¹ (1 - s)

/-- Reciprocal Gamma is entire; the remaining Gamma factor is evaluated
only in its positive half-plane. -/
theorem differentiableAt_ordinaryGammaRatio (χ : HeckeCharacter K) {s : ℂ}
    (hs : s.re < 1) : DifferentiableAt ℂ (ordinaryGammaRatio K χ) s := by
  have hg : DifferentiableAt ℂ (canonicalHeckeGammaProfile K χ⁻¹) (1 - s) := by
    have h := (differentiable_canonicalHeckeGammaReciprocal K χ⁻¹ (1 - s)).inv
      (inv_ne_zero (canonicalHeckeGammaProfile_ne_zero_of_re_pos K χ⁻¹ (by
        simp only [Complex.sub_re, Complex.one_re]
        linarith)))
    simpa only [inv_inv] using h
  exact (differentiable_canonicalHeckeGammaReciprocal K χ s).mul
    (hg.comp s (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => 1 - z) s))

/-- Arbitrary negative strips admit an explicit polynomial degree. -/
theorem ordinaryGammaRatio_strip_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (χ : HeckeCharacter K) (A : ℝ) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, -A ≤ s.re → s.re ≤ 0 →
      ‖ordinaryGammaRatio K χ s‖ ≤
        C * (1 + |s.im|) ^ ((2 * Nat.ceil A + 2) * Fintype.card (InfinitePlace K)) := by
  have hlocal : ∀ v : InfinitePlace K, ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ,
      -A ≤ s.re → s.re ≤ 0 →
      ‖Complex.Gammaℂ (1 - s - (heckeRadialParameter K v χ : ℂ) * Complex.I +
          (((heckeArchWeight K χ v).natAbs : ℂ) / 2)) *
        (Complex.Gammaℂ (s + (heckeRadialParameter K v χ : ℂ) * Complex.I +
          (((heckeArchWeight K χ v).natAbs : ℂ) / 2)))⁻¹‖ ≤
          C * (1 + |s.im|) ^ (2 * Nat.ceil A + 2) := by
    intro v
    simpa only [Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_ofNat] using
      ordinary_gammaC_strip_bound A ((heckeArchWeight K χ v).natAbs / 2 : ℝ)
        (heckeRadialParameter K v χ) hA (by positivity)
  choose C hC hbound using hlocal
  refine ⟨∏ v, C v, Finset.prod_nonneg (fun v _ => hC v), ?_⟩
  intro s hslo hshi
  rw [ordinaryGammaRatio, canonicalHeckeGammaProfile_inv, canonicalHeckeGammaProfile,
    mul_comm, heckeGammaProfile_dual, heckeGammaProfile, ← Finset.prod_inv_distrib,
    ← Finset.prod_mul_distrib, norm_prod]
  calc
    _ ≤ ∏ v : InfinitePlace K, C v * (1 + |s.im|) ^ (2 * Nat.ceil A + 2) := by
      apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      intro v _
      simpa only [if_neg (v.not_isReal_iff_isComplex.mpr (hcomplex v))] using hbound v s hslo hshi
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← pow_mul]

end HeckeSkeleton.Moments.EngineInduction
