module

public import ThetaGlobal.GammaReciprocalGrowth
public import ThetaGlobal.GammaDeconvolver

/-!
# The finite Gamma profile has the required strip growth

This discharges the reciprocal-Gamma growth hypothesis of the scalar
deconvolver from the actual Gamma function.  The proof uses Euler reflection
and finite products; no separate Stirling assumption remains.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

namespace ThetaGlobal.GammaProfileGrowth

open Set MeasureTheory
open GaussianStripDecay GammaDeconvolver GammaReciprocalGrowth
open scoped BigOperators Classical

theorem growth_one : ExponentialStripGrowth (fun _ : ℂ => (1 : ℂ)) := by
  intro a b _
  refine ⟨1, zero_le_one, 0, 0, ?_⟩
  intro c hc t
  simp

theorem growth_prod {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ)
    (hf : ∀ j ∈ s, ExponentialStripGrowth (f j)) :
    ExponentialStripGrowth (fun z => ∏ j ∈ s, f j z) := by
  induction s using Finset.induction_on with
  | empty => simpa using growth_one
  | @insert j s hj ih =>
    simp only [Finset.prod_insert hj]
    apply (hf j (Finset.mem_insert_self _ _)).mul
    exact ih (fun k hk => hf k (Finset.mem_insert_of_mem hk))

theorem shifted_reciprocal_growth (shift radial : ℝ) :
    ExponentialStripGrowth (fun z : ℂ =>
      (Complex.Gamma ((shift : ℂ) + z + Complex.I * (radial : ℂ)))⁻¹) := by
  intro a b _
  obtain ⟨C, hC, hbound⟩ := inverse_Gamma_strip_bound (shift + a) (shift + b)
  refine ⟨C * Real.exp (Real.pi * |radial|), by positivity, Real.pi, 0, ?_⟩
  intro c hc t
  have he : (shift : ℂ) + ((c : ℂ) + (t : ℂ) * Complex.I) +
      Complex.I * (radial : ℂ) =
        ((shift + c : ℝ) : ℂ) + ((t + radial : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  dsimp only
  rw [he, pow_zero, mul_one]
  have h := hbound (shift + c) ⟨by linarith [hc.1], by linarith [hc.2]⟩ (t + radial)
  have hexp : Real.exp (Real.pi * |t + radial|) ≤
      Real.exp (Real.pi * |radial|) * Real.exp (Real.pi * |t|) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left (abs_add_le t radial) Real.pi_pos.le
    nlinarith
  exact h.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hexp hC)

theorem scalar_exp_growth (C : ℂ) (L : ℝ) :
    ExponentialStripGrowth (fun z : ℂ => C * Complex.exp (-((L : ℂ) * z))) := by
  intro a b _
  refine ⟨‖C‖ * Real.exp (|L| * (|a| + |b|)), by positivity, 0, 0, ?_⟩
  intro c hc t
  have hcabs : |c| ≤ |a| + |b| := by
    apply abs_le.mpr
    constructor
    · linarith [neg_abs_le a, abs_nonneg b, hc.1]
    · linarith [le_abs_self b, abs_nonneg a, hc.2]
  have hLc : -(L * c) ≤ |L| * (|a| + |b|) := by
    calc
      -(L * c) ≤ |L * c| := neg_le_abs _
      _ = |L| * |c| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hcabs (abs_nonneg L)
  rw [norm_mul, Complex.norm_exp]
  simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.add_re, Complex.I_re, Complex.I_im,
    mul_zero, zero_mul, sub_zero, zero_sub, add_zero, pow_zero,
    zero_mul, Real.exp_zero, mul_one]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hLc) (norm_nonneg C)

variable {ι : Type*} [Fintype ι] (p : GammaProfile ι)

theorem reciprocalGamma_growth : ExponentialStripGrowth (reciprocalGamma p) := by
  unfold reciprocalGamma
  apply (scalar_exp_growth p.C₀⁻¹ (Real.log p.A₀)).mul
  exact growth_prod Finset.univ _ (fun j _ => shifted_reciprocal_growth (p.shift j) (p.radial j))

/-- The deconvolver is now constructed from the Gamma profile and the
annular transform alone; reciprocal-Gamma growth is a theorem. -/
def canonicalDeconvolver (Vhat : ℂ → ℂ)
    (hV : Differentiable ℂ Vhat) (hVstrip : BoundedOnVerticalStrips Vhat)
    (ε : ℝ) (hε : 0 < ε) :
    AnnularTransfer.DeconvolverData
      (fun t : ℝ => directGamma p ((t : ℂ) * Complex.I))
      (fun t : ℝ => Vhat ((t : ℂ) * Complex.I)) ε :=
  gammaDeconvolver p Vhat hV hVstrip (reciprocalGamma_growth p) ε hε

theorem canonicalDeconvolver_all_power_moments (Vhat : ℂ → ℂ)
    (hV : Differentiable ℂ Vhat) (hVstrip : BoundedOnVerticalStrips Vhat)
    (ε : ℝ) (hε : 0 < ε) (q : ℝ) :
    IntegrableOn
      (fun t => ‖DeconvolverMoments.multiplicativeInverse
        (canonicalDeconvolver p Vhat hV hVstrip ε hε).spectrum t‖ * t ^ q / t)
      (Ioi 0) :=
  gammaDeconvolver_all_power_moments p Vhat hV hVstrip (reciprocalGamma_growth p) ε hε q

end ThetaGlobal.GammaProfileGrowth

#print axioms ThetaGlobal.GammaProfileGrowth.reciprocalGamma_growth
#print axioms ThetaGlobal.GammaProfileGrowth.canonicalDeconvolver_all_power_moments
