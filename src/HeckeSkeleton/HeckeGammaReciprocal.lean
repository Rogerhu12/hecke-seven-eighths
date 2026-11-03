import HeckeSkeleton.ExplicitHeckeFunctionalEquation
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
Entire reciprocal Gamma factors and uncompleted non-norm Hecke functions.
At a Gamma pole Mathlib's Gamma value is zero. The globally valid identity
is L = Gamma^{-1} times completed-L; Gamma times L is used only in its
proved positive half-plane. This distinction covers w=0 and negative w.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.HeckeGammaReciprocal

open NumberField IsDedekindDomain
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeSkeleton.ExplicitHeckeFunctionalEquation
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]

/-- The actual finite Gamma product, inverted with its entire zero values. -/
def heckeGammaReciprocal (τ : InfinitePlace K → ℝ) (m : InfinitePlace K → ℤ)
    (s : ℂ) : ℂ := (heckeGammaProfile K τ m s)⁻¹

theorem differentiable_heckeGammaReciprocal
    (τ : InfinitePlace K → ℝ) (m : InfinitePlace K → ℤ) :
    Differentiable ℂ (heckeGammaReciprocal K τ m) := by
  unfold heckeGammaReciprocal heckeGammaProfile
  simp_rw [← Finset.prod_inv_distrib]
  apply Differentiable.fun_finsetProd
  intro v _
  by_cases hv : v.IsReal
  · simp only [if_pos hv]
    exact Complex.differentiable_Gammaℝ_inv.comp
      ((differentiable_id.add_const ((τ v : ℂ) * Complex.I)).add_const
        (((m v).natAbs % 2 : ℕ) : ℂ))
  · simp only [if_neg hv]
    exact Complex.differentiable_Gammaℂ_inv.comp
      ((differentiable_id.add_const ((τ v : ℂ) * Complex.I)).add_const
        (((m v).natAbs : ℂ) / 2))

private theorem GammaC_ne_zero_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    Complex.Gammaℂ s ≠ 0 := by
  rw [Complex.Gammaℂ_def]
  apply mul_ne_zero
  · apply mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0)
    exact Complex.cpow_ne_zero_iff.mpr (Or.inl
      (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0)
        (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))
  · exact Complex.Gamma_ne_zero_of_re_pos hs

/-- Every real shift is nonnegative, so Re(s)>0 already suffices. -/
theorem heckeGammaProfile_ne_zero_of_re_pos
    (τ : InfinitePlace K → ℝ) (m : InfinitePlace K → ℤ)
    {s : ℂ} (hs : 0 < s.re) : heckeGammaProfile K τ m s ≠ 0 := by
  unfold heckeGammaProfile
  apply Finset.prod_ne_zero_iff.mpr
  intro v _
  by_cases hv : v.IsReal
  · rw [if_pos hv]
    apply Complex.Gammaℝ_ne_zero_of_re_pos
    have hre : (s + (τ v : ℂ) * Complex.I + (((m v).natAbs % 2 : ℕ) : ℂ)).re =
        s.re + (((m v).natAbs % 2 : ℕ) : ℝ) := by simp
    rw [hre]
    exact add_pos_of_pos_of_nonneg hs (Nat.cast_nonneg _)
  · rw [if_neg hv]
    apply GammaC_ne_zero_of_re_pos
    have hre : (s + (τ v : ℂ) * Complex.I + ((m v).natAbs : ℂ) / 2).re =
        s.re + ((m v).natAbs : ℝ) / 2 := by simp
    rw [hre]
    exact add_pos_of_pos_of_nonneg hs (div_nonneg (Nat.cast_nonneg _) (by norm_num))

theorem differentiable_canonicalHeckeGammaReciprocal (χ : HeckeCharacter K) :
    Differentiable ℂ (fun s => (canonicalHeckeGammaProfile K χ s)⁻¹) :=
  differentiable_heckeGammaReciprocal K _ _

theorem canonicalHeckeGammaProfile_ne_zero_of_re_pos (χ : HeckeCharacter K)
    {s : ℂ} (hs : 0 < s.re) : canonicalHeckeGammaProfile K χ s ≠ 0 :=
  heckeGammaProfile_ne_zero_of_re_pos K _ _ hs

/-- Entire uniqueness extends the reciprocal identity through Gamma poles,
without extending a totalized Gamma-times-L identity across those poles. -/
theorem heckeContinuation_eq_reciprocal_mul_completed_of_nonNorm
    (χ : HeckeCharacter K) (hχ : ∀ t : ℝ, χ ≠ heckeNormTwist K t)
    (τ : InfinitePlace K → ℝ) (m : InfinitePlace K → ℤ)
    (Λ : ℂ → ℂ) (hΛ : Differentiable ℂ Λ)
    (hid : ∀ s : ℂ, 0 < s.re →
      Λ s = heckeGammaProfile K τ m s * heckeContinuation K χ s) :
    ∀ s : ℂ, heckeContinuation K χ s = heckeGammaReciprocal K τ m s * Λ s := by
  have heq : heckeContinuation K χ = (fun s => heckeGammaReciprocal K τ m s * Λ s) := by
    apply entire_eq_of_eq_rightHalfPlane _ _
      (differentiable_heckeContinuation_of_nonNorm K χ hχ)
      ((differentiable_heckeGammaReciprocal K τ m).mul hΛ)
    intro s hs
    change heckeContinuation K χ s = heckeGammaReciprocal K τ m s * Λ s
    rw [hid s (by linarith), heckeGammaReciprocal, ← mul_assoc,
      inv_mul_cancel₀ (heckeGammaProfile_ne_zero_of_re_pos K τ m (by linarith)), one_mul]
  exact congrFun heq

theorem heckeContinuation_eq_canonicalReciprocal_mul_completed_of_nonNorm
    (χ : HeckeCharacter K) (hχ : ∀ t : ℝ, χ ≠ heckeNormTwist K t)
    (Λ : ℂ → ℂ) (hΛ : Differentiable ℂ Λ)
    (hid : ∀ s : ℂ, 0 < s.re →
      Λ s = canonicalHeckeGammaProfile K χ s * heckeContinuation K χ s) :
    ∀ s : ℂ, heckeContinuation K χ s = (canonicalHeckeGammaProfile K χ s)⁻¹ * Λ s :=
  heckeContinuation_eq_reciprocal_mul_completed_of_nonNorm K χ hχ _ _ Λ hΛ hid

/-- An uncompleted FE valid throughout Re(s)<1, including all Gamma pole
locations on the w=0 and negative-w lines. Only the reflected Gamma factor
is used as a multiplier; its argument has positive real part. -/
theorem exists_uncompleted_functionalEquation_left_of_one
    (χ : HeckeCharacter K) (hχ : ∀ t : ℝ, χ ≠ heckeNormTwist K t) :
    ∃ ε : ℂ, ‖ε‖ = 1 ∧ 0 < heckeConductorScale K χ ∧
      ∀ s : ℂ, s.re < 1 →
        heckeContinuation K χ s =
          ((canonicalHeckeGammaProfile K χ s)⁻¹ *
            canonicalHeckeGammaProfile K χ⁻¹ (1 - s) *
            heckeContinuation K χ⁻¹ (1 - s)) /
              (ε * (heckeConductorScale K χ : ℂ) ^ (s - 1 / 2)) := by
  obtain ⟨ε, Λ, Λd, hQ, hε, hΛ, hΛd, _, _, hid, hidd, hFE⟩ :=
    exists_completed_functionalEquation_explicitScale_of_nonNorm K χ hχ
  have hglobal := heckeContinuation_eq_canonicalReciprocal_mul_completed_of_nonNorm
    K χ hχ Λ hΛ hid
  refine ⟨ε, hε, hQ, ?_⟩
  intro s hs
  have hε0 : ε ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hε
    norm_num at hε
  have hcoef : ε * (heckeConductorScale K χ : ℂ) ^ (s - 1 / 2) ≠ 0 :=
    mul_ne_zero hε0 (Complex.cpow_ne_zero_iff.mpr
      (Or.inl (Complex.ofReal_ne_zero.mpr hQ.ne')))
  apply (eq_div_iff hcoef).mpr
  rw [hglobal s]
  calc
    ((canonicalHeckeGammaProfile K χ s)⁻¹ * Λ s) *
        (ε * (heckeConductorScale K χ : ℂ) ^ (s - 1 / 2)) =
      (canonicalHeckeGammaProfile K χ s)⁻¹ *
        (ε * (heckeConductorScale K χ : ℂ) ^ (s - 1 / 2) * Λ s) := by ring
    _ = (canonicalHeckeGammaProfile K χ s)⁻¹ * Λd (1 - s) := by rw [hFE s]
    _ = _ := by
      rw [hidd (1 - s) (by simp only [Complex.sub_re, Complex.one_re]; linarith)]
      ring

end HeckeSkeleton.HeckeGammaReciprocal
