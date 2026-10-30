import HeckeSkeleton.HeckeUniformStripGrowth
import HeckeSkeleton.HeckeBufferedReciprocal

/-!
Uniform buffered control for actual non-norm Hecke continuations of fixed
infinity type over a totally complex field.

The polynomial rectangle estimate is derived from the actual strip bound
at delta=1/8 and the uniform Euler-product bound further to the right.
The physical zero upper bound is then the only zero-exclusion premise.
All constants are chosen before the character, the abscissa and the heights.
The pure norm branch retains its separate pole-cleared treatment.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.HeckeUniformBufferedControl

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Bridge HeckeGeneral.Analysis
open HeckeSkeleton.ExplicitHeckeFunctionalEquation HeckeSkeleton.HeckeUniformStripGrowth
open HeckeSkeleton.HeckeBufferedReciprocal
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]

/-- Closed fixed-type analytic input: no polynomial growth or reciprocal
estimate for the family is assumed. The height padding is explicit. -/
theorem exists_uniform_fixedType_buffered_control
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (τ : InfinitePlace K → ℝ) (m : InfinitePlace K → ℤ)
    {e ε : ℝ} (he : 0 < e) (he' : e < 1 / 1000) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ (χ : HeckeCharacter K) (a H Hupper : ℝ),
      (∀ t : ℝ, χ ≠ heckeNormTwist K t) →
      (fun v => heckeRadialParameter K v χ) = τ → heckeArchWeight K χ = m →
      1 / 2 ≤ a → a ≤ 1 → 0 ≤ H → H + 3 / 2 ≤ Hupper →
      ZeroUpperBound K χ Hupper (a + 2 * e) →
      ∀ s : ℂ, a + 6 * e ≤ s.re → s.re ≤ 2 → |s.im| ≤ H →
        ‖heckeContinuation K χ s‖ + ‖(heckeContinuation K χ s)⁻¹‖ ≤
          D * heckeConductorScale K χ ^ ε *
            (2 + Hupper) ^ ((2 * Fintype.card (InfinitePlace K) : ℕ) * ε) := by
  obtain ⟨Cs, hCs, hstrip⟩ := exists_uniform_fixedType_strip_bound K hcomplex τ m
    (1 / 8) (by norm_num) (by norm_num)
  obtain ⟨Cr, hCr, hright⟩ := exists_uniform_rightHalfPlane_bound K (9 / 8) (by norm_num)
  let k : ℕ := 2 * Fintype.card (InfinitePlace K)
  let B₀ : ℝ := max 1 (max Cs Cr)
  let B : ℝ := Real.exp 1 * B₀
  have hB₀ : 1 ≤ B₀ := le_max_left _ _
  have hB₀pos : 0 < B₀ := zero_lt_one.trans_le hB₀
  have hB : 0 < B := mul_pos (Real.exp_pos _) hB₀pos
  have hexp : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hB₀B : B₀ ≤ B := le_mul_of_one_le_left hB₀pos.le hexp
  have hCsB : Cs ≤ B := (le_max_left Cs Cr).trans
    ((le_max_right 1 (max Cs Cr)).trans hB₀B)
  have hCrB : Cr ≤ B := (le_max_right Cs Cr).trans
    ((le_max_right 1 (max Cs Cr)).trans hB₀B)
  have hexpB : Real.exp 1 ≤ B := le_mul_of_one_le_right (Real.exp_pos _).le hB₀
  obtain ⟨D₀, hD₀, hcontrol⟩ := hecke_subpower_of_upper_strip_growth K
    (M := 1) he he' (by norm_num) hε
  refine ⟨D₀ * B ^ ε, mul_pos hD₀ (Real.rpow_pos_of_pos hB _), ?_⟩
  intro χ a H Hupper hχ hτ hm ha ha' hH hpadding hupper
  obtain ⟨root, Λ, Λd, hQ, _, _, _, _, _, _, _, _⟩ :=
    exists_completed_functionalEquation_explicitScale_of_nonNorm K χ hχ
  have hQone : 1 ≤ heckeConductorScale K χ := one_le_conductorScale_of_pos K χ hQ
  have hHU : 0 ≤ Hupper := by linarith
  have hT : 1 ≤ 2 + Hupper := by linarith
  have hTpos : 0 < 2 + Hupper := zero_lt_one.trans_le hT
  have hTpow : 1 ≤ (2 + Hupper) ^ k := one_le_pow₀ hT
  let C : ℝ := B * heckeConductorScale K χ * (2 + Hupper) ^ k
  have hBC : B ≤ C := by
    calc
      B ≤ B * heckeConductorScale K χ := le_mul_of_one_le_right hB.le hQone
      _ ≤ C := le_mul_of_one_le_right (mul_nonneg hB.le hQ.le) hTpow
  have hC : Real.exp 1 ≤ C := hexpB.trans hBC
  have hpoly : ∀ z : ℂ, a + 2 * e < z.re → |z.im| ≤ Hupper →
      ‖heckeContinuation K χ z‖ ≤ C ^ (1 : ℝ) := by
    intro z hz hheight
    have hheightpow : (2 + |z.im|) ^ k ≤ (2 + Hupper) ^ k :=
      pow_le_pow_left₀ (by positivity) (by linarith) k
    have hQpow : heckeConductorScale K χ ^ (1 / 2 + (1 / 8 : ℝ)) ≤
        heckeConductorScale K χ := by
      calc
        _ ≤ heckeConductorScale K χ ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hQone (by norm_num)
        _ = _ := Real.rpow_one _
    rw [Real.rpow_one]
    by_cases hleft : z.re ≤ 1 + (1 / 8 : ℝ)
    · have hb := hstrip χ hχ hτ hm z ⟨by linarith, hleft⟩
      calc
        ‖heckeContinuation K χ z‖ ≤
            Cs * heckeConductorScale K χ ^ (1 / 2 + (1 / 8 : ℝ)) *
              (2 + |z.im|) ^ k := hb
        _ ≤ B * heckeConductorScale K χ * (2 + Hupper) ^ k := by
          apply mul_le_mul _ hheightpow (by positivity) (mul_nonneg hB.le hQ.le)
          exact mul_le_mul hCsB hQpow (Real.rpow_nonneg hQ.le _) hB.le
        _ = C := rfl
    · have hb : ‖heckeContinuation K χ z‖ ≤ Cr :=
        hright χ z (by linarith)
      exact hb.trans (hCrB.trans hBC)
  have hscale : C ^ ε = B ^ ε * heckeConductorScale K χ ^ ε *
      (2 + Hupper) ^ ((k : ℝ) * ε) := by
    dsimp [C]
    rw [Real.mul_rpow (mul_nonneg hB.le hQ.le) (pow_nonneg hTpos.le k),
      Real.mul_rpow hB.le hQ.le, ← Real.rpow_natCast_mul hTpos.le k ε]
  intro s hs hs' hheight
  have hb := hcontrol a C H Hupper χ ha ha' hC hχ hpadding hupper hpoly
    s hs hs' hheight
  rw [hscale] at hb
  exact hb.trans_eq (by dsimp [k]; ring)

end HeckeSkeleton.HeckeUniformBufferedControl
