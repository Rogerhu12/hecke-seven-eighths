import HeckeSkeleton.HeckeStripPolynomial
import HeckeSkeleton.HeckeGammaQualitativeGrowth
import HeckeSkeleton.HeckeFixedTypeGammaBound
import HeckeSkeleton.ActualEulerLogarithm

/-!
Polynomial strip growth for actual non-norm Hecke continuations of a fixed
infinity type over a totally complex number field.

The final constant is chosen before the character. The two boundary bounds
come from the uniform Euler logarithm and the explicit-conductor functional
equation. Character-dependent boundedness of the completed function is used
only to establish the qualitative growth required for Phragmen--Lindelof.
The interpolation theorem removes those qualitative constants.

The generic Gamma and strip interpolation inputs have their source and
Apache-2.0 attribution recorded in their own modules. This module assembles
them with the actual Hecke continuation and actual conductor scale.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.HeckeUniformStripGrowth

open NumberField IsDedekindDomain AutomorphicForm
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Bridge HeckeGeneral.Analysis
open HeckeSkeleton.ExplicitHeckeFunctionalEquation HeckeSkeleton.HeckeGammaReciprocal
open HeckeSkeleton.ActualEulerLogarithm HeckeSkeleton.HeckeFixedTypeGammaBound
open HeckeSkeleton.HeckeGammaQualitativeGrowth HeckeSkeleton.HeckeStripPolynomial
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]

/-- Uniformity includes every unitary character, with no infinity restriction. -/
theorem exists_uniform_rightHalfPlane_bound (σ : ℝ) (hσ : 1 < σ) :
    ∃ E : ℝ, 0 < E ∧ ∀ (χ : HeckeCharacter K) (s : ℂ), σ ≤ s.re →
      ‖heckeContinuation K χ s‖ ≤ E := by
  let A : ℝ := (3 / 2 : ℝ) *
    ∑' I : NonzeroIdeal K, idealNorm K I ^ (-σ)
  refine ⟨Real.exp A, Real.exp_pos _, ?_⟩
  intro χ s hs
  rw [← exp_heckeEulerLog_eq_continuation K χ s (hσ.trans_le hs), Complex.norm_exp]
  exact Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans
    (heckeEulerLog_norm_le K χ σ hσ s hs))

/-- Integrality of the actual discriminant-conductor product gives Q >= 1. -/
theorem one_le_conductorScale_of_pos (χ : HeckeCharacter K)
    (hQ : 0 < heckeConductorScale K χ) : 1 ≤ heckeConductorScale K χ := by
  have hcast : heckeConductorScale K χ =
      (((NumberField.discr K).natAbs * (finiteConductor K χ).val.absNorm : ℕ) : ℝ) := by
    simp only [heckeConductorScale, Nat.cast_mul]
  rw [hcast] at hQ ⊢
  have hn : 0 < (NumberField.discr K).natAbs * (finiteConductor K χ).val.absNorm := by
    exact_mod_cast hQ
  exact_mod_cast (Nat.succ_le_iff.mpr hn)

/-- Arbitrary fixed real/complex infinity type has qualitative exponential
reciprocal-Gamma growth; all Gamma pole values are included. -/
theorem heckeGammaProfile_inverse_strip_exp_bound
    (τ : InfinitePlace K → ℝ) (m : InfinitePlace K → ℤ)
    (a b : ℝ) (hab : a ≤ b) :
    ∃ G : ℝ, 0 < G ∧ ∀ s : ℂ, a ≤ s.re ∧ s.re ≤ b →
      ‖(heckeGammaProfile K τ m s)⁻¹‖ ≤
        G * Real.exp ((Fintype.card (InfinitePlace K) : ℝ) * Real.pi * |s.im|) := by
  let g (v : InfinitePlace K) (s : ℂ) : ℂ :=
    if v.IsReal then
      Complex.Gammaℝ (s + (τ v : ℂ) * Complex.I + (((m v).natAbs % 2 : ℕ) : ℂ))
    else Complex.Gammaℂ (s + (τ v : ℂ) * Complex.I + ((m v).natAbs : ℂ) / 2)
  have hlocal : ∀ v : InfinitePlace K, ∃ G : ℝ, 0 < G ∧
      ∀ s : ℂ, a ≤ s.re ∧ s.re ≤ b →
        ‖(g v s)⁻¹‖ ≤ G * Real.exp (Real.pi * |s.im|) := by
    intro v
    by_cases hv : v.IsReal
    · simpa only [g, if_pos hv, add_assoc] using
        gammaR_inverse_shifted_strip_exp_bound a b hab
          ((τ v : ℂ) * Complex.I + (((m v).natAbs % 2 : ℕ) : ℂ))
    · simpa only [g, if_neg hv, add_assoc] using
        gammaC_inverse_shifted_strip_exp_bound a b hab
          ((τ v : ℂ) * Complex.I + ((m v).natAbs : ℂ) / 2)
  choose G hGpos hG using hlocal
  refine ⟨∏ v, G v, Finset.prod_pos (fun v _ => hGpos v), ?_⟩
  intro s hs
  change ‖(∏ v, g v s)⁻¹‖ ≤ _
  rw [← Finset.prod_inv_distrib, norm_prod]
  calc
    ∏ v, ‖(g v s)⁻¹‖ ≤ ∏ v, G v * Real.exp (Real.pi * |s.im|) :=
      Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun v _ => hG v s hs)
    _ = (∏ v, G v) * Real.exp
        ((Fintype.card (InfinitePlace K) : ℝ) * Real.pi * |s.im|) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        ← Real.exp_nat_mul]
      congr 2
      ring

/-- This is a proved qualitative growth condition for the actual L-function,
not an additional hypothesis on the family in the final uniform theorem. -/
theorem heckeContinuation_quadratic_strip_growth
    (χ : HeckeCharacter K) (hχ : ∀ t : ℝ, χ ≠ heckeNormTwist K t)
    (τ : InfinitePlace K → ℝ) (m : InfinitePlace K → ℤ)
    (hτ : (fun v => heckeRadialParameter K v χ) = τ)
    (hm : heckeArchWeight K χ = m) (a b : ℝ) (hab : a ≤ b) :
    ∃ M B : ℝ, 0 ≤ M ∧ 0 ≤ B ∧ ∀ s : ℂ,
      a < s.re ∧ s.re < b →
        ‖heckeContinuation K χ s‖ ≤ M * Real.exp (B * (1 + |s.im|) ^ 2) := by
  obtain ⟨ε, Λ, Λd, _, _, hΛ, _, hb, _, hid, _, _⟩ :=
    exists_completed_functionalEquation_explicitScale_of_nonNorm K χ hχ
  have hid' : ∀ s : ℂ, 0 < s.re →
      Λ s = heckeGammaProfile K τ m s * heckeContinuation K χ s := by
    simpa only [canonicalHeckeGammaProfile, hτ, hm] using hid
  have hglobal := heckeContinuation_eq_reciprocal_mul_completed_of_nonNorm
    K χ hχ τ m Λ hΛ hid'
  obtain ⟨G, hGpos, hG⟩ := heckeGammaProfile_inverse_strip_exp_bound K τ m a b hab
  obtain ⟨C, hC⟩ := hb a b
  let B : ℝ := (Fintype.card (InfinitePlace K) : ℝ) * Real.pi
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨G * max C 0, B, by positivity, hB, ?_⟩
  intro s hs
  have hΛb : ‖Λ s‖ ≤ max C 0 := (hC s hs.1.le hs.2.le).trans (le_max_left _ _)
  have ht : |s.im| ≤ (1 + |s.im|) ^ 2 := by nlinarith [abs_nonneg s.im]
  rw [hglobal s, heckeGammaReciprocal, norm_mul]
  calc
    ‖(heckeGammaProfile K τ m s)⁻¹‖ * ‖Λ s‖ ≤
        (G * Real.exp (B * |s.im|)) * max C 0 :=
      mul_le_mul (hG s ⟨hs.1.le, hs.2.le⟩) hΛb (norm_nonneg _) (by positivity)
    _ ≤ (G * Real.exp (B * (1 + |s.im|) ^ 2)) * max C 0 := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht hB)) hGpos.le)
          (le_max_right _ _)
    _ = (G * max C 0) * Real.exp (B * (1 + |s.im|) ^ 2) := by ring

/-- A common polynomial bound for the whole reflected Gamma product.
Its constant depends only on the fixed infinity type and delta. -/
theorem fixedType_gamma_multiplier_left_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (τ : InfinitePlace K → ℝ) (m : InfinitePlace K → ℤ)
    (δ : ℝ) (hδ : 0 < δ) (hδsmall : δ < 1 / 4) :
    ∃ G : ℝ, 0 < G ∧ ∀ s : ℂ, s.re = -δ →
      ‖heckeGammaProfile K (-τ) (-m) (1 - s) *
        (heckeGammaProfile K τ m s)⁻¹‖ ≤
          G * (2 + |s.im|) ^ (2 * Fintype.card (InfinitePlace K)) := by
  have hlocal : ∀ v : InfinitePlace K, ∃ G : ℝ, 0 < G ∧
      ∀ s : ℂ, s.re = -δ →
        ‖Complex.Gammaℂ (1 - s - (τ v : ℂ) * Complex.I + ((m v).natAbs : ℂ) / 2) *
          (Complex.Gammaℂ (s + (τ v : ℂ) * Complex.I + ((m v).natAbs : ℂ) / 2))⁻¹‖ ≤
            G * (2 + |s.im|) ^ 2 := by
    intro v
    simpa only [Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_ofNat] using
      gammaC_fixedType_reflected_left_bound δ ((m v).natAbs / 2 : ℝ) (τ v)
      hδ hδsmall (by positivity)
  choose G hGpos hG using hlocal
  refine ⟨∏ v, G v, Finset.prod_pos (fun v _ => hGpos v), ?_⟩
  intro s hs
  rw [heckeGammaProfile_dual, heckeGammaProfile, ← Finset.prod_inv_distrib,
    ← Finset.prod_mul_distrib, norm_prod]
  calc
    _ ≤ ∏ v : InfinitePlace K, G v * (2 + |s.im|) ^ 2 := by
      apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      intro v _
      simpa only [if_neg (v.not_isReal_iff_isComplex.mpr (hcomplex v))] using hG v s hs
    _ = (∏ v, G v) * (2 + |s.im|) ^ (2 * Fintype.card (InfinitePlace K)) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← pow_mul]

/-- Uniform left boundary from the actual explicit-conductor FE. -/
theorem fixedType_left_boundary_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (τ : InfinitePlace K → ℝ) (m : InfinitePlace K → ℤ)
    (δ : ℝ) (hδ : 0 < δ) (hδsmall : δ < 1 / 4) :
    ∃ C : ℝ, 0 < C ∧ ∀ (χ : HeckeCharacter K),
      (∀ t : ℝ, χ ≠ heckeNormTwist K t) →
      (fun v => heckeRadialParameter K v χ) = τ → heckeArchWeight K χ = m →
      ∀ s : ℂ, s.re = -δ →
        ‖heckeContinuation K χ s‖ ≤ C * heckeConductorScale K χ ^ (1 / 2 + δ) *
          (2 + |s.im|) ^ (2 * Fintype.card (InfinitePlace K)) := by
  obtain ⟨G, hGpos, hG⟩ := fixedType_gamma_multiplier_left_bound K hcomplex τ m δ hδ hδsmall
  obtain ⟨E, hEpos, hE⟩ := exists_uniform_rightHalfPlane_bound K (1 + δ) (by linarith)
  refine ⟨G * E, mul_pos hGpos hEpos, ?_⟩
  intro χ hχ hτ hm s hs
  obtain ⟨ε, hε, hQ, hFE⟩ := exists_uncompleted_functionalEquation_left_of_one K χ hχ
  have hcan : canonicalHeckeGammaProfile K χ s = heckeGammaProfile K τ m s := by
    simp only [canonicalHeckeGammaProfile, hτ, hm]
  have hcanD : canonicalHeckeGammaProfile K χ⁻¹ (1 - s) =
      heckeGammaProfile K (-τ) (-m) (1 - s) := by
    rw [canonicalHeckeGammaProfile_inv, hτ, hm]
  have hGb : ‖(canonicalHeckeGammaProfile K χ s)⁻¹ *
      canonicalHeckeGammaProfile K χ⁻¹ (1 - s)‖ ≤
        G * (2 + |s.im|) ^ (2 * Fintype.card (InfinitePlace K)) := by
    rw [hcan, hcanD, mul_comm]
    exact hG s hs
  have hEb : ‖heckeContinuation K χ⁻¹ (1 - s)‖ ≤ E := by
    apply hE
    simp only [Complex.sub_re, Complex.one_re, hs]
    linarith
  have hre : (s - 1 / 2).re = -(1 / 2 + δ) := by simp [hs]; ring
  have hnorm : ‖heckeContinuation K χ s‖ =
      (‖(canonicalHeckeGammaProfile K χ s)⁻¹ * canonicalHeckeGammaProfile K χ⁻¹ (1 - s)‖ *
        ‖heckeContinuation K χ⁻¹ (1 - s)‖) * heckeConductorScale K χ ^ (1 / 2 + δ) := by
    rw [hFE s (by rw [hs]; linarith), norm_div, norm_mul,
      norm_mul ε, hε, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos hQ,
      hre, Real.rpow_neg hQ.le, div_inv_eq_mul]
  rw [hnorm]
  calc
    _ ≤ ((G * (2 + |s.im|) ^ (2 * Fintype.card (InfinitePlace K))) * E) *
        heckeConductorScale K χ ^ (1 / 2 + δ) := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hQ.le _)
      exact mul_le_mul hGb hEb (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- The family constant is chosen before chi. The finite conductor enters
only through its actual scale Q, and every height in the closed strip is covered. -/
theorem exists_uniform_fixedType_strip_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (τ : InfinitePlace K → ℝ) (m : InfinitePlace K → ℤ)
    (δ : ℝ) (hδ : 0 < δ) (hδsmall : δ < 1 / 4) :
    ∃ C : ℝ, 0 < C ∧ ∀ (χ : HeckeCharacter K),
      (∀ t : ℝ, χ ≠ heckeNormTwist K t) →
      (fun v => heckeRadialParameter K v χ) = τ → heckeArchWeight K χ = m →
      ∀ s : ℂ, -δ ≤ s.re ∧ s.re ≤ 1 + δ →
        ‖heckeContinuation K χ s‖ ≤ C * heckeConductorScale K χ ^ (1 / 2 + δ) *
          (2 + |s.im|) ^ (2 * Fintype.card (InfinitePlace K)) := by
  obtain ⟨A, hApos, hA⟩ := fixedType_left_boundary_bound K hcomplex τ m δ hδ hδsmall
  obtain ⟨E, hEpos, hE⟩ := exists_uniform_rightHalfPlane_bound K (1 + δ) (by linarith)
  let C₀ : ℝ := max A E
  let k : ℕ := 2 * Fintype.card (InfinitePlace K)
  have hC₀ : 0 < C₀ := hApos.trans_le (le_max_left _ _)
  refine ⟨6 ^ k * C₀, by positivity, ?_⟩
  intro χ hχ hτ hm
  obtain ⟨ε, Λ, Λd, hQ, _, _, _, _, _, _, _, _⟩ :=
    exists_completed_functionalEquation_explicitScale_of_nonNorm K χ hχ
  have hQone : 1 ≤ heckeConductorScale K χ := one_le_conductorScale_of_pos K χ hQ
  have hQpow : 1 ≤ heckeConductorScale K χ ^ (1 / 2 + δ) :=
    Real.one_le_rpow hQone (by linarith)
  let H : ℝ := C₀ * heckeConductorScale K χ ^ (1 / 2 + δ)
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hboundary : ∀ s : ℂ, (s.re = -δ ∨ s.re = 1 + δ) →
      ‖heckeContinuation K χ s‖ ≤ H * (2 + |s.im|) ^ k := by
    intro s hs
    rcases hs with hs | hs
    · exact (hA χ hχ hτ hm s hs).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (le_max_left A E) (Real.rpow_nonneg hQ.le _)) (by positivity))
    · have hEb := hE χ s hs.ge
      have hbase : 1 ≤ (2 + |s.im|) ^ k := one_le_pow₀ (by linarith [abs_nonneg s.im])
      have hEC : E ≤ C₀ := le_max_right _ _
      have hCH : C₀ ≤ H := by
        dsimp [H]
        exact le_mul_of_one_le_right hC₀.le hQpow
      exact hEb.trans (hEC.trans (hCH.trans (le_mul_of_one_le_right hH hbase)))
  have hstrip := norm_le_on_closed_strip_of_polynomial_boundary δ hδ hδsmall.le
    k H hH (heckeContinuation K χ)
    (differentiable_heckeContinuation_of_nonNorm K χ hχ).diffContOnCl
    (heckeContinuation_quadratic_strip_growth K χ hχ τ m hτ hm (-δ) (1 + δ)
      (by linarith)) hboundary
  intro s hs
  exact (hstrip s hs).trans_eq (by dsimp [H]; ring)

end HeckeSkeleton.HeckeUniformStripGrowth
