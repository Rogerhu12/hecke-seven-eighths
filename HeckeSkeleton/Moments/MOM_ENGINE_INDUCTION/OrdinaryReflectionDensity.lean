import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.OrdinaryRestorationOperator

/-!
# A genuine row-independent frequency envelope

The original compact-test seminorm controls all polynomial frequency
costs.  The exact Euler restoration phase is charged at its proved
subpower mass.  Constants and the original Euler order are selected
before every moving row, deleted set, physical scale and frequency.
No supremum of independent row measures is exchanged with an integral.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField MeasureTheory Set Filter
open HeckeGeneral.Analysis HeckeGeneral.Characters HeckeGeneral.Bridge
open HeckeGeneral.ThetaSkeleton.Global HeckeSkeleton.ThetaKernel
open HeckePort.Moments
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]

/-- The actual scalar multiplying a common power-window child column. -/
def ordinaryReflectionDensity (χ : HeckeCharacter K) (V : SmoothAnnularTest)
    (a ai : Ideal (𝓞 K) → ℂ) (S : Finset (Ideal (𝓞 K))) (Q X N σ t : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ))⁻¹ * ordinaryMellinGamma K χ V σ t *
    ordinaryRestorationPhase a ai S Q X N σ t

/-- Polynomial costs of actual child profiles can be put in this
frequency envelope.  No derivative is asserted uniformly bounded in t. -/
theorem ordinaryReflectionDensity_weighted_uniform
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (χ : HeckeCharacter K) {δ B ε : ℝ}
    (hδ : 0 < δ) (hB : 0 < B) (hε : 0 < ε) (n : ℕ) :
    ∃ J : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (V : SmoothAnnularTest), V.upper ≤ B →
      ∀ (a ai : Ideal (𝓞 K) → ℂ), IdealCoeff a → IdealCoeff ai →
      ∀ (S : Finset (Ideal (𝓞 K))) (hS : ∀ P ∈ S, Prime P)
      (Q X N σ : ℝ), 0 < Q → 0 < X → 0 < N → 1 / 4 ≤ σ → σ ≤ 3 / 4 →
      ∀ t : ℝ, (1 + |t|) ^ n * ‖ordinaryReflectionDensity K χ V a ai S Q X N σ t‖ ≤
        C * testSeminorm V.toFun J δ *
          (N * X / Q) ^ (σ - 1 / 2) * (Ideal.absNorm (∏ P ∈ S, P) : ℝ) ^ ε *
            (1 + |t|) ^ (-(2 : ℝ)) := by
  obtain ⟨J, Cg, hCg, hgamma⟩ := ordinaryMellinGamma_weighted_uniform K hcomplex χ hδ hB n
  obtain ⟨Ce, hCe, heuler⟩ := ordinaryRestorationPhase_norm_subpower (K := K)
    (1 / 4) ε (by norm_num) hε
  refine ⟨J, ‖(2 * (Real.pi : ℂ))⁻¹‖ * Cg * Ce, by positivity, ?_⟩
  intro V hupper a ai ha hai S hS Q X N σ hQ hX hN hlo hhi t
  have hline : σ ∈ Icc (-δ) (3 / 4) := ⟨by linarith, hhi⟩
  have hM := (hgamma V hupper σ hline).1 t
  have hE := heuler a ai ha hai S hS Q X N σ hQ hX hN hlo (by linarith) t
  have hSnonneg : 0 ≤ testSeminorm V.toFun J δ :=
    (Iint_nonneg V 0 (-1 / 4)).trans (Iint_left_le V 0 J (Nat.zero_le _) δ)
  rw [ordinaryReflectionDensity, norm_mul, norm_mul]
  calc
    _ = ‖(2 * (Real.pi : ℂ))⁻¹‖ *
        (((1 + |t|) ^ n * ‖ordinaryMellinGamma K χ V σ t‖) *
          ‖ordinaryRestorationPhase a ai S Q X N σ t‖) := by ring
    _ ≤ ‖(2 * (Real.pi : ℂ))⁻¹‖ *
        ((Cg * testSeminorm V.toFun J δ * (1 + |t|) ^ (-(2 : ℝ))) *
          (Ce * (N * X / Q) ^ (σ - 1 / 2) *
            (Ideal.absNorm (∏ P ∈ S, P) : ℝ) ^ ε)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul hM hE (norm_nonneg _) (by positivity)) (norm_nonneg _)
    _ = _ := by ring

/-- Finite-order arithmetic rows have the identical Mellin/Gamma density
as the fixed background.  The finite conductor only changes the explicit
scale parameter Q, not any constant or Euler order in this theorem. -/
theorem ordinaryReflectionDensity_finiteRows_uniform
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (background : HeckeCharacter K) {δ B ε : ℝ}
    (hδ : 0 < δ) (hB : 0 < B) (hε : 0 < ε) (n : ℕ) :
    ∃ J : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (row : HeckeCharacter K), FiniteOrder row →
      ∀ (V : SmoothAnnularTest), V.upper ≤ B →
      ∀ (a ai : Ideal (𝓞 K) → ℂ), IdealCoeff a → IdealCoeff ai →
      ∀ (S : Finset (Ideal (𝓞 K))) (hS : ∀ P ∈ S, Prime P)
      (Q X N σ : ℝ), 0 < Q → 0 < X → 0 < N → 1 / 4 ≤ σ → σ ≤ 3 / 4 →
      ∀ t : ℝ, (1 + |t|) ^ n *
        ‖ordinaryReflectionDensity K (background * row) V a ai S Q X N σ t‖ ≤
        C * testSeminorm V.toFun J δ *
          (N * X / Q) ^ (σ - 1 / 2) * (Ideal.absNorm (∏ P ∈ S, P) : ℝ) ^ ε *
            (1 + |t|) ^ (-(2 : ℝ)) := by
  obtain ⟨J, C, hC, hbound⟩ := ordinaryReflectionDensity_weighted_uniform
    K hcomplex background hδ hB hε n
  refine ⟨J, C, hC, ?_⟩
  intro row hrow V hupper a ai ha hai S hS Q X N σ hQ hX hN hlo hhi t
  have hτ : (fun v => heckeRadialParameter K v (background * row)) =
      (fun v => heckeRadialParameter K v background) := by
    funext v
    rw [heckeRadialParameter_mul, heckeRadialParameter_finiteOrder K v hrow, add_zero]
  have hm : heckeArchWeight K (background * row) = heckeArchWeight K background := by
    funext v
    rw [heckeArchWeight_of_complex K (background * row) v (hcomplex v),
      heckeArchWeight_of_complex K background v (hcomplex v), heckeComplexWeight_mul,
      heckeComplexWeight_finiteOrder K v (hcomplex v) hrow, add_zero]
  simpa only [ordinaryReflectionDensity, ordinaryMellinGamma,
    ordinaryGammaRatio_eq_of_type K (background * row) background hτ hm] using
    hbound V hupper a ai ha hai S hS Q X N σ hQ hX hN hlo hhi t

/-- Exactly two common child families suffice; the row-dependent choice
is absorbed into a scalar coefficient of one of these two labels. -/
def ordinaryReflectionLine (r : ℝ) : ℝ := if r ≤ 1 then 3 / 4 else 1 / 4

theorem ordinaryReflectionLine_bound {r : ℝ} (hr : 0 < r) :
    (ordinaryReflectionLine r = 1 / 4 ∨ ordinaryReflectionLine r = 3 / 4) ∧
    1 / 4 ≤ ordinaryReflectionLine r ∧ ordinaryReflectionLine r ≤ 3 / 4 ∧
      r ^ (ordinaryReflectionLine r - 1 / 2) ≤ 1 := by
  by_cases h : r ≤ 1
  · simp only [ordinaryReflectionLine, if_pos h]
    refine ⟨by simp, by norm_num, by norm_num, ?_⟩
    exact Real.rpow_le_one hr.le h (by norm_num)
  · simp only [ordinaryReflectionLine, if_neg h]
    refine ⟨by simp, by norm_num, by norm_num, ?_⟩
    exact Real.rpow_le_one_of_one_le_of_nonpos (le_of_not_ge h) (by norm_num)

end HeckeSkeleton.Moments.EngineInduction
