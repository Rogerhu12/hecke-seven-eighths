import HeckeSkeleton.HeckeConductorNorm
import Mathlib.Tactic

/-!
The conductor-power budget for the actual high-row L-ratio.
All characters may be arbitrary continuous unitary Hecke characters.
No analytic estimate is assumed. The sole row-arithmetic premise is the
explicit upper bound Q_chi <= A*R, to be supplied by the actual Kummer
conductor theorem. R can remain the actual radical norm throughout.

The final form retains the factor (R/N)^(lambda+2epsilon); replacing it
by one would discard the conductor-deficit saving and is not done here.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.HeckeLRatioConductorBudget

open NumberField IsDedekindDomain
open HeckeGeneral.Characters
open HeckeSkeleton.ExplicitHeckeFunctionalEquation HeckeSkeleton.HeckeConductorNorm

variable (K : Type) [Field K] [NumberField K]

/-- This constant depends on the background, A and epsilon, and not on the
varying character, the radical norm or the contour exponent lambda. -/
def backgroundConductorBudget (ψ : HeckeCharacter K) (A ε : ℝ) : ℝ :=
  ((finiteConductor K ψ).val.absNorm : ℝ) ^ ε * A ^ (1 + 2 * ε)

theorem backgroundConductorBudget_pos (ψ : HeckeCharacter K)
    (A ε : ℝ) (hA : 1 ≤ A) : 0 < backgroundConductorBudget K ψ A ε := by
  have hf : 0 < ((finiteConductor K ψ).val.absNorm : ℝ) :=
    Nat.cast_pos.mpr (Ideal.absNorm_pos_of_nonZeroDivisors (finiteConductor K ψ))
  exact mul_pos (Real.rpow_pos_of_pos hf _)
    (Real.rpow_pos_of_pos (zero_lt_one.trans_le hA) _)

/-- The three actual FE/buffered scale powers cost only the radical norm,
with a background constant independent of chi, lambda and R. -/
theorem conductorPowers_le_radicalPower
    (ψ χ : HeckeCharacter K) (A R lam ε : ℝ)
    (hA : 1 ≤ A) (hR : 1 ≤ R) (hlam : 0 ≤ lam) (hlamone : lam ≤ 1)
    (hε : 0 < ε) (hQ : heckeConductorScale K χ ≤ A * R) :
    heckeConductorScale K χ ^ lam * heckeConductorScale K χ⁻¹ ^ ε *
        heckeConductorScale K (ψ * conjugate χ) ^ ε ≤
      backgroundConductorBudget K ψ A ε * R ^ (lam + 2 * ε) := by
  have hq : 0 < heckeConductorScale K χ := conductorScale_pos K χ
  have hf : 0 < ((finiteConductor K ψ).val.absNorm : ℝ) :=
    Nat.cast_pos.mpr (Ideal.absNorm_pos_of_nonZeroDivisors (finiteConductor K ψ))
  have ha : 0 < A := zero_lt_one.trans_le hA
  have hr : 0 < R := zero_lt_one.trans_le hR
  have hsum : 0 ≤ lam + 2 * ε := by linarith
  have hbg : heckeConductorScale K (ψ * conjugate χ) ^ ε ≤
      ((finiteConductor K ψ).val.absNorm : ℝ) ^ ε * heckeConductorScale K χ ^ ε := by
    have hh := Real.rpow_le_rpow (conductorScale_pos K (ψ * conjugate χ)).le
      (conductorScale_mul_conjugate_le K ψ χ) hε.le
    rwa [Real.mul_rpow hf.le hq.le] at hh
  have hApow : A ^ (lam + 2 * ε) ≤ A ^ (1 + 2 * ε) :=
    Real.rpow_le_rpow_of_exponent_le hA (by linarith)
  rw [conductorScale_inv]
  calc
    _ ≤ (heckeConductorScale K χ ^ lam * heckeConductorScale K χ ^ ε) *
        (((finiteConductor K ψ).val.absNorm : ℝ) ^ ε * heckeConductorScale K χ ^ ε) :=
      mul_le_mul_of_nonneg_left hbg (by positivity)
    _ = ((finiteConductor K ψ).val.absNorm : ℝ) ^ ε *
        heckeConductorScale K χ ^ (lam + 2 * ε) := by
      rw [show lam + 2 * ε = (lam + ε) + ε by ring,
        Real.rpow_add hq, Real.rpow_add hq]
      ring
    _ ≤ ((finiteConductor K ψ).val.absNorm : ℝ) ^ ε * (A * R) ^ (lam + 2 * ε) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hq.le hQ hsum)
        (Real.rpow_nonneg hf.le _)
    _ = (((finiteConductor K ψ).val.absNorm : ℝ) ^ ε * A ^ (lam + 2 * ε)) *
        R ^ (lam + 2 * ε) := by
      rw [Real.mul_rpow ha.le hr.le]
      ring
    _ ≤ (((finiteConductor K ψ).val.absNorm : ℝ) ^ ε * A ^ (1 + 2 * ε)) *
        R ^ (lam + 2 * ε) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hApow (Real.rpow_nonneg hf.le _))
          (Real.rpow_nonneg hr.le _)
    _ = _ := rfl

/-- The quantifier order makes the character-uniform constant explicit. -/
theorem exists_uniform_conductorPower_budget
    (ψ : HeckeCharacter K) (A ε : ℝ) (hA : 1 ≤ A) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ C = backgroundConductorBudget K ψ A ε ∧
      ∀ (χ : HeckeCharacter K) (R lam : ℝ), 1 ≤ R → 0 ≤ lam → lam ≤ 1 →
      heckeConductorScale K χ ≤ A * R →
      heckeConductorScale K χ ^ lam * heckeConductorScale K χ⁻¹ ^ ε *
          heckeConductorScale K (ψ * conjugate χ) ^ ε ≤ C * R ^ (lam + 2 * ε) := by
  refine ⟨backgroundConductorBudget K ψ A ε,
    backgroundConductorBudget_pos K ψ A ε hA, rfl, ?_⟩
  intro χ R lam hR hlam hlamone hQ
  exact conductorPowers_le_radicalPower K ψ χ A R lam ε hA hR hlam hlamone hε hQ

/-- Retain the exact radical-to-row norm deficit, together with its bound
by one. This is an algebraic consequence of the actual-scale budget. -/
theorem conductorPowers_le_with_radicalDeficit
    (ψ χ : HeckeCharacter K) (A R N lam ε : ℝ)
    (hA : 1 ≤ A) (hR : 1 ≤ R) (hN : 0 < N) (hRN : R ≤ N)
    (hlam : 0 ≤ lam) (hlamone : lam ≤ 1) (hε : 0 < ε)
    (hQ : heckeConductorScale K χ ≤ A * R) :
    (heckeConductorScale K χ ^ lam * heckeConductorScale K χ⁻¹ ^ ε *
        heckeConductorScale K (ψ * conjugate χ) ^ ε ≤
      backgroundConductorBudget K ψ A ε * N ^ (lam + 2 * ε) *
        (R / N) ^ (lam + 2 * ε)) ∧
      (R / N) ^ (lam + 2 * ε) ≤ 1 := by
  have hr : 0 ≤ R := zero_le_one.trans hR
  have hidentity : N ^ (lam + 2 * ε) * (R / N) ^ (lam + 2 * ε) =
      R ^ (lam + 2 * ε) := by
    rw [← Real.mul_rpow hN.le (div_nonneg hr hN.le)]
    congr 1
    field_simp [hN.ne'] <;> ring
  refine ⟨(conductorPowers_le_radicalPower K ψ χ A R lam ε hA hR hlam hlamone hε hQ).trans_eq
    ?_, ?_⟩
  · calc
      backgroundConductorBudget K ψ A ε * R ^ (lam + 2 * ε) =
          backgroundConductorBudget K ψ A ε *
            (N ^ (lam + 2 * ε) * (R / N) ^ (lam + 2 * ε)) := by rw [hidentity]
      _ = _ := by ring
  · apply Real.rpow_le_one (div_nonneg hr hN.le)
    · exact (div_le_iff₀ hN).mpr (by simpa using hRN)
    · linarith

end HeckeSkeleton.HeckeLRatioConductorBudget
