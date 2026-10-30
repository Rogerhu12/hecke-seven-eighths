import HeckeSkeleton.HighBinSupport.ValuationSeries
import HeckeSkeleton.HighBinSupport.UnramifiedFiniteTable
import HeckeGeneral.Analysis.RowEulerRational

/-!
# Exact local factorization after summing the valuation table

The mark removes precisely the completed-unit term. Both identities retain
zeros of the finite numerator and divide only by the geometric denominators
which are nonzero on the original domain of absolute convergence.

AI-assisted: ChatGPT / GPT-6 Astra Pro, 2026-10-31.
-/

set_option autoImplicit false
noncomputable section
namespace HighBin.LocalSeriesFactorization

open HighBin.FiniteLocalTable HighBin.ValuationSeries HighBin.UnramifiedFiniteTable
open HeckeGeneral.ThetaSkeleton.Physical

private theorem cancel_scale (A B C T : ℂ) (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) :
    C / (A * B) * (T * A * B / C) = T := by
  field_simp [hA, hB, hC] <;> ring

private theorem cancel_unit (V W D : ℂ)
    (hV : 1 - V ≠ 0) (hW : 1 - W ≠ 0) (hD : 1 - D ≠ 0) :
    (1 - D) / ((1 - V) * (1 - W)) * ((1 - W * V) / (1 - D)) =
      1 / (1 - V) + W / (1 - W) := by
  field_simp [hV, hW, hD]
  ring

theorem regular (q θ : ℂ) (G : ℕ → ℂ) (ρ X Y V : ℂ)
    (hq : q ≠ 0) (hρ : ρ ^ 6 = 1)
    (hV : ‖V‖ < 1) (hR : ‖ratio q θ X V‖ < 1)
    (hW : 1 - ρ * Y ≠ 0) (hD : 1 - eta q θ G * ρ⁻¹ * X ≠ 0)
    (hG : G 1 * G 5 = q) (marked : Bool) :
    (if marked then 0 else 1 / (1 - V) + (ρ * Y) / (1 - ρ * Y)) +
        markedSeries q θ G ρ X Y V 0 =
      (1 - eta q θ G * ρ⁻¹ * X) / ((1 - V) * (1 - ρ * Y)) *
        (rowEulerRationalValue q q⁻¹ V (ρ * Y) (eta q θ G * ρ⁻¹ * X)
            (ratio q θ X V) -
          if marked then (1 - (ρ * Y) * V) / (1 - eta q θ G * ρ⁻¹ * X) else 0) := by
  have hV0 : 1 - V ≠ 0 := by
    intro h
    have h' : V = 1 := (sub_eq_zero.mp h).symm
    simpa [h'] using hV
  have hR0 : 1 - ratio q θ X V ≠ 0 := by
    intro h
    have h' : ratio q θ X V = 1 := (sub_eq_zero.mp h).symm
    simpa [h'] using hR
  have hs := regular_base_identification q θ G ρ X Y V hq hρ hV0 hR0 hG
  rw [← markedSeries_eq_base q θ G ρ X Y V hq hρ hV hR 0 (by norm_num)] at hs
  have hc := rowEulerLiteral_eq_rational q q⁻¹ V (ρ * Y)
    (eta q θ G * ρ⁻¹ * X) (ratio q θ X V) hV0 hW hR0 hD
  have hf :
      (1 - eta q θ G * ρ⁻¹ * X) / ((1 - V) * (1 - ρ * Y)) *
        rowEulerRationalValue q q⁻¹ V (ρ * Y) (eta q θ G * ρ⁻¹ * X)
          (ratio q θ X V) =
      1 / (1 - V) + (ρ * Y) / (1 - ρ * Y) + markedSeries q θ G ρ X Y V 0 := by
    rw [hs, ← hc]
    simpa only [regularSeriesValue, one_div] using
      cancel_scale (1 - V) (1 - ρ * Y) (1 - eta q θ G * ρ⁻¹ * X)
        (regularSeriesValue q (ratio q θ X V) V (ρ * Y) (eta q θ G * ρ⁻¹ * X))
        hV0 hW hD
  have hu :
      (1 - eta q θ G * ρ⁻¹ * X) / ((1 - V) * (1 - ρ * Y)) *
        ((1 - (ρ * Y) * V) / (1 - eta q θ G * ρ⁻¹ * X)) =
      1 / (1 - V) + (ρ * Y) / (1 - ρ * Y) :=
    cancel_unit V (ρ * Y) (eta q θ G * ρ⁻¹ * X) hV0 hW hD
  cases marked
  · simpa only [Bool.false_eq_true, if_false, sub_zero] using hf.symm
  · simp only [if_true, zero_add]
    rw [mul_sub, hf, hu]
    ring

theorem ramified (q θ : ℂ) (G : ℕ → ℂ) (ρ X Y V : ℂ)
    (hq : q ≠ 0) (hρ : ρ ^ 6 = 1)
    (hV : ‖V‖ < 1) (hR : ‖ratio q θ X V‖ < 1)
    (j : Fin 5) (marked : Bool) :
    (if marked then 0 else 1 / (1 - V)) +
        markedSeries q θ G ρ X Y V (j.val + 1) =
      1 / (1 - V) * (finiteTableCorrection q θ G ρ X Y V j -
        if marked then 1 else 0) := by
  have hV0 : 1 - V ≠ 0 := by
    intro h
    have h' : V = 1 := (sub_eq_zero.mp h).symm
    simpa [h'] using hV
  rw [← ramifiedSeries_eq_finiteTable q θ G ρ X Y V hq hρ hV hR j]
  cases marked <;> simp only [Bool.false_eq_true, if_false, if_true, zero_add, sub_zero]
  all_goals field_simp [hV0] <;> ring

#print axioms regular
#print axioms ramified

end HighBin.LocalSeriesFactorization
