import CubicSieve.CoprimeGramGeneral

/-! Finite coprime Gram contraction for two independent coefficient vectors.
This is the exact prefix-mask interface used by two-column profile transfer.
-/

set_option autoImplicit false
noncomputable section
namespace CubicSieve.CoprimeBilinear
open scoped Classical BigOperators

variable {m n P : Type*} [Fintype m] [Fintype n] [DecidableEq P]

def row (s : n → Finset P) (A : m → n → ℂ) (x y : n → ℂ) (i : m) : ℂ :=
  ∑ j, ∑ k, if Disjoint (s j) (s k) then (A i j * x j) * star (A i k * y k) else 0

theorem budget_bound (s : n → Finset P) (A : m → n → ℂ)
    (U D E : ℝ) (hU : 0 ≤ U) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hcost : ∀ j, (2 : ℝ) ^ (s j).card ≤ D)
    (hA : ∀ z : n → ℂ, (∑ i, ‖∑ j, A i j * z j‖ ^ 2) ≤ U * ∑ j, ‖z j‖ ^ 2)
    (x y : n → ℂ) (hx : (∑ j, ‖x j‖ ^ 2) ≤ E) (hy : (∑ j, ‖y j‖ ^ 2) ≤ E) :
    (∑ i, ‖row s A x y i‖) ≤ U * D * E := by
  let X := ∑ j, (2 : ℝ) ^ (s j).card * ‖x j‖ ^ 2
  let Y := ∑ j, (2 : ℝ) ^ (s j).card * ‖y j‖ ^ 2
  have hX0 : 0 ≤ X := Finset.sum_nonneg (fun _ _ => mul_nonneg (by positivity) (sq_nonneg _))
  have hY0 : 0 ≤ Y := Finset.sum_nonneg (fun _ _ => mul_nonneg (by positivity) (sq_nonneg _))
  have hX : X ≤ D * E := by
    calc
      _ ≤ ∑ j, D * ‖x j‖ ^ 2 :=
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hcost j) (sq_nonneg _))
      _ = D * ∑ j, ‖x j‖ ^ 2 := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hx hD
  have hY : Y ≤ D * E := by
    calc
      _ ≤ ∑ j, D * ‖y j‖ ^ 2 :=
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hcost j) (sq_nonneg _))
      _ = D * ∑ j, ‖y j‖ ^ 2 := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hy hD
  have hsq := CubicSieve.CoprimeGram.General.coprime_bilinear_operator_bound
    s s A A U U hU hU hA hA x y
  have hbound : U * U * X * Y ≤ (U * D * E) ^ 2 := by
    calc
      _ = (U * X) * (U * Y) := by ring
      _ ≤ (U * (D * E)) * (U * (D * E)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hX hU)
          (mul_le_mul_of_nonneg_left hY hU) (mul_nonneg hU hY0)
          (mul_nonneg hU (mul_nonneg hD hE))
      _ = _ := by ring
  have hmass0 : 0 ≤ ∑ i, ‖row s A x y i‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hsq' : (∑ i, ‖row s A x y i‖) ^ 2 ≤ U * U * X * Y := by
    simpa only [row, X, Y] using hsq
  have hmain : (∑ i, ‖row s A x y i‖) ^ 2 ≤ (U * D * E) ^ 2 := hsq'.trans hbound
  exact (sq_le_sq₀ hmass0 (mul_nonneg (mul_nonneg hU hD) hE)).mp hmain

end CubicSieve.CoprimeBilinear
