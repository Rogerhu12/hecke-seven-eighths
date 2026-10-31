import HeckeSkeleton.Moments.MOM_PRIME.ExceptionalHecke

/-!
# One exceptional-terminal constant for a finite Hecke family

The manuscript uses finitely many fixed backgrounds `ω₀ * θ`. The theorem
below takes the genuine volume/profile inputs for that finite family and
chooses a single constant and a single height order before the character,
the profiles, the radical and the scales. Empty finite families are allowed.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_PRIME

open NumberField HeckeGeneral.Characters
open HeckePort.CenteredMomentVolume
open scoped Classical BigOperators

variable {K : Type*} [Field K] [NumberField K]

/-- Uniformity over the finite fixed-background family, including the
empty-family case and unequal height orders among its members. -/
theorem hecke_exceptional_finite_family {β ι : Type*} [Fintype β]
    (χ : β → HeckeCharacter K)
    (V : ∀ k, IdealVolumeInput K (heckeExceptionalCharacter K (χ k)))
    (F : ∀ k, ExceptionalProfiles (V k) ι)
    (ε B : ℝ) (hε : 0 < ε) (hB : 0 ≤ B) :
    ∃ N : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 ≤ Z →
      ∀ R : Ideal (𝓞 K), R ≠ ⊥ → (Ideal.absNorm R : ℝ) ≤ Z ^ B →
      ∀ k i j t X₁ X₂ Y₁ Y₂ T a, 0 ≤ a →
      Z ^ a ≤ X₁ → Z ^ a ≤ X₂ → Z ^ a ≤ Y₁ → Z ^ a ≤ Y₂ →
      X₁ * X₂ = T → Y₁ * Y₂ = T →
      ‖(Real.sqrt T : ℂ)⁻¹ *
        (heckeExceptionalSum K (χ k) R ((F k).weight i) t X₁ *
            heckeExceptionalSum K (χ k) R ((F k).weight j) t X₂ -
          heckeExceptionalSum K (χ k) R ((F k).weight i) t Y₁ *
            heckeExceptionalSum K (χ k) R ((F k).weight j) t Y₂)‖ ≤
        C * Z ^ ε * Real.sqrt T * Z ^ (-a) *
          ((F k).seminorm i + (F k).seminorm j) ^ 2 * (1 + ‖t‖) ^ N := by
  let C₀ (k : β) : ℝ := Classical.choose
    (hecke_exceptional_equal_product (χ k) (V k) (F k) ε B hε hB)
  have hC₀ (k : β) : 0 < C₀ k := (Classical.choose_spec
    (hecke_exceptional_equal_product (χ k) (V k) (F k) ε B hε hB)).1
  let C : ℝ := 1 + ∑ k : β, C₀ k
  let N : ℕ := ∑ k : β, (F k).order
  have hsum : 0 ≤ ∑ k : β, C₀ k := Finset.sum_nonneg (fun k _ => (hC₀ k).le)
  have hC : 0 < C := by dsimp only [C]; linarith
  refine ⟨N, C, hC, ?_⟩
  intro Z hZ R hR hnorm k i j t X₁ X₂ Y₁ Y₂ T a ha hX₁ hX₂ hY₁ hY₂ hpX hpY
  have hbound := (Classical.choose_spec
    (hecke_exceptional_equal_product (χ k) (V k) (F k) ε B hε hB)).2
      Z hZ R hR hnorm i j t X₁ X₂ Y₁ Y₂ T a ha hX₁ hX₂ hY₁ hY₂ hpX hpY
  have hcoeff : C₀ k ≤ C := by
    have hs : C₀ k ≤ ∑ l : β, C₀ l := Finset.single_le_sum
      (fun l _ => (hC₀ l).le) (Finset.mem_univ k)
    dsimp only [C]
    linarith
  have hdegree : (F k).order ≤ N :=
    Finset.single_le_sum (fun l _ => Nat.zero_le ((F l).order)) (Finset.mem_univ k)
  have hheight : (1 + ‖t‖) ^ (F k).order ≤ (1 + ‖t‖) ^ N :=
    pow_le_pow_right₀ (by linarith [norm_nonneg t]) hdegree
  have hZn : 0 ≤ Z := zero_le_one.trans hZ
  have hz : 0 ≤ Z ^ ε := Real.rpow_nonneg hZn _
  have hza : 0 ≤ Z ^ (-a) := Real.rpow_nonneg hZn _
  have hsqrt : 0 ≤ Real.sqrt T := Real.sqrt_nonneg T
  have hsq : 0 ≤ ((F k).seminorm i + (F k).seminorm j) ^ 2 := sq_nonneg _
  have hbase : C₀ k * Z ^ ε * Real.sqrt T * Z ^ (-a) *
      ((F k).seminorm i + (F k).seminorm j) ^ 2 ≤
      C * Z ^ ε * Real.sqrt T * Z ^ (-a) *
        ((F k).seminorm i + (F k).seminorm j) ^ 2 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoeff hz) hsqrt) hza) hsq
  exact hbound.trans (mul_le_mul hbase hheight (by positivity)
    (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC.le hz) hsqrt) hza) hsq))

end HeckeSkeleton.Moments.MOM_PRIME
