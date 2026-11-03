import HeckeSkeleton.LowEnergy.KeepOriginalRow
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# The two-divisor weighted normal form on actual integral ideals

The equality proved here is before all norm estimates. Its hypotheses are
the finite Möbius formula and multiplicativity of the cubic kernel. The
quadratic row is unchanged. The original reconstructed coefficient can
retain every support and coprimality condition in `beta`.
-/

namespace HeckeSkeleton.LowEnergy.KeepOriginalRow

open NumberField Ideal
open scoped BigOperators NumberField Classical
noncomputable section

variable {K : Type*} [Field K] [NumberField K]

theorem masked_columns_reindex
    (k : Ideal (𝓞 K)) (ds ps cs : Finset (Ideal (𝓞 K)))
    (mu : Ideal (𝓞 K) → ℂ)
    (hmask : ∀ n, mask k n = ∑ D ∈ ds, if D ∣ n then mu D else 0)
    (F : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ) :
    (∑ P ∈ ps, ∑ c ∈ cs, mask k P * mask k c * F P c) =
      ∑ D ∈ ds, ∑ r ∈ ds, mu D * mu r *
        ∑ P ∈ quotientSupport D ps, ∑ c ∈ quotientSupport r cs, F (D * P) (r * c) := by
  classical
  have hexpand (P c : Ideal (𝓞 K)) :
      mask k P * mask k c =
        ∑ D ∈ ds, ∑ r ∈ ds, if D ∣ P ∧ r ∣ c then mu D * mu r else 0 := by
    rw [hmask, hmask, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro D hD
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    by_cases hDP : D ∣ P <;> by_cases hrc : r ∣ c <;> simp [hDP, hrc]
  simp_rw [hexpand, Finset.sum_mul]
  calc
    _ = ∑ P ∈ ps, ∑ D ∈ ds, ∑ c ∈ cs, ∑ r ∈ ds,
        (if D ∣ P ∧ r ∣ c then mu D * mu r else 0) * F P c := by
      apply Finset.sum_congr rfl
      intro P hP
      exact Finset.sum_comm
    _ = ∑ D ∈ ds, ∑ P ∈ ps, ∑ c ∈ cs, ∑ r ∈ ds,
        (if D ∣ P ∧ r ∣ c then mu D * mu r else 0) * F P c := Finset.sum_comm
    _ = ∑ D ∈ ds, ∑ r ∈ ds, ∑ P ∈ ps, ∑ c ∈ cs,
        (if D ∣ P ∧ r ∣ c then mu D * mu r else 0) * F P c := by
      apply Finset.sum_congr rfl
      intro D hD
      calc
        _ = ∑ P ∈ ps, ∑ r ∈ ds, ∑ c ∈ cs,
            (if D ∣ P ∧ r ∣ c then mu D * mu r else 0) * F P c := by
          apply Finset.sum_congr rfl
          intro P hP
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro D hD
      apply Finset.sum_congr rfl
      intro r hr
      rw [← double_column_reindex ps cs D r F, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro P hP
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c hc
      split_ifs <;> simp

theorem three_by_two_sum_order
    {T C M H P : Type*} (ts : Finset T) (cs : Finset C) (ms : Finset M)
    (hs : Finset H) (ps : Finset P) (F : T → C → M → H → P → ℂ) :
    (∑ u ∈ ts ×ˢ (ms ×ˢ hs), ∑ p ∈ ps, ∑ c ∈ cs, F u.1 c u.2.1 u.2.2 p) =
      ∑ t ∈ ts, ∑ c ∈ cs, ∑ m ∈ ms, ∑ h ∈ hs, ∑ p ∈ ps, F t c m h p := by
  simp only [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro t ht
  calc
    _ = ∑ m ∈ ms, ∑ h ∈ hs, ∑ c ∈ cs, ∑ p ∈ ps, F t c m h p := by
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro h hh
      exact Finset.sum_comm
    _ = ∑ m ∈ ms, ∑ c ∈ cs, ∑ h ∈ hs, ∑ p ∈ ps, F t c m h p := by
      apply Finset.sum_congr rfl
      intro m hm
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

def blockBeta
    (cubic : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (beta : Ideal (𝓞 K) → Ideal (𝓞 K) → Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (D r t c m h : Ideal (𝓞 K)) : ℂ :=
  beta t (r * c) m h * cubic D ((r * c) * m) * mask D (h * t)

def blockColumn
    (cubic : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (a : Ideal (𝓞 K) → ℂ) (D r t h P : Ideal (𝓞 K)) : ℂ :=
  (a (D * P) * cubic P r * mask P (h * t)) /
    (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ)

/-- The finite row after exact square extraction and reduction of the cubic
collision mask, before the two Möbius expansions. -/
def reconstructedRow
    (cubic quad : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (ts cs ms hs ps : Finset (Ideal (𝓞 K)))
    (a : Ideal (𝓞 K) → ℂ)
    (beta : Ideal (𝓞 K) → Ideal (𝓞 K) → Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (k : Ideal (𝓞 K)) : ℂ :=
  ∑ u ∈ ts ×ˢ (ms ×ˢ hs), mask k u.1 * quad k (u.2.1 * u.2.2) *
    ∑ P ∈ ps, ∑ c ∈ cs, mask k P * mask k c *
      (a P / (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ) *
        beta u.1 c u.2.1 u.2.2 * cubic P (c * u.2.1) * mask P (u.2.2 * u.1))

/-- One actual weighted block. Its cubic column is `c*m`, while its
quadratic column is the different product `m*h`. -/
def extractedRow
    (cubic quad : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (ts cs ms hs ps : Finset (Ideal (𝓞 K)))
    (a : Ideal (𝓞 K) → ℂ)
    (beta : Ideal (𝓞 K) → Ideal (𝓞 K) → Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (D r k : Ideal (𝓞 K)) : ℂ :=
  ∑ t ∈ ts, ∑ c ∈ quotientSupport r cs, mask k t *
    (∑ m ∈ ms, ∑ h ∈ hs, quad k (m * h) *
      (blockBeta cubic beta D r t c m h *
        (∑ P ∈ quotientSupport D ps, blockColumn cubic a D r t h P * cubic P (c * m))))

theorem reconstructed_column_factorization
    (Ext : Ideal (𝓞 K) → Prop)
    (cubic : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (hmul_left : ∀ D P n, cubic (D * P) n = cubic D n * cubic P n)
    (hmul_right : ∀ P n m, Ext P → cubic P (n * m) = cubic P n * cubic P m)
    (a : Ideal (𝓞 K) → ℂ)
    (beta : Ideal (𝓞 K) → Ideal (𝓞 K) → Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (D r t c m h P : Ideal (𝓞 K)) (hP : Ext P) :
    a (D * P) / (Real.sqrt (Ideal.absNorm (D * P) : ℝ) : ℂ) *
      beta t (r * c) m h * cubic (D * P) ((r * c) * m) * mask (D * P) (h * t) =
      (1 / (Real.sqrt (Ideal.absNorm D : ℝ) : ℂ)) *
        blockBeta cubic beta D r t c m h *
        blockColumn cubic a D r t h P * cubic P (c * m) := by
  have hcubic : cubic P ((r * c) * m) = cubic P r * cubic P (c * m) := by
    rw [mul_assoc, hmul_right P r (c * m) hP]
  rw [normalized_product_coefficient, hmul_left, mask_mul_left, hcubic]
  unfold blockBeta blockColumn
  ring

/-- Literal two-divisor normal-form equality for actual ideal rows. No
normal-form equality or energy estimate is an input. -/
theorem reconstructedRow_eq_normalForm
    (Ext : Ideal (𝓞 K) → Prop)
    (cubic quad : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (hmul_left : ∀ D P n, cubic (D * P) n = cubic D n * cubic P n)
    (hmul_right : ∀ P n m, Ext P → cubic P (n * m) = cubic P n * cubic P m)
    (ts cs ms hs ps ds : Finset (Ideal (𝓞 K)))
    (a : Ideal (𝓞 K) → ℂ)
    (beta : Ideal (𝓞 K) → Ideal (𝓞 K) → Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (mu : Ideal (𝓞 K) → ℂ) (k : Ideal (𝓞 K))
    (hmask : ∀ n, mask k n = ∑ D ∈ ds, if D ∣ n then mu D else 0)
    (hExt : ∀ D ∈ ds, ∀ P ∈ quotientSupport D ps, Ext P) :
    reconstructedRow cubic quad ts cs ms hs ps a beta k =
      ∑ D ∈ ds, ∑ r ∈ ds, mu D * mu r *
        ((1 / (Real.sqrt (Ideal.absNorm D : ℝ) : ℂ)) *
          extractedRow cubic quad ts cs ms hs ps a beta D r k) := by
  classical
  let us := ts ×ˢ (ms ×ˢ hs)
  let F := fun (u : Ideal (𝓞 K) × (Ideal (𝓞 K) × Ideal (𝓞 K)))
    (P c : Ideal (𝓞 K)) =>
      a P / (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ) *
        beta u.1 c u.2.1 u.2.2 * cubic P (c * u.2.1) * mask P (u.2.2 * u.1)
  have hlocal (u : Ideal (𝓞 K) × (Ideal (𝓞 K) × Ideal (𝓞 K))) :=
    masked_columns_reindex k ds ps cs mu hmask (F u)
  unfold reconstructedRow
  change (∑ u ∈ us, mask k u.1 * quad k (u.2.1 * u.2.2) *
    ∑ P ∈ ps, ∑ c ∈ cs, mask k P * mask k c * F u P c) = _
  simp_rw [hlocal]
  calc
    _ = ∑ u ∈ us, ∑ D ∈ ds, ∑ r ∈ ds,
        mask k u.1 * quad k (u.2.1 * u.2.2) * (mu D * mu r *
          ∑ P ∈ quotientSupport D ps, ∑ c ∈ quotientSupport r cs, F u (D * P) (r * c)) := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro D hD
      rw [Finset.mul_sum]
    _ = ∑ D ∈ ds, ∑ r ∈ ds, ∑ u ∈ us,
        mask k u.1 * quad k (u.2.1 * u.2.2) * (mu D * mu r *
          ∑ P ∈ quotientSupport D ps, ∑ c ∈ quotientSupport r cs, F u (D * P) (r * c)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro D hD
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro D hD
      apply Finset.sum_congr rfl
      intro r hr
      let w : ℂ := 1 / (Real.sqrt (Ideal.absNorm D : ℝ) : ℂ)
      have hterm (u : Ideal (𝓞 K) × (Ideal (𝓞 K) × Ideal (𝓞 K)))
          (P : Ideal (𝓞 K)) (hP : P ∈ quotientSupport D ps) (c : Ideal (𝓞 K)) :
          F u (D * P) (r * c) = w *
            blockBeta cubic beta D r u.1 c u.2.1 u.2.2 *
            blockColumn cubic a D r u.1 u.2.2 P * cubic P (c * u.2.1) :=
        reconstructed_column_factorization Ext cubic hmul_left hmul_right a beta
          D r u.1 c u.2.1 u.2.2 P (hExt D hD P hP)
      have heq :
          (∑ u ∈ us, mask k u.1 * quad k (u.2.1 * u.2.2) *
            (mu D * mu r * ∑ P ∈ quotientSupport D ps, ∑ c ∈ quotientSupport r cs,
              F u (D * P) (r * c))) =
          mu D * mu r * w *
            (∑ u ∈ us, ∑ P ∈ quotientSupport D ps, ∑ c ∈ quotientSupport r cs,
              mask k u.1 * quad k (u.2.1 * u.2.2) *
                blockBeta cubic beta D r u.1 c u.2.1 u.2.2 *
                blockColumn cubic a D r u.1 u.2.2 P * cubic P (c * u.2.1)) := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro u hu
        apply Finset.sum_congr rfl
        intro P hP
        apply Finset.sum_congr rfl
        intro c hc
        rw [hterm u P hP c]
        ring
      rw [heq]
      rw [show us = ts ×ˢ (ms ×ˢ hs) from rfl,
        three_by_two_sum_order ts (quotientSupport r cs) ms hs (quotientSupport D ps)
          (fun t c m h P => mask k t * quad k (m * h) *
            blockBeta cubic beta D r t c m h * blockColumn cubic a D r t h P *
              cubic P (c * m))]
      unfold extractedRow
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t ht
      apply Finset.sum_congr rfl
      intro c hc
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro h hh
      apply Finset.sum_congr rfl
      intro P hP
      dsimp only [w]
      ring

#print axioms masked_columns_reindex
#print axioms reconstructed_column_factorization
#print axioms reconstructedRow_eq_normalForm

end
end HeckeSkeleton.LowEnergy.KeepOriginalRow
