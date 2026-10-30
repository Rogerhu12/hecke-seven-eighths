import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.NormNum

/-!
# Descent through a finite meromorphic factorization

This file proves the local analytic step in the manuscript's abelian descent.
It uses actual mathlib meromorphic orders, including at poles. The arithmetic
factorization, pole classification, and simplicity of the norm-character pole
remain separate obligations when applying these lemmas to Hecke L-functions.
-/

namespace HeckeGeneral.Analysis

noncomputable section

open scoped BigOperators Topology
open Filter

variable {ι : Type*} {z : ℂ}

/-- At a regular point, order zero is precisely nonvanishing. -/
theorem analytic_ne_zero_of_order_eq_zero {f : ℂ → ℂ}
    (hf : AnalyticAt ℂ f z) (ho : meromorphicOrderAt f z = 0) : f z ≠ 0 := by
  apply hf.analyticOrderAt_eq_zero.mp
  rw [hf.meromorphicOrderAt_eq] at ho
  cases h : analyticOrderAt f z with
  | top => simp [h] at ho
  | coe n =>
    have hn : n = 0 := by simpa [h] using ho
    simp [hn]

/-- Every nonnegative summand in a nonpositive sum of orders must be zero. -/
theorem order_eq_zero_of_nonneg_sum_nonpos (s : Finset ι) (a : ι → WithTop ℤ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hs : ∑ i ∈ s, a i ≤ 0) {i : ι} (hi : i ∈ s) :
    a i = 0 := by
  exact le_antisymm ((Finset.single_le_sum ha hi).trans hs) (ha i hi)

/-- A distinguished finite order can be cancelled from a finite sum.
The remaining nonnegative orders are then all zero. -/
theorem other_orders_zero_of_sum_eq [DecidableEq ι]
    (s : Finset ι) (a : ι → WithTop ℤ) {p : ι} (hp : p ∈ s)
    (hfinite : a p ≠ ⊤) (hsum : ∑ i ∈ s, a i = a p)
    (ha : ∀ i ∈ s, i ≠ p → 0 ≤ a i) {i : ι} (hi : i ∈ s) (hip : i ≠ p) :
    a i = 0 := by
  have hcancel : a p + ∑ j ∈ s.erase p, a j = a p + 0 := by
    calc
      a p + ∑ j ∈ s.erase p, a j = (∑ j ∈ s.erase p, a j) + a p := add_comm _ _
      _ = ∑ j ∈ s, a j := Finset.sum_erase_add _ _ hp
      _ = a p + 0 := by simpa using hsum
  have hzero : ∑ j ∈ s.erase p, a j = 0 :=
    WithTop.add_left_cancel hfinite hcancel
  apply order_eq_zero_of_nonneg_sum_nonpos (s.erase p) a
  · intro j hj
    exact ha j (Finset.mem_erase.mp hj).2 (Finset.mem_erase.mp hj).1
  · exact hzero.le
  · exact Finset.mem_erase.mpr ⟨hip, hi⟩

/-- No regular factor can vanish when the product has the same order as the
unique possible pole. This includes the simple-pole case of abelian descent. -/
theorem regular_factors_nonzero_of_same_pole_order [DecidableEq ι]
    (s : Finset ι) (f : ι → ℂ → ℂ) {p : ι} (hp : p ∈ s)
    (hf : ∀ i ∈ s, MeromorphicAt (f i) z)
    (hregular : ∀ i ∈ s, i ≠ p → AnalyticAt ℂ (f i) z)
    (hfinite : meromorphicOrderAt (f p) z ≠ ⊤)
    (horder : meromorphicOrderAt (fun w => ∏ i ∈ s, f i w) z =
      meromorphicOrderAt (f p) z)
    {i : ι} (hi : i ∈ s) (hip : i ≠ p) : f i z ≠ 0 := by
  apply analytic_ne_zero_of_order_eq_zero (hregular i hi hip)
  apply other_orders_zero_of_sum_eq s (fun j => meromorphicOrderAt (f j) z)
    hp hfinite
  · rwa [meromorphicOrderAt_fun_prod hf] at horder
  · intro j hj hjp
    exact (hregular j hj hjp).meromorphicOrderAt_nonneg
  · exact hi
  · exact hip

/-- Local form of the descent argument, with both regular and pole cases
stated explicitly. `hfactor` is equality of meromorphic germs, not equality
of arbitrary values assigned at poles. -/
theorem factors_order_nonpos_of_factorization [DecidableEq ι]
    (s : Finset ι) (f : ι → ℂ → ℂ) (F : ℂ → ℂ)
    (hf : ∀ i ∈ s, MeromorphicAt (f i) z)
    (hfactor : F =ᶠ[𝓝[≠] z] (fun w => ∏ i ∈ s, f i w))
    (hF : meromorphicOrderAt F z ≤ 0)
    (hpoles : (∀ i ∈ s, AnalyticAt ℂ (f i) z) ∨
      ∃ p ∈ s, meromorphicOrderAt (f p) z = (-1 : ℤ) ∧
        meromorphicOrderAt F z = (-1 : ℤ) ∧
        ∀ i ∈ s, i ≠ p → AnalyticAt ℂ (f i) z) :
    ∀ i ∈ s, meromorphicOrderAt (f i) z ≤ 0 := by
  have hsum : meromorphicOrderAt F z = ∑ i ∈ s, meromorphicOrderAt (f i) z := by
    rw [meromorphicOrderAt_congr hfactor, meromorphicOrderAt_fun_prod hf]
  rcases hpoles with hregular | ⟨p, hp, hporder, hForder, hregular⟩
  · intro i hi
    exact (order_eq_zero_of_nonneg_sum_nonpos s _
      (fun j hj => (hregular j hj).meromorphicOrderAt_nonneg) (hsum ▸ hF) hi).le
  · intro i hi
    by_cases hip : i = p
    · subst i
      rw [hporder]
      exact WithTop.coe_le_coe.mpr (by decide : (-1 : ℤ) ≤ 0)
    · have hzero : meromorphicOrderAt (f i) z = 0 := by
        apply other_orders_zero_of_sum_eq s (fun j => meromorphicOrderAt (f j) z) hp
        · rw [hporder]
          exact WithTop.coe_ne_top
        · rw [← hsum, hForder, hporder]
        · intro j hj hjp
          exact (hregular j hj hjp).meromorphicOrderAt_nonneg
        · exact hi
        · exact hip
      exact hzero.le

/-- A convention for genuine zero-freeness which permits poles.
Meromorphicity is included so the fallback order of a nonmeromorphic function
cannot make this proposition hold accidentally. -/
def MeromorphicZeroFreeOn (f : ℂ → ℂ) (U : Set ℂ) : Prop :=
  MeromorphicOn f U ∧ ∀ z ∈ U, meromorphicOrderAt f z ≤ 0

theorem MeromorphicZeroFreeOn.ne_zero {f : ℂ → ℂ} {U : Set ℂ}
    (h : MeromorphicZeroFreeOn f U) (hz : z ∈ U) (hregular : AnalyticAt ℂ f z) :
    f z ≠ 0 :=
  analytic_ne_zero_of_order_eq_zero hregular
    (le_antisymm (h.2 z hz) hregular.meromorphicOrderAt_nonneg)

/-- Global analytic descent. A Hecke application must supply the genuine
abelian factorization and pole classification at every point of `U`. -/
theorem meromorphicZeroFreeOn_of_factorization [DecidableEq ι]
    (S : Finset ι) (f : ι → ℂ → ℂ) (F : ℂ → ℂ) (U : Set ℂ)
    (hf : ∀ i ∈ S, MeromorphicOn (f i) U)
    (hF : MeromorphicZeroFreeOn F U)
    (hfactor : ∀ z ∈ U, F =ᶠ[𝓝[≠] z] (fun w => ∏ i ∈ S, f i w))
    (hpoles : ∀ z ∈ U, (∀ i ∈ S, AnalyticAt ℂ (f i) z) ∨
      ∃ p ∈ S, meromorphicOrderAt (f p) z = (-1 : ℤ) ∧
        meromorphicOrderAt F z = (-1 : ℤ) ∧
        ∀ i ∈ S, i ≠ p → AnalyticAt ℂ (f i) z)
    {i : ι} (hi : i ∈ S) : MeromorphicZeroFreeOn (f i) U := by
  refine ⟨hf i hi, ?_⟩
  intro z hz
  exact factors_order_nonpos_of_factorization S f F
    (fun j hj => hf j hj z hz) (hfactor z hz) (hF.2 z hz) (hpoles z hz) i hi

end

end HeckeGeneral.Analysis
