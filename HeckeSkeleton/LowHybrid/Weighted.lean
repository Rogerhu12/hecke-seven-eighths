import HeckeSkeleton.LowHybrid.SieveComposition
import Mathlib.Analysis.Real.Sqrt

/-!
# Weighted quadratic--cubic composition without dyadic separation

The first Cauchy inequality acts on the joint `(t,c)` index. Its weights remain
inside the positive coefficient sum until the actual cube-support budget is
used. The quadratic and cubic assumptions are bounds for arbitrary
coefficients; in an ideal instantiation their constants include the two
product-fiber multiplicities and the kernels are extended by zero off their
squarefree product supports.
-/

namespace HeckeSkeleton.LowHybrid

open scoped BigOperators

noncomputable section

/-- Weighted finite Cauchy--Schwarz, with all weights strictly positive on
the actual summation set. -/
theorem weighted_sum_sq {I : Type*} (s : Finset I) (w : I → ℝ) (f : I → ℂ)
    (hw : ∀ i ∈ s, 0 < w i) :
    ‖∑ i ∈ s, f i‖ ^ 2 ≤
      (∑ i ∈ s, 1 / w i) * (∑ i ∈ s, w i * ‖f i‖ ^ 2) := by
  have hprod :
      (∑ i ∈ s, (1 / Real.sqrt (w i)) * (Real.sqrt (w i) * ‖f i‖)) =
        ∑ i ∈ s, ‖f i‖ := by
    apply Finset.sum_congr rfl
    intro i hi
    have hs : Real.sqrt (w i) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (hw i hi))
    field_simp [hs] <;> ring
  have hleft : (∑ i ∈ s, (1 / Real.sqrt (w i)) ^ 2) = ∑ i ∈ s, 1 / w i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [div_pow, one_pow, Real.sq_sqrt (le_of_lt (hw i hi))]
  have hright : (∑ i ∈ s, (Real.sqrt (w i) * ‖f i‖) ^ 2) =
      ∑ i ∈ s, w i * ‖f i‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [mul_pow, Real.sq_sqrt (le_of_lt (hw i hi))]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s
    (fun i => 1 / Real.sqrt (w i)) (fun i => Real.sqrt (w i) * ‖f i‖)
  rw [hprod, hleft, hright] at hcs
  exact (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2).trans hcs

/-- Weighted Cauchy in the row Hilbert space. The input bounds the weighted
energy of each frozen summand; no row-dependent coefficient is discarded. -/
theorem weighted_mixture_energy {K I : Type*}
    (rows : Finset K) (s : Finset I) (w : I → ℝ) (F : I → K → ℂ)
    (E : I → ℝ) (hw : ∀ i ∈ s, 0 < w i)
    (hE : ∀ i ∈ s, w i * (∑ k ∈ rows, ‖F i k‖ ^ 2) ≤ E i) :
    (∑ k ∈ rows, ‖∑ i ∈ s, F i k‖ ^ 2) ≤
      (∑ i ∈ s, 1 / w i) * (∑ i ∈ s, E i) := by
  have hW : 0 ≤ ∑ i ∈ s, 1 / w i := by
    apply Finset.sum_nonneg
    intro i hi
    exact le_of_lt (one_div_pos.mpr (hw i hi))
  calc
    _ ≤ ∑ k ∈ rows, (∑ i ∈ s, 1 / w i) * (∑ i ∈ s, w i * ‖F i k‖ ^ 2) := by
      exact Finset.sum_le_sum (fun k _ => weighted_sum_sq s w (fun i => F i k) hw)
    _ = (∑ i ∈ s, 1 / w i) * (∑ i ∈ s, w i * (∑ k ∈ rows, ‖F i k‖ ^ 2)) := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Finset.sum_le_sum hE) hW

/-- The two reciprocal weights factor exactly. -/
theorem reciprocal_grid_sum {T H : Type*}
    (ts : Finset T) (hs : Finset H) (wt : T → ℝ) (wh : H → ℝ) (R : ℝ)
    (hwt : ∀ t ∈ ts, 0 < wt t) (hwh : ∀ h ∈ hs, 0 < wh h) :
    (∑ t ∈ ts, ∑ h ∈ hs, R / (wt t * wh h)) =
      R * (∑ t ∈ ts, 1 / wt t) * (∑ h ∈ hs, 1 / wh h) := by
  calc
    _ = ∑ t ∈ ts, ∑ h ∈ hs, R * (1 / wt t) * (1 / wh h) := by
      apply Finset.sum_congr rfl
      intro t ht
      apply Finset.sum_congr rfl
      intro h hh
      field_simp [ne_of_gt (hwt t ht), ne_of_gt (hwh h hh)] <;> ring
    _ = (∑ t ∈ ts, R * (1 / wt t)) * (∑ h ∈ hs, 1 / wh h) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro t ht
      rw [Finset.mul_sum]
    _ = _ := by rw [← Finset.mul_sum]

private theorem sum_tcmh_swap {T C M H : Type*}
    (ts : Finset T) (cs : Finset C) (ms : Finset M) (hs : Finset H)
    (f : T → C → M → H → ℝ) :
    (∑ t ∈ ts, ∑ c ∈ cs, ∑ m ∈ ms, ∑ h ∈ hs, f t c m h) =
      ∑ t ∈ ts, ∑ h ∈ hs, ∑ m ∈ ms, ∑ c ∈ cs, f t c m h := by
  apply Finset.sum_congr rfl
  intro t ht
  calc
    (∑ c ∈ cs, ∑ m ∈ ms, ∑ h ∈ hs, f t c m h) =
        ∑ m ∈ ms, ∑ c ∈ cs, ∑ h ∈ hs, f t c m h := Finset.sum_comm
    _ = ∑ m ∈ ms, ∑ h ∈ hs, ∑ c ∈ cs, f t c m h := by
      apply Finset.sum_congr rfl
      intro m hm
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- Fubini after the quadratic step: the cubic row sum is kept joint in
`(m,c)`, while the reciprocal `t,h` factors remain outside it. -/
theorem weighted_cubic_total {T C M H : Type*}
    (ts : Finset T) (cs : Finset C) (ms : Finset M) (hs : Finset H)
    (wt : T → ℝ) (wh : H → ℝ) (E : T → H → M → C → ℝ)
    (R U : ℝ) (hR : 0 ≤ R)
    (hwt : ∀ t ∈ ts, 0 < wt t) (hwh : ∀ h ∈ hs, 0 < wh h)
    (hE : ∀ t ∈ ts, ∀ h ∈ hs, (∑ m ∈ ms, ∑ c ∈ cs, E t h m c) ≤ U) :
    (∑ t ∈ ts, ∑ c ∈ cs, ∑ m ∈ ms, ∑ h ∈ hs,
      (R / (wt t * wh h)) * E t h m c) ≤
        R * U * (∑ t ∈ ts, 1 / wt t) * (∑ h ∈ hs, 1 / wh h) := by
  calc
    _ = ∑ t ∈ ts, ∑ h ∈ hs, ∑ m ∈ ms, ∑ c ∈ cs,
        (R / (wt t * wh h)) * E t h m c := sum_tcmh_swap ts cs ms hs _
    _ = ∑ t ∈ ts, ∑ h ∈ hs,
        (R / (wt t * wh h)) * (∑ m ∈ ms, ∑ c ∈ cs, E t h m c) := by
      apply Finset.sum_congr rfl
      intro t ht
      apply Finset.sum_congr rfl
      intro h hh
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.mul_sum]
    _ ≤ ∑ t ∈ ts, ∑ h ∈ hs, (R / (wt t * wh h)) * U := by
      apply Finset.sum_le_sum
      intro t ht
      apply Finset.sum_le_sum
      intro h hh
      exact mul_le_mul_of_nonneg_left (hE t ht h hh)
        (div_nonneg hR (le_of_lt (mul_pos (hwt t ht) (hwh h hh))))
    _ = (∑ t ∈ ts, ∑ h ∈ hs, R / (wt t * wh h)) * U := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro t ht
      rw [Finset.sum_mul]
    _ = _ := by
      rw [reciprocal_grid_sum ts hs wt wh R hwt hwh]
      ring

/-- A weighted composition of the two arbitrary-coefficient sieve bounds.

`beta` is independent of rows and cubic columns; `a` is independent of rows
and the joint cubic index `(m,c)`. The row mask is removed only after freezing
`t` and taking a positive sum. The support budget is the only coupling of the
three weights to `beta`. -/
theorem weighted_energy_of_two_sieves
    {K T C M H P : Type*}
    (rows : Finset K) (ts : Finset T) (cs : Finset C)
    (ms : Finset M) (hs : Finset H) (ps : Finset P)
    (q : K → M → H → ℂ) (chi : M → C → P → ℂ)
    (a : T → H → P → ℂ) (beta : T → C → M → H → ℂ)
    (rowMask : K → T → ℂ) (wt : T → ℝ) (wc : C → ℝ) (wh : H → ℝ)
    (Q S R A : ℝ) (hQ : 0 ≤ Q) (hS : 0 ≤ S) (hR : 0 ≤ R) (hA : 0 ≤ A)
    (hwt : ∀ t ∈ ts, 0 < wt t) (hwc : ∀ c ∈ cs, 0 < wc c)
    (hwh : ∀ h ∈ hs, 0 < wh h)
    (hmask : ∀ k ∈ rows, ∀ t ∈ ts, ‖rowMask k t‖ ≤ 1)
    (hbudget : ∀ t ∈ ts, ∀ c ∈ cs, ∀ m ∈ ms, ∀ h ∈ hs,
      wt t * wc c * ‖beta t c m h‖ ^ 2 ≤ R / (wt t * wh h))
    (ha : ∀ t ∈ ts, ∀ h ∈ hs, (∑ p ∈ ps, ‖a t h p‖ ^ 2) ≤ A)
    (hquadratic : ∀ f : M → H → ℂ,
      (∑ k ∈ rows, ‖∑ m ∈ ms, ∑ h ∈ hs, q k m h * f m h‖ ^ 2) ≤
        Q * (∑ m ∈ ms, ∑ h ∈ hs, ‖f m h‖ ^ 2))
    (hcubic : ∀ u : P → ℂ,
      (∑ m ∈ ms, ∑ c ∈ cs, ‖∑ p ∈ ps, u p * chi m c p‖ ^ 2) ≤
        S * (∑ p ∈ ps, ‖u p‖ ^ 2)) :
    (∑ k ∈ rows, ‖∑ t ∈ ts, ∑ c ∈ cs, rowMask k t *
      (∑ m ∈ ms, ∑ h ∈ hs, q k m h *
        (beta t c m h * (∑ p ∈ ps, a t h p * chi m c p)))‖ ^ 2) ≤
      Q * S * R * A * (∑ t ∈ ts, 1 / wt t) ^ 2 *
        (∑ c ∈ cs, 1 / wc c) * (∑ h ∈ hs, 1 / wh h) := by
  classical
  let column (t : T) (h : H) (m : M) (c : C) : ℂ :=
    ∑ p ∈ ps, a t h p * chi m c p
  let E (t : T) (h : H) (m : M) (c : C) : ℝ := ‖column t h m c‖ ^ 2
  let idx : Finset (T × C) := ts ×ˢ cs
  let w (i : T × C) : ℝ := wt i.1 * wc i.2
  let F (i : T × C) (k : K) : ℂ := rowMask k i.1 *
    (∑ m ∈ ms, ∑ h ∈ hs, q k m h * (beta i.1 i.2 m h * column i.1 h m i.2))
  let G (i : T × C) : ℝ := Q *
    (∑ m ∈ ms, ∑ h ∈ hs, (R / (wt i.1 * wh h)) * E i.1 h m i.2)
  have hw : ∀ i ∈ idx, 0 < w i := by
    intro i hi
    have hi' := Finset.mem_product.mp hi
    exact mul_pos (hwt i.1 hi'.1) (hwc i.2 hi'.2)
  have hE (i : T × C) (hi : i ∈ idx) :
      w i * (∑ k ∈ rows, ‖F i k‖ ^ 2) ≤ G i := by
    have hi' := Finset.mem_product.mp hi
    have hm : (∑ k ∈ rows, ‖F i k‖ ^ 2) ≤
        ∑ k ∈ rows, ‖∑ m ∈ ms, ∑ h ∈ hs,
          q k m h * (beta i.1 i.2 m h * column i.1 h m i.2)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro k hk
      dsimp only [F]
      have hb := mul_le_mul_of_nonneg_right (hmask k hk i.1 hi'.1)
        (norm_nonneg (∑ m ∈ ms, ∑ h ∈ hs,
          q k m h * (beta i.1 i.2 m h * column i.1 h m i.2)))
      have hn : ‖rowMask k i.1 * (∑ m ∈ ms, ∑ h ∈ hs,
          q k m h * (beta i.1 i.2 m h * column i.1 h m i.2))‖ ≤
          ‖∑ m ∈ ms, ∑ h ∈ hs,
            q k m h * (beta i.1 i.2 m h * column i.1 h m i.2)‖ := by
        simpa only [norm_mul, one_mul] using hb
      exact pow_le_pow_left₀ (norm_nonneg _) hn 2
    have hq := hm.trans (hquadratic (fun m h => beta i.1 i.2 m h * column i.1 h m i.2))
    calc
      w i * (∑ k ∈ rows, ‖F i k‖ ^ 2) ≤
          w i * (Q * (∑ m ∈ ms, ∑ h ∈ hs,
            ‖beta i.1 i.2 m h * column i.1 h m i.2‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hq (le_of_lt (hw i hi))
      _ = Q * (∑ m ∈ ms, ∑ h ∈ hs,
          (wt i.1 * wc i.2 * ‖beta i.1 i.2 m h‖ ^ 2) * E i.1 h m i.2) := by
        simp only [norm_mul, mul_pow, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m hm
        apply Finset.sum_congr rfl
        intro h hh
        dsimp only [w, E]
        ring
      _ ≤ G i := by
        apply mul_le_mul_of_nonneg_left _ hQ
        apply Finset.sum_le_sum
        intro m hm
        apply Finset.sum_le_sum
        intro h hh
        exact mul_le_mul_of_nonneg_right
          (hbudget i.1 hi'.1 i.2 hi'.2 m hm h hh) (sq_nonneg _)
  have hcolumn (t : T) (ht : t ∈ ts) (h : H) (hh : h ∈ hs) :
      (∑ m ∈ ms, ∑ c ∈ cs, E t h m c) ≤ S * A := by
    exact (hcubic (a t h)).trans (mul_le_mul_of_nonneg_left (ha t ht h hh) hS)
  have htotal := weighted_cubic_total ts cs ms hs wt wh E R (S * A)
    hR hwt hwh hcolumn
  have hG : (∑ i ∈ idx, G i) ≤
      Q * (R * (S * A) * (∑ t ∈ ts, 1 / wt t) * (∑ h ∈ hs, 1 / wh h)) := by
    calc
      _ = Q * (∑ t ∈ ts, ∑ c ∈ cs, ∑ m ∈ ms, ∑ h ∈ hs,
          (R / (wt t * wh h)) * E t h m c) := by
        simp only [idx, G, Finset.sum_product, Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left htotal hQ
  have hW : 0 ≤ ∑ i ∈ idx, 1 / w i := by
    apply Finset.sum_nonneg
    intro i hi
    exact le_of_lt (one_div_pos.mpr (hw i hi))
  have hwprod : (∑ i ∈ idx, 1 / w i) =
      (∑ t ∈ ts, 1 / wt t) * (∑ c ∈ cs, 1 / wc c) := by
    simpa only [idx, w, Finset.sum_product, one_mul] using
      reciprocal_grid_sum ts cs wt wc 1 hwt hwc
  calc
    _ = ∑ k ∈ rows, ‖∑ i ∈ idx, F i k‖ ^ 2 := by
      simp only [idx, F, column, Finset.sum_product]
    _ ≤ (∑ i ∈ idx, 1 / w i) * (∑ i ∈ idx, G i) :=
      weighted_mixture_energy rows idx w F G hw hE
    _ ≤ (∑ i ∈ idx, 1 / w i) *
        (Q * (R * (S * A) * (∑ t ∈ ts, 1 / wt t) * (∑ h ∈ hs, 1 / wh h))) :=
      mul_le_mul_of_nonneg_left hG hW
    _ = _ := by
      rw [hwprod]
      ring

#print axioms weighted_sum_sq
#print axioms weighted_mixture_energy
#print axioms reciprocal_grid_sum
#print axioms weighted_cubic_total
#print axioms weighted_energy_of_two_sieves

end
end HeckeSkeleton.LowHybrid
