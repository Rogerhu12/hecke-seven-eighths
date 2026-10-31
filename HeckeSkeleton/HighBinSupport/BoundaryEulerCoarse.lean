import HeckeSkeleton.HighBinSupport.ExplicitEulerFamily
/-!
Coarse, uniform bounds for every marked/unmarked Euler branch on the
actual swept tube. Row primes cost at most the fourth power of their
norm product; the bounded number of marks costs a fixed constant.
These estimates suffice for the boundary and require no subpower lemma.
-/

set_option autoImplicit false
noncomputable section
namespace HighBinBoundary.CoarseEuler

open HeckeSkeleton.HighBinContinuation
open HeckeGeneral.ThetaSkeleton.Physical.HighEulerScalarBounds
open scoped BigOperators

def denominatorGap : ℝ := 1 - (2 : ℝ) ^ (-(1 / 2 : ℝ))

theorem denominatorGap_pos : 0 < denominatorGap := by
  have h := Real.rpow_lt_one_of_one_lt_of_neg
    (by norm_num : (1 : ℝ) < 2) (by norm_num : -(1 / 2 : ℝ) < 0)
  dsimp [denominatorGap]
  linarith

def markedBound : ℝ := 1 + 11 / sweptTubeEulerMargin + 2 / denominatorGap

theorem one_le_markedBound : 1 ≤ markedBound := by
  have h1 : 0 ≤ 11 / sweptTubeEulerMargin :=
    div_nonneg (by norm_num) sweptTubeEulerMargin_pos.le
  have h2 : 0 ≤ 2 / denominatorGap := div_nonneg (by norm_num) denominatorGap_pos.le
  dsimp [markedBound]
  linarith

/-- The zero valuation subtraction at a marked prime is uniformly bounded,
including the negative-w endpoint of the contour move. -/
theorem unmarkedZeroPart_bound {q a e : ℝ} (hq : 2 ≤ q)
    (ha : 51 / 100 ≤ a) (ha1 : a ≤ 1) (he : 0 ≤ e) (he1 : e ≤ 1 / 10000)
    (cW cD : ℂ) (hW : ‖cW‖ ≤ 1) (hD : ‖cD‖ ≤ 1)
    (v : ℂ × ℂ × ℂ) (hv : v ∈ sweptTube a e) :
    ‖unmarkedZeroPart q cW cD v.1 v.2.1 v.2.2‖ ≤ 2 / denominatorGap := by
  have hq0 : 0 < q := by linarith
  have hq1 : 1 ≤ q := by linarith
  obtain ⟨hV, hW', hD', _⟩ := phase_coordinate_bounds hq cW cD 0
    v.1 v.2.1 v.2.2 hW hD (by simp) hv.1.le hv.2.1.le hv.2.2.le
  have hWV : ‖cW * (q : ℂ) ^ (-v.2.1) * (q : ℂ) ^ (-6 * v.2.2)‖ ≤ 1 := by
    rw [norm_mul]
    calc
      _ ≤ q ^ (a - 1 + 7 * e) * q ^ (-(51 / 25 : ℝ) + 6 * e) :=
        mul_le_mul hW' hV (norm_nonneg _) (Real.rpow_nonneg hq0.le _)
      _ = q ^ ((a - 1 + 7 * e) + (-(51 / 25 : ℝ) + 6 * e)) :=
        (Real.rpow_add hq0 _ _).symm
      _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hq1 (by linarith)
  have hnum : ‖1 - cW * (q : ℂ) ^ (-v.2.1) * (q : ℂ) ^ (-6 * v.2.2)‖ ≤ 2 := by
    have hh := norm_sub_le (1 : ℂ)
      (cW * (q : ℂ) ^ (-v.2.1) * (q : ℂ) ^ (-6 * v.2.2))
    rw [norm_one] at hh
    linarith
  have hsmall : ‖cD * (q : ℂ) ^ (-v.1)‖ ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) := by
    exact hD'.trans ((Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)).trans
      (Real.rpow_le_rpow_of_nonpos (by norm_num) hq (by norm_num)))
  have hden : denominatorGap ≤ ‖1 - cD * (q : ℂ) ^ (-v.1)‖ := by
    have hh := norm_sub_norm_le (1 : ℂ) (cD * (q : ℂ) ^ (-v.1))
    rw [norm_one] at hh
    dsimp [denominatorGap]
    linarith
  rw [unmarkedZeroPart, norm_div]
  exact div_le_div₀ (by norm_num) hnum denominatorGap_pos hden

theorem phaseRowEuler_coarse_bound {q a e : ℝ} (hq : 2 ≤ q)
    (ha : 51 / 100 ≤ a) (ha1 : a ≤ 1) (he : 0 ≤ e) (he1 : e ≤ 1 / 10000)
    (cW cD cE : ℂ) (hW : ‖cW‖ ≤ 1) (hD : ‖cD‖ ≤ 1) (hE : ‖cE‖ ≤ 1)
    (v : ℂ × ℂ × ℂ) (hv : v ∈ sweptTube a e) :
    ‖phaseRowEuler q cW cD cE v.1 v.2.1 v.2.2‖ ≤ 1 + 11 / sweptTubeEulerMargin := by
  have h := phaseRowEuler_sweptTube_bound hq ha ha1 he he1 cW cD cE hW hD hE v hv
  have hp : q ^ (-1 - 8 * e) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  have he' := mul_le_mul_of_nonneg_left hp
    (div_nonneg (by norm_num : (0 : ℝ) ≤ 11) sweptTubeEulerMargin_pos.le)
  have hn := norm_add_le (phaseRowEuler q cW cD cE v.1 v.2.1 v.2.2 - 1) (1 : ℂ)
  rw [sub_add_cancel, norm_one] at hn
  linarith

/-- A marked row-prime factor is H_j-1; an unmarked row-prime factor is H_j.
Both fit the same coarse q^4 bound, without dividing by H_j. -/
theorem explicitLocalEuler_row_bound {ι : Type*} [DecidableEq ι]
    (R Q : Finset ι) (q : ι → ℝ) (cW cD cE : ι → ℂ)
    (P : ι → PhaseData) (j : ι → Fin 5) {a e : ℝ}
    (hq : ∀ i, 2 ≤ q i) (ha : 51 / 100 ≤ a) (he : 0 ≤ e) (he1 : e ≤ 1 / 10000)
    (i : ι) (hi : i ∈ R) (v : ℂ × ℂ × ℂ) (hv : v ∈ sweptTube a e) :
    ‖explicitLocalEuler R Q q cW cD cE P j i v‖ ≤ (q i) ^ 4 := by
  have hh := ramifiedTable_swept_bound (P i) (q i) a e (hq i) (by linarith) he he1
    v.1 v.2.1 v.2.2 hv.1.le hv.2.1.le hv.2.2.le (j i)
  have hp : (q i) ^ (-8 * e) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [hq i]) (by linarith)
  have hten : ‖explicitLocalEuler R Q q cW cD cE P j i v‖ ≤ 10 := by
    by_cases hQ : i ∈ Q
    · simp only [explicitLocalEuler, if_pos hi, if_pos hQ]
      linarith
    · simp only [explicitLocalEuler, if_pos hi, if_neg hQ, sub_zero]
      have hn := norm_add_le (ramifiedTableValue (P i) (q i) v.1 v.2.1 v.2.2 (j i) - 1) (1 : ℂ)
      rw [sub_add_cancel, norm_one] at hn
      linarith
  have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) (hq i) 4
  norm_num at hpow
  exact hten.trans (by linarith)

theorem explicitLocalEuler_mark_bound {ι : Type*} [DecidableEq ι]
    (R Q : Finset ι) (q : ι → ℝ) (cW cD cE : ι → ℂ)
    (P : ι → PhaseData) (j : ι → Fin 5) {a e : ℝ}
    (hq : ∀ i, 2 ≤ q i) (ha : 51 / 100 ≤ a) (ha1 : a ≤ 1)
    (he : 0 ≤ e) (he1 : e ≤ 1 / 10000)
    (hW : ∀ i, ‖cW i‖ ≤ 1) (hD : ∀ i, ‖cD i‖ ≤ 1) (hE : ∀ i, ‖cE i‖ ≤ 1)
    (i : ι) (hi : i ∉ R) (hQ : i ∈ Q) (v : ℂ × ℂ × ℂ) (hv : v ∈ sweptTube a e) :
    ‖explicitLocalEuler R Q q cW cD cE P j i v‖ ≤ markedBound := by
  simp only [explicitLocalEuler, if_neg hi, if_pos hQ]
  exact (norm_sub_le _ _).trans
    (add_le_add
      (phaseRowEuler_coarse_bound (hq i) ha ha1 he he1
        (cW i) (cD i) (cE i) (hW i) (hD i) (hE i) v hv)
      (unmarkedZeroPart_bound (hq i) ha ha1 he he1 (cW i) (cD i) (hW i) (hD i) v hv))

/-- The finite exceptional mass of the explicit four-case family.
An overlap of row support and marks is allowed and causes no division. -/
theorem explicitEuler_finite_exceptional_bound {ι : Type*} [DecidableEq ι]
    (R Q : Finset ι) (q : ι → ℝ) (cW cD cE : ι → ℂ)
    (P : ι → PhaseData) (j : ι → Fin 5) {a e : ℝ}
    (hq : ∀ i, 2 ≤ q i) (ha : 51 / 100 ≤ a) (ha1 : a ≤ 1)
    (he : 0 ≤ e) (he1 : e ≤ 1 / 10000)
    (hW : ∀ i, ‖cW i‖ ≤ 1) (hD : ∀ i, ‖cD i‖ ≤ 1) (hE : ∀ i, ‖cE i‖ ≤ 1)
    (v : ℂ × ℂ × ℂ) (hv : v ∈ sweptTube a e) :
    (∏ i ∈ R ∪ Q, ‖explicitLocalEuler R Q q cW cD cE P j i v‖) ≤
      (∏ i ∈ R, q i) ^ 4 * markedBound ^ Q.card := by
  have hmajor (i : ι) (hi : i ∈ R ∪ Q) :
      ‖explicitLocalEuler R Q q cW cD cE P j i v‖ ≤
        (if i ∈ R then (q i) ^ 4 else 1) * (if i ∈ Q then markedBound else 1) := by
    by_cases hR : i ∈ R
    · rw [if_pos hR]
      apply (explicitLocalEuler_row_bound R Q q cW cD cE P j hq ha he he1 i hR v hv).trans
      have hx : 0 ≤ (q i) ^ 4 := pow_nonneg (by linarith [hq i]) _
      by_cases hQ : i ∈ Q
      · rw [if_pos hQ]
        simpa only [mul_one] using mul_le_mul_of_nonneg_left one_le_markedBound hx
      · rw [if_neg hQ, mul_one]
    · have hQ : i ∈ Q := (Finset.mem_union.mp hi).resolve_left hR
      rw [if_neg hR, if_pos hQ, one_mul]
      exact explicitLocalEuler_mark_bound R Q q cW cD cE P j
        hq ha ha1 he he1 hW hD hE i hR hQ v hv
  have hR : (R ∪ Q) ∩ R = R := by
    ext i
    exact ⟨fun h => (Finset.mem_inter.mp h).2,
      fun h => Finset.mem_inter.mpr ⟨Finset.mem_union_left Q h, h⟩⟩
  have hQ : (R ∪ Q) ∩ Q = Q := by
    ext i
    exact ⟨fun h => (Finset.mem_inter.mp h).2,
      fun h => Finset.mem_inter.mpr ⟨Finset.mem_union_right R h, h⟩⟩
  apply (Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) hmajor).trans_eq
  rw [Finset.prod_mul_distrib, Finset.prod_ite_mem, Finset.prod_ite_mem,
    hR, hQ, Finset.prod_const, ← Finset.prod_pow]

/-- A uniform polynomial bound for the complete explicit product.
For actual row support the norm product is rad(u), bounded by N(u). -/
theorem explicitEuler_coarse_bound {ι : Type*} [DecidableEq ι]
    (R Q : Finset ι) (q : ι → ℝ) (cW cD cE : ι → ℂ)
    (P : ι → PhaseData) (j : ι → Fin 5) {a e : ℝ}
    (hq : ∀ i, 2 ≤ q i) (ha : 51 / 100 ≤ a) (ha1 : a ≤ 1)
    (he : 0 ≤ e) (he1 : e ≤ 1 / 10000)
    (hW : ∀ i, ‖cW i‖ ≤ 1) (hD : ∀ i, ‖cD i‖ ≤ 1) (hE : ∀ i, ‖cE i‖ ≤ 1)
    (hsum : Summable (fun i => (q i) ^ (-1 - 8 * e)))
    (v : ℂ × ℂ × ℂ) (hv : v ∈ sweptTube a e) :
    ‖∏' i, explicitLocalEuler R Q q cW cD cE P j i v‖ ≤
      ((∏ i ∈ R, q i) ^ 4 * markedBound ^ Q.card) *
        Real.exp (∑' i, (11 / sweptTubeEulerMargin) * (q i) ^ (-1 - 8 * e)) := by
  have hb (i : ι) : 0 ≤ (11 / sweptTubeEulerMargin) * (q i) ^ (-1 - 8 * e) :=
    mul_nonneg (div_nonneg (by norm_num) sweptTubeEulerMargin_pos.le)
      (Real.rpow_nonneg (by linarith [hq i]) _)
  have hf (i : ι) (hi : i ∉ R ∪ Q) :
      ‖explicitLocalEuler R Q q cW cD cE P j i v - 1‖ ≤
        (11 / sweptTubeEulerMargin) * (q i) ^ (-1 - 8 * e) := by
    have hR : i ∉ R := fun h => hi (Finset.mem_union_left Q h)
    have hQ : i ∉ Q := fun h => hi (Finset.mem_union_right R h)
    simpa only [explicitLocalEuler, if_neg hR, if_neg hQ, sub_zero] using
      phaseRowEuler_sweptTube_bound (hq i) ha ha1 he he1
        (cW i) (cD i) (cE i) (hW i) (hD i) (hE i) v hv
  have h := (finite_exceptional_product_bound (R ∪ Q)
    (fun i => explicitLocalEuler R Q q cW cD cE P j i v)
    (fun i => (11 / sweptTubeEulerMargin) * (q i) ^ (-1 - 8 * e))
    hb (hsum.mul_left _) hf).2
  exact h.trans (mul_le_mul_of_nonneg_right
    (explicitEuler_finite_exceptional_bound R Q q cW cD cE P j
      hq ha ha1 he he1 hW hD hE v hv) (Real.exp_pos _).le)

#print axioms unmarkedZeroPart_bound
#print axioms explicitEuler_finite_exceptional_bound
#print axioms explicitEuler_coarse_bound

end HighBinBoundary.CoarseEuler
