import HeckeSkeleton.HighBinSupport.EulerUniformSubpower
import HeckeSkeleton.HighBinSupport.BoundaryEulerCoarse
/-!
# Conductor subpower bound for the complete marked Euler product

Overlaps of the row support and the marks are retained literally.  The
argument uses multiplication by finite factors, so it remains valid when
one of the local Gauss polynomials or the full Euler product is zero.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.HighBinContinuation
open HeckeGeneral.ThetaSkeleton.Physical.HighEulerScalarBounds
open HighBinBoundary.CoarseEuler
open scoped BigOperators

theorem finite_marked_exceptional_product {ι : Type*} [DecidableEq ι]
    (R Q : Finset ι) (f : ι → ℂ) (K : ℝ) (hK : 1 ≤ K)
    (hf : ∀ i, i ∉ R → i ∈ Q → ‖f i‖ ≤ K) :
    (∏ i ∈ R ∪ Q, ‖f i‖) ≤ (∏ i ∈ R, ‖f i‖) * K ^ Q.card := by
  have hmajor (i : ι) (hi : i ∈ R ∪ Q) :
      ‖f i‖ ≤ (if i ∈ R then ‖f i‖ else 1) * (if i ∈ Q then K else 1) := by
    by_cases hR : i ∈ R
    · rw [if_pos hR]
      by_cases hQ : i ∈ Q
      · rw [if_pos hQ]
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hK (norm_nonneg (f i))
      · rw [if_neg hQ, mul_one]
    · have hQ : i ∈ Q := (Finset.mem_union.mp hi).resolve_left hR
      simpa only [if_neg hR, if_pos hQ, one_mul] using hf i hR hQ
  have hR : (R ∪ Q) ∩ R = R := by ext i; simp
  have hQ : (R ∪ Q) ∩ Q = Q := by ext i; simp
  apply (Finset.prod_le_prod₀ (fun i _ => norm_nonneg (f i)) hmajor).trans_eq
  rw [Finset.prod_mul_distrib, Finset.prod_ite_mem, Finset.prod_ite_mem,
    hR, hQ, Finset.prod_const]

theorem explicitLocalEuler_row_norm_le_ten {ι : Type*} [DecidableEq ι]
    (R Q : Finset ι) (q : ι → ℝ) (cW cD cE : ι → ℂ)
    (P : ι → PhaseData) (j : ι → Fin 5) {a e : ℝ}
    (hq : ∀ i, 2 ≤ q i) (ha : 51 / 100 ≤ a) (he : 0 ≤ e) (he' : e ≤ 1 / 10000)
    (i : ι) (hi : i ∈ R) (v : ℂ × ℂ × ℂ) (hv : v ∈ sweptTube a e) :
    ‖explicitLocalEuler R Q q cW cD cE P j i v‖ ≤ 10 := by
  by_cases hQ : i ∈ Q
  · simp only [explicitLocalEuler, if_pos hi, if_pos hQ]
    have hb := ramifiedTable_swept_bound (P i) (q i) a e (hq i) (by linarith)
      he he' v.1 v.2.1 v.2.2 hv.1.le hv.2.1.le hv.2.2.le (j i)
    have hp : (q i) ^ (-8 * e) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [hq i]) (by linarith)
    nlinarith
  · simpa only [explicitLocalEuler, if_pos hi, if_neg hQ, sub_zero] using
      ramifiedTable_swept_norm_le_ten (P i) (q i) a e (hq i) (by linarith)
        he he' v hv (j i)

/-- A single constant works for every row, every finite mark set, all
phases, and all heights in the full swept tube.  Only the explicit factor
`markedBound ^ Q.card` depends on the number of marks. -/
theorem explicitEuler_marked_uniform_subpower {ι : Type*} [DecidableEq ι]
    (q : ι → ℝ) {e η : ℝ} (hq : ∀ i, 2 ≤ q i)
    (he : 0 ≤ e) (he' : e ≤ 1 / 10000) (hη : 0 < η)
    (hsum : Summable (fun i => (q i) ^ (-1 - 8 * e))) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R Q : Finset ι) (N a : ℝ)
      (cW cD cE : ι → ℂ) (P : ι → PhaseData) (j : ι → Fin 5),
      (∏ i ∈ R, q i) ≤ N → 51 / 100 ≤ a → a ≤ 1 →
      (∀ i, ‖cW i‖ ≤ 1) → (∀ i, ‖cD i‖ ≤ 1) → (∀ i, ‖cE i‖ ≤ 1) →
      ∀ v ∈ sweptTube a e,
        ‖∏' i, explicitLocalEuler R Q q cW cD cE P j i v‖ ≤
          C * N ^ η * markedBound ^ Q.card := by
  have hsα : Summable (fun i => (q i) ^ (-(1 + 8 * e))) := by
    have hexp : -(1 + 8 * e) = -1 - 8 * e := by ring
    simpa only [hexp] using hsum
  obtain ⟨C₀, hC₀, hC⟩ := uniform_finite_exceptional_subpower q
    (fun i => by linarith [hq i]) (by linarith : 0 < 1 + 8 * e) hη hsα
  let b : ι → ℝ := fun i => (11 / sweptTubeEulerMargin) * (q i) ^ (-1 - 8 * e)
  have hb : ∀ i, 0 ≤ b i := fun i => mul_nonneg
    (div_nonneg (by norm_num) sweptTubeEulerMargin_pos.le)
    (Real.rpow_nonneg (by linarith [hq i]) _)
  have hbs : Summable b := hsum.mul_left _
  refine ⟨C₀ * Real.exp (∑' i, b i), mul_pos hC₀ (Real.exp_pos _), ?_⟩
  intro R Q N a cW cD cE P j hN ha ha' hW hD hE v hv
  let f : ι → ℂ := fun i => explicitLocalEuler R Q q cW cD cE P j i v
  have hf : ∀ i, i ∉ R ∪ Q → ‖f i - 1‖ ≤ b i := by
    intro i hi
    have hR : i ∉ R := fun h => hi (Finset.mem_union_left Q h)
    have hQ : i ∉ Q := fun h => hi (Finset.mem_union_right R h)
    simpa only [f, explicitLocalEuler, if_neg hR, if_neg hQ, sub_zero, b] using
      phaseRowEuler_sweptTube_bound (hq i) ha ha' he he'
        (cW i) (cD i) (cE i) (hW i) (hD i) (hE i) v hv
  have hrow : ∀ i ∈ R, ‖f i‖ ≤ 10 := fun i hi =>
    explicitLocalEuler_row_norm_le_ten R Q q cW cD cE P j hq ha he he' i hi v hv
  have hmark : ∀ i, i ∉ R → i ∈ Q → ‖f i‖ ≤ markedBound := fun i hi hQ =>
    explicitLocalEuler_mark_bound R Q q cW cD cE P j
      hq ha ha' he he' hW hD hE i hi hQ v hv
  have hfinite : (∏ i ∈ R ∪ Q, ‖f i‖) ≤
      (C₀ * N ^ η) * markedBound ^ Q.card :=
    (finite_marked_exceptional_product R Q f markedBound one_le_markedBound hmark).trans
      (mul_le_mul_of_nonneg_right (hC R f N hN hrow)
        (pow_nonneg (zero_le_one.trans one_le_markedBound) _))
  calc
    ‖∏' i, f i‖ ≤ (∏ i ∈ R ∪ Q, ‖f i‖) * Real.exp (∑' i, b i) :=
      (finite_exceptional_product_bound (R ∪ Q) f b hb hbs hf).2
    _ ≤ ((C₀ * N ^ η) * markedBound ^ Q.card) * Real.exp (∑' i, b i) :=
      mul_le_mul_of_nonneg_right hfinite (Real.exp_pos _).le
    _ = (C₀ * Real.exp (∑' i, b i)) * N ^ η * markedBound ^ Q.card := by ring

#print axioms finite_marked_exceptional_product
#print axioms explicitLocalEuler_row_norm_le_ten
#print axioms explicitEuler_marked_uniform_subpower
end HeckeSkeleton.HighBinContinuation
