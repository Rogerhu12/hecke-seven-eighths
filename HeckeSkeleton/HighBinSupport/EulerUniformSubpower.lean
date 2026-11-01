import HeckeSkeleton.HighBinSupport.ExplicitEulerFamily
/-!
# Uniform conductor subpower for the explicit Euler family

The finite small-prime set is constructed from a scalar summability
hypothesis.  No bound on its cardinality or cutoff is supplied as an
extra premise.  The resulting constant is independent of the exceptional
set, the conductor, all phases, and all points of the swept tube.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.HighBinContinuation
open HeckeGeneral.ThetaSkeleton.Physical.HighEulerScalarBounds
open Filter
open scoped BigOperators Topology

theorem finite_small_norms_from_summable {ι : Type*} (q : ι → ℝ)
    {α η : ℝ} (hq : ∀ i, 0 < q i) (hα : 0 < α) (hη : 0 < η)
    (hsum : Summable (fun i => (q i) ^ (-α))) :
    ∃ small : Finset ι, ∀ i, i ∉ small → 10 ≤ (q i) ^ η := by
  classical
  let C : ℝ := (10 : ℝ) ^ (1 / η)
  have hC : 0 < C := Real.rpow_pos_of_pos (by norm_num) _
  have hlim : ∀ᶠ i in cofinite, (q i) ^ (-α) < C ^ (-α) :=
    hsum.tendsto_cofinite_zero.eventually_lt_const (Real.rpow_pos_of_pos hC _)
  have hevent : ∀ᶠ i in cofinite, 10 ≤ (q i) ^ η := by
    filter_upwards [hlim] with i hi
    have hCq : C ≤ q i := by
      by_contra hn
      have hqC : q i ≤ C := (lt_of_not_ge hn).le
      have hanti := Real.rpow_le_rpow_of_nonpos (hq i) hqC (neg_nonpos.mpr hα.le)
      exact (not_lt_of_ge hanti) hi
    have hCpow : C ^ η = 10 := by
      dsimp [C]
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 10)]
      rw [div_mul_cancel₀ 1 (ne_of_gt hη), Real.rpow_one]
    calc
      10 = C ^ η := hCpow.symm
      _ ≤ (q i) ^ η := Real.rpow_le_rpow hC.le hCq hη.le
  have hf := Filter.eventually_cofinite.mp hevent
  refine ⟨hf.toFinset, ?_⟩
  intro i hi
  simpa only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] using hi

theorem uniform_finite_exceptional_subpower {ι : Type*} [DecidableEq ι]
    (q : ι → ℝ) {α η : ℝ} (hq : ∀ i, 1 ≤ q i)
    (hα : 0 < α) (hη : 0 < η)
    (hsum : Summable (fun i => (q i) ^ (-α))) :
    ∃ C : ℝ, 0 < C ∧ ∀ (E : Finset ι) (f : ι → ℂ) (N : ℝ),
      (∏ i ∈ E, q i) ≤ N → (∀ i ∈ E, ‖f i‖ ≤ 10) →
      (∏ i ∈ E, ‖f i‖) ≤ C * N ^ η := by
  obtain ⟨small, hs⟩ := finite_small_norms_from_summable q
    (fun i => lt_of_lt_of_le zero_lt_one (hq i)) hα hη hsum
  refine ⟨10 ^ small.card, by positivity, ?_⟩
  intro E f N hN hf
  exact finite_exceptional_subpower E small f q N η hη.le
    (fun i _ => hq i) hN hf (fun i _ hi => hs i hi)

theorem ramifiedTable_swept_norm_le_ten (P : PhaseData) (q a e : ℝ)
    (hq : 2 ≤ q) (ha : 1 / 2 ≤ a) (he : 0 ≤ e) (he' : e ≤ 1 / 10000)
    (v : ℂ × ℂ × ℂ) (hv : v ∈ sweptTube a e) (j : Fin 5) :
    ‖ramifiedTableValue P q v.1 v.2.1 v.2.2 j‖ ≤ 10 := by
  have hb := ramifiedTable_swept_bound P q a e hq ha he he'
    v.1 v.2.1 v.2.2 hv.1.le hv.2.1.le hv.2.2.le j
  have hp : q ^ (-8 * e) ≤ 1 := by
    calc
      q ^ (-8 * e) ≤ q ^ (0 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ = 1 := Real.rpow_zero q
  have htriangle := norm_add_le
    (ramifiedTableValue P q v.1 v.2.1 v.2.2 j - 1) (1 : ℂ)
  rw [sub_add_cancel, norm_one] at htriangle
  nlinarith

/-- The literal unmarked explicit product has a conductor-subpower bound
with one constant for every real part a, all heights, and all phases.
Arithmetic identification with the number-field Fourier sum is separate. -/
theorem explicitEuler_unmarked_uniform_subpower {ι : Type*} [DecidableEq ι]
    (q : ι → ℝ) {e η : ℝ} (hq : ∀ i, 2 ≤ q i)
    (he : 0 ≤ e) (he' : e ≤ 1 / 10000) (hη : 0 < η)
    (hsum : Summable (fun i => (q i) ^ (-1 - 8 * e))) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : Finset ι) (N a : ℝ)
      (cW cD cE : ι → ℂ) (P : ι → PhaseData) (j : ι → Fin 5),
      (∏ i ∈ R, q i) ≤ N → 51 / 100 ≤ a → a ≤ 1 →
      (∀ i, ‖cW i‖ ≤ 1) → (∀ i, ‖cD i‖ ≤ 1) → (∀ i, ‖cE i‖ ≤ 1) →
      ∀ v ∈ sweptTube a e,
        ‖∏' i, explicitLocalEuler R ∅ q cW cD cE P j i v‖ ≤ C * N ^ η := by
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
  intro R N a cW cD cE P j hN ha ha' hW hD hE v hv
  let f : ι → ℂ := fun i => explicitLocalEuler R ∅ q cW cD cE P j i v
  have hf : ∀ i, i ∉ R → ‖f i - 1‖ ≤ b i := by
    intro i hi
    simpa only [f, explicitLocalEuler, if_neg hi, Finset.notMem_empty,
      if_false, sub_zero, b] using
      phaseRowEuler_sweptTube_bound (hq i) ha ha' he he'
        (cW i) (cD i) (cE i) (hW i) (hD i) (hE i) v hv
  have hlocal : ∀ i ∈ R, ‖f i‖ ≤ 10 := by
    intro i hi
    simpa only [f, explicitLocalEuler, if_pos hi, Finset.notMem_empty,
      if_false, sub_zero] using
      ramifiedTable_swept_norm_le_ten (P i) (q i) a e (hq i) (by linarith)
        he he' v hv (j i)
  calc
    ‖∏' i, f i‖ ≤ (∏ i ∈ R, ‖f i‖) * Real.exp (∑' i, b i) :=
      (finite_exceptional_product_bound R f b hb hbs hf).2
    _ ≤ (C₀ * N ^ η) * Real.exp (∑' i, b i) :=
      mul_le_mul_of_nonneg_right (hC R f N hN hlocal) (Real.exp_pos _).le
    _ = (C₀ * Real.exp (∑' i, b i)) * N ^ η := by ring

#print axioms finite_small_norms_from_summable
#print axioms uniform_finite_exceptional_subpower
#print axioms ramifiedTable_swept_norm_le_ten
#print axioms explicitEuler_unmarked_uniform_subpower
end HeckeSkeleton.HighBinContinuation
