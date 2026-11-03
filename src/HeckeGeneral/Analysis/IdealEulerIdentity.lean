import HeckeGeneral.Analysis.IdealEulerProduct
import HeckeGeneral.Arithmetic.IdealFactorization
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# Euler summation over finitely supported prime exponents

The finite-support lemma is proved by an explicit exponent decomposition and
an unconditional-series tail argument. It uses neither natural-number primes
nor an Euler identity as an assumption.
-/

noncomputable section

namespace HeckeGeneral.Analysis.FiniteSupportEuler

open Filter
open scoped BigOperators Topology Classical

variable {ι : Type*}

def weight (g : ι → ℂ) (e : ι →₀ ℕ) : ℂ := e.prod (fun p n => g p ^ n)

@[simp] theorem weight_zero (g : ι → ℂ) : weight g 0 = 1 := by
  simp [weight]

theorem weight_add (g : ι → ℂ) (e f : ι →₀ ℕ) :
    weight g (e + f) = weight g e * weight g f := by
  exact Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)

@[simp] theorem weight_single (g : ι → ℂ) (p : ι) (n : ℕ) :
    weight g (Finsupp.single p n) = g p ^ n := by
  exact Finsupp.prod_single_index (pow_zero _)

abbrev Supported (S : Finset ι) := {e : ι →₀ ℕ // e.support ⊆ S}

/-- Extract the exponent at the new prime and erase precisely that coordinate. -/
def insertEquiv (S : Finset ι) (p : ι) (hp : p ∉ S) :
    ℕ × Supported S ≃ Supported (insert p S) where
  toFun x := ⟨Finsupp.single p x.1 + x.2.val, by
    intro q hq
    by_cases hqp : q = p
    · simp [hqp]
    apply Finset.mem_insert_of_mem
    apply x.2.property
    rw [Finsupp.mem_support_iff] at hq ⊢
    simpa [Finsupp.single_apply, hqp] using hq⟩
  invFun e := (e.val p, ⟨e.val.erase p, by
    intro q hq
    rw [Finsupp.support_erase, Finset.mem_erase] at hq
    exact (Finset.mem_insert.mp (e.property hq.2)).resolve_left hq.1⟩)
  left_inv x := by
    apply Prod.ext
    · have hp0 : x.2.val p = 0 :=
        Finsupp.notMem_support_iff.mp (fun h => hp (x.2.property h))
      simp [hp0]
    · apply Subtype.ext
      ext q
      by_cases hqp : q = p
      · subst q
        have hp0 : x.2.val p = 0 :=
          Finsupp.notMem_support_iff.mp (fun h => hp (x.2.property h))
        simp [hp0]
      · simp [hqp]
  right_inv e := by
    apply Subtype.ext
    ext q
    by_cases hqp : q = p
    · subst q
      simp
    · simp [hqp]

@[simp] theorem weight_insertEquiv (g : ι → ℂ) (S : Finset ι) (p : ι) (hp : p ∉ S)
    (x : ℕ × Supported S) :
    weight g (insertEquiv S p hp x).val = g p ^ x.1 * weight g x.2.val := by
  exact (weight_add g _ _).trans (by rw [weight_single])

set_option maxHeartbeats 1200000 in
/-- Each finite prime-supported sum is the product of its full geometric sums. -/
theorem hasSum_supported (g : ι → ℂ)
    (hg : ∀ p, Summable (fun n : ℕ => ‖g p ^ n‖)) (S : Finset ι) :
    Summable (fun e : Supported S => ‖weight g e.val‖) ∧
      HasSum (fun e : Supported S => weight g e.val)
        (∏ p ∈ S, ∑' n : ℕ, g p ^ n) := by
  induction S using Finset.induction with
  | empty =>
    let : Unique (Supported (∅ : Finset ι)) :=
      { default := ⟨0, by simp⟩
        uniq := by
          intro e
          apply Subtype.ext
          apply Finsupp.support_eq_empty.mp
          exact Finset.eq_empty_iff_forall_notMem.mpr (fun p hp => by
            simpa using e.property hp) }
    constructor
    · exact Summable.of_finite
    · rw [Finset.prod_empty]
      have h : (∑ e : Supported (∅ : Finset ι), weight g e.val) = 1 := by
        rw [Fintype.sum_unique]
        exact weight_zero g
      exact h ▸ hasSum_fintype (fun e : Supported (∅ : Finset ι) => weight g e.val)
  | insert p S hp ih =>
    constructor
    · apply (insertEquiv S p hp).summable_iff.mp
      change Summable (fun x : ℕ × Supported S => ‖weight g (insertEquiv S p hp x).val‖)
      simp only [weight_insertEquiv, norm_mul]
      exact (hg p).mul_of_nonneg ih.1 (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    · rw [Finset.prod_insert hp]
      apply (insertEquiv S p hp).hasSum_iff.mp
      change HasSum (fun x : ℕ × Supported S => weight g (insertEquiv S p hp x).val) _
      simp only [weight_insertEquiv]
      have hleft : HasSum (fun n : ℕ => g p ^ n) (∑' n : ℕ, g p ^ n) :=
        (hg p).of_norm.hasSum
      have habs : Summable (fun x : ℕ × Supported S =>
          ‖g p ^ x.1‖ * ‖weight g x.2.val‖) :=
        (hg p).mul_of_nonneg ih.1 (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
      have hprod : Summable (fun x : ℕ × Supported S => g p ^ x.1 * weight g x.2.val) :=
        Summable.of_norm (by simpa only [norm_mul] using habs)
      have hval : (∑' n : ℕ, g p ^ n) * (∑' e : Supported S, weight g e.val) =
          ∑' x : ℕ × Supported S, g p ^ x.1 * weight g x.2.val :=
        tsum_mul_tsum_of_summable_norm
          (f := fun n : ℕ => g p ^ n) (g := fun e : Supported S => weight g e.val)
          (hg p) ih.1
      rw [ih.2.tsum_eq] at hval
      exact hval.symm ▸ hprod.hasSum

/-- No finite-support vectors are lost in the Euler-product limit. -/
theorem hasProd_of_summable_weight (g : ι → ℂ)
    (hg : ∀ p, Summable (fun n : ℕ => ‖g p ^ n‖))
    (hw : Summable (fun e : ι →₀ ℕ => ‖weight g e‖)) :
    HasProd (fun p => ∑' n : ℕ, g p ^ n) (∑' e : ι →₀ ℕ, weight g e) := by
  change Tendsto (fun S : Finset ι => ∏ p ∈ S, ∑' n : ℕ, g p ^ n)
    atTop (𝓝 (∑' e : ι →₀ ℕ, weight g e))
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨T, hT⟩ := hw.of_norm.tsum_vanishing (Metric.ball_mem_nhds 0 hε)
  let S : Finset ι := T.biUnion Finsupp.support
  refine ⟨S, fun U hU => ?_⟩
  have hdisj : Disjoint (↑T : Set (ι →₀ ℕ)) {e : ι →₀ ℕ | e.support ⊆ U}ᶜ := by
    refine Set.disjoint_left.mpr ?_
    intro e he hnot
    apply hnot
    intro p hp
    exact hU (Finset.mem_biUnion.mpr ⟨e, he, hp⟩)
  have htail := hT _ hdisj.symm
  rw [Metric.mem_ball, dist_zero_right] at htail
  have hsum := hw.of_norm.tsum_subtype_add_tsum_subtype_compl
    {e : ι →₀ ℕ | e.support ⊆ U}
  change (∑' e : Supported U, weight g e.val) +
    (∑' e : ↑({e : ι →₀ ℕ | e.support ⊆ U}ᶜ), weight g e.val) =
      ∑' e : ι →₀ ℕ, weight g e at hsum
  rw [dist_eq_norm, norm_sub_rev, ← (hasSum_supported g hg U).2.tsum_eq,
    ← hsum, add_sub_cancel_left]
  exact htail

end HeckeGeneral.Analysis.FiniteSupportEuler

namespace HeckeGeneral.Analysis

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic
open scoped BigOperators Topology Classical nonZeroDivisors

variable (K : Type*) [Field K] [NumberField K]

theorem idealEulerWeight_primeExponents (a : HeightOneSpectrum (𝓞 K) → ℂ) (s : ℂ)
    (e : HeightOneSpectrum (𝓞 K) →₀ ℕ) :
    idealEulerWeight K a s (idealOfPrimeExponents e).val =
      FiniteSupportEuler.weight (primeIdealRatio K a s) e := by
  change idealEulerWeightHom K a s _ = _
  rw [map_idealOfPrimeExponents]
  unfold FiniteSupportEuler.weight
  apply Finsupp.prod_congr
  intro p _
  exact congrArg (fun z : ℂ => z ^ e p) (idealEulerWeight_prime K a s p)

theorem absolutelySummable_primeExponent_weight (a : HeightOneSpectrum (𝓞 K) → ℂ)
    (ha : ∀ p, ‖a p‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun e : HeightOneSpectrum (𝓞 K) →₀ ℕ =>
      ‖FiniteSupportEuler.weight (primeIdealRatio K a s) e‖) := by
  have h := (primeExponentEquiv (R := 𝓞 K)).symm.summable_iff.mpr
    (absolutelySummable_idealEulerWeight K a ha hs)
  apply h.congr
  intro e
  exact congrArg norm (idealEulerWeight_primeExponents K a s e)

theorem idealDirichletSeries_eq_tsum_primeExponents
    (a : HeightOneSpectrum (𝓞 K) → ℂ) (s : ℂ) :
    idealDirichletSeries K (nonzeroIdealCoefficient a) s =
      ∑' e : HeightOneSpectrum (𝓞 K) →₀ ℕ,
        FiniteSupportEuler.weight (primeIdealRatio K a s) e := by
  unfold idealDirichletSeries dirichletSeries
  rw [← (primeExponentEquiv (R := 𝓞 K)).symm.tsum_eq
    (dirichletTerm (idealNorm K) (nonzeroIdealCoefficient a) s)]
  apply tsum_congr
  intro e
  rw [primeExponentEquiv_symm_apply, ← idealEulerWeight_nonzero,
    idealEulerWeight_primeExponents]

/-- The full Euler identity for the absolutely convergent series indexed by
actual nonzero integral ideals. -/
theorem hasProd_idealDirichletSeries (a : HeightOneSpectrum (𝓞 K) → ℂ)
    (ha : ∀ p, ‖a p‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p => (1 - primeIdealRatio K a s p)⁻¹)
      (idealDirichletSeries K (nonzeroIdealCoefficient a) s) := by
  have hg (p : HeightOneSpectrum (𝓞 K)) :
      Summable (fun n : ℕ => ‖primeIdealRatio K a s p ^ n‖) := by
    simpa only [norm_pow] using summable_geometric_of_lt_one
      (norm_nonneg (primeIdealRatio K a s p)) (norm_primeIdealRatio_lt_one K a ha hs p)
  have h := FiniteSupportEuler.hasProd_of_summable_weight (primeIdealRatio K a s) hg
    (absolutelySummable_primeExponent_weight K a ha hs)
  rw [idealDirichletSeries_eq_tsum_primeExponents]
  apply h.congr_fun
  intro p
  exact (hasSum_geometric_of_norm_lt_one (norm_primeIdealRatio_lt_one K a ha hs p)).tsum_eq.symm

theorem idealDirichletSeries_eq_primeIdealEulerValue
    (a : HeightOneSpectrum (𝓞 K) → ℂ) (ha : ∀ p, ‖a p‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) :
    idealDirichletSeries K (nonzeroIdealCoefficient a) s = primeIdealEulerValue K a s :=
  (hasProd_idealDirichletSeries K a ha hs).unique (hasProd_primeIdeal_factors K a ha hs)

theorem idealDirichletSeries_eq_primeIdeal_tprod
    (a : HeightOneSpectrum (𝓞 K) → ℂ) (ha : ∀ p, ‖a p‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) :
    idealDirichletSeries K (nonzeroIdealCoefficient a) s =
      ∏' p, (1 - primeIdealRatio K a s p)⁻¹ :=
  (hasProd_idealDirichletSeries K a ha hs).tprod_eq.symm

/-- Nonvanishing of the actual ideal series in its absolute-convergence half-plane. -/
theorem idealDirichletSeries_ne_zero (a : HeightOneSpectrum (𝓞 K) → ℂ)
    (ha : ∀ p, ‖a p‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    idealDirichletSeries K (nonzeroIdealCoefficient a) s ≠ 0 := by
  rw [idealDirichletSeries_eq_primeIdealEulerValue K a ha hs]
  exact primeIdealEulerValue_ne_zero K a s

end HeckeGeneral.Analysis
