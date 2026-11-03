import HeckeGeneral.Analysis.BalancedLatticeShape

/-!
# Uniform finite Schwartz sums in compact families of actual local multipliers

The bound applies to any injectively indexed subset of a fixed nonzero
lattice. It is a finite-sum estimate, so it can be used to establish absolute
convergence without assuming summability of the orbit series first.

The archimedean multiplier is a genuine mixed-space unit. Its action is
transported through the trace model, and compactness controls the inverse
operator norm. The arithmetic injection of the relevant S-units into a
single denominator-cleared lattice is a separate input to the application.
-/

noncomputable section

namespace HeckeGeneral.Analysis

open HeckeGeneral.Arithmetic NumberField
open scoped Classical BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_schwartz_equiv_le_inverse_power (f : SchwartzMap E ℂ)
    (e : E ≃L[ℝ] E) (M : ℕ) {B : ℝ}
    (hB : ‖e.symm.toContinuousLinearMap‖ ≤ B) {x : E} (hx : x ≠ 0) :
    ‖f (e x)‖ ≤ SchwartzMap.seminorm ℂ M 0 f * B ^ M * ‖x‖⁻¹ ^ M := by
  have hex : e x ≠ 0 := by
    intro he
    exact hx (e.injective (by simpa only [map_zero] using he))
  have hf : ‖f (e x)‖ ≤ SchwartzMap.seminorm ℂ M 0 f * ‖e x‖⁻¹ ^ M := by
    simpa only [one_smul, pow_zero, one_mul, norm_iteratedFDeriv_zero,
      Nat.add_zero, inv_one, one_pow, mul_one] using
      schwartz_scaled_derivative_bound f M 0 (α := 1) zero_lt_one hex
  calc
    _ ≤ SchwartzMap.seminorm ℂ M 0 f * ‖e x‖⁻¹ ^ M := hf
    _ ≤ SchwartzMap.seminorm ℂ M 0 f * (B * ‖x‖⁻¹) ^ M :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (inv_nonneg.mpr (norm_nonneg _))
          (inv_norm_equiv_le e hB hx) M)
        (apply_nonneg (SchwartzMap.seminorm ℂ M 0) f)
    _ = _ := by rw [mul_pow, mul_assoc]

variable [FiniteDimensional ℝ E]

/-- Injectivity retains multiplicity correctly when comparing a finite orbit
sum with the whole lattice. No summability assumption on the orbit is used. -/
theorem sum_norm_weighted_schwartz_equiv_le {ι : Type*}
    (L : Submodule ℤ E) [DiscreteTopology L]
    (f : SchwartzMap E ℂ) (e : E ≃L[ℝ] E) (M : ℕ)
    (hM : Module.finrank ℤ L < M) {B C : ℝ}
    (hB : ‖e.symm.toContinuousLinearMap‖ ≤ B) (hC : 0 ≤ C)
    (j : ι → NonzeroLattice L) (hj : Function.Injective j)
    (b : ι → ℂ) (hb : ∀ i, ‖b i‖ ≤ C) (s : Finset ι) :
    (∑ i ∈ s, ‖b i * f (e (((j i : NonzeroLattice L) : L) : E))‖) ≤
      C * (SchwartzMap.seminorm ℂ M 0 f * B ^ M) * latticeInversePowerMass L M := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans hB
  have hcoef : 0 ≤ C * (SchwartzMap.seminorm ℂ M 0 f * B ^ M) :=
    mul_nonneg hC (mul_nonneg (apply_nonneg (SchwartzMap.seminorm ℂ M 0) f)
      (pow_nonneg hB0 M))
  calc
    _ ≤ ∑ i ∈ s, C * (SchwartzMap.seminorm ℂ M 0 f * B ^ M) *
        ‖(((j i : NonzeroLattice L) : L) : E)‖⁻¹ ^ M := by
      apply Finset.sum_le_sum
      intro i _hi
      rw [norm_mul]
      calc
        _ ≤ C * ‖f (e (((j i : NonzeroLattice L) : L) : E))‖ :=
          mul_le_mul_of_nonneg_right (hb i) (norm_nonneg _)
        _ ≤ C * (SchwartzMap.seminorm ℂ M 0 f * B ^ M *
            ‖(((j i : NonzeroLattice L) : L) : E)‖⁻¹ ^ M) := by
          apply mul_le_mul_of_nonneg_left _ hC
          exact norm_schwartz_equiv_le_inverse_power f e M hB (by
            intro hz
            exact (j i).property (Subtype.ext hz))
        _ = _ := by ring
    _ = C * (SchwartzMap.seminorm ℂ M 0 f * B ^ M) *
        ∑ l ∈ s.image j, ‖((l : L) : E)‖⁻¹ ^ M := by
      rw [Finset.sum_image]
      · rw [Finset.mul_sum]
      · intro i _ k _ hik
        exact hj hik
    _ ≤ _ := mul_le_mul_of_nonneg_left
      ((summable_lattice_inverse_power L M hM).sum_le_tsum (s.image j)
        (fun _ _ => by positivity)) hcoef

/-- Only indices with nonzero finite coefficient need an arithmetic lattice
embedding. Zero coefficients are removed before the injective comparison. -/
theorem sum_norm_weighted_schwartz_le_of_support {ι : Type*}
    (L : Submodule ℤ E) [DiscreteTopology L]
    (f : SchwartzMap E ℂ) (e : E ≃L[ℝ] E) (M : ℕ)
    (hM : Module.finrank ℤ L < M) {B C : ℝ}
    (hB : ‖e.symm.toContinuousLinearMap‖ ≤ B) (hC : 0 ≤ C)
    (v : ι → E) (b : ι → ℂ) (hb : ∀ i, ‖b i‖ ≤ C)
    (j : {i : ι // b i ≠ 0} → NonzeroLattice L) (hj : Function.Injective j)
    (hmatch : ∀ i, e (((j i : NonzeroLattice L) : L) : E) = v i.val)
    (s : Finset ι) :
    (∑ i ∈ s, ‖b i * f (v i)‖) ≤
      C * (SchwartzMap.seminorm ℂ M 0 f * B ^ M) * latticeInversePowerMass L M := by
  have hfilter : (∑ i ∈ s with b i ≠ 0, ‖b i * f (v i)‖) =
      ∑ i ∈ s, ‖b i * f (v i)‖ := by
    apply Finset.sum_filter_of_ne
    intro i _hi hn hbi
    apply hn
    rw [hbi, zero_mul, norm_zero]
  calc
    _ = ∑ i ∈ s.subtype (fun i => b i ≠ 0), ‖b i.val * f (v i.val)‖ := by
      rw [Finset.sum_subtype_eq_sum_filter (fun i => ‖b i * f (v i)‖)]
      exact hfilter.symm
    _ ≤ _ := by
      have h := sum_norm_weighted_schwartz_equiv_le L f e M hM hB hC j hj
        (fun i => b i.val) (fun i => hb i.val) (s.subtype (fun i => b i ≠ 0))
      simpa only [hmatch] using h

variable (K : Type*) [Field K] [NumberField K]

private theorem normAtPlace_unit_ne_zero
    (u : (mixedEmbedding.mixedSpace K)ˣ) (w : InfinitePlace K) :
    mixedEmbedding.normAtPlace w (u : mixedEmbedding.mixedSpace K) ≠ 0 := by
  apply mixedEmbedding.norm_ne_zero_iff.mp
  have hm := congrArg mixedEmbedding.norm u.val_inv
  rw [map_mul, map_one] at hm
  intro hz
  rw [hz, zero_mul] at hm
  exact zero_ne_one hm

/-- Multiplication by the given actual mixed-space unit in the trace metric. -/
def traceUnitMulEquiv (u : (mixedEmbedding.mixedSpace K)ˣ) :
    mixedEmbedding.euclidean.mixedSpace K ≃L[ℝ]
      mixedEmbedding.euclidean.mixedSpace K :=
  traceCoordinateMulEquiv K u (normAtPlace_unit_ne_zero K u)

theorem traceToMixed_traceUnitMulEquiv
    (u : (mixedEmbedding.mixedSpace K)ˣ) (z : mixedEmbedding.euclidean.mixedSpace K) :
    traceToMixed K (traceUnitMulEquiv K u z) =
      (u : mixedEmbedding.mixedSpace K) * traceToMixed K z := by
  change traceToMixed K ((traceToMixed K).symm
    ((u : mixedEmbedding.mixedSpace K) * traceToMixed K z)) = _
  exact (traceToMixed K).apply_symm_apply _

theorem continuous_traceUnitMulEquiv_inverseCLM :
    Continuous (fun u : (mixedEmbedding.mixedSpace K)ˣ =>
      (traceUnitMulEquiv K u).symm.toContinuousLinearMap) :=
  continuous_traceCoordinateMulEquiv_inverseCLM K _ Units.continuous_val
    (normAtPlace_unit_ne_zero K)

/-- The constant is obtained from the given actual compact unit set. -/
theorem exists_uniform_traceUnit_inverse_bound
    (C : Set (mixedEmbedding.mixedSpace K)ˣ) (hC : IsCompact C) :
    ∃ B : ℝ, 0 < B ∧ ∀ u ∈ C,
      ‖(traceUnitMulEquiv K u).symm.toContinuousLinearMap‖ ≤ B := by
  obtain ⟨B, hB, hb⟩ :=
    (hC.image (continuous_traceUnitMulEquiv_inverseCLM K)).isBounded.exists_pos_norm_le
  exact ⟨B, hB, fun u hu => hb _ (Set.mem_image_of_mem _ hu)⟩

end HeckeGeneral.Analysis
