import HeckeGeneral.Analysis.TraceProductCovolume
import HeckeGeneral.Analysis.TraceJointSchwartzFourierBounds
import HeckeGeneral.Analysis.LatticeFiniteMask

/-!
# Genuine two-column Poisson summation

Both sums retain the coordinate axes. The nonzero identity removes precisely
the single vector `(0,0)`, not the union of the two axes. Absolute summability
comes from the existing Schwartz lattice theorems. The mixed operator is the
actual operator defined by the two-column mixed Haar integral, with both
conjugate frequencies and the squared Jacobian retained.
-/

noncomputable section

namespace HeckeGeneral.Analysis

open HeckeGeneral.Arithmetic NumberField NumberField.InfinitePlace MeasureTheory
open scoped Classical FourierTransform nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]

local notation "W" => traceProductSpace K

/-- Actual translated inner-product PSF on both trace ideal columns. -/
theorem traceProductPoisson
    (I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (F : SchwartzMap W ℂ) (v : W) :
    (∑' l : traceProductIdealLattice K I J, F (v + l)) =
      (1 / ZLattice.covolume (traceProductIdealLattice K I J) : ℂ) *
        ∑' m : dualLattice (traceProductIdealLattice K I J),
          (𝓕 ⇑F m) * Complex.exp (2 * Real.pi * Complex.I * inner ℝ v m) :=
  poissonSummation_innerProductSpace _ F v

/-- At zero translation, the actual inner-product Fourier lattice sum. -/
theorem traceProductPoisson_zero
    (I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (F : SchwartzMap W ℂ) :
    (∑' l : traceProductIdealLattice K I J, F l) =
      (1 / ZLattice.covolume (traceProductIdealLattice K I J) : ℂ) *
        ∑' m : dualLattice (traceProductIdealLattice K I J), 𝓕 ⇑F m := by
  simpa using traceProductPoisson K I J F 0

/-- Explicit conjugate inverse-different frequency indexing. The arithmetic
identity for `traceDualIdealUnit` is already supplied by TraceDualIdeal. -/
theorem traceProductPoisson_conjugateDual
    (I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (F : SchwartzMap W ℂ) :
    (∑' l : traceProductIdealLattice K I J, F l) =
      (1 / ZLattice.covolume (traceProductIdealLattice K I J) : ℂ) *
        ∑' m : lpProductLattice
          (conjugateTraceIdealLattice K (traceDualIdealUnit K I))
          (conjugateTraceIdealLattice K (traceDualIdealUnit K J)), 𝓕 ⇑F m := by
  rw [← dualLattice_traceProductIdealLattice_eq_conjugate]
  exact traceProductPoisson_zero K I J F

/-- Only the single origin is removed; mixed-axis frequencies remain. -/
theorem traceProductPoisson_nonzero
    (I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (F : SchwartzMap W ℂ) :
    (∑' l : traceProductIdealLattice K I J, if l = 0 then 0 else F l) =
      (1 / ZLattice.covolume (traceProductIdealLattice K I J) : ℂ) *
        (∑' m : dualLattice (traceProductIdealLattice K I J),
          if m = 0 then 0 else 𝓕 ⇑F m) +
      (1 / ZLattice.covolume (traceProductIdealLattice K I J) : ℂ) *
        (𝓕 ⇑F 0) - F 0 := by
  have hl : Summable fun l : traceProductIdealLattice K I J => F (l : W) := by
    simpa using (summable_norm_schwartz_lattice (traceProductIdealLattice K I J) F 0).of_norm
  have hm := (summable_norm_fourier_lattice (traceProductIdealLattice K I J) F).of_norm
  have h := traceProductPoisson_zero K I J F
  rw [hl.tsum_eq_add_tsum_ite 0, hm.tsum_eq_add_tsum_ite 0] at h
  simp only [Submodule.coe_zero] at h
  linear_combination h

/-- The precise two-column mixed-Haar coefficient. -/
def traceProductMixedPoissonCoefficient
    (I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : ℂ :=
  (((((2 : ℝ) ^ nrComplexPlaces K) ^ 2) : ℝ) : ℂ) /
    (ZLattice.covolume (traceProductIdealLattice K I J) : ℂ)

theorem traceProductMixedPoissonCoefficient_eq
    (I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    traceProductMixedPoissonCoefficient K I J =
      (2 : ℂ) ^ (2 * nrComplexPlaces K) /
        ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) *
          FractionalIdeal.absNorm (J : FractionalIdeal (𝓞 K)⁰ K) *
            |(discr K : ℝ)| : ℝ) : ℂ) := by
  unfold traceProductMixedPoissonCoefficient
  rw [covolume_traceProductIdealLattice]
  push_cast
  rw [← pow_mul, Nat.mul_comm (nrComplexPlaces K) 2]

private theorem fourier_eq_jacobian_traceJointFourier
    (F : SchwartzMap W ℂ) (m : W) :
    𝓕 ⇑F m =
      (((((2 : ℝ) ^ nrComplexPlaces K) ^ 2) : ℝ) : ℂ) *
        traceJointFourierCLM K F ((traceJointConjugation K).symm m) := by
  rw [traceJointFourierCLM_apply, LinearIsometryEquiv.apply_symm_apply]
  have hj : (((((2 : ℝ) ^ nrComplexPlaces K) ^ 2) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast pow_ne_zero 2 (pow_ne_zero (nrComplexPlaces K) (by norm_num : (2 : ℝ) ≠ 0))
  push_cast at hj ⊢
  rw [← mul_assoc, mul_inv_cancel₀ hj, one_mul]

/-- The genuine mixed Fourier formula. Frequencies are indexed by the actual
polar lattice and un-conjugated in the operator argument. By the preceding
conjugate-dual identity, this is the conjugate inverse-different product,
not an assumed self-dual lattice. -/
theorem traceProductPoisson_mixed
    (I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (F : SchwartzMap W ℂ) :
    (∑' l : traceProductIdealLattice K I J, F l) =
      traceProductMixedPoissonCoefficient K I J *
        ∑' m : dualLattice (traceProductIdealLattice K I J),
          traceJointFourierCLM K F ((traceJointConjugation K).symm (m : W)) := by
  have h := traceProductPoisson_zero K I J F
  simp_rw [fourier_eq_jacobian_traceJointFourier K F] at h
  rw [tsum_mul_left] at h
  rw [h]
  unfold traceProductMixedPoissonCoefficient
  ring

/-- Exact removal of the one mixed-Fourier origin, retaining both axes and
both true zero terms. No summability hypothesis is added. -/
theorem traceProductPoisson_mixed_nonzero
    (I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (F : SchwartzMap W ℂ) :
    (∑' l : traceProductIdealLattice K I J, if l = 0 then 0 else F l) =
      traceProductMixedPoissonCoefficient K I J *
        (∑' m : dualLattice (traceProductIdealLattice K I J),
          if m = 0 then 0 else
            traceJointFourierCLM K F ((traceJointConjugation K).symm (m : W))) +
      traceProductMixedPoissonCoefficient K I J * traceJointFourierCLM K F 0 - F 0 := by
  have h := traceProductPoisson_nonzero K I J F
  simp_rw [fourier_eq_jacobian_traceJointFourier K F] at h
  simp only [map_zero] at h
  have heq :
      (∑' m : dualLattice (traceProductIdealLattice K I J),
        if m = 0 then 0 else
          (((((2 : ℝ) ^ nrComplexPlaces K) ^ 2) : ℝ) : ℂ) *
            traceJointFourierCLM K F ((traceJointConjugation K).symm (m : W))) =
      (((((2 : ℝ) ^ nrComplexPlaces K) ^ 2) : ℝ) : ℂ) *
        (∑' m : dualLattice (traceProductIdealLattice K I J),
          if m = 0 then 0 else
            traceJointFourierCLM K F ((traceJointConjugation K).symm (m : W))) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro m
    split_ifs <;> simp
  rw [heq] at h
  rw [h]
  unfold traceProductMixedPoissonCoefficient
  ring

end HeckeGeneral.Analysis
