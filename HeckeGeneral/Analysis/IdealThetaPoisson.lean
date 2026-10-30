import HeckeGeneral.Analysis.LatticePoisson
import HeckeGeneral.Arithmetic.IdealTraceLattice

/-!
# Poisson summation on the actual trace-weighted ideal lattice

The Euclidean-coordinate Poisson theorem is transported by an orthonormal
basis. Its Fourier transform and covolume use the standard additive volume.
No second proof of Poisson summation or additional analytic input is assumed.
-/

open MeasureTheory NumberField Classical
open scoped FourierTransform Real nonZeroDivisors

noncomputable section

namespace HeckeGeneral.Analysis

open HeckeGeneral.Arithmetic

section InnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The actual polar lattice commutes with an isometric change of coordinates. -/
theorem dualLattice_comap_linearIsometry (L : Submodule ℤ E) (e : F ≃ₗᵢ[ℝ] E) :
    dualLattice (ZLattice.comap ℝ L e.toLinearEquiv.toLinearMap) =
      ZLattice.comap ℝ (dualLattice L) e.toLinearEquiv.toLinearMap := by
  ext x
  change (∀ y ∈ ZLattice.comap ℝ L e.toLinearEquiv.toLinearMap,
      inner ℝ x y ∈ (1 : Submodule ℤ ℝ)) ↔
    ∀ y ∈ L, inner ℝ (e x) y ∈ (1 : Submodule ℤ ℝ)
  constructor
  · intro hx y hy
    have hmem : e.symm y ∈ ZLattice.comap ℝ L e.toLinearEquiv.toLinearMap := by
      change e (e.symm y) ∈ L
      simpa using hy
    have h := hx (e.symm y) hmem
    rw [← e.inner_map_map x (e.symm y), e.apply_symm_apply] at h
    exact h
  · intro hx y hy
    change e y ∈ L at hy
    have h := hx (e y) hy
    rwa [e.inner_map_map] at h

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Genuine translated Poisson summation in an arbitrary finite-dimensional
real inner-product space, obtained from the Euclidean-space theorem. -/
theorem poissonSummation_innerProductSpace (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] (f : SchwartzMap E ℂ) (v : E) :
    ∑' l : L, f (v + l) = (1 / ZLattice.covolume L : ℂ) *
      ∑' m : dualLattice L,
        (𝓕 ⇑f m) * Complex.exp (2 * Real.pi * Complex.I * inner ℝ v m) := by
  let A : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) ≃ₗᵢ[ℝ] E :=
    (stdOrthonormalBasis ℝ E).repr.symm
  let L₀ : Submodule ℤ (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :=
    ZLattice.comap ℝ L A.toContinuousLinearEquiv.toLinearMap
  let f₀ : SchwartzMap (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) ℂ :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.toContinuousLinearEquiv f
  have hA : MeasurePreserving A volume volume := A.measurePreserving
  have hcov : ZLattice.covolume L₀ = ZLattice.covolume L :=
    ZLattice.covolume_comap L (μ := volume) (ν := volume)
      (e := A.toContinuousLinearEquiv) hA
  have hdual : SchwartzMap.polarIntegerLattice L₀ =
      ZLattice.comap ℝ (dualLattice L) A.toLinearEquiv.toLinearMap :=
    dualLattice_comap_linearIsometry L A
  have hlhs : (∑' l : L₀, f₀ (A.symm v + l)) = ∑' l : L, f (v + l) := by
    change (∑' l : ZLattice.comap ℝ L A.toLinearEquiv.toLinearMap,
      f₀ (A.symm v + l)) = _
    rw [← (ZLattice.comap_equiv ℝ L A.toLinearEquiv).toEquiv.tsum_eq]
    apply tsum_congr
    intro l
    simp [f₀, A.map_add]
  have hrhs : (∑' m : SchwartzMap.polarIntegerLattice L₀,
      𝓕 ⇑f₀ m * Complex.exp (2 * Real.pi * Complex.I * inner ℝ (A.symm v) m)) =
      ∑' m : dualLattice L,
        𝓕 ⇑f m * Complex.exp (2 * Real.pi * Complex.I * inner ℝ v m) := by
    rw [hdual, ← (ZLattice.comap_equiv ℝ (dualLattice L) A.toLinearEquiv).toEquiv.tsum_eq]
    apply tsum_congr
    intro m
    change 𝓕 (⇑f ∘ A) (A.symm m) *
      Complex.exp (2 * Real.pi * Complex.I * inner ℝ (A.symm v) (A.symm m)) = _
    rw [Real.fourier_comp_linearIsometry, A.apply_symm_apply, A.symm.inner_map_map]
  have h := SchwartzMap.latticePoissonSummationFormula L₀ f₀ (A.symm v)
  simpa only [← RCLike.inner_eq_wInner_one, hlhs, hcov, hrhs] using h

end InnerProductSpace

section NumberField

variable (K : Type*) [Field K] [NumberField K]

/-- Translated Poisson summation on the genuine trace-weighted embedding of a
nonzero fractional ideal. Its frequencies are the embedded conjugate of the
trace-dual ideal; `coe_traceDualIdealUnit_eq_inverseDifferent_mul_inv` gives the
explicit inverse-different description of that arithmetic ideal. -/
theorem idealTracePoisson
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (f : SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ)
    (v : mixedEmbedding.euclidean.mixedSpace K) :
    ∑' l : traceIdealLattice K I, f (v + l) =
      (1 / ZLattice.covolume (traceIdealLattice K I) : ℂ) *
      ∑' m : conjugateTraceIdealLattice K (traceDualIdealUnit K I),
        (𝓕 ⇑f m) * Complex.exp (2 * Real.pi * Complex.I * inner ℝ v m) := by
  rw [← dualLattice_traceIdealLattice]
  exact poissonSummation_innerProductSpace (traceIdealLattice K I) f v

end NumberField

end HeckeGeneral.Analysis
