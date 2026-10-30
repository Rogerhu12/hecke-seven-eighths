import HeckeGeneral.Arithmetic.TraceLatticeCovolume
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# The actual two-column trace lattice

The two columns live in the Hilbert product, whose inner product is the sum
of the two actual trace-coordinate inner products. Testing the two axes
identifies its polar with the product of the two polars. The ideal-lattice
specialization retains the conjugation in the existing trace-dual formula.

This module does not assert a product-covolume identity.
-/

noncomputable section

namespace HeckeGeneral.Analysis

open HeckeGeneral.Arithmetic NumberField NumberField.InfinitePlace
open scoped Classical InnerProductSpace nonZeroDivisors

section Product

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The actual inverse image of the product submodule in Hilbert coordinates. -/
def lpProductLattice (L : Submodule ℤ E) (M : Submodule ℤ F) :
    Submodule ℤ (WithLp 2 (E × F)) :=
  ZLattice.comap ℝ (L.prod M)
    (WithLp.prodContinuousLinearEquiv 2 ℝ E F).toLinearMap

@[simp]
theorem mem_lpProductLattice (L : Submodule ℤ E) (M : Submodule ℤ F)
    (x : WithLp 2 (E × F)) :
    x ∈ lpProductLattice L M ↔
      (WithLp.ofLp x).1 ∈ L ∧ (WithLp.ofLp x).2 ∈ M :=
  Iff.rfl

/-- The polar of the actual Hilbert-product lattice is the product polar.
No full-rank or discreteness hypothesis is needed for this identity. -/
theorem dualLattice_lpProductLattice (L : Submodule ℤ E) (M : Submodule ℤ F) :
    dualLattice (lpProductLattice L M) =
      lpProductLattice (dualLattice L) (dualLattice M) := by
  ext x
  rw [mem_lpProductLattice]
  constructor
  · intro hx
    change ∀ y ∈ lpProductLattice L M,
      ⟪x, y⟫_ℝ ∈ (1 : Submodule ℤ ℝ) at hx
    constructor
    · change ∀ y ∈ L, ⟪(WithLp.ofLp x).1, y⟫_ℝ ∈ (1 : Submodule ℤ ℝ)
      intro y hy
      have haxis : WithLp.toLp 2 (y, (0 : F)) ∈ lpProductLattice L M := by
        rw [mem_lpProductLattice]
        exact ⟨hy, M.zero_mem⟩
      simpa only [WithLp.prod_inner_apply, WithLp.ofLp_toLp,
        inner_zero_right, add_zero] using hx _ haxis
    · change ∀ y ∈ M, ⟪(WithLp.ofLp x).2, y⟫_ℝ ∈ (1 : Submodule ℤ ℝ)
      intro y hy
      have haxis : WithLp.toLp 2 ((0 : E), y) ∈ lpProductLattice L M := by
        rw [mem_lpProductLattice]
        exact ⟨L.zero_mem, hy⟩
      simpa only [WithLp.prod_inner_apply, WithLp.ofLp_toLp,
        inner_zero_right, zero_add] using hx _ haxis
  · rintro ⟨hxL, hxM⟩
    change ∀ y ∈ L, ⟪(WithLp.ofLp x).1, y⟫_ℝ ∈ (1 : Submodule ℤ ℝ) at hxL
    change ∀ y ∈ M, ⟪(WithLp.ofLp x).2, y⟫_ℝ ∈ (1 : Submodule ℤ ℝ) at hxM
    change ∀ y ∈ lpProductLattice L M,
      ⟪x, y⟫_ℝ ∈ (1 : Submodule ℤ ℝ)
    intro y hy
    obtain ⟨hyL, hyM⟩ := (mem_lpProductLattice L M y).mp hy
    simpa only [WithLp.prod_inner_apply] using
      add_mem (hxL _ hyL) (hxM _ hyM)

end Product

variable (K : Type*) [Field K] [NumberField K]

/-- The actual Hilbert space for two weighted trace columns. -/
abbrev traceProductSpace := WithLp 2
  (mixedEmbedding.euclidean.mixedSpace K × mixedEmbedding.euclidean.mixedSpace K)

/-- The coordinate equivalence used to pull back the product of ideal lattices. -/
def traceProductEquiv : traceProductSpace K ≃L[ℝ]
    (mixedEmbedding.euclidean.mixedSpace K × mixedEmbedding.euclidean.mixedSpace K) :=
  WithLp.prodContinuousLinearEquiv 2 ℝ _ _

/-- The two-column lattice for arbitrary nonzero fractional ideals. -/
def traceProductIdealLattice
    (I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : Submodule ℤ (traceProductSpace K) :=
  lpProductLattice
    (E := mixedEmbedding.euclidean.mixedSpace K)
    (F := mixedEmbedding.euclidean.mixedSpace K)
    (traceIdealLattice K I) (traceIdealLattice K J)

theorem dualLattice_traceProductIdealLattice
    (I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    dualLattice (traceProductIdealLattice K I J) =
      ZLattice.comap ℝ
        (E := mixedEmbedding.euclidean.mixedSpace K × mixedEmbedding.euclidean.mixedSpace K)
        (F := traceProductSpace K)
        ((dualLattice (traceIdealLattice K I)).prod
          (dualLattice (traceIdealLattice K J)))
        (traceProductEquiv K).toLinearMap :=
  dualLattice_lpProductLattice
    (E := mixedEmbedding.euclidean.mixedSpace K)
    (F := mixedEmbedding.euclidean.mixedSpace K) _ _

/-- The existing conjugate trace-dual identification, in both columns. -/
theorem dualLattice_traceProductIdealLattice_eq_conjugate
    (I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    dualLattice (traceProductIdealLattice K I J) =
      lpProductLattice
        (E := mixedEmbedding.euclidean.mixedSpace K)
        (F := mixedEmbedding.euclidean.mixedSpace K)
        (conjugateTraceIdealLattice K (traceDualIdealUnit K I))
        (conjugateTraceIdealLattice K (traceDualIdealUnit K J)) := by
  rw [traceProductIdealLattice, dualLattice_lpProductLattice,
    dualLattice_traceIdealLattice, dualLattice_traceIdealLattice]

/-- Two trace columns have twice the real dimension of one number-field column. -/
theorem finrank_traceProductSpace :
    Module.finrank ℝ (traceProductSpace K) = 2 * Module.finrank ℚ K := by
  rw [LinearEquiv.finrank_eq (traceProductEquiv K).toLinearEquiv]
  simp only [Module.finrank_prod, mixedEmbedding.euclidean.finrank]
  omega

end HeckeGeneral.Analysis
