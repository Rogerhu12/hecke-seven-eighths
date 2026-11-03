import HeckeGeneral.Analysis.TraceProductLattice
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Covolume of the actual two-column trace lattice

The ordinary product lattice has a product fundamental domain. The canonical
WithLp coordinate equivalence preserves the actual Hilbert-space volume, so
there is no additional factor from the change of product norm. Each weighted
trace lattice contributes `N(I) * sqrt |D_K|`; together they contribute
`N(I) * N(J) * |D_K|`. No dual-lattice conjugation is changed here.
-/

noncomputable section

namespace HeckeGeneral.Analysis

open HeckeGeneral.Arithmetic NumberField NumberField.InfinitePlace
  MeasureTheory Module ZSpan
open scoped Classical nonZeroDivisors

section Product

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The product-submodule topology is the product of the two discrete topologies. -/
instance discreteTopology_prodSubmodule (L : Submodule ℤ E) (M : Submodule ℤ F)
    [DiscreteTopology L] [DiscreteTopology M] : DiscreteTopology (L.prod M) := by
  change DiscreteTopology ↥((L : Set E) ×ˢ (M : Set F))
  exact (Homeomorph.Set.prod (L : Set E) (M : Set F)).isEmbedding.discreteTopology

/-- The two actual spans fill both axes of the product space. -/
instance isZLattice_prodSubmodule (L : Submodule ℤ E) (M : Submodule ℤ F)
    [DiscreteTopology L] [DiscreteTopology M]
    [IsZLattice ℝ L] [IsZLattice ℝ M] : IsZLattice ℝ (L.prod M) where
  span_top := by
    change Submodule.span ℝ ((L : Set E) ×ˢ (M : Set F)) = ⊤
    rw [Submodule.span_prod_eq ℝ L.zero_mem M.zero_mem,
      IsZLattice.span_top (K := ℝ) (L := L),
      IsZLattice.span_top (K := ℝ) (L := M)]
    simp

variable {ι κ : Type*}

private theorem span_basis_prod (b : Basis ι ℝ E) (c : Basis κ ℝ F) :
    Submodule.span ℤ (Set.range (b.prod c)) =
      (Submodule.span ℤ (Set.range b)).prod (Submodule.span ℤ (Set.range c)) := by
  ext x
  rw [(b.prod c).mem_span_iff_repr_mem ℤ, Submodule.mem_prod,
    b.mem_span_iff_repr_mem ℤ, c.mem_span_iff_repr_mem ℤ]
  simp only [Sum.forall, Basis.prod_repr_inl, Basis.prod_repr_inr]

private theorem fundamentalDomain_basis_prod (b : Basis ι ℝ E) (c : Basis κ ℝ F) :
    fundamentalDomain (b.prod c) = fundamentalDomain b ×ˢ fundamentalDomain c := by
  ext x
  simp only [mem_fundamentalDomain, Set.mem_prod, Sum.forall,
    Basis.prod_repr_inl, Basis.prod_repr_inr]

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]

/-- Covolume of the genuine product submodule with product Lebesgue volume. -/
theorem covolume_prodSubmodule (L : Submodule ℤ E) (M : Submodule ℤ F)
    [DiscreteTopology L] [DiscreteTopology M]
    [IsZLattice ℝ L] [IsZLattice ℝ M] :
    ZLattice.covolume (L.prod M) = ZLattice.covolume L * ZLattice.covolume M := by
  letI : (volume : Measure (E × F)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]
    infer_instance
  let b := Free.chooseBasis ℤ L
  let c := Free.chooseBasis ℤ M
  let bR := b.ofZLatticeBasis ℝ
  let cR := c.ofZLatticeBasis ℝ
  have hspan : Submodule.span ℤ (Set.range (bR.prod cR)) = L.prod M := by
    rw [span_basis_prod]
    exact congrArg₂ (fun (L' : Submodule ℤ E) (M' : Submodule ℤ F) => L'.prod M')
      (b.ofZLatticeBasis_span ℝ) (c.ofZLatticeBasis_span ℝ)
  have hFD : IsAddFundamentalDomain (L.prod M)
      (fundamentalDomain (bR.prod cR)) volume := by
    rw [← hspan]
    exact ZSpan.isAddFundamentalDomain (bR.prod cR) volume
  rw [ZLattice.covolume_eq_measure_fundamentalDomain (L.prod M) volume hFD,
    fundamentalDomain_basis_prod, Measure.volume_eq_prod,
    measureReal_prod_prod,
    ZLattice.covolume_eq_measure_fundamentalDomain L volume
      (ZLattice.isAddFundamentalDomain b volume),
    ZLattice.covolume_eq_measure_fundamentalDomain M volume
      (ZLattice.isAddFundamentalDomain c volume)]

end Product

section HilbertProduct

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

instance discreteTopology_lpProductLattice (L : Submodule ℤ E) (M : Submodule ℤ F)
    [DiscreteTopology L] [DiscreteTopology M] :
    DiscreteTopology (lpProductLattice L M) := by
  unfold lpProductLattice
  infer_instance

instance isZLattice_lpProductLattice (L : Submodule ℤ E) (M : Submodule ℤ F)
    [DiscreteTopology L] [DiscreteTopology M]
    [IsZLattice ℝ L] [IsZLattice ℝ M] : IsZLattice ℝ (lpProductLattice L M) := by
  unfold lpProductLattice
  infer_instance

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]

/-- Exact volume transport for the actual WithLp coordinate equivalence. -/
theorem measurePreserving_lpProductEquiv :
    MeasurePreserving (WithLp.prodContinuousLinearEquiv 2 ℝ E F)
      (volume : Measure (WithLp 2 (E × F))) (volume : Measure (E × F)) :=
  WithLp.volume_preserving_ofLp E F

theorem covolume_lpProductLattice (L : Submodule ℤ E) (M : Submodule ℤ F)
    [DiscreteTopology L] [DiscreteTopology M]
    [IsZLattice ℝ L] [IsZLattice ℝ M] :
    ZLattice.covolume (lpProductLattice L M) =
      ZLattice.covolume L * ZLattice.covolume M := by
  letI : (volume : Measure (E × F)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]
    infer_instance
  rw [lpProductLattice, ZLattice.covolume_comap (L.prod M) volume volume
    (measurePreserving_lpProductEquiv (E := E) (F := F)), covolume_prodSubmodule]

end HilbertProduct

variable (K : Type*) [Field K] [NumberField K]

/-- The canonical inner-product volume, with its component instances supplied
explicitly to keep inference through the nested Hilbert products bounded. -/
instance (priority := 100) measureSpace_traceProductSpace :
    MeasureSpace (traceProductSpace K) := by
  letI : BorelSpace (traceProductSpace K) := inferInstance
  exact measureSpaceOfInnerProductSpace

instance discreteTopology_traceProductIdealLattice
    (I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    DiscreteTopology (traceProductIdealLattice K I J) := by
  unfold traceProductIdealLattice
  infer_instance

instance isZLattice_traceProductIdealLattice
    (I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    IsZLattice ℝ (traceProductIdealLattice K I J) := by
  unfold traceProductIdealLattice
  infer_instance

theorem covolume_traceProductIdealLattice_mul
    (I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ZLattice.covolume (traceProductIdealLattice K I J)
        (volume (α := traceProductSpace K)) =
      ZLattice.covolume (traceIdealLattice K I) *
        ZLattice.covolume (traceIdealLattice K J) :=
  covolume_lpProductLattice
    (E := mixedEmbedding.euclidean.mixedSpace K)
    (F := mixedEmbedding.euclidean.mixedSpace K) _ _

/-- The exact arithmetic covolume of the actual two-column trace lattice. -/
theorem covolume_traceProductIdealLattice
    (I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ZLattice.covolume (traceProductIdealLattice K I J)
        (volume (α := traceProductSpace K)) =
      FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) *
        FractionalIdeal.absNorm (J : FractionalIdeal (𝓞 K)⁰ K) * |(discr K : ℝ)| := by
  rw [covolume_traceProductIdealLattice_mul]
  simp only [covolume_traceIdealLattice]
  calc
    _ = FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) *
        FractionalIdeal.absNorm (J : FractionalIdeal (𝓞 K)⁰ K) *
          (Real.sqrt |(discr K : ℝ)|) ^ 2 := by ring
    _ = _ := by rw [Real.sq_sqrt (abs_nonneg _)]

end HeckeGeneral.Analysis
