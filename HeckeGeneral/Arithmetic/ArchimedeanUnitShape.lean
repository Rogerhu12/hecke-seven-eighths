import HeckeGeneral.Arithmetic.FiniteIndexUnitBalancing
import HeckeGeneral.Analysis.BalancedLatticeShape
import Mathlib.Topology.Algebra.Group.Units

/-!
# The actual unit-group lift of the compact archimedean shape

The mixed algebra is a product of real and complex fields, rather than a
field. Its nonzero multiplicative norm ensures every coordinate is nonzero.
We reuse the existing coordinate inverse and its continuous dependence to
lift the finite-index unit shape into the actual unit group.

Build and declaration-audit evidence is tracked in docs/NEXT_POISSON.md.
-/

noncomputable section

namespace HeckeGeneral.Arithmetic

open NumberField NumberField.mixedEmbedding HeckeGeneral.Analysis
open scoped Classical

variable (K : Type*) [Field K] [NumberField K]

theorem mixed_mul_coordinateInverse {x : mixedSpace K}
    (hx : mixedEmbedding.norm x ≠ 0) : x * mixedCoordinateInverse K x = 1 := by
  have h := (mixedCoordinateMulEquiv K x
    (mixedEmbedding.norm_ne_zero_iff.mp hx)).apply_symm_apply (1 : mixedSpace K)
  change x * (mixedCoordinateInverse K x * 1) = 1 at h
  simpa only [mul_one] using h

/-- A genuine unit, constructed using the already verified coordinate inverse. -/
def mixedUnitOfNormNeZero (x : mixedSpace K) (hx : mixedEmbedding.norm x ≠ 0) :
    (mixedSpace K)ˣ where
  val := x
  inv := mixedCoordinateInverse K x
  val_inv := mixed_mul_coordinateInverse K hx
  inv_val := by rw [mul_comm]; exact mixed_mul_coordinateInverse K hx

@[simp] theorem mixedUnitOfNormNeZero_val (x : mixedSpace K)
    (hx : mixedEmbedding.norm x ≠ 0) :
    (mixedUnitOfNormNeZero K x hx).val = x := rfl

@[simp] theorem mixedUnitOfNormNeZero_inv_val (x : mixedSpace K)
    (hx : mixedEmbedding.norm x ≠ 0) :
    ((mixedUnitOfNormNeZero K x hx)⁻¹).val = mixedCoordinateInverse K x := rfl

theorem continuous_mixedUnitOfNormNeZero {T : Type*} [TopologicalSpace T]
    (x : T → mixedSpace K) (hc : Continuous x)
    (hx : ∀ t, mixedEmbedding.norm (x t) ≠ 0) :
    Continuous (fun t => mixedUnitOfNormNeZero K (x t) (hx t)) := by
  apply Units.continuous_iff.mpr
  exact ⟨hc, continuous_mixedCoordinateInverse K x hc
    (fun t => mixedEmbedding.norm_ne_zero_iff.mp (hx t))⟩

abbrev FiniteIndexArchShape (Γ : Subgroup (𝓞 K)ˣ) :=
  {x : mixedSpace K // x ∈ finiteIndexBalancedShape K Γ}

def finiteIndexArchShapeUnit (Γ : Subgroup (𝓞 K)ˣ)
    (x : FiniteIndexArchShape K Γ) : (mixedSpace K)ˣ :=
  mixedUnitOfNormNeZero K x (by
    rw [norm_eq_one_of_mem_finiteIndexBalancedShape K Γ x.property]
    exact one_ne_zero)

@[simp] theorem finiteIndexArchShapeUnit_val (Γ : Subgroup (𝓞 K)ˣ)
    (x : FiniteIndexArchShape K Γ) : (finiteIndexArchShapeUnit K Γ x).val = x := rfl

theorem continuous_finiteIndexArchShapeUnit (Γ : Subgroup (𝓞 K)ˣ) :
    Continuous (finiteIndexArchShapeUnit K Γ) := by
  exact continuous_mixedUnitOfNormNeZero K Subtype.val continuous_subtype_val
    (fun x => by
      rw [norm_eq_one_of_mem_finiteIndexBalancedShape K Γ x.property]
      exact one_ne_zero)

/-- The compact shape now lies in the actual archimedean multiplication group. -/
def finiteIndexArchUnitShape (Γ : Subgroup (𝓞 K)ˣ) : Set (mixedSpace K)ˣ :=
  Set.range (finiteIndexArchShapeUnit K Γ)

theorem isCompact_finiteIndexArchUnitShape (Γ : Subgroup (𝓞 K)ˣ) [Γ.FiniteIndex] :
    IsCompact (finiteIndexArchUnitShape K Γ) := by
  have hc : IsCompact (Set.univ : Set (FiniteIndexArchShape K Γ)) :=
    isCompact_iff_isCompact_univ.mp (isCompact_finiteIndexBalancedShape K Γ)
  simpa only [finiteIndexArchUnitShape, Set.image_univ] using
    hc.image (continuous_finiteIndexArchShapeUnit K Γ)

theorem mem_finiteIndexArchUnitShape_iff (Γ : Subgroup (𝓞 K)ˣ)
    (u : (mixedSpace K)ˣ) :
    u ∈ finiteIndexArchUnitShape K Γ ↔ u.val ∈ finiteIndexBalancedShape K Γ := by
  constructor
  · rintro ⟨x, rfl⟩
    exact x.property
  · intro hu
    refine ⟨⟨u.val, hu⟩, ?_⟩
    apply Units.ext
    rfl

theorem norm_eq_one_of_mem_finiteIndexArchUnitShape (Γ : Subgroup (𝓞 K)ˣ)
    {u : (mixedSpace K)ˣ} (hu : u ∈ finiteIndexArchUnitShape K Γ) :
    mixedEmbedding.norm u.val = 1 :=
  norm_eq_one_of_mem_finiteIndexBalancedShape K Γ
    ((mem_finiteIndexArchUnitShape_iff K Γ u).mp hu)

end HeckeGeneral.Arithmetic
