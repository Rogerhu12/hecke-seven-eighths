import HeckeGeneral.Arithmetic.IdealLatticeQuotient
import HeckeGeneral.Analysis.TraceProductCovolume
import HeckeGeneral.Analysis.LatticeFiniteMask
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic

/-!
# The ordinary two-column trace quotient

This candidate identifies the actual quotient of the ordinary trace product
lattice by the two copies of an integral ideal with the two actual residue
rings. Integer representatives are preserved. The norm-square cardinal and
the arithmetic covolume consequently cancel, leaving the absolute field
discriminant. UNCOMPILED: no native verification is claimed.
-/

noncomputable section

namespace HeckeGeneral.Analysis.ActualTraceProductResidueQuotientDraft

open HeckeGeneral.Arithmetic NumberField MeasureTheory
open scoped Classical nonZeroDivisors

variable (K : Type*) [Field K] [NumberField K]

local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "W" => traceProductSpace K

/-- The actual ordinary two-column trace lattice. -/
abbrev ordinaryProductLattice : Submodule ℤ W := traceProductIdealLattice K 1 1

/-- The actual two-column sublattice cut out by the same integral ideal. -/
abbrev integralProductLattice (I : (Ideal (𝓞 K))⁰) : Submodule ℤ W :=
  traceProductIdealLattice K (integralIdealUnit K I) (integralIdealUnit K I)

/-- The two lattice coordinates, without asserting that the ambient
sup-norm product and the Hilbert product are isometric. -/
def traceProductCoordinatesEquiv (I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    traceProductIdealLattice K I J ≃+
      (traceIdealLattice K I × traceIdealLattice K J) where
  toFun l := (⟨(WithLp.ofLp (l : W)).1, l.property.1⟩,
    ⟨(WithLp.ofLp (l : W)).2, l.property.2⟩)
  invFun l := ⟨WithLp.toLp 2 ((l.1 : V), (l.2 : V)), ⟨l.1.property, l.2.property⟩⟩
  left_inv l := by apply Subtype.ext; rfl
  right_inv l := by apply Prod.ext <;> apply Subtype.ext <;> rfl
  map_add' l m := by apply Prod.ext <;> apply Subtype.ext <;> rfl

/-- Every ordinary product-lattice point has an actual pair of integer
representatives. -/
def traceProductIntegerEquiv : (𝓞 K × 𝓞 K) ≃+ ordinaryProductLattice K :=
  ((traceIntegerLatticeEquiv K).prodCongr (traceIntegerLatticeEquiv K)).trans
    (traceProductCoordinatesEquiv K 1 1).symm

@[simp] theorem traceProductIntegerEquiv_coe (a b : 𝓞 K) :
    (traceProductIntegerEquiv K (a, b) : W) =
      WithLp.toLp 2 (traceEmbedding K (a : K), traceEmbedding K (b : K)) := rfl

theorem integralProductLattice_le (I : (Ideal (𝓞 K))⁰) :
    integralProductLattice K I ≤ ordinaryProductLattice K := by
  intro l hl
  exact ⟨trace_integralIdealLattice_le K I hl.1,
    trace_integralIdealLattice_le K I hl.2⟩

abbrev singleIdealSubgroup (I : (Ideal (𝓞 K))⁰) : AddSubgroup (traceIdealLattice K 1) :=
  latticeSubgroup (traceIdealLattice K 1) (traceIdealLattice K (integralIdealUnit K I))

/-- The actual coordinate map into the product-subgroup quotient. -/
def productCoordinateQuotientMap (I : (Ideal (𝓞 K))⁰) :
    ordinaryProductLattice K →+
      ((traceIdealLattice K 1 × traceIdealLattice K 1) ⧸
        (singleIdealSubgroup K I).prod (singleIdealSubgroup K I)) :=
  (QuotientAddGroup.mk' ((singleIdealSubgroup K I).prod (singleIdealSubgroup K I))).comp
    (traceProductCoordinatesEquiv K 1 1).toAddMonoidHom

theorem productCoordinateQuotientMap_surjective (I : (Ideal (𝓞 K))⁰) :
    Function.Surjective (productCoordinateQuotientMap K I) :=
  (QuotientAddGroup.mk'_surjective _).comp (traceProductCoordinatesEquiv K 1 1).surjective

theorem productCoordinateQuotientMap_ker (I : (Ideal (𝓞 K))⁰) :
    (productCoordinateQuotientMap K I).ker =
      latticeSubgroup (ordinaryProductLattice K) (integralProductLattice K I) := by
  ext l
  change (QuotientAddGroup.mk (traceProductCoordinatesEquiv K 1 1 l) :
    (traceIdealLattice K 1 × traceIdealLattice K 1) ⧸
      (singleIdealSubgroup K I).prod (singleIdealSubgroup K I)) = 0 ↔
        (l : W) ∈ integralProductLattice K I
  rw [QuotientAddGroup.eq_zero_iff]
  rfl

/-- The actual lattice quotient is the product of the actual residue rings.
The middle equivalence is Mathlib's quotient-of-product equivalence. -/
def traceProductResidueEquiv (I : (Ideal (𝓞 K))⁰) :
    LatticeQuotient (ordinaryProductLattice K) (integralProductLattice K I) ≃+
      ((𝓞 K ⧸ I.val) × (𝓞 K ⧸ I.val)) :=
  ((QuotientAddGroup.quotientAddEquivOfEq
      (productCoordinateQuotientMap_ker K I).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective
      (productCoordinateQuotientMap K I) (productCoordinateQuotientMap_surjective K I))).trans
    ((QuotientAddGroup.prodAddEquiv (singleIdealSubgroup K I) (singleIdealSubgroup K I)).trans
      ((traceLatticeResidueEquiv K I).prodCongr (traceLatticeResidueEquiv K I)))

@[simp] theorem traceProductResidueEquiv_mk (I : (Ideal (𝓞 K))⁰)
    (l : ordinaryProductLattice K) :
    traceProductResidueEquiv K I
      (latticeQuotientMap (ordinaryProductLattice K) (integralProductLattice K I) l) =
    (traceLatticeResidueMap K I (traceProductCoordinatesEquiv K 1 1 l).1,
      traceLatticeResidueMap K I (traceProductCoordinatesEquiv K 1 1 l).2) := rfl

@[simp] theorem traceProductResidueEquiv_mk_integer (I : (Ideal (𝓞 K))⁰) (a b : 𝓞 K) :
    traceProductResidueEquiv K I
      (latticeQuotientMap (ordinaryProductLattice K) (integralProductLattice K I)
        (traceProductIntegerEquiv K (a, b))) =
      (Ideal.Quotient.mk I.val a, Ideal.Quotient.mk I.val b) := by
  rw [traceProductResidueEquiv_mk]
  change (traceLatticeResidueMap K I (traceIntegerLatticeEquiv K a),
    traceLatticeResidueMap K I (traceIntegerLatticeEquiv K b)) = _
  exact Prod.ext (traceLatticeResidueEquiv_mk_integer K I a)
    (traceLatticeResidueEquiv_mk_integer K I b)

@[simp] theorem traceProductResidueEquiv_symm_mk_integer (I : (Ideal (𝓞 K))⁰)
    (a b : 𝓞 K) :
    (traceProductResidueEquiv K I).symm
      (Ideal.Quotient.mk I.val a, Ideal.Quotient.mk I.val b) =
      latticeQuotientMap (ordinaryProductLattice K) (integralProductLattice K I)
        (traceProductIntegerEquiv K (a, b)) := by
  apply (traceProductResidueEquiv K I).injective
  rw [AddEquiv.apply_symm_apply, traceProductResidueEquiv_mk_integer]

instance finite_traceProductResidueQuotient (I : (Ideal (𝓞 K))⁰) :
    Finite (LatticeQuotient (ordinaryProductLattice K) (integralProductLattice K I)) :=
  Finite.of_equiv ((𝓞 K ⧸ I.val) × (𝓞 K ⧸ I.val)) (traceProductResidueEquiv K I).symm.toEquiv

noncomputable instance fintype_traceProductResidueQuotient (I : (Ideal (𝓞 K))⁰) :
    Fintype (LatticeQuotient (ordinaryProductLattice K) (integralProductLattice K I)) :=
  Fintype.ofFinite _

theorem natCard_traceProductResidueQuotient (I : (Ideal (𝓞 K))⁰) :
    Nat.card (LatticeQuotient (ordinaryProductLattice K) (integralProductLattice K I)) =
      Ideal.absNorm I.val ^ 2 := by
  rw [Nat.card_congr (traceProductResidueEquiv K I).toEquiv, Nat.card_prod]
  have h : Nat.card (𝓞 K ⧸ I.val) = Ideal.absNorm I.val := rfl
  rw [h, pow_two]

theorem card_traceProductResidueQuotient (I : (Ideal (𝓞 K))⁰) :
    Fintype.card (LatticeQuotient (ordinaryProductLattice K) (integralProductLattice K I)) =
      Ideal.absNorm I.val ^ 2 := by
  simpa only [Nat.card_eq_fintype_card] using natCard_traceProductResidueQuotient K I

/-- Arithmetic covolume: the norm factor is the same norm square as in the
actual residue quotient cardinal. -/
theorem covolume_integralProductLattice (I : (Ideal (𝓞 K))⁰) :
    ZLattice.covolume (integralProductLattice K I) (volume (α := W)) =
      (Ideal.absNorm I.val : ℝ) ^ 2 * |(discr K : ℝ)| := by
  rw [integralProductLattice, covolume_traceProductIdealLattice_mul]
  simp only [covolume_trace_integralIdealLattice]
  calc
    _ = (Ideal.absNorm I.val : ℝ) ^ 2 * (Real.sqrt |(discr K : ℝ)|) ^ 2 := by ring
    _ = _ := by rw [Real.sq_sqrt (abs_nonneg _)]

theorem covolume_eq_card_mul_absDiscr (I : (Ideal (𝓞 K))⁰) :
    ZLattice.covolume (integralProductLattice K I) (volume (α := W)) =
      (Fintype.card (LatticeQuotient (ordinaryProductLattice K)
        (integralProductLattice K I)) : ℝ) * |(discr K : ℝ)| := by
  rw [covolume_integralProductLattice, card_traceProductResidueQuotient, Nat.cast_pow]

/-- The exact quotient-cardinal/covolume cancellation, with all nonvanishing
facts proved from the nonzero ideal and the number-field discriminant. -/
theorem card_div_covolume_traceProductResidueQuotient (I : (Ideal (𝓞 K))⁰) :
    (Fintype.card (LatticeQuotient (ordinaryProductLattice K)
      (integralProductLattice K I)) : ℝ) /
        ZLattice.covolume (integralProductLattice K I) (volume (α := W)) =
      1 / |(discr K : ℝ)| := by
  have hnorm : (Ideal.absNorm I.val : ℝ) ≠ 0 := by
    exact_mod_cast Ideal.absNorm_ne_zero_of_nonZeroDivisors I
  have hdiscr : |(discr K : ℝ)| ≠ 0 := abs_ne_zero.mpr (by
    exact_mod_cast NumberField.discr_ne_zero K)
  rw [card_traceProductResidueQuotient, covolume_integralProductLattice, Nat.cast_pow]
  field_simp [hnorm, hdiscr]

end HeckeGeneral.Analysis.ActualTraceProductResidueQuotientDraft
