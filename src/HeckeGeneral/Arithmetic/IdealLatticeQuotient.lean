import HeckeGeneral.Arithmetic.TraceLatticeCovolume
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.NumberTheory.NumberField.Ideal.Basic

/-!
The finite residue ring and the quotient of the actual trace ideal lattices
are identified by the embedding of integers. No arbitrary identification
of a finite parameter set with a lattice quotient is used.
-/

noncomputable section

open Classical NumberField
open scoped nonZeroDivisors

namespace HeckeGeneral.Arithmetic

variable (K : Type*) [Field K] [NumberField K]

/-- A nonzero integral ideal, as the genuine invertible fractional ideal. -/
def integralIdealUnit (c : (Ideal (𝓞 K))⁰) : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  Units.mk0 (c.val : FractionalIdeal (𝓞 K)⁰ K) (by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]
    exact nonZeroDivisors.coe_ne_zero c)

@[simp] theorem coe_integralIdealUnit (c : (Ideal (𝓞 K))⁰) :
    (integralIdealUnit K c : FractionalIdeal (𝓞 K)⁰ K) = c.val := rfl

theorem traceEmbedding_integral_mem (c : (Ideal (𝓞 K))⁰) (a : 𝓞 K) :
    traceEmbedding K (a : K) ∈ traceIdealLattice K (integralIdealUnit K c) ↔ a ∈ c.val := by
  rw [traceEmbedding_mem_traceIdealLattice]
  change (a : K) ∈ (c.val : FractionalIdeal (𝓞 K)⁰ K) ↔ a ∈ c.val
  rw [FractionalIdeal.mem_coeIdeal]
  constructor
  · rintro ⟨b, hb, hba⟩
    have h : b = a := RingOfIntegers.coe_injective hba
    exact h ▸ hb
  · intro ha
    exact ⟨a, ha, rfl⟩

/-- Integers map onto, rather than merely into, their actual trace lattice. -/
def traceIntegerLatticeHom : 𝓞 K →+ traceIdealLattice K 1 where
  toFun a := ⟨traceEmbedding K (a : K),
    (traceEmbedding_mem_traceIdealLattice K 1).mpr
      (FractionalIdeal.coe_mem_one (𝓞 K)⁰ a)⟩
  map_zero' := by apply Subtype.ext; simp [traceEmbedding]
  map_add' a b := by
    apply Subtype.ext
    exact (traceEmbeddingIntLinearMap K).map_add (a : K) (b : K)

@[simp] theorem traceIntegerLatticeHom_coe (a : 𝓞 K) :
    (traceIntegerLatticeHom K a : mixedEmbedding.euclidean.mixedSpace K) =
      traceEmbedding K (a : K) := rfl

theorem traceIntegerLatticeHom_bijective : Function.Bijective (traceIntegerLatticeHom K) := by
  constructor
  · intro a b hab
    apply RingOfIntegers.coe_injective
    apply mixedEmbedding_injective K
    have h := congrArg (fun l : traceIdealLattice K 1 => traceToMixed K (l :
      mixedEmbedding.euclidean.mixedSpace K)) hab
    simpa [traceIntegerLatticeHom, traceEmbedding] using h
  · intro l
    obtain ⟨x, hx, hxl⟩ := exists_traceEmbedding_eq_of_mem_traceIdealLattice K 1 l.property
    obtain ⟨a, ha⟩ := (FractionalIdeal.mem_one_iff (𝓞 K)⁰).mp hx
    refine ⟨a, Subtype.ext ?_⟩
    simpa only [traceIntegerLatticeHom_coe, ha] using hxl

def traceIntegerLatticeEquiv : 𝓞 K ≃+ traceIdealLattice K 1 :=
  AddEquiv.ofBijective (traceIntegerLatticeHom K) (traceIntegerLatticeHom_bijective K)

@[simp] theorem traceIntegerLatticeEquiv_apply (a : 𝓞 K) :
    (traceIntegerLatticeEquiv K a : mixedEmbedding.euclidean.mixedSpace K) =
      traceEmbedding K (a : K) := rfl

theorem trace_integralIdealLattice_le (c : (Ideal (𝓞 K))⁰) :
    traceIdealLattice K (integralIdealUnit K c) ≤ traceIdealLattice K 1 := by
  intro l hl
  obtain ⟨x, hx, rfl⟩ := exists_traceEmbedding_eq_of_mem_traceIdealLattice
    K (integralIdealUnit K c) hl
  apply (traceEmbedding_mem_traceIdealLattice K 1).mpr
  exact FractionalIdeal.coeIdeal_le_one hx

/-- The actual residue map on the integer lattice. -/
def traceLatticeResidueMap (c : (Ideal (𝓞 K))⁰) : traceIdealLattice K 1 →+ (𝓞 K ⧸ c.val) :=
  (Ideal.Quotient.mk c.val).toAddMonoidHom.comp (traceIntegerLatticeEquiv K).symm.toAddMonoidHom

theorem traceLatticeResidueMap_surjective (c : (Ideal (𝓞 K))⁰) :
    Function.Surjective (traceLatticeResidueMap K c) :=
  (Ideal.Quotient.mk_surjective).comp (traceIntegerLatticeEquiv K).symm.surjective

theorem traceLatticeResidueMap_ker (c : (Ideal (𝓞 K))⁰) :
    (traceLatticeResidueMap K c).ker =
      (traceIdealLattice K (integralIdealUnit K c)).toAddSubgroup.addSubgroupOf
        (traceIdealLattice K 1).toAddSubgroup := by
  ext l
  obtain ⟨a, rfl⟩ := (traceIntegerLatticeEquiv K).surjective l
  change Ideal.Quotient.mk c.val ((traceIntegerLatticeEquiv K).symm
    (traceIntegerLatticeEquiv K a)) = 0 ↔
      (traceIntegerLatticeEquiv K a : mixedEmbedding.euclidean.mixedSpace K) ∈
        traceIdealLattice K (integralIdealUnit K c)
  rw [AddEquiv.symm_apply_apply, Ideal.Quotient.eq_zero_iff_mem,
    traceIntegerLatticeEquiv_apply, traceEmbedding_integral_mem]

/-- The lattice quotient is the actual integral residue ring additively. -/
def traceLatticeResidueEquiv (c : (Ideal (𝓞 K))⁰) :
    (traceIdealLattice K 1 ⧸
      (traceIdealLattice K (integralIdealUnit K c)).toAddSubgroup.addSubgroupOf
        (traceIdealLattice K 1).toAddSubgroup) ≃+ (𝓞 K ⧸ c.val) :=
  (QuotientAddGroup.quotientAddEquivOfEq (traceLatticeResidueMap_ker K c).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective (traceLatticeResidueMap K c)
      (traceLatticeResidueMap_surjective K c))

@[simp] theorem traceLatticeResidueEquiv_mk (c : (Ideal (𝓞 K))⁰)
    (l : traceIdealLattice K 1) :
    traceLatticeResidueEquiv K c (QuotientAddGroup.mk l) = traceLatticeResidueMap K c l := rfl

@[simp] theorem traceLatticeResidueEquiv_mk_integer (c : (Ideal (𝓞 K))⁰) (a : 𝓞 K) :
    traceLatticeResidueEquiv K c (QuotientAddGroup.mk (traceIntegerLatticeEquiv K a)) =
      Ideal.Quotient.mk c.val a := by
  rw [traceLatticeResidueEquiv_mk]
  change Ideal.Quotient.mk c.val ((traceIntegerLatticeEquiv K).symm
    (traceIntegerLatticeEquiv K a)) = _
  rw [AddEquiv.symm_apply_apply]

instance finite_integralResidue (c : (Ideal (𝓞 K))⁰) : Finite (𝓞 K ⧸ c.val) :=
  c.val.finiteQuotientOfFreeOfNeBot (nonZeroDivisors.coe_ne_zero c)

instance finite_traceLatticeQuotient (c : (Ideal (𝓞 K))⁰) :
    Finite (traceIdealLattice K 1 ⧸
      (traceIdealLattice K (integralIdealUnit K c)).toAddSubgroup.addSubgroupOf
        (traceIdealLattice K 1).toAddSubgroup) :=
  Finite.of_equiv _ (traceLatticeResidueEquiv K c).symm.toEquiv

/-- The norm/discriminant covolume in integral-ideal form. -/
theorem covolume_trace_integralIdealLattice (c : (Ideal (𝓞 K))⁰) :
    ZLattice.covolume (traceIdealLattice K (integralIdealUnit K c)) =
      (Ideal.absNorm c.val : ℝ) * Real.sqrt |discr K| := by
  rw [covolume_traceIdealLattice, coe_integralIdealUnit, FractionalIdeal.coeIdeal_absNorm]
  norm_cast

end HeckeGeneral.Arithmetic
