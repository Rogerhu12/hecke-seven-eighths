import ActualExteriorIdealGcdEquiv
import ActualExteriorPairDivisorReindex

/-!
The actual finite ideal-pair sum is partitioned by its common ideal.
For each common ideal the residual family is the FULL finite dilation
preimage of the original support; coprimality is an indicator on this
family, not a restriction built into the family before Mobius insertion.
UNCOMPILED SOURCE CANDIDATE / native 0.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeGeneral.ThetaSkeleton.Global.ActualGcdMobiusDraft

open NumberField IsDedekindDomain
open ActualIdealGcdDraft ActualPairDivisorDraft
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

local notation "E" => ExteriorIdeal K S

/-- Only actual gcd values of pairs in the original finite support. -/
def finiteCommonParts (A B : Finset E) : Finset E :=
  (finiteGcdTriples K S A B).image (fun t => t.val.1)

theorem finiteCommonParts_eq_image (A B : Finset E) :
    finiteCommonParts K S A B =
      (A.product B).image (fun ij => commonPart K S ij.1 ij.2) := by
  unfold finiteCommonParts finiteGcdTriples
  exact Finset.image_image

theorem mem_finiteCommonParts (A B : Finset E) (C : E) :
    C ∈ finiteCommonParts K S A B ↔
      ∃ I ∈ A, ∃ J ∈ B, commonPart K S I J = C := by
  rw [finiteCommonParts_eq_image]
  constructor
  · intro h
    obtain ⟨ij, hij, hC⟩ := Finset.mem_image.mp h
    exact ⟨ij.1, (Finset.mem_product.mp hij).1,
      ij.2, (Finset.mem_product.mp hij).2, hC⟩
  · rintro ⟨I, hI, J, hJ, hC⟩
    exact Finset.mem_image.mpr ⟨(I, J), Finset.mem_product.mpr ⟨hI, hJ⟩, hC⟩

/-- All residual pairs with the original reconstructed cutoffs.
There is deliberately no coprimality filter in this finite family. -/
def fullResidualPairs (C : E) (A B : Finset E) : Finset (E × E) :=
  divisorResidualPairs K S C (A.product B)

@[simp] theorem mem_fullResidualPairs (C : E) (A B : Finset E) (mn : E × E) :
    mn ∈ fullResidualPairs K S C A B ↔
      exteriorMul K S C mn.1 ∈ A ∧ exteriorMul K S C mn.2 ∈ B := by
  change mn ∈ divisorResidualPairs K S C (A.product B) ↔ _
  rw [mem_divisorResidualPairs]
  exact Finset.mem_product

/-- A genuine gcd fiber equals the full residual family weighted by its
ordinary ideal-coprimality indicator. -/
theorem sum_gcdFiber_eq_fullResidual (C : E) (A B : Finset E)
    (F : E → E → ℂ) :
    (∑ t ∈ finiteGcdTriples K S A B with t.val.1 = C,
      F (exteriorMul K S t.val.1 t.val.2.1)
        (exteriorMul K S t.val.1 t.val.2.2)) =
      ∑ mn ∈ fullResidualPairs K S C A B,
        F (exteriorMul K S C mn.1) (exteriorMul K S C mn.2) *
          (if IsCoprime mn.1.val.val mn.2.val.val then 1 else 0) := by
  calc
    _ = ∑ mn ∈ fullResidualPairs K S C A B with
        IsCoprime mn.1.val.val mn.2.val.val,
        F (exteriorMul K S C mn.1) (exteriorMul K S C mn.2) := by
      refine Finset.sum_bij (fun t _ => t.val.2) ?_ ?_ ?_ ?_
      · intro t ht
        obtain ⟨htT, htC⟩ := Finset.mem_filter.mp ht
        have htAB := (mem_finiteGcdTriples K S A B t).mp htT
        refine Finset.mem_filter.mpr ⟨?_, t.property⟩
        apply (mem_fullResidualPairs K S C A B t.val.2).mpr
        simpa only [htC] using htAB
      · intro t ht u hu heq
        have htC := (Finset.mem_filter.mp ht).2
        have huC := (Finset.mem_filter.mp hu).2
        apply Subtype.ext
        exact Prod.ext (htC.trans huC.symm) heq
      · intro mn hmn
        obtain ⟨hmnR, hmnC⟩ := Finset.mem_filter.mp hmn
        let t : CoprimeTriple K S := ⟨(C, mn), hmnC⟩
        have htT : t ∈ finiteGcdTriples K S A B :=
          (mem_finiteGcdTriples K S A B t).mpr
            ((mem_fullResidualPairs K S C A B mn).mp hmnR)
        exact ⟨t, Finset.mem_filter.mpr ⟨htT, rfl⟩, rfl⟩
      · intro t ht
        rw [(Finset.mem_filter.mp ht).2]
    _ = _ := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro mn _
      by_cases h : IsCoprime mn.1.val.val mn.2.val.val <;> simp only [h, ite_true,
        ite_false, mul_one, mul_zero]

/-- The complete original finite double sum, before any Mobius insertion. -/
theorem sum_pair_eq_commonParts_fullResidual (A B : Finset E)
    (F : E → E → ℂ) :
    (∑ I ∈ A, ∑ J ∈ B, F I J) =
      ∑ C ∈ finiteCommonParts K S A B,
        ∑ mn ∈ fullResidualPairs K S C A B,
          F (exteriorMul K S C mn.1) (exteriorMul K S C mn.2) *
            (if IsCoprime mn.1.val.val mn.2.val.val then 1 else 0) := by
  calc
    _ = ∑ t ∈ finiteGcdTriples K S A B,
        F (exteriorMul K S t.val.1 t.val.2.1)
          (exteriorMul K S t.val.1 t.val.2.2) :=
      sum_pair_eq_sum_gcdTriples K S A B F
    _ = ∑ C ∈ finiteCommonParts K S A B,
        ∑ t ∈ finiteGcdTriples K S A B with t.val.1 = C,
          F (exteriorMul K S t.val.1 t.val.2.1)
            (exteriorMul K S t.val.1 t.val.2.2) := by
      symm
      apply Finset.sum_fiberwise_of_maps_to (g := fun t : CoprimeTriple K S => t.val.1)
      intro t ht
      exact Finset.mem_image.mpr ⟨t, ht, rfl⟩
    _ = _ := by
      apply Finset.sum_congr rfl
      intro C _
      exact sum_gcdFiber_eq_fullResidual K S C A B F

end HeckeGeneral.ThetaSkeleton.Global.ActualGcdMobiusDraft
