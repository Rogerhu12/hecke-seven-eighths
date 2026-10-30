import HeckeGeneral.Analysis.SUnitAnnularPartitionCutoff

/-! Covariance of the actual unit partition under the original S-unit
subgroup. Both the archimedean point and the finite unit coordinate move.
The resulting partition identities retain every subgroup element, including
torsion, and use two independent subgroup sums for two columns. -/

noncomputable section

namespace HeckeGeneral.Analysis

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]

local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "W" => mixedEmbedding.mixedSpace K
local notation "G" => sLocalMultiplicativeGroup K S
local notation "T" => sLocalNormOneGroup K S
local notation "R" => traceArchRegular K
local notation "Z" => SFiniteLocalGroup K S

/-- Literal archimedean multiplication by an element of the original Γ. -/
def sUnitPartitionArchTranslate (u : Γ) (z : R) : R :=
  ⟨traceUnitMulEquiv K (sLocalDiagonal K S u.val).1 z.val, by
    rw [traceArchRegular_iff_isUnit, traceToMixed_traceUnitMulEquiv]
    exact (sLocalDiagonal K S u.val).1.isUnit.mul
      ((traceArchRegular_iff_isUnit K z.val).mp z.property)⟩

@[simp] theorem sUnitPartitionArchTranslate_val (u : Γ) (z : R) :
    (sUnitPartitionArchTranslate K S Γ u z).val =
      traceUnitMulEquiv K (sLocalDiagonal K S u.val).1 z.val := rfl

@[simp] theorem sUnitPartitionArchTranslate_one (z : R) :
    sUnitPartitionArchTranslate K S Γ 1 z = z := by
  apply Subtype.ext
  apply (traceToMixed K).injective
  rw [sUnitPartitionArchTranslate_val, traceToMixed_traceUnitMulEquiv]
  simp only [Subgroup.coe_one, map_one, Prod.fst_one, Units.val_one, one_mul]

theorem sUnitPartitionArchTranslate_mul (u v : Γ) (z : R) :
    sUnitPartitionArchTranslate K S Γ (u * v) z =
      sUnitPartitionArchTranslate K S Γ u (sUnitPartitionArchTranslate K S Γ v z) := by
  apply Subtype.ext
  apply (traceToMixed K).injective
  simp only [sUnitPartitionArchTranslate_val, traceToMixed_traceUnitMulEquiv,
    Subgroup.coe_mul, map_mul, Prod.fst_mul, Units.val_mul, mul_assoc]

/-- The finite coordinate changes by the same actual diagonal S-unit. -/
theorem sUnitPartitionFibreInput_translate (u : Γ) (ζ : Z) (z : R) :
    sUnitPartitionFibreInput K S ((sLocalDiagonal K S u.val).2 * ζ)
        (sUnitPartitionArchTranslate K S Γ u z) =
      sLocalDiagonal K S u.val * sUnitPartitionFibreInput K S ζ z := by
  apply Prod.ext
  · apply Units.ext
    change traceToMixed K (traceUnitMulEquiv K (sLocalDiagonal K S u.val).1 z.val) =
      ((sLocalDiagonal K S u.val).1 : W) * traceToMixed K z.val
    exact traceToMixed_traceUnitMulEquiv K _ _
  · rfl

/-- The product of the archimedean and finite norms is Γ-invariant.
Neither factor is separately asserted to be invariant. -/
theorem sUnitPartitionFibre_totalNorm_translate (u : Γ) (ζ : Z) (z : R) :
    traceArchProductNorm K (sUnitPartitionArchTranslate K S Γ u z).val *
        sFiniteProductNorm K S ((sLocalDiagonal K S u.val).2 * ζ) =
      traceArchProductNorm K z.val * sFiniteProductNorm K S ζ := by
  change sLocalProductNorm K S
      (sUnitPartitionFibreInput K S ((sLocalDiagonal K S u.val).2 * ζ)
        (sUnitPartitionArchTranslate K S Γ u z)) =
    sLocalProductNorm K S (sUnitPartitionFibreInput K S ζ z)
  rw [sUnitPartitionFibreInput_translate, sLocalProductNorm_diagonal_mul]

theorem sUnitPartitionFibreRadius_translate (u : Γ) (ζ : Z) (z : R) :
    sUnitPartitionFibreRadius K S ((sLocalDiagonal K S u.val).2 * ζ)
        (sUnitPartitionArchTranslate K S Γ u z) =
      sUnitPartitionFibreRadius K S ζ z := by
  apply Subtype.ext
  change sLocalProductNorm K S
      (sUnitPartitionFibreInput K S ((sLocalDiagonal K S u.val).2 * ζ)
        (sUnitPartitionArchTranslate K S Γ u z)) =
    sLocalProductNorm K S (sUnitPartitionFibreInput K S ζ z)
  rw [sUnitPartitionFibreInput_translate, sLocalProductNorm_diagonal_mul]

/-- Normalization commutes with simultaneous archimedean and finite
multiplication, as an equality in the actual norm-one subgroup. -/
theorem sUnitPartitionFibreNormalize_translate (u : Γ) (ζ : Z) (z : R) :
    sUnitPartitionFibreNormalize K S ((sLocalDiagonal K S u.val).2 * ζ)
        (sUnitPartitionArchTranslate K S Γ u z) =
      sUnitPartitionDiagonal K S Γ u * sUnitPartitionFibreNormalize K S ζ z := by
  apply Subtype.ext
  change (sLocalNormSection K S
        (sUnitPartitionFibreRadius K S ((sLocalDiagonal K S u.val).2 * ζ)
          (sUnitPartitionArchTranslate K S Γ u z)))⁻¹ *
      sUnitPartitionFibreInput K S ((sLocalDiagonal K S u.val).2 * ζ)
        (sUnitPartitionArchTranslate K S Γ u z) =
    sLocalDiagonal K S u.val *
      ((sLocalNormSection K S (sUnitPartitionFibreRadius K S ζ z))⁻¹ *
        sUnitPartitionFibreInput K S ζ z)
  rw [sUnitPartitionFibreRadius_translate, sUnitPartitionFibreInput_translate]
  ac_rfl

theorem sUnitNormalizedPartitionArchPullback_translate (u : Γ) (ζ : Z) (z : R) :
    sUnitNormalizedPartitionArchPullback K S Γ ((sLocalDiagonal K S u.val).2 * ζ)
        (sUnitPartitionArchTranslate K S Γ u z).val =
      sUnitNormalizedPartition K S Γ
        (sUnitPartitionDiagonal K S Γ u * sUnitPartitionFibreNormalize K S ζ z) := by
  rw [sUnitNormalizedPartitionArchPullback,
    dif_pos (sUnitPartitionArchTranslate K S Γ u z).property,
    sUnitPartitionFibreNormalize_translate]

/-- This pullback family is genuinely summable, from compact support and
the discrete actual subgroup; no convergence input is supplied. -/
theorem summable_sUnitNormalizedPartitionArchPullback_translates (ζ : Z) (z : R) :
    Summable (fun u : Γ =>
      sUnitNormalizedPartitionArchPullback K S Γ ((sLocalDiagonal K S u.val).2 * ζ)
        (sUnitPartitionArchTranslate K S Γ u z).val) := by
  simp_rw [sUnitNormalizedPartitionArchPullback_translate]
  exact summable_of_hasFiniteSupport (finite_sUnitPartition_nonzero_terms K S Γ
    (sUnitNormalizedPartition K S Γ) (hasCompactSupport_sUnitNormalizedPartition K S Γ)
    (sUnitPartitionFibreNormalize K S ζ z))

theorem sUnitNormalizedPartitionArchPullback_partition (ζ : Z) (z : R) :
    (∑' u : Γ,
      sUnitNormalizedPartitionArchPullback K S Γ ((sLocalDiagonal K S u.val).2 * ζ)
        (sUnitPartitionArchTranslate K S Γ u z).val) = 1 := by
  simp_rw [sUnitNormalizedPartitionArchPullback_translate]
  exact sUnitNormalizedPartition_partition K S Γ (sUnitPartitionFibreNormalize K S ζ z)

/-- The finite coordinates move separately in the two independent Γ sums. -/
theorem sUnitNormalizedPartitionArchPullback_two_column (ζ ξ : Z) (z w : R) :
    (∑' u : Γ, ∑' v : Γ,
      sUnitNormalizedPartitionArchPullback K S Γ ((sLocalDiagonal K S u.val).2 * ζ)
          (sUnitPartitionArchTranslate K S Γ u z).val *
        sUnitNormalizedPartitionArchPullback K S Γ ((sLocalDiagonal K S v.val).2 * ξ)
          (sUnitPartitionArchTranslate K S Γ v w).val) = 1 := by
  simp_rw [sUnitNormalizedPartitionArchPullback_translate]
  exact sUnitNormalizedPartition_two_column K S Γ
    (sUnitPartitionFibreNormalize K S ζ z) (sUnitPartitionFibreNormalize K S ξ w)

theorem sUnitAnnularPartitionCutoff_translate (a : ℝ → ℝ) (u : Γ) (ζ : Z) (z : R) :
    sUnitAnnularPartitionCutoff K S Γ a ((sLocalDiagonal K S u.val).2 * ζ)
        (sUnitPartitionArchTranslate K S Γ u z).val =
      a (traceArchProductNorm K z.val * sFiniteProductNorm K S ζ) *
        sUnitNormalizedPartition K S Γ
          (sUnitPartitionDiagonal K S Γ u * sUnitPartitionFibreNormalize K S ζ z) := by
  rw [sUnitAnnularPartitionCutoff, sUnitPartitionFibre_totalNorm_translate,
    sUnitNormalizedPartitionArchPullback_translate]

/-- The true annular weight is reconstructed with a moving finite fibre. -/
theorem sUnitAnnularPartitionCutoff_partition (a : ℝ → ℝ) (ζ : Z) (z : R) :
    (∑' u : Γ, sUnitAnnularPartitionCutoff K S Γ a
      ((sLocalDiagonal K S u.val).2 * ζ) (sUnitPartitionArchTranslate K S Γ u z).val) =
      a (traceArchProductNorm K z.val * sFiniteProductNorm K S ζ) := by
  simp_rw [sUnitAnnularPartitionCutoff_translate]
  rw [tsum_mul_left, sUnitNormalizedPartition_partition, mul_one]

/-- The same original partition reconstructs two annular weights using
independent translates, with the corresponding finite fibres retained. -/
theorem sUnitAnnularPartitionCutoff_two_column (a : ℝ → ℝ) (ζ ξ : Z) (z w : R) :
    (∑' u : Γ, ∑' v : Γ,
      sUnitAnnularPartitionCutoff K S Γ a ((sLocalDiagonal K S u.val).2 * ζ)
          (sUnitPartitionArchTranslate K S Γ u z).val *
        sUnitAnnularPartitionCutoff K S Γ a ((sLocalDiagonal K S v.val).2 * ξ)
          (sUnitPartitionArchTranslate K S Γ v w).val) =
      a (traceArchProductNorm K z.val * sFiniteProductNorm K S ζ) *
        a (traceArchProductNorm K w.val * sFiniteProductNorm K S ξ) := by
  simp only [tsum_mul_left, tsum_mul_right, sUnitAnnularPartitionCutoff_partition]

end HeckeGeneral.Analysis
