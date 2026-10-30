import HeckeGeneral.Analysis.SUnitArchPartitionCutoff
import HeckeGeneral.Analysis.SUnitPartitionSupport
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-! A continuous compact normalized partition for the literal original Γ.
Only continuity on the norm-one group is asserted here. Archimedean fibre
smoothness requires a separate argument. -/

noncomputable section

namespace HeckeGeneral.Analysis

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic Set
open scoped Classical Topology BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]
local notation "G" => sLocalMultiplicativeGroup K S
local notation "T" => sLocalNormOneGroup K S

def sUnitPartitionBase (x : T) : ℝ := sUnitPartitionNumerator K S Γ (x : G)

theorem continuous_sUnitPartitionBase : Continuous (sUnitPartitionBase K S Γ) :=
  (continuous_sUnitPartitionNumerator K S Γ).comp continuous_subtype_val

/-- Restriction retains compact support because T is a closed subgroup. -/
theorem hasCompactSupport_sUnitPartitionBase :
    HasCompactSupport (sUnitPartitionBase K S Γ) := by
  have hclosed := isClosed_sLocalNormOneGroup K S
  have hc := hclosed.isClosedEmbedding_subtypeVal.isCompact_preimage
    (hasCompactSupport_sUnitPartitionNumerator K S Γ)
  apply hc.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _
    ((isClosed_tsupport (sUnitPartitionNumerator K S Γ)).preimage continuous_subtype_val)
  intro x hx
  exact subset_closure hx

theorem sUnitPartitionBase_mem_Icc (x : T) :
    sUnitPartitionBase K S Γ x ∈ Icc (0 : ℝ) 1 :=
  sUnitPartitionNumerator_mem_Icc K S Γ (x : G)

def sUnitPartitionPeriod (x : T) : ℝ :=
  ∑' u : Γ, sUnitPartitionBase K S Γ (sUnitPartitionDiagonal K S Γ u * x)

theorem summable_sUnitPartitionBase_translates (x : T) :
    Summable (fun u : Γ =>
      sUnitPartitionBase K S Γ (sUnitPartitionDiagonal K S Γ u * x)) :=
  summable_of_hasFiniteSupport (finite_sUnitPartition_nonzero_terms K S Γ
    (sUnitPartitionBase K S Γ) (hasCompactSupport_sUnitPartitionBase K S Γ) x)

theorem continuous_sUnitPartitionPeriod : Continuous (sUnitPartitionPeriod K S Γ) := by
  have hlf := locallyFinite_sUnitPartition_tsupport K S Γ
    (sUnitPartitionBase K S Γ) (hasCompactSupport_sUnitPartitionBase K S Γ)
  have hsupport : LocallyFinite (fun u : Γ => Function.support (fun x : T =>
      sUnitPartitionBase K S Γ (sUnitPartitionDiagonal K S Γ u * x))) := by
    apply hlf.subset
    intro u x hx
    exact subset_closure hx
  have hcont := continuous_finsum (fun u : Γ =>
    (continuous_sUnitPartitionBase K S Γ).comp (continuous_const.mul continuous_id)) hsupport
  have heq : sUnitPartitionPeriod K S Γ = (fun x : T => ∑ᶠ u : Γ,
      sUnitPartitionBase K S Γ (sUnitPartitionDiagonal K S Γ u * x)) := by
    funext x
    exact tsum_eq_finsum (finite_sUnitPartition_nonzero_terms K S Γ
      (sUnitPartitionBase K S Γ) (hasCompactSupport_sUnitPartitionBase K S Γ) x)
  rwa [heq]

theorem sUnitPartitionPeriod_nonneg (x : T) : 0 ≤ sUnitPartitionPeriod K S Γ x :=
  tsum_nonneg (fun u => (sUnitPartitionBase_mem_Icc K S Γ _).1)

theorem sUnitPartitionPeriod_invariant (u : Γ) (x : T) :
    sUnitPartitionPeriod K S Γ (sUnitPartitionDiagonal K S Γ u * x) =
      sUnitPartitionPeriod K S Γ x := by
  unfold sUnitPartitionPeriod
  simpa only [Equiv.coe_mulRight, map_mul, mul_assoc] using
    (Equiv.mulRight u).tsum_eq (fun v : Γ =>
      sUnitPartitionBase K S Γ (sUnitPartitionDiagonal K S Γ v * x))

theorem sUnitPartitionPeriod_pos (x : T) : 0 < sUnitPartitionPeriod K S Γ x := by
  obtain ⟨u, hu⟩ := exists_subgroup_mem_sUnitCompactRepresentativeSet K S Γ (x : G)
    ((mem_sLocalNormOneGroup K S _).mp x.property)
  have hone : sUnitPartitionBase K S Γ (sUnitPartitionDiagonal K S Γ u * x) = 1 :=
    sUnitPartitionNumerator_eq_one_on_representatives K S Γ _ hu
  exact (summable_sUnitPartitionBase_translates K S Γ x).tsum_pos
    (fun v => (sUnitPartitionBase_mem_Icc K S Γ _).1) u (by rw [hone]; norm_num)

theorem sUnitPartitionBase_le_period (x : T) :
    sUnitPartitionBase K S Γ x ≤ sUnitPartitionPeriod K S Γ x := by
  simpa only [sUnitPartitionPeriod, map_one, one_mul] using
    (summable_sUnitPartitionBase_translates K S Γ x).le_tsum (1 : Γ)
      (fun u _ => (sUnitPartitionBase_mem_Icc K S Γ _).1)

def sUnitNormalizedPartition (x : T) : ℝ :=
  sUnitPartitionBase K S Γ x / sUnitPartitionPeriod K S Γ x

theorem continuous_sUnitNormalizedPartition : Continuous (sUnitNormalizedPartition K S Γ) :=
  (continuous_sUnitPartitionBase K S Γ).div (continuous_sUnitPartitionPeriod K S Γ)
    (fun x => (sUnitPartitionPeriod_pos K S Γ x).ne')

theorem hasCompactSupport_sUnitNormalizedPartition :
    HasCompactSupport (sUnitNormalizedPartition K S Γ) := by
  have heq : sUnitNormalizedPartition K S Γ =
      sUnitPartitionBase K S Γ * (fun x => (sUnitPartitionPeriod K S Γ x)⁻¹) := by
    funext x
    exact div_eq_mul_inv _ _
  rw [heq]
  exact (hasCompactSupport_sUnitPartitionBase K S Γ).mul_right
    (f' := fun x => (sUnitPartitionPeriod K S Γ x)⁻¹)

theorem sUnitNormalizedPartition_mem_Icc (x : T) :
    sUnitNormalizedPartition K S Γ x ∈ Icc (0 : ℝ) 1 :=
  ⟨div_nonneg (sUnitPartitionBase_mem_Icc K S Γ x).1
      (sUnitPartitionPeriod_pos K S Γ x).le,
    div_le_one_of_le₀ (sUnitPartitionBase_le_period K S Γ x)
      (sUnitPartitionPeriod_pos K S Γ x).le⟩

/-- The sum runs over all of the original subgroup, including torsion. -/
theorem sUnitNormalizedPartition_partition (x : T) :
    (∑' u : Γ, sUnitNormalizedPartition K S Γ
      (sUnitPartitionDiagonal K S Γ u * x)) = 1 := by
  simp_rw [sUnitNormalizedPartition, sUnitPartitionPeriod_invariant]
  rw [tsum_div_const]
  exact div_self (sUnitPartitionPeriod_pos K S Γ x).ne'

/-- Two independent original subgroup sums use the same actual partition.
This is not a claim about a single simultaneous diagonal subgroup sum. -/
theorem sUnitNormalizedPartition_two_column (x y : T) :
    (∑' u : Γ, ∑' v : Γ,
      sUnitNormalizedPartition K S Γ (sUnitPartitionDiagonal K S Γ u * x) *
      sUnitNormalizedPartition K S Γ (sUnitPartitionDiagonal K S Γ v * y)) = 1 := by
  simp only [tsum_mul_left, sUnitNormalizedPartition_partition, mul_one]

end HeckeGeneral.Analysis
