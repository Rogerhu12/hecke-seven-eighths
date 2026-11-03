import HeckeGeneral.Arithmetic.SUnitNormOneTopology
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.LocallyFinite

/-! Finite overlap for the actual original S-unit subgroup. These lemmas
are the support input for periodizing a compact cutoff; no partition of
unity or torsion-free subgroup is assumed or substituted. -/

noncomputable section

namespace HeckeGeneral.Analysis

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic Set Filter Topology
open scoped Classical

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (Γ : Subgroup (S.unit K))
local notation "T" => sLocalNormOneGroup K S
local notation "H" => sLocalNormOneGamma K S Γ

/-- The original subgroup, including all its torsion, acts by the actual
diagonal. -/
def sUnitPartitionDiagonal : Γ →* T :=
  (sLocalNormOneDiagonal K S).comp Γ.subtype

theorem sUnitPartitionDiagonal_injective :
    Function.Injective (sUnitPartitionDiagonal K S Γ) :=
  (sLocalNormOneDiagonal_injective K S).comp Subtype.val_injective

theorem finite_sUnitPartitionDiagonal_preimage
    (C : Set T) (hC : IsCompact C) :
    Set.Finite ((sUnitPartitionDiagonal K S Γ) ⁻¹' C) := by
  have hmem (u : Γ) : sUnitPartitionDiagonal K S Γ u ∈ H :=
    Subgroup.mem_map.mpr ⟨u.val, u.property, rfl⟩
  have hfinite : Set.Finite ((H : Set T) ∩ C) :=
    (hC.inter_left (isClosed_sLocalNormOneGamma K S Γ)).finite
      ((isDiscrete_sLocalNormOneGamma K S Γ).mono inter_subset_left)
  have hpre : (sUnitPartitionDiagonal K S Γ) ⁻¹' C =
      (sUnitPartitionDiagonal K S Γ) ⁻¹' ((H : Set T) ∩ C) := by
    ext u
    exact ⟨fun hu => ⟨hmem u, hu⟩, fun hu => hu.2⟩
  rw [hpre]
  exact hfinite.preimage (sUnitPartitionDiagonal_injective K S Γ).injOn

/-- Two compact subsets meet under only finitely many translates of the
literal original Γ. This requires no finite-index or torsion hypothesis. -/
theorem finite_sUnitPartition_compact_overlap
    (C D : Set T) (hC : IsCompact C) (hD : IsCompact D) :
    Set.Finite {u : Γ | ∃ x ∈ C, sUnitPartitionDiagonal K S Γ u * x ∈ D} := by
  have hfinite := finite_sUnitPartitionDiagonal_preimage K S Γ
    ((fun p : T × T => p.1 / p.2) '' (D ×ˢ C))
    ((hD.prod hC).image continuous_div')
  apply hfinite.subset
  rintro u ⟨x, hx, hy⟩
  exact ⟨(sUnitPartitionDiagonal K S Γ u * x, x), ⟨hy, hx⟩, by simp⟩

/-- Compact-cutoff translates are locally finite in the actual norm-one
group. In particular their periodization is locally a finite sum. -/
theorem locallyFinite_sUnitPartition_tsupport
    (f : T → ℝ) (hf : HasCompactSupport f) :
    LocallyFinite (fun u : Γ =>
      (fun x : T => sUnitPartitionDiagonal K S Γ u * x) ⁻¹' tsupport f) := by
  intro x
  obtain ⟨C, hC, hxC⟩ := exists_compact_mem_nhds x
  refine ⟨C, hxC, ?_⟩
  apply (finite_sUnitPartition_compact_overlap K S Γ C (tsupport f) hC hf).subset
  rintro u ⟨y, hy, hyC⟩
  exact ⟨y, hyC, hy⟩

theorem finite_sUnitPartition_nonzero_terms
    (f : T → ℝ) (hf : HasCompactSupport f) (x : T) :
    Set.Finite {u : Γ | f (sUnitPartitionDiagonal K S Γ u * x) ≠ 0} := by
  apply ((locallyFinite_sUnitPartition_tsupport K S Γ f hf).point_finite x).subset
  intro u hu
  exact subset_closure hu

end HeckeGeneral.Analysis
