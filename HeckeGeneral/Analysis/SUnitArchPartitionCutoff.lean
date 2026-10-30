import HeckeGeneral.Analysis.SUnitFinitePartitionBox
import HeckeGeneral.Analysis.TraceLogNormSmooth
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Topology.Separation.Regular

/-! An actual smooth archimedean cutoff and a compact numerator for the
original S-unit representatives. Existence uses smooth Urysohn on the
actual compact archimedean projection, inside its regular open locus. -/

noncomputable section

namespace HeckeGeneral.Analysis

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic Set
open scoped Classical ContDiff

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "W" => mixedEmbedding.mixedSpace K
local notation "G" => sLocalMultiplicativeGroup K S

def sUnitArchRepresentativeSet : Set V :=
  (fun x : G => (traceToMixed K).symm (x.1 : W)) ''
    sUnitCompactRepresentativeSet K S Γ

theorem isCompact_sUnitArchRepresentativeSet :
    IsCompact (sUnitArchRepresentativeSet K S Γ) :=
  (isCompact_sUnitCompactRepresentativeSet K S Γ).image
    ((traceToMixed K).symm.continuous.comp (Units.continuous_val.comp continuous_fst))

theorem sUnitArchRepresentativeSet_subset_regular :
    sUnitArchRepresentativeSet K S Γ ⊆ traceArchRegular K := by
  rintro z ⟨x, _, rfl⟩
  exact traceArchRegular_unit K x.1

/-- A genuine compact smooth Urysohn cutoff, equal to one on all actual
representative archimedean coordinates and supported away from every
individual zero archimedean coordinate. -/
theorem exists_sUnitArchPartitionCutoff :
    ∃ b : V → ℝ, ContDiff ℝ ∞ b ∧ HasCompactSupport b ∧
      tsupport b ⊆ traceArchRegular K ∧
      (∀ z, b z ∈ Icc (0 : ℝ) 1) ∧
      (∀ z ∈ sUnitArchRepresentativeSet K S Γ, b z = 1) := by
  obtain ⟨U, hU, hCU, hUr, hUc⟩ :=
    exists_open_between_and_isCompact_closure
      (isCompact_sUnitArchRepresentativeSet K S Γ)
      (isOpen_traceArchRegular K) (sUnitArchRepresentativeSet_subset_regular K S Γ)
  obtain ⟨b, hb, hbrange, hbsupport, hbone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hU
      (isCompact_sUnitArchRepresentativeSet K S Γ).isClosed hCU
  have hts : tsupport b = closure U := by
    change closure (Function.support b) = closure U
    rw [hbsupport]
  refine ⟨b, hb, ?_, ?_, fun z => hbrange (mem_range_self z), ?_⟩
  · change IsCompact (tsupport b)
    rwa [hts]
  · rwa [hts]
  · intro z hz
    exact (hbone z).mp hz

def sUnitArchPartitionCutoff : V → ℝ :=
  Classical.choose (exists_sUnitArchPartitionCutoff K S Γ)

theorem sUnitArchPartitionCutoff_spec :
    ContDiff ℝ ∞ (sUnitArchPartitionCutoff K S Γ) ∧
      HasCompactSupport (sUnitArchPartitionCutoff K S Γ) ∧
      tsupport (sUnitArchPartitionCutoff K S Γ) ⊆ traceArchRegular K ∧
      (∀ z, sUnitArchPartitionCutoff K S Γ z ∈ Icc (0 : ℝ) 1) ∧
      (∀ z ∈ sUnitArchRepresentativeSet K S Γ,
        sUnitArchPartitionCutoff K S Γ z = 1) :=
  Classical.choose_spec (exists_sUnitArchPartitionCutoff K S Γ)

def sUnitPartitionNumerator (x : G) : ℝ :=
  sUnitArchPartitionCutoff K S Γ ((traceToMixed K).symm (x.1 : W)) *
    sUnitFinitePartitionCutoff K S (finiteIndexSUnitBoxWidth K S Γ) x.2

theorem continuous_sUnitPartitionNumerator :
    Continuous (sUnitPartitionNumerator K S Γ) :=
  ((sUnitArchPartitionCutoff_spec K S Γ).1.continuous.comp
    ((traceToMixed K).symm.continuous.comp (Units.continuous_val.comp continuous_fst))).mul
      ((sUnitFinitePartitionCutoff K S (finiteIndexSUnitBoxWidth K S Γ)).continuous.comp
        continuous_snd)

theorem sUnitPartitionNumerator_eq_one_on_representatives
    (x : G) (hx : x ∈ sUnitCompactRepresentativeSet K S Γ) :
    sUnitPartitionNumerator K S Γ x = 1 := by
  unfold sUnitPartitionNumerator
  rw [(sUnitArchPartitionCutoff_spec K S Γ).2.2.2.2 _ ⟨x, hx, rfl⟩,
    sUnitFinitePartitionCutoff_eq_one_on_representatives K S Γ x hx, mul_one]

theorem sUnitPartitionNumerator_mem_Icc (x : G) :
    sUnitPartitionNumerator K S Γ x ∈ Icc (0 : ℝ) 1 := by
  have ha := (sUnitArchPartitionCutoff_spec K S Γ).2.2.2.1
    ((traceToMixed K).symm (x.1 : W))
  have hf := sUnitFinitePartitionCutoff_mem_Icc K S
    (finiteIndexSUnitBoxWidth K S Γ) x.2
  exact ⟨mul_nonneg ha.1 hf.1,
    (mul_le_mul_of_nonneg_right ha.2 hf.1).trans (by simpa using hf.2)⟩

/-- Compactness is proved in the unit-group topology, retaining inverse
coordinates; continuity of a pullback alone would not establish it. -/
theorem hasCompactSupport_sUnitPartitionNumerator :
    HasCompactSupport (sUnitPartitionNumerator K S Γ) := by
  let b := sUnitArchPartitionCutoff K S Γ
  have hb := sUnitArchPartitionCutoff_spec K S Γ
  let Z := {z : V // z ∈ tsupport b}
  letI : CompactSpace Z := isCompact_iff_compactSpace.mp hb.2.1
  let lift : Z → Wˣ := fun z => mixedUnitOfNormNeZero K (traceToMixed K z.val)
    (hb.2.2.1 z.property)
  have hlift : Continuous lift :=
    continuous_mixedUnitOfNormNeZero K (fun z : Z => traceToMixed K z.val)
      ((traceToMixed K).continuous.comp continuous_subtype_val)
      (fun z => hb.2.2.1 z.property)
  let A : Set Wˣ := Set.range lift
  have hA : IsCompact A := isCompact_range hlift
  let B := finiteLocalValuationBox K S (finiteIndexSUnitBoxWidth K S Γ)
  have hB : IsCompact B := isCompact_finiteLocalValuationBox K S _
  apply (hA.prod hB).of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ (hA.prod hB).isClosed
  intro x hx
  have hmul : b ((traceToMixed K).symm (x.1 : W)) *
      sUnitFinitePartitionCutoff K S (finiteIndexSUnitBoxWidth K S Γ) x.2 ≠ 0 := hx
  have harch := (mul_ne_zero_iff.mp hmul).1
  have hfin := (mul_ne_zero_iff.mp hmul).2
  refine ⟨?_, ?_⟩
  · refine ⟨⟨(traceToMixed K).symm (x.1 : W), subset_closure harch⟩, ?_⟩
    apply Units.ext
    exact (traceToMixed K).apply_symm_apply (x.1 : W)
  · by_contra hnot
    have hnot' : x.2 ∉ finiteLocalValuationBox K S (finiteIndexSUnitBoxWidth K S Γ) := hnot
    exact hfin (by simp [sUnitFinitePartitionCutoff_apply, hnot'])

end HeckeGeneral.Analysis
