import HeckeGeneral.Arithmetic.SUnitCompactRepresentatives
import Mathlib.Topology.LocallyConstant.Algebra
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Clopen

/-! The existing actual finite valuation box is compact and open. Its
literal characteristic function is the finite-coordinate cutoff for the
original subgroup's compact representatives. -/

noncomputable section

namespace HeckeGeneral.Analysis

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters Set
open scoped Classical

variable (K : Type*) [Field K] [NumberField K]

theorem mem_localValuationBox_iff_order_bounds
    (v : HeightOneSpectrum (𝓞 K)) (H : ℕ) (x : (v.adicCompletion K)ˣ) :
    x ∈ localValuationBox K v H ↔
      0 ≤ -(localOrderHom K v x).toAdd ∧
        -(localOrderHom K v x).toAdd < (H : ℤ) := by
  constructor
  · intro hx
    obtain ⟨e, he⟩ := mem_iUnion.mp hx
    obtain ⟨u, rfl⟩ := he
    have horder :
        (localOrderHom K v (localIntegerUnitsEmbedding K v u *
          localUniformizerUnit K v ^ (-(e.val : ℤ)))).toAdd = -(e.val : ℤ) := by
      rw [map_mul, map_zpow, localOrder_integralUnit, localOrder_uniformizer]
      simp
    rw [horder, neg_neg]
    exact ⟨Int.natCast_nonneg _, by exact_mod_cast e.isLt⟩
  · rintro ⟨hlo, hhi⟩
    exact mem_localValuationBox_of_bounds K v H x hlo hhi

theorem isClopen_localValuationBox (v : HeightOneSpectrum (𝓞 K)) (H : ℕ) :
    IsClopen (localValuationBox K v H) := by
  have hset : localValuationBox K v H =
      (localOrderHom K v) ⁻¹'
        {n : Multiplicative ℤ | 0 ≤ -n.toAdd ∧ -n.toAdd < (H : ℤ)} := by
    ext x
    exact mem_localValuationBox_iff_order_bounds K v H x
  rw [hset]
  exact (isClopen_discrete _).preimage (localOrder K v).continuous

variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

theorem isClopen_finiteLocalValuationBox (H : ℕ) :
    IsClopen (finiteLocalValuationBox K S H) := by
  have hset : finiteLocalValuationBox K S H =
      ⋂ v : S, (fun x : ((v : S) → (v.val.adicCompletion K)ˣ) => x v) ⁻¹' localValuationBox K v.val H := by
    ext x
    simp only [finiteLocalValuationBox, mem_setOf_eq, mem_iInter, mem_preimage]
  rw [hset]
  exact isClopen_iInter_of_finite fun v =>
    (isClopen_localValuationBox K v.val H).preimage (continuous_apply v)

def sUnitFinitePartitionCutoff (H : ℕ) : LocallyConstant ((v : S) → (v.val.adicCompletion K)ˣ) ℝ :=
  LocallyConstant.charFn ℝ (isClopen_finiteLocalValuationBox K S H)

@[simp] theorem sUnitFinitePartitionCutoff_apply (H : ℕ) (x : ((v : S) → (v.val.adicCompletion K)ˣ)) :
    sUnitFinitePartitionCutoff K S H x =
      if x ∈ finiteLocalValuationBox K S H then 1 else 0 := rfl

theorem hasCompactSupport_sUnitFinitePartitionCutoff (H : ℕ) :
    HasCompactSupport (sUnitFinitePartitionCutoff K S H : ((v : S) → (v.val.adicCompletion K)ˣ) → ℝ) := by
  apply (isCompact_finiteLocalValuationBox K S H).of_isClosed_subset
    (isClosed_tsupport _)
  apply closure_minimal _ (isClopen_finiteLocalValuationBox K S H).isClosed
  intro x hx
  by_contra hnot
  exact hx (by simp [sUnitFinitePartitionCutoff_apply, hnot])

theorem isLocallyConstant_sUnitFinitePartitionCutoff (H : ℕ) :
    IsLocallyConstant (sUnitFinitePartitionCutoff K S H : ((v : S) → (v.val.adicCompletion K)ˣ) → ℝ) :=
  (sUnitFinitePartitionCutoff K S H).isLocallyConstant

theorem sUnitFinitePartitionCutoff_mem_Icc (H : ℕ) (x : ((v : S) → (v.val.adicCompletion K)ˣ)) :
    sUnitFinitePartitionCutoff K S H x ∈ Icc (0 : ℝ) 1 := by
  rw [sUnitFinitePartitionCutoff_apply]
  split_ifs <;> simp

/-- The actual representative parameter has cutoff value exactly one. -/
@[simp] theorem sUnitFinitePartitionCutoff_representativeMap
    (Γ : Subgroup (S.unit K)) (p : SUnitRepresentativeParameters K S Γ) :
    sUnitFinitePartitionCutoff K S (finiteIndexSUnitBoxWidth K S Γ)
      (sUnitRepresentativeMap K S Γ p).2 = 1 := by
  change sUnitFinitePartitionCutoff K S (finiteIndexSUnitBoxWidth K S Γ) p.2.val = 1
  simp only [sUnitFinitePartitionCutoff_apply, if_pos p.2.property]

/-- No enlargement of S or change of subgroup is used for the cutoff. -/
theorem sUnitFinitePartitionCutoff_eq_one_on_representatives
    (Γ : Subgroup (S.unit K)) (x : sLocalMultiplicativeGroup K S)
    (hx : x ∈ sUnitCompactRepresentativeSet K S Γ) :
    sUnitFinitePartitionCutoff K S (finiteIndexSUnitBoxWidth K S Γ) x.2 = 1 := by
  obtain ⟨p, rfl⟩ := hx
  exact sUnitFinitePartitionCutoff_representativeMap K S Γ p

end HeckeGeneral.Analysis
