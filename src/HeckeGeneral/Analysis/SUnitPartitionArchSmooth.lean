import HeckeGeneral.Analysis.SUnitNormalizedPartition
import HeckeGeneral.Arithmetic.SIntegerBalancedRepresentatives
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! Smooth archimedean fibres of the actual normalized partition. The
finite unit coordinate is fixed. Smoothness is stated on the regular
trace locus, without putting a real manifold structure on the local group. -/

noncomputable section

namespace HeckeGeneral.Analysis

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic Set Filter
open scoped Classical Topology ContDiff BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "W" => mixedEmbedding.mixedSpace K
local notation "G" => sLocalMultiplicativeGroup K S
local notation "T" => sLocalNormOneGroup K S
local notation "R" => traceArchRegular K

def sUnitPartitionFibreInput (ζ : ((v : S) → (v.val.adicCompletion K)ˣ)) (z : R) : G :=
  (mixedUnitOfNormNeZero K (traceToMixed K z.val) z.property, ζ)

theorem continuous_sUnitPartitionFibreInput (ζ : ((v : S) → (v.val.adicCompletion K)ˣ)) :
    Continuous (sUnitPartitionFibreInput K S ζ) :=
  (continuous_mixedUnitOfNormNeZero K (fun z : R => traceToMixed K z.val)
    ((traceToMixed K).continuous.comp continuous_subtype_val) (fun z => z.property)).prodMk
      continuous_const

def sUnitPartitionFibreRadius (ζ : ((v : S) → (v.val.adicCompletion K)ˣ)) (z : R) : {r : ℝ // 0 < r} :=
  ⟨sLocalProductNorm K S (sUnitPartitionFibreInput K S ζ z), sLocalProductNorm_pos K S _⟩

def sUnitPartitionFibreNormalize (ζ : ((v : S) → (v.val.adicCompletion K)ˣ)) (z : R) : T :=
  ⟨(sLocalNormSection K S (sUnitPartitionFibreRadius K S ζ z))⁻¹ *
    sUnitPartitionFibreInput K S ζ z, by
      rw [mem_sLocalNormOneGroup, sLocalProductNorm_mul, sLocalProductNorm_inv,
        sLocalProductNorm_section]
      exact inv_mul_cancel₀ (sLocalProductNorm_pos K S _).ne'⟩

theorem continuous_sUnitPartitionFibreNormalize (ζ : ((v : S) → (v.val.adicCompletion K)ˣ)) :
    Continuous (sUnitPartitionFibreNormalize K S ζ) := by
  have hr : Continuous (sUnitPartitionFibreRadius K S ζ) :=
    ((continuous_sLocalProductNorm K S).comp
      (continuous_sUnitPartitionFibreInput K S ζ)).subtype_mk _
  exact (((continuous_sLocalNormSection K S).comp hr).inv.mul
    (continuous_sUnitPartitionFibreInput K S ζ)).subtype_mk _

theorem sUnitPartitionFibreNormalize_finite (ζ : ((v : S) → (v.val.adicCompletion K)ˣ)) (z : R) :
    ((sUnitPartitionFibreNormalize K S ζ z : T) : G).2 = ζ := by
  simp [sUnitPartitionFibreNormalize, sLocalNormSection, sUnitPartitionFibreInput]

/-- The degree is the actual number-field degree, including complex
multiplicity through the actual product norm. -/
def sUnitPartitionFibreScale (ζ : ((v : S) → (v.val.adicCompletion K)ˣ)) (z : V) : ℝ :=
  ((traceArchProductNorm K z * sFiniteProductNorm K S ζ) ^
    ((Module.finrank ℚ K : ℝ)⁻¹))⁻¹

theorem sUnitPartitionFibreNormalize_arch (ζ : ((v : S) → (v.val.adicCompletion K)ˣ)) (z : R) :
    (((sUnitPartitionFibreNormalize K S ζ z : T) : G).1 : W) =
      sUnitPartitionFibreScale K S ζ z.val • traceToMixed K z.val := by
  change algebraMap ℝ W
      (((traceArchProductNorm K z.val * sFiniteProductNorm K S ζ) ^
        ((Module.finrank ℚ K : ℝ)⁻¹))⁻¹) * traceToMixed K z.val = _
  rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  rfl

theorem contDiffOn_sUnitPartitionFibreScale (ζ : ((v : S) → (v.val.adicCompletion K)ˣ)) :
    ContDiffOn ℝ ∞ (sUnitPartitionFibreScale K S ζ) R := by
  intro z hz
  have hprod : ContDiffAt ℝ ∞
      (fun z : V => traceArchProductNorm K z * sFiniteProductNorm K S ζ) z :=
    (contDiffAt_traceArchProductNorm K hz).mul contDiffAt_const
  have hp : 0 < traceArchProductNorm K z * sFiniteProductNorm K S ζ :=
    mul_pos (traceArchProductNorm_pos K hz) (sFiniteProductNorm_pos K S ζ)
  exact ((hprod.rpow_const_of_ne hp.ne').inv
    (Real.rpow_pos_of_pos hp _).ne').contDiffWithinAt

variable (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]

def sUnitPartitionFibreBaseTerm (ζ : ((v : S) → (v.val.adicCompletion K)ˣ)) (u : Γ) (z : V) : ℝ :=
  sUnitArchPartitionCutoff K S Γ
    (traceUnitMulEquiv K (((sUnitPartitionDiagonal K S Γ u : T) : G).1)
      (sUnitPartitionFibreScale K S ζ z • z)) *
  sUnitFinitePartitionCutoff K S (finiteIndexSUnitBoxWidth K S Γ)
    ((((sUnitPartitionDiagonal K S Γ u : T) : G).2) * ζ)

theorem sUnitPartitionFibreBaseTerm_eq_actual (ζ : ((v : S) → (v.val.adicCompletion K)ˣ)) (u : Γ) (z : R) :
    sUnitPartitionFibreBaseTerm K S Γ ζ u z.val =
      sUnitPartitionBase K S Γ
        (sUnitPartitionDiagonal K S Γ u * sUnitPartitionFibreNormalize K S ζ z) := by
  have ha : (traceToMixed K).symm
      ((((sUnitPartitionDiagonal K S Γ u * sUnitPartitionFibreNormalize K S ζ z : T) : G).1) : W) =
      traceUnitMulEquiv K (((sUnitPartitionDiagonal K S Γ u : T) : G).1)
        (sUnitPartitionFibreScale K S ζ z.val • z.val) := by
    apply (traceToMixed K).injective
    rw [ContinuousLinearEquiv.apply_symm_apply, traceToMixed_traceUnitMulEquiv, map_smul]
    change _ * _ = _ * _
    rw [sUnitPartitionFibreNormalize_arch]
  unfold sUnitPartitionFibreBaseTerm sUnitPartitionBase sUnitPartitionNumerator
  rw [ha]
  congr 1
  congr 1
  change _ * ζ = _ * _
  rw [sUnitPartitionFibreNormalize_finite]

theorem contDiffOn_sUnitPartitionFibreBaseTerm (ζ : ((v : S) → (v.val.adicCompletion K)ˣ)) (u : Γ) :
    ContDiffOn ℝ ∞ (sUnitPartitionFibreBaseTerm K S Γ ζ u) R := by
  have hscale := (contDiffOn_sUnitPartitionFibreScale K S ζ).smul contDiffOn_id
  exact (((sUnitArchPartitionCutoff_spec K S Γ).1.comp_contDiffOn
    ((traceUnitMulEquiv K (((sUnitPartitionDiagonal K S Γ u : T) : G).1)).contDiff.comp_contDiffOn
      hscale)).mul contDiffOn_const)

/-- A locally finite smooth family on an open locus may be summed there.
The subtype is used only for topology, not as a real differentiable space. -/
private theorem contDiffOn_tsum_of_locallyFinite_restrict
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} (U : Set E) (f : ι → E → ℝ)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) U)
    (hlf : LocallyFinite (fun i => Function.support (fun z : U => f i z.val))) :
    ContDiffOn ℝ ∞ (fun z => ∑' i, f i z) U := by
  intro z hz
  obtain ⟨s, hs⟩ := hlf.exists_finset_support (⟨z, hz⟩ : U)
  have hwithin : ∀ᶠ w in 𝓝[U] z, Function.support (fun i => f i w) ⊆ s := by
    rw [← map_nhds_subtype_val (⟨z, hz⟩ : U)]
    exact hs
  have heq : (fun w => ∑' i, f i w) =ᶠ[𝓝[U] z] (fun w => ∑ i ∈ s, f i w) := by
    filter_upwards [hwithin] with w hw
    apply tsum_eq_sum
    intro i hi
    by_contra hne
    exact hi (hw hne)
  exact (ContDiffWithinAt.sum (fun i _ => hf i z hz)).congr_of_eventuallyEq_of_mem heq hz

def sUnitPartitionFibrePeriod (ζ : ((v : S) → (v.val.adicCompletion K)ˣ)) (z : V) : ℝ :=
  ∑' u : Γ, sUnitPartitionFibreBaseTerm K S Γ ζ u z

theorem sUnitPartitionFibrePeriod_eq_actual (ζ : ((v : S) → (v.val.adicCompletion K)ˣ)) (z : R) :
    sUnitPartitionFibrePeriod K S Γ ζ z.val =
      sUnitPartitionPeriod K S Γ (sUnitPartitionFibreNormalize K S ζ z) := by
  apply tsum_congr
  intro u
  exact sUnitPartitionFibreBaseTerm_eq_actual K S Γ ζ u z

theorem contDiffOn_sUnitPartitionFibrePeriod (ζ : ((v : S) → (v.val.adicCompletion K)ˣ)) :
    ContDiffOn ℝ ∞ (sUnitPartitionFibrePeriod K S Γ ζ) R := by
  apply contDiffOn_tsum_of_locallyFinite_restrict R _
    (contDiffOn_sUnitPartitionFibreBaseTerm K S Γ ζ)
  have hlf := (locallyFinite_sUnitPartition_tsupport K S Γ
    (sUnitPartitionBase K S Γ) (hasCompactSupport_sUnitPartitionBase K S Γ)).preimage_continuous
      (continuous_sUnitPartitionFibreNormalize K S ζ)
  apply hlf.subset
  intro u z hz
  change sUnitPartitionFibreBaseTerm K S Γ ζ u z.val ≠ 0 at hz
  rw [sUnitPartitionFibreBaseTerm_eq_actual] at hz
  exact subset_closure hz

def sUnitNormalizedPartitionArchFibre (ζ : ((v : S) → (v.val.adicCompletion K)ˣ)) (z : V) : ℝ :=
  sUnitPartitionFibreBaseTerm K S Γ ζ 1 z / sUnitPartitionFibrePeriod K S Γ ζ z

/-- The smooth formula is literally the existing normalized partition
pulled back along the actual norm-one normalization map. -/
theorem sUnitNormalizedPartitionArchFibre_eq_actual (ζ : ((v : S) → (v.val.adicCompletion K)ˣ)) (z : R) :
    sUnitNormalizedPartitionArchFibre K S Γ ζ z.val =
      sUnitNormalizedPartition K S Γ (sUnitPartitionFibreNormalize K S ζ z) := by
  rw [sUnitNormalizedPartitionArchFibre, sUnitPartitionFibreBaseTerm_eq_actual,
    sUnitPartitionFibrePeriod_eq_actual]
  simp only [map_one, one_mul, sUnitNormalizedPartition]

theorem contDiffOn_sUnitNormalizedPartitionArchFibre (ζ : ((v : S) → (v.val.adicCompletion K)ˣ)) :
    ContDiffOn ℝ ∞ (sUnitNormalizedPartitionArchFibre K S Γ ζ) R := by
  apply (contDiffOn_sUnitPartitionFibreBaseTerm K S Γ ζ 1).div
    (contDiffOn_sUnitPartitionFibrePeriod K S Γ ζ)
  intro z hz
  rw [sUnitPartitionFibrePeriod_eq_actual K S Γ ζ ⟨z, hz⟩]
  exact (sUnitPartitionPeriod_pos K S Γ _).ne'

/-- A total function used solely to state smoothness of the literal η
pullback on the regular locus. No boundary regularity is claimed. -/
def sUnitNormalizedPartitionArchPullback (ζ : ((v : S) → (v.val.adicCompletion K)ˣ)) (z : V) : ℝ :=
  if hz : z ∈ R then
    sUnitNormalizedPartition K S Γ (sUnitPartitionFibreNormalize K S ζ ⟨z, hz⟩)
  else 0

/-- The existing actual η, rather than a replacement cutoff, has smooth
archimedean fibres for every fixed finite unit coordinate. -/
theorem contDiffOn_sUnitNormalizedPartitionArchPullback (ζ : ((v : S) → (v.val.adicCompletion K)ˣ)) :
    ContDiffOn ℝ ∞ (sUnitNormalizedPartitionArchPullback K S Γ ζ) R := by
  apply (contDiffOn_sUnitNormalizedPartitionArchFibre K S Γ ζ).congr
  intro z hz
  rw [sUnitNormalizedPartitionArchPullback, dif_pos hz]
  exact (sUnitNormalizedPartitionArchFibre_eq_actual K S Γ ζ ⟨z, hz⟩).symm

end HeckeGeneral.Analysis
