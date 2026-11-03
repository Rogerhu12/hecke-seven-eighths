import HeckeGeneral.Analysis.SUnitPartitionArchSmooth
import HeckeGeneral.Analysis.TraceJointSchwartzCutoff

/-! Actual annular unit-partition cutoffs. Compactness comes from the
constructed arch numerator support and the actual radial annulus, not
from an assumed compact pullback of the normalized partition. -/

noncomputable section

namespace HeckeGeneral.Analysis

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic Set Function
open scoped Classical ContDiff Topology BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "W" => mixedEmbedding.mixedSpace K
local notation "G" => sLocalMultiplicativeGroup K S
local notation "T" => sLocalNormOneGroup K S
local notation "R" => traceArchRegular K
local notation "d" => (Module.finrank ℚ K : ℝ)

def sUnitAnnularPartitionCutoff (a : ℝ → ℝ) (ζ : ((v : S) → (v.val.adicCompletion K)ˣ)) (z : V) : ℝ :=
  a (traceArchProductNorm K z * sFiniteProductNorm K S ζ) *
    sUnitNormalizedPartitionArchPullback K S Γ ζ z

theorem sUnitAnnularPartitionCutoff_eq_actual (a : ℝ → ℝ) (ζ : ((v : S) → (v.val.adicCompletion K)ˣ)) (z : R) :
    sUnitAnnularPartitionCutoff K S Γ a ζ z.val =
      a (sLocalProductNorm K S (sUnitPartitionFibreInput K S ζ z)) *
        sUnitNormalizedPartition K S Γ (sUnitPartitionFibreNormalize K S ζ z) := by
  rw [sUnitAnnularPartitionCutoff, sUnitNormalizedPartitionArchPullback, dif_pos z.property]
  rfl

def sUnitAnnularPartitionEnclosure (a0 b0 : ℝ) : Set V :=
  (fun p : ℝ × V => p.1 ^ d⁻¹ • p.2) ''
    (Icc a0 b0 ×ˢ tsupport (sUnitArchPartitionCutoff K S Γ))

theorem isCompact_sUnitAnnularPartitionEnclosure (a0 b0 : ℝ) (ha0 : 0 < a0) :
    IsCompact (sUnitAnnularPartitionEnclosure K S Γ a0 b0) := by
  apply (isCompact_Icc.prod (sUnitArchPartitionCutoff_spec K S Γ).2.1).image_of_continuousOn
  have hr : ContinuousOn (fun p : ℝ × V => p.1 ^ d⁻¹)
      (Icc a0 b0 ×ˢ tsupport (sUnitArchPartitionCutoff K S Γ)) :=
    continuousOn_fst.rpow_const (fun p hp => Or.inl (ha0.trans_le hp.1.1).ne')
  exact hr.smul continuousOn_snd

theorem sUnitAnnularPartitionEnclosure_subset_regular
    (a0 b0 : ℝ) (ha0 : 0 < a0) :
    sUnitAnnularPartitionEnclosure K S Γ a0 b0 ⊆ R := by
  rintro z ⟨⟨r, y⟩, ⟨hr, hy⟩, rfl⟩
  have hreg := (sUnitArchPartitionCutoff_spec K S Γ).2.2.1 hy
  change mixedEmbedding.norm (traceToMixed K (r ^ d⁻¹ • y)) ≠ 0
  rw [map_smul, mixedEmbedding.norm_smul]
  exact mul_ne_zero (pow_ne_zero _ (abs_ne_zero.mpr
    (Real.rpow_pos_of_pos (ha0.trans_le hr.1) _).ne')) hreg

/-- Nonvanishing forces both actual annular radius and an actual arch
numerator point. Their radial image is the required compact enclosure. -/
theorem support_sUnitAnnularPartitionCutoff_subset_enclosure
    (a : ℝ → ℝ) (ζ : ((v : S) → (v.val.adicCompletion K)ˣ)) (a0 b0 : ℝ) (ha0 : 0 < a0)
    (haSupport : tsupport a ⊆ Icc a0 b0) :
    support (sUnitAnnularPartitionCutoff K S Γ a ζ) ⊆
      sUnitAnnularPartitionEnclosure K S Γ a0 b0 := by
  intro z hz
  have hparts := mul_ne_zero_iff.mp hz
  have hzR : z ∈ R := by
    by_contra hnot
    exact hparts.2 (by simp [sUnitNormalizedPartitionArchPullback, hnot])
  let zR : R := ⟨z, hzR⟩
  let x : T := sUnitPartitionFibreNormalize K S ζ zR
  let r : ℝ := traceArchProductNorm K z * sFiniteProductNorm K S ζ
  let y : V := (traceToMixed K).symm (((x : G).1) : W)
  have hr : r ∈ Icc a0 b0 := haSupport (subset_closure hparts.1)
  have hrpos : 0 < r := ha0.trans_le hr.1
  have hη : sUnitNormalizedPartition K S Γ x ≠ 0 := by
    simpa only [sUnitNormalizedPartitionArchPullback, dif_pos hzR] using hparts.2
  have hb : sUnitPartitionBase K S Γ x ≠ 0 := by
    intro hzero
    exact hη (by simp [sUnitNormalizedPartition, hzero])
  have hbarch : sUnitArchPartitionCutoff K S Γ y ≠ 0 := by
    change sUnitArchPartitionCutoff K S Γ y *
      sUnitFinitePartitionCutoff K S (finiteIndexSUnitBoxWidth K S Γ) (x : G).2 ≠ 0 at hb
    exact (mul_ne_zero_iff.mp hb).1
  have hy : y = (r ^ d⁻¹)⁻¹ • z := by
    apply (traceToMixed K).injective
    change traceToMixed K ((traceToMixed K).symm _) = _
    rw [ContinuousLinearEquiv.apply_symm_apply, sUnitPartitionFibreNormalize_arch, map_smul] <;> rfl
  refine ⟨(r, y), ⟨hr, subset_closure hbarch⟩, ?_⟩
  change r ^ d⁻¹ • y = z
  rw [hy, smul_smul, mul_inv_cancel₀ (Real.rpow_pos_of_pos hrpos _).ne', one_smul]

theorem tsupport_sUnitAnnularPartitionCutoff_subset_enclosure
    (a : ℝ → ℝ) (ζ : ((v : S) → (v.val.adicCompletion K)ˣ)) (a0 b0 : ℝ) (ha0 : 0 < a0)
    (haSupport : tsupport a ⊆ Icc a0 b0) :
    tsupport (sUnitAnnularPartitionCutoff K S Γ a ζ) ⊆
      sUnitAnnularPartitionEnclosure K S Γ a0 b0 :=
  closure_minimal
    (support_sUnitAnnularPartitionCutoff_subset_enclosure K S Γ a ζ a0 b0 ha0 haSupport)
    (isCompact_sUnitAnnularPartitionEnclosure K S Γ a0 b0 ha0).isClosed

theorem hasCompactSupport_sUnitAnnularPartitionCutoff
    (a : ℝ → ℝ) (ζ : ((v : S) → (v.val.adicCompletion K)ˣ)) (a0 b0 : ℝ) (ha0 : 0 < a0)
    (haSupport : tsupport a ⊆ Icc a0 b0) :
    HasCompactSupport (sUnitAnnularPartitionCutoff K S Γ a ζ) :=
  (isCompact_sUnitAnnularPartitionEnclosure K S Γ a0 b0 ha0).of_isClosed_subset
    (isClosed_tsupport _)
    (tsupport_sUnitAnnularPartitionCutoff_subset_enclosure K S Γ a ζ a0 b0 ha0 haSupport)

theorem tsupport_sUnitAnnularPartitionCutoff_subset_regular
    (a : ℝ → ℝ) (ζ : ((v : S) → (v.val.adicCompletion K)ˣ)) (a0 b0 : ℝ) (ha0 : 0 < a0)
    (haSupport : tsupport a ⊆ Icc a0 b0) :
    tsupport (sUnitAnnularPartitionCutoff K S Γ a ζ) ⊆ R :=
  (tsupport_sUnitAnnularPartitionCutoff_subset_enclosure K S Γ a ζ a0 b0 ha0 haSupport).trans
    (sUnitAnnularPartitionEnclosure_subset_regular K S Γ a0 b0 ha0)

theorem contDiff_sUnitAnnularPartitionCutoff
    (a : ℝ → ℝ) (ha : ContDiff ℝ ∞ a) (ζ : ((v : S) → (v.val.adicCompletion K)ˣ)) (a0 b0 : ℝ) (ha0 : 0 < a0)
    (haSupport : tsupport a ⊆ Icc a0 b0) :
    ContDiff ℝ ∞ (sUnitAnnularPartitionCutoff K S Γ a ζ) := by
  have hOn : ContDiffOn ℝ ∞ (sUnitAnnularPartitionCutoff K S Γ a ζ) R :=
    (ha.comp_contDiffOn ((contDiffOn_traceArchProductNorm K).mul contDiffOn_const)).mul
      (contDiffOn_sUnitNormalizedPartitionArchPullback K S Γ ζ)
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases hz : z ∈ tsupport (sUnitAnnularPartitionCutoff K S Γ a ζ)
  · exact hOn.contDiffAt ((isOpen_traceArchRegular K).mem_nhds
      (tsupport_sUnitAnnularPartitionCutoff_subset_regular K S Γ a ζ a0 b0 ha0 haSupport hz))
  · exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hz)

def sUnitAnnularPartitionJointCutoff (a : ℝ → ℝ) (ζ ξ : ((v : S) → (v.val.adicCompletion K)ˣ)) (p : V × V) : ℂ :=
  (sUnitAnnularPartitionCutoff K S Γ a ζ p.1 *
    sUnitAnnularPartitionCutoff K S Γ a ξ p.2 : ℝ)

/-- All three actual χ hypotheses of TraceJointSchwartzCutoff are proved
for the same original subgroup and normalized partition in both columns. -/
theorem sUnitAnnularPartitionJointCutoff_spec
    (a : ℝ → ℝ) (ha : ContDiff ℝ ∞ a) (ζ ξ : ((v : S) → (v.val.adicCompletion K)ˣ)) (a0 b0 : ℝ) (ha0 : 0 < a0)
    (haSupport : tsupport a ⊆ Icc a0 b0) :
    ContDiff ℝ ∞ (sUnitAnnularPartitionJointCutoff K S Γ a ζ ξ) ∧
      HasCompactSupport (sUnitAnnularPartitionJointCutoff K S Γ a ζ ξ) ∧
      tsupport (sUnitAnnularPartitionJointCutoff K S Γ a ζ ξ) ⊆ R ×ˢ R := by
  have hζ := contDiff_sUnitAnnularPartitionCutoff K S Γ a ha ζ a0 b0 ha0 haSupport
  have hξ := contDiff_sUnitAnnularPartitionCutoff K S Γ a ha ξ a0 b0 ha0 haSupport
  have hcζ := hasCompactSupport_sUnitAnnularPartitionCutoff K S Γ a ζ a0 b0 ha0 haSupport
  have hcξ := hasCompactSupport_sUnitAnnularPartitionCutoff K S Γ a ξ a0 b0 ha0 haSupport
  have hs : tsupport (sUnitAnnularPartitionJointCutoff K S Γ a ζ ξ) ⊆
      tsupport (sUnitAnnularPartitionCutoff K S Γ a ζ) ×ˢ
        tsupport (sUnitAnnularPartitionCutoff K S Γ a ξ) := by
    apply closure_minimal _ ((isClosed_tsupport _).prod (isClosed_tsupport _))
    intro p hp
    have hreal : sUnitAnnularPartitionCutoff K S Γ a ζ p.1 *
        sUnitAnnularPartitionCutoff K S Γ a ξ p.2 ≠ 0 := by
      intro hzero
      exact hp (by simp [sUnitAnnularPartitionJointCutoff, hzero])
    exact ⟨subset_closure (mul_ne_zero_iff.mp hreal).1,
      subset_closure (mul_ne_zero_iff.mp hreal).2⟩
  refine ⟨Complex.ofRealCLM.contDiff.comp
    ((hζ.comp contDiff_fst).mul (hξ.comp contDiff_snd)),
    (hcζ.prod hcξ).of_isClosed_subset (isClosed_tsupport _) hs, ?_⟩
  exact hs.trans (Set.prod_mono
    (tsupport_sUnitAnnularPartitionCutoff_subset_regular K S Γ a ζ a0 b0 ha0 haSupport)
    (tsupport_sUnitAnnularPartitionCutoff_subset_regular K S Γ a ξ a0 b0 ha0 haSupport))

end HeckeGeneral.Analysis
