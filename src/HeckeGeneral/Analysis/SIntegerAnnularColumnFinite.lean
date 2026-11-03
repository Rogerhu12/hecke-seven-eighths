import HeckeGeneral.Analysis.SUnitPartitionFiniteFibres
import HeckeGeneral.Arithmetic.SIntegerCompactDenominators
import HeckeGeneral.Arithmetic.ClearedUnitLattice

/-!
actual annular columns have finite element support.
No quotient by associates is taken. Both the actual diagonal finite
coordinate and the scaled trace embedding occur in the final statement.
-/

noncomputable section

namespace HeckeGeneral.Analysis

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic
open scoped Classical nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "W" => mixedEmbedding.mixedSpace K
local notation "N" => NonzeroRingElements (S.integer K)
local notation "Z" => SFiniteLocalGroup K S

/-- Compact additive conditions in both sets of places select finitely
many actual nonzero S-integers. Compactness is used to construct a common
denominator; no finiteness of the original diagonal is assumed. -/
theorem finite_sInteger_diagonal_compact_conditions
    (Carch : Set V) (hCarch : IsCompact Carch)
    (Cf : Set ((v : S) → v.val.adicCompletion K)) (hCf : IsCompact Cf) :
    Set.Finite {m : N | traceEmbedding K (m.val : K) ∈ Carch ∧
      (fun v : S => algebraMap K (v.val.adicCompletion K) (m.val : K)) ∈ Cf} := by
  obtain ⟨a, ha, hclear⟩ :=
    exists_nonzero_integer_mul_sIntegers_mem_range_of_compact K S
      (Set.toFinite S) Cf hCf
  let L := traceIdealLattice K (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
  let A : V → V := fun z => (traceToMixed K).symm
    (mixedEmbedding K (algebraMap (𝓞 K) K a) * traceToMixed K z)
  have hA : Continuous A :=
    (traceToMixed K).symm.continuous.comp
      (continuous_const.mul (traceToMixed K).continuous)
  have hclosed : IsClosed (L : Set V) :=
    @AddSubgroup.isClosed_of_discreteTopology _ _ _ _ _ L.toAddSubgroup
      (inferInstanceAs (DiscreteTopology L))
  have hfinite : Set.Finite ((A '' Carch) ∩ (L : Set V)) :=
    Metric.finite_isBounded_inter_isClosed
      (show IsDiscrete (L : Set V) from ⟨inferInstanceAs (DiscreteTopology L)⟩)
      (hCarch.image hA).isBounded hclosed
  let f : N → V := fun m =>
    traceEmbedding K (algebraMap (𝓞 K) K a * (m.val : K))
  have hf : Function.Injective f := by
    intro m n hmn
    have he := traceEmbedding_injective K hmn
    have he' := mul_left_cancel₀ (RingOfIntegers.coe_ne_zero_iff.mpr ha) he
    exact Subtype.ext (Subtype.ext he')
  apply Set.Finite.of_finite_image (f := f) _ hf.injOn
  apply hfinite.subset
  rintro z ⟨m, ⟨hmarch, hmf⟩, rfl⟩
  refine ⟨?_, ?_⟩
  · refine ⟨traceEmbedding K (m.val : K), hmarch, ?_⟩
    simp only [A, f, traceEmbedding, ContinuousLinearEquiv.apply_symm_apply, map_mul]
  · exact (traceEmbedding_mem_traceIdealLattice K 1).mpr
      ((FractionalIdeal.mem_one_iff (𝓞 K)⁰).mpr (hclear m.val hmf))

variable (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]

/-- The literal annular column, with its actual finite diagonal coordinate.
The real scale is arbitrary and nonzero; taking the degree-th-root scale
of a positive norm parameter is a direct specialization. -/
def sIntegerAnnularColumn (a : ℝ → ℝ) (r : ℝ) (m : N) : ℝ :=
  sUnitAnnularPartitionCutoff K S Γ a
    (sLocalNonzeroIntegerDiagonal K S m).2
    (r⁻¹ • traceEmbedding K (m.val : K))

/-- Every element, including every torsion translate, remains an index.
Finiteness follows from the actual partition enclosure and valuation box. -/
theorem finite_support_sIntegerAnnularColumn
    (a : ℝ → ℝ) (a0 b0 : ℝ) (ha0 : 0 < a0)
    (haSupport : tsupport a ⊆ Set.Icc a0 b0)
    (r : ℝ) (hr : r ≠ 0) :
    Set.Finite (Function.support (sIntegerAnnularColumn K S Γ a r)) := by
  let B : Set Z := finiteLocalValuationBox K S (finiteIndexSUnitBoxWidth K S Γ)
  let Cf : Set ((v : S) → v.val.adicCompletion K) :=
    (fun ζ : Z => fun v : S => (ζ v).val) '' B
  have hCf : IsCompact Cf :=
    (isCompact_finiteLocalValuationBox K S _).image
      (continuous_pi fun v => Units.continuous_val.comp (continuous_apply v))
  let C : Set V := sUnitAnnularPartitionEnclosure K S Γ a0 b0
  have hC : IsCompact C :=
    isCompact_sUnitAnnularPartitionEnclosure K S Γ a0 b0 ha0
  have hfinite := finite_sInteger_diagonal_compact_conditions K S
    ((fun z : V => r • z) '' C)
    (hC.image (continuous_const_smul r))
    Cf hCf
  apply hfinite.subset
  intro m hm
  have hm' : sUnitAnnularPartitionCutoff K S Γ a
      (sLocalNonzeroIntegerDiagonal K S m).2
      (r⁻¹ • traceEmbedding K (m.val : K)) ≠ 0 := hm
  have harch := support_sUnitAnnularPartitionCutoff_subset_enclosure K S Γ
    a (sLocalNonzeroIntegerDiagonal K S m).2 a0 b0 ha0 haSupport hm'
  have hbox : (sLocalNonzeroIntegerDiagonal K S m).2 ∈ B := by
    by_contra hnot
    have hz := sUnitAnnularPartitionCutoff_eq_zero_of_not_mem_box K S Γ a
      (sLocalNonzeroIntegerDiagonal K S m).2 hnot
    exact hm' (congrFun hz _)
  refine ⟨?_, ?_⟩
  · refine ⟨r⁻¹ • traceEmbedding K (m.val : K), harch, ?_⟩
    simp only [smul_smul, mul_inv_cancel₀ hr, one_smul]
  · exact ⟨(sLocalNonzeroIntegerDiagonal K S m).2, hbox, rfl⟩

end HeckeGeneral.Analysis
