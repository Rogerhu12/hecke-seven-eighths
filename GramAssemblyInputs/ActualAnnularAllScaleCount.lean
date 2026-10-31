import NonzeroLatticeAllScaleCount
import HeckeGeneral.Arithmetic.SIntegerLocalDiagonal

/-!
UNCOMPILED candidate. The actual nonzero S-integer annular columns have
O(N) elements for every N > 0, with all associates retained. The fixed
denominator is cleared before the scale is chosen. Small scales use the
proved lattice gap; no nonempty-annulus lower bound is a premise.

The main counting argument adapts the existing verified
SIntegerAnnularColumnCount proof to the nonzero lattice target.
-/

noncomputable section

namespace HeckeGeneral.Analysis.ActualAnnularAllScaleCountDraft

open MeasureTheory Filter Set
open NonzeroLatticeAllScaleCountDraft
open scoped Topology Classical

section ActualColumns

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic
open scoped nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]

local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "N" => NonzeroRingElements (S.integer K)
local notation "Z" => SFiniteLocalGroup K S

/-- An all-positive-scale count for the actual element-indexed annular column. The
clearing denominator, lattice and constant are chosen before the moving
scale. Torsion translates and all other associates remain actual indices. -/
theorem exists_sIntegerAnnularColumn_allScale_count_le
    (a : ℝ → ℝ) (a0 b0 : ℝ) (ha0 : 0 < a0)
    (haSupport : tsupport a ⊆ Set.Icc a0 b0) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r →
      (Nat.card (Function.support (sIntegerAnnularColumn K S Γ a r)) : ℝ) ≤
        C * r ^ Module.finrank ℚ K := by
  let B : Set Z := finiteLocalValuationBox K S (finiteIndexSUnitBoxWidth K S Γ)
  let Cf : Set ((v : S) → v.val.adicCompletion K) :=
    (fun ζ : Z => fun v : S => (ζ v).val) '' B
  have hCf : IsCompact Cf :=
    (isCompact_finiteLocalValuationBox K S _).image
      (continuous_pi fun v => Units.continuous_val.comp (continuous_apply v))
  obtain ⟨den, hden, hclear⟩ :=
    exists_nonzero_integer_mul_sIntegers_mem_range_of_compact K S (Set.toFinite S) Cf hCf
  let L := traceIdealLattice K (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
  let A : V → V := fun z => (traceToMixed K).symm
    (mixedEmbedding K (algebraMap (𝓞 K) K den) * traceToMixed K z)
  have hA : Continuous A := (traceToMixed K).symm.continuous.comp
    (continuous_const.mul (traceToMixed K).continuous)
  have hAsmul (r : ℝ) (z : V) : A (r • z) = r • A z := by
    simp only [A, map_smul, mul_smul_comm]
  let enclosure := sUnitAnnularPartitionEnclosure K S Γ a0 b0
  have hcompact : IsCompact (A '' enclosure) :=
    (isCompact_sUnitAnnularPartitionEnclosure K S Γ a0 b0 ha0).image hA
  obtain ⟨R, hR⟩ := hcompact.isBounded.subset_closedBall (0 : V)
  let D : ℝ := max 1 R
  have hD : 1 ≤ D := le_max_left _ _
  have hDbound (z : V) (hz : z ∈ enclosure) : ‖A z‖ ≤ D := by
    have hb := hR (Set.mem_image_of_mem A hz)
    have hb' : ‖A z‖ ≤ R := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hb
    exact hb'.trans (le_max_right 1 R)
  obtain ⟨C0, hC0, hcount⟩ := exists_nonzero_lattice_norm_power_count_le L
  let d := Module.finrank ℝ V
  have hd : d = Module.finrank ℚ K := mixedEmbedding.euclidean.finrank K
  refine ⟨C0 * D ^ d, by positivity, fun r hr => ?_⟩
  have hrpos : 0 < r := hr
  have hDpos : 0 < D := zero_lt_one.trans_le hD
  have hpow : 0 < (r * D) ^ d := pow_pos (mul_pos hrpos hDpos) _
  let target : Set V := {x : V | x ≠ 0 ∧ ‖x‖ ^ d ≤ (r * D) ^ d} ∩ (L : Set V)
  have htarget : target.Finite := finite_nonzero_lattice_norm_power_sublevel L _
  let f : N → V := fun m =>
    traceEmbedding K (algebraMap (𝓞 K) K den * (m.val : K))
  have hf : Function.Injective f := by
    intro m n hmn
    have he := traceEmbedding_injective K hmn
    have he' := mul_left_cancel₀ (RingOfIntegers.coe_ne_zero_iff.mpr hden) he
    exact Subtype.ext (Subtype.ext he')
  have hmem (m : N) (hm : m ∈ Function.support (sIntegerAnnularColumn K S Γ a r)) :
      f m ∈ target := by
    have hm' : sUnitAnnularPartitionCutoff K S Γ a
        (sLocalNonzeroIntegerDiagonal K S m).2
        (r⁻¹ • traceEmbedding K (m.val : K)) ≠ 0 := hm
    have harch := support_sUnitAnnularPartitionCutoff_subset_enclosure K S Γ a
      (sLocalNonzeroIntegerDiagonal K S m).2 a0 b0 ha0 haSupport hm'
    have hbox : (sLocalNonzeroIntegerDiagonal K S m).2 ∈ B := by
      by_contra hnot
      exact hm' (congrFun (sUnitAnnularPartitionCutoff_eq_zero_of_not_mem_box K S Γ a
        (sLocalNonzeroIntegerDiagonal K S m).2 hnot) _)
    have hfinite : (fun v : S => algebraMap K (v.val.adicCompletion K) (m.val : K)) ∈ Cf :=
      ⟨(sLocalNonzeroIntegerDiagonal K S m).2, hbox, rfl⟩
    have hmatch : f m = r • A (r⁻¹ • traceEmbedding K (m.val : K)) := by
      rw [← hAsmul, smul_smul, mul_inv_cancel₀ hrpos.ne', one_smul]
      simp only [A, f, traceEmbedding, ContinuousLinearEquiv.apply_symm_apply, map_mul]
    have hnorm : ‖f m‖ ≤ r * D := by
      rw [hmatch, norm_smul, Real.norm_of_nonneg hrpos.le]
      exact mul_le_mul_of_nonneg_left (hDbound _ harch) hrpos.le
    have hfne : f m ≠ 0 := by
      intro hz
      have hz' : traceEmbedding K (algebraMap (𝓞 K) K den * (m.val : K)) =
          traceEmbedding K 0 := by
        rw [traceEmbedding_zero]
        exact hz
      exact mul_ne_zero (RingOfIntegers.coe_ne_zero_iff.mpr hden)
        (nonzeroSIntegerFieldUnit K S m).ne_zero (traceEmbedding_injective K hz')
    refine ⟨⟨hfne, pow_le_pow_left₀ (norm_nonneg _) hnorm d⟩, ?_⟩
    exact (traceEmbedding_mem_traceIdealLattice K 1).mpr
      ((FractionalIdeal.mem_one_iff (𝓞 K)⁰).mpr (hclear m.val hfinite))
  let j : Function.support (sIntegerAnnularColumn K S Γ a r) → target :=
    fun m => ⟨f m.val, hmem m.val m.property⟩
  have hj : Function.Injective j := by
    intro m n hmn
    exact Subtype.ext (hf (congrArg Subtype.val hmn))
  letI : Finite target := htarget.to_subtype
  have hcard : Nat.card (Function.support (sIntegerAnnularColumn K S Γ a r)) ≤ Nat.card target :=
    Nat.card_le_card_of_injective j hj
  have hcardR : (Nat.card (Function.support (sIntegerAnnularColumn K S Γ a r)) : ℝ) ≤
      (Nat.card target : ℝ) := by exact_mod_cast hcard
  calc
    _ ≤ (Nat.card target : ℝ) := hcardR
    _ ≤ C0 * (r * D) ^ d := hcount _ hpow
    _ = (C0 * D ^ d) * r ^ Module.finrank ℚ K := by rw [mul_pow, ← hd]; ring

/-- In the norm parameter the actual column count is O(N), with the
degree-th-root archimedean scale and the same fixed denominator. -/
theorem exists_sIntegerAnnularColumn_allScale_norm_count_le
    (a : ℝ → ℝ) (a0 b0 : ℝ) (ha0 : 0 < a0)
    (haSupport : tsupport a ⊆ Set.Icc a0 b0) :
    ∃ C : ℝ, 0 < C ∧ ∀ Y : ℝ, 0 < Y →
      (Nat.card (Function.support (sIntegerAnnularColumn K S Γ a
        (Y ^ (Module.finrank ℚ K : ℝ)⁻¹))) : ℝ) ≤ C * Y := by
  obtain ⟨C, hC, hb⟩ := exists_sIntegerAnnularColumn_allScale_count_le K S Γ a a0 b0 ha0 haSupport
  refine ⟨C, hC, fun Y hN => ?_⟩
  have hd : (Module.finrank ℚ K : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K)).ne'
  have hscale : 0 < Y ^ (Module.finrank ℚ K : ℝ)⁻¹ := Real.rpow_pos_of_pos hN _
  have hpower : (Y ^ (Module.finrank ℚ K : ℝ)⁻¹) ^ Module.finrank ℚ K = Y := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le,
      inv_mul_cancel₀ hd, Real.rpow_one]
  simpa only [hpower] using hb _ hscale


/-- An actual nonempty subunit annulus has a fixed positive lower bound.
The constant precedes every norm scale and every element in the support. -/
theorem exists_sIntegerAnnularColumn_norm_lower_bound
    (a : ℝ → ℝ) (a0 b0 : ℝ) (ha0 : 0 < a0)
    (haSupport : tsupport a ⊆ Set.Icc a0 b0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ Y : ℝ, 0 < Y →
      (Function.support (sIntegerAnnularColumn K S Γ a
        (Y ^ (Module.finrank ℚ K : ℝ)⁻¹))).Nonempty → δ ≤ Y := by
  obtain ⟨C, hC, hcount⟩ :=
    exists_sIntegerAnnularColumn_allScale_norm_count_le K S Γ a a0 b0 ha0 haSupport
  refine ⟨C⁻¹, inv_pos.mpr hC, fun Y hY hne => ?_⟩
  have hfinite := finite_support_sIntegerAnnularColumn K S Γ a a0 b0 ha0 haSupport
    (Y ^ (Module.finrank ℚ K : ℝ)⁻¹) (Real.rpow_pos_of_pos hY _).ne'
  have hcard : 1 ≤ Nat.card (Function.support (sIntegerAnnularColumn K S Γ a
      (Y ^ (Module.finrank ℚ K : ℝ)⁻¹))) := (Nat.card_pos_iff.mpr ⟨hne.to_subtype, hfinite⟩)
  have hcardR : (1 : ℝ) ≤ (Nat.card (Function.support (sIntegerAnnularColumn K S Γ a
      (Y ^ (Module.finrank ℚ K : ℝ)⁻¹))) : ℝ) := by exact_mod_cast hcard
  have hproduct : 1 ≤ C * Y := hcardR.trans (hcount Y hY)
  rw [inv_eq_one_div, div_le_iff₀ hC]
  simpa only [mul_comm] using hproduct

/-- Both actual annular columns give the degree-independent O(N²) count.
This includes all positive subunit scales; no quotient by units is taken. -/
theorem exists_sIntegerAnnularColumn_pair_count_le
    (a : ℝ → ℝ) (a0 b0 : ℝ) (ha0 : 0 < a0)
    (haSupport : tsupport a ⊆ Set.Icc a0 b0) :
    ∃ C : ℝ, 0 < C ∧ ∀ Y : ℝ, 0 < Y →
      (Nat.card ((Function.support (sIntegerAnnularColumn K S Γ a
        (Y ^ (Module.finrank ℚ K : ℝ)⁻¹))) ×
        (Function.support (sIntegerAnnularColumn K S Γ a
        (Y ^ (Module.finrank ℚ K : ℝ)⁻¹)))) : ℝ) ≤ C * Y ^ 2 := by
  obtain ⟨C, hC, hcount⟩ :=
    exists_sIntegerAnnularColumn_allScale_norm_count_le K S Γ a a0 b0 ha0 haSupport
  refine ⟨C ^ 2, pow_pos hC _, fun Y hY => ?_⟩
  rw [Nat.card_prod, Nat.cast_mul, ← pow_two]
  calc
    _ ≤ (C * Y) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) (hcount Y hY) 2
    _ = C ^ 2 * Y ^ 2 := mul_pow _ _ _

end ActualColumns

end HeckeGeneral.Analysis.ActualAnnularAllScaleCountDraft
