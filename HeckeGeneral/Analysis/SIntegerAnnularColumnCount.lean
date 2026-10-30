import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.SetTheory.Cardinal.Finite
import HeckeGeneral.Analysis.SIntegerAnnularColumnFinite

/-!
Exact-dimensional lattice counting. This is the
quantitative input for denominator-cleared annular columns: the exponent
is the actual real dimension, without a Schwartz inverse-power loss.
-/

noncomputable section

namespace HeckeGeneral.Analysis

open MeasureTheory Filter Set
open scoped Topology Classical

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E]
variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

private theorem finite_lattice_norm_power_sublevel (c : ℝ) (hc : 1 ≤ c) :
    Set.Finite ({x : E | ‖x‖ ^ Module.finrank ℝ E ≤ c} ∩ (L : Set E)) := by
  have hd : Module.finrank ℝ E ≠ 0 := (Module.finrank_pos (R := ℝ) (M := E)).ne'
  have hbound : {x : E | ‖x‖ ^ Module.finrank ℝ E ≤ c} ⊆ Metric.closedBall 0 c := by
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right]
    by_cases hnorm : ‖x‖ ≤ 1
    · exact hnorm.trans hc
    · exact (le_self_pow₀ (le_of_not_ge hnorm) hd).trans hx
  have hclosed : IsClosed (L : Set E) :=
    @AddSubgroup.isClosed_of_discreteTopology _ _ _ _ _ L.toAddSubgroup
      (inferInstanceAs (DiscreteTopology L))
  exact Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete
    (Metric.isBounded_closedBall.subset hbound) hclosed

/-- The exact real-dimensional lattice count, uniform for every c ≥ 1.
The constant is constructed from the proved covolume asymptotic and one
finite threshold count; no cardinality bound is a hypothesis. -/
theorem exists_lattice_norm_power_count_le :
    ∃ C : ℝ, 0 < C ∧ ∀ c : ℝ, 1 ≤ c →
      (Nat.card ↥(({x : E | ‖x‖ ^ Module.finrank ℝ E ≤ c} : Set E) ∩ (L : Set E)) : ℝ) ≤ C * c := by
  let d := Module.finrank ℝ E
  have hd : d ≠ 0 := (Module.finrank_pos (R := ℝ) (M := E)).ne'
  have hunit : {x : E | x ∈ (Set.univ : Set E) ∧ ‖x‖ ^ d ≤ 1} =
      Metric.closedBall 0 1 := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_univ, true_and, Metric.mem_closedBall,
      dist_zero_right, pow_le_one_iff_of_nonneg (norm_nonneg x) hd]
  have hlim := ZLattice.covolume.tendsto_card_le_div' L
    (X := Set.univ) (F := fun x : E => ‖x‖ ^ d)
    (fun _ _ _ _ => Set.mem_univ _)
    (fun x r hr => by simp only [norm_smul, Real.norm_of_nonneg hr, mul_pow]; rfl)
    (by rw [hunit]; exact Metric.isBounded_closedBall)
    (by rw [hunit]; exact measurableSet_closedBall)
    (by rw [hunit, frontier_closedBall _ one_ne_zero]
        exact Measure.addHaar_sphere volume (0 : E) 1)
  let ell : ℝ := volume.real (Metric.closedBall (0 : E) 1) / ZLattice.covolume L
  have hlim' : Tendsto (fun c : ℝ =>
      (Nat.card ↥(({x : E | ‖x‖ ^ d ≤ c} : Set E) ∩ (L : Set E)) : ℝ) / c)
      atTop (𝓝 ell) := by
    rw [hunit] at hlim
    simpa only [Set.mem_univ, true_and] using hlim
  have hell : ell < |ell| + 1 := by linarith [le_abs_self ell]
  have hev : ∀ᶠ c : ℝ in atTop,
      (Nat.card ↥(({x : E | ‖x‖ ^ d ≤ c} : Set E) ∩ (L : Set E)) : ℝ) / c < |ell| + 1 :=
    hlim'.eventually (isOpen_Iio.mem_nhds hell)
  obtain ⟨T, hT⟩ := eventually_atTop.mp hev
  let c0 : ℝ := max 1 T
  have hc0 : 1 ≤ c0 := le_max_left _ _
  let b : ℝ := Nat.card ↥(({x : E | ‖x‖ ^ d ≤ c0} : Set E) ∩ (L : Set E))
  let C : ℝ := |ell| + 1 + b
  have hb : 0 ≤ b := Nat.cast_nonneg _
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, fun c hc => ?_⟩
  change (Nat.card ↥(({x : E | ‖x‖ ^ d ≤ c} : Set E) ∩ (L : Set E)) : ℝ) ≤ C * c
  by_cases hlarge : c0 ≤ c
  · have hcpos : 0 < c := lt_of_lt_of_le zero_lt_one hc
    have hratio := hT c ((le_max_right 1 T).trans hlarge)
    have hcount := (div_lt_iff₀ hcpos).mp hratio
    exact hcount.le.trans (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) hcpos.le)
  · have hmono : Nat.card ↥(({x : E | ‖x‖ ^ d ≤ c} : Set E) ∩ (L : Set E)) ≤
        Nat.card ↥(({x : E | ‖x‖ ^ d ≤ c0} : Set E) ∩ (L : Set E)) :=
      Nat.card_mono (finite_lattice_norm_power_sublevel L c0 hc0)
        (fun x hx => ⟨hx.1.trans (le_of_not_ge hlarge), hx.2⟩)
    have hcount : (Nat.card ↥(({x : E | ‖x‖ ^ d ≤ c} : Set E) ∩ (L : Set E)) : ℝ) ≤ b := by
      dsimp only [b]
      exact_mod_cast hmono
    exact hcount.trans ((show b ≤ C by dsimp [C]; linarith [abs_nonneg ell]).trans
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hc hC.le))

section ActualColumns

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic
open scoped nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]

local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "N" => NonzeroRingElements (S.integer K)
local notation "Z" => SFiniteLocalGroup K S

/-- A linear count for the actual element-indexed annular column. The
clearing denominator, lattice and constant are chosen before the moving
scale. Torsion translates and all other associates remain actual indices. -/
theorem exists_sIntegerAnnularColumn_count_le
    (a : ℝ → ℝ) (a0 b0 : ℝ) (ha0 : 0 < a0)
    (haSupport : tsupport a ⊆ Set.Icc a0 b0) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 1 ≤ r →
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
  obtain ⟨C0, hC0, hcount⟩ := exists_lattice_norm_power_count_le L
  let d := Module.finrank ℝ V
  have hd : d = Module.finrank ℚ K := mixedEmbedding.euclidean.finrank K
  refine ⟨C0 * D ^ d, by positivity, fun r hr => ?_⟩
  have hrpos : 0 < r := zero_lt_one.trans_le hr
  have hrd : 1 ≤ r * D := by nlinarith
  have hpow : 1 ≤ (r * D) ^ d := one_le_pow₀ hrd
  let target : Set V := {x : V | ‖x‖ ^ d ≤ (r * D) ^ d} ∩ (L : Set V)
  have htarget : target.Finite := finite_lattice_norm_power_sublevel L _ hpow
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
    refine ⟨pow_le_pow_left₀ (norm_nonneg _) hnorm d, ?_⟩
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
theorem exists_sIntegerAnnularColumn_norm_count_le
    (a : ℝ → ℝ) (a0 b0 : ℝ) (ha0 : 0 < a0)
    (haSupport : tsupport a ⊆ Set.Icc a0 b0) :
    ∃ C : ℝ, 0 < C ∧ ∀ Y : ℝ, 1 ≤ Y →
      (Nat.card (Function.support (sIntegerAnnularColumn K S Γ a
        (Y ^ (Module.finrank ℚ K : ℝ)⁻¹))) : ℝ) ≤ C * Y := by
  obtain ⟨C, hC, hb⟩ := exists_sIntegerAnnularColumn_count_le K S Γ a a0 b0 ha0 haSupport
  refine ⟨C, hC, fun Y hN => ?_⟩
  have hd : (Module.finrank ℚ K : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K)).ne'
  have hscale : 1 ≤ Y ^ (Module.finrank ℚ K : ℝ)⁻¹ :=
    Real.one_le_rpow hN (inv_nonneg.mpr (Nat.cast_nonneg _))
  have hpower : (Y ^ (Module.finrank ℚ K : ℝ)⁻¹) ^ Module.finrank ℚ K = Y := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (zero_le_one.trans hN),
      inv_mul_cancel₀ hd, Real.rpow_one]
  simpa only [hpower] using hb _ hscale

end ActualColumns

end HeckeGeneral.Analysis
