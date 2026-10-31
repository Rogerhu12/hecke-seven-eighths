import NonzeroLatticeAllScaleCount
import ActualCompactDivisorReduction

/-!
UNCOMPILED candidate. Counts the actual columns m with d*m in the annular
support, uniformly in a compactly normalized divisor. The effective norm
scale is Y/q_d, rather than Y. One original-subgroup representative supplies
both compact shape and the fixed clearing denominator. All associates remain.
-/

noncomputable section

namespace HeckeGeneral.Analysis.ActualDivisorAnnularCountDraft

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic
open NonzeroLatticeAllScaleCountDraft ActualGramFixedDenominatorDraft
open scoped Classical nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (Γ : Subgroup (S.unit K)) [Γ.FiniteIndex]
local notation "V" => mixedEmbedding.euclidean.mixedSpace K
local notation "G" => sLocalMultiplicativeGroup K S
local notation "NZ" => NonzeroRingElements (S.integer K)
local notation "H" => finiteIndexSUnitBoxWidth K S Γ

theorem exists_compact_divisor_annular_radius_count
    (a : ℝ → ℝ) (a₀ b₀ : ℝ) (ha₀ : 0 < a₀)
    (ha : tsupport a ⊆ Set.Icc a₀ b₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ d : NZ,
      normalizedDivisorLocalPoint K S d ∈ sUnitCompactRepresentativeSet K S Γ →
      ∀ r : ℝ, 0 < r →
        (Nat.card (Function.support (fun m : NZ =>
          sIntegerAnnularColumn K S Γ a r (sIntegerNonzeroMul K S d m))) : ℝ) ≤
          C * (r ^ Module.finrank ℚ K / (sIntegerElementNorm K S d).val) := by
  let den : 𝓞 K := (finiteSIntegerDenominator K S) ^ H
  have hden : den ≠ 0 := pow_ne_zero _ (finiteSIntegerDenominator_ne_zero K S)
  let L := traceIdealLattice K (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
  let A : G × V → V := fun p => (traceToMixed K).symm
    (mixedEmbedding K (den : K) * ((p.1.1⁻¹).val * traceToMixed K p.2))
  have hA : Continuous A := by dsimp only [A]; fun_prop
  have hAsmul (y : G) (r : ℝ) (z : V) : A (y, r • z) = r • A (y, z) := by
    simp only [A, map_smul, mul_smul_comm]
  let shape := sUnitCompactRepresentativeSet K S Γ
  let enclosure := sUnitAnnularPartitionEnclosure K S Γ a₀ b₀
  have hcompact : IsCompact (A '' (shape ×ˢ enclosure)) :=
    ((isCompact_sUnitCompactRepresentativeSet K S Γ).prod
      (isCompact_sUnitAnnularPartitionEnclosure K S Γ a₀ b₀ ha₀)).image hA
  obtain ⟨R, hR⟩ := hcompact.isBounded.subset_closedBall (0 : V)
  let B : ℝ := max 1 R
  have hB : 0 < B := zero_lt_one.trans_le (le_max_left _ _)
  have hAbound (y : G) (hy : y ∈ shape) (z : V) (hz : z ∈ enclosure) :
      ‖A (y, z)‖ ≤ B := by
    have hb := hR (Set.mem_image_of_mem A (show (y, z) ∈ shape ×ˢ enclosure from ⟨hy, hz⟩))
    have hb' : ‖A (y, z)‖ ≤ R := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hb
    exact hb'.trans (le_max_right _ _)
  obtain ⟨C₀, hC₀, hcount⟩ := exists_nonzero_lattice_norm_power_count_le L
  let n := Module.finrank ℝ V
  have hn : n = Module.finrank ℚ K := mixedEmbedding.euclidean.finrank K
  refine ⟨C₀ * B ^ n, mul_pos hC₀ (pow_pos hB _), ?_⟩
  intro d hd r hr
  let y := normalizedDivisorLocalPoint K S d
  let ell : ℝ := (sIntegerElementNorm K S d).val ^ (Module.finrank ℚ K : ℝ)⁻¹
  have hell : 0 < ell := Real.rpow_pos_of_pos (sIntegerElementNorm K S d).property _
  have hellpow : ell ^ Module.finrank ℚ K = (sIntegerElementNorm K S d).val :=
    Real.rpow_inv_natCast_pow (sIntegerElementNorm K S d).property.le Module.finrank_pos.ne'
  have hbox : (sLocalNonzeroIntegerDiagonal K S d).2 ∈ finiteLocalValuationBox K S H := by
    obtain ⟨p, hp⟩ := hd
    rw [← normalizedDivisorLocalPoint_finite K S d, ← hp]
    exact p.2.property
  let f : NZ → V := fun m => traceEmbedding K ((den : K) * (m.val : K))
  have hf : Function.Injective f := by
    intro m m' he
    have he' := mul_left_cancel₀ (RingOfIntegers.coe_ne_zero_iff.mpr hden)
      (traceEmbedding_injective K he)
    exact Subtype.ext (Subtype.ext he')
  let target : Set V :=
    {x | x ≠ 0 ∧ ‖x‖ ^ n ≤ ((r / ell) * B) ^ n} ∩ (L : Set V)
  have htarget : target.Finite := finite_nonzero_lattice_norm_power_sublevel L _
  have hmem (m : NZ) (hm : sIntegerAnnularColumn K S Γ a r
      (sIntegerNonzeroMul K S d m) ≠ 0) : f m ∈ target := by
    let dm := sIntegerNonzeroMul K S d m
    have harch := support_sUnitAnnularPartitionCutoff_subset_enclosure K S Γ a
      (sLocalNonzeroIntegerDiagonal K S dm).2 a₀ b₀ ha₀ ha hm
    have hdm : (sLocalNonzeroIntegerDiagonal K S dm).2 ∈ finiteLocalValuationBox K S H := by
      by_contra hnot
      exact hm (congrFun (sUnitAnnularPartitionCutoff_eq_zero_of_not_mem_box
        K S Γ a _ hnot) _)
    obtain ⟨z, hz⟩ := exactSDenominator_pow_clears_divisor_quotient K S H d m hbox hdm
    have harchUnit : y.1⁻¹ * (sLocalNonzeroIntegerDiagonal K S dm).1 =
        (sLocalNormSection K S (sIntegerElementNorm K S d)).1 *
          (sLocalNonzeroIntegerDiagonal K S m).1 := by
      dsimp only [y, normalizedDivisorLocalPoint, dm]
      rw [sLocalNonzeroIntegerDiagonal_nonzeroMul]
      change ((sLocalNormSection K S (sIntegerElementNorm K S d)).1⁻¹ *
        (sLocalNonzeroIntegerDiagonal K S d).1)⁻¹ *
          ((sLocalNonzeroIntegerDiagonal K S d).1 *
            (sLocalNonzeroIntegerDiagonal K S m).1) = _
      rw [mul_inv_rev, inv_inv, mul_comm ((sLocalNonzeroIntegerDiagonal K S d).1)⁻¹,
        mul_assoc, inv_mul_cancel_left]
    have harchVal : (y.1⁻¹).val * mixedEmbedding K (dm.val : K) =
        ell • mixedEmbedding K (m.val : K) := by
      change (y.1⁻¹ * (sLocalNonzeroIntegerDiagonal K S dm).1).val = _
      rw [harchUnit]
      exact (Algebra.smul_def ell (mixedEmbedding K (m.val : K))).symm
    have hAraw : A (y, traceEmbedding K (dm.val : K)) = ell • f m := by
      simp only [A, traceEmbedding, ContinuousLinearEquiv.apply_symm_apply]
      rw [harchVal, mul_smul_comm, map_smul]
      simp only [f, traceEmbedding, map_mul]
    have hmatch : f m = (r / ell) • A (y, r⁻¹ • traceEmbedding K (dm.val : K)) := by
      rw [hAsmul, hAraw, smul_smul, smul_smul]
      have hscalar : ((r / ell) * r⁻¹) * ell = 1 := by field_simp [hr.ne', hell.ne']
      rw [hscalar, one_smul]
    have hnorm : ‖f m‖ ≤ (r / ell) * B := by
      rw [hmatch, norm_smul, Real.norm_of_nonneg (div_pos hr hell).le]
      exact mul_le_mul_of_nonneg_left (hAbound y hd _ harch) (div_pos hr hell).le
    have hne : f m ≠ 0 := by
      intro he
      have he' : traceEmbedding K (algebraMap (𝓞 K) K den * (m.val : K)) =
          traceEmbedding K 0 := by
        rw [traceEmbedding_zero]
        exact he
      exact mul_ne_zero (RingOfIntegers.coe_ne_zero_iff.mpr hden)
        (nonzeroSIntegerFieldUnit K S m).ne_zero (traceEmbedding_injective K he')
    refine ⟨⟨hne, pow_le_pow_left₀ (norm_nonneg _) hnorm n⟩, ?_⟩
    apply (traceEmbedding_mem_traceIdealLattice K 1).mpr
    apply (FractionalIdeal.mem_one_iff (𝓞 K)⁰).mpr
    exact ⟨z, (congrArg (fun w : S.integer K => (w : K)) hz).symm⟩
  let j : Function.support (fun m : NZ =>
      sIntegerAnnularColumn K S Γ a r (sIntegerNonzeroMul K S d m)) → target :=
    fun m => ⟨f m.val, hmem m.val m.property⟩
  have hj : Function.Injective j := by
    intro m m' he
    exact Subtype.ext (hf (congrArg Subtype.val he))
  letI : Finite target := htarget.to_subtype
  have hcard := Nat.card_le_card_of_injective j hj
  have hcardR : (Nat.card (Function.support (fun m : NZ =>
      sIntegerAnnularColumn K S Γ a r (sIntegerNonzeroMul K S d m))) : ℝ) ≤
      (Nat.card target : ℝ) := by exact_mod_cast hcard
  calc
    _ ≤ (Nat.card target : ℝ) := hcardR
    _ ≤ C₀ * ((r / ell) * B) ^ n := hcount _ (pow_pos (mul_pos (div_pos hr hell) hB) _)
    _ = (C₀ * B ^ n) * (r ^ Module.finrank ℚ K / (sIntegerElementNorm K S d).val) := by
      rw [mul_pow, div_pow, hn, hellpow]
      ring

/-- Every divisor has one subgroup representative, chosen before Y,
whose actual divided columns have O(Y/q_d) elements at every Y > 0. -/
theorem exists_subgroup_divisor_annular_norm_count
    (a : ℝ → ℝ) (a₀ b₀ : ℝ) (ha₀ : 0 < a₀)
    (ha : tsupport a ⊆ Set.Icc a₀ b₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ d : NZ, ∃ u : Γ, ∀ Y : ℝ, 0 < Y →
      (Nat.card (Function.support (fun m : NZ => sIntegerAnnularColumn K S Γ a
        (Y ^ (Module.finrank ℚ K : ℝ)⁻¹)
        (sIntegerNonzeroMul K S (sIntegerOrbitTranslate K S Γ u d) m))) : ℝ) ≤
        C * (Y / (sIntegerElementNorm K S d).val) := by
  obtain ⟨C, hC, hb⟩ := exists_compact_divisor_annular_radius_count K S Γ a a₀ b₀ ha₀ ha
  refine ⟨C, hC, fun d => ?_⟩
  obtain ⟨u, hu, _⟩ := exists_compact_divisor_with_fixed_denominator K S Γ d
  refine ⟨u, fun Y hY => ?_⟩
  have h := hb (sIntegerOrbitTranslate K S Γ u d) hu
    (Y ^ (Module.finrank ℚ K : ℝ)⁻¹) (Real.rpow_pos_of_pos hY _)
  rw [Real.rpow_inv_natCast_pow hY.le Module.finrank_pos.ne',
    elementNorm_subgroup_translate] at h
  exact h

end HeckeGeneral.Analysis.ActualDivisorAnnularCountDraft
