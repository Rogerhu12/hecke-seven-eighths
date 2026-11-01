import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.ReflectionConductor
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.CoreGeometry
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Actual conductor scales, common dyadic cutoffs and reflected geometry

The complete row norm is bounded by the literal `pairedRows` cutoff.
For recursive remaining ideals, the stronger primitive product budget
`N(u) * N(R) ≤ U^M` is consumed explicitly.  Together with the genuine
conductor/deletion bound, it gives one upper dual scale `U^(M-n+c)` for
every D/H restoration label.  The fixed conductor constant is absorbed
only after a common threshold has been selected.  The more general
separate-budget estimate is retained, with its full extra cost displayed.

The dyadic cutoff is selected before any arithmetic row.  Its retained
scales are exactly `2^j`; their new plain exponents are nonnegative and
realize these scales exactly.  The numerical core lemmas use the actual
short/long relation.  A factor beyond the whole-series threshold produces
no recursive child: its complete reflected series is a terminal.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.ExplicitHeckeFunctionalEquation
open HeckePort.Moments HeckePort.IdealMobiusDivisorSum
open scoped Classical BigOperators nonZeroDivisors

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}

/-- The real width in the induction is the exact exponent used by the
original exhaustive arithmetic row enumeration. -/
theorem Node.paired_row_norm_le (node : Node K ω ψ) {U : ℝ} {u : NonzeroIdeal K}
    (hu : u ∈ pairedRows node.data node.parameters U) :
    idealNorm K u ≤ U ^ node.width := by
  have hrows : u ∈ node.data.rows (U ^ (node.parameters.m + node.parameters.q)) :=
    (Finset.mem_filter.mp hu).1
  exact ((node.data.rows_spec _ _).mp hrows).2

/-- The stronger primitive row cutoff and the remaining-ideal budget
combine to the full width.  Membership in `pairedRows` alone does not
give this statement: its cutoff already uses `m+q`. -/
theorem Node.row_remaining_product_budget (node : Node K ω ψ)
    {U : ℝ} (hU : 0 < U) (u extra : NonzeroIdeal K)
    (hrow : idealNorm K u ≤ U ^ node.parameters.m)
    (hextra : idealNorm K extra ≤ U ^ node.parameters.q) :
    idealNorm K u * idealNorm K extra ≤ U ^ node.width := by
  calc
    _ ≤ U ^ node.parameters.m * U ^ node.parameters.q :=
      mul_le_mul hrow hextra (idealNorm_pos K extra).le
        (Real.rpow_nonneg hU.le _)
    _ = U ^ node.width := (Real.rpow_add hU _ _).symm

/-- Joint conductor/deletion calibration from the complete product
budget.  The possibly large remaining exponent `q` is paid inside the
existing width, not as an unrecorded reflection boundary. -/
theorem actualConductor_remainingProduct_rpow_le
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
    (P : ProbeData K S) (R : RowCharacterInput K S P)
    (node : Node K ω ψ) (ξ : SixthUnitClasses K S)
    (u : ExteriorIdeal K S) (extra : NonzeroIdeal K)
    (hrow : node.data.rowCharacter u.val = completeIdealRowCharacter K S P R ξ u.val)
    {U c : ℝ} (hU : 1 < U)
    (hfixed : uniformReflectionConductorConstant S ψ ≤ U ^ c)
    (hproduct : idealNorm K u.val * idealNorm K extra ≤ U ^ node.width) :
    let χ := node.data.plainBackground * node.data.rowCharacter u.val
    let E := remainingRowDeletionPrimes S u.val extra \ primeSupport (finiteConductor K χ).val
    heckeConductorScale K χ * (Ideal.absNorm (∏ p ∈ E, p) : ℝ) ≤
      U ^ (node.width + c) := by
  dsimp only
  rw [hrow]
  have hU0 : 0 < U := zero_lt_one.trans hU
  have hC : reflectionConductorConstant S node.data.plainBackground ≤ U ^ c :=
    (reflectionConductorConstant_le_uniform S node.data.plainBackground ψ
      node.data.plain_background_spec).trans hfixed
  apply (actualReflectionScale_remainingProduct_le S P R
    node.data.plainBackground ξ u extra).trans
  calc
    _ = reflectionConductorConstant S node.data.plainBackground *
        (idealNorm K u.val * idealNorm K extra) := mul_assoc _ _ _
    _ ≤ U ^ c * U ^ node.width :=
      mul_le_mul hC hproduct (mul_nonneg (idealNorm_pos K u.val).le
        (idealNorm_pos K extra).le) (Real.rpow_nonneg hU0.le c)
    _ = U ^ (node.width + c) := by rw [← Real.rpow_add hU0]; congr 1; ring

private theorem actualConductorScale_one_le (χ : HeckeCharacter K) :
    1 ≤ heckeConductorScale K χ := by
  have hd : (1 : ℝ) ≤ ((NumberField.discr K).natAbs : ℝ) := by
    exact_mod_cast Nat.succ_le_iff.mpr (Int.natAbs_pos.mpr (NumberField.discr_ne_zero K))
  have hc : (1 : ℝ) ≤ (Ideal.absNorm (finiteConductor K χ).val : ℝ) := by
    exact_mod_cast Nat.succ_le_iff.mpr
      (Ideal.absNorm_pos_of_nonZeroDivisors (finiteConductor K χ))
  change 1 ≤ ((NumberField.discr K).natAbs : ℝ) *
    (Ideal.absNorm (finiteConductor K χ).val : ℝ)
  nlinarith

/-- The genuine Euler restoration mass uses this same joint width
budget; the remaining ideal is not charged a second time. -/
theorem actual_remainingProduct_rpow_le
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
    (P : ProbeData K S) (R : RowCharacterInput K S P)
    (node : Node K ω ψ) (ξ : SixthUnitClasses K S)
    (u : ExteriorIdeal K S) (extra : NonzeroIdeal K)
    (hrow : node.data.rowCharacter u.val = completeIdealRowCharacter K S P R ξ u.val)
    {U c : ℝ} (hU : 1 < U)
    (hfixed : uniformReflectionConductorConstant S ψ ≤ U ^ c)
    (hproduct : idealNorm K u.val * idealNorm K extra ≤ U ^ node.width) :
    let χ := node.data.plainBackground * node.data.rowCharacter u.val
    let E := remainingRowDeletionPrimes S u.val extra \ primeSupport (finiteConductor K χ).val
    (Ideal.absNorm (∏ p ∈ E, p) : ℝ) ≤ U ^ (node.width + c) := by
  dsimp only
  have h := actualConductor_remainingProduct_rpow_le S P R node ξ u extra hrow
    hU hfixed hproduct
  have hQ := actualConductorScale_one_le
    (node.data.plainBackground * node.data.rowCharacter u.val)
  have hsmall :
      (Ideal.absNorm (∏ p ∈ remainingRowDeletionPrimes S u.val extra \
        primeSupport (finiteConductor K
          (node.data.plainBackground * node.data.rowCharacter u.val)).val, p) : ℝ) ≤
      heckeConductorScale K (node.data.plainBackground * node.data.rowCharacter u.val) *
        (Ideal.absNorm (∏ p ∈ remainingRowDeletionPrimes S u.val extra \
          primeSupport (finiteConductor K
            (node.data.plainBackground * node.data.rowCharacter u.val)).val, p) : ℝ) := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hQ
      (Nat.cast_nonneg (Ideal.absNorm (∏ p ∈ remainingRowDeletionPrimes S u.val extra \
        primeSupport (finiteConductor K
          (node.data.plainBackground * node.data.rowCharacter u.val)).val, p)))
  exact hsmall.trans h

/-- The terminal and child-geometry consumers use this product-budget
version: only the arbitrarily small absorbed fixed cost `c` remains. -/
theorem actual_reflectedScale_rpow_le_of_row_product
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
    (P : ProbeData K S) (R : RowCharacterInput K S P)
    (node : Node K ω ψ) (ξ : SixthUnitClasses K S)
    (u : ExteriorIdeal K S) (extra : NonzeroIdeal K)
    (hrow : node.data.rowCharacter u.val = completeIdealRowCharacter K S P R ξ u.val)
    {U n c : ℝ} (hU : 1 < U)
    (hfixed : uniformReflectionConductorConstant S ψ ≤ U ^ c)
    (hproduct : idealNorm K u.val * idealNorm K extra ≤ U ^ node.width)
    (D : Finset (Ideal (𝓞 K)))
    (hD : D ⊆ remainingRowDeletionPrimes S u.val extra \
      primeSupport (finiteConductor K
        (node.data.plainBackground * node.data.rowCharacter u.val)).val)
    (H : HeckePort.Moments.NI K) :
    heckeConductorScale K (node.data.plainBackground * node.data.rowCharacter u.val) *
        (Ideal.absNorm (∏ p ∈ D, p) : ℝ) / (U ^ n * inorm H) ≤
      U ^ (node.width - n + c) := by
  have hU0 : 0 < U := zero_lt_one.trans hU
  have hD' : D ⊆ remainingRowDeletionPrimes S u.val extra \
      primeSupport (finiteConductor K (node.data.plainBackground *
        completeIdealRowCharacter K S P R ξ u.val)).val := by
    simpa only [hrow] using hD
  have hscale := actual_reflectedScale_le S P R node.data.plainBackground ξ
    u extra D hD' H (U ^ n) (Real.rpow_pos_of_pos hU0 n)
  have hC : reflectionConductorConstant S node.data.plainBackground ≤ U ^ c :=
    (reflectionConductorConstant_le_uniform S node.data.plainBackground ψ
      node.data.plain_background_spec).trans hfixed
  have hprod : reflectionConductorConstant S node.data.plainBackground *
      idealNorm K u.val * idealNorm K extra ≤ U ^ c * U ^ node.width := by
    rw [mul_assoc]
    exact mul_le_mul hC hproduct (mul_nonneg (idealNorm_pos K u.val).le
      (idealNorm_pos K extra).le) (Real.rpow_nonneg hU0.le c)
  rw [hrow]
  apply hscale.trans
  calc
    _ ≤ (U ^ c * U ^ node.width) / U ^ n :=
      div_le_div_of_nonneg_right hprod (Real.rpow_nonneg hU0.le n)
    _ = U ^ (node.width - n + c) := by
      rw [← Real.rpow_add hU0, ← Real.rpow_sub hU0]
      congr 1
      ring

/-- Actual physical D/H scales in a node.  The source supplies only its
row-character identification and remaining-ideal budget; the conductor
estimate and complete-row norm estimate are proved internally. -/
theorem actual_reflectedScale_rpow_le
    (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
    (P : ProbeData K S) (R : RowCharacterInput K S P)
    (node : Node K ω ψ) (ξ : SixthUnitClasses K S)
    (u : ExteriorIdeal K S) (extra : NonzeroIdeal K)
    (hrow : node.data.rowCharacter u.val = completeIdealRowCharacter K S P R ξ u.val)
    {U n c r : ℝ} (hU : 1 < U)
    (hu : u.val ∈ pairedRows node.data node.parameters U)
    (hfixed : uniformReflectionConductorConstant S ψ ≤ U ^ c)
    (hextra : idealNorm K extra ≤ U ^ r)
    (D : Finset (Ideal (𝓞 K)))
    (hD : D ⊆ remainingRowDeletionPrimes S u.val extra \
      primeSupport (finiteConductor K
        (node.data.plainBackground * node.data.rowCharacter u.val)).val)
    (H : HeckePort.Moments.NI K) :
    heckeConductorScale K (node.data.plainBackground * node.data.rowCharacter u.val) *
        (Ideal.absNorm (∏ p ∈ D, p) : ℝ) / (U ^ n * inorm H) ≤
      U ^ (node.width - n + (c + r)) := by
  have hU0 : 0 < U := zero_lt_one.trans hU
  have hD' : D ⊆ remainingRowDeletionPrimes S u.val extra \
      primeSupport (finiteConductor K (node.data.plainBackground *
        completeIdealRowCharacter K S P R ξ u.val)).val := by
    simpa only [hrow] using hD
  have hscale := actual_reflectedScale_le S P R node.data.plainBackground ξ
    u extra D hD' H (U ^ n) (Real.rpow_pos_of_pos hU0 n)
  have hC : reflectionConductorConstant S node.data.plainBackground ≤ U ^ c :=
    (reflectionConductorConstant_le_uniform S node.data.plainBackground ψ
      node.data.plain_background_spec).trans hfixed
  have hnorm := node.paired_row_norm_le hu
  have hproduct : reflectionConductorConstant S node.data.plainBackground *
      idealNorm K u.val * idealNorm K extra ≤ (U ^ c * U ^ node.width) * U ^ r :=
    mul_le_mul
      (mul_le_mul hC hnorm (idealNorm_pos K u.val).le (Real.rpow_nonneg hU0.le c))
      hextra (idealNorm_pos K extra).le
      (mul_nonneg (Real.rpow_nonneg hU0.le c) (Real.rpow_nonneg hU0.le node.width))
  rw [hrow]
  apply hscale.trans
  calc
    _ ≤ ((U ^ c * U ^ node.width) * U ^ r) / U ^ n :=
      div_le_div_of_nonneg_right hproduct (Real.rpow_nonneg hU0.le n)
    _ = U ^ (node.width - n + (c + r)) := by
      rw [← Real.rpow_add hU0, ← Real.rpow_add hU0, ← Real.rpow_sub hU0]
      congr 1
      ring

/-- Fixed conductor costs and one dyadic rounding factor have a common
threshold, chosen before the node, row and restoration labels. -/
theorem reflection_constant_threshold {C c b : ℝ}
    (hC : 0 < C) (hc : 0 < c) (hb : 0 < b) :
    ∃ U₀ : ℝ, 2 ≤ U₀ ∧ ∀ U : ℝ, U₀ ≤ U → C ≤ U ^ c ∧ 2 ≤ U ^ b := by
  let U₀ : ℝ := max 2 (max (C ^ c⁻¹) ((2 : ℝ) ^ b⁻¹))
  refine ⟨U₀, le_max_left _ _, fun U hU => ?_⟩
  have hCU : C ^ c⁻¹ ≤ U := (le_max_left _ _).trans ((le_max_right _ _).trans hU)
  have h2U : (2 : ℝ) ^ b⁻¹ ≤ U := (le_max_right _ _).trans ((le_max_right _ _).trans hU)
  constructor
  · calc
      C = (C ^ c⁻¹) ^ c := by
        rw [← Real.rpow_mul hC.le, inv_mul_cancel₀ hc.ne', Real.rpow_one]
      _ ≤ U ^ c := Real.rpow_le_rpow (Real.rpow_nonneg hC.le _) hCU hc.le
  · calc
      (2 : ℝ) = ((2 : ℝ) ^ b⁻¹) ^ b := by
        rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
          inv_mul_cancel₀ hb.ne', Real.rpow_one]
      _ ≤ U ^ b := Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num) _) h2U hb.le

/-- One finite dyadic endpoint for an entire reflected row family.  The
rounding loss is exactly the available factor `2 ≤ U^b`. -/
theorem exists_reflection_dyadic_cutoff {U B b : ℝ} (hU : 1 < U)
    (hB : 0 ≤ B) (hround : 2 ≤ U ^ b) :
    ∃ J : ℕ, U ^ B ≤ (2 : ℝ) ^ J ∧ (2 : ℝ) ^ J ≤ U ^ (B + b) := by
  obtain ⟨N, hlo, hhi⟩ := exists_nat_pow_near (Real.one_le_rpow hU.le hB)
    (by norm_num : (1 : ℝ) < 2)
  refine ⟨N + 1, hhi.le, ?_⟩
  rw [pow_succ]
  calc
    (2 : ℝ) ^ N * 2 ≤ U ^ B * U ^ b :=
      mul_le_mul hlo hround (by norm_num) (Real.rpow_nonneg (zero_lt_one.trans hU).le _)
    _ = U ^ (B + b) := (Real.rpow_add (zero_lt_one.trans hU) _ _).symm

/-- The actual real exponent of the retained dyadic scale. -/
def reflectionDyadicExponent (U : ℝ) (j : ℕ) : ℝ :=
  Real.log ((2 : ℝ) ^ j) / Real.log U

theorem reflectionDyadicExponent_nonneg {U : ℝ} (hU : 1 < U) (j : ℕ) :
    0 ≤ reflectionDyadicExponent U j := by
  exact div_nonneg (Real.log_nonneg (one_le_pow₀ (by norm_num))) (Real.log_pos hU).le

/-- This is an exact scale identity for the finite polynomial, not a
change to its row-enumeration exponent or common mask. -/
theorem reflectionDyadicExponent_scale {U : ℝ} (hU : 1 < U) (j : ℕ) :
    U ^ reflectionDyadicExponent U j = (2 : ℝ) ^ j := by
  have hU0 : 0 < U := zero_lt_one.trans hU
  have hlog : Real.log U ≠ 0 := (Real.log_pos hU).ne'
  rw [reflectionDyadicExponent, Real.rpow_def_of_pos hU0]
  have hc : Real.log U * (Real.log ((2 : ℝ) ^ j) / Real.log U) =
      Real.log ((2 : ℝ) ^ j) := by field_simp
  rw [hc, Real.exp_log (pow_pos (by norm_num) _)]

theorem reflectionDyadicExponent_le {U B : ℝ} {J j : ℕ}
    (hU : 1 < U) (hcutoff : (2 : ℝ) ^ J ≤ U ^ B) (hj : j ≤ J) :
    reflectionDyadicExponent U j ≤ B := by
  apply (Real.rpow_le_rpow_left_iff hU).mp
  rw [reflectionDyadicExponent_scale hU]
  exact (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hj).trans hcutoff

/-- The common cutoff's real exponent also retains its lower bound,
as required by the genuine reflected-tail exponent ledger. -/
theorem le_reflectionDyadicExponent {U B : ℝ} {J : ℕ}
    (hU : 1 < U) (hcutoff : U ^ B ≤ (2 : ℝ) ^ J) :
    B ≤ reflectionDyadicExponent U J := by
  apply (Real.rpow_le_rpow_left_iff hU).mp
  rw [reflectionDyadicExponent_scale hU]
  exact hcutoff

/-- `r` includes the remaining ideal and the absorbed fixed conductor
cost. The cutoff is common to all rows and D/H labels. Every retained
plain exponent is nonnegative and fits the same advertised boundary. -/
theorem exists_reflection_dyadic_geometry {U M n r η b : ℝ}
    (hU : 1 < U) (hr : 0 ≤ r) (hη : 0 ≤ η) (hround : 2 ≤ U ^ b) :
    ∃ J : ℕ,
      U ^ (max (M - n + r) 0 + η) ≤ (2 : ℝ) ^ J ∧
      (2 : ℝ) ^ J ≤ U ^ (max (M - n + r) 0 + η + b) ∧
      ∀ j ∈ Finset.range (J + 1),
        0 ≤ reflectionDyadicExponent U j ∧
        U ^ reflectionDyadicExponent U j = (2 : ℝ) ^ j ∧
        reflectionDyadicExponent U j ≤ max (M - n) 0 + (r + η + b) := by
  have hB : 0 ≤ max (M - n + r) 0 + η :=
    add_nonneg (le_max_right _ _) hη
  obtain ⟨J, hlo, hhi⟩ := exists_reflection_dyadic_cutoff hU hB hround
  refine ⟨J, hlo, hhi, fun j hj => ⟨reflectionDyadicExponent_nonneg hU j,
    reflectionDyadicExponent_scale hU j, ?_⟩⟩
  have hmax : max (M - n + r) 0 ≤ max (M - n) 0 + r := by
    apply max_le
    · linarith [le_max_left (M - n) 0]
    · linarith [le_max_right (M - n) 0]
  exact (reflectionDyadicExponent_le hU hhi
    (Nat.le_of_lt_succ (Finset.mem_range.mp hj))).trans (by linarith)

/-- A retained outer-reflection child enters the zero-slot padded core.
The long factor is below the whole-series terminal threshold and is at
least the other factor; both inequalities are necessary. -/
theorem reflection_outer_child_core {M short long nextLength gap boundary padding : ℝ}
    (hgap : 0 ≤ gap) (horder : short ≤ long) (hlong : long ≤ M + gap)
    (hnext : nextLength ≤ max (M - long) 0 + boundary)
    (hbudget : gap + boundary ≤ padding) :
    short + nextLength ≤ M + padding := by
  by_cases hlongM : long ≤ M
  · rw [max_eq_left (by linarith)] at hnext
    linarith
  · rw [max_eq_right (by linarith)] at hnext
    linarith

/-- The ordinary short-factor branch and the quarter comparison share
this actual reflected-length calculation. It also covers a long factor
slightly above `M` in the padded zero-slot core. -/
theorem reflection_comparison_child_length
    {M short long nextLength z padding boundary : ℝ}
    (hz : 0 ≤ z) (hshort : short ≤ M / 4)
    (hcore : short + long + z ≤ M + padding) (hpadding : padding ≤ M / 4)
    (hnext : nextLength ≤ max (M - long) 0 + boundary) :
    short + nextLength + z ≤ 3 * M / 2 - (short + long + z) + 2 * z + boundary := by
  by_cases hlongM : long ≤ M
  · rw [max_eq_left (by linarith)] at hnext
    linarith
  · rw [max_eq_right (by linarith)] at hnext
    linarith

/-- Specialization to the genuine equal-product quarter comparison. -/
theorem reflection_quarter_comparison_length {M A nextLength z padding boundary : ℝ}
    (hz : 0 ≤ z) (hcore : A ≤ M + padding) (hpadding : padding ≤ M / 4)
    (hnext : nextLength ≤ max (M - (A - z - M / 4)) 0 + boundary) :
    M / 4 + nextLength + z ≤ 3 * M / 2 - A + 2 * z + boundary := by
  have h := reflection_comparison_child_length hz (le_refl (M / 4))
    (show M / 4 + (A - z - M / 4) + z ≤ M + padding by linarith)
    hpadding hnext
  linarith

/-- Beyond the long-factor threshold the genuine whole-series bound
uses a small upper dual scale; no same-width child is introduced. -/
theorem reflection_whole_scale_le {U M n r η Y : ℝ} (hU : 1 ≤ U)
    (hscale : Y ≤ U ^ (M - n + r)) (hlong : M + r + η ≤ n) :
    Y ≤ U ^ (-η) :=
  hscale.trans (Real.rpow_le_rpow_of_exponent_le hU (by linarith))

end HeckeSkeleton.Moments.EngineInduction
