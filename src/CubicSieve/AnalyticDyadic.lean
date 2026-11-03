import CubicSieve.AnalyticFactorization
import CubicSieve.ExteriorKernel
import DedekindZetaZeroFree.Analysis.DyadicLengthBounds
import Mathlib.Data.Nat.Log

/-!
Exact dyadic partition of the first and second actual cubic ideal parts.
The original norm cutoff forces the cube scale, without deleting any row.
-/

set_option autoImplicit false
noncomputable section
namespace CubicSieve.AnalyticDyadic

open NumberField IsDedekindDomain
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open CubicSieve.AnalyticFactorization
open DedekindZetaZeroFree.LargeSieve.Vendor
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

theorem one_le_norm (I : ExteriorIdeal K S) : 1 ≤ exteriorNorm K S I := by
  have hn := Ideal.absNorm_pos_of_nonZeroDivisors I.val
  change (1 : ℝ) ≤ (I.val.val.absNorm : ℝ)
  exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn.ne')

theorem first_norm_le (I : ExteriorIdeal K S) :
    exteriorNorm K S (exteriorFirst K S I) ≤ exteriorNorm K S I := by
  rw [exterior_norm_factorization K S I]
  have ha := one_le_norm K S (exteriorFirst K S I)
  have hb := one_le_pow₀ (one_le_norm K S (exteriorSecond K S I)) (n := 2)
  have hc := one_le_pow₀ (one_le_norm K S (exteriorCube K S I)) (n := 3)
  exact (le_mul_of_one_le_right (by linarith) hb).trans
    (le_mul_of_one_le_right (by positivity) hc)

theorem second_norm_le (I : ExteriorIdeal K S) :
    exteriorNorm K S (exteriorSecond K S I) ≤ exteriorNorm K S I := by
  rw [exterior_norm_factorization K S I]
  have ha := one_le_norm K S (exteriorFirst K S I)
  have hb := one_le_norm K S (exteriorSecond K S I)
  have hc := one_le_pow₀ (one_le_norm K S (exteriorCube K S I)) (n := 3)
  exact (le_self_pow₀ hb (by decide : (2 : ℕ) ≠ 0)).trans
    ((le_mul_of_one_le_left (by positivity) ha).trans
      (le_mul_of_one_le_right (by positivity) hc))

def normBin (I : ExteriorIdeal K S) : ℕ := Nat.log 2 I.val.val.absNorm

theorem normBin_bounds (I : ExteriorIdeal K S) :
    (2 : ℝ) ^ normBin K S I ≤ exteriorNorm K S I ∧
      exteriorNorm K S I ≤ 2 * (2 : ℝ) ^ normBin K S I := by
  have hn := Ideal.absNorm_pos_of_nonZeroDivisors I.val
  change (2 : ℝ) ^ Nat.log 2 I.val.val.absNorm ≤ (I.val.val.absNorm : ℝ) ∧
    (I.val.val.absNorm : ℝ) ≤ 2 * (2 : ℝ) ^ Nat.log 2 I.val.val.absNorm
  constructor
  · exact_mod_cast Nat.pow_log_le_self 2 hn.ne'
  · have hh := Nat.lt_pow_succ_log_self (by decide : 1 < 2) I.val.val.absNorm
    have hh' : (I.val.val.absNorm : ℝ) < (2 : ℝ) ^ (Nat.log 2 I.val.val.absNorm + 1) := by
      exact_mod_cast hh
    rw [pow_succ] at hh'
    linarith

theorem normBin_mem_range (I : ExteriorIdeal K S) (M : ℝ)
    (hI : exteriorNorm K S I ≤ M) : normBin K S I ∈ Finset.range (dyadicLength M + 1) := by
  have hc : (I.val.val.absNorm : ℝ) ≤ (2 : ℝ) ^ dyadicLength M := hI.trans (dyadicLength_cover M)
  have hn : I.val.val.absNorm ≤ 2 ^ dyadicLength M := by exact_mod_cast hc
  have hlog := Nat.log_mono_right (b := 2) hn
  rw [Nat.log_pow (by decide : 1 < 2)] at hlog
  exact Finset.mem_range.mpr (by change Nat.log 2 I.val.val.absNorm < _; omega)

def block (R : Finset (ExteriorIdeal K S)) (i j : ℕ) : Finset (ExteriorIdeal K S) :=
  R.filter (fun I => normBin K S (exteriorFirst K S I) = i ∧
    normBin K S (exteriorSecond K S I) = j)

theorem block_bounds (R : Finset (ExteriorIdeal K S)) (i j : ℕ)
    (I : ExteriorIdeal K S) (hI : I ∈ block K S R i j) :
    (2 : ℝ) ^ i ≤ exteriorNorm K S (exteriorFirst K S I) ∧
    exteriorNorm K S (exteriorFirst K S I) ≤ 2 * (2 : ℝ) ^ i ∧
    (2 : ℝ) ^ j ≤ exteriorNorm K S (exteriorSecond K S I) ∧
    exteriorNorm K S (exteriorSecond K S I) ≤ 2 * (2 : ℝ) ^ j := by
  obtain ⟨_, hi, hj⟩ := Finset.mem_filter.mp hI
  have hA := normBin_bounds K S (exteriorFirst K S I)
  have hB := normBin_bounds K S (exteriorSecond K S I)
  rw [hi] at hA
  rw [hj] at hB
  exact ⟨hA.1, hA.2, hB.1, hB.2⟩

/-- Each row belongs to exactly one original two-part norm block. -/
theorem energy_partition (D : ThetaArithmeticData K S)
    (R T : Finset (ExteriorIdeal K S)) (M : ℝ)
    (hR : ∀ I ∈ R, exteriorNorm K S I ≤ M) (z : ExteriorIdeal K S → ℂ) :
    (∑ i ∈ Finset.range (dyadicLength M + 1),
      ∑ j ∈ Finset.range (dyadicLength M + 1),
        ExteriorKernel.energy K S D 2 (block K S R i j) T z) =
      ExteriorKernel.energy K S D 2 R T z := by
  have hmap : ∀ I ∈ R,
      (normBin K S (exteriorFirst K S I), normBin K S (exteriorSecond K S I)) ∈
        (Finset.range (dyadicLength M + 1)).product (Finset.range (dyadicLength M + 1)) := by
    intro I hI
    exact Finset.mem_product.mpr
      ⟨normBin_mem_range K S _ M ((first_norm_le K S I).trans (hR I hI)),
        normBin_mem_range K S _ M ((second_norm_le K S I).trans (hR I hI))⟩
  have hh := Finset.sum_fiberwise_of_maps_to hmap
    (fun I => ‖ExteriorKernel.rowSum K S D 2 T z I‖ ^ 2)
  have hprod := Finset.sum_product (Finset.range (dyadicLength M + 1))
    (Finset.range (dyadicLength M + 1))
    (fun p : ℕ × ℕ => ∑ I ∈ R.filter (fun I =>
      (normBin K S (exteriorFirst K S I), normBin K S (exteriorSecond K S I)) = p),
      ‖ExteriorKernel.rowSum K S D 2 T z I‖ ^ 2)
  simpa only [Prod.mk.injEq, block, ExteriorKernel.energy] using hprod.symm.trans hh

/-- The cube factor's norm is forced by the true lower bounds of both residual parts. -/
theorem cube_norm_le (I : ExteriorIdeal K S) (M X Y : ℝ)
    (hX : 0 < X) (hY : 0 < Y)
    (hfirst : X ≤ exteriorNorm K S (exteriorFirst K S I))
    (hsecond : Y ≤ exteriorNorm K S (exteriorSecond K S I))
    (hnorm : exteriorNorm K S I ≤ M) :
    exteriorNorm K S (exteriorCube K S I) ≤ (M / (X * Y ^ 2)) ^ (1 / 3 : ℝ) := by
  have hC := one_le_norm K S (exteriorCube K S I)
  have hAB : X * Y ^ 2 ≤ exteriorNorm K S (exteriorFirst K S I) *
      exteriorNorm K S (exteriorSecond K S I) ^ 2 :=
    mul_le_mul hfirst (pow_le_pow_left₀ hY.le hsecond 2) (sq_nonneg _)
      (by have ha := one_le_norm K S (exteriorFirst K S I); linarith)
  have hprod := mul_le_mul_of_nonneg_right hAB
    (pow_nonneg (show 0 ≤ exteriorNorm K S (exteriorCube K S I) by linarith) 3)
  have htotal := exterior_norm_factorization K S I
  have hle : (exteriorNorm K S (exteriorCube K S I)) ^ 3 ≤ M / (X * Y ^ 2) := by
    apply (le_div_iff₀ (mul_pos hX (sq_pos_of_pos hY))).mpr
    nlinarith [hprod, hnorm]
  have hquot : 0 ≤ M / (X * Y ^ 2) := (pow_nonneg (by linarith) 3).trans hle
  apply le_of_pow_le_pow_left₀ (by decide : (3 : ℕ) ≠ 0) (Real.rpow_nonneg hquot _)
  have hr : ((M / (X * Y ^ 2)) ^ (1 / 3 : ℝ)) ^ 3 = M / (X * Y ^ 2) := by
    simpa only [one_div, Nat.cast_ofNat] using Real.rpow_inv_natCast_pow hquot
      (by decide : (3 : ℕ) ≠ 0)
  rw [hr]
  exact hle

end CubicSieve.AnalyticDyadic
