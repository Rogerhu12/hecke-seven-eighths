import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstActiveDictionary
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalPoolAllowanceTransport

/-!
# The first saving from the actual original ideal windows

The common lengths and active radical are computed from the literal
first block. Its positive-part allowance is therefore available by
definition. Three individual norm windows supply the active-radical,
opposite-common and extracted-factor lengths required by the ledger.

The direct, main-pool and valuation-error versions derive the moving
length bounds internally. They do not assume the final first-saving
inequality and do not modify any source, row, mask or allocation.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis

variable {K : Type} [Field K] [NumberField K]

private theorem first_logLength_le_of_norm_le
    (Z : ℝ) (hZ : 1 < Z) (I : Ideal (𝓞 K)) (hI : I ≠ 0)
    (x : ℝ) (h : (Ideal.absNorm I : ℝ) ≤ Z ^ x) : idealLogLength Z I ≤ x := by
  apply (Real.rpow_le_rpow_left_iff hZ).mp
  simpa only [rpow_idealLogLength Z hZ I hI] using h

private theorem firstAllowance_max_div (c d R : ℝ) :
    max (3 * c - 5 * d - R) 0 / 6 ≤ firstAllowance c d R := by
  unfold firstAllowance
  by_cases h : 0 ≤ 3 * c - 5 * d - R
  · rw [max_eq_left h, max_eq_left (by linarith : 0 ≤ (3 * c - 5 * d - R) / 6)]
  · have hn : 3 * c - 5 * d - R ≤ 0 := le_of_not_ge h
    rw [max_eq_right hn,
      max_eq_right (by linarith : (3 * c - 5 * d - R) / 6 ≤ 0)]
    norm_num

/-- The first saving is a theorem of original individual ideal norms.
The allowance and every common-support length are computed here. -/
theorem firstSaving_from_original_ideal_windows
    (Z : ℝ) (hZ : 1 < Z) (C D G : Ideal (𝓞 K))
    (hC : C ≠ 0) (hD : D ≠ 0) (hG : G ≠ 0)
    (D₀ w q wo ell stepσ δ : ℝ)
    (hw : 0 ≤ w) (hwo : 0 ≤ wo) (hell : 0 ≤ ell)
    (hσ : 0 ≤ stepσ) (hδ : 0 ≤ δ) (hwσ : w ≤ 7 * stepσ / 3)
    (hactive : (Ideal.absNorm (firstActiveRadical C D) : ℝ) ≤ Z ^ q)
    (hopposite : (Ideal.absNorm D : ℝ) ≤ Z ^ (D₀ + δ))
    (hextracted : (Ideal.absNorm G : ℝ) ≤
      Z ^ (max (D₀ - idealLogLength Z C - 2 * w + wo) 0 + 2 * stepσ)) :
    2 * (idealLogLength Z C + w) / 3 - 3 * stepσ - 5 * δ / 6 ≤
      firstSaving (idealLogLength Z C) D₀ w q wo
        (firstAllowance (idealLogLength Z C) (idealLogLength Z D)
          (idealLogLength Z (firstActiveRadical C D)))
        (idealLogLength Z G) ell := by
  have hc := idealLogLength_nonneg Z hZ C hC
  have hr := idealLogLength_nonneg Z hZ (firstActiveRadical C D) (firstActiveRadical_ne_zero C D)
  have hR := first_logLength_le_of_norm_le Z hZ (firstActiveRadical C D)
    (firstActiveRadical_ne_zero C D) q hactive
  have hd := first_logLength_le_of_norm_le Z hZ D hD (D₀ + δ) hopposite
  have hg := first_logLength_le_of_norm_le Z hZ G hG _ hextracted
  exact firstSaving_lower (idealLogLength Z C) (idealLogLength Z D) D₀ w q
    (idealLogLength Z (firstActiveRadical C D)) wo _ (idealLogLength Z G) ell stepσ δ
    hc hw (hr.trans hR) hwo (firstAllowance_nonneg _ _ _) hσ hδ hR
    (firstAllowance_max_div _ _ _) (by linarith) hg hell hwσ

variable {A : SArithmeticData K}
variable {ι κ : Type*} {I : ι → A.Exterior} {J : κ → A.Exterior}
variable {DE : Ideal (𝓞 K) × Ideal (𝓞 K)}

namespace FirstCommonCharacterBlock

variable (b : FirstCommonCharacterBlock I J DE)

/-- The active norm is the actual quotient in this first transform;
the existing prime-power identity identifies its radical internally. -/
theorem firstSaving_from_original_norms
    (Z : ℝ) (hZ : 1 < Z) (G : A.Exterior)
    (D₀ w q wo ell stepσ δ : ℝ)
    (hw : 0 ≤ w) (hwo : 0 ≤ wo) (hell : 0 ≤ ell)
    (hσ : 0 ≤ stepσ) (hδ : 0 ≤ δ) (hwσ : w ≤ 7 * stepσ / 3)
    (hactive : A.exteriorNorm (firstActiveIdeal b.primes b.leftMultiplicity b.rightMultiplicity) ≤ Z ^ q)
    (hopposite : (Ideal.absNorm DE.2 : ℝ) ≤ Z ^ (D₀ + δ))
    (hextracted : (Ideal.absNorm G.val : ℝ) ≤
      Z ^ (max (D₀ - idealLogLength Z DE.1 - 2 * w + wo) 0 + 2 * stepσ)) :
    2 * (idealLogLength Z DE.1 + w) / 3 - 3 * stepσ - 5 * δ / 6 ≤
      firstSaving (idealLogLength Z DE.1) D₀ w q wo
        (firstAllowance (idealLogLength Z DE.1) (idealLogLength Z DE.2)
          (idealLogLength Z (firstActiveRadical DE.1 DE.2)))
        (idealLogLength Z G.val) ell := by
  have hC : DE.1 ≠ 0 := by
    rw [← b.common_left]
    exact (primePowerProduct b.primes b.leftMultiplicity).property.1
  have hD : DE.2 ≠ 0 := by
    rw [← b.common_right]
    exact (primePowerProduct b.primes b.rightMultiplicity).property.1
  apply firstSaving_from_original_ideal_windows Z hZ DE.1 DE.2 G.val hC hD G.property.1
    D₀ w q wo ell stepσ δ hw hwo hell hσ hδ hwσ _ hopposite hextracted
  simpa only [b.activeNorm_eq] using hactive

/-- The genuine direct entrance has zero moving lengths. Its first
saving requires only the three original norm windows. -/
theorem direct_firstSaving_from_original_norms
    (Z : ℝ) (hZ : 1 < Z) (G : A.Exterior) (D₀ q stepσ δ : ℝ)
    (hσ : 0 ≤ stepσ) (hδ : 0 ≤ δ)
    (hactive : A.exteriorNorm (firstActiveIdeal b.primes b.leftMultiplicity b.rightMultiplicity) ≤ Z ^ q)
    (hopposite : (Ideal.absNorm DE.2 : ℝ) ≤ Z ^ (D₀ + δ))
    (hextracted : (Ideal.absNorm G.val : ℝ) ≤
      Z ^ (max (D₀ - idealLogLength Z DE.1) 0 + 2 * stepσ)) :
    2 * idealLogLength Z DE.1 / 3 - 3 * stepσ - 5 * δ / 6 ≤
      firstSaving (idealLogLength Z DE.1) D₀ 0 q 0
        (firstAllowance (idealLogLength Z DE.1) (idealLogLength Z DE.2)
          (idealLogLength Z (firstActiveRadical DE.1 DE.2)))
        (idealLogLength Z G.val) 0 := by
  simpa only [add_zero, mul_zero, sub_zero] using
    b.firstSaving_from_original_norms Z hZ G D₀ 0 q 0 0 stepσ δ
      le_rfl le_rfl le_rfl hσ hδ (by positivity) hactive hopposite
      (by simpa only [mul_zero, sub_zero, add_zero] using hextracted)

variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}

/-- The main pool length is paid by the original choice
`ell ≤ stepσ / 3`, rather than a new saving hypothesis. -/
theorem main_firstSaving_from_original_norms
    (pool : PowerScaleExteriorPool A bad Z ell eps)
    (G : A.Exterior) (D₀ q stepσ δ : ℝ)
    (hpool : ell ≤ stepσ / 3) (hδ : 0 ≤ δ)
    (hactive : A.exteriorNorm (firstActiveIdeal b.primes b.leftMultiplicity b.rightMultiplicity) ≤ Z ^ q)
    (hopposite : (Ideal.absNorm DE.2 : ℝ) ≤ Z ^ (D₀ + δ))
    (hextracted : (Ideal.absNorm G.val : ℝ) ≤
      Z ^ (max (D₀ - idealLogLength Z DE.1 - 2 * ell + ell) 0 + 2 * stepσ)) :
    2 * (idealLogLength Z DE.1 + ell) / 3 - 3 * stepσ - 5 * δ / 6 ≤
      firstSaving (idealLogLength Z DE.1) D₀ ell q ell
        (firstAllowance (idealLogLength Z DE.1) (idealLogLength Z DE.2)
          (idealLogLength Z (firstActiveRadical DE.1 DE.2)))
        (idealLogLength Z G.val) ell := by
  have hσ : 0 ≤ stepσ := by linarith [pool.exponent_pos]
  exact b.firstSaving_from_original_norms Z pool.base_gt_one G D₀ ell q ell ell stepσ δ
    pool.exponent_pos.le pool.exponent_pos.le pool.exponent_pos.le hσ hδ
    (by linarith) hactive hopposite hextracted

/-- At valuations one, six and seven, both moving lengths use the
literal norm of the retained prime. The pool upper norm window and
`n ≤ 7` prove the ledger's moving-length constraint internally. -/
theorem residual_firstSaving_from_original_norms
    (pool : PowerScaleExteriorPool A bad Z ell eps) (p : pool.primes)
    (n : ℕ) (hn : n ∈ ({1, 6, 7} : Finset ℕ))
    (G : A.Exterior) (D₀ q stepσ δ : ℝ)
    (hpool : ell ≤ stepσ / 3) (hδ : 0 ≤ δ)
    (hactive : A.exteriorNorm (firstActiveIdeal b.primes b.leftMultiplicity b.rightMultiplicity) ≤ Z ^ q)
    (hopposite : (Ideal.absNorm DE.2 : ℝ) ≤ Z ^ (D₀ + δ))
    (hextracted : (Ideal.absNorm G.val : ℝ) ≤
      Z ^ (max (D₀ - idealLogLength Z DE.1 - 2 * ((n : ℝ) * idealLogLength Z p.val.val.asIdeal) +
        (amplifierMovingExponent n : ℝ) * idealLogLength Z p.val.val.asIdeal) 0 + 2 * stepσ)) :
    2 * (idealLogLength Z DE.1 + (n : ℝ) * idealLogLength Z p.val.val.asIdeal) / 3 -
        3 * stepσ - 5 * δ / 6 ≤
      firstSaving (idealLogLength Z DE.1) D₀ ((n : ℝ) * idealLogLength Z p.val.val.asIdeal) q
        ((amplifierMovingExponent n : ℝ) * idealLogLength Z p.val.val.asIdeal)
        (firstAllowance (idealLogLength Z DE.1) (idealLogLength Z DE.2)
          (idealLogLength Z (firstActiveRadical DE.1 DE.2)))
        (idealLogLength Z G.val) ell := by
  have hlen0 := idealLogLength_nonneg Z pool.base_gt_one p.val.val.asIdeal p.val.val.ne_bot
  have hlen := first_logLength_le_of_norm_le Z pool.base_gt_one p.val.val.asIdeal
    p.val.val.ne_bot ell (pool.norm_upper p.val p.property)
  have hn7 : n ≤ 7 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with rfl | rfl | rfl <;> norm_num
  have hn7r : (n : ℝ) ≤ 7 := by exact_mod_cast hn7
  have hw : (n : ℝ) * idealLogLength Z p.val.val.asIdeal ≤ 7 * stepσ / 3 := by
    calc
      _ ≤ 7 * ell := mul_le_mul hn7r hlen hlen0 (by norm_num)
      _ ≤ _ := by linarith
  have hσ : 0 ≤ stepσ := by linarith [pool.exponent_pos]
  exact b.firstSaving_from_original_norms Z pool.base_gt_one G D₀ _ q _ ell stepσ δ
    (mul_nonneg (Nat.cast_nonneg _) hlen0) (mul_nonneg (Nat.cast_nonneg _) hlen0)
    pool.exponent_pos.le hσ hδ hw hactive hopposite hextracted

end FirstCommonCharacterBlock
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.firstSaving_from_original_ideal_windows
#print axioms HeckeSkeleton.Moments.EngineStep.FirstCommonCharacterBlock.direct_firstSaving_from_original_norms
#print axioms HeckeSkeleton.Moments.EngineStep.FirstCommonCharacterBlock.main_firstSaving_from_original_norms
#print axioms HeckeSkeleton.Moments.EngineStep.FirstCommonCharacterBlock.residual_firstSaving_from_original_norms
