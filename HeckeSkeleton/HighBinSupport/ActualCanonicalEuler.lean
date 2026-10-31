import HeckeSkeleton.HighBinSupport.ActualCanonicalData
import HeckeGeneral.Analysis.RowEulerNegativeStrip

/-!
# Euler control for the constructed canonical target

The Euler data and buffer below are the same definitions used by the
canonical detector blocks and norm-form packet. The exceptional factor
is their actual finite rational table. Its estimate uses the computed
five-row Gauss table, with constant 9 and cutoff 2. The regular estimate
holds throughout the negative-w strip and has no imaginary-part bound.

No presentation identity is an input: `targetEuler` is definitionally the
arithmetic construction, and its initial calibration is already proved
from the original four-ideal Fourier series.

AI-assisted: ChatGPT / GPT-6 Astra Pro, 2026-10-31.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HeckeSkeleton.HighBinCanonicalTarget

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.HighBinActualEuler
open scoped Classical

variable (K : Type) [Field K] [NumberField K]
variable (c : TargetContext K)

/-- The full local correction belonging to the canonical target data. -/
def targetEulerFactor
    (Q : Finset (ExteriorPrime K (places K c)))
    (u : FrequencyRow K (places K c)) (p : ExteriorPrime K (places K c))
    (s w z : ℂ) : ℂ :=
  if hp : p ∈ rowExceptionalPrimes K (places K c) Q u then
    finiteEulerRationalValue ((targetEuler K c).exceptionalFactor Q u ⟨p, hp⟩)
      (p.val.asIdeal.absNorm : ℝ) s w z
  else
    localRowCorrection K (places K c) (probeData K c) (targetCharacter K c)
      ((targetEuler K c).rows.character u) p s w z

/-- A single explicit constant for both actual local branches. -/
def targetEulerConstant : ℝ := max 9 (11 / negativeStripEulerMargin)

theorem targetEulerConstant_pos : 0 < targetEulerConstant :=
  lt_of_lt_of_le (by norm_num : (0 : ℝ) < 9) (le_max_left _ _)

/-- The regular branch is uniform over the entire canonical bin range. -/
theorem targetEuler_regular_bound
    (a : ℝ) (ha : 51 / 100 ≤ a) (haB : a ≤ c.family.B)
    (Q : Finset (ExteriorPrime K (places K c)))
    (u : FrequencyRow K (places K c)) (p : ExteriorPrime K (places K c))
    (hp : p ∉ rowExceptionalPrimes K (places K c) Q u)
    (s w z : ℂ) (hs : s.re = a + 16 * targetBuffer K c)
    (hw : w.re = 1 - a - 6 * targetBuffer K c) (hz : z.re = 17 / 50) :
    ‖targetEulerFactor K c Q u p s w z - 1‖ ≤
      (11 / negativeStripEulerMargin) *
        (p.val.asIdeal.absNorm : ℝ) ^ (-1 - 10 * targetBuffer K c) := by
  simpa only [targetEulerFactor, dif_neg hp] using
    localRowCorrection_negativeStrip_bound K (places K c) (probeData K c)
      (targetCharacter K c) ((targetEuler K c).rows.character u) p
      ha (haB.trans c.family.B_upper) (targetBuffer_pos K c).le
      (targetBuffer_small K c) s w z hs hw hz

/-- The exceptional table has its computed constant 9. An exceptional
prime outside the mark set divides the original row ideal. -/
theorem targetEuler_exceptional_bound
    (a : ℝ) (ha : 51 / 100 ≤ a)
    (Q : Finset (ExteriorPrime K (places K c)))
    (u : FrequencyRow K (places K c)) (p : ExteriorPrime K (places K c))
    (hp : p ∈ rowExceptionalPrimes K (places K c) Q u) (hpQ : p ∉ Q)
    (s w z : ℂ) (hs : s.re = a + 16 * targetBuffer K c)
    (hw : w.re = 1 - a - 6 * targetBuffer K c) (hz : z.re = 17 / 50) :
    ‖finiteEulerRationalValue ((targetEuler K c).exceptionalFactor Q u ⟨p, hp⟩)
        (p.val.asIdeal.absNorm : ℝ) s w z - 1‖ ≤
      9 * (p.val.asIdeal.absNorm : ℝ) ^
        (if p.val.asIdeal ∣ u.ideal.val.val then
          -10 * targetBuffer K c else -1 - 10 * targetBuffer K c) := by
  have hmem := exceptional_unmarked_mem_row K (places K c) Q u p hp hpQ
  have hdvd : p.val.asIdeal ∣ u.ideal.val.val :=
    (mem_exteriorSupport_iff K (places K c) u.ideal p).mp hmem
  have h := exceptional_unmarked_dynamic_bound K (places K c)
    (probeData K c) (targetCharacter K c) Q u p hp hpQ
    (by linarith : (1 / 2 : ℝ) ≤ a) (targetBuffer_pos K c).le s w z hs hw hz
  simpa only [targetEuler, if_pos hdvd] using h

/-- The exceptional endpoint chooses constant 9 and cutoff 2 before
the bin, row, mark set and every complex contour coordinate. -/
theorem targetEuler_exceptional_control :
    ∃ C cutoff : ℝ, C = 9 ∧ cutoff = 2 ∧ 0 < C ∧ 1 ≤ cutoff ∧
      ∀ a : ℝ, 51 / 100 ≤ a → a ≤ c.family.B →
      ∀ Q : Finset (ExteriorPrime K (places K c)),
      ∀ u : FrequencyRow K (places K c), ∀ p : ExteriorPrime K (places K c),
      ∀ hp : p ∈ rowExceptionalPrimes K (places K c) Q u,
      p ∉ Q → cutoff ≤ (p.val.asIdeal.absNorm : ℝ) → ∀ s w z : ℂ,
      s.re = a + 16 * targetBuffer K c →
      w.re = 1 - a - 6 * targetBuffer K c → z.re = 17 / 50 →
      ‖finiteEulerRationalValue ((targetEuler K c).exceptionalFactor Q u ⟨p, hp⟩)
          (p.val.asIdeal.absNorm : ℝ) s w z - 1‖ ≤
        C * (p.val.asIdeal.absNorm : ℝ) ^
          (if p.val.asIdeal ∣ u.ideal.val.val then
            -10 * targetBuffer K c else -1 - 10 * targetBuffer K c) := by
  refine ⟨9, 2, rfl, rfl, by norm_num, by norm_num, ?_⟩
  intro a ha _haB Q u p hp hpQ _hcutoff s w z hs hw hz
  exact targetEuler_exceptional_bound K c a ha Q u p hp hpQ s w z hs hw hz

/-- Uniform control of the full constructed factor on the dynamic
contour, including a = 1 and the resulting negative real part of w. -/
theorem targetEuler_factor_bound
    (a : ℝ) (ha : 51 / 100 ≤ a) (haB : a ≤ c.family.B)
    (Q : Finset (ExteriorPrime K (places K c)))
    (u : FrequencyRow K (places K c)) (p : ExteriorPrime K (places K c))
    (hpQ : p ∉ Q) (s w z : ℂ) (hs : s.re = a + 16 * targetBuffer K c)
    (hw : w.re = 1 - a - 6 * targetBuffer K c) (hz : z.re = 17 / 50) :
    ‖targetEulerFactor K c Q u p s w z - 1‖ ≤
      targetEulerConstant * (p.val.asIdeal.absNorm : ℝ) ^
        (if p.val.asIdeal ∣ u.ideal.val.val then
          -10 * targetBuffer K c else -1 - 10 * targetBuffer K c) := by
  let q : ℝ := (p.val.asIdeal.absNorm : ℝ)
  let beta : ℝ := if p.val.asIdeal ∣ u.ideal.val.val then
    -10 * targetBuffer K c else -1 - 10 * targetBuffer K c
  have hpow : 0 ≤ q ^ beta := Real.rpow_nonneg (Nat.cast_nonneg _) _
  by_cases hp : p ∈ rowExceptionalPrimes K (places K c) Q u
  · have htable := targetEuler_exceptional_bound K c a ha Q u p hp hpQ s w z hs hw hz
    have hfactor : ‖targetEulerFactor K c Q u p s w z - 1‖ ≤ 9 * q ^ beta := by
      simpa only [targetEulerFactor, dif_pos hp] using htable
    exact hfactor.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hpow)
  · let Creg : ℝ := 11 / negativeStripEulerMargin
    have hCreg : 0 < Creg := div_pos (by norm_num) negativeStripEulerMargin_pos
    have hregular := targetEuler_regular_bound K c a ha haB Q u p hp s w z hs hw hz
    have hq1 : 1 ≤ q := by
      have hqN : 1 < p.val.asIdeal.absNorm := one_lt_primeIdeal_absNorm K p.val
      exact_mod_cast hqN.le
    have hexponent : -1 - 10 * targetBuffer K c ≤ beta := by
      dsimp only [beta]
      split_ifs <;> linarith
    calc
      ‖targetEulerFactor K c Q u p s w z - 1‖ ≤
          Creg * q ^ (-1 - 10 * targetBuffer K c) := hregular
      _ ≤ Creg * q ^ beta := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hq1 hexponent) hCreg.le
      _ ≤ targetEulerConstant * q ^ beta :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hpow

/-- Initial Euler identification and the full uniform correction bound
belong to one concrete target provider and its fixed positive buffer. -/
theorem targetEuler_full_control :
    TRowEulerInput K (places K c) (probeData K c) (targetCharacter K c)
        (targetEuler K c) ∧
      ∃ C cutoff : ℝ, 0 < C ∧ 1 ≤ cutoff ∧
      ∀ a : ℝ, 51 / 100 ≤ a → a ≤ c.family.B →
      ∀ Q : Finset (ExteriorPrime K (places K c)),
      ∀ u : FrequencyRow K (places K c), ∀ p : ExteriorPrime K (places K c),
      p ∉ Q → cutoff ≤ (p.val.asIdeal.absNorm : ℝ) → ∀ s w z : ℂ,
      s.re = a + 16 * targetBuffer K c →
      w.re = 1 - a - 6 * targetBuffer K c → z.re = 17 / 50 →
      ‖targetEulerFactor K c Q u p s w z - 1‖ ≤
        C * (p.val.asIdeal.absNorm : ℝ) ^
          (if p.val.asIdeal ∣ u.ideal.val.val then
            -10 * targetBuffer K c else -1 - 10 * targetBuffer K c) := by
  refine ⟨targetEuler_input K c, targetEulerConstant, 2,
    targetEulerConstant_pos, by norm_num, ?_⟩
  intro a ha haB Q u p hpQ _hcutoff s w z hs hw hz
  exact targetEuler_factor_bound K c a ha haB Q u p hpQ s w z hs hw hz

end HeckeSkeleton.HighBinCanonicalTarget

#print axioms HeckeSkeleton.HighBinCanonicalTarget.targetEuler_exceptional_control
#print axioms HeckeSkeleton.HighBinCanonicalTarget.targetEuler_factor_bound
#print axioms HeckeSkeleton.HighBinCanonicalTarget.targetEuler_full_control
