import HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalProviderMarks
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalProviderHilbert
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalProviderCubeMass
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.TerminalProviderShort
import HeckeSkeleton.Moments.MOM_INV_INDUCTION.ProviderNodes
import HeckeSkeleton.Moments.MOM_INV_STEP.CoefficientBounds

/-!
# The original short-cube marks and their actual divisor mass

Slots assigned to the extracted cube keep their original prime
coefficients. The remaining slots retain their original lengths and
windows, with precisely the already assigned primes removed. Weighted
Minkowski is applied after this exact priority identity. Its arithmetic
mass is the actual divisor count of the cube, divided by its norm.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_INDUCTION

open NumberField IsDedekindDomain UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOM_BASE HeckeSkeleton.Moments.MOMInvStep
open HeckeSkeleton.Moments.MOM_INV_STEP
open HeckePort.IdealMobiusDivisorSum DedekindZetaZeroFree.LargeSieve
open scoped Classical BigOperators nonZeroDivisors

namespace ProviderNodes.MarkConditions

variable {K : Type} [Field K] [NumberField K]
variable {S : Finset (HeightOneSpectrum (𝓞 K))} {σ : Type*}

/-- Filtering a list by the exact cube priority preserves every
original arithmetic condition and individual prime window. -/
theorem residual_lists {slotCap : ℕ} {Z z lo hi : ℝ}
    {I : Finset σ} {L : σ → Finset (Ideal (𝓞 K))}
    {a : σ → Ideal (𝓞 K) → ℂ} {lengths : σ → ℝ}
    (h : MarkConditions K S slotCap Z z lo hi I L a lengths)
    (H : Ideal (𝓞 K)) :
    MarkConditions K S slotCap Z z lo hi I (residualDivisorLists H L) a lengths where
  card_le := h.card_le
  length_nonneg := h.length_nonneg
  total_length := h.total_length
  prime := fun i hi p hp => h.prime i hi p (Finset.mem_filter.mp hp).1
  exterior := fun i hi p hp => h.exterior i hi p (Finset.mem_filter.mp hp).1
  norm_window := fun i hi p hp => h.norm_window i hi p (Finset.mem_filter.mp hp).1
  weights_le := fun i hi p hp => h.weights_le i hi p (Finset.mem_filter.mp hp).1
  disjoint := fun i hi j hj hij => (h.disjoint i hi j hj hij).mono
    (Finset.filter_subset _ _) (Finset.filter_subset _ _)

end ProviderNodes.MarkConditions

namespace TerminalCubePriority

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)
local notation "Ext" => ExteriorIdeal K S

/-- Every original cube-priority summand is bounded in the same row
Hilbert space. The number of subsets depends only on the original slot
capacity, and the divisor weight remains attached to the actual cube. -/
theorem completed_energy {σ κ : Type*} [DecidableEq σ]
    (slotCap : ℕ) (θ : HeckeCharacter K) (rows : Finset κ)
    (row : κ → S.integer K) (r : Ext)
    (I : Finset σ) (L : σ → Finset (Ideal (𝓞 K)))
    (a : σ → Ideal (𝓞 K) → ℂ) (H : Ideal (𝓞 K))
    (hH : H ≠ 0) (hcard : I.card ≤ slotCap)
    (hprime : ∀ i ∈ I, ∀ p ∈ L i, Prime p)
    (ha : ∀ i ∈ I, ∀ p ∈ L i, ‖a i p‖ ≤ 1)
    (V : ℝ → ℂ) (X U B : ℝ) (hX : 0 < X)
    (hV : Function.support V ⊆ Set.Iic U) (hB : 0 ≤ B)
    (hcompleted : ∀ J ∈ I.powerset,
      (∑ k ∈ rows, ‖canonicalCompletedSum (exteriorGamma K S D)
        (canonicalTau K S D θ (row k) r.val.val)
        (divisorMark (I \ J) (residualDivisorLists (H ^ 3) L) a) V X‖ ^ 2) ≤ B) :
    (∑ k ∈ rows, ‖weightedCompletedTheta K S D θ (row k) r ∅
      (fun A => divisorMark I L a (H ^ 3 * A)) V X‖ ^ 2) ≤
      ((2 : ℝ) ^ slotCap * ((idealDivisors (H ^ 3)).card : ℝ) ^ slotCap) ^ 2 * B := by
  let w : ℝ := ((idealDivisors (H ^ 3)).card : ℝ) ^ slotCap
  have hw : 0 ≤ w := pow_nonneg (Nat.cast_nonneg _) _
  have hτ : 1 ≤ ((idealDivisors (H ^ 3)).card : ℝ) := by
    exact_mod_cast FixedTripleFibers.divisor_card_pos (H ^ 3) (pow_ne_zero _ hH)
  have hc (J : Finset σ) (hJ : J ∈ I.powerset) :
      ‖divisorMark J L a (H ^ 3)‖ ≤ w := by
    have hJI := Finset.mem_powerset.mp hJ
    exact (CoefficientBounds.divisorMark_norm_le_divisorPower K J L a (H ^ 3)
      (pow_ne_zero _ hH) (fun i hi => ha i (hJI hi))).trans
      (pow_le_pow_right₀ hτ ((Finset.card_le_card hJI).trans hcard))
  have hb := TerminalHilbert.finite_coefficient_energy I.powerset rows
    (fun J _ => divisorMark J L a (H ^ 3))
    (fun J k => canonicalCompletedSum (exteriorGamma K S D)
      (canonicalTau K S D θ (row k) r.val.val)
      (divisorMark (I \ J) (residualDivisorLists (H ^ 3) L) a) V X)
    (fun _ => w) (fun _ => 1) B hB (fun _ _ => hw) (fun _ _ => zero_le_one)
    (fun J hJ _ _ => hc J hJ)
    (fun J hJ => by simpa only [one_pow, one_mul] using hcompleted J hJ)
  have he (k : κ) :
      weightedCompletedTheta K S D θ (row k) r ∅
        (fun A => divisorMark I L a (H ^ 3 * A)) V X =
        ∑ J ∈ I.powerset, divisorMark J L a (H ^ 3) *
          canonicalCompletedSum (exteriorGamma K S D)
            (canonicalTau K S D θ (row k) r.val.val)
            (divisorMark (I \ J) (residualDivisorLists (H ^ 3) L) a) V X := by
    have ht := canonicalCompletedSum_eq_weightedTheta K S D θ (row k) r ∅
      (fun A => divisorMark I L a (H ^ 3 * A)) V X U hX hV
    simp only [wholeMarkWeight_empty, one_mul] at ht
    rw [← ht]
    exact TerminalMarks.canonicalCompletedSum_cube_priority K S D θ (row k) r I L a H
      hprime V X U hX hV
  simp_rw [← he] at hb
  have hmass : (∑ _J ∈ I.powerset, w * 1) ≤ (2 : ℝ) ^ slotCap * w := by
    simp only [mul_one, Finset.sum_const, nsmul_eq_mul, Finset.card_powerset,
      Nat.cast_pow, Nat.cast_ofNat]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hcard) hw
  exact hb.trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => mul_nonneg hw zero_le_one) hmass 2) hB)

/-- The literal signed short sum is reconstructed with its original
row phases. Only its proved 1/N(H) majorant is used in Minkowski. -/
theorem short_energy {σ κ : Type*} [DecidableEq σ]
    (slotCap : ℕ) (θ : HeckeCharacter K) (rows : Finset κ)
    (row : κ → S.integer K) (f r : Ext)
    (I : Finset σ) (L : σ → Finset (Ideal (𝓞 K)))
    (a : σ → Ideal (𝓞 K) → ℂ) (hcard : I.card ≤ slotCap)
    (hprime : ∀ i ∈ I, ∀ p ∈ L i, Prime p)
    (ha : ∀ i ∈ I, ∀ p ∈ L i, ‖a i p‖ ≤ 1)
    (W : ℝ → ℂ) (X T B mass : ℝ) (hX : 0 < X)
    (hW : Function.support W ⊆ Set.Iic 2) (hB : 0 ≤ B)
    (hmass : (∑ H ∈ shortCubes K S T,
      (((idealDivisors (H.val.val ^ 3)).card : ℝ) ^ slotCap) / exteriorNorm K S H) ≤ mass)
    (hcompleted : ∀ H ∈ shortCubes K S T, ∀ J ∈ I.powerset,
      (∑ k ∈ rows, ‖canonicalCompletedSum (exteriorGamma K S D)
        (canonicalTau K S D θ (row k * D.generator f ^ 4) r.val.val)
        (divisorMark (I \ J) (residualDivisorLists (H.val.val ^ 3) L) a)
        (canonicalVstar W) (X / exteriorNorm K S H ^ 3)‖ ^ 2) ≤ B) :
    (∑ k ∈ rows, ‖shortCompletedColumn K S D θ (row k) f r
      (divisorMark I L a) W X T‖ ^ 2) ≤ ((2 : ℝ) ^ slotCap * mass) ^ 2 * B := by
  let amp := fun H : Ext => (2 : ℝ) ^ slotCap *
    ((idealDivisors (H.val.val ^ 3)).card : ℝ) ^ slotCap
  have hamp (H : Ext) : 0 ≤ amp H := by dsimp only [amp]; positivity
  have hw (H : Ext) : 0 ≤ 1 / exteriorNorm K S H :=
    (one_div_pos.mpr (idealNorm_pos K H.val)).le
  have hb := TerminalHilbert.finite_coefficient_energy (shortCubes K S T) rows
    (fun H k => (moebius H.val.val : ℂ) *
      canonicalTau K S D θ (row k * D.generator f ^ 4) r.val.val H.val.val ^ 3 /
        (exteriorNorm K S H : ℂ))
    (fun H k => weightedCompletedTheta K S D θ (row k * D.generator f ^ 4) r ∅
      (fun A => divisorMark I L a (H.val.val ^ 3 * A)) (canonicalVstar W)
      (X / exteriorNorm K S H ^ 3))
    (fun H => 1 / exteriorNorm K S H) amp B hB (fun H _ => hw H) (fun H _ => hamp H)
    (fun H _ k _ => completeCanonicalColumn_cube_coefficient_norm_le K S D θ (row k) f r H)
    (fun H hH => completed_energy K S D slotCap θ rows
      (fun k => row k * D.generator f ^ 4) r I L a H.val.val
      (nonZeroDivisors.coe_ne_zero H.val) hcard hprime ha (canonicalVstar W)
      (X / exteriorNorm K S H ^ 3) 2 B
      (div_pos hX (pow_pos (idealNorm_pos K H.val) _))
      (canonicalVstar_support_upper W 2 hW) hB (hcompleted H hH))
  change (∑ k ∈ rows, ‖shortCompletedColumn K S D θ (row k) f r
    (divisorMark I L a) W X T‖ ^ 2) ≤
      (∑ H ∈ shortCubes K S T, (1 / exteriorNorm K S H) * amp H) ^ 2 * B at hb
  have hm : (∑ H ∈ shortCubes K S T, (1 / exteriorNorm K S H) * amp H) ≤
      (2 : ℝ) ^ slotCap * mass := by
    calc
      _ = (2 : ℝ) ^ slotCap * ∑ H ∈ shortCubes K S T,
          (((idealDivisors (H.val.val ^ 3)).card : ℝ) ^ slotCap) / exteriorNorm K S H := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro H hH
        dsimp only [amp]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hmass (by positivity)
  exact hb.trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (Finset.sum_nonneg fun H _ => mul_nonneg (hw H) (hamp H)) hm 2) hB)

end TerminalCubePriority
end HeckeSkeleton.Moments.MOM_INV_INDUCTION

end
