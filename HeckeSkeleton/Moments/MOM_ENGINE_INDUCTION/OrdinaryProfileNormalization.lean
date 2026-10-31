import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.PowerWindowSeminorm
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.ProfileControlScaling

/-!
# Normalizing actual ordinary-reflection child profiles

The fixed window has polynomial frequency cost.  A positive envelope
normalizes the complete literal child data, including all profiles which
were retained from the parent.  The extracted energy factor is exact.
This file establishes a unit control at a specified child Euler order;
it does not claim that reflection is closed at a fixed Euler order.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField MeasureTheory Set
open HeckeGeneral.Analysis HeckeGeneral.Characters
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.UniformAmplify
open scoped Classical BigOperators

/-- Chosen once at a requested child Euler order, before frequency. -/
def ordinaryProfileEnvelope (E0 : ℝ) (J : ℕ) (t : ℝ) : ℝ :=
  E0 * (1 + |t|) ^ J

/-- Conjugating the dual column reverses frequency without changing its
normalization envelope. -/
theorem ordinaryProfileEnvelope_neg (E0 : ℝ) (J : ℕ) (t : ℝ) :
    ordinaryProfileEnvelope E0 J (-t) = ordinaryProfileEnvelope E0 J t := by
  simp only [ordinaryProfileEnvelope, abs_neg]

theorem one_le_ordinaryProfileEnvelope {E0 : ℝ} (hE0 : 1 ≤ E0) (J : ℕ) (t : ℝ) :
    1 ≤ ordinaryProfileEnvelope E0 J t := by
  exact one_le_mul_of_one_le_of_one_le hE0
    (one_le_pow₀ (by linarith [abs_nonneg t]))

/-- Every actual plain/slot profile contributes one power in the row
amplitude.  A fixed slot cap gives one polynomial frequency cost. -/
theorem ordinaryProfileEnvelope_amplitude_bound {E0 : ℝ} (hE0 : 1 ≤ E0)
    (J slots cap : ℕ) (hslots : slots ≤ cap) (t : ℝ) :
    ordinaryProfileEnvelope E0 J t ^ (slots + 2) ≤
      E0 ^ (cap + 2) * (1 + |t|) ^ (J * (cap + 2)) := by
  calc
    _ ≤ ordinaryProfileEnvelope E0 J t ^ (cap + 2) :=
      pow_le_pow_right₀ (one_le_ordinaryProfileEnvelope hE0 J t) (by omega)
    _ = _ := by rw [ordinaryProfileEnvelope, mul_pow, ← pow_mul]

variable {K : Type} [Field K] [NumberField K]
variable {omegaCharacter psiCharacter : HeckeCharacter K}

/-- Normalize the actual one-frequency child, retaining its complete
original arithmetic row, mask and slot geometry. -/
def normalizedOrdinaryPowerChild (d : MomentData K omegaCharacter psiCharacter)
    (first : Bool) (σ frequency E0 : ℝ) (hE0 : 1 ≤ E0) (J : ℕ) :
    MomentData K omegaCharacter psiCharacter :=
  scaledMomentProfiles (ordinaryPowerChild K d first σ frequency)
    (ordinaryProfileEnvelope E0 J frequency)⁻¹
    (inv_pos.mpr (zero_lt_one.trans_le (one_le_ordinaryProfileEnvelope hE0 J frequency)))

/-- One fixed envelope normalizes all profiles of every actual child.
The parent control is requested only at the child order; its higher
order needed for the reflection density is supplied by the finite rank
schedule, not inferred from this statement. -/
theorem exists_normalizedOrdinaryPowerChild_control (J : ℕ) (A : ℝ) :
    ∃ E0 : ℝ, ∃ hE0 : 1 ≤ E0,
      ∀ (d : MomentData K omegaCharacter psiCharacter) (first : Bool)
      (σ frequency a b : ℝ),
      ModelProfileControl d J A 1 0 a b 0 → a ≤ 1 / 2 → 2 ≤ b →
      σ ∈ Icc (1 / 4) (3 / 4) →
      ModelProfileControl (normalizedOrdinaryPowerChild d first σ frequency E0 hE0 J)
        J A 1 0 a b 0 := by
  obtain ⟨C, hC, hwindow⟩ := ordinaryPowerWindow_sliceControl J A
  let E0 := max 1 C
  have hE0 : 1 ≤ E0 := le_max_left _ _
  refine ⟨E0, hE0, ?_⟩
  intro d first σ frequency a b hparent ha hb hσ
  have henv := one_le_ordinaryProfileEnvelope hE0 J frequency
  have raise {f : ℝ → ℂ} (h : SliceControl J A 1 0 a b 0 f) :
      SliceControl J A E0 (J : ℝ) a b |frequency| f := by
    refine ⟨h.1, h.2.1, ?_⟩
    have hi : testSeminorm f J A ≤ 1 := by simpa only [Real.rpow_zero, mul_one] using h.2.2
    simpa only [ordinaryProfileEnvelope, Real.rpow_natCast] using hi.trans henv
  have hnew : SliceControl J A E0 (J : ℝ) a b |frequency| (ordinaryPowerWindow σ frequency) := by
    have h := hwindow σ hσ frequency
    refine ⟨h.1, fun y hy => ⟨ha.trans (h.2.1 y hy).1, (h.2.1 y hy).2.trans hb⟩,
      h.2.2.trans ?_⟩
    exact mul_le_mul_of_nonneg_right (le_max_right 1 C) (Real.rpow_nonneg (by positivity) _)
  have hc : ModelProfileControl (ordinaryPowerChild K d first σ frequency)
      J A E0 (J : ℝ) a b |frequency| := by
    intro q
    cases q with
    | inverse u => exact raise (modelProfileControl_inverse hparent u)
    | plain₁ u =>
      cases first with
      | false => exact raise (modelProfileControl_plain₁ hparent u)
      | true =>
        simpa [modelProfile, ordinaryPowerChild, IdealTest.freezeTwist,
          ordinaryPowerWindowIdealTest, profilePower_zero] using hnew
    | plain₂ u =>
      cases first with
      | false =>
        simpa [modelProfile, ordinaryPowerChild, IdealTest.freezeTwist,
          ordinaryPowerWindowIdealTest, profilePower_zero] using hnew
      | true => exact raise (modelProfileControl_plain₂ hparent u)
    | prime j => exact raise (modelProfileControl_prime hparent j)
  exact normalizedMomentProfiles_unit_control hc
    (zero_lt_one.trans_le henv) (by simp only [ordinaryProfileEnvelope, Real.rpow_natCast])

/-- The exact complete child energy removed during normalization. -/
theorem ordinaryPowerChild_energy_normalization
    (d : MomentData K omegaCharacter psiCharacter) (first : Bool)
    (σ frequency E0 : ℝ) (hE0 : 1 ≤ E0) (J : ℕ)
    (p : RealParameters) (U t : ℝ) :
    pairedEnergy (ordinaryPowerChild K d first σ frequency) p U t =
      ordinaryProfileEnvelope E0 J frequency ^ ((d.geometry.slotCount + 2) * 2) *
        pairedEnergy (normalizedOrdinaryPowerChild d first σ frequency E0 hE0 J) p U t :=
  pairedEnergy_normalizedMomentProfiles (ordinaryPowerChild K d first σ frequency) p
    (ordinaryProfileEnvelope E0 J frequency)
    (zero_lt_one.trans_le (one_le_ordinaryProfileEnvelope hE0 J frequency)) U t

end HeckeSkeleton.Moments.EngineInduction
