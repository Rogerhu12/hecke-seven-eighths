import HeckeSkeleton.Moments.MOM_ENGINE_STEP.NormalizedMomentProfiles
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.UniformLengthCapacity

/-!
# Profile normalization before one uniform slot removal

All live profiles are normalized before applying the fixed prime bounds.
Restriction commutes with this actual normalization.  Thus the source
comparison extracts the original live-slot degree, even if some of those
slots are subsequently removed.  The identities below also verify the
same accounting when a raw prime bound is written with its explicit
square of the profile radius.
-/

noncomputable section
open scoped Classical BigOperators

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments

variable {K : Type} [Field K] [NumberField K]
variable {ω ψ : HeckeCharacter K}

theorem normalizedMomentProfiles_restrictSlots (d : MomentData K ω ψ)
    (keep : Finset (Fin d.geometry.slotCount)) (B : ℝ) (hB : 0 < B) :
    normalizedMomentProfiles (d.restrictSlots keep) B hB =
      (normalizedMomentProfiles d B hB).restrictSlots keep := rfl

theorem normalizedMomentProfiles_lengthSlot (d : MomentData K ω ψ)
    (n : ℕ) (hc : d.geometry.slotCount = n) (B : ℝ) (hB : 0 < B) (i : Fin n) :
    lengthSlot (normalizedMomentProfiles d B hB) n hc i = lengthSlot d n hc i := rfl

theorem normalizedMomentProfiles_lengthSelection (d : MomentData K ω ψ)
    (n : ℕ) (hc : d.geometry.slotCount = n) (B : ℝ) (hB : 0 < B)
    (keep : Finset (Fin n)) :
    lengthSelection (normalizedMomentProfiles d B hB) n hc keep =
      lengthSelection d n hc keep := rfl

theorem normalizedMomentProfiles_remainingParameters (d : MomentData K ω ψ)
    (a : RealParameters) (keep : Finset (Fin d.geometry.slotCount)) (B : ℝ) (hB : 0 < B) :
    remainingParameters (normalizedMomentProfiles d B hB) a keep =
      remainingParameters d a keep := rfl

theorem MomentProfileUnitBall.restrictSlots (d : MomentData K ω ψ)
    (keep : Finset (Fin d.geometry.slotCount)) (t : ℝ) (orders : Finset (ℕ × ℝ))
    (h : MomentProfileUnitBall d t orders) :
    MomentProfileUnitBall (d.restrictSlots keep) t orders := by
  refine ⟨h.1, ?_⟩
  intro q hq i
  exact h.2 q hq (selectedSlotIndex keep i)

/-- Normalized prime bounds give exactly a square of the radius in the
raw bound, one factor for each deleted prime slot. -/
theorem primePolynomial_profile_factor (d : MomentData K ω ψ)
    (B : ℝ) (hB : 0 < B) (i : Fin d.geometry.slotCount)
    (u : NonzeroIdeal K) (Z t : ℝ) :
    ‖primePolynomial d i u Z t‖ ^ 2 =
      B ^ 2 * ‖primePolynomial (normalizedMomentProfiles d B hB) i u Z t‖ ^ 2 := by
  rw [primePolynomial_normalizedMomentProfiles, norm_mul,
    Complex.norm_of_nonneg (inv_nonneg.mpr hB.le), mul_pow, inv_pow, ← mul_assoc,
    mul_inv_cancel₀ (pow_ne_zero _ hB.ne'), one_mul]

theorem removed_retained_card {n : ℕ} (removed : Finset (Fin n)) :
    removed.card + (Finset.univ \ removed).card = n := by
  have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ removed)
  simpa only [Finset.card_univ, Fintype.card_fin, Nat.add_comm] using h

theorem removed_retained_profile_power {n : ℕ} (removed : Finset (Fin n)) (B : ℝ) :
    B ^ removed.card * B ^ ((Finset.univ \ removed).card + 2) = B ^ (n + 2) := by
  rw [← pow_add]
  congr 1
  have h := removed_retained_card removed
  omega

/-- This exact equality shows why normalizing only the retained slots
would omit the profile costs of the deleted ones. -/
theorem removed_retained_profile_energy {n : ℕ}
    (removed : Finset (Fin n)) (B : ℝ) (C : Fin n → ℝ) :
    (∏ i ∈ removed, B ^ 2 * C i) *
      B ^ (((Finset.univ \ removed).card + 2) * 2) =
    B ^ ((n + 2) * 2) * (∏ i ∈ removed, C i) := by
  rw [Finset.prod_mul_distrib, Finset.prod_const]
  have hp : 2 * removed.card + ((Finset.univ \ removed).card + 2) * 2 =
      (n + 2) * 2 := by
    have h := removed_retained_card removed
    omega
  calc
    _ = B ^ (2 * removed.card + ((Finset.univ \ removed).card + 2) * 2) *
        (∏ i ∈ removed, C i) := by
      rw [pow_add, pow_mul]
      ring
    _ = _ := by rw [hp]

theorem removed_retained_profile_sqrt {n : ℕ}
    (removed : Finset (Fin n)) (B : ℝ) (hB : 0 ≤ B) (C : Fin n → ℝ) (W : ℝ) :
    Real.sqrt (W * (∏ i ∈ removed, B ^ 2 * C i)) *
      B ^ ((Finset.univ \ removed).card + 2) =
    B ^ (n + 2) * Real.sqrt (W * (∏ i ∈ removed, C i)) := by
  rw [Finset.prod_mul_distrib, Finset.prod_const]
  have he : W * ((B ^ 2) ^ removed.card * (∏ i ∈ removed, C i)) =
      (B ^ removed.card) ^ 2 * (W * (∏ i ∈ removed, C i)) := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm 2 removed.card]
    ring
  rw [he, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (pow_nonneg hB _)]
  calc
    _ = (B ^ removed.card * B ^ ((Finset.univ \ removed).card + 2)) *
        Real.sqrt (W * (∏ i ∈ removed, C i)) := by ring
    _ = _ := by rw [removed_retained_profile_power]

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.normalizedMomentProfiles_restrictSlots
#print axioms HeckeSkeleton.Moments.EngineStep.removed_retained_profile_energy
#print axioms HeckeSkeleton.Moments.EngineStep.removed_retained_profile_sqrt
