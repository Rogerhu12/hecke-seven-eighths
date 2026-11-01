import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ExceptionalAtomBudget

/-!
# One original profile power pays every exceptional atom

Only individual original common, frozen and live atom constants occur
in the window.  Both complete occurrence counts are bounded by the
original cap, including slots later frozen or removed.  The resulting
power is fixed before the original profile control is chosen.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Characters HeckePort.CenteredMomentCounting

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable [IsPrincipalIdealRing A.R]
variable {H ι : Type*} [Fintype ι] [DecidableEq ι]
variable {C : A.GeneralArithmeticContext σ η hS}
variable {R : ActualSecondCorrelationRows A σ H ι}
variable {k l kLeft kRight : ℕ}
variable {left : ActualColumnAllocation K k} {right : ActualColumnAllocation K l}

/-- No product estimate is a field: all inputs are the original
single-atom bounds and the one earlier occurrence cap. -/
structure ExceptionalOriginalAtomWindow
    (W : ActualSecondRowMass R C kLeft kRight)
    (UL : ExceptionalAtomicScales left) (UR : ExceptionalAtomicScales right)
    (cap : ℕ) (B : ℝ) : Prop where
  left_slots : k ≤ cap
  right_slots : l ≤ cap
  left_common_slots : kLeft ≤ cap
  right_common_slots : kRight ≤ cap
  common_profile : W.profileBound ≤ B
  left_common : ∀ i ∈ Finset.univ \ W.leftAtoms.keep,
    W.leftAtoms.annulus i * W.leftAtoms.profile i ≤ B
  right_common : ∀ i ∈ Finset.univ \ W.rightAtoms.keep,
    W.rightAtoms.annulus i * W.rightAtoms.profile i ≤ B
  left_frozen : ∀ i ∈ Finset.univ \ left.keep, UL.annulus i * UL.profileSquare i ≤ B
  right_frozen : ∀ i ∈ Finset.univ \ right.keep, UR.annulus i * UR.profileSquare i ≤ B
  left_root : UL.rootConstant ≤ B
  right_root : UR.rootConstant ≤ B
  left_cutoff : ∀ i, UL.cutoffConstant i ≤ B
  right_cutoff : ∀ i, UR.cutoffConstant i ≤ B
  left_atom : ∀ i, UL.atomConstant i ≤ B
  right_atom : ∀ i, UR.atomConstant i ≤ B

namespace ExceptionalOriginalAtomWindow

variable {W : ActualSecondRowMass R C kLeft kRight}
variable {UL : ExceptionalAtomicScales left} {UR : ExceptionalAtomicScales right}
variable {cap : ℕ} {B : ℝ}

/-- Both original common envelopes and all frozen/live slot atoms are
paid once, with a degree depending only on the original slot cap. -/
theorem envelope_le (a : ExceptionalOriginalAtomWindow W UL UR cap B) (hB : 1 ≤ B) :
    W.commonEnvelope * (UL.constant * UR.constant) ≤
      idealCountConstant K ^ (2 * cap) * B ^ (6 * cap + 3) := by
  have hc := W.commonEnvelope_le_from_atoms cap B hB
    a.left_common_slots a.right_common_slots a.common_profile a.left_common a.right_common
  have hp := UL.pair_constant_le_from_atoms UR cap B hB a.left_slots a.right_slots
    a.left_frozen a.right_frozen a.left_root a.right_root
    a.left_cutoff a.right_cutoff a.left_atom a.right_atom
  apply (mul_le_mul hc hp (mul_nonneg UL.constant_nonneg UR.constant_nonneg)
    (pow_nonneg (zero_le_one.trans hB) _)).trans_eq
  rw [mul_pow, ← pow_mul]
  calc
    _ = idealCountConstant K ^ (2 * cap) *
        ((B ^ (cap + 1) * B ^ (cap + 2)) * B ^ (2 * (2 * cap))) := by ring
    _ = idealCountConstant K ^ (2 * cap) * B ^ ((cap + 1) + (cap + 2) + 2 * (2 * cap)) := by
      rw [← pow_add, ← pow_add]
    _ = _ := by congr 2 <;> omega

/-- The original control may be any fixed positive power.  Its degree
is selected before P and is unchanged by the actual source or rows. -/
theorem envelope_le_profile_power {P : ℝ} (hP : 1 ≤ P) (degree : ℕ)
    (a : ExceptionalOriginalAtomWindow W UL UR cap (P ^ degree)) :
    W.commonEnvelope * (UL.constant * UR.constant) ≤
      idealCountConstant K ^ (2 * cap) * P ^ (degree * (6 * cap + 3)) := by
  simpa only [pow_mul] using a.envelope_le (one_le_pow₀ hP)

end ExceptionalOriginalAtomWindow
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ExceptionalOriginalAtomWindow.envelope_le_profile_power
