import HeckeSkeleton.LowEnergy.GeneralRows
import HeckeSkeleton.LowEnergy.GeneralConductor

/-!
# The conductor inequalities on the original row annuli

The row is first split by its actual prime valuations, including the
valuation-one primes on the label and puncture.  The bounds below retain
the complete powerful part of that original row.  Fixed support endpoints
give the explicit logarithmic errors in Lemma 4.8; neither conductor
comparison is an assumption of the energy theorem.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.LowEnergy.GeneralAnnuli

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.LowEnergy.ActualReflection
open HeckeSkeleton.LowEnergy.ActualReflectionReindex
open HeckeSkeleton.LowEnergy.ActualFrozenCharges
open HeckeSkeleton.LowEnergy.GeneralRows
open HeckeSkeleton.LowEnergy.LogGeometry
open scoped Classical BigOperators NumberField nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- The moving row and the original powerful part have their exact
logarithmic lengths, before any support endpoint is substituted. -/
theorem actual_moving_width (k label puncture : ExteriorIdeal K S)
    {Z : ℝ} (hZ : 1 < Z) :
    scale Z (exteriorNorm K S (movingRow K S k label puncture)) ≤
      scale Z (exteriorNorm K S k) -
        scale Z (exteriorNorm K S (exteriorPowerfulPart K S k)) := by
  have h := scale_mono hZ
    (mul_pos (exteriorNorm_pos K S _) (exteriorNorm_pos K S _))
    (moving_powerful_norm_le K S k label puncture)
  rw [scale_mul Z (exteriorNorm_pos K S _) (exteriorNorm_pos K S _)] at h
  linarith

/-- The second comparison uses the original row and its original powerful
part even when the row meets the fixed label or puncture. -/
theorem actual_conductor_width (k label puncture : ExteriorIdeal K S)
    (hlabel : Squarefree label.val.val) (hpuncture : Squarefree puncture.val.val)
    (s : FrozenState K S (reflectedFrozen K S k label puncture) puncture)
    {Z : ℝ} (hZ : 1 < Z) :
    2 * scale Z (exteriorNorm K S (movingRow K S k label puncture)) +
      2 * scale Z (exteriorNorm K S (primeSetIdeal K S s.active)) -
      scale Z (exteriorNorm K S (minimumLinearIdeal K S s)) -
      scale Z (exteriorNorm K S (minimumSmallIdeal K S s)) -
      4 * scale Z (exteriorNorm K S (minimumCubeIdeal K S s)) ≤
      2 * scale Z (exteriorNorm K S k) -
        scale Z (exteriorNorm K S (exteriorPowerfulPart K S k)) +
        scale Z (exteriorNorm K S label) + scale Z (exteriorNorm K S puncture) := by
  have h := GeneralConductor.conductor_charge_width K S
    (frozenRow K S k label puncture) label puncture (movingRow K S k label puncture)
    hlabel hpuncture s hZ
  rw [moving_frozenRow_eq, powerfulPart_frozenRow] at h
  exact h

theorem lower_support_width {Z C x O : ℝ} (hZ : 1 < Z)
    (hC : 0 < C) (hx : 0 < x) (h : Z ^ O ≤ C * x) :
    O - scale Z C ≤ scale Z x := by
  have hs := scale_mono hZ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) O) h
  rw [scale_rpow hZ O, scale_mul Z hC hx] at hs
  linarith

/-- Both inequalities of (can-conductor-comparison), with the O(1/log Z)
terms replaced by their actual fixed support constants.  X is arbitrary;
its length is exactly log_Z X, and the active-mark length is log_Z Plo. -/
theorem actual_annular_comparisons (k label puncture : ExteriorIdeal K S)
    (hlabel : Squarefree label.val.val) (hpuncture : Squarefree puncture.val.val)
    (s : FrozenState K S (reflectedFrozen K S k label puncture) puncture)
    {Z X Klo Plo M O V Ck Cp Cf : ℝ}
    (hZ : 1 < Z) (hKlo : 0 < Klo)
    (hCk : 0 < Ck) (hCp : 0 < Cp) (hCf : 0 < Cf)
    (hmoving : Klo ≤ exteriorNorm K S (movingRow K S k label puncture))
    (hrow : exteriorNorm K S k ≤ Ck * Z ^ M)
    (hpowerful : Z ^ O ≤ Cp * exteriorNorm K S (exteriorPowerfulPart K S k))
    (hlabelScale : exteriorNorm K S label ≤ Cf * Z ^ V) :
    scale Z Klo ≤ M - O + (Real.log Ck + Real.log Cp) / Real.log Z ∧
      GeneralBlockPolynomial.threshold Z X
          (exteriorNorm K S (primeSetIdeal K S s.active))
          (exteriorNorm K S (minimumLinearIdeal K S s))
          (exteriorNorm K S (minimumCubeIdeal K S s)) Klo Plo -
        scale Z (exteriorNorm K S (minimumSmallIdeal K S s)) -
        scale Z (exteriorNorm K S (minimumCubeIdeal K S s)) ≤
      2 * M - O + scale Z (exteriorNorm K S puncture) + V - scale Z X +
        2 * scale Z Plo +
        (2 * Real.log Ck + Real.log Cp + Real.log Cf) / Real.log Z := by
  have hm := scale_mono hZ hKlo hmoving
  have hr := window_width hZ (exteriorNorm_pos K S k) hCk hrow
  have hp := lower_support_width hZ hCp (exteriorNorm_pos K S _) hpowerful
  have hf := window_width hZ (exteriorNorm_pos K S label) hCf hlabelScale
  have hfirst := actual_moving_width K S k label puncture hZ
  have hsecond := actual_conductor_width K S k label puncture hlabel hpuncture s hZ
  have hconstants1 : (Real.log Ck + Real.log Cp) / Real.log Z =
      scale Z Ck + scale Z Cp := by unfold scale; ring
  have hconstants2 : (2 * Real.log Ck + Real.log Cp + Real.log Cf) / Real.log Z =
      2 * scale Z Ck + scale Z Cp + scale Z Cf := by unfold scale; ring
  rw [hconstants1, hconstants2]
  constructor
  · linarith
  · unfold GeneralBlockPolynomial.threshold
    linarith

#print axioms actual_moving_width
#print axioms actual_conductor_width
#print axioms actual_annular_comparisons

end HeckeSkeleton.LowEnergy.GeneralAnnuli
