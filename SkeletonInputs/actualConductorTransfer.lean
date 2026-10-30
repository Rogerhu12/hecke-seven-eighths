import ArithmeticFrequencyRowConductorNorm
import HeckeGeneral.Analysis.PhysicalProbeContours

/-!
Generic transport of the verified canonical radical conductor bound.

This source imports no admitted skeleton presentation or target context. The
only identification required is equality of whole Hecke characters for every
original FrequencyRow, or literal equality with arithmeticRowCharacterInput.
The constant is chosen from K and S before ProbeData, Euler data and rows.
This is the genuine finite conductor norm, not an analytic conductor scale.
New isolated source only: native verification remains separate.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HeckeGeneral.ThetaSkeleton.Physical.ActualConductorTransfer

open NumberField IsDedekindDomain
open HeckeGeneral.Characters
open HeckeGeneral.Arithmetic.ConductorNormDraft
open HeckeGeneral.ThetaSkeleton.Physical

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- The full all-row radical bound, with a real constant, independent of any
particular high-bin context, cutoff, detector or selected height. -/
def HighRadicalBound (P : ProbeData K S) (E : RowEulerData K S P) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ u : FrequencyRow K S,
    ((finiteConductor K (E.rows.character u)).val.absNorm : ℝ) ≤
      C * (u.ideal.val.val.radical.absNorm : ℝ)

/-- The stronger natural-number estimate retains the actual fixed canonical
constant. There is no additional conductor premise. -/
theorem natural_radical_bound_of_actual_calibration
    (P : ProbeData K S) (E : RowEulerData K S P)
    (hChar : ∀ u : FrequencyRow K S,
      E.rows.character u = arithmeticRowCharacter K S P u)
    (u : FrequencyRow K S) :
    (finiteConductor K (E.rows.character u)).val.absNorm ≤
      sexticSConductorNormConstant K S * u.ideal.val.val.radical.absNorm := by
  rw [hChar u]
  exact arithmeticRowCharacter_finiteConductor_absNorm_le_radical K S P u

/-- One real constant precedes every ProbeData, Euler provider, calibration and
actual row. Whole-character calibration is the sole provider identification. -/
theorem exists_fixed_real_radical_bound_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : ProbeData K S) (E : RowEulerData K S P),
      (∀ u : FrequencyRow K S,
        E.rows.character u = arithmeticRowCharacter K S P u) →
      ∀ u : FrequencyRow K S,
        ((finiteConductor K (E.rows.character u)).val.absNorm : ℝ) ≤
          C * (u.ideal.val.val.radical.absNorm : ℝ) := by
  refine ⟨(sexticSConductorNormConstant K S : ℝ), ?_, ?_⟩
  · exact_mod_cast sexticSConductorNormConstant_pos K S
  · intro P E hChar u
    exact_mod_cast natural_radical_bound_of_actual_calibration K S P E hChar u

theorem highRadicalBound_of_actual_calibration
    (P : ProbeData K S) (E : RowEulerData K S P)
    (hChar : ∀ u : FrequencyRow K S,
      E.rows.character u = arithmeticRowCharacter K S P u) :
    HighRadicalBound K S P E := by
  obtain ⟨C, hC, hbound⟩ := exists_fixed_real_radical_bound_constant K S
  exact ⟨C, hC, hbound P E hChar⟩

/-- Literal equality with the actual constructor supplies exactly the required
global calibration, without a separate conductor or finite-fiber assumption. -/
theorem highRadicalBound_of_rows_eq
    (P : ProbeData K S) (E : RowEulerData K S P)
    (hRows : E.rows = arithmeticRowCharacterInput K S P) :
    HighRadicalBound K S P E := by
  apply highRadicalBound_of_actual_calibration K S P E
  intro u
  exact congrArg (fun R : RowCharacterInput K S P => R.character u) hRows

end HeckeGeneral.ThetaSkeleton.Physical.ActualConductorTransfer
