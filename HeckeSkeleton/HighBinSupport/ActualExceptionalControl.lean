import HeckeSkeleton.HighBin
import HeckeSkeleton.HighBinSupport.ActualEulerData

/-!
# The original exceptional-Euler interface for the arithmetic provider

The estimate is proved for the repository's `HighExceptionalEulerControl`,
with the explicit constants 9 and 2. The provider-identification argument
is retained for API compatibility and is now witnessed by `rfl`: every
actual presentation uses the constructed arithmetic Euler tables by
definition. The remaining named presentation choices are still admitted;
no norm-form or boundary estimate is assumed here.

AI-assisted: ChatGPT / GPT-6 Astra Pro, 2026-10-31.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HeckeSkeleton

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Physical

variable (K : Type) [Field K] [NumberField K]

/-- The actual finite tables satisfy the original exceptional-prime
obligation uniformly over every retained block and all imaginary parts. -/
theorem highExceptionalEulerControl_of_arithmetic
    (c : TargetContext K) (P : ActualHighPresentation K c)
    (hEuler : P.euler = HighBinActualEuler.arithmeticHighEulerData K _
      (targetData K c).probe (targetCharacter K c)) :
    HighExceptionalEulerControl K c P := by
  refine ⟨9, 2, by norm_num, by norm_num, ?_⟩
  intro Z T hZ hT b Q u _hu p hp hpQ _hcutoff s w z hs hw hz
  have hmem := HighBinActualEuler.exceptional_unmarked_mem_row K _ Q u p hp hpQ
  have hdvd : p.val.asIdeal ∣ u.ideal.val.val :=
    (HighBinActualEuler.mem_exteriorSupport_iff K _ u.ideal p).mp hmem
  have ha : (1 / 2 : ℝ) ≤ (((targetData K c).expansion Z T).block b).bin := by
    linarith [(P.bin_range Z T hZ hT b).1]
  have h := HighBinActualEuler.exceptional_unmarked_dynamic_bound K _
    (targetData K c).probe (targetCharacter K c) Q u p hp hpQ
    ha P.e_pos.le s w z hs hw hz
  simpa only [hEuler, if_pos hdvd] using h

end HeckeSkeleton
