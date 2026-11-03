import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.ProfileWindowAssembly
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.ProfileFormulaTask

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# N5b: original raw and clipped profile windows

Paper: 2927–2946 and 3043–3073. The raw global dictionary is supplied by N3. N5a gives the uniform
analytic estimate; N5b constructs the actual clipped profiles, preserves
the separate original and broad windows, and bounds the computed
polynomial-radius cost on the genuine active source.
-/

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks

open NumberField
open HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]

theorem profile_windows (c : TargetContext K) : ProfileWindowTask c :=
  Assembly.profile_windows_of_formula c profile_formula_control

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks.profile_windows
