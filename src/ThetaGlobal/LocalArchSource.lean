import ThetaGlobal.FiniteSkeletonSource
import ThetaGlobal.LocalArchInput

/-!
# The high K-type Mellin input on the skeleton's one fixed source

The source is selected before the local vectors. The canonical constructor
uses exactly that source, the same actual recipe and the actual period
character. The generic `FiniteSkeletonSource.data` remains available with
an explicit input; the public skeleton entry point chooses this one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HeckeSkeleton

open NumberField
open HeckeGeneral.ThetaSkeleton.Physical
open scoped NumberField Classical

variable (K : Type) [Field K] [NumberField K] (c : TargetContext K)

/-- The same fixed source supplies all local high K-type Mellin fields. -/
def localHighKMellinInput : LocalHighKMellinInput K c :=
  ThetaGlobal.LocalArchInput.input (thetaRecipe K c)
    (thetaPeriod K (places K c) (probeData K c) (targetCharacter K c))
    (thetaFiniteSource K c)

end HeckeSkeleton

#print axioms HeckeSkeleton.localHighKMellinInput
