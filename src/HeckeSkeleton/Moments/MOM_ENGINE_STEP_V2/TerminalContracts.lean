module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.FirstZeroContracts
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SecondZeroContracts
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.ExceptionalContracts
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.TailContracts

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The four independently selected terminal witnesses

This package only names the four separate certificates. It is not an
additional proof task, and it contains no source construction or child.
-/

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open NumberField HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]

structure TerminalCertificates (c : TargetContext K) (frame : SourceFrame)
    (p : SourceParameters c) where
  first : FirstZeroCertificate c frame p
  second : SecondZeroCertificate c frame p
  exceptional : ExceptionalCertificate c frame p
  tail : TailCertificate c frame p

def TerminalCertificates.costs {c : TargetContext K} {frame : SourceFrame}
    {p : SourceParameters c} (certificates : TerminalCertificates c frame p)
    (arithmeticMass profileMass : Finset (ℕ × ℕ) → UniformCost) : UniformCosts where
  firstZero _ := certificates.first.cost
  secondZero _ := certificates.second.cost
  exceptional _ := certificates.exceptional.cost
  tail _ := certificates.tail.cost
  arithmeticMass := arithmeticMass
  profileMass := profileMass

end HeckeSkeleton.Moments.EngineStepV2.Blueprint
