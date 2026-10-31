import HeckeSkeleton.Principal
import HeckeSkeleton.Expansion
import HeckeSkeleton.HighBin
import HeckeSkeleton.Moments
import HeckeSkeleton.Descent

/-! A compiling dependency skeleton is NOT a proof of the main theorem.
All admissions occur in named upstream obligations, never in this assembly. -/
set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton
open NumberField HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Physical HeckeGeneral.ThetaSkeleton.TIP
variable (K : Type) [Field K] [NumberField K]

theorem sourceT (c : TargetContext K) :
    TSource c.geometry (targetCharacter K c) (targetData K c)
      c.family.B c.family.lamA c.lamB where
  principal := principalSource K c
  expansion := expansionSource K c
  tail := expansion_tail K c (wholeBoundaryTail K c)
  highBin := highBin K c

theorem familyInputs (zeta : K) (hzeta : IsPrimitiveRoot zeta 12)
    (ω : HeckeCharacter K) : TIPInput K ω := by
  intro B hB hBupper hboundary lamA hlamA hlamAsmall
  let f : FamilyContext K :=
    ⟨zeta, hzeta, ω, B, hB, hBupper, hboundary, lamA, hlamA, hlamAsmall⟩
  refine ⟨(momentMesh K f).val, (momentMesh K f).property, ?_⟩
  intro g hg lamB hlamB χ
  let c : TargetContext K := ⟨f, g, hg, lamB, hlamB, χ⟩
  refine ⟨(representative K c).val, (representative K c).property,
    targetData K c, sourceT K c,
    inverseSource K c, plainSource K c⟩

/-- EXPLORATORY endpoint. It retains the pre-existing sorryAx dependencies
listed by Audit. The actual fixed source supplies its high K-type Mellin
input and exterior digit tables, so this assembly has no added local premise. -/
theorem generalHeckeSevenEighths_skeleton : GeneralHeckeSevenEighths := by
  intro F _ _
  apply Descent.descend F
  intro ω
  exact familyInputs (Descent.Extension F) (Descent.root12 F)
    (Descent.primitive_root12 F) ω

end HeckeSkeleton
