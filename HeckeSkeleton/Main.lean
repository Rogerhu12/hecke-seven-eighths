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

theorem sourceT (c : TargetContext K) (L : LocalHighKMellinInput K c)
    (H : LocalExteriorDigitInput K c) :
    TSource c.geometry (targetCharacter K c) (targetData K c)
      c.family.B c.family.lamA c.lamB where
  principal := principalSource K c L H
  expansion := expansionSource K c
  tail := expansion_tail K c (wholeBoundaryTail K c)
  highBin := highBin K c

theorem familyInputs (zeta : K) (hzeta : IsPrimitiveRoot zeta 12)
    (ω : HeckeCharacter K)
    (localData : ∀ c : TargetContext K, LocalHighKMellinInput K c)
    (localDigits : ∀ c : TargetContext K, LocalExteriorDigitInput K c) : TIPInput K ω := by
  intro B hB hBupper hboundary lamA hlamA hlamAsmall
  let f : FamilyContext K :=
    ⟨zeta, hzeta, ω, B, hB, hBupper, hboundary, lamA, hlamA, hlamAsmall⟩
  refine ⟨(momentMesh K f).val, (momentMesh K f).property, ?_⟩
  intro g hg lamB hlamB χ
  let c : TargetContext K := ⟨f, g, hg, lamB, hlamB, χ⟩
  refine ⟨(representative K c).val, (representative K c).property,
    targetData K c, sourceT K c (localData c) (localDigits c),
    inverseSource K c (localData c) (localDigits c), plainSource K c⟩

/-- EXPLORATORY endpoint. It retains the pre-existing sorryAx dependencies
listed by Audit. The explicit premises supply only the one-place high K-type
vectors and Mellin formulas, and the one-place exterior digit tables. -/
theorem generalHeckeSevenEighths_skeleton
    (localData : ∀ (F : Type) [Field F] [NumberField F] (c : TargetContext F),
      Nonempty (LocalHighKMellinInput F c))
    (localDigits : ∀ (F : Type) [Field F] [NumberField F] (c : TargetContext F),
      LocalExteriorDigitInput F c) : GeneralHeckeSevenEighths := by
  intro F _ _
  apply Descent.descend F
  intro ω
  exact familyInputs (Descent.Extension F) (Descent.root12 F)
    (Descent.primitive_root12 F) ω (fun c => Classical.choice (localData _ c))
    (fun c => localDigits _ c)

end HeckeSkeleton
