module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.FirstZeroProfileBounds
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalParentTuples

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# T1: the original pair tuple at the fixed occurrence cap

The source equivalence is applied separately to the two columns. The
existing original tuple retains both plain ideals and every prime
occurrence, padding only by units to the fixed cap. Tuple injectivity
is global; its product is identified with the source's original ideal
product on the unchanged finite source carrier.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.FirstZeroProof

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.EngineStep

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

/-- The literal two-column factor tuple, with only unit padding. -/
def firstPairFactors (F : FirstPresentation call p)
    (ij : F.source.Column × F.source.Column) :
    Fin (2 * (c.geometry.slots + 2)) → Ideal (𝓞 K) :=
  call.workingRaw.originalPairIdealFactors
    (A := Arithmetic.data c) (Γ := Arithmetic.unitSubgroup c)
    c.geometry.slots call.slots_le (F.index ij.1, F.index ij.2)

theorem firstPairFactors_injective (F : FirstPresentation call p) :
    Function.Injective (firstPairFactors F) := by
  intro ij kl h
  have he : (F.index ij.1, F.index ij.2) = (F.index kl.1, F.index kl.2) :=
    call.workingRaw.originalPairIdealFactors_injective
      (A := Arithmetic.data c) (Γ := Arithmetic.unitSubgroup c)
      c.geometry.slots call.slots_le h
  exact Prod.ext (F.index.injective (congrArg Prod.fst he))
    (F.index.injective (congrArg Prod.snd he))

/-- The full source ideal product is recovered on its actual carrier. -/
theorem firstPairFactors_product (F : FirstPresentation call p) (hF : F.Realizes)
    (ij : F.source.Column × F.source.Column)
    (hij : ij ∈ F.source.columns ×ˢ F.source.columns) :
    PowerfulDiagonal.tupleIdeal (firstPairFactors F ij) =
      (F.source.ideal ij.1).val * (F.source.ideal ij.2).val := by
  have hleft : (F.source.ideal ij.1).val =
      call.workingRaw.columnIdeal (F.index ij.1) :=
    (congrArg (fun I : (Arithmetic.data c).Exterior => I.val) (hF.ideal ij.1)).trans
      (call.workingRaw.columnExterior_val_of_mem (F.index ij.1)
        (first_index_mem F hF ij.1 (Finset.mem_product.mp hij).1))
  have hright : (F.source.ideal ij.2).val =
      call.workingRaw.columnIdeal (F.index ij.2) :=
    (congrArg (fun I : (Arithmetic.data c).Exterior => I.val) (hF.ideal ij.2)).trans
      (call.workingRaw.columnExterior_val_of_mem (F.index ij.2)
        (first_index_mem F hF ij.2 (Finset.mem_product.mp hij).2))
  calc
    PowerfulDiagonal.tupleIdeal (firstPairFactors F ij) =
        call.workingRaw.columnIdeal (F.index ij.1) *
          call.workingRaw.columnIdeal (F.index ij.2) :=
      call.workingRaw.originalPairIdealFactors_product
        (A := Arithmetic.data c) (Γ := Arithmetic.unitSubgroup c)
        c.geometry.slots call.slots_le (F.index ij.1, F.index ij.2)
    _ = (F.source.ideal ij.1).val * (F.source.ideal ij.2).val :=
      congrArg₂ (fun I J : Ideal (𝓞 K) => I * J) hleft.symm hright.symm

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.FirstZeroProof

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.FirstZeroProof.firstPairFactors_injective
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.FirstZeroProof.firstPairFactors_product
