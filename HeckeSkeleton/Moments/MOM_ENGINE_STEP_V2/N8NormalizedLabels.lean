import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.RefinementAssembly
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SourceIndexContracts

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The actual refined arithmetic sum counts each label once

The equivalence preserves the original raw index, both passive keys,
both comparison bits and the already chosen capacity children.  The
source-index ledger is not rebuilt when the finite sums are regrouped.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2

open NumberField HeckeGeneral.ThetaSkeleton.Global
open EngineStep Blueprint

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable {input : ProfileInput call}
variable {F : FirstPresentation call p} {family : FirstCauchyFamily F}
variable {expansion : PoolExpansion family} {second : SecondFamily expansion}
variable {geometry : GeometryFamily second}

namespace Blueprint.RefinementData

variable {packet : RawLeafPacket call p} {O : OrdinaryData packet}
variable (R : RefinementData O input) (C : R.Calibrations) (G : C.Capacities)

def arithmeticMass : ℝ :=
  ∑ b : (R.normalizedFamily C G).active Finset.univ,
    R.outer b.val * (R.normalizedFamily C G).weight Finset.univ
      (call.node.parameters.m + call.node.parameters.q) b

theorem arithmeticMass_nonneg : 0 ≤ R.arithmeticMass C G := by
  apply Finset.sum_nonneg
  intro b _
  exact mul_nonneg (R.outer_nonneg b.val)
    ((R.normalizedFamily C G).weight_nonneg Finset.univ
      (call.node.parameters.m + call.node.parameters.q) b call.base_pos)

end Blueprint.RefinementData

namespace Assembly

variable (raw : RawFamily geometry)
variable (O : ∀ j : Fin raw.count, OrdinaryData (raw.packet j))
variable (R : ∀ j, RefinementData (O j) input)
variable (C : ∀ j, (R j).Calibrations) (G : ∀ j, (C j).Capacities)

/-- Reindex only proofs of membership; all label values are unchanged. -/
def refinedActiveEquiv :
    (refinedNormalizedData raw O R C G).Active ≃
      Σ j : Fin raw.count, ((R j).normalizedFamily (C j) (G j)).active Finset.univ where
  toFun b := ⟨b.val.1, ⟨b.val.2, Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, (Finset.mem_filter.mp b.property).2⟩⟩⟩
  invFun b := ⟨⟨b.1, b.2.val⟩, Finset.mem_filter.mpr
    ⟨@Finset.mem_univ _ (refinedNormalizedData raw O R C G).finite _,
      (Finset.mem_filter.mp b.2.property).2⟩⟩
  left_inv := by
    rintro ⟨⟨j, b⟩, hb⟩
    rfl
  right_inv := by
    rintro ⟨j, ⟨b, hb⟩⟩
    rfl

@[simp] theorem refinedActiveEquiv_raw
    (b : (refinedNormalizedData raw O R C G).Active) :
    (refinedActiveEquiv raw O R C G b).1 = b.val.1 := rfl

@[simp] theorem refinedActiveEquiv_passive
    (b : (refinedNormalizedData raw O R C G).Active) :
    (refinedActiveEquiv raw O R C G b).2.val = b.val.2 := rfl

theorem refinedNormalizedData_arithmeticMass :
    (refinedNormalizedData raw O R C G).arithmeticMass =
      ∑ j, (R j).arithmeticMass (C j) (G j) := by
  calc
    _ = ∑ b : (Σ j : Fin raw.count,
        ((R j).normalizedFamily (C j) (G j)).active Finset.univ),
        (R b.1).outer b.2.val *
          ((R b.1).normalizedFamily (C b.1) (G b.1)).weight Finset.univ
            (call.node.parameters.m + call.node.parameters.q) b.2 :=
      Fintype.sum_equiv (refinedActiveEquiv raw O R C G) _ _ (fun _ => rfl)
    _ = _ := by rw [Fintype.sum_sigma]; rfl

/-- The final regrouping step of N8b.  The substantive pointwise
estimates are supplied by the original scalar and passive-allocation
proofs, before this identity is consumed by ArithmeticMassAssembly. -/
theorem refinedNormalizedData_mass_le_indexMass (factor : ℝ)
    (h : ∀ j, (R j).arithmeticMass (C j) (G j) ≤ factor * raw.indexWeight j) :
    (refinedNormalizedData raw O R C G).arithmeticMass ≤ factor * raw.indexMass := by
  rw [refinedNormalizedData_arithmeticMass]
  calc
    _ ≤ ∑ j, factor * raw.indexWeight j := Finset.sum_le_sum fun j _ => h j
    _ = _ := by rw [← Finset.mul_sum]; rfl

end Assembly
end HeckeSkeleton.Moments.EngineStepV2

#print axioms HeckeSkeleton.Moments.EngineStepV2.Assembly.refinedActiveEquiv
#print axioms HeckeSkeleton.Moments.EngineStepV2.Assembly.refinedNormalizedData_arithmeticMass
#print axioms HeckeSkeleton.Moments.EngineStepV2.Assembly.refinedNormalizedData_mass_le_indexMass
