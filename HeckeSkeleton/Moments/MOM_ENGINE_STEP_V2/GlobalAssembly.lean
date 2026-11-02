import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.NormalizationCertificate
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SourceAssembly
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.LocalAssembly
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.EmptyAssembly
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.UniformAssembly

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Global quantifier assembly after the named tasks are composed

The three internal certificates are selected before the original
profile coefficients and the moving call. The numerical task sees all
six fixed cost witnesses and both finite construction demands. It then
prepares the original profiles once. The source, four terminal estimates
and normalization refer to that same call and the same raw family.

The final blueprint theorem supplies these internal certificates by
explicitly composing the named S, N and T task proofs. This helper is
not a replacement for those task hypotheses.
-/

noncomputable section

namespace HeckeSkeleton.Moments.EngineStepV2.Assembly

open NumberField
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton.Global
open EngineInduction.Source Blueprint

variable {K : Type} [Field K] [NumberField K]

theorem pairedStepHypothesis_of_certificates (c : TargetContext K)
    (p : SourceParameters c)
    (source : ∀ frame : SourceFrame, SourceCertificate c frame p)
    (terminal : ∀ frame : SourceFrame, TerminalCertificates c frame p)
    (normalization : ∀ frame : SourceFrame, NormalizationCertificate c frame p)
    (uniform : UniformChoiceTask c) : PairedStepHypothesis EngineParameter c := by
  classical
  let demand (frame : SourceFrame) (orders : Finset (ℕ × ℕ)) :=
    (source frame).demand.join ((normalization frame).demand orders)
  let costs (frame : SourceFrame) :=
    ((terminal frame).costs (normalization frame).arithmeticCost
      (normalization frame).profileCost).withDemand (demand frame)
  let realization (frame : SourceFrame) : UniformRealization c frame (costs frame) :=
    Classical.choice (uniform frame (costs frame))
  apply pairedStepHypothesis_of_preparations c
    (fun frame => (realization frame).preparation)
  intro frame Cp Hp hCp hminimum hHp request frequency
  let call := (realization frame).preparation.toCall request frequency
  let input := (realization frame).inputs Cp Hp hCp hminimum hHp request frequency
  have hframe : call.frame = frame := rfl
  by_cases active : call.Active
  · have ready : (demand frame call.childOrders).Ready call input.profile :=
      UniformCost.demand_ready_of_withDemand input.firstZero_ready
    obtain ⟨trace, geometry, raw, htrace, hgeometry, hraw, hsource⟩ :=
      (source frame).produce call input.profile hframe ready.ready_left active
    obtain ⟨normalized⟩ := (normalization frame).produce call input.profile hframe
      ready.ready_right
      (UniformCost.ready_of_withDemand input.arithmeticMass_ready)
      (UniformCost.ready_of_withDemand input.profileMass_ready)
      trace htrace geometry hgeometry raw hraw
    exact output_of_source_normalization (terminal frame)
      (normalization frame).arithmeticCost (normalization frame).profileCost
      (demand frame) call input hframe trace htrace geometry hgeometry raw hraw
      hsource normalized.data normalized.geometry normalized.atoms normalized.admissible
      normalized.ordinary normalized.arithmetic normalized.profile
  · exact emptyOutput call active

end HeckeSkeleton.Moments.EngineStepV2.Assembly

#print axioms HeckeSkeleton.Moments.EngineStepV2.Assembly.pairedStepHypothesis_of_certificates
