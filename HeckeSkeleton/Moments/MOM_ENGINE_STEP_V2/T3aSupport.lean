import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3aElementary
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.HybridZeroRowSupport

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-! # Exact removal of noncontributing original exceptional rows -/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep
open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

namespace RawLeafPacket

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable (packet : RawLeafPacket call p)

theorem exceptional_live_subset : packet.R.live ⊆ packet.leaf.rows := by
  rw [packet.exceptional_leaf_rows]
  exact Finset.filter_subset _ _

theorem exceptional_rowWeight_zero_of_not_live (h : Arithmetic.Orbit c)
    (hh : h ∈ packet.leaf.rows) (hnot : h ∉ packet.R.live) :
    packet.leaf.rowWeight h = 0 := by
  rw [packet.exceptional_leaf_rowWeight]
  have hcorr : packet.R.correlation h = 0 := by
    by_contra hne
    exact hnot (Finset.mem_filter.mpr
      ⟨by simpa only [packet.exceptional_leaf_rows] using hh, hne⟩)
  rw [hcorr, mul_zero]

/-- Exact equality on the original whole centered polynomials. The
finite support deletion uses no bound and takes no triangle inequality. -/
theorem exceptional_exact_support (z : ℝ × ℝ) :
    packet.leaf.exceptionalIntegrand z = packet.supportedExceptionalIntegrand z := by
  unfold ActualHybridLeaf.exceptionalIntegrand
  rw [jointColumnPairMagnitude_filter_eq_on_zero_rows
    packet.leaf.rows packet.R.live packet.leaf.left packet.leaf.right
    packet.leaf.rowWeight packet.leaf.leftCoefficient
    (fun h j => star (packet.leaf.rightCoefficient h j)) _ _ packet.leaf.exceptional
    (WithLp.toLp 2 z) packet.exceptional_live_subset
    packet.exceptional_rowWeight_zero_of_not_live]
  rw [T3a.pairMagnitude_subtype_filter]
  rw [T3a.pairMagnitude_eq_supported]
  simp only [supportedExceptionalIntegrand, exceptionalRows,
    Finset.filter_filter, ne_eq, star_eq_zero]

end RawLeafPacket

end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.exceptional_exact_support
