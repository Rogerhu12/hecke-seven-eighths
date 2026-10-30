import HeckeGeneral.Analysis.PhysicalProbeData
import DedekindZetaZeroFree.Moments.Probes.AnnularWeightsAndCancellingProfiles

/-!
# Axiom's real annular weight as the skeleton's denominator test

The real weight `W1` of an Axiom principal probe is smooth, nonnegative, nonzero
and compactly supported inside `(0, ∞)`. Viewed as a complex function it is the
skeleton's `DenominatorTest`: its support lies in `[lower, upper]`, where `lower`
and `upper` are the infimum and supremum of the compact topological support.
The infimum is attained, hence positive. The function itself is unchanged.
-/

noncomputable section

namespace HeckeAxiom

open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open scoped ContDiff

namespace DenominatorAdapter

variable (W : DedekindZetaZeroFree.ProbeRealAnnularWeight)

theorem tsupport_nonempty : (tsupport W.toFun).Nonempty := by
  obtain ⟨y, hy⟩ := Function.ne_iff.mp W.nonzero
  exact ⟨y, subset_tsupport _ hy⟩

/-- The lower end of the topological support. -/
def lower : ℝ := sInf (tsupport W.toFun)

/-- The upper end of the topological support. -/
def upper : ℝ := sSup (tsupport W.toFun)

theorem lower_mem : lower W ∈ tsupport W.toFun :=
  W.compactSupport.sInf_mem (tsupport_nonempty W)

theorem lower_pos : 0 < lower W := W.support_positive (lower_mem W)

theorem lower_le_upper : lower W ≤ upper W :=
  le_csSup W.compactSupport.bddAbove (lower_mem W)

theorem support_subset : Function.support (fun y : ℝ => (W.toFun y : ℂ)) ⊆
    Set.Icc (lower W) (upper W) := by
  intro y hy
  have hy' : y ∈ tsupport W.toFun :=
    subset_tsupport _ (by simpa [Function.mem_support] using hy)
  exact ⟨csInf_le W.compactSupport.bddBelow hy', le_csSup W.compactSupport.bddAbove hy'⟩

end DenominatorAdapter

/-- The Axiom real annular weight, as the skeleton's denominator test. -/
def denominatorTest (W : DedekindZetaZeroFree.ProbeRealAnnularWeight) : DenominatorTest where
  toFun y := (W.toFun y : ℂ)
  smooth := Complex.ofRealCLM.contDiff.comp W.smooth
  lower := DenominatorAdapter.lower W
  upper := DenominatorAdapter.upper W
  lower_pos := DenominatorAdapter.lower_pos W
  upper_ge := DenominatorAdapter.lower_le_upper W
  support := DenominatorAdapter.support_subset W
  nonnegative y := by simpa using W.nonnegative y
  real_valued y := by simp
  nonzero := by
    obtain ⟨y, hy⟩ := Function.ne_iff.mp W.nonzero
    exact ⟨y, by simpa using hy⟩

@[simp] theorem denominatorTest_toFun (W : DedekindZetaZeroFree.ProbeRealAnnularWeight)
    (y : ℝ) : (denominatorTest W).toFun y = (W.toFun y : ℂ) := rfl

end HeckeAxiom
