import HeckeSkeleton.ExpansionModels.DyadicMomentEnvelope
import HeckePort.Schedule.MomentMesh

/-!
# The repaired row exponent fits the already chosen numerical mesh

The supplied schedule is copied verbatim to the local dependency tree for
independent compilation.  Its cap is M=2.  The paper's effective width is
M=m+q, and the actual source parameters have q=0.  Thus the dyadic envelope
repair remains inside that same pretarget numerical schedule for U>=2.

This verifies the numerical schedule compatibility only; it does not
instantiate the project's unfinished canonical analytic admissibility.
-/

set_option autoImplicit false
noncomputable section

namespace ExpansionRecipe

open HeckePort.Schedule

theorem repaired_effective_width_le_cap {U q : ℝ}
    (hU : 2 ≤ U) (hq : q = 0) :
    0 ≤ dyadicMassExponent U + q ∧ dyadicMassExponent U + q ≤ 2 := by
  rw [hq, add_zero]
  exact ⟨le_trans zero_le_one (dyadicMassExponent_gt_one (by linarith)).le,
    dyadicMassExponent_le_two hU⟩

theorem repaired_width_covered_by_existing_schedule {U ε : ℝ}
    (hU : 2 ≤ U) (hε : 0 < ε) :
    dyadicMassExponent U <
      width 2 (finalSourceCap 2 0 1 ε) ε (count 2 ε) := by
  have h := bounds 2 (finalSourceCap 2 0 1 ε) 1 ε (by norm_num)
    (finalSourceCap_nonneg 2 0 1 ε (by norm_num) le_rfl) zero_le_one hε
  exact (dyadicMassExponent_le_two hU).trans_lt h.2.2.2.2.2.2.2.2.1

theorem existing_mesh_for_repaired_width {U κ ε : ℝ}
    (hU : 2 ≤ U) (hκ : 0 ≤ κ) (hκ' : κ ≤ 1) (hε : 0 < ε) :
    1 ≤ dyadicMassExponent U ∧ dyadicMassExponent U ≤ 2 ∧
      0 < momentMeshValue ε ∧ momentMeshValue ε ≤ fineMesh 2 0 1 κ ε := by
  exact ⟨(dyadicMassExponent_gt_one (by linarith)).le,
    dyadicMassExponent_le_two hU, momentMeshValue_pos hε,
    momentMeshValue_le_fineMesh hε hκ hκ'⟩

end ExpansionRecipe

#print axioms ExpansionRecipe.repaired_effective_width_le_cap
#print axioms ExpansionRecipe.repaired_width_covered_by_existing_schedule
#print axioms ExpansionRecipe.existing_mesh_for_repaired_width
