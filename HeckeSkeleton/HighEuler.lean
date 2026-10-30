import HeckeSkeleton.HighEulerRegionAudit
import HeckeSkeleton.HighEulerScalarBounds
import HeckeSkeleton.HighEulerFiniteData
import HeckeSkeleton.HighEulerCheckedTable

/-!
# Checked components for the high-row Euler task

This entry point collects:

* exact algebra for the supplied project's rational correction and an audit of
  the region's real inequalities;
* explicit finite rational data, with coefficient parameters left visible;
* a pointwise bound `9 * q ^ (-10 * e)` for the five normalized ramified tables
  on the dynamic line, valid uniformly in their allowed local phases;
* proved evaluation identities connecting explicit normalized finite data to
  those scalar expressions, including the marked tables.

The arithmetic identification of those parameters with `finitePoissonFactor`
is a separate obligation.  The original region also needs its two missing
mixed inequalities before a full normal-convergence theorem can be supplied.
This file therefore does not declare `highEulerData`, `TRowEulerInput`, or the
presentation-level `HighExceptionalEulerControl`.
-/

#print axioms HBEulerRegionAudit.project_rational_sub_one
#print axioms HBEulerRegionAudit.dv_large_w_region_counterexample
#print axioms HeckeGeneral.ThetaSkeleton.Physical.HighEulerScalarBounds.ramified_table_dynamic_bound
#print axioms HBEulerCheckedTable.normalizedFiniteFactor_dynamic_bound
#print axioms HBEulerCheckedTable.normalizedMarkedFiniteFactor_dynamic_bound
#print axioms HBEulerCheckedTable.normalizedFiniteFactor_twisted_dynamic_bound
