import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SelectedFamily

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The same computed family supplies the public children and kernels

The finite enumeration follows the actual passive and capacity activity
test. Both sides use the same normalized nested Fourier measure. Its
outer coefficient is the full weight of the original selected leaf.
The exact induction invariant is proved about these existing children.
-/

noncomputable section
open scoped Classical BigOperators

namespace HeckeSkeleton.Moments.EngineStepV2

open EngineStep EngineInduction
open NumberField IsDedekindDomain MeasureTheory DedekindZetaZeroFree
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {frame : SourceFrame} {Cp Hp : ℝ}
variable {hCp : 0 < Cp} {hminimum : (selectedSchedule c frame).minimumCp ≤ Cp}
variable {hHp : 0 ≤ Hp}

namespace SelectedLeafPacket

variable {request : Request c frame Cp Hp hCp hminimum hHp} {frequency : ℝ × ℝ}
variable {leaf : ActualHybridLeaf K (ActualSIntegerOrbit K (places K c)) ℝ ℝ}
variable (p : SelectedLeafPacket request frequency leaf)
variable (hrows : (SelectedProfileData.rows request frequency).Nonempty) (valid : p.Valid)

def childCount : ℕ := Fintype.card ((p.family hrows valid).active Finset.univ)

/-- Geometry is transported back to the original parameters. The
full-support reparametrization preserved their total width and kappa. -/
theorem outputGeometry : (p.family hrows valid).OutputGeometry Finset.univ
    (selectedModel request frequency).data (selectedModel request frequency).parameters
    (recipeInductionSigma c) Set.univ (Set.Icc 0 (SelectedProfileData.upper request))
    (childOrdersAtRank c frame (selectedRank request)) := by
  sorry

/-- The positive local annulus, original slot inverses, profile orders,
mesh and complete arithmetic source recipe hold for these same frozen
normalized children. No child or frequency is reselected. -/
theorem actualAdmissible (side : Bool)
    (b : (p.family hrows valid).active Finset.univ) (ξ : WithLp 2 (ℝ × ℝ)) :
    admissibleOfInvariant request.primitive
      (NormalizedFamilyAdapter.data (p.family hrows valid) Finset.univ side b ξ)
      (NormalizedFamilyAdapter.parameters (p.family hrows valid) Finset.univ side b) := by
  sorry

/-- Individual polynomial profile radii and the original Schwartz
kernels supply convergence, without an aggregate mass hypothesis. -/
theorem outputIntegrability : (p.family hrows valid).OutputIntegrability Finset.univ
    ((p.family hrows valid).kernel Finset.univ
      (actualNestedLabelMeasure (fun _ => leaf.firstKernel) (fun _ => leaf.secondKernel)
        (fun _ => leaf.weight))
      ((selectedModel request frequency).parameters.m +
        (selectedModel request frequency).parameters.q)) := by
  sorry

def children : ChildFamily (Fin (p.childCount hrows valid)) (WithLp 2 (ℝ × ℝ))
    (selectedModel request frequency).data (selectedModel request frequency).parameters
    (recipeInductionSigma c) (admissibleOfInvariant request.primitive) :=
  NormalizedFamilyAdapter.finChildren (p.family hrows valid) Finset.univ
    (p.outputGeometry hrows valid) (p.actualAdmissible hrows valid)

def measures : FiniteKernelFamily (p.children hrows valid) request.base :=
  NormalizedFamilyAdapter.finKernels (p.family hrows valid) Finset.univ
    (p.outputGeometry hrows valid) (p.actualAdmissible hrows valid)
    (fun _ => leaf.firstKernel) (fun _ => leaf.secondKernel) (fun _ => leaf.weight)
    (p.outputIntegrability hrows valid)

/-- The literal source identity, two finite Minkowski inequalities and
the actual normalized atom inequalities bound this original leaf. -/
theorem ordinary_bound : leaf.ordinaryCost /
    request.base ^ (selectedModel request frequency).width ≤
      (p.measures hrows valid).pairIntegral := by
  sorry

end SelectedLeafPacket
end HeckeSkeleton.Moments.EngineStepV2
