import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.LeafCoverage
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.FiniteKernelFamily

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Normalize every literal leaf using one side-parametric construction

Every physical leaf has its finite allocation/capacity children.  The
two sides share the exact same measure.  The dependent sum below is the
whole child family, including empty ordinary parts and zero-slot cases.
-/

noncomputable section
open scoped Classical BigOperators

namespace HeckeSkeleton.Moments.EngineStepV2

open NumberField MeasureTheory HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global EngineInduction

variable {K : Type} [Field K] [NumberField K] {c : TargetContext K}
variable {n : Node K c.family.omega (targetCharacter K c)} {Z : ℝ}
variable {input : OriginalInput c n Z}

structure NormalizedExpansion (E : HybridExpansion c n Z input) (σ : ℝ)
    (admissible : MomentData K c.family.omega (targetCharacter K c) → RealParameters → Prop) where
  childCount : Fin E.branches → ℕ
  family : ∀ b, ChildFamily (Fin (childCount b)) (WithLp 2 (ℝ × ℝ))
    n.data n.parameters σ admissible
  measures : ∀ b, FiniteKernelFamily (family b) Z
  ordinary_bound : ∀ b, (E.leaf b).ordinaryCost / Z ^ n.width ≤ (measures b).pairIntegral

namespace NormalizedExpansion

variable {E : HybridExpansion c n Z input} {σ : ℝ}
variable {admissible : MomentData K c.family.omega (targetCharacter K c) → RealParameters → Prop}

abbrev Label (N : NormalizedExpansion E σ admissible) :=
  Σ b : Fin E.branches, Fin (N.childCount b)

def children (N : NormalizedExpansion E σ admissible) :
    ChildFamily N.Label (WithLp 2 (ℝ × ℝ)) n.data n.parameters σ admissible :=
  ChildFamily.sigma N.family

def kernels (N : NormalizedExpansion E σ admissible) : FiniteKernelFamily N.children Z :=
  FiniteKernelFamily.sigma N.measures

theorem ordinary_bound_sum (N : NormalizedExpansion E σ admissible) :
    E.ordinary / Z ^ n.width ≤ N.kernels.pairIntegral := by
  sorry

theorem mass_eq_sum (N : NormalizedExpansion E σ admissible) :
    N.kernels.mass = ∑ b : Fin E.branches, (N.measures b).mass := by
  sorry

end NormalizedExpansion

namespace HybridExpansion

def normalizedTerminals (E : HybridExpansion c n Z input) (hZ : 0 ≤ Z) : ScalarLedger :=
  ScalarLedger.scale ((Z ^ n.width)⁻¹)
    (inv_nonneg.mpr (Real.rpow_nonneg hZ _)) E.terminals

theorem normalizedTerminals_total (E : HybridExpansion c n Z input) (hZ : 0 ≤ Z) :
    (E.normalizedTerminals hZ).total = E.terminals.total / Z ^ n.width := by
  sorry

/-- The source estimate is transported to the exact normalized energy
without changing the four terminal contributions or the common kernels. -/
theorem normalized_parent_bound (E : HybridExpansion c n Z input)
    (σ : ℝ)
    (admissible : MomentData K c.family.omega (targetCharacter K c) → RealParameters → Prop)
    (N : NormalizedExpansion E σ admissible) (hZ : 0 < Z)
    (hsource : n.energy Z 0 ≤ E.total) :
    n.normalizedEnergy Z 0 ≤ (E.normalizedTerminals hZ.le).total + N.kernels.pairIntegral := by
  sorry

end HybridExpansion
end HeckeSkeleton.Moments.EngineStepV2
