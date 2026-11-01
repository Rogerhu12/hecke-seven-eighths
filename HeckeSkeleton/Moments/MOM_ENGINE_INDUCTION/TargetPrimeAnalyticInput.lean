import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.MovingPrimeProvider
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.RecipeThetaFamily
import Expansion.CanonicalDetectorCharacters

/-!
# Original analytic inputs for the actual target source

The given packet boundary supplies the finite-order boundary at the
original dynamic kappa.  The Euler half-plane handles all larger real
parts directly, so no independent seed or finite-order seven-eighths
theorem is needed.  The raw analytic provider is then instantiated on
the fixed finite source theta, before every recursive source and scale.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction.Source

open NumberField HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open Expansion.Project EngineStep

variable {K : Type} [Field K] [NumberField K] (c : TargetContext K)

/-- The target's existing packet boundary already covers every finite
character.  The convergence half-plane is discharged by the actual
Euler product rather than by a stronger boundary assumption. -/
theorem targetFiniteOrderBoundary : FiniteOrderBoundary (K := K) c.family.B := by
  intro chi hfinite s hs
  by_cases hright : 1 < s.re
  · rw [meromorphicOrderAt_heckeContinuation K chi hright]
    exact le_rfl
  · apply le_of_not_gt
    intro hzero
    let index : HeckePacketIndex K c.family.omega :=
      ⟨chi, finiteOrder_mem_heckePacket K c.family.omega chi hfinite⟩
    have hbound := c.family.boundary index s.re ⟨s, rfl, hzero⟩
      (by linarith [c.family.B_lower]) (le_of_not_gt hright)
    exact (not_le_of_gt hs) hbound

/-- The cancellation parameter is the same one retained by the
original source and every actual descendant. -/
theorem targetDynamicFiniteOrderBoundary (kappa : ℝ)
    (hkappa : kappa = 2 * c.family.B - 1) :
    FiniteOrderBoundary (K := K) ((kappa + 1) / 2) := by
  rw [hkappa, show (2 * c.family.B - 1 + 1) / 2 = c.family.B by ring]
  exact targetFiniteOrderBoundary c

/-- The actual fixed canonical theta needs no additional finite-order
certificate from a caller of the strict induction producer. -/
theorem actualSourcePrimeAnalyticProvider
    (rows : RowCharacterInput K (places K c) (probeData K c)) :
    CanonicalOriginalPrimeAnalyticProvider.Provider
      (A := (axiomChoice K c).A) (P := probeData K c) (R := rows)
      (canonicalDetectorTheta K (targetCharacter K c)) :=
  originalPrimeAnalyticProvider (isComplex_of_family K c)
    (canonicalDetectorTheta K (targetCharacter K c))
    (canonicalDetectorTheta_finiteOrder K (targetCharacter K c))

/-- The same construction also supplies the finite union used in the
generic recipe recursion. Moving characters are not put in this set. -/
theorem recipeSourcePrimeAnalyticProvider
    (recipe : ExpansionRecipe.RecipeExpansion K (places K c) (targetCharacter K c)
      c.geometry (expansionShellAllowance K c))
    (rows : RowCharacterInput K (places K c) (probeData K c)) :
    CanonicalOriginalPrimeAnalyticProvider.Provider
      (A := (axiomChoice K c).A) (P := probeData K c) (R := rows)
      (recipeThetaFamily recipe) :=
  originalPrimeAnalyticProvider (isComplex_of_family K c)
    (recipeThetaFamily recipe) (recipeThetaFamily_finiteOrder recipe)

end HeckeSkeleton.Moments.EngineInduction.Source
