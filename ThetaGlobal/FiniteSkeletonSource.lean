module

public import HeckeSkeleton.Base
public import ThetaGlobal.FiniteLocalHighK
public import ThetaGlobal.FiniteAssembly

/-!
# Finite Mellin data on the skeleton's one actual arithmetic choice

The recipe, Haar transport, source, finite projection, and coefficient
table are selected constructively from `Base.axiomChoice`.  The only
remaining input is the explicit per-place high K-type Mellin package.
The source is selected before that local input, and every later theorem
uses the same selection.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
noncomputable section

namespace HeckeSkeleton

open NumberField MeasureTheory DedekindZetaZeroFree DedekindZetaZeroFree.MomentSources
open HeckeGeneral.Characters HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open scoped NumberField Classical BigOperators

variable (K : Type) [Field K] [NumberField K] (c : TargetContext K)

def thetaRecipe : PrincipalMellin.ActualRecipe (axiomChoice K c).A (axiomChoice K c).η :=
  ThetaGlobal.GlobalSameChoice.recipe (axiomChoice K c) (axiomChoice_modulus_top K c)

theorem thetaRecipe_aligned : RootAligned (thetaRecipe K c) :=
  axiomChoice_coefficientEmbedding K c

def thetaFiniteSource : ThetaGlobal.FiniteFixedSource.Source (thetaRecipe K c)
    (thetaPeriod K (places K c) (probeData K c) (targetCharacter K c)) :=
  ThetaGlobal.FiniteFixedSource.source (thetaRecipe K c) (thetaRecipe_aligned K c)
    (thetaPeriod K (places K c) (probeData K c) (targetCharacter K c))

/-- Explicit local high K-type vectors, their actual one-place Whittaker
functionals, and their two local Mellin pairs.  No global reflection,
summability, coefficient table or cutoff estimate is assumed. -/
abbrev LocalHighKMellinInput := ThetaGlobal.FiniteLocalHighK.Input (thetaRecipe K c)
  (thetaPeriod K (places K c) (probeData K c) (targetCharacter K c)) (thetaFiniteSource K c)

namespace FiniteSkeletonSource

variable (L : LocalHighKMellinInput K c)

def data : FiniteMellinData K (places K c) :=
  ThetaGlobal.FiniteLocalHighK.finiteMellinData (thetaRecipe K c)
    (thetaPeriod K (places K c) (probeData K c) (targetCharacter K c))
    (thetaFiniteSource K c) L

theorem admissible : FiniteMellinAdmissible K (places K c) (data K c L) :=
  ThetaGlobal.ProjectedFiniteMellin.targetFiniteMellinData_admissible
    (thetaRecipe K c) (thetaFiniteSource K c).projected.base.factorization
    (thetaFiniteSource K c).transport
    (ThetaGlobal.FiniteLocalHighK.C₀ _ _ _ L)
    (ThetaGlobal.FiniteLocalHighK.C₀_ne_zero _ _ _ L)
    (ThetaGlobal.FiniteLocalHighK.A₀ _ _ _ L)
    (ThetaGlobal.FiniteLocalHighK.A₀_pos _ _ _ L)
    (thetaPeriod K (places K c) (probeData K c) (targetCharacter K c))

local notation "R" => thetaRecipe K c
local notation "C" => thetaFiniteSource K c
local notation "D" => C.projected.base.factorization
local notation "θ" => thetaPeriod K (places K c) (probeData K c) (targetCharacter K c)

theorem data_C₀ : (data K c L).C₀ =
    (ThetaGlobal.FiniteDirectMellin.cutoffVolume R C.transport C.projected.cutoffs : ℂ) *
      (∏ w : InfinitePlace K, L.directConstant w) /
      (∏ w : InfinitePlace K, L.reflectedConstant w) := rfl

theorem data_A₀ : (data K c L).A₀ = ∏ w : InfinitePlace K, L.scale w := rfl

def termClass (l : Fin (data K c L).terms) :
    ∀ p : R.A.Sf, ThetaGlobal.ProjectFiniteClass.LocalClass R.A p :=
  ThetaGlobal.ProjectedFiniteMellin.termClassEquiv R D C.transport
    (ThetaGlobal.FiniteLocalHighK.C₀ R θ C L)
    (ThetaGlobal.FiniteLocalHighK.C₀_ne_zero R θ C L)
    (ThetaGlobal.FiniteLocalHighK.A₀ R θ C L)
    (ThetaGlobal.FiniteLocalHighK.A₀_pos R θ C L) θ l

local instance (p : R.A.Sf) :
    MeasurableSpace (LocalIntegerRing K p.val)ˣ := borel _

local instance (p : R.A.Sf) : BorelSpace (LocalIntegerRing K p.val)ˣ := ⟨rfl⟩

/-- Literal shell formula for the skeleton's constructed table.  The
coefficient is integrated against the same source's actual unit Haar. -/
theorem coefficient_shell_spec
    (u : SixthUnitClasses K (places K c))
    (κ : SixthLocalClasses K (places K c))
    (l : Fin (data K c L).terms) (p : R.A.Sf) (k : ℤ) :
    (data K c L).coefficient u κ l p k =
      ∫ z,
        (if p = D.scalarSlot then
          ThetaGlobal.ProjectFiniteClass.reflectedClassMask R.A R.probe.correction.B R.σ κ
            (ThetaGlobal.ProjectFiniteClass.assemble R.A (termClass K c L l)) else 1) *
        (if (QuotientGroup.mk (ThetaGlobal.ProjectLocalShell.shellPoint K p.val k z) :
          ThetaGlobal.ProjectFiniteClass.LocalClass R.A p) = termClass K c L l p
          then 1 else 0) *
        (ThetaGlobal.TargetFinitePeriod.localPeriod R θ u p
          (ThetaGlobal.ProjectLocalShell.shellPoint K p.val k z) : ℂ) *
        ThetaGlobal.FiniteCanonicalVectors.weylValue R D p
          (ThetaGlobal.ProjectedFiniteMellin.normalizedSelectedVector R D u p)
          (ThetaGlobal.ProjectLocalShell.shellPoint K p.val k z)
        ∂ThetaGlobal.ProjectedFiniteMellin.unitHaar R C.transport p :=
  ThetaGlobal.ProjectedFiniteMellin.targetCoefficient_enumerated_spec R D C.transport
    (ThetaGlobal.FiniteLocalHighK.C₀ R θ C L)
    (ThetaGlobal.FiniteLocalHighK.C₀_ne_zero R θ C L)
    (ThetaGlobal.FiniteLocalHighK.A₀ R θ C L)
    (ThetaGlobal.FiniteLocalHighK.A₀_pos R θ C L) θ u κ l p k

end FiniteSkeletonSource

end HeckeSkeleton

#print axioms HeckeSkeleton.thetaFiniteSource
#print axioms HeckeSkeleton.FiniteSkeletonSource.admissible
