import HeckeGeneral.Analysis.MomentSlotScaleChange

/-!
# Source-family interface for the absolute prime endpoint

This interface uses the repository's actual `MomentData`, `pairedRows`, and
`slotProduct`.  It records the prime-geometry identification that is absent
from `WholeMomentProfileControl`.  It has no field asserting a prime bound
or a moment estimate.  An arbitrary dependent index type and an arbitrary
finite sector type retain all of the source's external parameters.

Keeping the source index and models as parameters also keeps this interface
independent of the unfinished `highExpansion` and `momentModels` definitions.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_PRIME

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Physical HeckeGeneral.ThetaSkeleton.Global
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]

/-- The structural data supplied by the source-model construction.  The
geometry equality preserves the actual fixed windows through both of the
existing data operations, while all masks and characters remain in `data`.
-/
structure PrimeEndpointFamily (g : PrimeWindowGeometry)
    (ω ψ : HeckeCharacter K) (Index : ℝ → ℝ → Type*) (Sector : Type*) where
  shell : ∀ Z T, Index Z T → ℝ
  shell_pos : ∀ Z T i, 0 < shell Z T i
  selected : ∀ Z T, Index Z T → Finset (Fin g.slots)
  data : ∀ Z T, Index Z T → Sector → MomentData K ω ψ
  parameters : ∀ Z T, Index Z T → RealParameters
  row_width : ∀ Z T i, (parameters Z T i).m + (parameters Z T i).q = 1
  geometry : ∀ Z T i s, (data Z T i s).geometry =
    ((momentPrimeGeometry K g).changeBase (shell Z T i) (shell_pos Z T i)).restrictSlots
      (selected Z T i)

variable {K} {g : PrimeWindowGeometry} {ω ψ : HeckeCharacter K}
  {Index : ℝ → ℝ → Type*} {Sector : Type*}

namespace PrimeEndpointFamily

def base (F : PrimeEndpointFamily K g ω ψ Index Sector) {Z T} (i : Index Z T) : ℝ :=
  Z ^ F.shell Z T i

def selectedLength (F : PrimeEndpointFamily K g ω ψ Index Sector)
    {Z T} (i : Index Z T) : ℝ :=
  ∑ _j ∈ F.selected Z T i,
    HeckeGeneral.ThetaSkeleton.TIP.slotLength g.slots (F.shell Z T i)

/-- Both `pairedRows` branches and every original common mask occur in the
literal finite energy.  No arbitrary rowwise energy is substituted. -/
def energy [Fintype Sector] (F : PrimeEndpointFamily K g ω ψ Index Sector)
    {Z T} (i : Index Z T) : ℝ :=
  ∑ s : Sector, ∑ u ∈ pairedRows (F.data Z T i s) (F.parameters Z T i) (F.base i),
    ‖slotProduct (F.data Z T i s) u (F.base i) 0‖ ^ 2

theorem one_le_base (F : PrimeEndpointFamily K g ω ψ Index Sector)
    {Z T} (i : Index Z T) (hZ : 1 ≤ Z) : 1 ≤ F.base i :=
  Real.one_le_rpow hZ (F.shell_pos Z T i).le

end PrimeEndpointFamily

end HeckeSkeleton.Moments.MOM_PRIME
