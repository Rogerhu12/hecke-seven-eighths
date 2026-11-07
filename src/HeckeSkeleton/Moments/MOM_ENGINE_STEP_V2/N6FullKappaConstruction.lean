module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N6OriginalAnalytic

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# N6: construct normalization from the original single-profile windows

The two windows are exactly the raw and clipped conclusions of N5b,
at one common original polynomial radius. The fixed analytic choices
enlarge only the common positive radius, before base chooses whole
slots. No full-kappa input, normalized capacity, prime-sum bound, child
energy estimate or kernel estimate is a premise of this construction.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.N6

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open PrimeCancellation.Analytic
open EngineStep EngineInduction EngineInduction.Source Blueprint

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c}
variable {H Row ι : Type} [Fintype ι] [DecidableEq ι] {k : ℕ}
variable {R : ActualSecondCorrelationRows (Arithmetic.data c) (Arithmetic.embedding c) H ι}
variable {side : Bool}
variable {s : ActualAllocatedSource (Arithmetic.data c) EngineParameter Row k}
variable {D : OriginalCalibration call s} {loss B : ℝ} {J₁ J₂ : ℕ}

variable (choices : FullKappaChoices c loss) (G : SideGeometryData R side s D)
variable (conditions : D.SourceConditions) (windows : FullKappaWindows D B J₁ J₂)

/-- All fields are derived from the original geometry, source
conditions, N5b profile windows and the target's analytic provider. -/
def fullKappaInput :
    D.calibration.FullKappaProfileInput D.recipe Set.univ Set.univ
      (Set.Icc 0 (2 * call.prepared.upper)) call.childOrders B J₁ J₂
      choices.contour (fullKappaLengthBound c) (choices.heightC * (1 + Real.log s.base)) 2 where
  coefficient_nonneg := windows.coefficient_nonneg
  orders := call.fixedRange.childOrders_prime ∅ call.childOrder call.frame.decay
  raw := windows.broadRaw
  clipped := windows.clipped
  annulus := max 1 (2 * call.prepared.upper)
  annulus_one := le_max_left _ _
  window_upper := fun _ hx => hx.2.trans (le_max_right _ _)
  prime_support ξ i :=
    (conditions.primeSupport ξ).rawProfileWindow (windows.raw ξ) i (D.calibration.height ξ)
  rows := fun _ _ _ => Set.mem_univ _
  height := fun _ => Set.mem_univ _
  delta_pos := choices.contour_pos
  delta_le := choices.contour_le_quarter
  length_nonneg := G.mesh_nonneg
  length_le := childLength_le_mesh D
  kappa_lower := by rw [D.kappa_eq]; exact call.domain.kappa_lower
  kappa_upper := by rw [D.kappa_eq]; exact call.domain.kappa_upper
  full_support := fullJointBudget_two G conditions.joint
  analytic hκ ξ u hu i :=
    (slotCertificate choices G conditions hκ ξ u hu
      (lengthSlot (D.calibration.data ξ) s.allocation.keep.card (D.calibration.count ξ) i)).val
  analytic_height hκ ξ u hu i :=
    (slotCertificate choices G conditions hκ ξ u hu
      (lengthSlot (D.calibration.data ξ) s.allocation.keep.card (D.calibration.count ξ) i)).property

/-- The output fixes both sets of original representatives and their
annulus. Capacity and the child-profile connection are derived by the
contract's literal base constructors. -/
def sideResult : FullKappaSideResult choices G windows where
  profiles := fullKappaInput choices G conditions windows
  raw_eq := rfl
  clipped_eq := rfl
  annulus_eq := rfl

/-- The exact polynomial radius is available to N9, with the same
fixed contour, norm box and analytic height used by this normalization. -/
theorem capacity_radius (ξ : EngineParameter) :
    (sideResult choices G conditions windows).capacity.radius ξ =
      polynomialProfileRadius
        (CanonicalFullKappaPrime.enlargedCoefficient B
          (CanonicalFullKappaPrime.radiusFactor K s.base choices.contour (fullKappaLengthBound c)
            (CanonicalHeckePrimeAnalytic.degreeBound K)
            (choices.heightC * (1 + Real.log s.base))
            (CompleteMovingRowRecipe.primeMaskLogBound (Arithmetic.data c) s.base 2)))
        J₁ J₂ (WithLp.ofLp ξ) := rfl

theorem capacity_primeBound (i : Fin s.allocation.keep.card) :
    (sideResult choices G conditions windows).capacity.primeBound i = 1 := rfl

end HeckeSkeleton.Moments.EngineStepV2.N6

#print axioms HeckeSkeleton.Moments.EngineStepV2.N6.fullKappaInput
#print axioms HeckeSkeleton.Moments.EngineStepV2.N6.sideResult
#print axioms HeckeSkeleton.Moments.EngineStepV2.N6.capacity_radius
#print axioms HeckeSkeleton.Moments.EngineStepV2.N6.capacity_primeBound
