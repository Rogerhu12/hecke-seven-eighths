import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SideGeometryData
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalOriginalPrimeAnalyticProvider

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# N6: fixed original analytic choices and normalization of the same side

The choices precede every call. N3 and N4 supply one actual calibration,
its complete source conditions and its original sixth-root geometry.
N5b supplies the raw and clipped windows at the same polynomial radius.
The conclusion constructs FullKappaProfileInput on these data. Its
capacity and child-profile connection are then the literal base
constructions, not independent fields that could select another child.

Paper: lines 2927--2946 and 3043--3073. This is a candidate contract.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open EngineStep EngineInduction EngineInduction.Source

variable {K : Type} [Field K] [NumberField K]

/-- Every pre-removal slot and both plain profiles on both sides. -/
def fullKappaProfilePower (c : TargetContext K) : ℕ :=
  (c.geometry.slots + 2) + (c.geometry.slots + 2)

def fullKappaLengthBound (c : TargetContext K) : ℝ := (momentMesh K c.family).val

/-- Original analytic input and numerical constants only. No allocated
source, normalized child, prime-sum or kernel estimate is a field. -/
structure FullKappaChoices (c : TargetContext K) (loss : ℝ) where
  heightC : ℝ
  heightC_pos : 0 < heightC
  window : CanonicalOriginalPrimeAnalyticProvider.Window
    (A := Arithmetic.data c) (P := probeData K c) (R := momentRowCharacters K c)
    (Expansion.Project.canonicalDetectorTheta K (targetCharacter K c)) 2 heightC
  contour : ℝ
  contour_pos : 0 < contour
  contour_le_quarter : contour ≤ 1 / 4
  radiusConstant : ℝ
  radiusConstant_one_le : 1 ≤ radiusConstant
  radius_power : ∀ Z : ℝ, 1 ≤ Z →
    CanonicalFullKappaPrime.radiusFactor K Z contour (fullKappaLengthBound c)
      (CanonicalHeckePrimeAnalytic.degreeBound K) (heightC * (1 + Real.log Z))
      (CompleteMovingRowRecipe.primeMaskLogBound (Arithmetic.data c) Z 2) ^
        fullKappaProfilePower c ≤ radiusConstant ^ fullKappaProfilePower c * Z ^ loss

variable {c : TargetContext K} {call : Call c}
variable {H Row ι : Type} [Fintype ι] [DecidableEq ι] {k : ℕ}
variable {R : ActualSecondCorrelationRows (Arithmetic.data c) (Arithmetic.embedding c) H ι}
variable {side : Bool}
variable {s : ActualAllocatedSource (Arithmetic.data c) EngineParameter Row k}
variable {D : OriginalCalibration call s} {loss B : ℝ} {J₁ J₂ : ℕ}

/-- N5b controls the same raw and clipped profiles by one common
polynomial radius. The raw positive window is retained for N7b. -/
structure FullKappaWindows (D : OriginalCalibration call s) (B : ℝ) (J₁ J₂ : ℕ) where
  coefficient_nonneg : 0 ≤ B
  raw : ∀ ξ, RawProfileWindow Set.univ Set.univ call.window call.childOrders
    (D.calibration.data ξ) (polynomialProfileRadius B J₁ J₂ (WithLp.ofLp ξ))
  clipped : ∀ ξ, RawProfileWindow Set.univ Set.univ
    (Set.Icc 0 (2 * call.prepared.upper)) call.childOrders (D.calibration.clippedData ξ)
    (polynomialProfileRadius B J₁ J₂ (WithLp.ofLp ξ))

namespace FullKappaWindows

/-- Only the support inclusion is weakened. Every representative and
its exact pointwise identity and seminorm bound remain unchanged. -/
def broadRaw (windows : FullKappaWindows D B J₁ J₂) (ξ : EngineParameter) :
    RawProfileWindow Set.univ Set.univ (Set.Icc 0 (2 * call.prepared.upper))
      call.childOrders (D.calibration.data ξ)
      (polynomialProfileRadius B J₁ J₂ (WithLp.ofLp ξ)) := by
  have inclusion : call.window ⊆ Set.Icc 0 (2 * call.prepared.upper) := by
    intro x hx
    exact ⟨(call.window_positive hx).le, hx.2⟩
  exact { windows.raw ξ with
    inverse_support := fun u hu t ht =>
      ((windows.raw ξ).inverse_support u hu t ht).trans inclusion
    left_support := fun u hu t ht =>
      ((windows.raw ξ).left_support u hu t ht).trans inclusion
    right_support := fun u hu t ht =>
      ((windows.raw ξ).right_support u hu t ht).trans inclusion
    prime_support := fun i t ht => ((windows.raw ξ).prime_support i t ht).trans inclusion }

end FullKappaWindows

/-- The actual raw/clipped windows are bound to those supplied by N5b.
The complete fixed norm box two retains every factor of the full mask. -/
structure FullKappaSideResult (choices : FullKappaChoices c loss)
    (G : SideGeometryData R side s D) (windows : FullKappaWindows D B J₁ J₂) where
  profiles : D.calibration.FullKappaProfileInput D.recipe Set.univ Set.univ
    (Set.Icc 0 (2 * call.prepared.upper)) call.childOrders B J₁ J₂
    choices.contour (fullKappaLengthBound c) (choices.heightC * (1 + Real.log s.base)) 2
  raw_eq : profiles.raw = windows.broadRaw
  clipped_eq : profiles.clipped = windows.clipped
  annulus_eq : profiles.annulus = max 1 (2 * call.prepared.upper)

namespace FullKappaSideResult

variable {choices : FullKappaChoices c loss} {G : SideGeometryData R side s D}
variable {windows : FullKappaWindows D B J₁ J₂}

/-- Capacity is the existing base construction on this very result. -/
def capacity (result : FullKappaSideResult choices G windows) :
    D.calibration.NormalizedCapacityData := G.normalization result.profiles

/-- Every result, including one obtained through the public existential
task, has this exact radius with the original fixed analytic choices. -/
theorem capacity_radius (result : FullKappaSideResult choices G windows)
    (ξ : EngineParameter) :
    result.capacity.radius ξ = polynomialProfileRadius
      (CanonicalFullKappaPrime.enlargedCoefficient B
        (CanonicalFullKappaPrime.radiusFactor K s.base choices.contour (fullKappaLengthBound c)
          (CanonicalHeckePrimeAnalytic.degreeBound K)
          (choices.heightC * (1 + Real.log s.base))
          (CompleteMovingRowRecipe.primeMaskLogBound (Arithmetic.data c) s.base 2)))
      J₁ J₂ (WithLp.ofLp ξ) := rfl

theorem capacity_primeBound (result : FullKappaSideResult choices G windows)
    (i : Fin s.allocation.keep.card) : result.capacity.primeBound i = 1 := rfl

end FullKappaSideResult

/-- A target-level fixed choice precedes every scale, source, side and
Fourier parameter. Only earlier tasks' original data and windows enter
the single-side construction. -/
def FullKappaTask (c : TargetContext K) : Prop :=
  ∀ loss : ℝ, 0 < loss → ∃ choices : FullKappaChoices c loss,
    ∀ (call : Call c) {H Row ι : Type} [Fintype ι] [DecidableEq ι] {k : ℕ}
      {R : ActualSecondCorrelationRows (Arithmetic.data c) (Arithmetic.embedding c) H ι}
      {side : Bool} {s : ActualAllocatedSource (Arithmetic.data c) EngineParameter Row k}
      (D : OriginalCalibration call s) (G : SideGeometryData R side s D),
      D.SourceConditions → ∀ (B : ℝ) (J₁ J₂ : ℕ) (windows : FullKappaWindows D B J₁ J₂),
        Nonempty (FullKappaSideResult choices G windows)

end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.FullKappaSideResult.capacity_radius
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.FullKappaSideResult.capacity_primeBound
