import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualChildMass
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualCapacityCanonicalBridge
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.JointRowBudgetProduction

/-!
# Choose the actual arithmetic calibration before producing a child

The row cost is proved from the actual orbital scalar, common frozen
atoms and complete correlation.  The frozen allocation scalar supplies
its own inverse norm of the second divisor.  The original finite fibers
supply the remaining cost.  The capacity and profile inputs retain their
original geometry and representatives, and the producer is invoked only
after these three numerical fields have been chosen.

In particular, this construction never lowers the cost of a previously
selected child.  It can be applied after the joint row-budget filter:
the filter and the arithmetic cost choice both preserve the same actual
moving-mask dictionary.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Characters
open HeckeGeneral.Analysis.ConditionalMoments

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {H ι V : Type*} [Fintype ι] [DecidableEq ι]
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable [IsPrincipalIdealRing A.R]
variable {R : ActualSecondCorrelationRows A σ H ι}
variable {Ray : Type*} [CommGroup Ray] [Fintype Ray]
variable {ω ψ : HeckeCharacter F} {k l kLeft kRight : ℕ}

namespace SecondSideFrame

variable {side : SecondColumnSide}
variable (f : SecondSideFrame (V := V) C R Ray side k)

/-- Every original capacity datum is retained when the actual row,
allocation-scalar and original-fiber costs are chosen. -/
def arithmeticCapacityInput
    (cal : f.source.Calibration (σ := σ) ω ψ)
    (W : ActualSecondRowMass R C kLeft kRight)
    (B : f.source.FrozenAtomBounds) (I : cal.CapacityInput) :
    (f.arithmeticCalibration cal W B).CapacityInput :=
  ActualAllocatedSource.Calibration.withCosts.capacityInput cal
    W.rowBound B.scalarBound W.originalFiber W.rowBound_nonneg B.scalarBound_nonneg
    (fun h _ => by
      rw [f.source_row_weight]
      exact W.row_bound h.val (Finset.mem_filter.mp h.property).1)
    (B.scalar_bound C)
    (fun J => by
      simpa only [f.source_rows, f.source_row_momentIdeal] using W.extracted_fibers J) I

@[simp] theorem arithmeticCapacityInput_exponent
    (cal : f.source.Calibration (σ := σ) ω ψ)
    (W : ActualSecondRowMass R C kLeft kRight)
    (B : f.source.FrozenAtomBounds) (I : cal.CapacityInput) :
    (f.arithmeticCapacityInput cal W B I).exponent = I.exponent := rfl

@[simp] theorem arithmeticCapacityInput_primeBound
    (cal : f.source.Calibration (σ := σ) ω ψ)
    (W : ActualSecondRowMass R C kLeft kRight)
    (B : f.source.FrozenAtomBounds) (I : cal.CapacityInput) :
    (f.arithmeticCapacityInput cal W B I).primeBound = I.primeBound := rfl

end SecondSideFrame

namespace SecondSideNormalization

variable {side : SecondColumnSide}
variable {f : SecondSideFrame (V := V) C R Ray side k}
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal F)}
variable {heightDomain window : Set ℝ} {seminorms : Finset (ℕ × ℕ)}
variable (N : SecondSideNormalization f ω ψ rowDomain heightDomain window seminorms)
variable (W : ActualSecondRowMass R C kLeft kRight)
variable (B : f.source.FrozenAtomBounds)

/-- The actual arithmetic costs are chosen at the normalization-input
stage, before any fixed deletion or child family is selected. -/
def arithmeticCalibration :
    SecondSideNormalization f ω ψ rowDomain heightDomain window seminorms where
  calibration := f.arithmeticCalibration N.calibration W B
  capacity := f.arithmeticCapacityInput N.calibration W B N.capacity
  amplitude := N.amplitude
  amplitude_pos := N.amplitude_pos
  bounds := N.bounds
  bounds_nonneg := N.bounds_nonneg
  factor := N.factor
  profile := N.profile

@[simp] theorem arithmeticCalibration_calibration :
    (N.arithmeticCalibration W B).calibration =
      f.arithmeticCalibration N.calibration W B := rfl

@[simp] theorem arithmeticCalibration_data :
    (N.arithmeticCalibration W B).calibration.data = N.calibration.data := rfl

@[simp] theorem arithmeticCalibration_parameters :
    (N.arithmeticCalibration W B).calibration.parameters = N.calibration.parameters := rfl

@[simp] theorem arithmeticCalibration_height :
    (N.arithmeticCalibration W B).calibration.height = N.calibration.height := rfl

@[simp] theorem arithmeticCalibration_amplitude :
    (N.arithmeticCalibration W B).amplitude = N.amplitude := rfl

@[simp] theorem arithmeticCalibration_bounds :
    (N.arithmeticCalibration W B).bounds = N.bounds := rfl

@[simp] theorem arithmeticCalibration_mass :
    (N.arithmeticCalibration W B).calibration.mass =
      W.rowBound * (B.envelope / (Ideal.absNorm f.source.allocation.divisor : ℝ)) *
        (W.originalFiber : ℝ) := rfl

/-- The representation by the original fixed ambient mask and the
actual squarefree moving mask survives the arithmetic choice. -/
def arithmeticCalibration_maskRecipe
    (M : ActualMovingMaskRecipe A N.calibration.data) :
    ActualMovingMaskRecipe A (N.arithmeticCalibration W B).calibration.data := M

/-- The row filter changes the enumerated data and its source dictionary;
the arithmetic choice changes only the three cost fields.  Both orders
therefore give the same normalization input, before child selection. -/
theorem arithmeticCalibration_withJointRowBudget
    (M : ActualMovingMaskRecipe A N.calibration.data)
    (hsource : ∀ h ∈ f.source.rows,
      A.exteriorNorm (f.source.originalIdeal h) *
        A.exteriorNorm (M.support (f.source.row h).momentIdeal) ≤
          f.source.normFactor h * f.source.base ^
            (N.calibration.parameters.m + N.calibration.parameters.q)) :
    (N.withJointRowBudget M hsource).arithmeticCalibration W B =
      (N.arithmeticCalibration W B).withJointRowBudget
        (N.arithmeticCalibration_maskRecipe W B M) hsource := rfl

theorem arithmeticCalibration_withJointRowBudget_calibration
    (M : ActualMovingMaskRecipe A N.calibration.data)
    (hsource : ∀ h ∈ f.source.rows,
      A.exteriorNorm (f.source.originalIdeal h) *
        A.exteriorNorm (M.support (f.source.row h).momentIdeal) ≤
          f.source.normFactor h * f.source.base ^
            (N.calibration.parameters.m + N.calibration.parameters.q)) :
    ((N.arithmeticCalibration W B).withJointRowBudget
      (N.arithmeticCalibration_maskRecipe W B M) hsource).calibration =
      f.arithmeticCalibration (N.calibration.withJointRowBudget M hsource) W B := rfl

/-- This equality is between the literal capacity records, not merely
their numerical exponents.  The rowwise hypotheses are restricted to
the same filtered rows in either order. -/
theorem arithmeticCalibration_withJointRowBudget_capacity
    (M : ActualMovingMaskRecipe A N.calibration.data)
    (hsource : ∀ h ∈ f.source.rows,
      A.exteriorNorm (f.source.originalIdeal h) *
        A.exteriorNorm (M.support (f.source.row h).momentIdeal) ≤
          f.source.normFactor h * f.source.base ^
            (N.calibration.parameters.m + N.calibration.parameters.q)) :
    ((N.arithmeticCalibration W B).withJointRowBudget
      (N.arithmeticCalibration_maskRecipe W B M) hsource).capacity =
      f.arithmeticCapacityInput (N.calibration.withJointRowBudget M hsource) W B
        (N.capacity.withJointRowBudget M hsource) := rfl

/-- This is the literal envelope-free cost of whichever child the new
calibration produces.  The common correlation occurs in rowBound once;
the independent second divisor occurs in the frozen allocation scalar. -/
theorem arithmeticCalibration_child_cost
    (c : (N.arithmeticCalibration W B).calibration.CapacityChild
      (N.arithmeticCalibration W B).capacity) :
    c.envelopeFreeCost (N.arithmeticCalibration W B).bounds =
      (W.rowBound * (B.envelope / (Ideal.absNorm f.source.allocation.divisor : ℝ)) *
        (W.originalFiber : ℝ)) *
        ((∏ i ∈ c.removed, N.bounds i) * f.source.base ^ N.capacity.exponent) := rfl

variable {left : SecondSideFrame (V := V) C R Ray .left k}
variable {right : SecondSideFrame (V := V) C R Ray .right l}

/-- The genuine producer is called on the two canonical arithmetic
calibrations.  The result contains its actual fixed deletions, and can
be transported to the normalized-capacity presentation without making
a second choice. -/
theorem produce_arithmetic
    (P : ProfileNormalizationInput F ω ψ)
    (L : SecondSideNormalization left ω ψ rowDomain heightDomain window seminorms)
    (R₀ : SecondSideNormalization right ω ψ rowDomain heightDomain window seminorms)
    (W : ActualSecondRowMass R C kLeft kRight)
    (BL : left.source.FrozenAtomBounds) (BR : right.source.FrozenAtomBounds) :
    Produced P (L.arithmeticCalibration W BL) (R₀.arithmeticCalibration W BR) :=
  produce P (L.arithmeticCalibration W BL) (R₀.arithmeticCalibration W BR)

end SecondSideNormalization

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.SecondSideFrame.arithmeticCapacityInput
#print axioms HeckeSkeleton.Moments.EngineStep.SecondSideNormalization.arithmeticCalibration
#print axioms HeckeSkeleton.Moments.EngineStep.SecondSideNormalization.produce_arithmetic

