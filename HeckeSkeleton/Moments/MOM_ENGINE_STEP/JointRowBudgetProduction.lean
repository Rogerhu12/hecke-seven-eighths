import HeckeSkeleton.Moments.MOM_ENGINE_STEP.JointRowBudget
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondClassProduction

/-!
# Produce the actual children after the joint row-budget filter

The old length ledger and single-prime bounds are transported to the
smaller actual row set.  The profile representatives are unchanged.
The capacity producer is then called on the filtered calibration itself;
an energy inequality for an old larger child is never reused.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {ω ψ : HeckeCharacter F}

/-- Literal profile representatives and every original window survive
a restriction of the row enumeration. -/
def RawProfileWindow.withJointRowBudget
    {rowDomain : Set (NonzeroIdeal F)} {heightDomain window : Set ℝ}
    {seminorms : Finset (ℕ × ℕ)} {d : MomentData F ω ψ} {radius : ℝ}
    (raw : RawProfileWindow rowDomain heightDomain window seminorms d radius)
    (support : NonzeroIdeal F → A.Exterior) (budget : ℝ) :
    RawProfileWindow rowDomain heightDomain window seminorms
      (jointRowBudgetData d support budget) radius where
  inverseRep := raw.inverseRep
  leftRep := raw.leftRep
  rightRep := raw.rightRep
  primeRep := raw.primeRep
  inverse_eq := raw.inverse_eq
  left_eq := raw.left_eq
  right_eq := raw.right_eq
  prime_eq := raw.prime_eq
  inverse_support := raw.inverse_support
  left_support := raw.left_support
  right_support := raw.right_support
  prime_support := raw.prime_support
  inverse_bound := raw.inverse_bound
  left_bound := raw.left_bound
  right_bound := raw.right_bound
  prime_bound := raw.prime_bound

namespace ActualAllocatedSource.Calibration

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {k : ℕ}
variable {s : ActualAllocatedSource A V H k}
variable (D : s.Calibration (σ := σ) ω ψ)
variable (M : ActualMovingMaskRecipe A D.data)
variable (hsource : ∀ h ∈ s.rows,
  A.exteriorNorm (s.originalIdeal h) *
    A.exteriorNorm (M.support (s.row h).momentIdeal) ≤
      s.normFactor h * s.base ^ (D.parameters.m + D.parameters.q))

theorem withJointRowBudget_rows_subset (ξ : V) :
    pairedRows ((D.withJointRowBudget M hsource).data ξ) D.parameters s.base ⊆
      pairedRows (D.data ξ) D.parameters s.base := by
  change pairedRows (jointRowBudgetData (D.data ξ) M.support
    (s.base ^ (D.parameters.m + D.parameters.q))) D.parameters s.base ⊆ _
  rw [pairedRows_jointRowBudgetData]
  exact Finset.filter_subset _ _

theorem withJointRowBudget_clippedData (ξ : V) :
    (D.withJointRowBudget M hsource).clippedData ξ =
      jointRowBudgetData (D.clippedData ξ) M.support
        (s.base ^ (D.parameters.m + D.parameters.q)) := rfl

namespace CapacityInput

variable {D} (I : D.CapacityInput)

/-- No capacity estimate is a new premise: all numerical fields are
the original ledger, and its three rowwise analytic fields restrict
along the actual finite-row inclusion proved above. -/
def withJointRowBudget (I : D.CapacityInput)
    (M : ActualMovingMaskRecipe A D.data)
    (hsource : ∀ h ∈ s.rows,
      A.exteriorNorm (s.originalIdeal h) *
        A.exteriorNorm (M.support (s.row h).momentIdeal) ≤
          s.normFactor h * s.base ^ (D.parameters.m + D.parameters.q)) :
    (D.withJointRowBudget M hsource).CapacityInput where
  skeleton := I.skeleton
  b₂ := I.b₂
  p₂ := I.p₂
  boundary := I.boundary
  ell := I.ell
  gap := I.gap
  delta := I.delta
  mesh := I.mesh
  supportError := I.supportError
  rawClipError := I.rawClipError
  widthError := I.widthError
  leftAnnulus := I.leftAnnulus
  rightAnnulus := I.rightAnnulus
  leftAnnulus_one := I.leftAnnulus_one
  rightAnnulus_one := I.rightAnnulus_one
  left_window ξ u hu := I.left_window ξ u (D.withJointRowBudget_rows_subset M hsource ξ hu)
  right_window ξ u hu := I.right_window ξ u (D.withJointRowBudget_rows_subset M hsource ξ hu)
  gap_pos := I.gap_pos
  kappa_pos := I.kappa_pos
  mesh_nonneg := I.mesh_nonneg
  mesh_bound := I.mesh_bound
  enlargement := I.enlargement
  unit_part := I.unit_part
  actual_width := I.actual_width
  delta_bound := I.delta_bound
  principal_part := I.principal_part
  boundary_nonneg := I.boundary_nonneg
  parent_capacity := I.parent_capacity
  common_part := I.common_part
  paid_shift := I.paid_shift
  raw_degree := I.raw_degree
  width_error := I.width_error
  budget_nonneg := I.budget_nonneg
  charge_nonneg := I.charge_nonneg
  primeBound := I.primeBound
  primeBound_nonneg := I.primeBound_nonneg
  prime_bound ξ u hu i := I.prime_bound ξ u
    (D.withJointRowBudget_rows_subset M hsource ξ hu) i

@[simp] theorem withJointRowBudget_exponent :
    (I.withJointRowBudget M hsource).exponent = I.exponent := rfl

@[simp] theorem withJointRowBudget_allowance
    (removed : Finset (Fin s.allocation.keep.card)) (ξ : V) :
    (I.withJointRowBudget M hsource).allowance removed ξ = I.allowance removed ξ := rfl

end CapacityInput
end ActualAllocatedSource.Calibration

namespace SecondSideNormalization

variable {V H ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable [Fintype ι] [DecidableEq ι]
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {R : ActualSecondCorrelationRows A σ H ι}
variable {Ray : Type*} [CommGroup Ray] [Fintype Ray]
variable {side : SecondColumnSide} {k l : ℕ}
variable {f : SecondSideFrame (V := V) C R Ray side k}
variable {rowDomain : Set (NonzeroIdeal F)}
variable {heightDomain window : Set ℝ} {seminorms : Finset (ℕ × ℕ)}
variable (N : SecondSideNormalization f ω ψ rowDomain heightDomain window seminorms)
variable (M : ActualMovingMaskRecipe A N.calibration.data)
variable (hsource : ∀ h ∈ f.source.rows,
  A.exteriorNorm (f.source.originalIdeal h) *
    A.exteriorNorm (M.support (f.source.row h).momentIdeal) ≤
      f.source.normFactor h * f.source.base ^
        (N.calibration.parameters.m + N.calibration.parameters.q))

/-- This is the normalization input of the filtered source calibration.
The actual capacity producer will choose its child only afterwards. -/
def withJointRowBudget :
    SecondSideNormalization f ω ψ rowDomain heightDomain window seminorms where
  calibration := N.calibration.withJointRowBudget M hsource
  capacity := N.capacity.withJointRowBudget M hsource
  amplitude := N.amplitude
  amplitude_pos := N.amplitude_pos
  bounds := N.bounds
  bounds_nonneg := N.bounds_nonneg
  factor := N.factor
  profile ξ := by
    rw [N.calibration.withJointRowBudget_clippedData M hsource ξ]
    exact (N.profile ξ).withJointRowBudget M.support
      (f.source.base ^ (N.calibration.parameters.m + N.calibration.parameters.q))

@[simp] theorem withJointRowBudget_mass :
    (N.withJointRowBudget M hsource).calibration.mass = N.calibration.mass := rfl

@[simp] theorem withJointRowBudget_amplitude :
    (N.withJointRowBudget M hsource).amplitude = N.amplitude := rfl

def withJointRowBudget_maskRecipe :
    ActualMovingMaskRecipe A (N.withJointRowBudget M hsource).calibration.data :=
  N.calibration.withJointRowBudget_maskRecipe M hsource

variable {left : SecondSideFrame (V := V) C R Ray .left k}
variable {right : SecondSideFrame (V := V) C R Ray .right l}

/-- The same source energy now produces children whose calibration
already contains the correct joint row-mask filter. -/
theorem produce_withJointRowBudget
    (P : ProfileNormalizationInput F ω ψ)
    (L : SecondSideNormalization left ω ψ rowDomain heightDomain window seminorms)
    (R₀ : SecondSideNormalization right ω ψ rowDomain heightDomain window seminorms)
    (ML : ActualMovingMaskRecipe A L.calibration.data)
    (MR : ActualMovingMaskRecipe A R₀.calibration.data)
    (hleft : ∀ h ∈ left.source.rows,
      A.exteriorNorm (left.source.originalIdeal h) *
        A.exteriorNorm (ML.support (left.source.row h).momentIdeal) ≤
          left.source.normFactor h * left.source.base ^
            (L.calibration.parameters.m + L.calibration.parameters.q))
    (hright : ∀ h ∈ right.source.rows,
      A.exteriorNorm (right.source.originalIdeal h) *
        A.exteriorNorm (MR.support (right.source.row h).momentIdeal) ≤
          right.source.normFactor h * right.source.base ^
            (R₀.calibration.parameters.m + R₀.calibration.parameters.q)) :
    Produced P (L.withJointRowBudget ML hleft) (R₀.withJointRowBudget MR hright) :=
  produce P (L.withJointRowBudget ML hleft) (R₀.withJointRowBudget MR hright)

end SecondSideNormalization

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualAllocatedSource.Calibration.CapacityInput.withJointRowBudget
#print axioms HeckeSkeleton.Moments.EngineStep.SecondSideNormalization.withJointRowBudget
#print axioms HeckeSkeleton.Moments.EngineStep.SecondSideNormalization.produce_withJointRowBudget

