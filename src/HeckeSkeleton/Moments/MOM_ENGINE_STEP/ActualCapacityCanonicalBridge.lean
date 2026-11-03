import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalAllocatedCosts
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.NormalizedActualCapacityChild
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalProfileNormalizationInput
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondClassProduction
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.HybridNormalizedProduction

/-!
# The two actual capacity presentations use the same chosen child

The covered-source producer supplies a raw prime bound with its literal
profile amplitude factored out.  This file transports that producer's
already chosen deletion to the normalized-prime presentation.  It does
not choose another child.  The data, parameters, loss exponent and
envelope-free arithmetic cost agree exactly.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField DedekindZetaZeroFree
open HeckeGeneral.Characters HeckeGeneral.Analysis.ConditionalMoments

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {ω ψ : HeckeCharacter F} {k : ℕ}
variable {s : ActualAllocatedSource A V H k}

namespace ActualAllocatedSource.Calibration.CapacityInput

variable {D : s.Calibration (σ := σ) ω ψ} (I : D.CapacityInput)
variable (amplitude : V → ℝ) (hpos : ∀ ξ, 0 < amplitude ξ)
variable (bounds : Fin s.allocation.keep.card → ℝ) (hbounds : ∀ i, 0 ≤ bounds i)
variable (hfactor : ∀ ξ i, I.primeBound ξ i = amplitude ξ ^ 2 * bounds i)

theorem normalized_childData (keep : Finset (Fin s.allocation.keep.card)) (ξ : V) :
    (I.normalized amplitude hpos bounds hbounds hfactor).childData keep ξ =
      normalizedMomentProfiles (D.restrictedClippedData keep ξ) (amplitude ξ) (hpos ξ) := rfl

/-- The deletion and all geometric conclusions are those of the
original producer; only its proved energy inequality is rewritten. -/
def normalizedChild (c : D.CapacityChild I) :
    (I.normalized amplitude hpos bounds hbounds hfactor).Child where
  removed := c.removed
  width_nonneg := c.width_nonneg
  width_drop := c.width_le
  capacity := c.capacity
  energy := by
    intro ξ
    have hc := c.normalized_source_bound canonicalProfileNormalizationInput
      amplitude hpos bounds hfactor ξ
    change s.energy (σ := σ) ξ ≤
      c.envelopeFreeCost bounds * amplitude ξ ^ ((s.allocation.keep.card + 2) * 2) *
        pairedEnergy ((I.normalized amplitude hpos bounds hbounds hfactor).childData
          (Finset.univ \ c.removed) ξ) c.parameters s.base (D.height ξ)
    rw [I.normalized_childData amplitude hpos bounds hbounds hfactor]
    simpa only [CapacityChild.normalizedData, canonicalProfileNormalizationInput_normalize,
      CapacityChild.data] using hc

theorem normalizedChild_data (c : D.CapacityChild I) (ξ : V) :
    (I.normalizedChild amplitude hpos bounds hbounds hfactor c).data ξ =
      c.normalizedData canonicalProfileNormalizationInput amplitude hpos ξ := by
  rw [CapacityChild.normalizedData, canonicalProfileNormalizationInput_normalize]
  rfl

theorem normalizedChild_parameters (c : D.CapacityChild I) :
    (I.normalizedChild amplitude hpos bounds hbounds hfactor c).parameters = c.parameters := rfl

theorem normalizedChild_weight (c : D.CapacityChild I) :
    (I.normalizedChild amplitude hpos bounds hbounds hfactor c).weight =
      c.envelopeFreeCost bounds := rfl

end ActualAllocatedSource.Calibration.CapacityInput

namespace ActualAllocatedSource.Calibration.withCosts

variable (D : s.Calibration (σ := σ) ω ψ)
variable (rowCost scalarCost : ℝ) (fibers : ℕ)
variable (hrow : 0 ≤ rowCost) (hscalar : 0 ≤ scalarCost)
variable (row_bound : ∀ h ∈ s.rows, ‖s.weight h‖ ≤ rowCost)
variable (scalar_bound : ∀ h ∈ s.rows, ‖s.frozenScalar (σ := σ) h‖ ^ 2 ≤ scalarCost)
variable (fiber_bound : ∀ J : HeckeGeneral.Analysis.NonzeroIdeal F,
  (s.rows.filter (fun h => (s.row h).momentIdeal = J)).card ≤ fibers)

local notation "D'" => D.withCosts rowCost scalarCost fibers hrow hscalar row_bound scalar_bound fiber_bound

/-- Choosing the actual arithmetic costs retains every primitive
capacity input, including its original varying single-prime bound. -/
def capacityInput (I : D.CapacityInput) : (D').CapacityInput where
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
  left_window := I.left_window
  right_window := I.right_window
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
  prime_bound := I.prime_bound

theorem capacityInput_exponent (I : D.CapacityInput) :
    (capacityInput D rowCost scalarCost fibers hrow hscalar row_bound scalar_bound fiber_bound I).exponent =
      I.exponent := rfl

end ActualAllocatedSource.Calibration.withCosts

namespace SecondSideNormalization

variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {R : ActualSecondCorrelationRows A σ H ι}
variable {Ray : Type*} [CommGroup Ray] [Fintype Ray] {side : SecondColumnSide}
variable {f : SecondSideFrame (V := V) C R Ray side k}
variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal F)}
variable {heightDomain window : Set ℝ} {seminorms : Finset (ℕ × ℕ)}
variable (S : SecondSideNormalization f ω ψ rowDomain heightDomain window seminorms)

/-- Choose the original uniform single-prime constant in the actual
producer.  The precise Fourier amplitude is retained in its raw bound. -/
def withPrimeCost (primeCost : ℝ) (hcost : 0 ≤ primeCost)
    (hprime : ∀ ξ, ∀ u ∈ pairedRows (S.calibration.data ξ) S.calibration.parameters f.source.base,
      ∀ i : Fin f.source.allocation.keep.card,
      ‖primePolynomial (S.calibration.data ξ)
        (lengthSlot (S.calibration.data ξ) f.source.allocation.keep.card (S.calibration.count ξ) i)
          u f.source.base (S.calibration.height ξ)‖ ^ 2 ≤
        (S.amplitude ξ ^ 2 * primeCost) *
          f.source.base ^ (S.calibration.parameters.κ * f.source.childLength i)) :
    SecondSideNormalization f ω ψ rowDomain heightDomain window seminorms :=
  { S with
    capacity := { S.capacity with
      primeBound := fun ξ _ => S.amplitude ξ ^ 2 * primeCost
      primeBound_nonneg := fun ξ _ => mul_nonneg (sq_nonneg _) hcost
      prime_bound := hprime }
    bounds := fun _ => primeCost
    bounds_nonneg := fun _ => hcost
    factor := fun _ _ => rfl }

/-- The actual covered-source producer can use the selected arithmetic
costs directly.  This replaces the old bounds before choosing its child;
all source coefficients and all original profile representatives remain
the same. -/
def withCosts (rowCost scalarCost : ℝ) (fibers : ℕ)
    (hrow : 0 ≤ rowCost) (hscalar : 0 ≤ scalarCost)
    (row_bound : ∀ h ∈ f.source.rows, ‖f.source.weight h‖ ≤ rowCost)
    (scalar_bound : ∀ h ∈ f.source.rows, ‖f.source.frozenScalar (σ := σ) h‖ ^ 2 ≤ scalarCost)
    (fiber_bound : ∀ J : HeckeGeneral.Analysis.NonzeroIdeal F,
      (f.source.rows.filter (fun h => (f.source.row h).momentIdeal = J)).card ≤ fibers) :
    SecondSideNormalization f ω ψ rowDomain heightDomain window seminorms where
  calibration := S.calibration.withCosts rowCost scalarCost fibers hrow hscalar row_bound scalar_bound fiber_bound
  capacity := ActualAllocatedSource.Calibration.withCosts.capacityInput S.calibration
    rowCost scalarCost fibers hrow hscalar row_bound scalar_bound fiber_bound S.capacity
  amplitude := S.amplitude
  amplitude_pos := S.amplitude_pos
  bounds := S.bounds
  bounds_nonneg := S.bounds_nonneg
  factor := S.factor
  profile := S.profile

theorem withCosts_data (rowCost scalarCost : ℝ) (fibers : ℕ)
    (hrow : 0 ≤ rowCost) (hscalar : 0 ≤ scalarCost)
    (row_bound : ∀ h ∈ f.source.rows, ‖f.source.weight h‖ ≤ rowCost)
    (scalar_bound : ∀ h ∈ f.source.rows, ‖f.source.frozenScalar (σ := σ) h‖ ^ 2 ≤ scalarCost)
    (fiber_bound : ∀ J : HeckeGeneral.Analysis.NonzeroIdeal F,
      (f.source.rows.filter (fun h => (f.source.row h).momentIdeal = J)).card ≤ fibers) :
    (S.withCosts rowCost scalarCost fibers hrow hscalar row_bound scalar_bound fiber_bound).calibration.data =
      S.calibration.data := rfl

/-- The frozen-scalar field is computed from its original occurrence
allocation and individual factors.  No bound on a transformed family
or on a sum of labels is used to choose this normalization. -/
def withAllocationCosts
    (rowCost : ℝ) (fibers : ℕ) (hrow : 0 ≤ rowCost)
    (row_bound : ∀ h ∈ f.source.rows, ‖f.source.weight h‖ ≤ rowCost)
    (fiber_bound : ∀ J : HeckeGeneral.Analysis.NonzeroIdeal F,
      (f.source.rows.filter (fun h => (f.source.row h).momentIdeal = J)).card ≤ fibers)
    (annulus profile : Fin k → ℝ) (B : ℝ) (cap : ℕ) (hB : 1 ≤ B) (hcap : k ≤ cap)
    (hA : ∀ i, 0 ≤ annulus i) (hP : ∀ i, 0 ≤ profile i)
    (hfactor : ∀ i, annulus i * profile i ≤ B)
    (hsquarefree : Squarefree f.source.allocation.divisor)
    (hselection : f.source.allocation.selection ∈
      AllocationMass.idealAllocations f.source.allocation.divisor (k + 2))
    (hplain₁ : ∀ h ∈ f.source.rows,
      ‖sourcePlainCoefficient (f.source.characters h).plain (f.source.characters h).plainTwist
        (f.source.characters h).mask (f.source.allocation.plainDivisor 0)‖ ≤ 1)
    (hplain₂ : ∀ h ∈ f.source.rows,
      ‖sourcePlainCoefficient (f.source.characters h).plain (f.source.characters h).plainTwist
        (f.source.characters h).mask (f.source.allocation.plainDivisor (Fin.succ 0))‖ ≤ 1)
    (hprime : ∀ h ∈ f.source.rows, ∀ i ∈ Finset.univ \ f.source.allocation.keep,
      ‖sourcePrimeCoefficient ((f.source.characters h).slot i) ((f.source.characters h).slotTwist i)
        (f.source.characters h).mask (f.source.allocation.witness.2 i)‖ ≤ 1)
    (hannulus : ∀ i ∈ Finset.univ \ f.source.allocation.keep,
      (Ideal.absNorm (f.source.allocation.witness.2 i).asIdeal : ℝ) ≤
        annulus i * f.source.base ^ f.source.length i)
    (hprofile : ∀ h ∈ f.source.rows, ∀ i ∈ Finset.univ \ f.source.allocation.keep,
      ‖f.source.slotWeight h i (f.source.allocation.witness.2 i)‖ ^ 2 ≤ profile i) :
    SecondSideNormalization f ω ψ rowDomain heightDomain window seminorms :=
  S.withCosts rowCost (B ^ cap / (Ideal.absNorm f.source.allocation.divisor : ℝ)) fibers hrow
    (div_nonneg (pow_nonneg (zero_le_one.trans hB) _) (Nat.cast_nonneg _)) row_bound
    (f.source.frozenScalar_uniform_inverse_norm C annulus profile B cap hB hcap hA hP hfactor
      hsquarefree hselection hplain₁ hplain₂ hprime hannulus hprofile) fiber_bound

end SecondSideNormalization

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualAllocatedSource.Calibration.CapacityInput.normalizedChild
#print axioms HeckeSkeleton.Moments.EngineStep.ActualAllocatedSource.Calibration.CapacityInput.normalizedChild_weight
#print axioms HeckeSkeleton.Moments.EngineStep.SecondSideNormalization.withAllocationCosts
