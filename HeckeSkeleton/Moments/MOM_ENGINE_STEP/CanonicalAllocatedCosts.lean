import HeckeSkeleton.Moments.MOM_ENGINE_STEP.NormalizedCapacityChild
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.AllocationScalarNorm

/-!
# Choose the costs of the actual allocated source

A raw calibration is allowed to overestimate its row, frozen-scalar and
fiber costs.  A mass theorem must therefore choose these fields from
the original factors.  The constructions below replace only those
three bounds, retaining the actual data, characters, profiles, masks,
parameters, supports and source dictionary.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Characters HeckeGeneral.Analysis.ConditionalMoments
open HeckePort.IdealMobiusDivisorSum

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {ω ψ : HeckeCharacter F} {k : ℕ}

/-- A previously fixed factor bound and slot cap dominate any selected
product.  The selected set remains the actual one. -/
theorem selected_factor_product_le {ι : Type*} [Fintype ι]
    (keep : Finset ι) (f : ι → ℝ) (B : ℝ) (cap : ℕ)
    (hB : 1 ≤ B) (hcap : Fintype.card ι ≤ cap)
    (hnonneg : ∀ i ∈ keep, 0 ≤ f i) (hbound : ∀ i ∈ keep, f i ≤ B) :
    (∏ i ∈ keep, f i) ≤ B ^ cap := by
  calc
    _ ≤ ∏ _i ∈ keep, B := Finset.prod_le_prod₀ hnonneg hbound
    _ = B ^ keep.card := Finset.prod_const B
    _ ≤ B ^ cap := pow_le_pow_right₀ hB
      ((Finset.card_le_card (Finset.subset_univ keep)).trans
        (by simpa only [Finset.card_univ] using hcap))

namespace ActualAllocatedSource

variable (s : ActualAllocatedSource A V H k)

/-- The actual scalar obtains its inverse norm from the second divisor,
using the original individual central, annular and profile factors. -/
theorem frozenScalar_uniform_inverse_norm
    (C : A.GeneralArithmeticContext σ η hS)
    (annulus profile : Fin k → ℝ) (B : ℝ) (cap : ℕ) (hB : 1 ≤ B) (hcap : k ≤ cap)
    (hA : ∀ i, 0 ≤ annulus i) (hP : ∀ i, 0 ≤ profile i)
    (hfactor : ∀ i, annulus i * profile i ≤ B)
    (hsquarefree : Squarefree s.allocation.divisor)
    (hselection : s.allocation.selection ∈
      AllocationMass.idealAllocations s.allocation.divisor (k + 2))
    (hplain₁ : ∀ h ∈ s.rows,
      ‖sourcePlainCoefficient (s.characters h).plain (s.characters h).plainTwist
        (s.characters h).mask (s.allocation.plainDivisor 0)‖ ≤ 1)
    (hplain₂ : ∀ h ∈ s.rows,
      ‖sourcePlainCoefficient (s.characters h).plain (s.characters h).plainTwist
        (s.characters h).mask (s.allocation.plainDivisor (Fin.succ 0))‖ ≤ 1)
    (hprime : ∀ h ∈ s.rows, ∀ i ∈ Finset.univ \ s.allocation.keep,
      ‖sourcePrimeCoefficient ((s.characters h).slot i) ((s.characters h).slotTwist i)
        (s.characters h).mask (s.allocation.witness.2 i)‖ ≤ 1)
    (hannulus : ∀ i ∈ Finset.univ \ s.allocation.keep,
      (Ideal.absNorm (s.allocation.witness.2 i).asIdeal : ℝ) ≤ annulus i * s.base ^ s.length i)
    (hprofile : ∀ h ∈ s.rows, ∀ i ∈ Finset.univ \ s.allocation.keep,
      ‖s.slotWeight h i (s.allocation.witness.2 i)‖ ^ 2 ≤ profile i) :
    ∀ h ∈ s.rows, ‖s.frozenScalar (σ := σ) h‖ ^ 2 ≤
      B ^ cap / (Ideal.absNorm s.allocation.divisor : ℝ) := by
  intro h hh
  apply (s.allocation.scalar_norm_sq_le_divisor C (s.characters h)
    (s.extractedFactor h) (s.row h).element s.base (zero_lt_one.trans s.base_gt_one)
    s.length (s.slotWeight h) annulus profile (hplain₁ h hh) (hplain₂ h hh)
    (hprime h hh) hannulus (hprofile h hh) hA hP hsquarefree hselection).trans
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact selected_factor_product_le _ (fun i => annulus i * profile i) B cap hB
    (by simpa only [Fintype.card_fin] using hcap)
    (fun i _ => mul_nonneg (hA i) (hP i)) (fun i _ => hfactor i)

namespace Calibration

variable {s} (D : s.Calibration (σ := σ) ω ψ)

/-- Choose the costs from primitive row, scalar and fiber bounds. -/
def withCosts (rowCost scalarCost : ℝ) (fibers : ℕ)
    (hrow : 0 ≤ rowCost) (hscalar : 0 ≤ scalarCost)
    (row_bound : ∀ h ∈ s.rows, ‖s.weight h‖ ≤ rowCost)
    (scalar_bound : ∀ h ∈ s.rows, ‖s.frozenScalar (σ := σ) h‖ ^ 2 ≤ scalarCost)
    (fiber_bound : ∀ I : HeckeGeneral.Analysis.NonzeroIdeal F,
      (s.rows.filter (fun h => (s.row h).momentIdeal = I)).card ≤ fibers) :
    s.Calibration (σ := σ) ω ψ :=
  { D with
    rowBound := rowCost
    rowBound_nonneg := hrow
    row_bound := row_bound
    scalarBound := scalarCost
    scalarBound_nonneg := hscalar
    scalar_bound := scalar_bound
    fiberBound := fibers
    fibers := fiber_bound }

namespace withCosts

variable (rowCost scalarCost : ℝ) (fibers : ℕ)
variable (hrow : 0 ≤ rowCost) (hscalar : 0 ≤ scalarCost)
variable (row_bound : ∀ h ∈ s.rows, ‖s.weight h‖ ≤ rowCost)
variable (scalar_bound : ∀ h ∈ s.rows, ‖s.frozenScalar (σ := σ) h‖ ^ 2 ≤ scalarCost)
variable (fiber_bound : ∀ I : HeckeGeneral.Analysis.NonzeroIdeal F,
  (s.rows.filter (fun h => (s.row h).momentIdeal = I)).card ≤ fibers)

local notation "D'" => D.withCosts rowCost scalarCost fibers hrow hscalar row_bound scalar_bound fiber_bound

theorem data_eq : (D').data = D.data := rfl
theorem parameters_eq : (D').parameters = D.parameters := rfl
theorem height_eq : (D').height = D.height := rfl
theorem mass_eq : (D').mass = rowCost * scalarCost * (fibers : ℝ) := rfl

/-- The primitive geometric and normalized-prime ledger is unchanged
when the producer chooses the actual arithmetic costs. -/
def capacity (G : D.NormalizedCapacityData) : (D').NormalizedCapacityData where
  geometry := G.geometry
  b₂ := G.b₂
  p₂ := G.p₂
  boundary := G.boundary
  ell := G.ell
  gap := G.gap
  δ := G.δ
  mesh := G.mesh
  supportError := G.supportError
  rawClipError := G.rawClipError
  widthError := G.widthError
  leftAnnulus := G.leftAnnulus
  rightAnnulus := G.rightAnnulus
  leftAnnulus_one := G.leftAnnulus_one
  rightAnnulus_one := G.rightAnnulus_one
  left_annulus := G.left_annulus
  right_annulus := G.right_annulus
  gap_pos := G.gap_pos
  kappa_pos := G.kappa_pos
  mesh_nonneg := G.mesh_nonneg
  fits_mesh := G.fits_mesh
  enlargement := G.enlargement
  unit_length := G.unit_length
  actual_width := G.actual_width
  boundary_width := G.boundary_width
  radical_length := G.radical_length
  boundary_nonneg := G.boundary_nonneg
  parent_capacity := G.parent_capacity
  common_length := G.common_length
  paid_shift := G.paid_shift
  raw_length := G.raw_length
  width_error := G.width_error
  budget_nonneg := G.budget_nonneg
  charge_nonneg := G.charge_nonneg
  radius := G.radius
  radius_pos := G.radius_pos
  primeBound := G.primeBound
  primeBound_nonneg := G.primeBound_nonneg
  prime_bound := G.prime_bound

local notation "G'" G => capacity D rowCost scalarCost fibers hrow hscalar row_bound scalar_bound fiber_bound G

theorem normalizedData_eq (G : D.NormalizedCapacityData) :
    (G' G).normalizedData = G.normalizedData := rfl

theorem childData_eq (G : D.NormalizedCapacityData)
    (keep : Finset (Fin s.allocation.keep.card)) :
    (G' G).childData keep = G.childData keep := rfl

theorem radius_eq (G : D.NormalizedCapacityData) : (G' G).radius = G.radius := rfl
theorem loss_eq (G : D.NormalizedCapacityData) (removed : Finset (Fin s.allocation.keep.card)) :
    (G' G).loss removed = G.loss removed := rfl

end withCosts

namespace NormalizedCapacityData

variable {D} (G : D.NormalizedCapacityData)

/-- Choose one original uniform prime constant instead of retaining
arbitrarily inflated entries of a supplied ledger. -/
def withPrimeCost (primeCost : ℝ) (hcost : 0 ≤ primeCost)
    (hprime : ∀ ξ, ∀ u ∈ pairedRows (D.data ξ) D.parameters s.base,
      ∀ i : Fin s.allocation.keep.card,
      ‖primePolynomial (normalizedMomentProfiles (D.data ξ) (G.radius ξ) (G.radius_pos ξ))
        (lengthSlot (D.data ξ) s.allocation.keep.card (D.count ξ) i) u s.base (D.height ξ)‖ ^ 2 ≤
          primeCost * s.base ^ (D.parameters.κ * s.childLength i)) : D.NormalizedCapacityData :=
  { G with primeBound := fun _ => primeCost
           primeBound_nonneg := fun _ => hcost
           prime_bound := hprime }

theorem withPrimeCost_childData (primeCost : ℝ) (hcost : 0 ≤ primeCost)
    (hprime : ∀ ξ, ∀ u ∈ pairedRows (D.data ξ) D.parameters s.base,
      ∀ i : Fin s.allocation.keep.card,
      ‖primePolynomial (normalizedMomentProfiles (D.data ξ) (G.radius ξ) (G.radius_pos ξ))
        (lengthSlot (D.data ξ) s.allocation.keep.card (D.count ξ) i) u s.base (D.height ξ)‖ ^ 2 ≤
          primeCost * s.base ^ (D.parameters.κ * s.childLength i))
    (keep : Finset (Fin s.allocation.keep.card)) :
    (G.withPrimeCost primeCost hcost hprime).childData keep = G.childData keep := rfl

end NormalizedCapacityData

/-- The canonical scalar cost is chosen from individual original
factors, before producing the new capacity child. -/
def withAllocationCosts
    (C : A.GeneralArithmeticContext σ η hS)
    (rowCost : ℝ) (fibers : ℕ) (hrow : 0 ≤ rowCost)
    (row_bound : ∀ h ∈ s.rows, ‖s.weight h‖ ≤ rowCost)
    (fiber_bound : ∀ I : HeckeGeneral.Analysis.NonzeroIdeal F,
      (s.rows.filter (fun h => (s.row h).momentIdeal = I)).card ≤ fibers)
    (annulus profile : Fin k → ℝ) (B : ℝ) (cap : ℕ) (hB : 1 ≤ B) (hcap : k ≤ cap)
    (hA : ∀ i, 0 ≤ annulus i) (hP : ∀ i, 0 ≤ profile i)
    (hfactor : ∀ i, annulus i * profile i ≤ B)
    (hsquarefree : Squarefree s.allocation.divisor)
    (hselection : s.allocation.selection ∈
      AllocationMass.idealAllocations s.allocation.divisor (k + 2))
    (hplain₁ : ∀ h ∈ s.rows,
      ‖sourcePlainCoefficient (s.characters h).plain (s.characters h).plainTwist
        (s.characters h).mask (s.allocation.plainDivisor 0)‖ ≤ 1)
    (hplain₂ : ∀ h ∈ s.rows,
      ‖sourcePlainCoefficient (s.characters h).plain (s.characters h).plainTwist
        (s.characters h).mask (s.allocation.plainDivisor (Fin.succ 0))‖ ≤ 1)
    (hprime : ∀ h ∈ s.rows, ∀ i ∈ Finset.univ \ s.allocation.keep,
      ‖sourcePrimeCoefficient ((s.characters h).slot i) ((s.characters h).slotTwist i)
        (s.characters h).mask (s.allocation.witness.2 i)‖ ≤ 1)
    (hannulus : ∀ i ∈ Finset.univ \ s.allocation.keep,
      (Ideal.absNorm (s.allocation.witness.2 i).asIdeal : ℝ) ≤ annulus i * s.base ^ s.length i)
    (hprofile : ∀ h ∈ s.rows, ∀ i ∈ Finset.univ \ s.allocation.keep,
      ‖s.slotWeight h i (s.allocation.witness.2 i)‖ ^ 2 ≤ profile i) :
    s.Calibration (σ := σ) ω ψ :=
  D.withCosts rowCost (B ^ cap / (Ideal.absNorm s.allocation.divisor : ℝ)) fibers hrow
    (div_nonneg (pow_nonneg (zero_le_one.trans hB) _) (Nat.cast_nonneg _)) row_bound
    (s.frozenScalar_uniform_inverse_norm C annulus profile B cap hB hcap hA hP hfactor
      hsquarefree hselection hplain₁ hplain₂ hprime hannulus hprofile) fiber_bound

end Calibration
end ActualAllocatedSource

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualAllocatedSource.frozenScalar_uniform_inverse_norm
#print axioms HeckeSkeleton.Moments.EngineStep.ActualAllocatedSource.Calibration.withCosts.capacity
#print axioms HeckeSkeleton.Moments.EngineStep.ActualAllocatedSource.Calibration.withAllocationCosts
