import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CenteredAllocatedChildren
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.NestedHilbertPhase
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalLogNormLocations

/-!
# The fixed joint source of an actual allocated rectangle

The first Fourier mode multiplies the three original atom weights by
their individual phases.  Pairing their first locations with the fixed
second locations constructs one actual allocated source before either
mode is chosen.  Its rows, allocation, arithmetic characters, scales and
unmodulated weights are those of the given source.

The whole coefficient identity is proved from the individual terms and
the finite product.  This gives exact ordinary and centered energy
identities.  The computed frozen scalar acquires only the phase of the
actual removed slots, so neither its norm nor the child row weight
changes.  Common row translations likewise preserve the exact energy.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors
set_option autoImplicit false

namespace HeckeSkeleton.Moments.EngineStep.CanonicalJointAllocatedSource

open NumberField DedekindZetaZeroFree
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {U V H : Type*} {k : ℕ}
variable [NormedAddCommGroup U] [InnerProductSpace ℝ U]
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The complete coefficient of the literal original allocated column. -/
def columnCoefficient (s : ActualAllocatedSource A V H k) (h : H)
    (i : AllocationColumn F k) : ℂ :=
  rawSourceCoefficient (σ := σ) (s.characters h) (s.extractedFactor h)
    (s.row h).element s.scale₁ s.scale₂ s.base s.length
    (s.leftWeight h) (s.rightWeight h) (s.slotWeight h) i

/-- The sum of the original single-atom locations. -/
def columnLocation (s : ActualAllocatedSource A V H k) (h : H)
    (i : AllocationColumn F k) : V :=
  rawSourceLocation (s.leftLocation h) (s.rightLocation h) (s.slotLocation h) i

variable (s : ActualAllocatedSource A V H k)
variable (x₁ x₂ : H → HeckeGeneral.Analysis.NonzeroIdeal F → U)
variable (x : H → Fin k → HeightOneSpectrum (𝓞 F) → U)

/-- One fixed source whose locations carry both original Fourier modes. -/
def jointSource : ActualAllocatedSource A (WithLp 2 (U × V)) H k where
  allocation := s.allocation
  rows := s.rows
  weight := s.weight
  originalIdeal := s.originalIdeal
  frequency := s.frequency
  extractedFactor := s.extractedFactor
  normFactor := s.normFactor
  row := s.row
  characters := s.characters
  scale₁ := s.scale₁
  scale₂ := s.scale₂
  base := s.base
  base_gt_one := s.base_gt_one
  length := s.length
  length_pos := s.length_pos
  leftWeight := s.leftWeight
  rightWeight := s.rightWeight
  slotWeight := s.slotWeight
  leftLocation := fun h I => WithLp.toLp 2 (x₁ h I, s.leftLocation h I)
  rightLocation := fun h I => WithLp.toLp 2 (x₂ h I, s.rightLocation h I)
  slotLocation := fun h j p => WithLp.toLp 2 (x h j p, s.slotLocation h j p)

/-- Insert the first mode only into the original atom weights. -/
def withFirstMode (ξ : U) : ActualAllocatedSource A V H k :=
  { s with
    leftWeight := fun h I => s.leftWeight h I * jointPhase ξ (x₁ h I)
    rightWeight := fun h I => s.rightWeight h I * jointPhase ξ (x₂ h I)
    slotWeight := fun h j p => s.slotWeight h j p * jointPhase ξ (x h j p) }

@[simp] theorem columnCoefficient_jointSource (h : H) (i : AllocationColumn F k) :
    columnCoefficient (σ := σ) (jointSource s x₁ x₂ x) h i =
      columnCoefficient (σ := σ) s h i := rfl

@[simp] theorem columnLocation_withFirstMode (ξ : U) (h : H)
    (i : AllocationColumn F k) :
    columnLocation (withFirstMode s x₁ x₂ x ξ) h i = columnLocation s h i := rfl

private theorem sourcePlainTerm_weight_phase
    (χ θ : HeckeCharacter F) (M : Ideal (𝓞 F) →* ℂ) (g h' : A.R)
    (w : HeckeGeneral.Analysis.NonzeroIdeal F → ℂ) (a : HeckeGeneral.Analysis.NonzeroIdeal F → U)
    (N : ℝ) (ξ : U) (I : HeckeGeneral.Analysis.NonzeroIdeal F) :
    sourcePlainTerm (σ := σ) χ θ M g h'
        (fun J => w J * jointPhase ξ (a J)) N I =
      sourcePlainTerm (σ := σ) χ θ M g h' w N I * jointPhase ξ (a I) := by
  simp only [sourcePlainTerm, mul_assoc]

private theorem sourcePrimeTerm_weight_phase
    (χ θ : HeckeCharacter F) (M : Ideal (𝓞 F) →* ℂ) (g h' : A.R)
    (w : HeightOneSpectrum (𝓞 F) → ℂ) (a : HeightOneSpectrum (𝓞 F) → U)
    (N : ℝ) (ξ : U) (p : HeightOneSpectrum (𝓞 F)) :
    sourcePrimeTerm (σ := σ) χ θ M g h'
        (fun q => w q * jointPhase ξ (a q)) N p =
      sourcePrimeTerm (σ := σ) χ θ M g h' w N p * jointPhase ξ (a p) := by
  simp only [sourcePrimeTerm, mul_assoc]

/-- The phase of a whole actual column is the product of its atom phases. -/
theorem rawSourceCoefficient_firstMode
    (T : FixedChildCharacters F k) (g h' : A.R) (N₁ N₂ Z : ℝ)
    (length : Fin k → ℝ) (w₁ w₂ : HeckeGeneral.Analysis.NonzeroIdeal F → ℂ)
    (w : Fin k → HeightOneSpectrum (𝓞 F) → ℂ)
    (a₁ a₂ : HeckeGeneral.Analysis.NonzeroIdeal F → U)
    (a : Fin k → HeightOneSpectrum (𝓞 F) → U)
    (ξ : U) (i : AllocationColumn F k) :
    rawSourceCoefficient (σ := σ) T g h' N₁ N₂ Z length
        (fun I => w₁ I * jointPhase ξ (a₁ I))
        (fun I => w₂ I * jointPhase ξ (a₂ I))
        (fun j p => w j p * jointPhase ξ (a j p)) i =
      rawSourceCoefficient (σ := σ) T g h' N₁ N₂ Z length w₁ w₂ w i *
        jointPhase ξ (rawSourceLocation a₁ a₂ a i) := by
  simp only [rawSourceCoefficient, FixedChildCharacters.coefficient,
    childCartesianCoefficient, rawSourceLocation, childCartesianLocation,
    sourcePlainTerm_weight_phase, sourcePrimeTerm_weight_phase,
    jointPhase_add, jointPhase_sum, Finset.prod_mul_distrib]
  ring

theorem columnCoefficient_withFirstMode (ξ : U) (h : H)
    (i : AllocationColumn F k) :
    columnCoefficient (σ := σ) (withFirstMode s x₁ x₂ x ξ) h i =
      columnCoefficient (σ := σ) s h i *
        jointPhase ξ (rawSourceLocation (x₁ h) (x₂ h) (x h) i) :=
  rawSourceCoefficient_firstMode (σ := σ) (s.characters h)
    (s.extractedFactor h) (s.row h).element s.scale₁ s.scale₂ s.base s.length
    (s.leftWeight h) (s.rightWeight h) (s.slotWeight h)
    (x₁ h) (x₂ h) (x h) ξ i

theorem columnLocation_jointSource (h : H) (i : AllocationColumn F k) :
    columnLocation (jointSource s x₁ x₂ x) h i =
      WithLp.toLp 2
        (rawSourceLocation (x₁ h) (x₂ h) (x h) i, columnLocation s h i) := by
  apply WithLp.ofLp_injective 2
  simp only [columnLocation, jointSource, rawSourceLocation, childCartesianLocation,
    WithLp.ofLp_add, WithLp.ofLp_sum, WithLp.ofLp_toLp,
    ← prod_mk_sum] <;> rfl

/-- Exact energy identification, before any capacity child is chosen. -/
theorem energy_identity (ξ : U) (ζ : V) :
    (withFirstMode s x₁ x₂ x ξ).energy (σ := σ) ζ =
      (jointSource s x₁ x₂ x).energy (σ := σ) (WithLp.toLp 2 (ξ, ζ)) := by
  change jointColumnEnergy s.rows s.allocation.columns s.weight
      (columnCoefficient (σ := σ) (withFirstMode s x₁ x₂ x ξ)) (columnLocation s) ζ =
    jointColumnEnergy s.rows s.allocation.columns s.weight
      (columnCoefficient (σ := σ) s) (columnLocation (jointSource s x₁ x₂ x))
        (WithLp.toLp 2 (ξ, ζ))
  have hc : columnCoefficient (σ := σ) (withFirstMode s x₁ x₂ x ξ) =
      (fun h i => columnCoefficient (σ := σ) s h i *
        jointPhase ξ (rawSourceLocation (x₁ h) (x₂ h) (x h) i)) := by
    funext h i
    exact columnCoefficient_withFirstMode s x₁ x₂ x ξ h i
  have hl : columnLocation (jointSource s x₁ x₂ x) =
      (fun h i => WithLp.toLp 2
        (rawSourceLocation (x₁ h) (x₂ h) (x h) i, columnLocation s h i)) := by
    funext h i
    exact columnLocation_jointSource s x₁ x₂ x h i
  rw [hc, hl]
  exact nested_jointColumnEnergy s.rows s.allocation.columns s.weight
    (columnCoefficient (σ := σ) s)
    (fun h => rawSourceLocation (x₁ h) (x₂ h) (x h)) (columnLocation s) ξ ζ

/-- The comparison rectangle uses the same first-mode slot weights. -/
theorem withFirstMode_comparison (N₁ N₂ : ℝ)
    (w₁ w₂ : H → HeckeGeneral.Analysis.NonzeroIdeal F → ℂ) (ξ : U) :
    withFirstMode (s.comparison N₁ N₂ w₁ w₂) x₁ x₂ x ξ =
      (withFirstMode s x₁ x₂ x ξ).comparison N₁ N₂
        (fun h I => w₁ h I * jointPhase ξ (x₁ h I))
        (fun h I => w₂ h I * jointPhase ξ (x₂ h I)) := rfl

theorem jointSource_comparison (N₁ N₂ : ℝ)
    (w₁ w₂ : H → HeckeGeneral.Analysis.NonzeroIdeal F → ℂ) :
    jointSource (s.comparison N₁ N₂ w₁ w₂) x₁ x₂ x =
      (jointSource s x₁ x₂ x).comparison N₁ N₂ w₁ w₂ := rfl

/-- The subtraction stays inside the same joint Fourier polynomial. -/
theorem centered_energy_identity (N₁ N₂ : ℝ)
    (w₁ w₂ : H → HeckeGeneral.Analysis.NonzeroIdeal F → ℂ) (ξ : U) (ζ : V) :
    (withFirstMode s x₁ x₂ x ξ).centeredEnergy (σ := σ) N₁ N₂
        (fun h I => w₁ h I * jointPhase ξ (x₁ h I))
        (fun h I => w₂ h I * jointPhase ξ (x₂ h I)) ζ =
      (jointSource s x₁ x₂ x).centeredEnergy (σ := σ) N₁ N₂ w₁ w₂
        (WithLp.toLp 2 (ξ, ζ)) := by
  change jointColumnEnergy s.rows s.allocation.columns s.weight
      (fun h i => columnCoefficient (σ := σ) (withFirstMode s x₁ x₂ x ξ) h i -
        columnCoefficient (σ := σ)
          (withFirstMode (s.comparison N₁ N₂ w₁ w₂) x₁ x₂ x ξ) h i)
      (columnLocation s) ζ =
    jointColumnEnergy s.rows s.allocation.columns s.weight
      (fun h i => columnCoefficient (σ := σ) s h i -
        columnCoefficient (σ := σ) (s.comparison N₁ N₂ w₁ w₂) h i)
      (columnLocation (jointSource s x₁ x₂ x)) (WithLp.toLp 2 (ξ, ζ))
  have hc :
      (fun h i => columnCoefficient (σ := σ) (withFirstMode s x₁ x₂ x ξ) h i -
        columnCoefficient (σ := σ)
          (withFirstMode (s.comparison N₁ N₂ w₁ w₂) x₁ x₂ x ξ) h i) =
      (fun h i => (columnCoefficient (σ := σ) s h i -
        columnCoefficient (σ := σ) (s.comparison N₁ N₂ w₁ w₂) h i) *
          jointPhase ξ (rawSourceLocation (x₁ h) (x₂ h) (x h) i)) := by
    funext h i
    simp only [columnCoefficient_withFirstMode, sub_mul]
  have hl : columnLocation (jointSource s x₁ x₂ x) =
      (fun h i => WithLp.toLp 2
        (rawSourceLocation (x₁ h) (x₂ h) (x h) i, columnLocation s h i)) := by
    funext h i
    exact columnLocation_jointSource s x₁ x₂ x h i
  rw [hc, hl]
  exact nested_jointColumnEnergy s.rows s.allocation.columns s.weight
    (fun h i => columnCoefficient (σ := σ) s h i -
      columnCoefficient (σ := σ) (s.comparison N₁ N₂ w₁ w₂) h i)
    (fun h => rawSourceLocation (x₁ h) (x₂ h) (x h)) (columnLocation s) ξ ζ

@[simp] theorem frozenScalar_jointSource (h : H) :
    (jointSource s x₁ x₂ x).frozenScalar (σ := σ) h =
      s.frozenScalar (σ := σ) h := rfl

@[simp] theorem childWeight_jointSource (h : H) :
    (jointSource s x₁ x₂ x).childWeight (σ := σ) h =
      s.childWeight (σ := σ) h := rfl

/-- Only the actual frozen prime occurrences enter this extra scalar phase. -/
theorem frozenScalar_withFirstMode (ξ : U) (h : H) :
    (withFirstMode s x₁ x₂ x ξ).frozenScalar (σ := σ) h =
      s.frozenScalar (σ := σ) h *
        jointPhase ξ (frozenSourceLocation s.allocation.keep s.allocation.witness.2 (x h)) := by
  simp only [ActualAllocatedSource.frozenScalar, withFirstMode,
    ActualColumnAllocation.scalar, FixedChildCharacters.frozenScalar,
    sourcePrimeTerm_weight_phase, frozenSourceLocation, jointPhase_sum,
    Finset.prod_mul_distrib]
  ring

@[simp] theorem norm_frozenScalar_withFirstMode (ξ : U) (h : H) :
    ‖(withFirstMode s x₁ x₂ x ξ).frozenScalar (σ := σ) h‖ =
      ‖s.frozenScalar (σ := σ) h‖ := by
  rw [frozenScalar_withFirstMode, norm_mul, norm_jointPhase, mul_one]

/-- The actual complex child row weight is unchanged, not just bounded. -/
@[simp] theorem childWeight_withFirstMode (ξ : U) (h : H) :
    (withFirstMode s x₁ x₂ x ξ).childWeight (σ := σ) h =
      s.childWeight (σ := σ) h := by
  change s.weight h * (withFirstMode s x₁ x₂ x ξ).frozenScalar (σ := σ) h *
      star ((withFirstMode s x₁ x₂ x ξ).frozenScalar (σ := σ) h) =
    s.weight h * s.frozenScalar (σ := σ) h * star (s.frozenScalar (σ := σ) h)
  simpa only [mul_assoc, Complex.star_def, Complex.mul_conj'] using
    congrArg (fun r : ℝ => s.weight h * (r : ℂ) ^ 2)
      (norm_frozenScalar_withFirstMode (σ := σ) s x₁ x₂ x ξ h)

/-- Translate each original atom location by a row-dependent constant. -/
def translateLocations (z₁ z₂ : H → V) (z : H → Fin k → V) :
    ActualAllocatedSource A V H k :=
  { s with
    leftLocation := fun h I => z₁ h + s.leftLocation h I
    rightLocation := fun h I => z₂ h + s.rightLocation h I
    slotLocation := fun h j p => z h j + s.slotLocation h j p }

@[simp] theorem columnCoefficient_translateLocations
    (z₁ z₂ : H → V) (z : H → Fin k → V) (h : H) (i : AllocationColumn F k) :
    columnCoefficient (σ := σ) (translateLocations s z₁ z₂ z) h i =
      columnCoefficient (σ := σ) s h i := rfl

theorem columnLocation_translateLocations
    (z₁ z₂ : H → V) (z : H → Fin k → V) (h : H) (i : AllocationColumn F k) :
    columnLocation (translateLocations s z₁ z₂ z) h i =
      (z₁ h + z₂ h + ∑ j, z h j) + columnLocation s h i := by
  simp only [columnLocation, translateLocations, rawSourceLocation,
    childCartesianLocation, Finset.sum_add_distrib]
  abel

theorem translateLocations_energy
    (z₁ z₂ : H → V) (z : H → Fin k → V) (ζ : V) :
    (translateLocations s z₁ z₂ z).energy (σ := σ) ζ = s.energy (σ := σ) ζ := by
  change jointColumnEnergy s.rows s.allocation.columns s.weight
      (columnCoefficient (σ := σ) s) (columnLocation (translateLocations s z₁ z₂ z)) ζ =
    jointColumnEnergy s.rows s.allocation.columns s.weight
      (columnCoefficient (σ := σ) s) (columnLocation s) ζ
  have hl : columnLocation (translateLocations s z₁ z₂ z) =
      (fun h i => (z₁ h + z₂ h + ∑ j, z h j) + columnLocation s h i) := by
    funext h i
    exact columnLocation_translateLocations s z₁ z₂ z h i
  rw [hl]
  exact jointColumnEnergy_rowTranslation s.rows s.allocation.columns s.weight
    (columnCoefficient (σ := σ) s) (columnLocation s)
    (fun h => z₁ h + z₂ h + ∑ j, z h j) ζ

@[simp] theorem frozenScalar_translateLocations
    (z₁ z₂ : H → V) (z : H → Fin k → V) (h : H) :
    (translateLocations s z₁ z₂ z).frozenScalar (σ := σ) h =
      s.frozenScalar (σ := σ) h := rfl

@[simp] theorem childWeight_translateLocations
    (z₁ z₂ : H → V) (z : H → Fin k → V) (h : H) :
    (translateLocations s z₁ z₂ z).childWeight (σ := σ) h =
      s.childWeight (σ := σ) h := rfl

end HeckeSkeleton.Moments.EngineStep.CanonicalJointAllocatedSource

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalJointAllocatedSource.energy_identity
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalJointAllocatedSource.centered_energy_identity
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalJointAllocatedSource.childWeight_withFirstMode
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalJointAllocatedSource.translateLocations_energy
