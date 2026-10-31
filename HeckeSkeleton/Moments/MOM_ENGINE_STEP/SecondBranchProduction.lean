import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualCapacityProduction
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondCenteredBinding
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondCoefficientNormalization

/-!
# Producing the actual children of one allocated second-kernel branch

The side frame contains the original allocated columns, per-factor
arithmetic dictionaries, actual common-correlation rows, positive Gauss
normalization scales and fixed Fourier locations.  Its energy is the
literal energy used by the allocated second kernel.  The engine proves
its equality with the actual source energy and then constructs a fixed
capacity child from primitive inputs.

Both frames precede the Fourier variable.  Taking their Hilbert space
to be `WithLp 2 (U × V)` therefore gives one deletion and one actual
family for both continuous variables.  Centered coefficients remain
intact until both ordinary rectangles have actual nonexceptional row
calibrations; exceptional rows use the unsplit identities separately.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree HeckeGeneral.Characters
open HeckeGeneral.Analysis.ConditionalMoments

inductive SecondColumnSide
  | left
  | right

def SecondColumnSide.phase (side : SecondColumnSide)
    (Ray : Type*) [CommGroup Ray] [Fintype Ray] (χ : (Ray × Ray) →* Circle) : Ray →* Circle :=
  match side with
  | .left => fixedLeftPhase Ray χ
  | .right => fixedRightPhase Ray χ

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {H ι V : Type*} [Fintype ι] [DecidableEq ι]
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Every coefficient and location is computed from original factor
data; no energy bound is a field of this frame. -/
structure SecondSideFrame (C : A.GeneralArithmeticContext σ η hS)
    (R : ActualSecondCorrelationRows A σ H ι) (Ray : Type*) [CommGroup Ray] [Fintype Ray]
    (side : SecondColumnSide) (k : ℕ) where
  allocation : ActualColumnAllocation F k
  characters : FixedChildCharacters F k
  phaseCharacter : (Ray × Ray) →* Circle
  dictionary : SecondCoefficientTermDictionary characters (side.phase Ray phaseCharacter)
    allocation.plain₁ allocation.plain₂ allocation.slots
  base_gt_one : 1 < dictionary.base
  length_pos : ∀ i, 0 < dictionary.length i
  ideal : AllocationColumn F k → A.Exterior
  ideal_product : ∀ i ∈ childCartesianColumns allocation.plain₁ allocation.plain₂ allocation.slots,
    (ideal i).val = allocationColumnIdeal i
  gaussScale₁ : ℝ
  gaussScale₂ : ℝ
  gaussSlotScale : Fin k → ℝ
  gaussScale₁_pos : 0 < gaussScale₁
  gaussScale₂_pos : 0 < gaussScale₂
  gaussSlotScale_pos : ∀ i, 0 < gaussSlotScale i
  leftLocation : H → HeckeGeneral.Analysis.NonzeroIdeal F → V
  rightLocation : H → HeckeGeneral.Analysis.NonzeroIdeal F → V
  slotLocation : H → Fin k → HeightOneSpectrum (𝓞 F) → V

namespace SecondSideFrame

variable {C : A.GeneralArithmeticContext σ η hS}
variable {R : ActualSecondCorrelationRows A σ H ι}
variable {Ray : Type*} [CommGroup Ray] [Fintype Ray]
variable {side : SecondColumnSide} {k : ℕ}
variable (f : SecondSideFrame (V := V) C R Ray side k)

def normalizationScale : ℝ := extraGaussScale f.gaussScale₁ f.gaussScale₂ f.gaussSlotScale

def normalizer : ℂ := extraGaussNormalizer f.gaussScale₁ f.gaussScale₂ f.gaussSlotScale

theorem normalizationScale_pos : 0 < f.normalizationScale :=
  extraGaussScale_pos _ _ _ f.gaussScale₁_pos f.gaussScale₂_pos f.gaussSlotScale_pos

def rawSource : ActualAllocatedSource A V R.live k :=
  R.source C f.allocation f.characters (side.phase Ray f.phaseCharacter) f.dictionary
    f.base_gt_one f.length_pos f.leftLocation f.rightLocation f.slotLocation

def source : ActualAllocatedSource A V R.live k :=
  match side with
  | .left => f.rawSource
  | .right => f.rawSource.negativeSide

def coefficient : H → AllocationColumn F k → ℂ :=
  match side with
  | .left => secondAllocatedLeftCoefficient (σ := σ) Ray f.ideal R.frequency f.dictionary.ray f.phaseCharacter
      (f.dictionary.normalizedCoefficient (Real.sqrt f.gaussScale₁ : ℂ)⁻¹
        (Real.sqrt f.gaussScale₂ : ℂ)⁻¹ (fun i => (Real.sqrt (f.gaussSlotScale i) : ℂ)⁻¹))
  | .right => secondAllocatedRightCoefficient (σ := σ) Ray f.ideal R.frequency f.dictionary.ray f.phaseCharacter
      (f.dictionary.normalizedCoefficient (Real.sqrt f.gaussScale₁ : ℂ)⁻¹
        (Real.sqrt f.gaussScale₂ : ℂ)⁻¹ (fun i => (Real.sqrt (f.gaussSlotScale i) : ℂ)⁻¹))

def energy (ξ : V) : ℝ :=
  jointColumnEnergy R.rows f.allocation.columns (fun h => R.weight h * R.correlation h)
    f.coefficient
    (fun h => rawSourceLocation (f.leftLocation h) (f.rightLocation h) (f.slotLocation h)) ξ

theorem energy_nonneg (ξ : V) : 0 ≤ f.energy ξ := jointColumnEnergy_nonneg _ _ _ _ _ _

theorem energy_eq_source (ξ : V) :
    f.energy ξ = ‖f.normalizer‖ ^ 2 * f.source.energy (σ := σ) ξ := by
  cases side with
  | left =>
    exact R.left_energy_eq_source Ray C f.allocation f.characters f.phaseCharacter f.dictionary
      f.base_gt_one f.length_pos f.ideal f.ideal_product
      (Real.sqrt f.gaussScale₁ : ℂ)⁻¹ (Real.sqrt f.gaussScale₂ : ℂ)⁻¹
      (fun i => (Real.sqrt (f.gaussSlotScale i) : ℂ)⁻¹)
      f.leftLocation f.rightLocation f.slotLocation ξ
  | right =>
    exact R.right_energy_eq_source Ray C f.allocation f.characters f.phaseCharacter f.dictionary
      f.base_gt_one f.length_pos f.ideal f.ideal_product
      (Real.sqrt f.gaussScale₁ : ℂ)⁻¹ (Real.sqrt f.gaussScale₂ : ℂ)⁻¹
      (fun i => (Real.sqrt (f.gaussSlotScale i) : ℂ)⁻¹)
      f.leftLocation f.rightLocation f.slotLocation ξ

theorem energy_eq_div_scale (ξ : V) :
    f.energy ξ = f.source.energy (σ := σ) ξ / f.normalizationScale := by
  rw [f.energy_eq_source]
  change ‖extraGaussNormalizer f.gaussScale₁ f.gaussScale₂ f.gaussSlotScale‖ ^ 2 * _ = _
  rw [extraGaussNormalizer_norm_sq _ _ _ f.gaussScale₁_pos f.gaussScale₂_pos f.gaussSlotScale_pos]
  unfold normalizationScale
  ring

variable {ω ψ : HeckeCharacter F}

/-- The literal allocated kernel side either vanishes or supplies a
constructed actual child with every capacity invariant. -/
theorem produce_child
    (cal : f.source.Calibration (σ := σ) ω ψ) (input : cal.CapacityInput) :
    (∀ ξ, f.energy ξ = 0) ∨
      ∃ child : cal.CapacityChild input, ∀ ξ,
        f.energy ξ ≤ (child.cost ξ / f.normalizationScale) *
          pairedEnergy (child.data ξ) child.parameters f.source.base (cal.height ξ) := by
  rcases cal.produce_capacity_child input with hzero | ⟨child⟩
  · left
    intro ξ
    rw [f.energy_eq_div_scale, hzero ξ, zero_div]
  · right
    refine ⟨child, ?_⟩
    intro ξ
    rw [f.energy_eq_div_scale]
    apply (div_le_div_of_nonneg_right (child.source_bound ξ) f.normalizationScale_pos.le).trans_eq
    ring

def comparison (e : SecondCoefficientComparison f.dictionary) :
    SecondSideFrame (V := V) C R Ray side k :=
  { f with dictionary := e.dictionary
    base_gt_one := f.base_gt_one
    length_pos := f.length_pos }

def centeredCoefficient (e : SecondCoefficientComparison f.dictionary) : H → AllocationColumn F k → ℂ :=
  match side with
  | .left => secondAllocatedLeftCoefficient (σ := σ) Ray f.ideal R.frequency f.dictionary.ray f.phaseCharacter
      (e.centeredCoefficient (Real.sqrt f.gaussScale₁ : ℂ)⁻¹ (Real.sqrt f.gaussScale₂ : ℂ)⁻¹
        (fun i => (Real.sqrt (f.gaussSlotScale i) : ℂ)⁻¹))
  | .right => secondAllocatedRightCoefficient (σ := σ) Ray f.ideal R.frequency f.dictionary.ray f.phaseCharacter
      (e.centeredCoefficient (Real.sqrt f.gaussScale₁ : ℂ)⁻¹ (Real.sqrt f.gaussScale₂ : ℂ)⁻¹
        (fun i => (Real.sqrt (f.gaussSlotScale i) : ℂ)⁻¹))

def centeredEnergy (e : SecondCoefficientComparison f.dictionary) (ξ : V) : ℝ :=
  jointColumnEnergy R.rows f.allocation.columns (fun h => R.weight h * R.correlation h)
    (f.centeredCoefficient e)
    (fun h => rawSourceLocation (f.leftLocation h) (f.rightLocation h) (f.slotLocation h)) ξ

theorem centeredCoefficient_eq (e : SecondCoefficientComparison f.dictionary)
    (h : H) (i : AllocationColumn F k) :
    f.centeredCoefficient e h i = f.coefficient h i - (f.comparison e).coefficient h i := by
  cases side <;>
    simp only [centeredCoefficient, coefficient, comparison,
      SecondCoefficientComparison.centeredCoefficient, SecondCoefficientComparison.dictionary,
      SecondCoefficientTermDictionary.ray,
      secondAllocatedLeftCoefficient, secondAllocatedRightCoefficient,
      sub_mul, star_sub]

theorem centered_sqrt_energy_le (e : SecondCoefficientComparison f.dictionary) (ξ : V) :
    Real.sqrt (f.centeredEnergy e ξ) ≤
      Real.sqrt (f.energy ξ) + Real.sqrt ((f.comparison e).energy ξ) := by
  simp only [centeredEnergy, f.centeredCoefficient_eq]
  exact sqrt_joint_energy_sub _ _ _ f.coefficient (f.comparison e).coefficient _ ξ

/-- Both ordinary rectangles have the actual nonexceptional row filter
and raw term dictionaries before this producing statement is invoked.
The entire centered source remains visible in the first conclusion. -/
theorem produce_centered_children (e : SecondCoefficientComparison f.dictionary)
    (main : f.source.Calibration (σ := σ) ω ψ)
    (other : (f.comparison e).source.Calibration (σ := σ) ω ψ)
    (mainInput : main.CapacityInput) (otherInput : other.CapacityInput) :
    (∀ ξ, Real.sqrt (f.centeredEnergy e ξ) ≤
      Real.sqrt (f.energy ξ) + Real.sqrt ((f.comparison e).energy ξ)) ∧
    ((∀ ξ, f.energy ξ = 0) ∨
      ∃ child : main.CapacityChild mainInput, ∀ ξ,
        f.energy ξ ≤ (child.cost ξ / f.normalizationScale) *
          pairedEnergy (child.data ξ) child.parameters f.source.base (main.height ξ)) ∧
    ((∀ ξ, (f.comparison e).energy ξ = 0) ∨
      ∃ child : other.CapacityChild otherInput, ∀ ξ,
        (f.comparison e).energy ξ ≤ (child.cost ξ / (f.comparison e).normalizationScale) *
          pairedEnergy (child.data ξ) child.parameters (f.comparison e).source.base (other.height ξ)) :=
  ⟨f.centered_sqrt_energy_le e, f.produce_child main mainInput,
    (f.comparison e).produce_child other otherInput⟩

end SecondSideFrame

/-- The actual paired second-kernel integrand produces two actual
families.  Its positive weight is computed from the two raw allocations,
the prime deletion costs and the two original Gauss scales. -/
theorem actual_second_pair_produces_children
    {C : A.GeneralArithmeticContext σ η hS} {R : ActualSecondCorrelationRows A σ H ι}
    {Ray : Type*} [CommGroup Ray] [Fintype Ray] {k l : ℕ}
    {ω ψ : HeckeCharacter F}
    (left : SecondSideFrame (V := V) C R Ray .left k)
    (right : SecondSideFrame (V := V) C R Ray .right l)
    (lc : left.source.Calibration (σ := σ) ω ψ)
    (rc : right.source.Calibration (σ := σ) ω ψ)
    (li : lc.CapacityInput) (ri : rc.CapacityInput) :
    (∀ ξ, Real.sqrt (left.energy ξ) * Real.sqrt (right.energy ξ) = 0) ∨
      ∃ lchild : lc.CapacityChild li, ∃ rchild : rc.CapacityChild ri, ∀ ξ,
        Real.sqrt (left.energy ξ) * Real.sqrt (right.energy ξ) ≤
          (Real.sqrt (lchild.cost ξ) * Real.sqrt (rchild.cost ξ) /
            (Real.sqrt left.normalizationScale * Real.sqrt right.normalizationScale)) *
          (Real.sqrt (pairedEnergy (lchild.data ξ) lchild.parameters left.source.base (lc.height ξ)) *
            Real.sqrt (pairedEnergy (rchild.data ξ) rchild.parameters right.source.base (rc.height ξ))) := by
  rcases left.produce_child lc li with hz | ⟨lchild, hl⟩
  · exact Or.inl (fun ξ => by rw [hz ξ, Real.sqrt_zero, zero_mul])
  rcases right.produce_child rc ri with hz | ⟨rchild, hr⟩
  · exact Or.inl (fun ξ => by rw [hz ξ, Real.sqrt_zero, mul_zero])
  right
  refine ⟨lchild, rchild, ?_⟩
  intro ξ
  apply (mul_le_mul (Real.sqrt_le_sqrt (hl ξ)) (Real.sqrt_le_sqrt (hr ξ))
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).trans_eq
  rw [Real.sqrt_mul (div_nonneg (lchild.cost_nonneg ξ) left.normalizationScale_pos.le),
    Real.sqrt_mul (div_nonneg (rchild.cost_nonneg ξ) right.normalizationScale_pos.le),
    Real.sqrt_div (lchild.cost_nonneg ξ), Real.sqrt_div (rchild.cost_nonneg ξ)]
  ring

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.SecondSideFrame.produce_child
#print axioms HeckeSkeleton.Moments.EngineStep.SecondSideFrame.produce_centered_children
#print axioms HeckeSkeleton.Moments.EngineStep.actual_second_pair_produces_children
