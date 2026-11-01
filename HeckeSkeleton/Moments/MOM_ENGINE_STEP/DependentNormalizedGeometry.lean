import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DependentNormalizedFamily
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.MovingEngineOutput
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.NormalizedFamilyGeometry

/-!
# Geometry and original dictionaries of dependent normalized families

The sigma family retains each component's calibration, capacity and
already selected children. Parent geometry, the actual fixed profile
windows and the original arithmetic dictionaries therefore pass to the
combined family by their original label projections.

These are structural transports. They neither select a child again nor
assume a parent estimate, total kernel mass or terminal bound.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Characters HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Physical

namespace ActualNormalizedPairFamily

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ} {ω ψ : HeckeCharacter K}
variable {V J : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {Λ : J → Type*} {Z : ℝ}
variable (families : ∀ j, ActualNormalizedPairFamily A σ V (Λ j) ω ψ Z)
variable (outer : Finset J) (labels : ∀ j, Finset (Λ j))
variable {parent : MomentData K ω ψ} {a : RealParameters} {step : ℝ}

/-- Each pre-deletion field is read from its original outer component. -/
theorem sigmaCombine_parentGeometry
    (geometry : ∀ j ∈ outer, (families j).ParentGeometry (labels j) parent a step) :
    (sigmaCombine families).ParentGeometry (outer.sigma labels) parent a step where
  left_parent b hb :=
    (geometry b.1 (Finset.mem_sigma.mp hb).1).left_parent b.2 (Finset.mem_sigma.mp hb).2
  right_parent b hb :=
    (geometry b.1 (Finset.mem_sigma.mp hb).1).right_parent b.2 (Finset.mem_sigma.mp hb).2
  left_gap b hb :=
    (geometry b.1 (Finset.mem_sigma.mp hb).1).left_gap b.2 (Finset.mem_sigma.mp hb).2
  right_gap b hb :=
    (geometry b.1 (Finset.mem_sigma.mp hb).1).right_gap b.2 (Finset.mem_sigma.mp hb).2
  left_kappa b hb :=
    (geometry b.1 (Finset.mem_sigma.mp hb).1).left_kappa b.2 (Finset.mem_sigma.mp hb).2
  right_kappa b hb :=
    (geometry b.1 (Finset.mem_sigma.mp hb).1).right_kappa b.2 (Finset.mem_sigma.mp hb).2
  left_slots b hb :=
    (geometry b.1 (Finset.mem_sigma.mp hb).1).left_slots b.2 (Finset.mem_sigma.mp hb).2
  right_slots b hb :=
    (geometry b.1 (Finset.mem_sigma.mp hb).1).right_slots b.2 (Finset.mem_sigma.mp hb).2
  left_theta b hb :=
    (geometry b.1 (Finset.mem_sigma.mp hb).1).left_theta b.2 (Finset.mem_sigma.mp hb).2
  right_theta b hb :=
    (geometry b.1 (Finset.mem_sigma.mp hb).1).right_theta b.2 (Finset.mem_sigma.mp hb).2

variable {rowDomain : Set (HeckeGeneral.Analysis.NonzeroIdeal K)}
variable {heightDomain window : Set ℝ} {seminorms : Finset (ℕ × ℕ)}

/-- The combined child data are the same frozen data to which each
component's original fixed-window theorem applies. -/
theorem sigmaCombine_in_fixed_window
    (windows : ∀ j ∈ outer, ∀ b : (families j).active (labels j), ∀ ξ : V,
      InFixedProfileWindow rowDomain heightDomain window seminorms
          ((families j).leftData (labels j) b ξ) ∧
        InFixedProfileWindow rowDomain heightDomain window seminorms
          ((families j).rightData (labels j) b ξ))
    (b : (sigmaCombine families).active (outer.sigma labels)) (ξ : V) :
    InFixedProfileWindow rowDomain heightDomain window seminorms
        ((sigmaCombine families).leftData (outer.sigma labels) b ξ) ∧
      InFixedProfileWindow rowDomain heightDomain window seminorms
        ((sigmaCombine families).rightData (outer.sigma labels) b ξ) :=
  windows b.val.1 (sigmaActiveOuter families outer labels b).property
    (sigmaActiveInner families outer labels b) ξ

/-- All output fields, including admissibility, refer to the same
component capacities and the same selected frozen children. -/
theorem sigmaCombine_outputGeometry
    (geometry : ∀ j ∈ outer,
      (families j).OutputGeometry (labels j) parent a step rowDomain window seminorms) :
    (sigmaCombine families).OutputGeometry (outer.sigma labels)
      parent a step rowDomain window seminorms where
  left_width b :=
    (geometry b.val.1 (sigmaActiveOuter families outer labels b).property).left_width
      (sigmaActiveInner families outer labels b)
  right_width b :=
    (geometry b.val.1 (sigmaActiveOuter families outer labels b).property).right_width
      (sigmaActiveInner families outer labels b)
  left_width_nonneg b :=
    (geometry b.val.1 (sigmaActiveOuter families outer labels b).property).left_width_nonneg
      (sigmaActiveInner families outer labels b)
  right_width_nonneg b :=
    (geometry b.val.1 (sigmaActiveOuter families outer labels b).property).right_width_nonneg
      (sigmaActiveInner families outer labels b)
  left_plain_left_nonneg b :=
    (geometry b.val.1 (sigmaActiveOuter families outer labels b).property).left_plain_left_nonneg
      (sigmaActiveInner families outer labels b)
  left_plain_right_nonneg b :=
    (geometry b.val.1 (sigmaActiveOuter families outer labels b).property).left_plain_right_nonneg
      (sigmaActiveInner families outer labels b)
  right_plain_left_nonneg b :=
    (geometry b.val.1 (sigmaActiveOuter families outer labels b).property).right_plain_left_nonneg
      (sigmaActiveInner families outer labels b)
  right_plain_right_nonneg b :=
    (geometry b.val.1 (sigmaActiveOuter families outer labels b).property).right_plain_right_nonneg
      (sigmaActiveInner families outer labels b)
  left_length b :=
    (geometry b.val.1 (sigmaActiveOuter families outer labels b).property).left_length
      (sigmaActiveInner families outer labels b)
  right_length b :=
    (geometry b.val.1 (sigmaActiveOuter families outer labels b).property).right_length
      (sigmaActiveInner families outer labels b)
  left_kappa b :=
    (geometry b.val.1 (sigmaActiveOuter families outer labels b).property).left_kappa
      (sigmaActiveInner families outer labels b)
  right_kappa b :=
    (geometry b.val.1 (sigmaActiveOuter families outer labels b).property).right_kappa
      (sigmaActiveInner families outer labels b)
  left_slots b :=
    (geometry b.val.1 (sigmaActiveOuter families outer labels b).property).left_slots
      (sigmaActiveInner families outer labels b)
  right_slots b :=
    (geometry b.val.1 (sigmaActiveOuter families outer labels b).property).right_slots
      (sigmaActiveInner families outer labels b)
  left_theta b :=
    (geometry b.val.1 (sigmaActiveOuter families outer labels b).property).left_theta
      (sigmaActiveInner families outer labels b)
  right_theta b :=
    (geometry b.val.1 (sigmaActiveOuter families outer labels b).property).right_theta
      (sigmaActiveInner families outer labels b)
  left_slot_characters b :=
    (geometry b.val.1 (sigmaActiveOuter families outer labels b).property).left_slot_characters
      (sigmaActiveInner families outer labels b)
  right_slot_characters b :=
    (geometry b.val.1 (sigmaActiveOuter families outer labels b).property).right_slot_characters
      (sigmaActiveInner families outer labels b)
  left_admissible b :=
    (geometry b.val.1 (sigmaActiveOuter families outer labels b).property).left_admissible
      (sigmaActiveInner families outer labels b)
  right_admissible b :=
    (geometry b.val.1 (sigmaActiveOuter families outer labels b).property).right_admissible
      (sigmaActiveInner families outer labels b)
  left_capacity b :=
    (geometry b.val.1 (sigmaActiveOuter families outer labels b).property).left_capacity
      (sigmaActiveInner families outer labels b)
  right_capacity b :=
    (geometry b.val.1 (sigmaActiveOuter families outer labels b).property).right_capacity
      (sigmaActiveInner families outer labels b)

variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {Q : Type*}

/-- Original moving recipes and both literal budgets are retained
before taking the active carrier or evaluating a Fourier parameter. -/
def sigmaCombine_movingRowInputs
    (raw : ∀ j ∈ outer, (families j).MovingRowInputs (P := P) (R := R) (labels j)) :
    (sigmaCombine families).MovingRowInputs (P := P) (R := R) (outer.sigma labels) where
  left b hb := (raw b.1 (Finset.mem_sigma.mp hb).1).left b.2 (Finset.mem_sigma.mp hb).2
  right b hb := (raw b.1 (Finset.mem_sigma.mp hb).1).right b.2 (Finset.mem_sigma.mp hb).2
  left_support b hb :=
    (raw b.1 (Finset.mem_sigma.mp hb).1).left_support b.2 (Finset.mem_sigma.mp hb).2
  right_support b hb :=
    (raw b.1 (Finset.mem_sigma.mp hb).1).right_support b.2 (Finset.mem_sigma.mp hb).2
  left_full b hb :=
    (raw b.1 (Finset.mem_sigma.mp hb).1).left_full b.2 (Finset.mem_sigma.mp hb).2
  right_full b hb :=
    (raw b.1 (Finset.mem_sigma.mp hb).1).right_full b.2 (Finset.mem_sigma.mp hb).2

theorem sigmaCombine_parentCharacterInputs
    (raw : ∀ j ∈ outer, (families j).ParentCharacterInputs (labels j) parent) :
    (sigmaCombine families).ParentCharacterInputs (outer.sigma labels) parent where
  left b hb := (raw b.1 (Finset.mem_sigma.mp hb).1).left b.2 (Finset.mem_sigma.mp hb).2
  right b hb := (raw b.1 (Finset.mem_sigma.mp hb).1).right b.2 (Finset.mem_sigma.mp hb).2

def sigmaCombine_normProfileInputs
    (raw : ∀ j ∈ outer, (families j).NormProfileInputs (labels j)) :
    (sigmaCombine families).NormProfileInputs (outer.sigma labels) where
  left b hb := (raw b.1 (Finset.mem_sigma.mp hb).1).left b.2 (Finset.mem_sigma.mp hb).2
  right b hb := (raw b.1 (Finset.mem_sigma.mp hb).1).right b.2 (Finset.mem_sigma.mp hb).2

def sigmaCombine_arithmeticAtomInputs
    (raw : ∀ j ∈ outer, (families j).ArithmeticAtomInputs (labels j) Q) :
    (sigmaCombine families).ArithmeticAtomInputs (outer.sigma labels) Q where
  left b hb := (raw b.1 (Finset.mem_sigma.mp hb).1).left b.2 (Finset.mem_sigma.mp hb).2
  right b hb := (raw b.1 (Finset.mem_sigma.mp hb).1).right b.2 (Finset.mem_sigma.mp hb).2

def sigmaCombine_parentSlotDictionaries
    (raw : ∀ j ∈ outer, (families j).ParentSlotDictionaries (labels j) parent) :
    (sigmaCombine families).ParentSlotDictionaries (outer.sigma labels) parent where
  left b hb := (raw b.1 (Finset.mem_sigma.mp hb).1).left b.2 (Finset.mem_sigma.mp hb).2
  right b hb := (raw b.1 (Finset.mem_sigma.mp hb).1).right b.2 (Finset.mem_sigma.mp hb).2

/-- A component may establish moving admissibility only on its active
carrier. No moving-support budget is required for an inactive label. -/
theorem sigmaCombine_moving_left_admissible
    (admissible : ∀ j ∈ outer, ∀ b : (families j).active (labels j), ∀ ξ : V,
      MovingEngineChildAdmissible A P R Q parent rowDomain window seminorms Z
        ((families j).leftData (labels j) b ξ) ((families j).leftParameters (labels j) b))
    (b : (sigmaCombine families).active (outer.sigma labels)) (ξ : V) :
    MovingEngineChildAdmissible A P R Q parent rowDomain window seminorms Z
      ((sigmaCombine families).leftData (outer.sigma labels) b ξ)
      ((sigmaCombine families).leftParameters (outer.sigma labels) b) :=
  admissible b.val.1 (sigmaActiveOuter families outer labels b).property
    (sigmaActiveInner families outer labels b) ξ

theorem sigmaCombine_moving_right_admissible
    (admissible : ∀ j ∈ outer, ∀ b : (families j).active (labels j), ∀ ξ : V,
      MovingEngineChildAdmissible A P R Q parent rowDomain window seminorms Z
        ((families j).rightData (labels j) b ξ) ((families j).rightParameters (labels j) b))
    (b : (sigmaCombine families).active (outer.sigma labels)) (ξ : V) :
    MovingEngineChildAdmissible A P R Q parent rowDomain window seminorms Z
      ((sigmaCombine families).rightData (outer.sigma labels) b ξ)
      ((sigmaCombine families).rightParameters (outer.sigma labels) b) :=
  admissible b.val.1 (sigmaActiveOuter families outer labels b).property
    (sigmaActiveInner families outer labels b) ξ

end ActualNormalizedPairFamily
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualNormalizedPairFamily.sigmaCombine_parentGeometry
#print axioms HeckeSkeleton.Moments.EngineStep.ActualNormalizedPairFamily.sigmaCombine_in_fixed_window
#print axioms HeckeSkeleton.Moments.EngineStep.ActualNormalizedPairFamily.sigmaCombine_outputGeometry
#print axioms HeckeSkeleton.Moments.EngineStep.ActualNormalizedPairFamily.sigmaCombine_movingRowInputs
#print axioms HeckeSkeleton.Moments.EngineStep.ActualNormalizedPairFamily.sigmaCombine_parentCharacterInputs
#print axioms HeckeSkeleton.Moments.EngineStep.ActualNormalizedPairFamily.sigmaCombine_normProfileInputs
#print axioms HeckeSkeleton.Moments.EngineStep.ActualNormalizedPairFamily.sigmaCombine_arithmeticAtomInputs
#print axioms HeckeSkeleton.Moments.EngineStep.ActualNormalizedPairFamily.sigmaCombine_parentSlotDictionaries
#print axioms HeckeSkeleton.Moments.EngineStep.ActualNormalizedPairFamily.sigmaCombine_moving_left_admissible
#print axioms HeckeSkeleton.Moments.EngineStep.ActualNormalizedPairFamily.sigmaCombine_moving_right_admissible
