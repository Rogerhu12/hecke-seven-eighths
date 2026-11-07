module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.UniformScalarPreparation
public import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.FiniteMellinBudget

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# U1: prepare the literal original Mellin models

The recursive node already carries its scheduled Euler control. The
strict width inequality gives positive rank, so the predecessor order
pays the selected Mellin derivatives. Finite rank bounds the actual
Mellin mass; the unchanged source profile budget pays its height power.
-/

noncomputable section

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.UniformMellinPreparation

open NumberField MeasureTheory HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton.Global
open EngineInduction EngineInduction.Source UniformAmplify UniformOrderPreparation

variable {K : Type} [Field K] [NumberField K]
variable (c : TargetContext K) (frame : SourceFrame) (costs : UniformCosts)

local instance uniformReflectionMeasurable : MeasurableSpace (ℕ × Bool) := ⊤
local instance uniformReflectionSingleton : MeasurableSingletonClass (ℕ × Bool) := by
  constructor
  intro x
  trivial

def lower (rank : ℕ) : ℝ :=
  clippedAnnulusLower frame.lower frame.upper (rankBound c) rank

def upper (rank : ℕ) : ℝ := rankedAnnulusUpper frame.upper (rankBound c) rank

theorem lower_pos (rank : ℕ) : 0 < lower c frame rank :=
  clippedAnnulusLower_pos frame.lower_pos _ _

theorem interval (rank : ℕ) : lower c frame rank ≤ upper c frame rank :=
  (clippedAnnulus_bounds frame.lower_pos frame.interval.le _ _).2

def mass (rank : ℕ) : ℝ :=
  mellinStrictMassConstant (K := K) (ω := c.family.omega)
    (ψ := targetCharacter K c) (Ω := CombinedParameter) c.geometry.slots
    (mellinOrder c frame costs (atRank c frame costs rank)) frame.decay
    (lower c frame rank) (upper c frame rank)
    (zero_lt_one.trans frame.decay_gt_one).le (lower_pos c frame rank)
    (interval c frame rank)

theorem mass_nonneg (rank : ℕ) : 0 ≤ mass c frame costs rank :=
  mellinStrictMassConstant_nonneg _ _ _ _ _ _ _ _

def bounds (Cp Hp : ℝ) (hCp : 0 < Cp) (hHp : 0 ≤ Hp) : UniformBounds where
  coefficient := finiteStrictConstant (rankBound c) (mass c frame costs) *
    (1 + Cp) ^ (2 * (c.geometry.slots + 2)) *
      (UniformScalarPreparation.uniform c frame costs).coefficient
  heightDegree := Hp * (2 * (c.geometry.slots + 2) : ℕ) +
    (UniformScalarPreparation.uniform c frame costs).degree
  threshold := (UniformScalarPreparation.uniform c frame costs).threshold ^ (16 : ℕ)
  coefficient_nonneg := mul_nonneg
    (mul_nonneg (finiteStrictConstant_pos _ _).le (pow_nonneg (by linarith) _))
    (UniformScalarPreparation.uniform c frame costs).coefficient_nonneg
  heightDegree_nonneg := add_nonneg (mul_nonneg hHp (Nat.cast_nonneg _))
    (UniformScalarPreparation.uniform c frame costs).degree_nonneg
  threshold_one_le := one_le_pow₀
    (UniformScalarPreparation.uniform c frame costs).threshold_one_le

variable {Cp Hp : ℝ} {B : UniformBounds}

def requestRank (request : SourceRequest c frame (schedule c frame costs) Cp Hp B) : ℕ :=
  parameterCoreRank (recipeInductionSigma c) 2 (recipeInductionSigma c / 16)
    request.parent.parameters

theorem requestRank_pos
    (request : SourceRequest c frame (schedule c frame costs) Cp Hp B) :
    0 < requestRank c frame costs request :=
  parameterCoreRank_pos_of_strict_width (recipeInduction_budget (c := c)).1
    request.domain.width_floor

theorem requestRank_le
    (request : SourceRequest c frame (schedule c frame costs) Cp Hp B) :
    requestRank c frame costs request ≤ rankBound c :=
  (parameterCoreRank_lt_bound request.parent.parameters
    (recipeInduction_budget (c := c)).1 request.node.down.property.width_le).le

theorem originalProfiles
    (request : SourceRequest c frame (schedule c frame costs) Cp Hp B) :
    ModelProfileControl request.parent.data
      (mellinOrder c frame costs (atRank c frame costs (requestRank c frame costs request)) + 2)
      frame.decay (profileFamilyBudget Cp Hp request.height) 0
      (lower c frame (requestRank c frame costs request))
      (upper c frame (requestRank c frame costs request)) 0 := by
  have h := (rankedAnnulusProfilePrimitive_iff 1 (engine c frame costs) frame.reflection
    (recipeInductionSigma c) 2 (recipeInductionSigma c / 16) frame.decay
    (profileFamilyBudget Cp Hp request.height) frame.lower frame.upper
    request.parent.data request.parent.parameters).mp
      request.node.down.property.admissible.2.2.2.2
  exact modelProfileControl_mono_order h
    (engine_atRank_le c frame costs (requestRank_pos c frame costs request))

def prepared (hCp : 0 < Cp) (hHp : 0 ≤ Hp)
    (request : SourceRequest c frame (schedule c frame costs) Cp Hp B) :
    PreparedCall request.parent where
  cap := c.geometry.slots
  order := mellinOrder c frame costs (atRank c frame costs (requestRank c frame costs request))
  weight := frame.decay
  lower := lower c frame (requestRank c frame costs request)
  upper := upper c frame (requestRank c frame costs request)
  weight_nonneg := (zero_lt_one.trans frame.decay_gt_one).le
  lower_pos := lower_pos c frame _
  interval := interval c frame _
  profileBudget := profileFamilyBudget Cp Hp request.height
  profileBudget_one_le := profileFamilyBudget_one_le hCp.le hHp request.height_nonneg
  slot_cap := request.node.down.property.slot_count
  profiles := originalProfiles c frame costs request
  engineCoefficient := (UniformScalarPreparation.uniform c frame costs).coefficient
  engineControl := (1 + request.height) ^ (UniformScalarPreparation.uniform c frame costs).degree
  engineCoefficient_nonneg := (UniformScalarPreparation.uniform c frame costs).coefficient_nonneg
  engineControl_nonneg := Real.rpow_nonneg (by linarith [request.height_nonneg]) _

theorem budget (hCp : 0 < Cp) (hHp : 0 ≤ Hp)
    (request : SourceRequest c frame (schedule c frame costs) Cp Hp B) :
    (prepared c frame costs hCp hHp request).mellinCost ≤
      (bounds c frame costs Cp Hp hCp hHp).coefficient *
        (1 + request.height) ^ (bounds c frame costs Cp Hp hCp hHp).heightDegree := by
  let E := UniformScalarPreparation.uniform c frame costs
  have h := finiteMellin_profile_budget
    (N := rankBound c) (rank := requestRank c frame costs request)
    (cap := c.geometry.slots) (mass := mass c frame costs) (engine := E.coefficient)
    (requestRank_le c frame costs request) (mass_nonneg c frame costs _)
    E.coefficient_nonneg hCp.le hHp request.height_nonneg
  have ht : 0 < 1 + request.height := by linarith [request.height_nonneg]
  change mass c frame costs (requestRank c frame costs request) *
    profileFamilyBudget Cp Hp request.height ^ (2 * (c.geometry.slots + 2)) *
      (E.coefficient * (1 + request.height) ^ E.degree) ≤ _
  calc
    _ = (mass c frame costs (requestRank c frame costs request) *
        profileFamilyBudget Cp Hp request.height ^ (2 * (c.geometry.slots + 2)) *
          E.coefficient) * (1 + request.height) ^ E.degree := by ring
    _ ≤ ((finiteStrictConstant (rankBound c) (mass c frame costs) *
        (1 + Cp) ^ (2 * (c.geometry.slots + 2)) * E.coefficient) *
          (1 + request.height) ^ (Hp * (2 * (c.geometry.slots + 2) : ℕ))) *
            (1 + request.height) ^ E.degree :=
      mul_le_mul_of_nonneg_right h (Real.rpow_nonneg ht.le _)
    _ = _ := by
      change _ = (finiteStrictConstant (rankBound c) (mass c frame costs) *
        (1 + Cp) ^ (2 * (c.geometry.slots + 2)) * E.coefficient) *
          (1 + request.height) ^ (Hp * (2 * (c.geometry.slots + 2) : ℕ) + E.degree)
      rw [Real.rpow_add ht]
      ring

def preparation : UniformPreparation c frame where
  schedule := schedule c frame costs
  bounds Cp Hp hCp _hminimum hHp := bounds c frame costs Cp Hp hCp hHp
  prepared _Cp _Hp hCp _hminimum hHp request := prepared c frame costs hCp hHp request
  budget _Cp _Hp hCp _hminimum hHp request := budget c frame costs hCp hHp request

theorem base_threshold (hCp : 0 < Cp) (hminimum : (schedule c frame costs).minimumCp ≤ Cp)
    (hHp : 0 ≤ Hp)
    (request : (preparation c frame costs).Request Cp Hp hCp hminimum hHp) :
    (UniformScalarPreparation.uniform c frame costs).threshold ≤ request.base :=
  _root_.ExpansionRecipe.shell_base_ge_of_physical_cutoff
    (UniformScalarPreparation.uniform c frame costs).threshold_one_le
    request.large (recipeMoment_shell_lower request.index)

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.UniformMellinPreparation

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.UniformMellinPreparation.originalProfiles
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.UniformMellinPreparation.budget
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.UniformMellinPreparation.base_threshold
