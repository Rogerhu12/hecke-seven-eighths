import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.FirstCauchyContracts
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstAllowanceNormalization

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The actual finite first-Cauchy family

The family enumerates the literal common-support, physical-divisor,
residual-divisor, finite-character and Cauchy-side keys exactly once.
All source fields are copied from the first presentation. No analytic
estimate or profile hypothesis is used in this finite construction.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.S2

open EngineStep EngineInduction EngineInduction.Source
open NumberField IsDedekindDomain MeasureTheory DedekindZetaZeroFree
open DedekindZetaZeroFree.LargeSieve
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open HeckePort.Moments HeckePort.Moments.MobiusRegroup
open HeckePort.IdealMobiusDivisorSum
open UniqueFactorizationMonoid

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

local instance s2CharacterFintype :
    Fintype ((PUnit.{1} × PUnit.{1}) →* Circle) := Fintype.ofFinite _

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

def allowanceTotal (F : FirstPresentation call p) (v : F.source.CommonLabel)
    (D : ((F.source.block v).mask F.source.mask).powerset) : ℝ :=
  call.workingParameters.n₁ + call.workingParameters.n₂ + call.workingParameters.z +
    call.workingParameters.q + idealLogLength call.base (firstActiveRadical v.val.1 v.val.2) +
    idealLogLength call.base (firstPhysicalDivisorIdeal (A := Arithmetic.data c) D.val).val

def normalization (F : FirstPresentation call p) : F.source.Normalization where
  left v D _ _ := firstLeftAllowance call.base (allowanceTotal F v D) v.val.1 v.val.2
  right v D _ _ := firstRightAllowance call.base (allowanceTotal F v D) v.val.1 v.val.2
  left_pos v D _ _ := firstLeftAllowance_pos _ _ call.base_pos _ _
  right_pos v D _ _ := firstRightAllowance_pos _ _ call.base_pos _ _

variable {F : FirstPresentation call p}

theorem key_left_ne_zero (key : FirstCauchyKey F) : key.1.val.1 ≠ 0 := by
  rw [← (FirstCauchyKey.block key).common_left]
  exact (primePowerProduct (FirstCauchyKey.block key).primes
    (FirstCauchyKey.block key).leftMultiplicity).property.1

theorem key_right_ne_zero (key : FirstCauchyKey F) : key.1.val.2 ≠ 0 := by
  rw [← (FirstCauchyKey.block key).common_right]
  exact (primePowerProduct (FirstCauchyKey.block key).primes
    (FirstCauchyKey.block key).rightMultiplicity).property.1

theorem key_residual_ne_zero (key : FirstCauchyKey F) :
    (FirstCauchyKey.residual key).val ≠ 0 := by
  obtain ⟨j, hj, hSj⟩ := Finset.mem_biUnion.mp (FirstCauchyKey.residual key).property
  have hd := (mem_idealDivisors
    ((FirstCauchyKey.piece key).rightData.ideal j).property.1).mp hSj
  intro hzero
  obtain ⟨J, hJ⟩ := hd
  exact ((FirstCauchyKey.piece key).rightData.ideal j).property.1
    (by simpa only [hzero, Ideal.zero_eq_bot, Ideal.bot_mul] using hJ)

def selected (key : FirstCauchyKey F) : HeckeGeneral.Analysis.NonzeroIdeal K :=
  if FirstCauchyKey.side key then ⟨key.1.val.2, key_right_ne_zero key⟩
  else ⟨key.1.val.1, key_left_ne_zero key⟩

def opposite (key : FirstCauchyKey F) : HeckeGeneral.Analysis.NonzeroIdeal K :=
  if FirstCauchyKey.side key then ⟨key.1.val.1, key_left_ne_zero key⟩
  else ⟨key.1.val.2, key_right_ne_zero key⟩

def complementary (key : FirstCauchyKey F) : HeckeGeneral.Analysis.NonzeroIdeal K :=
  ⟨(firstPhysicalDivisorIdeal (A := Arithmetic.data c) key.2.1.val).val,
    (firstPhysicalDivisorIdeal (A := Arithmetic.data c) key.2.1.val).property.1⟩

def residual (key : FirstCauchyKey F) : HeckeGeneral.Analysis.NonzeroIdeal K :=
  ⟨(FirstCauchyKey.residual key).val, key_residual_ne_zero key⟩

def activeIdeal (key : FirstCauchyKey F) : (Arithmetic.data c).Exterior :=
  firstActiveIdeal (FirstCauchyKey.block key).primes
    (FirstCauchyKey.block key).leftMultiplicity
    (FirstCauchyKey.block key).rightMultiplicity

def paidSupport (key : FirstCauchyKey F) : (Arithmetic.data c).Exterior := by
  let d := firstPhysicalDivisorIdeal (A := Arithmetic.data c) key.2.1.val
  refine ⟨call.oldSupport.val * (activeIdeal key).val * d.val,
    mul_ne_zero (mul_ne_zero call.oldSupport.property.1
      (activeIdeal key).property.1) d.property.1, ?_⟩
  exact (((Ideal.isCoprime_iff_sup_eq.mpr call.oldSupport.property.2).mul_left
    (Ideal.isCoprime_iff_sup_eq.mpr (activeIdeal key).property.2)).mul_left
      (Ideal.isCoprime_iff_sup_eq.mpr d.property.2)).sup_eq

def coordinates (key : FirstCauchyKey F) : FirstCoordinates call where
  selected := selected key
  opposite := opposite key
  complementary := complementary key
  residualDivisor := residual key
  firstElement := FirstCauchyKey.firstElement key
  firstRight := FirstCauchyKey.side key
  poolPower := unitExterior (Arithmetic.data c)
  tag := .direct
  retainedScale := max 1 ((F.source.source key.1).divisorPhysicalCutoff key.2.1.val)
  retainedScale_pos := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  fullDeletion := primeSupport (selected key).val
  paidSupport := paidSupport key

theorem outer_nonneg (key : FirstCauchyKey F) (N : F.source.Normalization) :
    0 ≤ FirstCauchyKey.outer key N := by
  have hden : 0 ≤ (if FirstCauchyKey.side key then
      N.right key.1 key.2.1 (FirstCauchyKey.residual key) (FirstCauchyKey.character key)
    else N.left key.1 key.2.1 (FirstCauchyKey.residual key) (FirstCauchyKey.character key)) := by
    split
    · exact (N.right_pos _ _ _ _).le
    · exact (N.left_pos _ _ _ _).le
  exact div_nonneg
    (mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
      (norm_nonneg _))
      (div_nonneg (mul_nonneg
        (mul_nonneg (FirstCauchyKey.piece key).rowBound_nonneg (Real.sqrt_nonneg _))
        (Real.sqrt_nonneg _)) (by norm_num))) hden

def source (key : FirstCauchyKey F) (N : F.source.Normalization) :
    PhysicalSource call p where
  Column := F.source.Column
  source := (FirstCauchyKey.data key).directSource (FirstCauchyKey.coefficient key)
  ancestor := F.index
  multiplier := FirstCauchyKey.multiplier key
  firstKernel := (FirstCauchyKey.chart key).kernel
  firstPoint := FirstCauchyKey.point key
  outerWeight := FirstCauchyKey.outer key N
  outerWeight_nonneg := outer_nonneg key N
  first := coordinates key

def family (F : FirstPresentation call p) : FirstCauchyFamily F where
  normalization := normalization F
  count := Fintype.card (FirstCauchyKey F)
  index := (Fintype.equivFin (FirstCauchyKey F)).symm
  source i := source ((Fintype.equivFin (FirstCauchyKey F)).symm i) (normalization F)

theorem family_realizes (F : FirstPresentation call p) : (family F).Realizes where
  leftAllowance _ _ _ _ := rfl
  rightAllowance _ _ _ _ := rfl
  column _ := rfl
  source _ := HEq.rfl
  ancestor _ := HEq.rfl
  multiplier _ := HEq.rfl
  kernel _ := rfl
  point _ := HEq.rfl
  outer _ := rfl
  selected i := by
    change (selected _).val = _
    unfold selected
    split <;> rfl
  opposite i := by
    change (opposite _).val = _
    unfold opposite
    split <;> rfl
  complementary _ := rfl
  residual _ := rfl
  firstElement _ := rfl
  firstRight _ := rfl
  poolPower _ := rfl
  tag _ := rfl
  retained _ := rfl
  deletion _ := rfl
  paid _ := rfl

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.S2

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.S2.family_realizes
