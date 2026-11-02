import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SecondZeroLocalEstimate
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SecondZeroOrbitMultiplicity
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SecondZeroPoolMass
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SecondZeroFrozenBounds
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SecondZeroContracts

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# T2: one uniform certificate for the actual signed second zero

All constants and thresholds are fixed before the call. The original
first Fourier measure, complete Cauchy index, one pool and actual orbital
fibres are summed explicitly. The parent scalar cancels the first mass
normalization and the original column total cancels the local zero
exponent. The remaining small powers fit the original terminal budget.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks.SecondZeroProof

open EngineStep EngineInduction EngineInduction.Source
open NumberField IsDedekindDomain DedekindZetaZeroFree MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Global FirstZeroProof

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

def secondPoolBound (c : TargetContext K) : ℝ :=
  1 + poolTerminalConstant K (recipeInductionSigma c / 3) 20

theorem secondPoolBound_pos (c : TargetContext K) : 0 < secondPoolBound c := by
  have h := poolTerminalConstant_pos (K := K) (recipeInductionSigma c / 3) 20
    (div_pos (recipeInduction_budget (c := c)).1 (by norm_num)) (by norm_num)
  dsimp only [secondPoolBound]
  linarith

theorem secondPoolBound_one_le (c : TargetContext K) : 1 ≤ secondPoolBound c := by
  have h := poolTerminalConstant_pos (K := K) (recipeInductionSigma c / 3) 20
    (div_pos (recipeInduction_budget (c := c)).1 (by norm_num)) (by norm_num)
  dsimp only [secondPoolBound]
  linarith

/-- Both constructors retain their actual padding. The direct source
uses the unchanged first family; the pooled source uses the single
original density and its exact main/1/6/7 index equivalence. -/
theorem expansion_firstSourceMass_padding_bound
    (frame : SourceFrame) (input : ProfileInput call) (hframe : call.frame = frame)
    (hannulusZ : uniformAnnulus c frame ^ (c.geometry.slots + 2) ≤ call.base ^ p.loss)
    (F : FirstPresentation call p) (hF : F.Realizes)
    (family : FirstCauchyFamily F) (hfamily : family.Realizes)
    (hWindows : ∀ i, (family.source i).Windows)
    (hlarge : ∀ P : PoolPresentation family, P.Realizes → ∀ i,
      2 * ((P.data i).rowExponent / ((recipeInductionSigma c / 3) / 2) +
        (P.data i).frozenExponent / ((recipeInductionSigma c / 3) / 2)) ≤
        call.base ^ (recipeInductionSigma c / 3 - p.loss))
    (expansion : PoolExpansion family) (hexpansion : expansion.Realizes) :
    (∑ i, firstSourceMass (expansion.source i) *
      call.base ^ ((expansion.source i).first.tag.padding (recipeInductionSigma c))) ≤
      secondPoolBound c * call.base ^ (2 * recipeInductionSigma c + p.loss) *
        ∑ i, firstSourceMass (family.source i) := by
  have hsigma := (recipeInduction_budget (c := c)).1
  have hsum : 0 ≤ ∑ i, firstSourceMass (family.source i) :=
    Finset.sum_nonneg (fun i _ => firstSourceMass_nonneg (family.source i))
  cases expansion with
  | direct =>
    change (∑ i, firstSourceMass (family.source i) *
      call.base ^ ((family.source i).first.tag.padding (recipeInductionSigma c))) ≤ _
    have heq : (∑ i, firstSourceMass (family.source i) *
        call.base ^ ((family.source i).first.tag.padding (recipeInductionSigma c))) =
        call.base ^ recipeInductionSigma c * ∑ i, firstSourceMass (family.source i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [hfamily.tag i]
      simp only [OriginalNominalTag.padding]
      ring
    rw [heq]
    apply mul_le_mul_of_nonneg_right _ hsum
    calc
      _ ≤ call.base ^ (2 * recipeInductionSigma c + p.loss) :=
        Real.rpow_le_rpow_of_exponent_le call.domain.scale.le (by linarith [p.loss_pos])
      _ ≤ _ := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right (secondPoolBound_one_le c)
          (Real.rpow_nonneg call.base_pos.le _)
  | pooled P count index source =>
    have hp := pooled_firstSourceMass_padding_le P count index source hexpansion.2.2 20
      (pool_rowExponent_le frame input hframe hannulusZ F hF family hfamily hWindows
        P hexpansion.2.1) (hlarge P hexpansion.2.1)
    apply hp.trans
    apply mul_le_mul_of_nonneg_right _ hsum
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg call.base_pos.le _)
    dsimp only [secondPoolBound]
    linarith

theorem sourceZeroMass_div_parent (source : PhysicalSource call p) :
    sourceZeroMass source / call.parentNormalizer =
      (source.orbitMultiplicity : ℝ) * firstSourceMass source := by
  dsimp only [sourceZeroMass, firstSourceMass]
  ring

/-- The terminal reserve was fixed with the original engine schedule.
Its explicit budget pays all thirty-two small losses and the actual
twice-step pool padding without changing any source parameter. -/
theorem second_zero_loss_le_terminal (p : SourceParameters c) :
    2 * recipeInductionSigma c + recipeInductionSigma c / 16 +
      10 * p.tilt + 22 * p.loss ≤ recipeInductionTerminalLoss c := by
  have hsigma := (recipeInduction_budget (c := c)).1
  have hreserve := (moment_mesh_engine_bounds c.family.lamA_pos).2.1
  have hsmall := p.loss_small
  have htilt := p.tilt_le_loss
  unfold recipeInductionTerminalLoss terminalBudget
  linarith [p.loss_pos]

/-- The original public quantifier order is preserved: the orders,
coefficient, degree and scale threshold precede every moving call and
every actual source trace. -/
theorem uniform_second_zero_certificate (c : TargetContext K)
    (p : SourceParameters c) (frame : SourceFrame) :
    Nonempty (SecondZeroCertificate c frame p) := by
  obtain ⟨Clocal, hClocal, hlocal⟩ := second_zero_local_estimate_uniform c p
  obtain ⟨Cmass, hCmass, hmass⟩ := first_family_mass_uniform c p 5 p.loss
    (by norm_num) p.loss_pos
  obtain ⟨Zannulus, hZannulus, hannulus⟩ := original_annulus_power_threshold
    c.geometry.slots (uniformAnnulus c frame) p.loss p.loss_pos
  obtain ⟨Zpool, hZpool, hpool⟩ := second_pool_mass_threshold c p 20 5
  let coefficient := Clocal * secondOrbitBound c * secondPoolBound c * Cmass
  have hcoefficient : 0 ≤ coefficient := by
    dsimp only [coefficient]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hClocal.le (secondOrbitBound_pos c).le)
        (secondPoolBound_pos c).le) hCmass.le
  let cost : UniformCost := {
    orders := {(0, 0)}
    coefficient := coefficient
    coefficient_nonneg := hcoefficient
    profileDegree := 2 * (c.geometry.slots + 2)
    heightDegree := 0
    heightDegree_nonneg := le_rfl
    threshold := max Zannulus Zpool
    threshold_one_le := hZannulus.le.trans (le_max_left _ _) }
  refine ⟨{ cost := cost, bound := ?_ }⟩
  intro call input hframe hready trace htrace
  have horders : {(0, 0)} ⊆ input.orders := hready.orders
  have hannulusZ : uniformAnnulus c frame ^ (c.geometry.slots + 2) ≤ call.base ^ p.loss :=
    hannulus call.base ((le_max_left _ _).trans hready.large)
  have hpoolZ : Zpool ≤ call.base := (le_max_right _ _).trans hready.large
  have hN : ∀ i ∈ trace.first.source.columns,
      (Arithmetic.data c).exteriorNorm (trace.first.source.ideal i) ≤ call.base ^ (5 : ℝ) :=
    first_complete_column_norm_le_five frame input hframe hannulusZ trace.first htrace.first
  have hlarge (P : PoolPresentation trace.cauchy) (hP : P.Realizes) :
      ∀ i, 2 * ((P.data i).rowExponent / ((recipeInductionSigma c / 3) / 2) +
        (P.data i).frozenExponent / ((recipeInductionSigma c / 3) / 2)) ≤
        call.base ^ (recipeInductionSigma c / 3 - p.loss) :=
    hpool hpoolZ P
      (pool_rowExponent_le frame input hframe hannulusZ trace.first htrace.first
        trace.cauchy htrace.cauchy htrace.firstWindows P hP)
      (pool_frozenExponent_le frame input hframe hannulusZ trace.first htrace.first
        trace.cauchy htrace.cauchy P hP)
  have hexpansionMass := expansion_firstSourceMass_padding_bound frame input hframe
    hannulusZ trace.first htrace.first trace.cauchy htrace.cauchy htrace.firstWindows
    hlarge trace.expansion htrace.expansion
  have hfirstMass : (∑ i, firstSourceMass (trace.cauchy.source i)) ≤
      Cmass * call.base ^ (call.workingParameters.n₁ + call.workingParameters.n₂ +
        call.workingParameters.z + 10 * p.tilt + p.loss) := by
    simpa only [show 2 * (5 : ℝ) = 10 by norm_num, firstSourceMass] using
      hmass trace.first htrace.first trace.cauchy htrace.cauchy hN
  let A := call.workingParameters.n₁ + call.workingParameters.n₂ + call.workingParameters.z
  let amplitude := input.amplitude ^ (2 * (c.geometry.slots + 2))
  let smallPower := call.base ^ (-A + recipeInductionSigma c / 16 + 20 * p.loss)
  have hamplitude : 0 ≤ amplitude := pow_nonneg (zero_le_one.trans input.amplitude_one_le) _
  have hsmallPower : 0 ≤ smallPower := Real.rpow_nonneg call.base_pos.le _
  have hterm (i) : (trace.second.source i).zero / call.parentNormalizer ≤
      (Clocal * amplitude * secondOrbitBound c) *
        (firstSourceMass (trace.expansion.source i) * call.base ^
          ((trace.expansion.source i).first.tag.padding (recipeInductionSigma c))) *
        smallPower := by
    have hzero := hlocal frame call input horders hframe hannulusZ trace htrace i
    have horbit := expansion_orbit_multiplicity_le frame input hframe hannulusZ
      trace.first htrace.first trace.cauchy htrace.cauchy htrace.firstWindows
      trace.expansion htrace.expansion i
    calc
      _ ≤ (Clocal * amplitude * sourceZeroMass (trace.expansion.source i) *
          call.base ^ (-A + (trace.expansion.source i).first.tag.padding
            (recipeInductionSigma c) + recipeInductionSigma c / 16 + 20 * p.loss)) /
          call.parentNormalizer := div_le_div_of_nonneg_right hzero call.parentNormalizer_pos.le
      _ = (Clocal * amplitude * ((trace.expansion.source i).orbitMultiplicity : ℝ)) *
          (firstSourceMass (trace.expansion.source i) * call.base ^
            ((trace.expansion.source i).first.tag.padding (recipeInductionSigma c))) *
          smallPower := by
        rw [show -A + (trace.expansion.source i).first.tag.padding
            (recipeInductionSigma c) + recipeInductionSigma c / 16 + 20 * p.loss =
          (trace.expansion.source i).first.tag.padding (recipeInductionSigma c) +
            (-A + recipeInductionSigma c / 16 + 20 * p.loss) by ring,
          Real.rpow_add call.base_pos]
        dsimp only [sourceZeroMass, firstSourceMass, smallPower]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left horbit (mul_nonneg hClocal.le hamplitude))
          (mul_nonneg (firstSourceMass_nonneg _) (Real.rpow_nonneg call.base_pos.le _)))
        hsmallPower
  have hprefix : 0 ≤ Clocal * amplitude * secondOrbitBound c :=
    mul_nonneg (mul_nonneg hClocal.le hamplitude) (secondOrbitBound_pos c).le
  calc
    trace.second.normalizedZero = ∑ i, (trace.second.source i).zero / call.parentNormalizer := by
      simp only [SecondFamily.normalizedZero, Call.normalizedScalar, SecondFamily.zero,
        Finset.sum_div]
    _ ≤ ∑ i, (Clocal * amplitude * secondOrbitBound c) *
        (firstSourceMass (trace.expansion.source i) * call.base ^
          ((trace.expansion.source i).first.tag.padding (recipeInductionSigma c))) *
        smallPower := Finset.sum_le_sum (fun i _ => hterm i)
    _ = (Clocal * amplitude * secondOrbitBound c) *
        (∑ i, firstSourceMass (trace.expansion.source i) * call.base ^
          ((trace.expansion.source i).first.tag.padding (recipeInductionSigma c))) *
        smallPower := by rw [Finset.mul_sum, Finset.sum_mul]
    _ ≤ (Clocal * amplitude * secondOrbitBound c) *
        (secondPoolBound c * call.base ^ (2 * recipeInductionSigma c + p.loss) *
          ∑ i, firstSourceMass (trace.cauchy.source i)) * smallPower :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hexpansionMass hprefix) hsmallPower
    _ ≤ (Clocal * amplitude * secondOrbitBound c) *
        (secondPoolBound c * call.base ^ (2 * recipeInductionSigma c + p.loss) *
          (Cmass * call.base ^ (A + 10 * p.tilt + p.loss))) * smallPower :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hfirstMass
            (mul_nonneg (secondPoolBound_pos c).le (Real.rpow_nonneg call.base_pos.le _)))
          hprefix) hsmallPower
    _ = coefficient * amplitude * call.base ^
        (2 * recipeInductionSigma c + recipeInductionSigma c / 16 +
          10 * p.tilt + 22 * p.loss) := by
      rw [show 2 * recipeInductionSigma c + recipeInductionSigma c / 16 +
          10 * p.tilt + 22 * p.loss =
        (2 * recipeInductionSigma c + p.loss) + (A + 10 * p.tilt + p.loss) +
          (-A + recipeInductionSigma c / 16 + 20 * p.loss) by ring,
        Real.rpow_add call.base_pos, Real.rpow_add call.base_pos]
      dsimp only [coefficient, smallPower]
      ring
    _ ≤ coefficient * amplitude * call.base ^ recipeInductionTerminalLoss c :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le call.domain.scale.le (second_zero_loss_le_terminal p))
        (mul_nonneg hcoefficient hamplitude)
    _ = cost.value input.amplitude call.request.height *
        call.base ^ recipeInductionTerminalLoss c := by
      simp only [cost, UniformCost.value, Real.rpow_zero, mul_one, amplitude]

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks.SecondZeroProof
