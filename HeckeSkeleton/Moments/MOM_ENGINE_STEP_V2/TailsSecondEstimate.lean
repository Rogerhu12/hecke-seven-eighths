import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.TailsSecondGeometry
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.TailsFirstEstimate

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Paying the second physical tail with its prescribed cutoff

This file performs the scalar assembly after the literal finite source
counts, coefficients, row fibres, kernel mass and geometric windows have
been proved. The positive second cutoff exponent is kept unchanged; only
the fixed Schwartz decay order is chosen to pay the resulting degree.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails

open EngineStep EngineInduction EngineInduction.Source
open NumberField IsDedekindDomain MeasureTheory DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Bridge HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.ThetaSkeleton.Global HeckePort.Moments

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

/-- Numerical constants for a proved bound on an original physical
source. They are fixed before the moving call or its source labels. -/
structure PhysicalTailBudget where
  columnConstant : ℝ
  columnConstant_nonneg : 0 ≤ columnConstant
  columnDegree : ℝ
  coefficientConstant : ℝ
  coefficientConstant_nonneg : 0 ≤ coefficientConstant
  coefficientDegree : ℝ
  profileDegree : ℕ
  rowConstant : ℝ
  rowConstant_nonneg : 0 ≤ rowConstant
  rowDegree : ℝ
  outerConstant : ℝ
  outerConstant_nonneg : 0 ≤ outerConstant
  outerDegree : ℝ
  kernelMass : ℝ
  kernelMass_nonneg : 0 ≤ kernelMass
  retainedDegree : ℝ
  lengthBound : ℝ

namespace PhysicalTailBudget

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

structure Holds (budget : PhysicalTailBudget) (input : ProfileInput call)
    (source : PhysicalSource call p) : Prop where
  columns : ((physicalActiveColumns source).card : ℝ) ≤
    budget.columnConstant * call.base ^ budget.columnDegree
  coefficient : ∀ i ∈ source.source.columns, ‖source.source.coefficient i‖ ≤
    budget.coefficientConstant * input.amplitude ^ budget.profileDegree *
      call.base ^ budget.coefficientDegree
  rows : (source.source.rows.card : ℝ) ≤ budget.rowConstant * call.base ^ budget.rowDegree
  outer : source.outerWeight ≤ budget.outerConstant * call.base ^ budget.outerDegree
  kernel : (actualFourierMeasure source.firstKernel).real Set.univ ≤ budget.kernelMass
  retained : source.first.retainedScale ≤ call.base ^ budget.retainedDegree
  activeLength : idealLogLength call.base
    (firstActiveRadical source.first.selected.val source.first.opposite.val) ≤ budget.lengthBound
  complementaryLength : idealLogLength call.base source.first.complementary.val ≤ budget.lengthBound

def rawCoefficient (budget : PhysicalTailBudget) (c : TargetContext K)
    (orders : Finset (ℕ × ℕ)) : ℝ :=
  2 * firstTailFieldConstant K * emptyMaskNorm c * originalKernelSeminorm c orders *
    budget.columnConstant ^ 2 * budget.coefficientConstant ^ 2

theorem rawCoefficient_nonneg (budget : PhysicalTailBudget) (c : TargetContext K)
    (orders : Finset (ℕ × ℕ)) : 0 ≤ budget.rawCoefficient c orders := by
  have hf := firstTailFieldConstant_nonneg (K := K)
  have hm := (emptyMaskNorm_pos c).le
  have hs := originalKernelSeminorm_nonneg c orders
  dsimp only [rawCoefficient]
  positivity

def rawDegree (budget : PhysicalTailBudget) (c : TargetContext K) (p : SourceParameters c) : ℝ :=
  2 * budget.columnDegree + 2 * budget.coefficientDegree + 2 * secondColumnExponent c p +
    max (secondRadiusExponent c budget.retainedDegree budget.lengthBound)
      (2 * secondColumnExponent c p)

def coefficient (budget : PhysicalTailBudget) (c : TargetContext K)
    {decay : ℝ} (estimate : UniformEstimate c decay) : ℝ :=
  (budget.outerConstant * budget.rowConstant) *
    (budget.kernelMass * (estimate.coefficient * budget.rawCoefficient c estimate.orders))

theorem coefficient_nonneg (budget : PhysicalTailBudget) (c : TargetContext K)
    {decay : ℝ} (estimate : UniformEstimate c decay) :
    0 ≤ budget.coefficient c estimate :=
  mul_nonneg (mul_nonneg budget.outerConstant_nonneg budget.rowConstant_nonneg)
    (mul_nonneg budget.kernelMass_nonneg
      (mul_nonneg estimate.coefficient_nonneg (budget.rawCoefficient_nonneg c estimate.orders)))

def degree (budget : PhysicalTailBudget) (c : TargetContext K) (p : SourceParameters c) : ℝ :=
  budget.outerDegree + budget.rowDegree + budget.rawDegree c p

private theorem rpow_sq (Z : ℝ) (hZ : 0 < Z) (x : ℝ) :
    (Z ^ x) ^ 2 = Z ^ (2 * x) := by
  rw [pow_two, ← Real.rpow_add hZ]
  congr 1
  ring

theorem rawTailMass_bound (budget : PhysicalTailBudget)
    (input : ProfileInput call) (hactive : call.Active)
    (source : SecondSource call p) (hs : source.Realizes)
    (hw : source.physical.Windows) (hb : budget.Holds input source.physical)
    (orders : Finset (ℕ × ℕ)) :
    source.stage.rawTailMass orders ≤
      budget.rawCoefficient c orders * input.amplitude ^ (2 * budget.profileDegree) *
        call.base ^ budget.rawDegree c p := by
  let N := budget.columnConstant * call.base ^ budget.columnDegree
  let A := budget.coefficientConstant * input.amplitude ^ budget.profileDegree *
    call.base ^ budget.coefficientDegree
  let X := call.base ^ secondColumnExponent c p
  let R := call.base ^ secondRadiusExponent c budget.retainedDegree budget.lengthBound
  let M := max (secondRadiusExponent c budget.retainedDegree budget.lengthBound)
    (2 * secondColumnExponent c p)
  have hamp := zero_le_one.trans input.amplitude_one_le
  have hN : 0 ≤ N := mul_nonneg budget.columnConstant_nonneg (Real.rpow_nonneg call.base_pos.le _)
  have hA : 0 ≤ A := mul_nonneg
    (mul_nonneg budget.coefficientConstant_nonneg (pow_nonneg hamp _))
    (Real.rpow_nonneg call.base_pos.le _)
  have hX : 0 ≤ X := Real.rpow_nonneg call.base_pos.le _
  have hR : 0 ≤ R := Real.rpow_nonneg call.base_pos.le _
  have hradius := second_inverseRadius_le source hs hactive budget.retainedDegree
    budget.lengthBound hb.retained hb.activeLength hb.complementaryLength
  have hraw := second_rawTailMass_le source hs orders N A X R hN hA hX hR hb.columns
    hb.coefficient (fun i hi => physical_active_ideal_le source.physical hw i hi) hradius
  have hRX : R + X ^ 2 ≤ 2 * call.base ^ M := by
    have hr : R ≤ call.base ^ M :=
      Real.rpow_le_rpow_of_exponent_le call.domain.scale.le (le_max_left _ _)
    have hx : X ^ 2 ≤ call.base ^ M := by
      rw [show X ^ 2 = call.base ^ (2 * secondColumnExponent c p) from
        rpow_sq call.base call.base_pos _]
      exact Real.rpow_le_rpow_of_exponent_le call.domain.scale.le (le_max_right _ _)
    linarith
  have hinputPow : (input.amplitude ^ budget.profileDegree) ^ 2 =
      input.amplitude ^ (2 * budget.profileDegree) := by
    rw [← pow_mul, Nat.mul_comm budget.profileDegree 2]
  calc
    _ ≤ N ^ 2 * (A ^ 2 * originalKernelSeminorm c orders) *
        (X ^ 2 * (firstTailFieldConstant K * emptyMaskNorm c * (R + X ^ 2))) := hraw
    _ ≤ N ^ 2 * (A ^ 2 * originalKernelSeminorm c orders) *
        (X ^ 2 * (firstTailFieldConstant K * emptyMaskNorm c * (2 * call.base ^ M))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hRX
            (mul_nonneg firstTailFieldConstant_nonneg (emptyMaskNorm_pos c).le))
          (sq_nonneg X))
        (mul_nonneg (sq_nonneg N)
          (mul_nonneg (sq_nonneg A) (originalKernelSeminorm_nonneg c orders)))
    _ = _ := by
      simp only [N, A, X, M, mul_pow, hinputPow, rpow_sq call.base call.base_pos,
        rawCoefficient, rawDegree, Real.rpow_add call.base_pos]
      ring

theorem tail_bound (budget : PhysicalTailBudget)
    (input : ProfileInput call) (hactive : call.Active)
    (source : SecondSource call p) (hs : source.Realizes)
    (hw : source.physical.Windows) (hb : budget.Holds input source.physical)
    {decay : ℝ} (estimate : UniformEstimate c decay) :
    source.tail ≤ budget.coefficient c estimate *
      input.amplitude ^ (2 * budget.profileDegree) *
        (p.secondCutoff call) ^ (1 - decay) * call.base ^ budget.degree c p := by
  let Raw := budget.rawCoefficient c estimate.orders *
    input.amplitude ^ (2 * budget.profileDegree) * call.base ^ budget.rawDegree c p
  let T := (p.secondCutoff call) ^ (1 - decay)
  have hT : 0 ≤ T := Real.rpow_nonneg (zero_le_one.trans (p.secondCutoff_one call)) _
  have hRaw : 0 ≤ Raw := mul_nonneg
    (mul_nonneg (budget.rawCoefficient_nonneg c estimate.orders)
      (pow_nonneg (zero_le_one.trans input.amplitude_one_le) _))
    (Real.rpow_nonneg call.base_pos.le _)
  have hraw : source.stage.rawTailMass estimate.orders ≤ Raw :=
    budget.rawTailMass_bound input hactive source hs hw hb estimate.orders
  have htail := second_tail_le estimate source
  rw [hs.cutoff] at htail
  have hmass : 0 ≤ (actualFourierMeasure source.physical.firstKernel).real Set.univ :=
    ENNReal.toReal_nonneg
  have hfiber : (source.stage.fiber : ℝ) ≤ budget.rowConstant * call.base ^ budget.rowDegree := by
    rw [hs.fiber]
    exact (Nat.cast_le.mpr (orbitMultiplicity_le_rows source.physical)).trans hb.rows
  have hout : source.physical.outerWeight * (source.stage.fiber : ℝ) ≤
      (budget.outerConstant * call.base ^ budget.outerDegree) *
        (budget.rowConstant * call.base ^ budget.rowDegree) :=
    mul_le_mul hb.outer hfiber (Nat.cast_nonneg _)
      (mul_nonneg budget.outerConstant_nonneg (Real.rpow_nonneg call.base_pos.le _))
  have htailRaw : source.tail ≤ source.physical.outerWeight * (source.stage.fiber : ℝ) *
      ((actualFourierMeasure source.physical.firstKernel).real Set.univ *
        (estimate.coefficient * T * Raw)) := by
    apply htail.trans
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hraw (mul_nonneg estimate.coefficient_nonneg hT)) hmass)
      (mul_nonneg source.physical.outerWeight_nonneg (Nat.cast_nonneg _))
  calc
    _ ≤ source.physical.outerWeight * (source.stage.fiber : ℝ) *
        ((actualFourierMeasure source.physical.firstKernel).real Set.univ *
          (estimate.coefficient * T * Raw)) := htailRaw
    _ ≤ (budget.outerConstant * call.base ^ budget.outerDegree) *
        (budget.rowConstant * call.base ^ budget.rowDegree) *
          (budget.kernelMass * (estimate.coefficient * T * Raw)) :=
      mul_le_mul hout
        (mul_le_mul_of_nonneg_right hb.kernel
          (mul_nonneg (mul_nonneg estimate.coefficient_nonneg hT) hRaw))
        (mul_nonneg hmass (mul_nonneg (mul_nonneg estimate.coefficient_nonneg hT) hRaw))
        (mul_nonneg
          (mul_nonneg budget.outerConstant_nonneg (Real.rpow_nonneg call.base_pos.le _))
          (mul_nonneg budget.rowConstant_nonneg (Real.rpow_nonneg call.base_pos.le _)))
    _ = _ := by
      simp only [Raw, T, coefficient, degree, Real.rpow_add call.base_pos]
      ring

end PhysicalTailBudget

/-- A uniform proved polynomial budget on the actual physical sources
and their exact index count supplies the second certificate. -/
theorem secondTailCertificate_of_physical_bounds
    (c : TargetContext K) (frame : SourceFrame) (p : SourceParameters c)
    (budget : PhysicalTailBudget) (countConstant countDegree : ℝ)
    (hcountConstant : 0 ≤ countConstant)
    (hphysical : ∀ (call : Call c) (input : ProfileInput call), call.frame = frame →
      originalOrders ⊆ input.orders → originalThreshold c call.frame ≤ call.base →
      ∀ (trace : SourceTrace call p), trace.Realizes → ∀ i,
        budget.Holds input (trace.second.source i).physical)
    (hcount : ∀ (call : Call c) (input : ProfileInput call), call.frame = frame →
      originalOrders ⊆ input.orders → originalThreshold c call.frame ≤ call.base →
      ∀ (trace : SourceTrace call p), trace.Realizes →
        (trace.expansion.count : ℝ) ≤ countConstant * call.base ^ countDegree) :
    Nonempty (SecondTailCertificate c frame p) := by
  let degree := countDegree + budget.degree c p
  let decay := tailDecayForWidth degree (-recipeInductionTerminalLoss c) p.secondCutoffExponent
  have hdecay : 1 < decay := tailDecayForWidth_gt_one _ _ _ p.secondCutoff_pos
  obtain ⟨estimate⟩ := exists_uniformEstimate c decay hdecay
  let cost : UniformCost := {
    orders := originalOrders
    coefficient := countConstant * budget.coefficient c estimate
    coefficient_nonneg := mul_nonneg hcountConstant (budget.coefficient_nonneg c estimate)
    profileDegree := 2 * budget.profileDegree
    heightDegree := 0
    heightDegree_nonneg := le_rfl
    threshold := originalThreshold c frame
    threshold_one_le := originalThreshold_one_le c frame }
  refine ⟨{ cost := cost, bound := ?_ }⟩
  intro call input hframe ready trace ht
  have horders : originalOrders ⊆ input.orders := ready.orders
  have hlarge : originalThreshold c call.frame ≤ call.base := by
    rw [hframe]
    exact ready.large
  have hbound (i : Fin trace.expansion.count) : (trace.second.source i).tail ≤
      budget.coefficient c estimate * input.amplitude ^ (2 * budget.profileDegree) *
        (p.secondCutoff call) ^ (1 - decay) * call.base ^ budget.degree c p := by
    apply budget.tail_bound input ht.first.active (trace.second.source i) (ht.second.stage i)
      (by rw [ht.second.physical i]; exact ht.poolWindows i)
      (hphysical call input hframe horders hlarge trace ht i) estimate
  have hconstant : 0 ≤ budget.coefficient c estimate *
      input.amplitude ^ (2 * budget.profileDegree) *
        (p.secondCutoff call) ^ (1 - decay) * call.base ^ budget.degree c p := by
    have hc := budget.coefficient_nonneg c estimate
    have ha := zero_le_one.trans input.amplitude_one_le
    have hcut := zero_le_one.trans (p.secondCutoff_one call)
    positivity
  have hfamily : trace.second.tail ≤
      (countConstant * budget.coefficient c estimate) *
        input.amplitude ^ (2 * budget.profileDegree) *
          (p.secondCutoff call) ^ (1 - decay) * call.base ^ degree := by
    calc
      _ ≤ ∑ _i : Fin trace.expansion.count,
          budget.coefficient c estimate * input.amplitude ^ (2 * budget.profileDegree) *
            (p.secondCutoff call) ^ (1 - decay) * call.base ^ budget.degree c p :=
        Finset.sum_le_sum (fun i _ => hbound i)
      _ = (trace.expansion.count : ℝ) *
          (budget.coefficient c estimate * input.amplitude ^ (2 * budget.profileDegree) *
            (p.secondCutoff call) ^ (1 - decay) * call.base ^ budget.degree c p) := by simp
      _ ≤ (countConstant * call.base ^ countDegree) *
          (budget.coefficient c estimate * input.amplitude ^ (2 * budget.profileDegree) *
            (p.secondCutoff call) ^ (1 - decay) * call.base ^ budget.degree c p) :=
        mul_le_mul_of_nonneg_right (hcount call input hframe horders hlarge trace ht) hconstant
      _ = _ := by rw [show degree = countDegree + budget.degree c p from rfl,
        Real.rpow_add call.base_pos]; ring
  have hcut := fixed_cutoff_power call.base degree degree (-recipeInductionTerminalLoss c)
    p.secondCutoffExponent p.secondCutoffExponent call.domain.scale.le p.secondCutoff_pos le_rfl le_rfl
  calc
    trace.second.normalizedTail ≤ trace.second.tail :=
      normalizedScalar_le call ht.first.active
        (Finset.sum_nonneg (fun _ _ => SecondSource.tail_nonneg _))
    _ ≤ (countConstant * budget.coefficient c estimate) *
        input.amplitude ^ (2 * budget.profileDegree) *
          (p.secondCutoff call) ^ (1 - decay) * call.base ^ degree := hfamily
    _ = ((countConstant * budget.coefficient c estimate) *
        input.amplitude ^ (2 * budget.profileDegree)) *
          ((call.base ^ p.secondCutoffExponent) ^ (1 - decay) * call.base ^ degree) := by
      simp only [SourceParameters.secondCutoff]
      ring
    _ ≤ ((countConstant * budget.coefficient c estimate) *
        input.amplitude ^ (2 * budget.profileDegree)) * call.base ^ recipeInductionTerminalLoss c := by
      apply mul_le_mul_of_nonneg_left (by simpa only [decay, neg_neg] using hcut)
      exact mul_nonneg (mul_nonneg hcountConstant (budget.coefficient_nonneg c estimate))
        (pow_nonneg (zero_le_one.trans input.amplitude_one_le) _)
    _ = _ := by simp only [cost, UniformCost.value, Real.rpow_zero, mul_one]

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails.PhysicalTailBudget.tail_bound
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails.secondTailCertificate_of_physical_bounds
