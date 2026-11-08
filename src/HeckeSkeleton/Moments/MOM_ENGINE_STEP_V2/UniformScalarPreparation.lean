module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.UniformOrderPreparation
public import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.FiniteProfileConstants

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# U1: actual numerical envelopes and their finite-rank maxima

The profile amplitude is already fixed by the requested finite orders.
Addition pays all four terminal terms and multiplication pays the
arithmetic/profile mass product. Only these real coefficients, height
degrees and thresholds enter the finite maxima.
-/

noncomputable section

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open NumberField HeckeGeneral.ThetaSkeleton.Global EngineInduction

variable {K : Type} [Field K] [NumberField K]

structure HeightEnvelope where
  coefficient : ℝ
  degree : ℝ
  threshold : ℝ
  coefficient_nonneg : 0 ≤ coefficient
  degree_nonneg : 0 ≤ degree
  threshold_one_le : 1 ≤ threshold

namespace HeightEnvelope

def value (E : HeightEnvelope) (height : ℝ) : ℝ :=
  E.coefficient * (1 + height) ^ E.degree

theorem value_nonneg (E : HeightEnvelope) {height : ℝ} (hheight : 0 ≤ height) :
    0 ≤ E.value height :=
  mul_nonneg E.coefficient_nonneg (Real.rpow_nonneg (by linarith) _)

def add (left right : HeightEnvelope) : HeightEnvelope where
  coefficient := left.coefficient + right.coefficient
  degree := left.degree + right.degree
  threshold := max left.threshold right.threshold
  coefficient_nonneg := add_nonneg left.coefficient_nonneg right.coefficient_nonneg
  degree_nonneg := add_nonneg left.degree_nonneg right.degree_nonneg
  threshold_one_le := left.threshold_one_le.trans (le_max_left _ _)

def mul (left right : HeightEnvelope) : HeightEnvelope where
  coefficient := left.coefficient * right.coefficient
  degree := left.degree + right.degree
  threshold := max left.threshold right.threshold
  coefficient_nonneg := mul_nonneg left.coefficient_nonneg right.coefficient_nonneg
  degree_nonneg := add_nonneg left.degree_nonneg right.degree_nonneg
  threshold_one_le := left.threshold_one_le.trans (le_max_left _ _)

theorem add_value (left right : HeightEnvelope) {height : ℝ} (hheight : 0 ≤ height) :
    left.value height + right.value height ≤ (left.add right).value height := by
  have hl : left.coefficient * (1 + height) ^ left.degree ≤
      left.coefficient * (1 + height) ^ (left.degree + right.degree) :=
    mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ 1 + height)
      (le_add_of_nonneg_right right.degree_nonneg)) left.coefficient_nonneg
  have hr : right.coefficient * (1 + height) ^ right.degree ≤
      right.coefficient * (1 + height) ^ (left.degree + right.degree) :=
    mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ 1 + height)
      (le_add_of_nonneg_left left.degree_nonneg)) right.coefficient_nonneg
  exact (add_le_add hl hr).trans_eq (by simp only [value, add]; ring)

theorem value_le_add_left (left right : HeightEnvelope) {height : ℝ}
    (hheight : 0 ≤ height) : left.value height ≤ (left.add right).value height :=
  (le_add_of_nonneg_right (right.value_nonneg hheight)).trans (left.add_value right hheight)

theorem value_le_add_right (left right : HeightEnvelope) {height : ℝ}
    (hheight : 0 ≤ height) : right.value height ≤ (left.add right).value height :=
  (le_add_of_nonneg_left (left.value_nonneg hheight)).trans (left.add_value right hheight)

theorem mul_value (left right : HeightEnvelope) {height : ℝ} (hheight : 0 ≤ height) :
    left.value height * right.value height = (left.mul right).value height := by
  unfold value mul
  rw [Real.rpow_add (by linarith : 0 < 1 + height)]
  ring

def finite (depth : ℕ) (E : ℕ → HeightEnvelope) : HeightEnvelope where
  coefficient := finiteStageBound depth (fun rank => (E rank).coefficient)
  degree := finiteStageBound depth (fun rank => (E rank).degree)
  threshold := finiteStageBound depth (fun rank => (E rank).threshold)
  coefficient_nonneg := (finiteStageBound_pos _ _).le
  degree_nonneg := (finiteStageBound_pos _ _).le
  threshold_one_le := (by norm_num : (1 : ℝ) ≤ 2).trans (finiteStageBound_two_le _ _)

theorem value_le_finite (depth : ℕ) (E : ℕ → HeightEnvelope) {rank : ℕ}
    (hrank : rank ≤ depth) {height : ℝ} (hheight : 0 ≤ height) :
    (E rank).value height ≤ (finite depth E).value height :=
  finiteStageBound_height_envelope depth (fun r => (E r).coefficient)
    (fun r => (E r).degree) hrank hheight

theorem threshold_le_finite (depth : ℕ) (E : ℕ → HeightEnvelope)
    {rank : ℕ} (hrank : rank ≤ depth) :
    (E rank).threshold ≤ (finite depth E).threshold :=
  le_finiteStageBound depth (fun r => (E r).threshold) hrank

end HeightEnvelope

namespace UniformCost

def envelope (cost : UniformCost) (amplitude : ℝ) (hamplitude : 0 ≤ amplitude) :
    HeightEnvelope where
  coefficient := cost.coefficient * amplitude ^ cost.profileDegree
  degree := cost.heightDegree
  threshold := cost.threshold
  coefficient_nonneg := mul_nonneg cost.coefficient_nonneg (pow_nonneg hamplitude _)
  degree_nonneg := cost.heightDegree_nonneg
  threshold_one_le := cost.threshold_one_le

theorem envelope_value (cost : UniformCost) (amplitude : ℝ)
    (hamplitude : 0 ≤ amplitude) (height : ℝ) :
    (cost.envelope amplitude hamplitude).value height = cost.value amplitude height := rfl

end UniformCost

namespace UniformCosts

variable (costs : UniformCosts) (orders : Finset (ℕ × ℕ))
variable (amplitude : ℝ) (hamplitude : 0 ≤ amplitude)

def terminalEnvelope : HeightEnvelope :=
  ((((costs.firstZero orders).envelope amplitude hamplitude).add
      ((costs.secondZero orders).envelope amplitude hamplitude)).add
        ((costs.exceptional orders).envelope amplitude hamplitude)).add
          ((costs.tail orders).envelope amplitude hamplitude)

def massEnvelope : HeightEnvelope :=
  ((costs.arithmeticMass orders).envelope amplitude hamplitude).mul
    ((costs.profileMass orders).envelope amplitude hamplitude)

def totalEnvelope : HeightEnvelope :=
  (costs.terminalEnvelope orders amplitude hamplitude).add
    (costs.massEnvelope orders amplitude hamplitude)

theorem terminalEnvelope_bound {height : ℝ} (hheight : 0 ≤ height) :
    (costs.firstZero orders).value amplitude height +
      (costs.secondZero orders).value amplitude height +
        (costs.exceptional orders).value amplitude height +
          (costs.tail orders).value amplitude height ≤
      (costs.terminalEnvelope orders amplitude hamplitude).value height := by
  let first := (costs.firstZero orders).envelope amplitude hamplitude
  let second := (costs.secondZero orders).envelope amplitude hamplitude
  let exceptional := (costs.exceptional orders).envelope amplitude hamplitude
  let tail := (costs.tail orders).envelope amplitude hamplitude
  exact (add_le_add (add_le_add (first.add_value second hheight)
    (le_refl (exceptional.value height))) (le_refl (tail.value height))).trans
      ((add_le_add ((first.add second).add_value exceptional hheight)
        (le_refl (tail.value height))).trans
          (((first.add second).add exceptional).add_value tail hheight))

theorem massEnvelope_eq {height : ℝ} (hheight : 0 ≤ height) :
    (costs.arithmeticMass orders).value amplitude height *
      (costs.profileMass orders).value amplitude height =
        (costs.massEnvelope orders amplitude hamplitude).value height :=
  HeightEnvelope.mul_value
    ((costs.arithmeticMass orders).envelope amplitude hamplitude)
    ((costs.profileMass orders).envelope amplitude hamplitude) hheight

theorem thresholds_le_total :
    (costs.firstZero orders).threshold ≤
        (costs.totalEnvelope orders amplitude hamplitude).threshold ∧
    (costs.secondZero orders).threshold ≤
        (costs.totalEnvelope orders amplitude hamplitude).threshold ∧
    (costs.exceptional orders).threshold ≤
        (costs.totalEnvelope orders amplitude hamplitude).threshold ∧
    (costs.tail orders).threshold ≤
        (costs.totalEnvelope orders amplitude hamplitude).threshold ∧
    (costs.arithmeticMass orders).threshold ≤
        (costs.totalEnvelope orders amplitude hamplitude).threshold ∧
    (costs.profileMass orders).threshold ≤
        (costs.totalEnvelope orders amplitude hamplitude).threshold := by
  simp only [totalEnvelope, terminalEnvelope, massEnvelope, UniformCost.envelope,
    HeightEnvelope.add, HeightEnvelope.mul]
  exact ⟨(le_max_left _ _).trans ((le_max_left _ _).trans
      ((le_max_left _ _).trans (le_max_left _ _))),
    (le_max_right _ _).trans ((le_max_left _ _).trans
      ((le_max_left _ _).trans (le_max_left _ _))),
    (le_max_right _ _).trans ((le_max_left _ _).trans (le_max_left _ _)),
    (le_max_right _ _).trans (le_max_left _ _),
    (le_max_left _ _).trans (le_max_right _ _),
    (le_max_right _ _).trans (le_max_right _ _)⟩

end UniformCosts

namespace UniformScalarPreparation

open UniformOrderPreparation

variable (c : TargetContext K) (frame : SourceFrame) (costs : UniformCosts)

def atRank (rank : ℕ) : HeightEnvelope :=
  let J := UniformOrderPreparation.atRank c frame costs rank
  costs.totalEnvelope (childOrders c frame J) (amplitude c frame costs J)
    (zero_le_one.trans (amplitude_one_le c frame costs J))

def uniform : HeightEnvelope :=
  HeightEnvelope.finite (rankBound c) (atRank c frame costs)

end UniformScalarPreparation
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.HeightEnvelope.value_le_finite
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.UniformCosts.terminalEnvelope_bound
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.UniformCosts.thresholds_le_total
