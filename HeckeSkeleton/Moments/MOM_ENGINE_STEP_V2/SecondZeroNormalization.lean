import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.FirstZeroInputBounds
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SecondData
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstAllowanceNormalization

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# T2: the two signed contributions and the original first allowance

The original column interval pays the Euler term and the original
Gauss origin separately. The retained physical radius is enlarged by
its actual maximum, and both branches of that maximum are compared
with the same first Cauchy allowance. The pool tag padding remains
visible until the original pool mass is summed.
-/

noncomputable section
open scoped Classical NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks.SecondZeroProof

open NumberField DedekindZetaZeroFree HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.EngineStep HeckeSkeleton.Moments.EngineInduction
open HeckeSkeleton.Moments.EngineInduction.Source
open FirstZeroProof

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K}

theorem source_sigma_le_one : recipeInductionSigma c ≤ 1 := by
  change min (1 : ℝ) (c.family.lamA / 16000) ≤ 1
  exact min_le_left _ _

theorem source_loss_le_one_div_sixtyfour (p : SourceParameters c) : p.loss ≤ 1 / 64 := by
  have hs : recipeInductionSigma c ≤ 1 := source_sigma_le_one
  linarith [p.loss_small]

/-- One fixed norm box controls the original column total together
with its physical four-loss interval. -/
theorem second_total_window_le_three (p : SourceParameters c) (call : Call c) :
    call.workingParameters.n₁ + call.workingParameters.n₂ +
      call.workingParameters.z + 4 * p.loss ≤ 3 := by
  have ht := working_total_le call
  have hs : recipeInductionSigma c ≤ 1 := source_sigma_le_one
  linarith [p.loss_small]

def secondCountingExponent (p : SourceParameters c) : ℝ := p.loss / 6

theorem secondCountingExponent_pos (p : SourceParameters c) :
    0 < secondCountingExponent p := div_pos p.loss_pos (by norm_num)

theorem second_counting_power_le (p : SourceParameters c)
    (Z a : ℝ) (hZ : 1 ≤ Z) (ha : a + 4 * p.loss ≤ 3) :
    (Z ^ (2 * (a + 4 * p.loss))) ^ secondCountingExponent p ≤ Z ^ p.loss := by
  rw [← Real.rpow_mul (zero_le_one.trans hZ)]
  apply Real.rpow_le_rpow_of_exponent_le hZ
  have h := mul_le_mul_of_nonneg_right ha p.loss_pos.le
  dsimp only [secondCountingExponent]
  nlinarith

/-- Exact cancellation of the two inverse column norms. The second
summand is the actual Gauss origin and is retained in the identity. -/
theorem second_stage_scalar_identity
    (Z Camp A a loss tilt retained enlargement : ℝ) (hZ : 0 < Z) :
    (Camp * Z ^ (-A / 2) * Z ^ (3 * tilt)) ^ 2 *
        (retained * Z ^ enlargement / Z ^ (a - 4 * loss) + 1) *
        Real.sqrt (Z ^ (2 * (a + 4 * loss))) =
      Camp ^ 2 * Z ^ (6 * tilt - A) *
        (retained * Z ^ enlargement * Z ^ (8 * loss) + Z ^ (a + 4 * loss)) := by
  have hsqrt : Real.sqrt (Z ^ (2 * (a + 4 * loss))) = Z ^ (a + 4 * loss) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hZ.le]
    congr 1
    ring
  have hsquare : (Camp * Z ^ (-A / 2) * Z ^ (3 * tilt)) ^ 2 =
      Camp ^ 2 * Z ^ (6 * tilt - A) := by
    calc
      _ = Camp ^ 2 * ((Z ^ (-A / 2) * Z ^ (3 * tilt)) *
          (Z ^ (-A / 2) * Z ^ (3 * tilt))) := by ring
      _ = _ := by
        simp only [← Real.rpow_add hZ]
        congr 2
        ring
  have hratio : Z ^ (a + 4 * loss) / Z ^ (a - 4 * loss) = Z ^ (8 * loss) := by
    rw [← Real.rpow_sub hZ]
    congr 1
    ring
  rw [hsqrt, hsquare]
  calc
    _ = Camp ^ 2 * Z ^ (6 * tilt - A) *
        (retained * Z ^ enlargement *
          (Z ^ (a + 4 * loss) / Z ^ (a - 4 * loss)) + Z ^ (a + 4 * loss)) := by ring
    _ = _ := by rw [hratio]

/-- At most fourteen source losses pay the two scalar contributions.
The physical radius and the original surviving column scale remain. -/
theorem second_stage_scalar_le
    (Z Camp A a loss tilt retained enlargement : ℝ)
    (hZ : 1 ≤ Z) (hloss : 0 ≤ loss) (htilt : tilt ≤ loss) (hretained : 0 ≤ retained) :
    (Camp * Z ^ (-A / 2) * Z ^ (3 * tilt)) ^ 2 *
        (retained * Z ^ enlargement / Z ^ (a - 4 * loss) + 1) *
        Real.sqrt (Z ^ (2 * (a + 4 * loss))) ≤
      Camp ^ 2 * (retained * Z ^ enlargement + Z ^ a) * Z ^ (-A + 14 * loss) := by
  have hZpos : 0 < Z := zero_lt_one.trans_le hZ
  rw [second_stage_scalar_identity Z Camp A a loss tilt retained enlargement hZpos]
  have hdual : Z ^ (6 * tilt - A) * Z ^ (8 * loss) ≤ Z ^ (-A + 14 * loss) := by
    rw [← Real.rpow_add hZpos]
    exact Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have horigin : Z ^ (6 * tilt - A) * Z ^ (a + 4 * loss) ≤
      Z ^ a * Z ^ (-A + 14 * loss) := by
    simp only [← Real.rpow_add hZpos]
    exact Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  calc
    _ = Camp ^ 2 * (retained * Z ^ enlargement *
        (Z ^ (6 * tilt - A) * Z ^ (8 * loss)) +
        Z ^ (6 * tilt - A) * Z ^ (a + 4 * loss)) := by ring
    _ ≤ Camp ^ 2 * (retained * Z ^ enlargement * Z ^ (-A + 14 * loss) +
        Z ^ a * Z ^ (-A + 14 * loss)) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left hdual
          (mul_nonneg hretained (Real.rpow_nonneg hZpos.le _))) horigin) (sq_nonneg Camp)
    _ = _ := by ring

/-- The same selected-side allowance as the original weighted Cauchy
step, expressed in its literal logarithmic ideal lengths. -/
def secondSideAllowance (Z A q R f selected opposite : ℝ) : ℝ :=
  Z ^ (A + q + R + f - selected + firstAllowance selected opposite R)

theorem second_origin_scale_le_allowance
    (Z A q R f selected opposite removed : ℝ)
    (hZ : 1 ≤ Z) (hq : 0 ≤ q) (hR : 0 ≤ R) (hf : 0 ≤ f) (hw : 0 ≤ removed) :
    Z ^ (A - selected - removed) ≤ secondSideAllowance Z A q R f selected opposite := by
  apply Real.rpow_le_rpow_of_exponent_le hZ
  have hallow := firstAllowance_nonneg selected opposite R
  linarith

/-- The maximum defining the actual second radius is paid on each
branch. The moving residual length is bounded by the removed length,
so no new ideal or comparison scale is chosen. -/
theorem second_enlarged_radius_le_allowance
    (Z A m q R f selected opposite removed moving retained padding tagPadding loss : ℝ)
    (hZ : 1 < Z) (hretained : 0 < retained)
    (hselected : 0 ≤ selected) (hopposite : 0 ≤ opposite)
    (hmoving : moving ≤ 2 * removed) (hloss : 0 ≤ loss)
    (hwidth : A ≤ m + q + padding)
    (hretained_upper : retained ≤
      Z ^ (2 * A - selected - opposite + R + f - m + 4 * loss)) :
    retained * Z ^
        (max (opposite - selected + (2 * A - selected - opposite + R + f - m) -
          Real.log retained / Real.log Z - 2 * removed + moving) 0 + tagPadding) ≤
      secondSideAllowance Z A q R f selected opposite *
        Z ^ (tagPadding + padding + 4 * loss) := by
  have hZpos : 0 < Z := zero_lt_one.trans hZ
  have hallow := firstAllowance_nonneg selected opposite R
  have hlog : Z ^ (Real.log retained / Real.log Z) = retained := by
    calc
      _ = Real.exp (Real.log retained) := by
        rw [Real.rpow_def_of_pos hZpos]
        congr 1
        field_simp [(Real.log_pos hZ).ne'] <;> ring
      _ = retained := Real.exp_log hretained
  let X := opposite - selected + (2 * A - selected - opposite + R + f - m) -
    Real.log retained / Real.log Z - 2 * removed + moving
  change retained * Z ^ (max X 0 + tagPadding) ≤ _
  by_cases hx : X ≤ 0
  · rw [max_eq_right hx, zero_add]
    apply (mul_le_mul_of_nonneg_right hretained_upper (Real.rpow_nonneg hZpos.le _)).trans
    simp only [secondSideAllowance, ← Real.rpow_add hZpos]
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    linarith
  · rw [max_eq_left (le_of_not_ge hx)]
    calc
      retained * Z ^ (X + tagPadding) =
          Z ^ (Real.log retained / Real.log Z) * Z ^ (X + tagPadding) := by rw [hlog]
      _ = Z ^ (opposite - selected + (2 * A - selected - opposite + R + f - m) -
          2 * removed + moving + tagPadding) := by
        rw [← Real.rpow_add hZpos]
        congr 1
        dsimp only [X]
        ring
      _ ≤ secondSideAllowance Z A q R f selected opposite *
          Z ^ (tagPadding + padding + 4 * loss) := by
        simp only [secondSideAllowance, ← Real.rpow_add hZpos]
        apply Real.rpow_le_rpow_of_exponent_le hZ.le
        linarith

/-- Both original signed contributions are paid by one and the same
first-side allowance. The actual tag padding is not replaced by a
different pool branch or charged a second time. -/
theorem second_signed_scalar_le_allowance
    (Z Camp A m q R f selected opposite removed moving retained padding tagPadding loss tilt : ℝ)
    (hZ : 1 < Z) (hretained : 0 < retained)
    (hq : 0 ≤ q) (hR : 0 ≤ R) (hf : 0 ≤ f) (hw : 0 ≤ removed)
    (hselected : 0 ≤ selected) (hopposite : 0 ≤ opposite)
    (hmoving : moving ≤ 2 * removed) (hloss : 0 ≤ loss) (htilt : tilt ≤ loss)
    (hpadding : 0 ≤ padding) (htag : 0 ≤ tagPadding)
    (hwidth : A ≤ m + q + padding)
    (hretained_upper : retained ≤
      Z ^ (2 * A - selected - opposite + R + f - m + 4 * loss)) :
    (Camp * Z ^ (-A / 2) * Z ^ (3 * tilt)) ^ 2 *
        (retained * Z ^
          (max (opposite - selected + (2 * A - selected - opposite + R + f - m) -
            Real.log retained / Real.log Z - 2 * removed + moving) 0 + tagPadding) /
          Z ^ (A - selected - removed - 4 * loss) + 1) *
        Real.sqrt (Z ^ (2 * (A - selected - removed + 4 * loss))) ≤
      2 * Camp ^ 2 * secondSideAllowance Z A q R f selected opposite *
        Z ^ (-A + tagPadding + padding + 18 * loss) := by
  have hZpos : 0 < Z := zero_lt_one.trans hZ
  let enlargement := max
    (opposite - selected + (2 * A - selected - opposite + R + f - m) -
      Real.log retained / Real.log Z - 2 * removed + moving) 0 + tagPadding
  let allowance := secondSideAllowance Z A q R f selected opposite
  have hallowance : 0 ≤ allowance := Real.rpow_nonneg hZpos.le _
  have hE : 1 ≤ Z ^ (tagPadding + padding + 4 * loss) :=
    Real.one_le_rpow hZ.le (by linarith)
  have hradius : retained * Z ^ enlargement ≤
      allowance * Z ^ (tagPadding + padding + 4 * loss) :=
    second_enlarged_radius_le_allowance Z A m q R f selected opposite removed moving
      retained padding tagPadding loss hZ hretained hselected hopposite hmoving hloss
      hwidth hretained_upper
  have horigin : Z ^ (A - selected - removed) ≤
      allowance * Z ^ (tagPadding + padding + 4 * loss) :=
    (second_origin_scale_le_allowance Z A q R f selected opposite removed
      hZ.le hq hR hf hw).trans
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hE hallowance)
  have hsum : retained * Z ^ enlargement + Z ^ (A - selected - removed) ≤
      2 * allowance * Z ^ (tagPadding + padding + 4 * loss) :=
    (add_le_add hradius horigin).trans_eq (by ring)
  calc
    _ ≤ Camp ^ 2 * (retained * Z ^ enlargement + Z ^ (A - selected - removed)) *
        Z ^ (-A + 14 * loss) :=
      second_stage_scalar_le Z Camp A (A - selected - removed) loss tilt retained
        enlargement hZ.le hloss htilt hretained.le
    _ ≤ Camp ^ 2 * (2 * allowance * Z ^ (tagPadding + padding + 4 * loss)) *
        Z ^ (-A + 14 * loss) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsum (sq_nonneg Camp)) (Real.rpow_nonneg hZpos.le _)
    _ = 2 * Camp ^ 2 * allowance *
        (Z ^ (tagPadding + padding + 4 * loss) * Z ^ (-A + 14 * loss)) := by ring
    _ = _ := by
      rw [← Real.rpow_add hZpos]
      congr 2
      ring

variable {call : Call c} {p : SourceParameters c}

/-- The allowance contains only the original three common ideal
lengths and the unchanged working support budget. -/
def sourceSideAllowance (source : PhysicalSource call p) : ℝ :=
  secondSideAllowance call.base
    (call.workingParameters.n₁ + call.workingParameters.n₂ + call.workingParameters.z)
    call.workingParameters.q
    (idealLogLength call.base (firstActiveRadical source.first.selected.val source.first.opposite.val))
    (idealLogLength call.base source.first.complementary.val)
    (idealLogLength call.base source.first.selected.val)
    (idealLogLength call.base source.first.opposite.val)

def sourceColumnExponent (source : PhysicalSource call p) : ℝ :=
  call.workingParameters.n₁ + call.workingParameters.n₂ + call.workingParameters.z -
    idealLogLength call.base source.first.selected.val -
    source.first.tag.removedLength call.base

theorem source_column_exponent_le_three (source : PhysicalSource call p) :
    sourceColumnExponent source + 4 * p.loss ≤ 3 := by
  have hselected := idealLogLength_nonneg call.base call.domain.scale
    source.first.selected.val (nonZeroDivisors.coe_ne_zero _)
  have hremoved := source.first.tag.removedLength_nonneg call.base call.domain.scale
  have htotal := second_total_window_le_three p call
  dsimp only [sourceColumnExponent]
  linarith

/-- A genuine nonzero source coefficient supplies an actual ideal
of norm at least one inside the upper column window. -/
theorem source_column_window_nonneg (source : PhysicalSource call p)
    (windows : source.Windows)
    (hactive : ∃ i ∈ source.source.columns, source.source.coefficient i ≠ 0) :
    0 ≤ sourceColumnExponent source + 4 * p.loss := by
  obtain ⟨i, hi, hcoeff⟩ := hactive
  have hone : 1 ≤ (Arithmetic.data c).exteriorNorm (source.source.ideal i) :=
    idealNorm_ge_one _ (source.source.ideal i).property.1
  have hupper := hone.trans (windows.column_upper i hi hcoeff)
  apply (Real.rpow_le_rpow_left_iff call.domain.scale).mp
  simpa only [Real.rpow_zero] using hupper

theorem source_product_window_one_le (source : PhysicalSource call p)
    (windows : source.Windows)
    (hactive : ∃ i ∈ source.source.columns, source.source.coefficient i ≠ 0) :
    1 ≤ call.base ^ (2 * (sourceColumnExponent source + 4 * p.loss)) :=
  Real.one_le_rpow call.domain.scale.le
    (mul_nonneg (by norm_num) (source_column_window_nonneg source windows hactive))

theorem source_selected_norm_le_cube (source : PhysicalSource call p)
    (windows : source.Windows)
    (hactive : ∃ i ∈ source.source.columns, source.source.coefficient i ≠ 0) :
    (Ideal.absNorm source.first.selected.val : ℝ) ≤ call.base ^ (3 : ℝ) := by
  have hwindow := source_column_window_nonneg source windows hactive
  have hremoved := source.first.tag.removedLength_nonneg call.base call.domain.scale
  have htotal := second_total_window_le_three p call
  have hselected : idealLogLength call.base source.first.selected.val ≤ 3 := by
    dsimp only [sourceColumnExponent] at hwindow
    linarith
  rw [← rpow_idealLogLength call.base call.domain.scale
    source.first.selected.val (nonZeroDivisors.coe_ne_zero _)]
  exact Real.rpow_le_rpow_of_exponent_le call.domain.scale.le hselected

theorem original_tag_moving_le_twice_removed (tag : OriginalNominalTag K) :
    tag.movingLength call.base ≤ 2 * tag.removedLength call.base := by
  cases tag with
  | direct => norm_num [OriginalNominalTag.movingLength, OriginalNominalTag.removedLength]
  | main => norm_num [OriginalNominalTag.movingLength, OriginalNominalTag.removedLength]
  | error e prime =>
      have hlength := idealLogLength_nonneg call.base call.domain.scale prime.asIdeal prime.ne_bot
      have hmove := amplifier_error_moving_le e (idealLogLength call.base prime.asIdeal) hlength
      have hremoved : 0 ≤ (e.multiplicity : ℝ) * idealLogLength call.base prime.asIdeal :=
        mul_nonneg (Nat.cast_nonneg _) hlength
      dsimp only [OriginalNominalTag.movingLength, OriginalNominalTag.removedLength]
      linarith

/-- Literal physical windows instantiate the preceding numerical
lemma. Both signed terms and the actual pool tag are still visible. -/
theorem source_signed_scalar_le_allowance (source : PhysicalSource call p)
    (windows : source.Windows) (hrows : source.source.rows.Nonempty) (Camp : ℝ) :
    (Camp * call.base ^ (-(call.workingParameters.n₁ + call.workingParameters.n₂ +
        call.workingParameters.z) / 2) * call.base ^ (3 * p.tilt)) ^ 2 *
        (source.first.retainedScale * call.base ^ source.enlargement /
          call.base ^ (sourceColumnExponent source - 4 * p.loss) + 1) *
        Real.sqrt (call.base ^ (2 * (sourceColumnExponent source + 4 * p.loss))) ≤
      2 * Camp ^ 2 * sourceSideAllowance source *
        call.base ^ (-(call.workingParameters.n₁ + call.workingParameters.n₂ +
          call.workingParameters.z) + source.first.tag.padding (recipeInductionSigma c) +
          recipeInductionSigma c / 16 + 18 * p.loss) := by
  have hsigma : 0 < recipeInductionSigma c := (recipeInduction_budget (c := c)).1
  have hselected := idealLogLength_nonneg call.base call.domain.scale
    source.first.selected.val (nonZeroDivisors.coe_ne_zero _)
  have hopposite := idealLogLength_nonneg call.base call.domain.scale
    source.first.opposite.val (nonZeroDivisors.coe_ne_zero _)
  have hradical := idealLogLength_nonneg call.base call.domain.scale
    (firstActiveRadical source.first.selected.val source.first.opposite.val)
    (firstActiveRadical_ne_zero _ _)
  have hcomplement := idealLogLength_nonneg call.base call.domain.scale
    source.first.complementary.val (nonZeroDivisors.coe_ne_zero _)
  have hremoved := source.first.tag.removedLength_nonneg call.base call.domain.scale
  have htag : 0 ≤ source.first.tag.padding (recipeInductionSigma c) := by
    cases source.first.tag <;> simp only [OriginalNominalTag.padding] <;> positivity
  have hwidth : call.workingParameters.n₁ + call.workingParameters.n₂ +
      call.workingParameters.z ≤ call.workingParameters.m + call.workingParameters.q +
        recipeInductionSigma c / 16 := by
    rw [working_total_eq, working_width]
    exact call.domain.padded_core
  exact second_signed_scalar_le_allowance call.base Camp
    (call.workingParameters.n₁ + call.workingParameters.n₂ + call.workingParameters.z)
    call.workingParameters.m call.workingParameters.q
    (idealLogLength call.base (firstActiveRadical source.first.selected.val source.first.opposite.val))
    (idealLogLength call.base source.first.complementary.val)
    (idealLogLength call.base source.first.selected.val)
    (idealLogLength call.base source.first.opposite.val)
    (source.first.tag.removedLength call.base) (source.first.tag.movingLength call.base)
    source.first.retainedScale (recipeInductionSigma c / 16)
    (source.first.tag.padding (recipeInductionSigma c)) p.loss p.tilt
    call.domain.scale source.first.retainedScale_pos (working_q_nonneg call)
    hradical hcomplement hremoved hselected hopposite
    (original_tag_moving_le_twice_removed (call := call) source.first.tag)
    p.loss_pos.le p.tilt_le_loss (div_nonneg hsigma.le (by norm_num)) htag hwidth
    (windows.retained_upper hrows)

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tasks.SecondZeroProof
