import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.Interface
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# From a common positive Cauchy kernel to the moment recursion

The two separated columns are calibrated to actual child `Node.energy`
values.  Their row-fiber, slot-removal and other positive scalar factors
are kept separately.  Before applying AM--GM, each column is normalized
by its own child's actual width.  The resulting density is

`sqrt (aL * U ^ widthL) * sqrt (aR * U ^ widthR) / U ^ widthParent`.

The child measure is the half-sum of the two pushforwards of the original
kernel with this density.  Its mass is exactly the integral of this
density against the original common kernel.  No estimate for a child
moment is a constructor field.  The local source inequality, termwise
column calibration, weighted integrability and actual earlier-child
identification remain explicit analytic inputs.

Earlier children are required only where the density is positive.  Thus
the construction also accommodates terminal nodes with zero child mass.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField HeckeGeneral.Characters MeasureTheory
open scoped BigOperators Classical NNReal ENNReal

universe u v

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}

theorem Node.normalizedEnergy_nonneg (n : Node K ω ψ) (U t : ℝ) (hU : 0 < U) :
    0 ≤ n.normalizedEnergy U t :=
  div_nonneg (n.energy_nonneg U t) (Real.rpow_pos_of_pos hU _).le

theorem Node.energy_eq_scale_normalizedEnergy (n : Node K ω ψ) (U t : ℝ)
    (hU : 0 < U) : n.energy U t = U ^ n.width * n.normalizedEnergy U t := by
  dsimp only [Node.normalizedEnergy]
  field_simp [(Real.rpow_pos_of_pos hU n.width).ne']

theorem sqrt_product_le_half_sum {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt a * Real.sqrt b ≤ (a + b) / 2 := by
  nlinarith [sq_nonneg (Real.sqrt a - Real.sqrt b), Real.sq_sqrt ha, Real.sq_sqrt hb]

theorem Node.sqrt_scaled_energy (n : Node K ω ψ) (U t a : ℝ)
    (hU : 0 < U) (ha : 0 ≤ a) :
    Real.sqrt (a * n.energy U t) =
      Real.sqrt (a * U ^ n.width) * Real.sqrt (n.normalizedEnergy U t) := by
  rw [n.energy_eq_scale_normalizedEnergy U t hU, ← mul_assoc]
  exact Real.sqrt_mul (mul_nonneg ha (Real.rpow_pos_of_pos hU _).le) _

/-- The actual width normalization of the two calibrated Cauchy columns. -/
def normalizedKernelWeight (parent left right : Node K ω ψ) (U a b : ℝ) : ℝ :=
  Real.sqrt (a * U ^ left.width) * Real.sqrt (b * U ^ right.width) / U ^ parent.width

theorem normalizedKernelWeight_nonneg (parent left right : Node K ω ψ)
    (U a b : ℝ) (hU : 0 < U) : 0 ≤ normalizedKernelWeight parent left right U a b := by
  exact div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    (Real.rpow_pos_of_pos hU _).le

/-- AM--GM is applied after both child energies have their own correct
normalization, so differing child widths remain in the positive density. -/
theorem normalized_node_cauchy_le_half (parent left right : Node K ω ψ)
    (U t a b : ℝ) (hU : 0 < U) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a * left.energy U t) * Real.sqrt (b * right.energy U t) /
        U ^ parent.width ≤
      normalizedKernelWeight parent left right U a b *
        (left.normalizedEnergy U t + right.normalizedEnergy U t) / 2 := by
  calc
    _ = normalizedKernelWeight parent left right U a b *
        (Real.sqrt (left.normalizedEnergy U t) *
          Real.sqrt (right.normalizedEnergy U t)) := by
      rw [left.sqrt_scaled_energy U t a hU ha, right.sqrt_scaled_energy U t b hU hb]
      unfold normalizedKernelWeight
      ring
    _ ≤ normalizedKernelWeight parent left right U a b *
        ((left.normalizedEnergy U t + right.normalizedEnergy U t) / 2) :=
      mul_le_mul_of_nonneg_left
        (sqrt_product_le_half_sum (left.normalizedEnergy_nonneg U t hU)
          (right.normalizedEnergy_nonneg U t hU))
        (normalizedKernelWeight_nonneg parent left right U a b hU)
    _ = _ := by ring

/-- Column energies may first be enlarged by genuine row-fiber or removal
estimates.  These are local polynomial estimates, not final moment bounds. -/
theorem normalized_column_cauchy_le_half (parent left right : Node K ω ψ)
    (U t a b c₁ c₂ : ℝ) (hU : 0 < U) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc₁ : c₁ ≤ a * left.energy U t) (hc₂ : c₂ ≤ b * right.energy U t) :
    Real.sqrt c₁ * Real.sqrt c₂ / U ^ parent.width ≤
      normalizedKernelWeight parent left right U a b *
        (left.normalizedEnergy U t + right.normalizedEnergy U t) / 2 := by
  apply (div_le_div_of_nonneg_right
    (mul_le_mul (Real.sqrt_le_sqrt hc₁) (Real.sqrt_le_sqrt hc₂)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    (Real.rpow_pos_of_pos hU _).le).trans
  exact normalized_node_cauchy_le_half parent left right U t a b hU ha hb

section Measures

variable {X : Type u} {Ω : Type v} [MeasurableSpace X] [MeasurableSpace Ω]

/-- Both children use the same positive kernel. -/
def halfPushforward (μ : Measure Ω) (left right : Ω → X) : Measure X :=
  (1 / 2 : ℝ≥0) • (μ.map left + μ.map right)

theorem halfPushforward_finite (μ : Measure Ω) [IsFiniteMeasure μ] (left right : Ω → X) :
    IsFiniteMeasure (halfPushforward μ left right) := by
  unfold halfPushforward
  infer_instance

theorem halfPushforward_mass (μ : Measure Ω) [IsFiniteMeasure μ]
    {left right : Ω → X} (hl : Measurable left) (hr : Measurable right) :
    (halfPushforward μ left right).real Set.univ = μ.real Set.univ := by
  rw [halfPushforward, measureReal_nnreal_smul_apply, measureReal_add_apply,
    map_measureReal_apply hl MeasurableSet.univ, map_measureReal_apply hr MeasurableSet.univ]
  simp only [Set.preimage_univ]
  norm_num <;> ring

theorem halfPushforward_integrable (μ : Measure Ω)
    {left right : Ω → X} {value : X → ℝ}
    (hl : Measurable left) (hr : Measurable right) (hv : Measurable value)
    (hil : Integrable (fun ξ => value (left ξ)) μ)
    (hir : Integrable (fun ξ => value (right ξ)) μ) :
    Integrable value (halfPushforward μ left right) := by
  have hml : Integrable value (μ.map left) :=
    (integrable_map_measure hv.aestronglyMeasurable hl.aemeasurable).2 hil
  have hmr : Integrable value (μ.map right) :=
    (integrable_map_measure hv.aestronglyMeasurable hr.aemeasurable).2 hir
  exact (hml.add_measure hmr).smul_measure_nnreal

theorem integral_halfPushforward (μ : Measure Ω)
    {left right : Ω → X} {value : X → ℝ}
    (hl : Measurable left) (hr : Measurable right) (hv : Measurable value)
    (hil : Integrable (fun ξ => value (left ξ)) μ)
    (hir : Integrable (fun ξ => value (right ξ)) μ) :
    (∫ y, value y ∂halfPushforward μ left right) =
      ((∫ ξ, value (left ξ) ∂μ) + ∫ ξ, value (right ξ) ∂μ) / 2 := by
  have hml : Integrable value (μ.map left) :=
    (integrable_map_measure hv.aestronglyMeasurable hl.aemeasurable).2 hil
  have hmr : Integrable value (μ.map right) :=
    (integrable_map_measure hv.aestronglyMeasurable hr.aemeasurable).2 hir
  rw [halfPushforward, integral_smul_nnreal_measure, integral_add_measure hml hmr,
    integral_map hl.aemeasurable hv.aestronglyMeasurable,
    integral_map hr.aemeasurable hv.aestronglyMeasurable]
  norm_num [NNReal.smul_def] <;> ring

theorem ae_halfPushforward (μ : Measure Ω) {left right : Ω → X} {p : X → Prop}
    (hl : Measurable left) (hr : Measurable right) (hp : MeasurableSet {y | p y})
    (hpl : ∀ᵐ ξ ∂μ, p (left ξ)) (hpr : ∀ᵐ ξ ∂μ, p (right ξ)) :
    ∀ᵐ y ∂halfPushforward μ left right, p y := by
  apply Measure.ae_smul_measure (c := (1 / 2 : ℝ≥0))
  apply ae_iff.2
  rw [Measure.add_apply, ae_iff.1 ((ae_map_iff hl.aemeasurable hp).2 hpl),
    ae_iff.1 ((ae_map_iff hr.aemeasurable hp).2 hpr), add_zero]

/-- The density is the full normalized Cauchy weight, not a selected
finite representative of the continuous frequency integral. -/
def kernelWeightedMeasure (μ : Measure Ω) (weight : Ω → ℝ) : Measure Ω :=
  μ.withDensity fun ξ => ENNReal.ofReal (weight ξ)

theorem kernelWeightedMeasure_finite (μ : Measure Ω) {weight : Ω → ℝ}
    (hw : ∀ ξ, 0 ≤ weight ξ) (hi : Integrable weight μ) :
    IsFiniteMeasure (kernelWeightedMeasure μ weight) := by
  apply isFiniteMeasure_withDensity
  exact ((hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hw)).1
    hi.hasFiniteIntegral).ne

theorem integrable_kernelWeightedMeasure (μ : Measure Ω) {weight value : Ω → ℝ}
    (hm : Measurable weight) (hw : ∀ ξ, 0 ≤ weight ξ)
    (hi : Integrable (fun ξ => weight ξ * value ξ) μ) :
    Integrable value (kernelWeightedMeasure μ weight) := by
  apply (integrable_withDensity_iff_integrable_smul' hm.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).2
  convert hi using 1
  ext ξ
  rw [ENNReal.toReal_ofReal (hw ξ), smul_eq_mul]

theorem integral_kernelWeightedMeasure (μ : Measure Ω) {weight : Ω → ℝ}
    (hm : Measurable weight) (hw : ∀ ξ, 0 ≤ weight ξ) (value : Ω → ℝ) :
    (∫ ξ, value ξ ∂kernelWeightedMeasure μ weight) =
      ∫ ξ, weight ξ * value ξ ∂μ := by
  rw [kernelWeightedMeasure, integral_withDensity_eq_integral_toReal_smul hm.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards with ξ
  rw [ENNReal.toReal_ofReal (hw ξ), smul_eq_mul]

theorem kernelWeightedMeasure_mass (μ : Measure Ω) {weight : Ω → ℝ}
    (hm : Measurable weight) (hw : ∀ ξ, 0 ≤ weight ξ) :
    (kernelWeightedMeasure μ weight).real Set.univ = ∫ ξ, weight ξ ∂μ := by
  simpa only [integral_const, smul_eq_mul, mul_one] using
    integral_kernelWeightedMeasure μ hm hw (fun _ => (1 : ℝ))

theorem ae_kernelWeightedMeasure (μ : Measure Ω) {weight : Ω → ℝ} {p : Ω → Prop}
    (hm : Measurable weight) (hp : ∀ᵐ ξ ∂μ, 0 < weight ξ → p ξ) :
    ∀ᵐ ξ ∂kernelWeightedMeasure μ weight, p ξ := by
  apply (ae_withDensity_iff hm.ennreal_ofReal).2
  filter_upwards [hp] with ξ hξ hweight
  apply hξ
  by_contra h
  exact hweight (ENNReal.ofReal_eq_zero.2 (le_of_not_gt h))

end Measures

/-- A local common-kernel source estimate and actual child calibrations.
The scalar factors may contain row-fiber multiplicities and slot-removal
costs.  Neither a final child moment estimate nor a final parent estimate
is part of this data. -/
structure CommonKernelReduction {σ W : ℝ} (S : PolynomialSystem.{u} K ω ψ σ W)
    (U t : ℝ) (Ω : Type v) [MeasurableSpace S.Label] [MeasurableSpace Ω] where
  kernel : S.Label → Measure Ω
  left : S.Label → Ω → S.Label
  right : S.Label → Ω → S.Label
  left_measurable : ∀ x, Measurable (left x)
  right_measurable : ∀ x, Measurable (right x)
  value_measurable : Measurable (fun x => (S.node x).normalizedEnergy U t)
  earlier_measurable : ∀ x,
    MeasurableSet {y | (S.schedule y).Earlier (S.schedule x)}
  leftFactor : S.Label → Ω → ℝ
  rightFactor : S.Label → Ω → ℝ
  leftFactor_nonneg : ∀ x ξ, 0 ≤ leftFactor x ξ
  rightFactor_nonneg : ∀ x ξ, 0 ≤ rightFactor x ξ
  leftColumn : S.Label → Ω → ℝ
  rightColumn : S.Label → Ω → ℝ
  left_calibration : ∀ x, ∀ᵐ ξ ∂kernel x,
    leftColumn x ξ ≤ leftFactor x ξ * (S.node (left x ξ)).energy U t
  right_calibration : ∀ x, ∀ᵐ ξ ∂kernel x,
    rightColumn x ξ ≤ rightFactor x ξ * (S.node (right x ξ)).energy U t
  remainder : S.Label → ℝ
  source_integrable : ∀ x,
    Integrable (fun ξ => Real.sqrt (leftColumn x ξ) * Real.sqrt (rightColumn x ξ)) (kernel x)
  source : ∀ x, (S.node x).energy U t ≤ remainder x +
    ∫ ξ, Real.sqrt (leftColumn x ξ) * Real.sqrt (rightColumn x ξ) ∂kernel x
  weight_measurable : ∀ x, Measurable fun ξ =>
    normalizedKernelWeight (S.node x) (S.node (left x ξ)) (S.node (right x ξ))
      U (leftFactor x ξ) (rightFactor x ξ)
  weight_integrable : ∀ x, Integrable (fun ξ =>
    normalizedKernelWeight (S.node x) (S.node (left x ξ)) (S.node (right x ξ))
      U (leftFactor x ξ) (rightFactor x ξ)) (kernel x)
  left_integrable : ∀ x, Integrable (fun ξ =>
    normalizedKernelWeight (S.node x) (S.node (left x ξ)) (S.node (right x ξ))
      U (leftFactor x ξ) (rightFactor x ξ) * (S.node (left x ξ)).normalizedEnergy U t)
        (kernel x)
  right_integrable : ∀ x, Integrable (fun ξ =>
    normalizedKernelWeight (S.node x) (S.node (left x ξ)) (S.node (right x ξ))
      U (leftFactor x ξ) (rightFactor x ξ) * (S.node (right x ξ)).normalizedEnergy U t)
        (kernel x)
  left_earlier : ∀ x, ∀ᵐ ξ ∂kernel x,
    0 < normalizedKernelWeight (S.node x) (S.node (left x ξ)) (S.node (right x ξ))
      U (leftFactor x ξ) (rightFactor x ξ) →
        (S.schedule (left x ξ)).Earlier (S.schedule x)
  right_earlier : ∀ x, ∀ᵐ ξ ∂kernel x,
    0 < normalizedKernelWeight (S.node x) (S.node (left x ξ)) (S.node (right x ξ))
      U (leftFactor x ξ) (rightFactor x ξ) →
        (S.schedule (right x ξ)).Earlier (S.schedule x)

namespace CommonKernelReduction

variable {σ W U t : ℝ} {S : PolynomialSystem.{u} K ω ψ σ W}
variable {Ω : Type v} [MeasurableSpace S.Label] [MeasurableSpace Ω]

def weight (d : CommonKernelReduction S U t Ω) (x : S.Label) (ξ : Ω) : ℝ :=
  normalizedKernelWeight (S.node x) (S.node (d.left x ξ)) (S.node (d.right x ξ))
    U (d.leftFactor x ξ) (d.rightFactor x ξ)

theorem weight_nonneg (d : CommonKernelReduction S U t Ω) (hU : 0 < U)
    (x : S.Label) (ξ : Ω) : 0 ≤ d.weight x ξ :=
  normalizedKernelWeight_nonneg _ _ _ U _ _ hU

def weightedKernel (d : CommonKernelReduction S U t Ω) (x : S.Label) : Measure Ω :=
  kernelWeightedMeasure (d.kernel x) (d.weight x)

def childrenMeasure (d : CommonKernelReduction S U t Ω) (x : S.Label) : Measure S.Label :=
  halfPushforward (d.weightedKernel x) (d.left x) (d.right x)

theorem weightedKernel_finite (d : CommonKernelReduction S U t Ω) (hU : 0 < U)
    (x : S.Label) : IsFiniteMeasure (d.weightedKernel x) :=
  kernelWeightedMeasure_finite (d.kernel x) (d.weight_nonneg hU x) (d.weight_integrable x)

theorem childrenMeasure_finite (d : CommonKernelReduction S U t Ω) (hU : 0 < U)
    (x : S.Label) : IsFiniteMeasure (d.childrenMeasure x) := by
  letI := d.weightedKernel_finite hU x
  exact halfPushforward_finite _ _ _

theorem left_integrable_weighted (d : CommonKernelReduction S U t Ω) (hU : 0 < U)
    (x : S.Label) :
    Integrable (fun ξ => (S.node (d.left x ξ)).normalizedEnergy U t) (d.weightedKernel x) :=
  integrable_kernelWeightedMeasure (d.kernel x) (d.weight_measurable x)
    (d.weight_nonneg hU x) (d.left_integrable x)

theorem right_integrable_weighted (d : CommonKernelReduction S U t Ω) (hU : 0 < U)
    (x : S.Label) :
    Integrable (fun ξ => (S.node (d.right x ξ)).normalizedEnergy U t) (d.weightedKernel x) :=
  integrable_kernelWeightedMeasure (d.kernel x) (d.weight_measurable x)
    (d.weight_nonneg hU x) (d.right_integrable x)

theorem childrenMeasure_integrable (d : CommonKernelReduction S U t Ω) (hU : 0 < U)
    (x : S.Label) :
    Integrable (fun y => (S.node y).normalizedEnergy U t) (d.childrenMeasure x) :=
  halfPushforward_integrable _ (d.left_measurable x) (d.right_measurable x)
    d.value_measurable (d.left_integrable_weighted hU x) (d.right_integrable_weighted hU x)

theorem childrenMeasure_earlier (d : CommonKernelReduction S U t Ω) (x : S.Label) :
    ∀ᵐ y ∂d.childrenMeasure x, (S.schedule y).Earlier (S.schedule x) :=
  ae_halfPushforward _ (d.left_measurable x) (d.right_measurable x) (d.earlier_measurable x)
    (ae_kernelWeightedMeasure _ (d.weight_measurable x) (d.left_earlier x))
    (ae_kernelWeightedMeasure _ (d.weight_measurable x) (d.right_earlier x))

/-- The exact mass charged by recursion.  Both branches contribute one
half of the same normalized kernel mass, including all actual widths. -/
theorem childrenMeasure_mass (d : CommonKernelReduction S U t Ω) (hU : 0 < U)
    (x : S.Label) : (d.childrenMeasure x).real Set.univ = ∫ ξ, d.weight x ξ ∂d.kernel x := by
  letI := d.weightedKernel_finite hU x
  rw [childrenMeasure, halfPushforward_mass _ (d.left_measurable x) (d.right_measurable x)]
  exact kernelWeightedMeasure_mass _ (d.weight_measurable x) (d.weight_nonneg hU x)

theorem linearized_estimate (d : CommonKernelReduction S U t Ω) (hU : 0 < U)
    (x : S.Label) : (S.node x).normalizedEnergy U t ≤
      d.remainder x / U ^ (S.node x).width +
        ∫ y, (S.node y).normalizedEnergy U t ∂d.childrenMeasure x := by
  have hpoint : ∀ᵐ ξ ∂d.kernel x,
      Real.sqrt (d.leftColumn x ξ) * Real.sqrt (d.rightColumn x ξ) /
          U ^ (S.node x).width ≤
        (d.weight x ξ * (S.node (d.left x ξ)).normalizedEnergy U t +
          d.weight x ξ * (S.node (d.right x ξ)).normalizedEnergy U t) / 2 := by
    filter_upwards [d.left_calibration x, d.right_calibration x] with ξ hl hr
    simpa only [weight, mul_add] using normalized_column_cauchy_le_half
      (S.node x) (S.node (d.left x ξ)) (S.node (d.right x ξ))
      U t (d.leftFactor x ξ) (d.rightFactor x ξ)
      (d.leftColumn x ξ) (d.rightColumn x ξ) hU
      (d.leftFactor_nonneg x ξ) (d.rightFactor_nonneg x ξ) hl hr
  have hint := integral_mono_ae
    ((d.source_integrable x).div_const (U ^ (S.node x).width))
    (((d.left_integrable x).add (d.right_integrable x)).div_const 2) hpoint
  rw [integral_div, integral_div] at hint
  simp only [Pi.add_apply] at hint
  rw [integral_add (d.left_integrable x) (d.right_integrable x)] at hint
  have hsource := div_le_div_of_nonneg_right (d.source x)
    (Real.rpow_pos_of_pos hU (S.node x).width).le
  rw [add_div] at hsource
  apply hsource.trans
  apply add_le_add_left
  convert hint using 1
  rw [childrenMeasure, integral_halfPushforward _ (d.left_measurable x)
    (d.right_measurable x) d.value_measurable
    (d.left_integrable_weighted hU x) (d.right_integrable_weighted hU x)]
  rw [weightedKernel, integral_kernelWeightedMeasure _ (d.weight_measurable x)
    (d.weight_nonneg hU x), integral_kernelWeightedMeasure _ (d.weight_measurable x)
    (d.weight_nonneg hU x)]

/-- Construct the continuous recursion on the unchanged, actual polynomial
system.  The raw source remainder is normalized by the actual parent width. -/
def toIntegralStep (d : CommonKernelReduction S U t Ω) (hU : 0 < U) :
    IntegralStep (fun x => (S.node x).normalizedEnergy U t) S.schedule where
  childrenMeasure := d.childrenMeasure
  finite := d.childrenMeasure_finite hU
  remainder x := d.remainder x / U ^ (S.node x).width
  integrable := d.childrenMeasure_integrable hU
  earlier := d.childrenMeasure_earlier
  estimate := d.linearized_estimate hU

theorem toIntegralStep_mass (d : CommonKernelReduction S U t Ω) (hU : 0 < U)
    (x : S.Label) : (d.toIntegralStep hU).mass x = ∫ ξ, d.weight x ξ ∂d.kernel x :=
  d.childrenMeasure_mass hU x

/-- Assemble the actual integral reduction with the raw terminal ledgers.
The analytic mass input concerns the explicit density against the original
kernel.  The terminal input remains a classified finite coefficient sum;
`RawParentReduction.closeTerminals` proves its resulting exponent bound. -/
def toRawParentReduction (d : CommonKernelReduction S U t Ω) (hU : 0 < U)
    (T C H β δ floor padding boundary : ℝ)
    (hfloor : 0 ≤ floor) (hpadding : 0 ≤ padding) (hboundary : 0 ≤ boundary)
    (hbudget : terminalBudget floor padding σ boundary ≤ β)
    (components : ∀ x, TerminalComponents.{u}
      (d.remainder x / U ^ (S.node x).width) U T C H floor padding σ boundary)
    (hmass : ∀ x, (∫ ξ, d.weight x ξ ∂d.kernel x) ≤ C * (1 + T) ^ H * U ^ δ) :
    RawParentReduction K S U T t C H β δ where
  reduction := .integral inferInstance (d.toIntegralStep hU)
  floor := floor
  padding := padding
  boundary := boundary
  floor_nonneg := hfloor
  padding_nonneg := hpadding
  boundary_nonneg := hboundary
  terminal_budget := hbudget
  components := components
  mass x := by
    change (d.toIntegralStep hU).mass x ≤ C * (1 + T) ^ H * U ^ δ
    rw [d.toIntegralStep_mass hU x]
    exact hmass x

end CommonKernelReduction

end HeckeSkeleton.Moments.EngineInduction
