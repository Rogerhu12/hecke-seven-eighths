import HeckeGeneral.Analysis.TraceJointSchwartzFourierBounds
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ChildAssembly
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# One Fourier measure for a complete two-column kernel

Fourier inversion of the actual Schwartz kernel gives the separation
identity below.  Its convergence is proved from Schwartz integrability;
neither a separation formula nor a parent moment estimate is an input.
All column coefficients, including centered differences, remain inside
their finite Fourier polynomials.  Cauchy uses the same row weight and
the same Fourier variable on both sides.

The last theorem transports the repository's ordinary-product kernel to
its genuine `WithLp 2` space.  The measure is its canonical Euclidean
volume.  The mixed-measure Jacobian and trace conjugation remain those
proved in `TraceJointSchwartzFourierBounds`; no self-dual mixed-measure
normalization is asserted here.
-/

noncomputable section
open scoped Classical BigOperators FourierTransform SchwartzMap
open MeasureTheory

namespace HeckeSkeleton.Moments.EngineStep

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def jointPhase (ξ z : V) : ℂ := (Real.fourierChar (inner ℝ ξ z) : ℂ)

@[simp] theorem norm_jointPhase (ξ z : V) : ‖jointPhase ξ z‖ = 1 :=
  Circle.norm_coe _

theorem jointPhase_add (ξ x y : V) :
    jointPhase ξ (x + y) = jointPhase ξ x * jointPhase ξ y := by
  simp only [jointPhase, inner_add_right, AddChar.map_add_eq_mul, Circle.coe_mul]

theorem continuous_jointPhase (z : V) : Continuous (fun ξ : V => jointPhase ξ z) :=
  continuous_subtype_val.comp
    (Real.continuous_fourierChar.comp (continuous_id.inner continuous_const))

/-- A complete column polynomial; its coefficient may already be centered. -/
def jointFourierColumn {ι : Type*} (columns : Finset ι) (c : ι → ℂ)
    (x : ι → V) (ξ : V) : ℂ :=
  ∑ a ∈ columns, c a * jointPhase ξ (x a)

theorem continuous_jointFourierColumn {ι : Type*} (columns : Finset ι)
    (c : ι → ℂ) (x : ι → V) : Continuous (jointFourierColumn columns c x) := by
  apply continuous_finsetSum
  intro a ha
  exact continuous_const.mul (continuous_jointPhase (x a))

theorem norm_jointFourierColumn_le {ι : Type*} (columns : Finset ι)
    (c : ι → ℂ) (x : ι → V) (ξ : V) :
    ‖jointFourierColumn columns c x ξ‖ ≤ ∑ a ∈ columns, ‖c a‖ := by
  apply (norm_sum_le _ _).trans
  simp only [norm_mul, norm_jointPhase, mul_one, le_refl]

def jointColumnEnergy {H ι : Type*} (rows : Finset H) (columns : Finset ι)
    (q : H → ℂ) (c : H → ι → ℂ) (x : H → ι → V) (ξ : V) : ℝ :=
  ∑ h ∈ rows, ‖q h‖ * ‖jointFourierColumn columns (c h) (x h) ξ‖ ^ 2

def jointColumnMass {H ι : Type*} (rows : Finset H) (columns : Finset ι)
    (q : H → ℂ) (c : H → ι → ℂ) : ℝ :=
  ∑ h ∈ rows, ‖q h‖ * (∑ a ∈ columns, ‖c h a‖) ^ 2

theorem jointColumnEnergy_nonneg {H ι : Type*} (rows : Finset H) (columns : Finset ι)
    (q : H → ℂ) (c : H → ι → ℂ) (x : H → ι → V) (ξ : V) :
    0 ≤ jointColumnEnergy rows columns q c x ξ :=
  Finset.sum_nonneg (fun _ _ => mul_nonneg (norm_nonneg _) (sq_nonneg _))

theorem continuous_jointColumnEnergy {H ι : Type*}
    (rows : Finset H) (columns : Finset ι) (q : H → ℂ)
    (c : H → ι → ℂ) (x : H → ι → V) :
    Continuous (jointColumnEnergy rows columns q c x) := by
  apply continuous_finsetSum
  intro h hh
  exact continuous_const.mul ((continuous_jointFourierColumn columns (c h) (x h)).norm.pow 2)

theorem jointColumnEnergy_le_mass {H ι : Type*}
    (rows : Finset H) (columns : Finset ι) (q : H → ℂ)
    (c : H → ι → ℂ) (x : H → ι → V) (ξ : V) :
    jointColumnEnergy rows columns q c x ξ ≤ jointColumnMass rows columns q c := by
  apply Finset.sum_le_sum
  intro h hh
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) (norm_jointFourierColumn_le columns (c h) (x h) ξ) 2)
    (norm_nonneg _)

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- Each actual inverse Fourier mode is integrable, without a separate premise. -/
theorem joint_kernel_mode_integrable (F : 𝓢(V, ℂ)) (z : V) :
    Integrable (fun ξ : V => (𝓕 F) ξ * jointPhase ξ z) := by
  have h := (Real.fourierIntegral_convergent_iff
    (f := (𝓕 F : 𝓢(V, ℂ))) (-z)).mpr (𝓕 F).integrable
  simpa only [inner_neg_right, neg_neg, Circle.smul_def, smul_eq_mul,
    jointPhase, mul_comm] using h

/-- Fourier inversion of the kernel, with the positive inverse-transform phase. -/
theorem joint_kernel_inversion (F : 𝓢(V, ℂ)) (z : V) :
    F z = ∫ ξ : V, (𝓕 F) ξ * jointPhase ξ z := by
  have h := congrFun
    (F.continuous.fourierInv_fourier_eq F.integrable (𝓕 F).integrable) z
  rw [Real.fourierInv_eq] at h
  simpa only [Circle.smul_def, smul_eq_mul, jointPhase, mul_comm] using h.symm

/-- The literal finite bilinear kernel form, including every row and column. -/
def jointKernelPairing {H ι κ : Type*} (F : 𝓢(V, ℂ))
    (rows : Finset H) (leftColumns : Finset ι) (rightColumns : Finset κ)
    (q : H → ℂ) (c : H → ι → ℂ) (d : H → κ → ℂ)
    (x : H → ι → V) (y : H → κ → V) : ℂ :=
  ∑ h ∈ rows, q h * ∑ a ∈ leftColumns, ∑ b ∈ rightColumns,
    c h a * star (d h b) * F (x h a + y h b)

/-- Exact separation by the Fourier transform of one common Schwartz kernel. -/
theorem joint_kernel_finite_separation {H ι κ : Type*} (F : 𝓢(V, ℂ))
    (rows : Finset H) (leftColumns : Finset ι) (rightColumns : Finset κ)
    (q : H → ℂ) (c : H → ι → ℂ) (d : H → κ → ℂ)
    (x : H → ι → V) (y : H → κ → V) :
    jointKernelPairing F rows leftColumns rightColumns q c d x y =
      ∫ ξ : V, (𝓕 F) ξ * ∑ h ∈ rows, q h *
        jointFourierColumn leftColumns (c h) (x h) ξ *
        jointFourierColumn rightColumns (fun b => star (d h b)) (y h) ξ := by
  have hi (h : H) (a : ι) (b : κ) : Integrable (fun ξ : V =>
      (q h * c h a * star (d h b)) * ((𝓕 F) ξ * jointPhase ξ (x h a + y h b))) :=
    (joint_kernel_mode_integrable F _).const_mul _
  symm
  calc
    _ = ∫ ξ : V, ∑ h ∈ rows, ∑ a ∈ leftColumns, ∑ b ∈ rightColumns,
        (q h * c h a * star (d h b)) * ((𝓕 F) ξ * jointPhase ξ (x h a + y h b)) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ξ => by
        simp_rw [jointFourierColumn, mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro h hh
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro b hb
        rw [jointPhase_add]
        ring
    _ = ∑ h ∈ rows, ∑ a ∈ leftColumns, ∑ b ∈ rightColumns,
        (q h * c h a * star (d h b)) * F (x h a + y h b) := by
      rw [integral_finsetSum rows (fun h hh => integrable_finsetSum leftColumns
        (fun a ha => integrable_finsetSum rightColumns (fun b hb => hi h a b)))]
      apply Finset.sum_congr rfl
      intro h hh
      rw [integral_finsetSum leftColumns
        (fun a ha => integrable_finsetSum rightColumns (fun b hb => hi h a b))]
      apply Finset.sum_congr rfl
      intro a ha
      rw [integral_finsetSum rightColumns (fun b hb => hi h a b)]
      apply Finset.sum_congr rfl
      intro b hb
      rw [integral_const_mul, ← joint_kernel_inversion]
    _ = _ := by
      unfold jointKernelPairing
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h hh
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      ring

/-- The common Fourier majorant is genuinely integrable. -/
theorem joint_kernel_energy_integrable {H ι κ : Type*} (F : 𝓢(V, ℂ))
    (rows : Finset H) (leftColumns : Finset ι) (rightColumns : Finset κ)
    (q : H → ℂ) (c : H → ι → ℂ) (d : H → κ → ℂ)
    (x : H → ι → V) (y : H → κ → V) :
    Integrable (fun ξ : V => ‖(𝓕 F) ξ‖ *
      (Real.sqrt (jointColumnEnergy rows leftColumns q c x ξ) *
        Real.sqrt (jointColumnEnergy rows rightColumns q d y ξ))) := by
  have hc := (Real.continuous_sqrt.comp
    (continuous_jointColumnEnergy rows leftColumns q c x)).mul
    (Real.continuous_sqrt.comp (continuous_jointColumnEnergy rows rightColumns q d y))
  apply (𝓕 F).integrable.norm.mul_bdd hc.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun ξ => by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
    exact mul_le_mul
      (Real.sqrt_le_sqrt (jointColumnEnergy_le_mass rows leftColumns q c x ξ))
      (Real.sqrt_le_sqrt (jointColumnEnergy_le_mass rows rightColumns q d y ξ))
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

/-- Cauchy is taken only after exact Fourier separation, with one common
frequency measure and one common nonnegative row measure `‖q h‖`. -/
theorem joint_kernel_paired_cauchy {H ι κ : Type*} (F : 𝓢(V, ℂ))
    (rows : Finset H) (leftColumns : Finset ι) (rightColumns : Finset κ)
    (q : H → ℂ) (c : H → ι → ℂ) (d : H → κ → ℂ)
    (x : H → ι → V) (y : H → κ → V) :
    ‖jointKernelPairing F rows leftColumns rightColumns q c d x y‖ ≤
      ∫ ξ : V, ‖(𝓕 F) ξ‖ *
        (Real.sqrt (jointColumnEnergy rows leftColumns q c x ξ) *
          Real.sqrt (jointColumnEnergy rows rightColumns q (fun h b => star (d h b)) y ξ)) := by
  rw [joint_kernel_finite_separation]
  apply norm_integral_le_of_norm_le
    (joint_kernel_energy_integrable F rows leftColumns rightColumns q c
      (fun h b => star (d h b)) x y)
  exact Filter.Eventually.of_forall fun ξ => by
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    simpa only [star_star, norm_star, jointColumnEnergy] using
      complex_weighted_cauchy rows q
        (fun h => jointFourierColumn leftColumns (c h) (x h) ξ)
        (fun h => star (jointFourierColumn rightColumns
          (fun b => star (d h b)) (y h) ξ))

section TraceJoint

open NumberField NumberField.InfinitePlace HeckeGeneral.Analysis

variable (K : Type) [Field K] [NumberField K]
local notation "VK" => mixedEmbedding.euclidean.mixedSpace K
local notation "WK" => TraceJointEuclideanSpace K

/-- The actual product kernel is transported by the existing isomorphism. -/
def euclideanJointKernel (F : 𝓢(VK × VK, ℂ)) : 𝓢(WK, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (traceJointToProduct K) F

theorem euclideanJointKernel_pair (F : 𝓢(VK × VK, ℂ)) (x y : VK) :
    euclideanJointKernel K F (WithLp.toLp 2 (x, 0) + WithLp.toLp 2 (0, y)) = F (x, y) := by
  change F ((x, (0 : VK)) + (0, y)) = F (x, y)
  simp only [Prod.mk_add_mk, add_zero, zero_add]

/-- The finite common-kernel form for the genuine two-column Schwartz space.
Applying `joint_kernel_paired_cauchy` to this same transport supplies its
paired energy bound; no Fourier kernel or separation equality is assumed. -/
theorem trace_joint_kernel_finite_separation {H ι κ : Type*}
    (F : 𝓢(VK × VK, ℂ))
    (rows : Finset H) (leftColumns : Finset ι) (rightColumns : Finset κ)
    (q : H → ℂ) (c : H → ι → ℂ) (d : H → κ → ℂ)
    (x : H → ι → VK) (y : H → κ → VK) :
    (∑ h ∈ rows, q h * ∑ a ∈ leftColumns, ∑ b ∈ rightColumns,
      c h a * star (d h b) * F (x h a, y h b)) =
      ∫ ξ : WK, (𝓕 (euclideanJointKernel K F)) ξ * ∑ h ∈ rows, q h *
        jointFourierColumn leftColumns (c h) (fun a => WithLp.toLp 2 (x h a, 0)) ξ *
        jointFourierColumn rightColumns (fun b => star (d h b))
          (fun b => WithLp.toLp 2 (0, y h b)) ξ := by
  simpa only [jointKernelPairing, euclideanJointKernel_pair] using
    joint_kernel_finite_separation (euclideanJointKernel K F) rows leftColumns rightColumns
      q c d (fun h a => WithLp.toLp 2 (x h a, 0))
        (fun h b => WithLp.toLp 2 (0, y h b))

/-- The paired estimate for that same actual product kernel and the same
Euclidean Fourier measure. -/
theorem trace_joint_kernel_paired_cauchy {H ι κ : Type*}
    (F : 𝓢(VK × VK, ℂ))
    (rows : Finset H) (leftColumns : Finset ι) (rightColumns : Finset κ)
    (q : H → ℂ) (c : H → ι → ℂ) (d : H → κ → ℂ)
    (x : H → ι → VK) (y : H → κ → VK) :
    ‖∑ h ∈ rows, q h * ∑ a ∈ leftColumns, ∑ b ∈ rightColumns,
      c h a * star (d h b) * F (x h a, y h b)‖ ≤
      ∫ ξ : WK, ‖(𝓕 (euclideanJointKernel K F)) ξ‖ *
        (Real.sqrt (jointColumnEnergy rows leftColumns q c
          (fun h a => WithLp.toLp 2 (x h a, 0)) ξ) *
        Real.sqrt (jointColumnEnergy rows rightColumns q (fun h b => star (d h b))
          (fun h b => WithLp.toLp 2 (0, y h b)) ξ)) := by
  simpa only [jointKernelPairing, euclideanJointKernel_pair] using
    joint_kernel_paired_cauchy (euclideanJointKernel K F) rows leftColumns rightColumns
      q c d (fun h a => WithLp.toLp 2 (x h a, 0))
        (fun h b => WithLp.toLp 2 (0, y h b))

end TraceJoint

end HeckeSkeleton.Moments.EngineStep

end

#print axioms HeckeSkeleton.Moments.EngineStep.joint_kernel_finite_separation
#print axioms HeckeSkeleton.Moments.EngineStep.joint_kernel_paired_cauchy
#print axioms HeckeSkeleton.Moments.EngineStep.trace_joint_kernel_finite_separation
#print axioms HeckeSkeleton.Moments.EngineStep.trace_joint_kernel_paired_cauchy
