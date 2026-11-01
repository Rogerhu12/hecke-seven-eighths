module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp
public import HeckeSkeleton.Moments.MOM_UNIFORM_AMPLIFY.FinitePropagation

/-!
# Propagation through a common Fourier integral

The finite Hilbert-space Minkowski inequality transports a common row
majorant through an integrable kernel over any measure space, including
finite-dimensional joint Fourier parameters.  Its remaining L¹ mass
contributes exactly its own arithmetic, logarithmic and height exponents,
without an additional row count.  The actual common kernel, its
integrability and its mass estimate must be supplied by the analytic edge.

This generalizes the proof of `RMMaskedDyadic.finite_integral_l2` and
`RMMaskedDyadic.finite_integral_l2_bound` from the real line to an arbitrary
measure, using the same finite Euclidean-space integral argument directly.
-/

@[expose] public section
noncomputable section
namespace HeckeSkeleton.Moments.UniformAmplify

open MeasureTheory
open scoped BigOperators

/-- The common-measure version of the finite Hilbert-space integral bound.
The measure need not be a probability measure or have finite total mass. -/
theorem shared_measure_integral_envelope {α : Type*} {ι : Type*}
    [MeasurableSpace α] [Fintype ι] (μ : Measure α)
    (g : α → ι → ℂ) (hg : ∀ i, Integrable (fun x : α => g x i) μ)
    (W : α → ℂ) (hW : Integrable W μ)
    {C p L H C' p' L' H' Z T : ℝ}
    (hC : 0 ≤ C) (hZ : 1 ≤ Z) (hT : 0 ≤ T)
    (hpoint : ∀ x : α, Real.sqrt (∑ i, ‖g x i‖ ^ 2) ≤
      ‖W x‖ * growthEnvelope C p L H Z T)
    (hmass : (∫ x : α, ‖W x‖ ∂μ) ≤ growthEnvelope C' p' L' H' Z T) :
    Real.sqrt (∑ i, ‖∫ x : α, g x i ∂μ‖ ^ 2) ≤
      growthEnvelope (C * C') (p + p') (L + L') (H + H') Z T := by
  let G : α → EuclideanSpace ℂ ι := fun x => WithLp.toLp 2 (g x)
  have hG : Integrable G μ := integrable_piLp_iff.mpr hg
  have he : (∫ x, G x ∂μ) = WithLp.toLp 2 (fun i => ∫ x, g x i ∂μ) := by
    ext i
    exact eval_integral_piLp hg i
  have hnorm : Real.sqrt (∑ i, ‖∫ x : α, g x i ∂μ‖ ^ 2) ≤
      ∫ x : α, Real.sqrt (∑ i, ‖g x i‖ ^ 2) ∂μ := by
    have hb := norm_integral_le_integral_norm (μ := μ) G
    rw [he, EuclideanSpace.norm_eq] at hb
    simpa only [EuclideanSpace.norm_eq, G, PiLp.toLp_apply] using hb
  have hroot : Integrable (fun x : α => Real.sqrt (∑ i, ‖g x i‖ ^ 2)) μ :=
    hG.norm.congr (Filter.Eventually.of_forall fun x => EuclideanSpace.norm_eq _)
  calc
    _ ≤ ∫ x : α, Real.sqrt (∑ i, ‖g x i‖ ^ 2) ∂μ := hnorm
    _ ≤ (∫ x : α, ‖W x‖ ∂μ) * growthEnvelope C p L H Z T := by
      rw [← integral_mul_const]
      exact integral_mono hroot (hW.norm.mul_const _) hpoint
    _ ≤ growthEnvelope C' p' L' H' Z T * growthEnvelope C p L H Z T :=
      mul_le_mul_of_nonneg_right hmass (growthEnvelope_nonneg hC hZ hT)
    _ = growthEnvelope C p L H Z T * growthEnvelope C' p' L' H' Z T :=
      mul_comm _ _
    _ = _ := growthEnvelope_mul hZ hT

/-- The real-line Fourier case is the Lebesgue-measure specialization. -/
theorem shared_fourier_integral_envelope {ι : Type*} [Fintype ι]
    (g : ℝ → ι → ℂ) (hg : ∀ i, Integrable (fun t : ℝ => g t i))
    (W : ℝ → ℂ) (hW : Integrable W)
    {C p L H C' p' L' H' Z T : ℝ}
    (hC : 0 ≤ C) (hZ : 1 ≤ Z) (hT : 0 ≤ T)
    (hpoint : ∀ t : ℝ, Real.sqrt (∑ i, ‖g t i‖ ^ 2) ≤
      ‖W t‖ * growthEnvelope C p L H Z T)
    (hmass : (∫ t : ℝ, ‖W t‖) ≤ growthEnvelope C' p' L' H' Z T) :
    Real.sqrt (∑ i, ‖∫ t : ℝ, g t i‖ ^ 2) ≤
      growthEnvelope (C * C') (p + p') (L + L') (H + H') Z T :=
  shared_measure_integral_envelope volume g hg W hW hC hZ hT hpoint hmass

end HeckeSkeleton.Moments.UniformAmplify
