import HeckeGeneral.Analysis.TraceProductPoisson
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! UNCOMPILED / native 0. Genuine Fourier dilation by a positive real
scalar, specialized to the actual two-column trace space. The Jacobian
N^2 is derived from the real dimension 2[K:Q]; it is not an input.
The weighted PSF retains the actual covolume and unnormalized mask.
All Fourier transforms in this module are the standard negative-sign
inner-product Fourier transform. Mixed-Haar factors are not changed. -/

noncomputable section
namespace HeckeGeneral.Analysis.ActualTraceProductFourierDilationDraft
open MeasureTheory NumberField
open HeckeGeneral.Arithmetic
open scoped Classical FourierTransform Real nonZeroDivisors

section Generic
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A direct additive-Haar change of variables. No integrability or
Fourier-transform identity is assumed, even for arbitrary totalized f. -/
theorem fourier_inverse_dilation (f : E → ℂ) (t : ℝ) (ht : 0 < t) (m : E) :
    𝓕 (fun x => f (t⁻¹ • x)) m =
      ((t ^ Module.finrank ℝ E : ℝ) : ℂ) * 𝓕 f (t • m) := by
  let g : E → ℂ := fun y => Real.fourierChar (-inner ℝ y (t • m)) • f y
  have hinner (x : E) : inner ℝ (t⁻¹ • x) (t • m) = inner ℝ x m := by
    rw [real_inner_smul_left, real_inner_smul_right]
    rw [← mul_assoc, inv_mul_cancel₀ ht.ne', one_mul]
  calc
    _ = ∫ x : E, g (t⁻¹ • x) := by
      rw [Real.fourier_eq]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by simp only [g, hinner]
    _ = t ^ Module.finrank ℝ E • ∫ y : E, g y :=
      Measure.integral_comp_inv_smul_of_nonneg volume g ht.le
    _ = _ := by
      rewrite [Complex.real_smul]
      rfl

/-- The actual Schwartz test obtained by inverse scalar dilation. -/
def inverseDilationSchwartz (t : ℝ) (ht : 0 < t) (F : SchwartzMap E ℂ) :
    SchwartzMap E ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := E)
      (Units.mk0 t⁻¹ (inv_ne_zero ht.ne'))) F

@[simp] theorem inverseDilationSchwartz_apply (t : ℝ) (ht : 0 < t)
    (F : SchwartzMap E ℂ) (x : E) :
    inverseDilationSchwartz t ht F x = F (t⁻¹ • x) := rfl

theorem fourier_inverseDilationSchwartz (t : ℝ) (ht : 0 < t)
    (F : SchwartzMap E ℂ) (m : E) :
    𝓕 (inverseDilationSchwartz t ht F : E → ℂ) m =
      ((t ^ Module.finrank ℝ E : ℝ) : ℂ) * 𝓕 (F : E → ℂ) (t • m) :=
  fourier_inverse_dilation F t ht m

end Generic

variable (K : Type) [Field K] [NumberField K]
local notation "W" => traceProductSpace K

/-- The literal degree-root scale from the manuscript norm parameter. -/
def traceNormScale (N : ℝ) : ℝ := N ^ (Module.finrank ℚ K : ℝ)⁻¹

theorem traceNormScale_pos (N : ℝ) (hN : 0 < N) : 0 < traceNormScale K N :=
  Real.rpow_pos_of_pos hN _

/-- The two genuine columns produce N^2, without a determinant premise. -/
theorem traceNormScale_jacobian (N : ℝ) (hN : 0 < N) :
    traceNormScale K N ^ Module.finrank ℝ W = N ^ 2 := by
  rw [finrank_traceProductSpace, Nat.mul_comm 2 (Module.finrank ℚ K), pow_mul]
  rw [traceNormScale, Real.rpow_inv_natCast_pow hN.le
    (Module.finrank_pos (R := ℚ) (M := K)).ne']

/-- The actual two-column test F_N(x)=F(N^(-1/d)x). -/
def traceProductScaledSchwartz (N : ℝ) (hN : 0 < N) (F : SchwartzMap W ℂ) :
    SchwartzMap W ℂ :=
  inverseDilationSchwartz (traceNormScale K N) (traceNormScale_pos K N hN) F

@[simp] theorem traceProductScaledSchwartz_apply (N : ℝ) (hN : 0 < N)
    (F : SchwartzMap W ℂ) (x : W) :
    traceProductScaledSchwartz K N hN F x = F ((traceNormScale K N)⁻¹ • x) := rfl

/-- Exact standard Fourier dilation on the actual product trace space. -/
theorem fourier_traceProductScaledSchwartz (N : ℝ) (hN : 0 < N)
    (F : SchwartzMap W ℂ) (m : W) :
    𝓕 (traceProductScaledSchwartz K N hN F : W → ℂ) m =
      (N : ℂ) ^ 2 * 𝓕 (F : W → ℂ) (traceNormScale K N • m) := by
  have h := fourier_inverseDilationSchwartz (traceNormScale K N)
    (traceNormScale_pos K N hN) F m
  rw [traceNormScale_jacobian K N hN] at h
  simpa only [traceProductScaledSchwartz, Complex.ofReal_pow] using h

/-- Actual scaled weighted PSF. The quotient, covolume, polar, positive
finite frequency character and all coordinate axes are retained. No
summability, Fourier-dilation, or volume formula is an input. -/
theorem weighted_lattice_poisson_trace_scaled
    (L J : Submodule ℤ W)
    [DiscreteTopology L] [IsZLattice ℝ L] [DiscreteTopology J] [IsZLattice ℝ J]
    [Fintype (LatticeQuotient L J)] (hJL : J ≤ L)
    (w : LatticeQuotient L J → ℂ) (F : SchwartzMap W ℂ)
    (N : ℝ) (hN : 0 < N) (v : W) :
    (∑' l : L, w (latticeQuotientMap L J l) *
      F ((traceNormScale K N)⁻¹ • (v + l))) =
      (1 / ZLattice.covolume J : ℂ) * (N : ℂ) ^ 2 *
        ∑' m : dualLattice J,
          (𝓕 (F : W → ℂ) (traceNormScale K N • (m : W))) *
            latticePhase v m * latticeMaskCoefficient L J w m := by
  have h := weighted_lattice_poisson L J hJL w (traceProductScaledSchwartz K N hN F) v
  simp only [traceProductScaledSchwartz_apply,
    fourier_traceProductScaledSchwartz K N hN F] at h
  have hsum :
      (∑' m : dualLattice J,
        ((N : ℂ) ^ 2 * 𝓕 (F : W → ℂ) (traceNormScale K N • (m : W))) *
          latticePhase v m * latticeMaskCoefficient L J w m) =
      (N : ℂ) ^ 2 * ∑' m : dualLattice J,
        𝓕 (F : W → ℂ) (traceNormScale K N • (m : W)) *
          latticePhase v m * latticeMaskCoefficient L J w m := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro m
    ring
  rw [hsum] at h
  simpa only [mul_assoc] using h

end HeckeGeneral.Analysis.ActualTraceProductFourierDilationDraft
