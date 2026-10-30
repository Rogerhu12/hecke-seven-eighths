import HeckeGeneral.Analysis.IdealThetaPoisson
import HeckeGeneral.Arithmetic.TraceLatticeCovolume

/-!
Explicit arithmetic normalization of Poisson summation on the trace lattice.
The norm is the actual fractional-ideal absolute norm and the frequencies are
the conjugate embedding of the actual inverse-different trace-dual ideal.
-/

open NumberField Classical
open scoped FourierTransform Real nonZeroDivisors

noncomputable section

namespace HeckeGeneral.Analysis

open HeckeGeneral.Arithmetic

variable (K : Type*) [Field K] [NumberField K]

/-- Ideal Poisson summation with its discriminant and ideal-norm prefactor. -/
theorem idealTracePoisson_normalized
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (f : SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ)
    (v : mixedEmbedding.euclidean.mixedSpace K) :
    ∑' l : traceIdealLattice K I, f (v + l) =
      (1 / (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) *
        Real.sqrt |discr K| : ℝ) : ℂ) *
      ∑' m : conjugateTraceIdealLattice K (traceDualIdealUnit K I),
        (𝓕 ⇑f m) * Complex.exp (2 * Real.pi * Complex.I * inner ℝ v m) := by
  simpa only [covolume_traceIdealLattice] using idealTracePoisson K I f v

/-- At the origin the phase disappears, leaving the actual dual-ideal sum. -/
theorem idealTracePoisson_zero_normalized
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (f : SchwartzMap (mixedEmbedding.euclidean.mixedSpace K) ℂ) :
    ∑' l : traceIdealLattice K I, f l =
      (1 / (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) *
        Real.sqrt |discr K| : ℝ) : ℂ) *
      ∑' m : conjugateTraceIdealLattice K (traceDualIdealUnit K I), 𝓕 ⇑f m := by
  simpa using idealTracePoisson_normalized K I f 0

end HeckeGeneral.Analysis
