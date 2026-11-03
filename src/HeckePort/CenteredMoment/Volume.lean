import HeckePort.CenteredMoment.Mask
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-!
# The volume input of the masked ideal sums

`IdealVolumeInput K Ψ` is the one analytic input of `MaskedVolume`,
`Cancellation` and `Counting`: a smoothed ideal sum weighted by `Ψ` is a linear
main term plus an error that is uniform in the length `X`.

Over `ℤ[ω]` openai/math proves it for the primary-generator characters as
`CenteredMomentPrimary.primary_ideal_volume_error_all`, from the radial lattice
Poisson summation of `Moments/Lattice.lean` (with `pv_lattice_bound`) and the
primary-generator dictionary of `Moments/Primary.lean`. Over a general field the
main term is the zero frequency of the weighted orbital Poisson summation
(`HeckeGeneral.Analysis.sIntegerPeriodicOrbitalPoisson`), and the uniform error
needs a bound for the dual orbital series at all radii. That bound belongs to the
open Gram obligations of the skeleton, so it stays an explicit input here.
-/

noncomputable section

namespace HeckePort.CenteredMomentVolume

open scoped NumberField SchwartzMap

variable (K : Type*) [Field K] [NumberField K]

/-- A main term `X * density W` and a uniform error `error W` for the smoothed
sums `∑ Ψ(I) W(N I / X)`. -/
structure IdealVolumeInput (Ψ : Ideal (𝓞 K) → ℂ) where
  density : 𝓢(ℝ, ℂ) → ℂ
  error : 𝓢(ℝ, ℂ) → ℝ
  error_nonneg : ∀ W, 0 ≤ error W
  volume : ∀ (W : 𝓢(ℝ, ℂ)) (X : ℝ), 0 < X →
    ‖(∑' I : Ideal (𝓞 K), Ψ I * W ((Ideal.absNorm I : ℝ) / X)) - (X : ℂ) * density W‖ ≤
      error W

end HeckePort.CenteredMomentVolume
