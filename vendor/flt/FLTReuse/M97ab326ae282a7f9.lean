import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.InnerProductSpace.PiL2
import FLTReuse.M1868db956c866c8d
import FLTReuse.M0c5733ba71e6969b

open scoped FourierTransform InnerProductSpace SchwartzMap
theorem SchwartzMap.tsum_eq_tsum_fourier_euclideanSpace
    {ι : Type*} [Fintype ι] (f : 𝓢(EuclideanSpace ℝ ι, ℂ)) (x : EuclideanSpace ℝ ι) :
    ∑' n : ι → ℤ, f (x + WithLp.toLp 2 (fun i ↦ (n i : ℝ))) =
      ∑' n : ι → ℤ, 𝓕 f (WithLp.toLp 2 (fun i ↦ (n i : ℝ))) *
        (𝐞 ⟪(WithLp.toLp 2 (fun i ↦ (n i : ℝ)) : EuclideanSpace ℝ ι), x⟫_ℝ : ℂ) := by p2m_exact_reverting @_root_.P2MW.S_SchwartzMap_tsum_eq_tsum_fourier_euclideanSpace.solution
