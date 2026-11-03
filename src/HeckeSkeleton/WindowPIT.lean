import HeckeSkeleton.WindowPIT.FromCounting
import HeckeSkeleton.WindowPIT.Counting

/-! The original prime window lower bound, using the unconditional prime ideal theorem. -/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.WindowPIT

open NumberField IsDedekindDomain HeckeGeneral.ThetaSkeleton.Global
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

theorem window_prime_lower (w : SmoothAnnularTest)
    (hre : ∀ y, (w.toFun y).im = 0) (hnn : ∀ y, 0 ≤ (w.toFun y).re)
    (hne : ∃ y, w.toFun y ≠ 0) (hsupp : Function.support w.toFun ⊆ Set.Ioo 1 2) :
    ∃ c X₀ : ℝ, 0 < c ∧ 1 < X₀ ∧ ∀ X : ℝ, X₀ ≤ X →
      c * X / Real.log X ≤
        ∑ p ∈ windowPrimes K S X, (w.toFun ((p.asIdeal.absNorm : ℝ) / X)).re :=
  window_prime_lower_of_counting K S
    (TauCeti.primeCount_univ_isEquivalent_div_log K) w hre hnn hne hsupp

end HeckeSkeleton.WindowPIT
