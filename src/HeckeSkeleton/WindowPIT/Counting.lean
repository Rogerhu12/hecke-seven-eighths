import HeckeSkeleton.WindowPIT.IntervalAsymptotics
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Prime.PrimeIdealTheorem

/-!
# Prime ideal counts in fixed ratio intervals

The sole number theoretic input is TauCeti's prime ideal theorem for an
arbitrary number field. The difference of inclusive prime counts records
the interval `(a * X, b * X]`.
-/

set_option autoImplicit false

namespace HeckeSkeleton.WindowPIT

open Filter
open scoped Topology

variable (K : Type) [Field K] [NumberField K]

/-- The prime ideal theorem after a fixed positive dilation. -/
theorem primeCount_scaled_div_tendsto (t : ℝ) (ht : 0 < t) :
    Tendsto
      (fun X : ℝ => TauCeti.primeCount K Set.univ (t * X) / (X / Real.log X))
      atTop (𝓝 t) :=
  scaled_div_tendsto (TauCeti.primeCount K Set.univ)
    (TauCeti.primeCount_univ_isEquivalent_div_log K) t ht

/-- A fixed interval of positive relative length contains `≫ X / log X` prime
ideals once `X` is sufficiently large. -/
theorem primeCount_interval_lower (a b : ℝ) (ha : 1 < a) (hab : a < b) :
    ∃ c X₀ : ℝ, 0 < c ∧ 1 < X₀ ∧ ∀ X : ℝ, X₀ ≤ X →
      c * X / Real.log X ≤
        TauCeti.primeCount K Set.univ (b * X) -
          TauCeti.primeCount K Set.univ (a * X) :=
  interval_lower_of_equivalent (TauCeti.primeCount K Set.univ)
    (TauCeti.primeCount_univ_isEquivalent_div_log K) a b ha hab

end HeckeSkeleton.WindowPIT
