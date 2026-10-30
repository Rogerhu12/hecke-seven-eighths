import HeckeSkeleton.ActualProbeIntegrable
import HeckeSkeleton.ActualProbeSixthUnitInvariant

/-!
# Reduced construction of the original probe integral input

UNCOMPILED candidate. The only mathematical premise retained is precisely
the original theta_absolute field. The other four original fields follow
from the literal probe definitions and the actual compact tensor support.
-/

noncomputable section

namespace HeckeGeneral.ThetaSkeleton.Physical

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Global
open ActualDenominatorAbsoluteDraft
open scoped Classical

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable [MeasurableSpace (sLocalNormOneGroup K S)] [BorelSpace (sLocalNormOneGroup K S)]

theorem ProbeIntegralInput.of_analytic_inputs (P : ProbeData K S) (ψ : HeckeCharacter K)
    (htheta : ∀ (m : S.integer K) (Q : Finset (ExteriorPrime K S)) (Z : ℝ),
      0 < Z → Summable (completedTerm K S P.arithmetic (thetaPeriod K S P ψ) m
        (primeSetIdeal K S ∅) Q logGaussianProfile Z)) :
    ProbeIntegralInput K S P ψ where
  theta_absolute := htheta
  row_finite := probeIntegralInput_row_finite K S P ψ
  denominator_absolute := actual_probeDenominator_absolute K S P ψ
  integral := probeIntegralInput_integral K S P ψ
  sixth_unit_invariant := probeIntegralInput_sixth_unit_invariant K S P ψ

end HeckeGeneral.ThetaSkeleton.Physical
