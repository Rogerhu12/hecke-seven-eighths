import HeckeGeneral.Analysis.SixthPowerFreeDecomposition
import HeckeGeneral.Analysis.GlobalThetaData

/-!
# The strict complete-row input to inverse amplification

This interface keeps the original independent scales and parameter maps
fixed while the row cutoff and divisor scales vary.  It contains the
canonical inverse input and no independent-scale energy conclusion.
The arithmetic proof and the source-data interface can import it separately.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.UniformAmplify

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open scoped BigOperators Classical

variable {K : Type} [Field K] [NumberField K]
variable {ω ψ : HeckeCharacter K}

/-- Only the profile is pulled back.  All original arithmetic fields,
backgrounds, directions and fixed-place zeros remain unchanged. -/
def sixthRootInverseData (d : MomentData K ω ψ) : MomentData K ω ψ :=
  { d with inverseTest := {
      profile u t y := d.inverseTest.profile (sixthPowerFreePart u) t y
      support u t D := d.inverseTest.support (sixthPowerFreePart u) t D
      support_spec u t D I :=
        d.inverseTest.support_spec (sixthPowerFreePart u) t D I } }

variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- The canonical zero-slot seed controls complete rows and all smaller
polynomial scales of the same inherited profile.  Its height order is
uniform before any member of the source family or row scale is selected.
It is a strict-scale statement, not the independent-scale conclusion. -/
def CompleteIdealScaleSupSeed {ι : Type*}
    (family : ι → MomentData K ω ψ) (height : ι → ℝ) : Prop :=
  ∀ gap ε : ℝ, 0 < gap → gap < 1 → 0 < ε →
    ∃ C A h H₀ : ℝ, 0 < C ∧ 0 ≤ A ∧ 0 < h ∧ 1 ≤ H₀ ∧
      ∀ i H, H₀ ≤ H → height i ≤ H ^ h →
        ∃ B : NonzeroIdeal K → ℝ, (∀ u, 0 ≤ B u) ∧
          (∀ u ∈ (family i).rows H, ∀ D : ℝ, 0 < D → D ≤ H ^ (1 - gap) →
            ‖inversePolynomial (sixthRootInverseData (family i)) u D 0‖ ^ 2 ≤ B u) ∧
          (∑ u ∈ (family i).rows H, B u) ≤
            C * H ^ (1 + ε) * (1 + height i) ^ A

/-- The fixed independent source scales and row-local parameter maps.  The
amplified row scale H is not part of these data. -/
structure UnmarkedProfileParameters (dimension : ℕ) where
  rowScale : ℝ
  polynomialScale : ℝ
  rowScale_one_le : 1 ≤ rowScale
  polynomialScale_one_le : 1 ≤ polynomialScale
  sector : SixthUnitClasses K S
  heights : Fin dimension → ℝ
  realShifts : NonzeroIdeal K → Fin dimension → ℝ
  imagShifts : NonzeroIdeal K → Fin dimension → ℝ
  realShifts_bound : ∀ u, ‖realShifts u‖ ≤ 8
  imagShifts_bound : ∀ u, ‖imagShifts u‖ ≤ 1 + ‖heights‖

variable {S}

def unmarkedProfileData {dimension : ℕ}
    (unmarked : ℝ → ℝ → SixthUnitClasses K S → (Fin dimension → ℝ) →
      (NonzeroIdeal K → Fin dimension → ℝ) →
      (NonzeroIdeal K → Fin dimension → ℝ) → MomentData K ω ψ)
    (i : UnmarkedProfileParameters S dimension) : MomentData K ω ψ :=
  unmarked i.rowScale i.polynomialScale i.sector i.heights i.realShifts i.imagShifts

/-- A source-independent version of the corrected no-slot canonical
output.  It can be used by the shared source interface without importing
the source-specific amplification consumer. -/
def CompleteUnmarkedScaleSupBound {dimension : ℕ}
    (unmarked : ℝ → ℝ → SixthUnitClasses K S → (Fin dimension → ℝ) →
      (NonzeroIdeal K → Fin dimension → ℝ) →
      (NonzeroIdeal K → Fin dimension → ℝ) → MomentData K ω ψ) : Prop :=
  CompleteIdealScaleSupSeed (unmarkedProfileData unmarked) (fun i => ‖i.heights‖)

end HeckeSkeleton.Moments.UniformAmplify
