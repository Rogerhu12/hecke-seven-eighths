import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralUniformMassCoefficient
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalFirstResidualProfileCost

set_option linter.unusedSectionVars false

/-!
# Fixed choices for the complete redistributed mass coefficient

The residual profile scalars are paid together with the original first
Poisson weight. Their only extra exponent is the literal `tiltError`.
Here both logarithmic tilts are fixed from the original length box and
the requested loss, before any source, scale, row or profile is given.

After that choice, the original Fourier orders may be chosen. The
single-prime contour and mass constant are then fixed before all moving
data. Half of the requested loss pays the complete pre-removal profile
radii; the other half pays the actual first-stage tilt. The original
atom costs, both Fourier seminorms and their full natural powers remain
in the displayed coefficient.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep.CanonicalLiteralCombinedMassCoefficient

open NumberField DedekindZetaZeroFree HeckeGeneral.Characters
open CanonicalLiteralFirstScalarCost

/-- This fixed positive tilt can be used for both original logarithmic
transforms. It does not depend on the Fourier orders or moving data. -/
def mellinTilt (lengthBound ε : ℝ) : ℝ :=
  min (1 / 4 : ℝ) (ε / (16 * (lengthBound + 1)))

theorem mellinTilt_properties {lengthBound ε : ℝ}
    (hbound : 0 ≤ lengthBound) (hε : 0 < ε) :
    0 < mellinTilt lengthBound ε ∧
      mellinTilt lengthBound ε ≤ 1 / 4 ∧
      mellinTilt lengthBound ε + mellinTilt lengthBound ε ≤ 1 / 2 ∧
      8 * lengthBound * mellinTilt lengthBound ε ≤ ε / 2 := by
  sorry

/-- The original nonnegative parent length and the three original
upper windows pay the exact tilt, without replacing its main exponent. -/
theorem tiltError_le_half {lengthBound ε m total mask active : ℝ}
    (hbound : 0 ≤ lengthBound) (hε : 0 < ε) (hm : 0 ≤ m)
    (htotal : total ≤ lengthBound) (hmask : mask ≤ lengthBound)
    (hactive : active ≤ lengthBound) :
    CanonicalFirstResidualProfileCost.tiltError m total mask active
      (mellinTilt lengthBound ε) (mellinTilt lengthBound ε) ≤ ε / 2 := by
  sorry

variable (K : Type) [Field K] [NumberField K]
variable (A : SArithmeticData K) (σ : K →+* ℂ) (ω ψ : HeckeCharacter K)

/-- The actual combined coefficient is uniformly paid after the two
original logarithmic tilts have been fixed. All hypotheses concern
individual original profile controls, analytic heights or numerical
length windows; no normalized-family mass bound is supplied. -/
theorem exists_uniform_combined_coefficient
    (cap d dRow dFirstKernel dSecondKernel heightDegree : ℕ)
    (annulus lo hi : ℝ) (hlo : 0 < lo) (hhi : 1 ≤ hi)
    (hannulus : 0 ≤ annulus) (lengthBound ε : ℝ)
    (hbound : 0 ≤ lengthBound) (hε : 0 < ε)
    (orders : Finset (ℕ × ℕ))
    (mesh heightConstant widthBound : ℝ) (hwidth : 0 ≤ widthBound) :
    let η := mellinTilt lengthBound ε
    ∃ δ Cmass : ℝ, 0 < δ ∧ δ ≤ 1 / 4 ∧ 0 < Cmass ∧
      ∀ Z T width height control originalBound row firstKernel secondKernel
          m total mask active : ℝ,
        1 ≤ Z → 0 ≤ T → width ≤ widthBound →
        height ≤ heightConstant * (1 + Real.log Z) * (1 + T) ^ heightDegree →
        1 + T ≤ control →
        0 ≤ originalBound → originalBound ≤ control ^ d →
        0 ≤ row → row ≤ control ^ dRow →
        0 ≤ firstKernel → firstKernel ≤ control ^ dFirstKernel →
        0 ≤ secondKernel → secondKernel ≤ control ^ dSecondKernel →
        0 ≤ m → total ≤ lengthBound → mask ≤ lengthBound → active ≤ lengthBound →
        (CanonicalLiteralKernelConstants.constant K A σ ω ψ cap (orders.sup Prod.snd) *
          (2 * CanonicalFullKappaPrime.radiusFactor K Z δ mesh
            (CanonicalHeckePrimeAnalytic.degreeBound K) height
            (CompleteMovingRowRecipe.primeMaskLogBound A Z width)) ^
              ((cap + 2) + (cap + 2)) *
          ((1 + CanonicalLiteralActiveRadius.twoSignsCoefficient
              originalBound lo hi hlo η η orders) ^ ((cap + 2) + (cap + 2)) *
            (atomBudget annulus originalBound ^ cap *
              CanonicalLiteralMassProfilePower.slotBudget originalBound ^ (2 * cap))) *
          row * firstKernel * secondKernel) *
            Z ^ CanonicalFirstResidualProfileCost.tiltError m total mask active η η ≤
          Cmass * control ^ CanonicalLiteralUniformMassCoefficient.degree
            cap d dRow dFirstKernel dSecondKernel heightDegree * Z ^ ε := by
  sorry

end HeckeSkeleton.Moments.EngineStep.CanonicalLiteralCombinedMassCoefficient

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralCombinedMassCoefficient.mellinTilt_properties
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralCombinedMassCoefficient.tiltError_le_half
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralCombinedMassCoefficient.exists_uniform_combined_coefficient
