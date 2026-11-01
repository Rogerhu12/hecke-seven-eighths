import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralUniformMassCoefficient
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalFirstResidualProfileCost

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
  have hden : 0 < 16 * (lengthBound + 1) := by positivity
  have hpos : 0 < mellinTilt lengthBound ε :=
    lt_min (by norm_num) (div_pos hε hden)
  have hsmall : mellinTilt lengthBound ε ≤ 1 / 4 := min_le_left _ _
  have hpaid : mellinTilt lengthBound ε * (16 * (lengthBound + 1)) ≤ ε :=
    (le_div_iff₀ hden).mp (min_le_right _ _)
  refine ⟨hpos, hsmall, ?_, ?_⟩ <;> nlinarith

/-- The original nonnegative parent length and the three original
upper windows pay the exact tilt, without replacing its main exponent. -/
theorem tiltError_le_half {lengthBound ε m total mask active : ℝ}
    (hbound : 0 ≤ lengthBound) (hε : 0 < ε) (hm : 0 ≤ m)
    (htotal : total ≤ lengthBound) (hmask : mask ≤ lengthBound)
    (hactive : active ≤ lengthBound) :
    CanonicalFirstResidualProfileCost.tiltError m total mask active
      (mellinTilt lengthBound ε) (mellinTilt lengthBound ε) ≤ ε / 2 := by
  obtain ⟨hpos, _, _, hpaid⟩ := mellinTilt_properties hbound hε
  calc
    _ ≤ 4 * lengthBound *
        (mellinTilt lengthBound ε + mellinTilt lengthBound ε) :=
      CanonicalFirstResidualProfileCost.tiltError_le hm hbound htotal hmask hactive
        hpos.le hpos.le
    _ = 8 * lengthBound * mellinTilt lengthBound ε := by ring
    _ ≤ _ := hpaid

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
  let η := mellinTilt lengthBound ε
  obtain ⟨δ, Cmass, hδ, hδhi, hCmass, hmass⟩ :=
    CanonicalLiteralUniformMassCoefficient.exists_uniform_coefficient K A σ ω ψ
      cap d dRow dFirstKernel dSecondKernel heightDegree annulus lo hi hlo hhi
      hannulus η η orders (ε / 2) mesh heightConstant widthBound (by positivity) hwidth
  refine ⟨δ, Cmass, hδ, hδhi, hCmass, ?_⟩
  intro Z T width height control originalBound row firstKernel secondKernel
    m total mask active hZ hT hbox hheight hcontrol hB hBbound
    hrow hrowBound hfirst hfirstBound hsecond hsecondBound hm htotal hmask hactive
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  have hcontrolZero : 0 ≤ control :=
    zero_le_one.trans ((le_add_of_nonneg_right hT).trans hcontrol)
  have hcoefficient := hmass Z T width height control originalBound row firstKernel
    secondKernel hZ hT hbox hheight hcontrol hB hBbound hrow hrowBound
    hfirst hfirstBound hsecond hsecondBound
  have htilt : CanonicalFirstResidualProfileCost.tiltError
      m total mask active η η ≤ ε / 2 :=
    tiltError_le_half hbound hε hm htotal hmask hactive
  have hpower := Real.rpow_le_rpow_of_exponent_le hZ htilt
  have hnonneg : 0 ≤ Cmass * control ^ CanonicalLiteralUniformMassCoefficient.degree
      cap d dRow dFirstKernel dSecondKernel heightDegree * Z ^ (ε / 2) :=
    mul_nonneg (mul_nonneg hCmass.le (pow_nonneg hcontrolZero _))
      (Real.rpow_nonneg hz.le _)
  calc
    _ ≤ (Cmass * control ^ CanonicalLiteralUniformMassCoefficient.degree
        cap d dRow dFirstKernel dSecondKernel heightDegree * Z ^ (ε / 2)) *
          Z ^ (ε / 2) :=
      mul_le_mul hcoefficient hpower (Real.rpow_nonneg hz.le _) hnonneg
    _ = (Cmass * control ^ CanonicalLiteralUniformMassCoefficient.degree
        cap d dRow dFirstKernel dSecondKernel heightDegree) *
          (Z ^ (ε / 2) * Z ^ (ε / 2)) := by ring
    _ = _ := by
      rw [← Real.rpow_add hz, show ε / 2 + ε / 2 = ε by ring]

end HeckeSkeleton.Moments.EngineStep.CanonicalLiteralCombinedMassCoefficient

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralCombinedMassCoefficient.mellinTilt_properties
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralCombinedMassCoefficient.tiltError_le_half
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralCombinedMassCoefficient.exists_uniform_combined_coefficient
