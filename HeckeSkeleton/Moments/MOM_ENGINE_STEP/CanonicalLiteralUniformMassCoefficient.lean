import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralMassProfilePower
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralKernelConstants

/-!
# Uniform payment of the literal mass coefficient

The same actual kernel theorem leaves an explicit coefficient in front
of its arithmetic sum. This file pays that coefficient: both complete
pre-removal profile counts, the original first scalar pair, all second
common and frozen atoms, and the two original Fourier seminorms.

The contour, constant and natural profile degree are selected before
the scale, source, label and original control values. Only individual
original profile and single-character height windows are inputs. No
kernel mass or terminal estimate is assumed here.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep.CanonicalLiteralUniformMassCoefficient

open NumberField DedekindZetaZeroFree HeckeGeneral.Characters
open CanonicalLiteralFirstScalarCost

variable (K : Type) [Field K] [NumberField K]
variable (A : SArithmeticData K) (σ : K →+* ℂ) (ω ψ : HeckeCharacter K)

/-- The height exponent pays the original single-prime factor on both
complete pre-removal profile lists. All other degrees are the exact
separate original-profile charges. -/
def degree (cap d dRow dFirstKernel dSecondKernel heightDegree : ℕ) : ℕ :=
  heightDegree * ((cap + 2) + (cap + 2)) +
    CanonicalLiteralMassProfilePower.degree cap d dRow dFirstKernel dSecondKernel

/-- A single original control may dominate both `1 + T` and the
individual original profile values. The chosen contour and constant
do not depend on any of those moving values. -/
theorem exists_uniform_coefficient
    (cap d dRow dFirstKernel dSecondKernel heightDegree : ℕ)
    (annulus lo hi : ℝ) (hlo : 0 < lo) (hhi : 1 ≤ hi)
    (hannulus : 0 ≤ annulus) (δ₁ δ₂ : ℝ) (orders : Finset (ℕ × ℕ))
    (ε mesh heightConstant widthBound : ℝ) (hε : 0 < ε) (hwidth : 0 ≤ widthBound) :
    ∃ δ Cmass : ℝ, 0 < δ ∧ δ ≤ 1 / 4 ∧ 0 < Cmass ∧
      ∀ Z T width height control originalBound row firstKernel secondKernel : ℝ,
        1 ≤ Z → 0 ≤ T → width ≤ widthBound →
        height ≤ heightConstant * (1 + Real.log Z) * (1 + T) ^ heightDegree →
        1 + T ≤ control →
        0 ≤ originalBound → originalBound ≤ control ^ d →
        0 ≤ row → row ≤ control ^ dRow →
        0 ≤ firstKernel → firstKernel ≤ control ^ dFirstKernel →
        0 ≤ secondKernel → secondKernel ≤ control ^ dSecondKernel →
        CanonicalLiteralKernelConstants.constant K A σ ω ψ cap (orders.sup Prod.snd) *
          (2 * CanonicalFullKappaPrime.radiusFactor K Z δ mesh
            (CanonicalHeckePrimeAnalytic.degreeBound K) height
            (CompleteMovingRowRecipe.primeMaskLogBound A Z width)) ^
              ((cap + 2) + (cap + 2)) *
          ((1 + CanonicalLiteralActiveRadius.twoSignsCoefficient
              originalBound lo hi hlo δ₁ δ₂ orders) ^ ((cap + 2) + (cap + 2)) *
            (atomBudget annulus originalBound ^ cap *
              CanonicalLiteralMassProfilePower.slotBudget originalBound ^ (2 * cap))) *
          row * firstKernel * secondKernel ≤
            Cmass * control ^ degree cap d dRow dFirstKernel dSecondKernel heightDegree *
              Z ^ ε := by
  let N := (cap + 2) + (cap + 2)
  let profileDegree :=
    CanonicalLiteralMassProfilePower.degree cap d dRow dFirstKernel dSecondKernel
  let Ckernel :=
    CanonicalLiteralKernelConstants.constant K A σ ω ψ cap (orders.sup Prod.snd)
  let Cprofile :=
    CanonicalLiteralMassProfilePower.coefficient cap annulus lo hi hlo δ₁ δ₂ orders
  have hCkernel : 0 < Ckernel :=
    CanonicalLiteralKernelConstants.constant_pos K A σ ω ψ cap (orders.sup Prod.snd)
  have hCprofile : 0 < Cprofile :=
    CanonicalLiteralMassProfilePower.coefficient_pos cap annulus lo hi hlo hhi δ₁ δ₂ orders
  obtain ⟨δ, Cr, hδ, hδhi, hCr, hradius⟩ :=
    CanonicalFullKappaPrime.exists_complete_profile_radius_bound A N heightDegree
      ε mesh (CanonicalHeckePrimeAnalytic.degreeBound K) heightConstant widthBound
      hε CanonicalHeckePrimeAnalytic.degreeBound_pos.le hwidth
  refine ⟨δ, Ckernel * (2 * Cr) ^ N * Cprofile, hδ, hδhi, ?_, ?_⟩
  · exact mul_pos (mul_pos hCkernel
      (pow_pos (mul_pos (by norm_num) (zero_lt_one.trans_le hCr)) _)) hCprofile
  intro Z T width height control originalBound row firstKernel secondKernel
    hZ hT hbox hheight hcontrol hB hBbound hrow hrowBound
    hfirst hfirstBound hsecond hsecondBound
  have hcontrolOne : 1 ≤ control := (le_add_of_nonneg_right hT).trans hcontrol
  have hcontrolZero : 0 ≤ control := zero_le_one.trans hcontrolOne
  have hZε : 0 ≤ Z ^ ε := Real.rpow_nonneg (zero_le_one.trans hZ) _
  let factor := CanonicalFullKappaPrime.radiusFactor K Z δ mesh
    (CanonicalHeckePrimeAnalytic.degreeBound K) height
    (CompleteMovingRowRecipe.primeMaskLogBound A Z width)
  have hheightPower : (1 + T) ^ (heightDegree * N) ≤ control ^ (heightDegree * N) :=
    pow_le_pow_left₀ (by positivity) hcontrol _
  have hfactor : (2 * factor) ^ N ≤
      (2 * Cr) ^ N * control ^ (heightDegree * N) * Z ^ ε := by
    calc
      _ = (2 : ℝ) ^ N * factor ^ N := mul_pow _ _ _
      _ ≤ (2 : ℝ) ^ N *
          (Cr ^ N * (1 + T) ^ (heightDegree * N) * Z ^ ε) :=
        mul_le_mul_of_nonneg_left
          (hradius Z T width height hZ hT hbox hheight) (pow_nonneg (by norm_num) _)
      _ ≤ (2 : ℝ) ^ N * (Cr ^ N * control ^ (heightDegree * N) * Z ^ ε) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hheightPower
              (pow_nonneg (zero_le_one.trans hCr) _)) hZε)
          (pow_nonneg (by norm_num) _)
      _ = _ := by rw [mul_pow]; ring
  have hprofiles := CanonicalLiteralMassProfilePower.complete_coefficient_le_profilePower
    cap d dRow dFirstKernel dSecondKernel annulus originalBound control lo hi hlo hhi
    δ₁ δ₂ orders row firstKernel secondKernel hannulus hB hcontrolOne hBbound
    hrow hfirst hsecond hrowBound hfirstBound hsecondBound
  have hfixed : 0 ≤ CanonicalLiteralActiveRadius.twoSignsCoefficient
      originalBound lo hi hlo δ₁ δ₂ orders :=
    CanonicalLiteralActiveRadius.twoSignsCoefficient_nonneg
      originalBound lo hi hB hlo hhi δ₁ δ₂ orders
  have hatom : 0 ≤ atomBudget annulus originalBound :=
    zero_le_one.trans (atomBudget_one annulus originalBound)
  have hslot : 0 ≤ CanonicalLiteralMassProfilePower.slotBudget originalBound :=
    zero_le_one.trans (CanonicalLiteralMassProfilePower.slotBudget_one originalBound)
  have hproduct := mul_le_mul hfactor hprofiles (by positivity)
    (mul_nonneg (mul_nonneg (pow_nonneg
      (mul_nonneg (by norm_num) (zero_le_one.trans hCr)) _)
      (pow_nonneg hcontrolZero _)) hZε)
  calc
    _ = Ckernel * ((2 * factor) ^ N *
        (((1 + CanonicalLiteralActiveRadius.twoSignsCoefficient
            originalBound lo hi hlo δ₁ δ₂ orders) ^ N *
          (atomBudget annulus originalBound ^ cap *
            CanonicalLiteralMassProfilePower.slotBudget originalBound ^ (2 * cap))) *
          row * firstKernel * secondKernel)) := by
      dsimp only [Ckernel, factor, N]
      ring
    _ ≤ Ckernel * (((2 * Cr) ^ N * control ^ (heightDegree * N) * Z ^ ε) *
        (Cprofile * control ^ profileDegree)) :=
      mul_le_mul_of_nonneg_left hproduct hCkernel.le
    _ = _ := by
      simp only [degree, N, profileDegree, pow_add]
      ring

end HeckeSkeleton.Moments.EngineStep.CanonicalLiteralUniformMassCoefficient

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralUniformMassCoefficient.exists_uniform_coefficient
