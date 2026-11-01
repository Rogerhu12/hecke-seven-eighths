import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralPassiveMassCoefficient

/-!
# The numerical coefficient of the original primitive source

These two expressions are the actual projections of the constructed
kernel and indexed-weight certificates.  The two fixed Fourier kernels
and the original unit index are paid once in a fixed constant.  The
moving tag power is left for the original amplified arithmetic index.
The full radius exponent and all three slot charges remain present.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPrimitiveMassCoefficient

open NumberField DedekindZetaZeroFree HeckeGeneral.Characters
open CanonicalLiteralFirstScalarCost CanonicalLiteralMassProfilePower

variable (K : Type) [Field K] [NumberField K]
variable (A : SArithmeticData K) (σ : K →+* ℂ) (ω ψ : HeckeCharacter K)

def kernelCoefficient (cap : ℕ) (orders : Finset (ℕ × ℕ))
    (lo hi : ℝ) (hlo : 0 < lo) (δ₁ δ₂ δ mesh : ℝ)
    (Z height width originalBound firstKernel secondKernel : ℝ) : ℝ :=
  CanonicalLiteralKernelConstants.constant K A σ ω ψ cap (orders.sup Prod.snd) *
    (2 * CanonicalFullKappaPrime.radiusFactor K Z δ mesh
      (CanonicalHeckePrimeAnalytic.degreeBound K) height
      (CompleteMovingRowRecipe.primeMaskLogBound A Z width)) ^ ((cap + 2) + (cap + 2)) *
    (1 + CanonicalLiteralActiveRadius.twoSignsCoefficient
      originalBound lo hi hlo δ₁ δ₂ orders) ^ ((cap + 2) + (cap + 2)) *
    firstKernel * secondKernel

def indexCoefficient (cap : ℕ) (annulus originalBound unitIndex : ℝ)
    (Z error mesh m total mask active δ₁ δ₂ moving : ℝ) : ℝ :=
  (orbitalFieldFactor K * atomBudget annulus originalBound ^ cap) *
    (unitIndex * 1 * slotBudget originalBound ^ (3 * cap) * orbitalFieldFactor K) *
    Z ^ (moving + 5 * error / 3 + mesh +
      CanonicalFirstResidualProfileCost.tiltError m total mask active δ₁ δ₂)

theorem kernelCoefficient_nonneg (cap : ℕ) (orders : Finset (ℕ × ℕ))
    (lo hi : ℝ) (hlo : 0 < lo) (hhi : 1 ≤ hi) (δ₁ δ₂ δ mesh : ℝ)
    (Z height width originalBound firstKernel secondKernel : ℝ)
    (hZ : 0 < Z) (hB : 0 ≤ originalBound)
    (hfirst : 0 ≤ firstKernel) (hsecond : 0 ≤ secondKernel) :
    0 ≤ kernelCoefficient K A σ ω ψ cap orders lo hi hlo δ₁ δ₂ δ mesh
      Z height width originalBound firstKernel secondKernel := by
  have hc := (CanonicalLiteralKernelConstants.constant_pos K A σ ω ψ cap
    (orders.sup Prod.snd)).le
  have hr := (CanonicalFullKappaPrime.radiusFactor_pos (K := K)
    Z δ mesh (CanonicalHeckePrimeAnalytic.degreeBound K) height
    (CompleteMovingRowRecipe.primeMaskLogBound A Z width) hZ).le
  have hf := CanonicalLiteralActiveRadius.twoSignsCoefficient_nonneg
    originalBound lo hi hB hlo hhi δ₁ δ₂ orders
  unfold kernelCoefficient
  positivity

/-- The complete fixed profile numerator is exactly the product of
the actual two certificates, after its original tag power is removed. -/
theorem product_eq (cap : ℕ) (orders : Finset (ℕ × ℕ))
    (annulus lo hi : ℝ) (hlo : 0 < lo) (δ₁ δ₂ δ mesh : ℝ)
    (Z height width originalBound firstKernel secondKernel unitIndex
      error m total mask active moving : ℝ) (hZ : 0 < Z) :
    kernelCoefficient K A σ ω ψ cap orders lo hi hlo δ₁ δ₂ δ mesh
      Z height width originalBound firstKernel secondKernel *
      indexCoefficient K cap annulus originalBound unitIndex
        Z error mesh m total mask active δ₁ δ₂ moving =
    (unitIndex * orbitalFieldFactor K ^ 2 * firstKernel * secondKernel) *
      ((CanonicalLiteralKernelConstants.constant K A σ ω ψ cap (orders.sup Prod.snd) *
        (2 * CanonicalFullKappaPrime.radiusFactor K Z δ mesh
          (CanonicalHeckePrimeAnalytic.degreeBound K) height
          (CompleteMovingRowRecipe.primeMaskLogBound A Z width)) ^ ((cap + 2) + (cap + 2)) *
        ((1 + CanonicalLiteralActiveRadius.twoSignsCoefficient
          originalBound lo hi hlo δ₁ δ₂ orders) ^ ((cap + 2) + (cap + 2)) *
          (atomBudget annulus originalBound ^ cap * slotBudget originalBound ^ (3 * cap)))) *
        Z ^ CanonicalFirstResidualProfileCost.tiltError m total mask active δ₁ δ₂) *
      Z ^ (5 * error / 3 + mesh) * Z ^ moving := by
  unfold kernelCoefficient indexCoefficient
  rw [show moving + 5 * error / 3 + mesh +
      CanonicalFirstResidualProfileCost.tiltError m total mask active δ₁ δ₂ =
      CanonicalFirstResidualProfileCost.tiltError m total mask active δ₁ δ₂ +
        (5 * error / 3 + mesh) + moving by ring,
    Real.rpow_add hZ, Real.rpow_add hZ]
  ring

/-- The contour, constant and natural exponent are fixed before every
scale, source, physical divisor and second common label.  No bound on
a family or its mass is an input. -/
theorem exists_uniform_product
    (cap d heightDegree : ℕ) (annulus lo hi : ℝ)
    (hlo : 0 < lo) (hhi : 1 ≤ hi) (hannulus : 0 ≤ annulus)
    (lengthBound ε : ℝ) (hbound : 0 ≤ lengthBound) (hε : 0 < ε)
    (orders : Finset (ℕ × ℕ)) (mesh heightConstant widthBound : ℝ)
    (hwidth : 0 ≤ widthBound)
    (unitIndex firstKernel secondKernel : ℝ)
    (hunit : 0 ≤ unitIndex) (hfirst : 0 ≤ firstKernel) (hsecond : 0 ≤ secondKernel) :
    let η := CanonicalLiteralCombinedMassCoefficient.mellinTilt lengthBound ε
    ∃ δ Cmass : ℝ, 0 < δ ∧ δ ≤ 1 / 4 ∧ 0 < Cmass ∧
      ∀ Z T width height control originalBound error m total mask active moving : ℝ,
        1 ≤ Z → 0 ≤ T → width ≤ widthBound →
        height ≤ heightConstant * (1 + Real.log Z) * (1 + T) ^ heightDegree →
        1 + T ≤ control → 0 ≤ originalBound → originalBound ≤ control ^ d →
        0 ≤ m → total ≤ lengthBound → mask ≤ lengthBound → active ≤ lengthBound →
        kernelCoefficient K A σ ω ψ cap orders lo hi hlo η η δ mesh
          Z height width originalBound firstKernel secondKernel *
          indexCoefficient K cap annulus originalBound unitIndex
            Z error mesh m total mask active η η moving ≤
          Cmass * control ^ CanonicalLiteralPassiveMassCoefficient.degree
            cap d 0 0 0 heightDegree * Z ^ (ε + 5 * error / 3 + mesh) * Z ^ moving := by
  let η := CanonicalLiteralCombinedMassCoefficient.mellinTilt lengthBound ε
  obtain ⟨δ, C₀, hδ, hδhi, hC₀, hmass⟩ :=
    CanonicalLiteralPassiveMassCoefficient.exists_uniform_combined_coefficient
      K A σ ω ψ cap d 0 0 0 heightDegree annulus lo hi hlo hhi hannulus
      lengthBound ε hbound hε orders mesh heightConstant widthBound hwidth
  let fixed := unitIndex * orbitalFieldFactor K ^ 2 * firstKernel * secondKernel
  have hfixed : 0 ≤ fixed := by dsimp [fixed]; positivity
  refine ⟨δ, (1 + fixed) * C₀, hδ, hδhi, mul_pos (by positivity) hC₀, ?_⟩
  intro Z T width height control originalBound error m total mask active moving
    hZ hT hbox hheight hcontrol hB hBbound hm htotal hmask hactive
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  have hP : 0 ≤ control := zero_le_one.trans ((le_add_of_nonneg_right hT).trans hcontrol)
  have h := hmass Z T width height control originalBound 1 1 1
    m total mask active hZ hT hbox hheight hcontrol hB hBbound
    (by norm_num) (by simp only [pow_zero])
    (by norm_num) (by simp only [pow_zero])
    (by norm_num) (by simp only [pow_zero]) hm htotal hmask hactive
  simp only [mul_one] at h
  have hlarge : 0 ≤ C₀ * control ^ CanonicalLiteralPassiveMassCoefficient.degree
      cap d 0 0 0 heightDegree * Z ^ ε := by positivity
  have hscaled := mul_le_mul_of_nonneg_left h hfixed
  have hfixed' : fixed ≤ 1 + fixed := by linarith
  have hfixedBound := mul_le_mul_of_nonneg_right hfixed' hlarge
  have he := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hscaled.trans hfixedBound)
      (Real.rpow_nonneg hz.le (5 * error / 3 + mesh)))
    (Real.rpow_nonneg hz.le moving)
  rw [product_eq K A σ ω ψ cap orders annulus lo hi hlo η η δ mesh
    Z height width originalBound firstKernel secondKernel unitIndex
    error m total mask active moving hz]
  calc
    _ ≤ ((1 + fixed) *
        (C₀ * control ^ CanonicalLiteralPassiveMassCoefficient.degree
          cap d 0 0 0 heightDegree * Z ^ ε)) * Z ^ (5 * error / 3 + mesh) * Z ^ moving := he
    _ = _ := by
      rw [show ε + 5 * error / 3 + mesh = ε + (5 * error / 3 + mesh) by ring,
        Real.rpow_add hz]
      ring

end HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPrimitiveMassCoefficient

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPrimitiveMassCoefficient.kernelCoefficient_nonneg
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPrimitiveMassCoefficient.product_eq
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPrimitiveMassCoefficient.exists_uniform_product
