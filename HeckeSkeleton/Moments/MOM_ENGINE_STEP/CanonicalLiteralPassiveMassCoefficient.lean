import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralCombinedMassCoefficient

/-!
# Fixed profile powers after independent passive allocation

The original common occurrences, the original allocation's frozen
occurrences, and the new passive allocation's frozen occurrences each
retain their own slot budget. Their total is `3 * cap`. The first
residual scalar still enters only once through its original atom
budget, and both complete pre-removal radius powers are unchanged.

The extra slot power raises the fixed natural profile degree by
`2 * d * cap`. It introduces no new scale-dependent constant and does
not alter either actual divisor denominator. The contour and mass
constant below are chosen before every moving profile, scale or label.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveMassCoefficient

open NumberField DedekindZetaZeroFree HeckeGeneral.Characters
open CanonicalLiteralFirstScalarCost CanonicalLiteralMassProfilePower

/-- The additional original frozen pair costs exactly one further
`cap` power of the squared original profile control. -/
theorem extra_slot_power_le_profilePower
    (cap d : ℕ) (B P : ℝ) (hB : 0 ≤ B) (hP : 1 ≤ P) (hbound : B ≤ P ^ d) :
    slotBudget B ^ cap ≤ P ^ (2 * d * cap) := by
  simpa only [← pow_mul] using
    pow_le_pow_left₀ (zero_le_one.trans (slotBudget_one B))
      (slotBudget_le_profilePower B P d hB hP hbound) cap

private theorem three_slot_powers (B : ℝ) (cap : ℕ) :
    slotBudget B ^ (3 * cap) = slotBudget B ^ (2 * cap) * slotBudget B ^ cap := by
  rw [show 3 * cap = 2 * cap + cap by omega, pow_add]

/-- The numerator now has three separately proved frozen/common
charges. No bound for their whole product is assumed. -/
theorem atomCosts_le_profilePower (cap d : ℕ) (annulus B P : ℝ)
    (hannulus : 0 ≤ annulus) (hB : 0 ≤ B) (hP : 1 ≤ P) (hbound : B ≤ P ^ d) :
    atomBudget annulus B ^ cap * slotBudget B ^ (3 * cap) ≤
      (max 1 annulus) ^ cap * P ^ (8 * d * cap) := by
  have hfirst := separateAtoms_le_profilePower cap d annulus B P hannulus hB hP hbound
  have hextra := extra_slot_power_le_profilePower cap d B P hB hP hbound
  have h := mul_le_mul hfirst hextra
    (pow_nonneg (zero_le_one.trans (slotBudget_one B)) _)
    (mul_nonneg (pow_nonneg (zero_le_one.trans (le_max_left (1 : ℝ) annulus)) _)
      (pow_nonneg (zero_le_one.trans hP) _))
  calc
    _ = (atomBudget annulus B ^ cap * slotBudget B ^ (2 * cap)) *
        slotBudget B ^ cap := by rw [three_slot_powers]; ring
    _ ≤ ((max 1 annulus) ^ cap * P ^ (6 * d * cap)) * P ^ (2 * d * cap) := h
    _ = _ := by
      rw [show 8 * d * cap = 6 * d * cap + 2 * d * cap by ring, pow_add]
      ring

def degree (cap d dRow dFirstKernel dSecondKernel heightDegree : ℕ) : ℕ :=
  CanonicalLiteralUniformMassCoefficient.degree
    cap d dRow dFirstKernel dSecondKernel heightDegree + 2 * d * cap

theorem degree_eq_row_enlargement
    (cap d dRow dFirstKernel dSecondKernel heightDegree : ℕ) :
    degree cap d dRow dFirstKernel dSecondKernel heightDegree =
      CanonicalLiteralUniformMassCoefficient.degree
        cap d (dRow + 2 * d * cap) dFirstKernel dSecondKernel heightDegree := by
  simp only [degree, CanonicalLiteralUniformMassCoefficient.degree,
    CanonicalLiteralMassProfilePower.degree]
  ring

theorem degree_eq_explicit
    (cap d dRow dFirstKernel dSecondKernel heightDegree : ℕ) :
    degree cap d dRow dFirstKernel dSecondKernel heightDegree =
      heightDegree * ((cap + 2) + (cap + 2)) + d * ((cap + 2) + (cap + 2)) +
        8 * d * cap + dRow + dFirstKernel + dSecondKernel := by
  simp only [degree, CanonicalLiteralUniformMassCoefficient.degree,
    CanonicalLiteralMassProfilePower.degree]
  ring

private theorem row_with_extra_slots_le
    (cap d dRow : ℕ) (B P row : ℝ)
    (hB : 0 ≤ B) (hP : 1 ≤ P) (hbound : B ≤ P ^ d)
    (hrow : row ≤ P ^ dRow) :
    row * slotBudget B ^ cap ≤ P ^ (dRow + 2 * d * cap) := by
  have h := mul_le_mul hrow (extra_slot_power_le_profilePower cap d B P hB hP hbound)
    (pow_nonneg (zero_le_one.trans (slotBudget_one B)) _)
    (pow_nonneg (zero_le_one.trans hP) _)
  simpa only [pow_add] using h

variable (K : Type) [Field K] [NumberField K]
variable (A : SArithmeticData K) (σ : K →+* ℂ) (ω ψ : HeckeCharacter K)

/-- The same fixed contours pay the complete pre-removal radii and
all three original frozen/common slot charges. The independent norm
denominators remain in the separate arithmetic mass theorem. -/
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
            (atomBudget annulus originalBound ^ cap * slotBudget originalBound ^ (3 * cap))) *
          row * firstKernel * secondKernel ≤
            Cmass * control ^ degree cap d dRow dFirstKernel dSecondKernel heightDegree * Z ^ ε := by
  obtain ⟨δ, Cmass, hδ, hδhi, hCmass, hmass⟩ :=
    CanonicalLiteralUniformMassCoefficient.exists_uniform_coefficient K A σ ω ψ
      cap d (dRow + 2 * d * cap) dFirstKernel dSecondKernel heightDegree
      annulus lo hi hlo hhi hannulus δ₁ δ₂ orders ε mesh heightConstant widthBound hε hwidth
  refine ⟨δ, Cmass, hδ, hδhi, hCmass, ?_⟩
  intro Z T width height control originalBound row firstKernel secondKernel
    hZ hT hbox hheight hcontrol hB hBbound hrow hrowBound
    hfirst hfirstBound hsecond hsecondBound
  have hcontrolOne : 1 ≤ control := (le_add_of_nonneg_right hT).trans hcontrol
  have hrowExtra := row_with_extra_slots_le cap d dRow originalBound control row
    hB hcontrolOne hBbound hrowBound
  have h := hmass Z T width height control originalBound
    (row * slotBudget originalBound ^ cap) firstKernel secondKernel
    hZ hT hbox hheight hcontrol hB hBbound
    (mul_nonneg hrow (pow_nonneg (zero_le_one.trans (slotBudget_one originalBound)) _))
    hrowExtra hfirst hfirstBound hsecond hsecondBound
  rw [← degree_eq_row_enlargement cap d dRow dFirstKernel dSecondKernel heightDegree] at h
  simpa only [three_slot_powers, mul_assoc, mul_left_comm, mul_comm] using h

/-- Both original logarithmic tilts are chosen from the fixed length
box first. The original profile orders and the single-prime contour
are then fixed before the source, scale and passive labels. -/
theorem exists_uniform_combined_coefficient
    (cap d dRow dFirstKernel dSecondKernel heightDegree : ℕ)
    (annulus lo hi : ℝ) (hlo : 0 < lo) (hhi : 1 ≤ hi)
    (hannulus : 0 ≤ annulus) (lengthBound ε : ℝ)
    (hbound : 0 ≤ lengthBound) (hε : 0 < ε)
    (orders : Finset (ℕ × ℕ))
    (mesh heightConstant widthBound : ℝ) (hwidth : 0 ≤ widthBound) :
    let η := CanonicalLiteralCombinedMassCoefficient.mellinTilt lengthBound ε
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
            (atomBudget annulus originalBound ^ cap * slotBudget originalBound ^ (3 * cap))) *
          row * firstKernel * secondKernel) *
            Z ^ CanonicalFirstResidualProfileCost.tiltError m total mask active η η ≤
          Cmass * control ^ degree cap d dRow dFirstKernel dSecondKernel heightDegree * Z ^ ε := by
  obtain ⟨δ, Cmass, hδ, hδhi, hCmass, hmass⟩ :=
    CanonicalLiteralCombinedMassCoefficient.exists_uniform_combined_coefficient K A σ ω ψ
      cap d (dRow + 2 * d * cap) dFirstKernel dSecondKernel heightDegree
      annulus lo hi hlo hhi hannulus lengthBound ε hbound hε orders
      mesh heightConstant widthBound hwidth
  refine ⟨δ, Cmass, hδ, hδhi, hCmass, ?_⟩
  intro Z T width height control originalBound row firstKernel secondKernel
    m total mask active hZ hT hbox hheight hcontrol hB hBbound
    hrow hrowBound hfirst hfirstBound hsecond hsecondBound hm htotal hmask hactive
  have hcontrolOne : 1 ≤ control := (le_add_of_nonneg_right hT).trans hcontrol
  have hrowExtra := row_with_extra_slots_le cap d dRow originalBound control row
    hB hcontrolOne hBbound hrowBound
  have h := hmass Z T width height control originalBound
    (row * slotBudget originalBound ^ cap) firstKernel secondKernel
    m total mask active hZ hT hbox hheight hcontrol hB hBbound
    (mul_nonneg hrow (pow_nonneg (zero_le_one.trans (slotBudget_one originalBound)) _))
    hrowExtra hfirst hfirstBound hsecond hsecondBound hm htotal hmask hactive
  rw [← degree_eq_row_enlargement cap d dRow dFirstKernel dSecondKernel heightDegree] at h
  simpa only [three_slot_powers, mul_assoc, mul_left_comm, mul_comm] using h

end HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveMassCoefficient

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveMassCoefficient.extra_slot_power_le_profilePower
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveMassCoefficient.atomCosts_le_profilePower
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveMassCoefficient.degree_eq_explicit
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveMassCoefficient.exists_uniform_coefficient
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralPassiveMassCoefficient.exists_uniform_combined_coefficient
