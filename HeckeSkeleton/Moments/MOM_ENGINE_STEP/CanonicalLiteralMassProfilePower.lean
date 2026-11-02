import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralFirstScalarCost
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralActiveRadius

set_option linter.unusedSectionVars false

/-!
# Fixed original-profile powers for the literal mass coefficient

The two first constants have already been bounded once by the original
frozen atom budget. The common and allocated second occurrences have
their separate squared original-profile budget. The literal normalized
radius is the explicit affine function of the same original control.

This module combines those calculated quantities. Its constant depends
only on the original annulus, fixed tilts, finite orders and slot cap;
its natural degree is selected before any original profile, scale,
source, Fourier point or actual label. No child weight or kernel-mass
bound is among the inputs.
-/

noncomputable section

namespace HeckeSkeleton.Moments.EngineStep.CanonicalLiteralMassProfilePower

open CanonicalLiteralFirstScalarCost

/-- The second occurrences have already paid the two literal norm
transforms, so their remaining individual cost is just a square. -/
def slotBudget (B : ℝ) : ℝ := max 1 (B ^ 2)

theorem slotBudget_one (B : ℝ) : 1 ≤ slotBudget B := by
  sorry

theorem slotBudget_atom (B : ℝ) : B ^ 2 ≤ slotBudget B := by
  sorry

/-- The fixed first annulus contributes to the constant only. -/
theorem atomBudget_le_profilePower (annulus B P : ℝ) (d : ℕ)
    (hannulus : 0 ≤ annulus) (hB : 0 ≤ B) (hP : 1 ≤ P)
    (hbound : B ≤ P ^ d) :
    atomBudget annulus B ≤ max 1 annulus * P ^ (2 * d) := by
  sorry

theorem slotBudget_le_profilePower (B P : ℝ) (d : ℕ)
    (hB : 0 ≤ B) (hP : 1 ≤ P) (hbound : B ≤ P ^ d) :
    slotBudget B ≤ P ^ (2 * d) := by
  sorry

/-- The first scalar pair costs `cap` original atom factors. The
second common and allocation costs contribute `2 * cap` more. -/
theorem separateAtoms_le_profilePower (cap d : ℕ) (annulus B P : ℝ)
    (hannulus : 0 ≤ annulus) (hB : 0 ≤ B) (hP : 1 ≤ P)
    (hbound : B ≤ P ^ d) :
    atomBudget annulus B ^ cap * slotBudget B ^ (2 * cap) ≤
      (max 1 annulus) ^ cap * P ^ (6 * d * cap) := by
  sorry

/-- The literal radius coefficient is affine in the original control.
All other factors remain fixed before that control is evaluated. -/
theorem combined_le_scale (B Cshape Cfourier factor clipping T : ℝ)
    (hshape : 0 ≤ Cshape) (hfourier : 0 ≤ Cfourier)
    (hfactor : 0 ≤ factor) (hclipping : 0 ≤ clipping)
    (hT : 1 ≤ T) (hBT : B ≤ T) :
    CanonicalLiteralRadiusBound.combined B Cshape Cfourier factor clipping ≤
      CanonicalLiteralRadiusBound.combined 1 Cshape Cfourier factor clipping * T := by
  sorry

theorem fixedCoefficient_le_profilePower
    (B P lo hi : ℝ) (hlo : 0 < lo) (hhi : 1 ≤ hi)
    (δ₁ δ₂ firstSign : ℝ) (s : Finset (ℕ × ℕ)) (d : ℕ)
    (hP : 1 ≤ P) (hbound : B ≤ P ^ d) :
    CanonicalLiteralRadiusBound.fixedCoefficient B lo hi hlo δ₁ δ₂ firstSign s ≤
      CanonicalLiteralRadiusBound.fixedCoefficient 1 lo hi hlo δ₁ δ₂ firstSign s * P ^ d := by
  sorry

theorem twoSignsCoefficient_le_profilePower
    (B P lo hi : ℝ) (hlo : 0 < lo) (hhi : 1 ≤ hi)
    (δ₁ δ₂ : ℝ) (s : Finset (ℕ × ℕ)) (d : ℕ)
    (hP : 1 ≤ P) (hbound : B ≤ P ^ d) :
    CanonicalLiteralActiveRadius.twoSignsCoefficient B lo hi hlo δ₁ δ₂ s ≤
      CanonicalLiteralActiveRadius.twoSignsCoefficient 1 lo hi hlo δ₁ δ₂ s * P ^ d := by
  sorry

theorem one_add_twoSignsCoefficient_le_profilePower
    (B P lo hi : ℝ) (hlo : 0 < lo) (hhi : 1 ≤ hi)
    (δ₁ δ₂ : ℝ) (s : Finset (ℕ × ℕ)) (d : ℕ)
    (hP : 1 ≤ P) (hbound : B ≤ P ^ d) :
    1 + CanonicalLiteralActiveRadius.twoSignsCoefficient B lo hi hlo δ₁ δ₂ s ≤
      (1 + CanonicalLiteralActiveRadius.twoSignsCoefficient 1 lo hi hlo δ₁ δ₂ s) * P ^ d := by
  sorry

/-- This constant is chosen before the original control, all scales
and all actual source labels. The first scalar pair enters only the
original annulus power `cap`. -/
def coefficient (cap : ℕ) (annulus lo hi : ℝ) (hlo : 0 < lo)
    (δ₁ δ₂ : ℝ) (s : Finset (ℕ × ℕ)) : ℝ :=
  (1 + CanonicalLiteralActiveRadius.twoSignsCoefficient 1 lo hi hlo δ₁ δ₂ s) ^
    ((cap + 2) + (cap + 2)) * (max 1 annulus) ^ cap

theorem coefficient_pos (cap : ℕ) (annulus lo hi : ℝ) (hlo : 0 < lo) (hhi : 1 ≤ hi)
    (δ₁ δ₂ : ℝ) (s : Finset (ℕ × ℕ)) :
    0 < coefficient cap annulus lo hi hlo δ₁ δ₂ s := by
  sorry

def degree (cap d dRow dFirstKernel dSecondKernel : ℕ) : ℕ :=
  d * ((cap + 2) + (cap + 2)) + 6 * d * cap + dRow + dFirstKernel + dSecondKernel

/-- The complete literal radius exponent uses both pre-removal
profile counts. Each original first scalar and each original atom
cost is paid with its own already computed multiplicity. -/
theorem radius_atoms_le_profilePower
    (cap d : ℕ) (annulus B P lo hi : ℝ) (hlo : 0 < lo) (hhi : 1 ≤ hi)
    (δ₁ δ₂ : ℝ) (s : Finset (ℕ × ℕ))
    (hannulus : 0 ≤ annulus) (hB : 0 ≤ B) (hP : 1 ≤ P) (hbound : B ≤ P ^ d) :
    (1 + CanonicalLiteralActiveRadius.twoSignsCoefficient B lo hi hlo δ₁ δ₂ s) ^
        ((cap + 2) + (cap + 2)) *
      (atomBudget annulus B ^ cap * slotBudget B ^ (2 * cap)) ≤
      coefficient cap annulus lo hi hlo δ₁ δ₂ s *
        P ^ (d * ((cap + 2) + (cap + 2)) + 6 * d * cap) := by
  sorry

/-- The remaining inputs are the three separate original controls:
the row profile and the two original Fourier seminorms. Their degrees
are fixed before their values are chosen. -/
theorem complete_coefficient_le_profilePower
    (cap d dRow dFirstKernel dSecondKernel : ℕ)
    (annulus B P lo hi : ℝ) (hlo : 0 < lo) (hhi : 1 ≤ hi)
    (δ₁ δ₂ : ℝ) (s : Finset (ℕ × ℕ))
    (row firstKernel secondKernel : ℝ)
    (hannulus : 0 ≤ annulus) (hB : 0 ≤ B) (hP : 1 ≤ P)
    (hbound : B ≤ P ^ d)
    (hrow : 0 ≤ row) (hfirst : 0 ≤ firstKernel) (hsecond : 0 ≤ secondKernel)
    (hrowBound : row ≤ P ^ dRow)
    (hfirstBound : firstKernel ≤ P ^ dFirstKernel)
    (hsecondBound : secondKernel ≤ P ^ dSecondKernel) :
    ((1 + CanonicalLiteralActiveRadius.twoSignsCoefficient B lo hi hlo δ₁ δ₂ s) ^
        ((cap + 2) + (cap + 2)) *
      (atomBudget annulus B ^ cap * slotBudget B ^ (2 * cap))) *
      row * firstKernel * secondKernel ≤
      coefficient cap annulus lo hi hlo δ₁ δ₂ s *
        P ^ degree cap d dRow dFirstKernel dSecondKernel := by
  sorry

end HeckeSkeleton.Moments.EngineStep.CanonicalLiteralMassProfilePower

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralMassProfilePower.separateAtoms_le_profilePower
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralMassProfilePower.radius_atoms_le_profilePower
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralMassProfilePower.complete_coefficient_le_profilePower
