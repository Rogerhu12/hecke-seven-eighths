import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralFirstScalarCost
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralActiveRadius

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

theorem slotBudget_one (B : ℝ) : 1 ≤ slotBudget B := le_max_left _ _

theorem slotBudget_atom (B : ℝ) : B ^ 2 ≤ slotBudget B := le_max_right _ _

/-- The fixed first annulus contributes to the constant only. -/
theorem atomBudget_le_profilePower (annulus B P : ℝ) (d : ℕ)
    (hannulus : 0 ≤ annulus) (hB : 0 ≤ B) (hP : 1 ≤ P)
    (hbound : B ≤ P ^ d) :
    atomBudget annulus B ≤ max 1 annulus * P ^ (2 * d) := by
  have hsquare : B ^ 2 ≤ P ^ (2 * d) := by
    calc
      _ ≤ (P ^ d) ^ 2 := pow_le_pow_left₀ hB hbound 2
      _ = _ := by rw [← pow_mul, Nat.mul_comm d 2]
  have hunit : 1 ≤ max 1 annulus * P ^ (2 * d) := by
    have hpow : 1 ≤ P ^ (2 * d) := one_le_pow₀ hP
    simpa only [one_mul] using mul_le_mul
      (le_max_left (1 : ℝ) annulus) hpow
      zero_le_one (zero_le_one.trans (le_max_left (1 : ℝ) annulus))
  exact max_le hunit (mul_le_mul (le_max_right 1 annulus) hsquare
    (sq_nonneg B) (zero_le_one.trans (le_max_left (1 : ℝ) annulus)))

theorem slotBudget_le_profilePower (B P : ℝ) (d : ℕ)
    (hB : 0 ≤ B) (hP : 1 ≤ P) (hbound : B ≤ P ^ d) :
    slotBudget B ≤ P ^ (2 * d) := by
  apply max_le (one_le_pow₀ hP)
  calc
    _ ≤ (P ^ d) ^ 2 := pow_le_pow_left₀ hB hbound 2
    _ = _ := by rw [← pow_mul, Nat.mul_comm d 2]

/-- The first scalar pair costs `cap` original atom factors. The
second common and allocation costs contribute `2 * cap` more. -/
theorem separateAtoms_le_profilePower (cap d : ℕ) (annulus B P : ℝ)
    (hannulus : 0 ≤ annulus) (hB : 0 ≤ B) (hP : 1 ≤ P)
    (hbound : B ≤ P ^ d) :
    atomBudget annulus B ^ cap * slotBudget B ^ (2 * cap) ≤
      (max 1 annulus) ^ cap * P ^ (6 * d * cap) := by
  have hP0 : 0 ≤ P := zero_le_one.trans hP
  have hfirst := pow_le_pow_left₀
    (zero_le_one.trans (atomBudget_one annulus B))
    (atomBudget_le_profilePower annulus B P d hannulus hB hP hbound) cap
  have hsecond := pow_le_pow_left₀
    (zero_le_one.trans (slotBudget_one B))
    (slotBudget_le_profilePower B P d hB hP hbound) (2 * cap)
  apply (mul_le_mul hfirst hsecond
    (pow_nonneg (zero_le_one.trans (slotBudget_one B)) _)
    (pow_nonneg (mul_nonneg
      (zero_le_one.trans (le_max_left (1 : ℝ) annulus)) (pow_nonneg hP0 _)) _)).trans_eq
  have he : 6 * d * cap = (2 * d) * cap + (2 * d) * (2 * cap) := by ring
  rw [he]
  simp only [mul_pow, pow_add, pow_mul]
  ring

/-- The literal radius coefficient is affine in the original control.
All other factors remain fixed before that control is evaluated. -/
theorem combined_le_scale (B Cshape Cfourier factor clipping T : ℝ)
    (hshape : 0 ≤ Cshape) (hfourier : 0 ≤ Cfourier)
    (hfactor : 0 ≤ factor) (hclipping : 0 ≤ clipping)
    (hT : 1 ≤ T) (hBT : B ≤ T) :
    CanonicalLiteralRadiusBound.combined B Cshape Cfourier factor clipping ≤
      CanonicalLiteralRadiusBound.combined 1 Cshape Cfourier factor clipping * T := by
  let D := (1 + Cshape * (1 + factor)) * (1 + Cfourier)
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hinner : 1 + B * D ≤ T + T * D :=
    add_le_add hT (mul_le_mul_of_nonneg_right hBT hD)
  calc
    _ = clipping * (1 + B * D) := by
      dsimp only [CanonicalLiteralRadiusBound.combined, D]
      ring
    _ ≤ clipping * (T + T * D) := mul_le_mul_of_nonneg_left hinner hclipping
    _ = _ := by
      dsimp only [CanonicalLiteralRadiusBound.combined, D]
      ring

theorem fixedCoefficient_le_profilePower
    (B P lo hi : ℝ) (hlo : 0 < lo) (hhi : 1 ≤ hi)
    (δ₁ δ₂ firstSign : ℝ) (s : Finset (ℕ × ℕ)) (d : ℕ)
    (hP : 1 ≤ P) (hbound : B ≤ P ^ d) :
    CanonicalLiteralRadiusBound.fixedCoefficient B lo hi hlo δ₁ δ₂ firstSign s ≤
      CanonicalLiteralRadiusBound.fixedCoefficient 1 lo hi hlo δ₁ δ₂ firstSign s * P ^ d := by
  have hclip : 0 ≤ 1 + 2 * CanonicalLogProfiles.clippingCoefficient hi s := by
    have hc := CanonicalLogProfiles.clippingCoefficient_one_le hi hhi s
    linarith
  exact combined_le_scale B _ _ _ _ _
    (CanonicalLogProfiles.shapeCoefficient_nonneg _ _ _ _ _)
    (CanonicalLiteralFourierWindows.coefficient_nonneg _ _ _ _ _)
    (Real.sqrt_nonneg _) hclip (one_le_pow₀ hP) hbound

theorem twoSignsCoefficient_le_profilePower
    (B P lo hi : ℝ) (hlo : 0 < lo) (hhi : 1 ≤ hi)
    (δ₁ δ₂ : ℝ) (s : Finset (ℕ × ℕ)) (d : ℕ)
    (hP : 1 ≤ P) (hbound : B ≤ P ^ d) :
    CanonicalLiteralActiveRadius.twoSignsCoefficient B lo hi hlo δ₁ δ₂ s ≤
      CanonicalLiteralActiveRadius.twoSignsCoefficient 1 lo hi hlo δ₁ δ₂ s * P ^ d := by
  have hP0 : 0 ≤ P ^ d := pow_nonneg (zero_le_one.trans hP) _
  apply max_le
  · exact (fixedCoefficient_le_profilePower B P lo hi hlo hhi δ₁ δ₂ 1 s d hP hbound).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hP0)
  · exact (fixedCoefficient_le_profilePower B P lo hi hlo hhi δ₁ δ₂ (-1) s d hP hbound).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hP0)

theorem one_add_twoSignsCoefficient_le_profilePower
    (B P lo hi : ℝ) (hlo : 0 < lo) (hhi : 1 ≤ hi)
    (δ₁ δ₂ : ℝ) (s : Finset (ℕ × ℕ)) (d : ℕ)
    (hP : 1 ≤ P) (hbound : B ≤ P ^ d) :
    1 + CanonicalLiteralActiveRadius.twoSignsCoefficient B lo hi hlo δ₁ δ₂ s ≤
      (1 + CanonicalLiteralActiveRadius.twoSignsCoefficient 1 lo hi hlo δ₁ δ₂ s) * P ^ d := by
  exact (add_le_add (one_le_pow₀ hP)
    (twoSignsCoefficient_le_profilePower B P lo hi hlo hhi δ₁ δ₂ s d hP hbound))
      .trans_eq (by ring)

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
  have hc := CanonicalLiteralActiveRadius.twoSignsCoefficient_nonneg
    1 lo hi zero_le_one hlo hhi δ₁ δ₂ s
  have ha : 0 < max 1 annulus := zero_lt_one.trans_le (le_max_left _ _)
  unfold coefficient
  positivity

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
  have hP0 : 0 ≤ P := zero_le_one.trans hP
  have hc := CanonicalLiteralActiveRadius.twoSignsCoefficient_nonneg
    B lo hi hB hlo hhi δ₁ δ₂ s
  have hc₁ := CanonicalLiteralActiveRadius.twoSignsCoefficient_nonneg
    1 lo hi zero_le_one hlo hhi δ₁ δ₂ s
  have hrad := pow_le_pow_left₀ (by linarith :
    0 ≤ 1 + CanonicalLiteralActiveRadius.twoSignsCoefficient B lo hi hlo δ₁ δ₂ s)
    (one_add_twoSignsCoefficient_le_profilePower B P lo hi hlo hhi δ₁ δ₂ s d hP hbound)
    ((cap + 2) + (cap + 2))
  have hatoms := separateAtoms_le_profilePower cap d annulus B P hannulus hB hP hbound
  apply (mul_le_mul hrad hatoms
    (mul_nonneg (pow_nonneg (zero_le_one.trans (atomBudget_one annulus B)) _)
      (pow_nonneg (zero_le_one.trans (slotBudget_one B)) _))
    (pow_nonneg (mul_nonneg (by linarith) (pow_nonneg hP0 _)) _)).trans_eq
  simp only [coefficient, pow_add, mul_pow, pow_mul]
  ring

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
  have hP0 : 0 ≤ P := zero_le_one.trans hP
  have hC : 0 ≤ coefficient cap annulus lo hi hlo δ₁ δ₂ s :=
    (coefficient_pos cap annulus lo hi hlo hhi δ₁ δ₂ s).le
  have hrad := radius_atoms_le_profilePower cap d annulus B P lo hi hlo hhi
    δ₁ δ₂ s hannulus hB hP hbound
  have h₁ := mul_le_mul hrad hrowBound hrow (mul_nonneg hC (pow_nonneg hP0 _))
  have h₂ := mul_le_mul h₁ hfirstBound hfirst
    (mul_nonneg (mul_nonneg hC (pow_nonneg hP0 _)) (pow_nonneg hP0 _))
  have h₃ := mul_le_mul h₂ hsecondBound hsecond
    (mul_nonneg (mul_nonneg (mul_nonneg hC (pow_nonneg hP0 _))
      (pow_nonneg hP0 _)) (pow_nonneg hP0 _))
  exact h₃.trans_eq (by simp only [degree, pow_add]; ring)

end HeckeSkeleton.Moments.EngineStep.CanonicalLiteralMassProfilePower

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralMassProfilePower.separateAtoms_le_profilePower
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralMassProfilePower.radius_atoms_le_profilePower
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralMassProfilePower.complete_coefficient_le_profilePower
