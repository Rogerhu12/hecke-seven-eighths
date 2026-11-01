import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalProfilePowerControl

/-!
# Fixed original-profile powers for the actual terminal coefficients

The first allowance, original first Fourier kernel, original coefficient
atoms and residual pair profile each enter the second terminal bound
once.  Their four natural degrees and the original slot cap are selected
before the moving profile control.  The product below is the literal
profile factor in both the direct and amplified source terminal bounds.

The comparison uses the original cap, with no maximum over moving labels
or descendants.  The common control degree can then be enlarged once for
all four terminals and the ordinary kernel, after their separate source
estimates have been proved.
-/

noncomputable section

namespace HeckeSkeleton.Moments.EngineStep

/-- Every original atom is charged once, including a frozen slot. -/
def originalTerminalProfileDegree (cap dFirst dKernel dAtom dResidual : ℕ) : ℕ :=
  dFirst + dKernel + dAtom * cap + dResidual

/-- The profile factor is exactly the one appearing in
`actual_second_zero_from_original_windows` and its three direct/tail
counterparts.  All assumptions concern individual original controls. -/
theorem original_terminal_profile_product_le
    (cap dFirst dKernel dAtom dResidual : ℕ)
    (P firstAmplitude kernelBound atomBound residualConstant : ℝ)
    (hP : 1 ≤ P)
    (hfirst : 0 ≤ firstAmplitude) (hkernel : 0 ≤ kernelBound)
    (hatom : 0 ≤ atomBound) (hresidual : 0 ≤ residualConstant)
    (hfirstPower : firstAmplitude ≤ P ^ dFirst)
    (hkernelPower : kernelBound ≤ P ^ dKernel)
    (hatomPower : atomBound ≤ P ^ dAtom)
    (hresidualPower : residualConstant ≤ P ^ dResidual) :
    firstAmplitude * kernelBound * atomBound ^ cap * residualConstant ≤
      P ^ originalTerminalProfileDegree cap dFirst dKernel dAtom dResidual := by
  have hP0 : 0 ≤ P := zero_le_one.trans hP
  have hatoms := pow_le_pow_left₀ hatom hatomPower cap
  have hpair := mul_le_mul hfirstPower hkernelPower hkernel (pow_nonneg hP0 _)
  have hthree := mul_le_mul hpair hatoms (pow_nonneg hatom _)
    (mul_nonneg (pow_nonneg hP0 _) (pow_nonneg hP0 _))
  have hall := mul_le_mul hthree hresidualPower hresidual
    (mul_nonneg (mul_nonneg (pow_nonneg hP0 _) (pow_nonneg hP0 _))
      (pow_nonneg (pow_nonneg hP0 _) _))
  apply hall.trans_eq
  simp only [originalTerminalProfileDegree, pow_add, pow_mul]

/-- The fixed original cap pays any smaller actual original slot count.
This comparison never refers to the number of retained child slots. -/
theorem original_terminal_profile_product_le_cap
    (slots cap dFirst dKernel dAtom dResidual : ℕ) (hslots : slots ≤ cap)
    (P firstAmplitude kernelBound atomBound residualConstant : ℝ)
    (hP : 1 ≤ P)
    (hfirst : 0 ≤ firstAmplitude) (hkernel : 0 ≤ kernelBound)
    (hatom : 1 ≤ atomBound) (hresidual : 0 ≤ residualConstant)
    (hfirstPower : firstAmplitude ≤ P ^ dFirst)
    (hkernelPower : kernelBound ≤ P ^ dKernel)
    (hatomPower : atomBound ≤ P ^ dAtom)
    (hresidualPower : residualConstant ≤ P ^ dResidual) :
    firstAmplitude * kernelBound * atomBound ^ slots * residualConstant ≤
      P ^ originalTerminalProfileDegree cap dFirst dKernel dAtom dResidual := by
  apply le_trans _ (original_terminal_profile_product_le
    cap dFirst dKernel dAtom dResidual P firstAmplitude kernelBound atomBound
    residualConstant hP hfirst hkernel (zero_le_one.trans hatom) hresidual
    hfirstPower hkernelPower hatomPower hresidualPower)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hatom hslots)
      (mul_nonneg hfirst hkernel)) hresidual

/-- Enlarging a degree uses the same original control, whose value is
at least one.  The constant and degree stay independent of moving data. -/
theorem original_profile_power_enlarge
    (degree degreeMax : ℕ) (hdegree : degree ≤ degreeMax)
    (P C : ℝ) (hP : 1 ≤ P) (hC : 0 ≤ C) :
    C * P ^ degree ≤ C * P ^ degreeMax :=
  mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hP hdegree) hC

/-- Uniform coefficients already obtained from the four literal
terminal source estimates can use one earlier chosen profile degree.
This is only their numerical addition; no terminal estimate is part of
an original source record. -/
theorem original_four_profile_coefficients_le
    (d₁ d₂ d₃ d₄ degree : ℕ)
    (h₁ : d₁ ≤ degree) (h₂ : d₂ ≤ degree)
    (h₃ : d₃ ≤ degree) (h₄ : d₄ ≤ degree)
    (P C₁ C₂ C₃ C₄ : ℝ) (hP : 1 ≤ P)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hC₃ : 0 ≤ C₃) (hC₄ : 0 ≤ C₄) :
    C₁ * P ^ d₁ + C₂ * P ^ d₂ + C₃ * P ^ d₃ + C₄ * P ^ d₄ ≤
      (C₁ + C₂ + C₃ + C₄) * P ^ degree := by
  calc
    _ ≤ C₁ * P ^ degree + C₂ * P ^ degree + C₃ * P ^ degree + C₄ * P ^ degree :=
      add_le_add (add_le_add (add_le_add
        (original_profile_power_enlarge d₁ degree h₁ P C₁ hP hC₁)
        (original_profile_power_enlarge d₂ degree h₂ P C₂ hP hC₂))
        (original_profile_power_enlarge d₃ degree h₃ P C₃ hP hC₃))
        (original_profile_power_enlarge d₄ degree h₄ P C₄ hP hC₄)
    _ = _ := by ring

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.original_terminal_profile_product_le
#print axioms HeckeSkeleton.Moments.EngineStep.original_terminal_profile_product_le_cap
#print axioms HeckeSkeleton.Moments.EngineStep.original_four_profile_coefficients_le
