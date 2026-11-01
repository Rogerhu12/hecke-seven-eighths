import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalPrimitiveEngineChoices
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstDualOriginalExponent

/-!
# A single original amplitude and height control

The public primitive window has one amplitude. Multiplying it by
`1 + |t|` pays the original height and every fixed polynomial profile
degree. These numerical estimates are used after the actual source
bounds have been proved; they introduce no source or descendant input.
-/

noncomputable section

namespace HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEngineControl

def value (amplitude t : ℝ) : ℝ := amplitude * (1 + |t|)

theorem height_le (amplitude t : ℝ) (hamplitude : 1 ≤ amplitude) :
    1 + |t| ≤ value amplitude t := by
  simpa only [one_mul, value] using
    mul_le_mul_of_nonneg_right hamplitude (by positivity : (0 : ℝ) ≤ 1 + |t|)

theorem amplitude_le (amplitude t : ℝ) (hamplitude : 1 ≤ amplitude) :
    amplitude ≤ value amplitude t := by
  have ht : (1 : ℝ) ≤ 1 + |t| := by linarith [abs_nonneg t]
  simpa only [mul_one, value] using
    mul_le_mul_of_nonneg_left ht (zero_le_one.trans hamplitude)

theorem one_le (amplitude t : ℝ) (hamplitude : 1 ≤ amplitude) :
    1 ≤ value amplitude t := hamplitude.trans (amplitude_le amplitude t hamplitude)

theorem profile_height_power (amplitude t : ℝ) (hamplitude : 1 ≤ amplitude)
    (profileDegree heightDegree : ℕ) :
    amplitude ^ profileDegree * (1 + |t|) ^ heightDegree ≤
      value amplitude t ^ (profileDegree + heightDegree) := by
  rw [pow_add]
  exact mul_le_mul
    (pow_le_pow_left₀ (zero_le_one.trans hamplitude)
      (amplitude_le amplitude t hamplitude) profileDegree)
    (pow_le_pow_left₀ (by positivity) (height_le amplitude t hamplitude) heightDegree)
    (by positivity)
    (pow_nonneg (zero_le_one.trans (one_le amplitude t hamplitude)) _)

/-- Every fixed smaller monomial is bounded by the common final
constant, degree and exponent. The scale need only be at least one. -/
theorem monomial_mono {c C control Z e E : ℝ} {d D : ℕ}
    (hC : 0 ≤ C) (hc : c ≤ C) (hcontrol : 1 ≤ control) (hZ : 1 ≤ Z)
    (hdegree : d ≤ D) (hexponent : e ≤ E) :
    c * control ^ d * Z ^ e ≤ C * control ^ D * Z ^ E := by
  apply mul_le_mul
    (mul_le_mul hc (pow_le_pow_right₀ hcontrol hdegree)
      (pow_nonneg (zero_le_one.trans hcontrol) _) hC)
    (Real.rpow_le_rpow_of_exponent_le hZ hexponent)
    (Real.rpow_nonneg (zero_le_one.trans hZ) _)
    (mul_nonneg hC (pow_nonneg (zero_le_one.trans hcontrol) _))

/-- The original four terminal coefficients add before a single
power of the original control is factored out. -/
theorem four_terms {x₁ x₂ x₃ x₄ C₁ C₂ C₃ C₄ control Z exponent : ℝ} {degree : ℕ}
    (h₁ : x₁ ≤ C₁ * control ^ degree * Z ^ exponent)
    (h₂ : x₂ ≤ C₂ * control ^ degree * Z ^ exponent)
    (h₃ : x₃ ≤ C₃ * control ^ degree * Z ^ exponent)
    (h₄ : x₄ ≤ C₄ * control ^ degree * Z ^ exponent) :
    x₁ + x₂ + x₃ + x₄ ≤
      (C₁ + C₂ + C₃ + C₄) * control ^ degree * Z ^ exponent := by
  calc
    _ ≤ C₁ * control ^ degree * Z ^ exponent + C₂ * control ^ degree * Z ^ exponent +
        C₃ * control ^ degree * Z ^ exponent + C₄ * control ^ degree * Z ^ exponent :=
      add_le_add (add_le_add (add_le_add h₁ h₂) h₃) h₄
    _ = _ := by ring

end HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEngineControl

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEngineControl.profile_height_power
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEngineControl.monomial_mono
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEngineControl.four_terms
