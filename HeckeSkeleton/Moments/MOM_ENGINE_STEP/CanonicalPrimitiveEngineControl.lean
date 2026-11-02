import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalPrimitiveEngineChoices
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstDualOriginalExponent

set_option linter.unusedSectionVars false

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
  sorry

theorem amplitude_le (amplitude t : ℝ) (hamplitude : 1 ≤ amplitude) :
    amplitude ≤ value amplitude t := by
  sorry

theorem one_le (amplitude t : ℝ) (hamplitude : 1 ≤ amplitude) :
    1 ≤ value amplitude t := by
  sorry

theorem profile_height_power (amplitude t : ℝ) (hamplitude : 1 ≤ amplitude)
    (profileDegree heightDegree : ℕ) :
    amplitude ^ profileDegree * (1 + |t|) ^ heightDegree ≤
      value amplitude t ^ (profileDegree + heightDegree) := by
  sorry

/-- Every fixed smaller monomial is bounded by the common final
constant, degree and exponent. The scale need only be at least one. -/
theorem monomial_mono {c C control Z e E : ℝ} {d D : ℕ}
    (hC : 0 ≤ C) (hc : c ≤ C) (hcontrol : 1 ≤ control) (hZ : 1 ≤ Z)
    (hdegree : d ≤ D) (hexponent : e ≤ E) :
    c * control ^ d * Z ^ e ≤ C * control ^ D * Z ^ E := by
  sorry

/-- The original four terminal coefficients add before a single
power of the original control is factored out. -/
theorem four_terms {x₁ x₂ x₃ x₄ C₁ C₂ C₃ C₄ control Z exponent : ℝ} {degree : ℕ}
    (h₁ : x₁ ≤ C₁ * control ^ degree * Z ^ exponent)
    (h₂ : x₂ ≤ C₂ * control ^ degree * Z ^ exponent)
    (h₃ : x₃ ≤ C₃ * control ^ degree * Z ^ exponent)
    (h₄ : x₄ ≤ C₄ * control ^ degree * Z ^ exponent) :
    x₁ + x₂ + x₃ + x₄ ≤
      (C₁ + C₂ + C₃ + C₄) * control ^ degree * Z ^ exponent := by
  sorry

end HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEngineControl

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEngineControl.profile_height_power
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEngineControl.monomial_mono
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalPrimitiveEngineControl.four_terms
