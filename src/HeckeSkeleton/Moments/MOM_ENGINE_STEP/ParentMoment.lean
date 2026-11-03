import HeckeGeneral.Analysis.MomentInputs
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.Pool

/-!
# The actual centered and uncentered parent energies

The stage bit is independent of the number of live slots.  A centered
parent retains both complete rectangles, the same actual row character,
the same common mask and every slot inside one squared norm.  The
comparison rectangle changes only the two plain scales.

These definitions expose the actual parent which the two orbital
transforms must reduce; they do not assume a parent recurrence.  The
comparison inequality below is proved row by row before any transform.
-/

noncomputable section
open scoped Classical BigOperators

namespace HeckeSkeleton.Moments.EngineStep

open NumberField HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments

variable {K : Type} [Field K] [NumberField K]
variable {ω ψ : HeckeCharacter K}

/-- Both formal rectangles share the original profiles, mask and slot product. -/
def pairedStagePolynomial (centered : Bool) (d : MomentData K ω ψ)
    (u : NonzeroIdeal K) (X₁ X₂ Y₁ Y₂ Z t : ℝ) : ℂ :=
  (plainPolynomial d d.plainTest₁ u X₁ t * plainPolynomial d d.plainTest₂ u X₂ t -
    if centered then
      plainPolynomial d d.plainTest₁ u Y₁ t * plainPolynomial d d.plainTest₂ u Y₂ t
    else 0) * slotProduct d u Z t

/-- The parent is an actual finite moment on the original exceptional-row exclusion. -/
def pairedStageEnergy (centered : Bool) (d : MomentData K ω ψ) (a : RealParameters)
    (Z t Y₁ Y₂ : ℝ) : ℝ :=
  ∑ u ∈ pairedRows d a Z,
    ‖pairedStagePolynomial centered d u (Z ^ a.n₁) (Z ^ a.n₂) Y₁ Y₂ Z t‖ ^ 2

theorem pairedStageEnergy_nonneg (centered : Bool) (d : MomentData K ω ψ)
    (a : RealParameters) (Z t Y₁ Y₂ : ℝ) :
    0 ≤ pairedStageEnergy centered d a Z t Y₁ Y₂ :=
  Finset.sum_nonneg (fun u hu => sq_nonneg _)

theorem pairedStageEnergy_uncentered (d : MomentData K ω ψ)
    (a : RealParameters) (Z t Y₁ Y₂ : ℝ) :
    pairedStageEnergy false d a Z t Y₁ Y₂ = pairedEnergy d a Z t := by
  simp only [pairedStageEnergy, pairedStagePolynomial, Bool.false_eq_true, ite_false,
    sub_zero, pairedEnergy]

theorem pairedStagePolynomial_centered (d : MomentData K ω ψ)
    (u : NonzeroIdeal K) (X₁ X₂ Y₁ Y₂ Z t : ℝ) :
    pairedStagePolynomial true d u X₁ X₂ Y₁ Y₂ Z t =
      pairedStagePolynomial false d u X₁ X₂ Y₁ Y₂ Z t -
        pairedStagePolynomial false d u Y₁ Y₂ X₁ X₂ Z t := by
  simp only [pairedStagePolynomial, Bool.false_eq_true, ite_false, ite_true, sub_zero]
  ring

/-- The comparison changes neither row width nor the live slots. -/
def comparisonParameters (a : RealParameters) (L : ℝ) : RealParameters :=
  { a with n₁ := L, n₂ := a.n₁ + a.n₂ - L }

theorem comparisonParameters_width (a : RealParameters) (L : ℝ) :
    (comparisonParameters a L).m + (comparisonParameters a L).q = a.m + a.q := rfl

theorem comparisonParameters_scales (a : RealParameters) (L Z : ℝ) (hZ : 0 < Z) :
    Z ^ (comparisonParameters a L).n₁ * Z ^ (comparisonParameters a L).n₂ =
      Z ^ a.n₁ * Z ^ a.n₂ := by
  rw [← Real.rpow_add hZ, ← Real.rpow_add hZ]
  congr 1
  dsimp only [comparisonParameters]
  ring

theorem pairedRows_comparison (d : MomentData K ω ψ) (a : RealParameters) (L Z : ℝ) :
    pairedRows d (comparisonParameters a L) Z = pairedRows d a Z := rfl

theorem norm_sq_le_two_centered_comparison (x y : ℂ) :
    ‖x‖ ^ 2 ≤ 2 * ‖x - y‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have hn : ‖x‖ ≤ ‖x - y‖ + ‖y‖ := norm_le_norm_sub_add x y
  have hs := (sq_le_sq₀ (norm_nonneg x) (by positivity)).mpr hn
  nlinarith [sq_nonneg (‖x - y‖ - ‖y‖)]

/-- The genuine comparison call plus the whole centered parent, uniformly
for zero and positive slot counts.  No row, profile or mask is replaced. -/
theorem paired_energy_comparison (d : MomentData K ω ψ)
    (a : RealParameters) (L Z t : ℝ) :
    pairedEnergy d a Z t ≤
      2 * pairedStageEnergy true d a Z t (Z ^ L) (Z ^ (a.n₁ + a.n₂ - L)) +
        2 * pairedEnergy d (comparisonParameters a L) Z t := by
  rw [pairedEnergy, pairedStageEnergy, pairedEnergy, pairedRows_comparison,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro u hu
  have hb := norm_sq_le_two_centered_comparison
    (plainPolynomial d d.plainTest₁ u (Z ^ a.n₁) t *
      plainPolynomial d d.plainTest₂ u (Z ^ a.n₂) t * slotProduct d u Z t)
    (plainPolynomial d d.plainTest₁ u (Z ^ L) t *
      plainPolynomial d d.plainTest₂ u (Z ^ (a.n₁ + a.n₂ - L)) t * slotProduct d u Z t)
  simpa only [pairedStagePolynomial, ite_true, sub_mul, comparisonParameters] using hb

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.paired_energy_comparison
