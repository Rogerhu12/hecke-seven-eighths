import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalExceptionalSavingCalibration
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OrdinaryActualExceptionalBudget

/-!
# Original numerical inputs for the ordinary exceptional terminal

The ordinary range comes from the original parent domain. The common
and removed lengths are logarithms of the actual original ideals, so
their nonnegativity is proved internally. The ordinary absolute-volume
estimate has no centered positive-part loss, minimum or height order.
Only the original support and allocation mesh errors remain to be
absorbed before the actual arithmetic index sum.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckePort.Moments

namespace ExceptionalOriginalNumbers

/-- The ordinary scalar exponent is derived from the separate original
errors. No estimate for an exceptional integral is an input. -/
theorem ordinary_remainder_from_windows (n : ExceptionalOriginalNumbers)
    (step loss movingLength : ℝ) (hloss : 0 ≤ loss)
    (hremaining : n.remaining ≤ movingLength + loss / 16)
    (hwidth : n.widthError ≤ loss / 16)
    (hstep : n.stepσ ≤ step) (hsupport : n.δ ≤ loss / 16)
    (hslot : n.slotError ≤ loss / 16) :
    n.remaining + n.widthError + (3 * n.stepσ + 5 * n.δ / 6 + n.slotError) ≤
      (3 * step + loss / 2) + movingLength := by
  linarith

end ExceptionalOriginalNumbers

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable [IsPrincipalIdealRing A.R]
variable {H ι : Type*} [Fintype ι] [DecidableEq ι]
variable {R : ActualSecondCorrelationRows A σ H ι}
variable {C : A.GeneralArithmeticContext σ η hS} {kLeft kRight : ℕ}
variable {a : RealParameters} {Z step : ℝ}

namespace OriginalNominalGeometry

variable (G : OriginalNominalGeometry (K := K) a Z step)
variable (W : ActualSecondRowMass R C kLeft kRight)
variable (vStar r₁ r₂ slotError firstProfile : ℝ)

/-- The original domain supplies the ordinary range for the computed
label; the numerical label cannot independently choose its total. -/
theorem exceptionalNumbers_ordinary_range
    {ω ψ : HeckeCharacter K} {d : MomentData K ω ψ}
    {Y₁ Y₂ floor padding : ℝ}
    (domain : PairedEngineDomain false d a Z Y₁ Y₂ floor padding) :
    (G.exceptionalNumbers W vStar r₁ r₂ slotError firstProfile).Aexp ≤
      5 * (a.m + a.q) / 6 :=
  domain.ordinary rfl

theorem exceptionalNumbers_common_nonneg (hZ : 1 < Z) :
    let n := G.exceptionalNumbers W vStar r₁ r₂ slotError firstProfile
    0 ≤ n.c ∧ 0 ≤ n.w ∧ 0 ≤ n.b₂ := by
  refine ⟨idealLogLength_nonneg Z hZ G.ideals.first.val
    (nonZeroDivisors.coe_ne_zero G.ideals.first), G.tag.removedLength_nonneg Z hZ, ?_⟩
  change 0 ≤ (idealLogLength Z W.leftIdeal + idealLogLength Z W.rightIdeal) / 2
  exact div_nonneg
    (add_nonneg
      (idealLogLength_nonneg Z hZ W.leftIdeal
        (primePowerProduct R.primes R.leftMultiplicity).property.1)
      (idealLogLength_nonneg Z hZ W.rightIdeal
        (primePowerProduct R.primes R.rightMultiplicity).property.1)) (by norm_num)

/-- The computed first allowance cancels internally. The same original
tag moving length will subsequently cancel its literal pool weight. -/
theorem exceptionalNumbers_ordinary_remainder
    (loss : ℝ) (hloss : 0 ≤ loss)
    (hsupport : G.supportError ≤ loss / 16) (hslot : slotError ≤ loss / 16) :
    let n := G.exceptionalNumbers W vStar r₁ r₂ slotError firstProfile
    n.remaining + n.widthError + (3 * n.stepσ + 5 * n.δ / 6 + n.slotError) ≤
      (3 * step + loss / 2) + G.tag.exceptionalMovingLength Z step := by
  dsimp only [exceptionalNumbers]
  linarith

/-- The actual normalizer is read from the original source, before
constructing any child. Its true total identity transfers the ordinary
range and common lengths to that same normalization. -/
theorem exceptionalNumbersAtNormalization_ordinary_inputs
    (normalization total : ℝ) (hZ : 1 < Z)
    {ω ψ : HeckeCharacter K} {d : MomentData K ω ψ}
    {Y₁ Y₂ floor padding : ℝ}
    (domain : PairedEngineDomain false d a Z Y₁ Y₂ floor padding) :
    let n := G.exceptionalNumbersAtNormalization W vStar r₁ r₂ slotError firstProfile
      normalization total
    n.Aexp ≤ 5 * (a.m + a.q) / 6 ∧ 0 ≤ n.c ∧ 0 ≤ n.w ∧ 0 ≤ n.b₂ := by
  exact ⟨G.exceptionalNumbers_ordinary_range W vStar r₁ r₂ slotError firstProfile domain,
    G.exceptionalNumbers_common_nonneg W vStar r₁ r₂ slotError firstProfile hZ⟩

/-- This fills the ordinary final numerical field using only the
original normalization recipe, total identity and individual errors. -/
theorem exceptionalNumbersAtNormalization_ordinary_remainder
    (normalization total : ℝ) (hZ : 1 < Z)
    (hN : normalization = firstLeftAllowance Z total G.ideals.first.val G.ideals.opposite.val)
    (htotal : total = G.skeleton.A + (G.skeleton.q + G.skeleton.R + G.skeleton.E))
    (loss : ℝ) (hloss : 0 ≤ loss)
    (hsupport : G.supportError ≤ loss / 16) (hslot : slotError ≤ loss / 16) :
    let n := G.exceptionalNumbersAtNormalization W vStar r₁ r₂ slotError firstProfile
      normalization total
    n.remaining + n.widthError + (3 * n.stepσ + 5 * n.δ / 6 + n.slotError) ≤
      (3 * step + loss / 2) + G.tag.exceptionalMovingLength Z step := by
  rw [G.exceptionalNumbersAtNormalization_eq W vStar r₁ r₂ slotError firstProfile
    normalization total hZ hN htotal]
  exact G.exceptionalNumbers_ordinary_remainder W vStar r₁ r₂ slotError firstProfile
    loss hloss hsupport hslot

end OriginalNominalGeometry

/-- Ordinary and centered bounds can use the same earlier profile
power; the ordinary proof itself uses one fewer factor. -/
theorem ordinaryExceptionalBudgetProfileDegree_le (cap degree : ℕ) :
    ordinaryExceptionalBudgetProfileDegree cap degree ≤ exceptionalBudgetProfileDegree cap degree := by
  unfold ordinaryExceptionalBudgetProfileDegree exceptionalBudgetProfileDegree
  exact Nat.mul_le_mul_left degree (by omega)

theorem ordinaryExceptionalBudgetProfilePower_le (cap degree : ℕ) (P : ℝ) (hP : 1 ≤ P) :
    P ^ ordinaryExceptionalBudgetProfileDegree cap degree ≤ P ^ exceptionalBudgetProfileDegree cap degree :=
  pow_le_pow_right₀ hP (ordinaryExceptionalBudgetProfileDegree_le cap degree)

/-- The actual ordinary index sum spends the reserved half loss. -/
theorem original_ordinary_exceptional_global_exponent
    (step loss δ₁ δ₂ δ₃ poolLoss mesh : ℝ) (hloss : 0 ≤ loss)
    (h₁ : δ₁ ≤ loss / 16) (h₂ : δ₂ ≤ loss / 16) (h₃ : δ₃ ≤ loss / 16)
    (hpool : poolLoss ≤ loss / 16) (hmesh : mesh ≤ loss / 16) :
    (3 * step + loss / 2) + δ₁ + δ₂ + δ₃ + poolLoss + mesh ≤ 3 * step + loss := by
  linarith

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ExceptionalOriginalNumbers.ordinary_remainder_from_windows
#print axioms HeckeSkeleton.Moments.EngineStep.OriginalNominalGeometry.exceptionalNumbers_ordinary_range
#print axioms HeckeSkeleton.Moments.EngineStep.OriginalNominalGeometry.exceptionalNumbers_common_nonneg
#print axioms HeckeSkeleton.Moments.EngineStep.OriginalNominalGeometry.exceptionalNumbersAtNormalization_ordinary_remainder
#print axioms HeckeSkeleton.Moments.EngineStep.ordinaryExceptionalBudgetProfilePower_le
#print axioms HeckeSkeleton.Moments.EngineStep.original_ordinary_exceptional_global_exponent
