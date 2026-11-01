import HeckeSkeleton.Moments.MOM_ENGINE_STEP.JointRowBudget
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.RemainingMaskRadical

/-!
# Joint budgets already satisfied by the actual original rows

When the original allowed-row predicate already contains the complete
joint norm budget, its finite enumeration survives the existing joint
filter exactly. The effective moving mask below is calculated from the
same complete recipe, including the remaining deletion. Its original
source-row bound follows by restoring the actual extraction factor.

These identities keep the moment data and calibration themselves, not
only their energies or numerical upper bounds. No child is selected in
this module.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {ω ψ : HeckeCharacter K}

/-- An exhaustive original row enumeration is unchanged when every
allowed row already satisfies the same joint budget. -/
theorem jointRowBudgetData_eq_self (d : MomentData K ω ψ)
    (support : HeckeGeneral.Analysis.NonzeroIdeal K → A.Exterior)
    (budget : ℝ)
    (hbudget : ∀ u, d.allowedRow u →
      idealNorm K u * A.exteriorNorm (support u) ≤ budget) :
    jointRowBudgetData d support budget = d := by
  have hallowed : (fun u => d.allowedRow u ∧
      idealNorm K u * A.exteriorNorm (support u) ≤ budget) = d.allowedRow := by
    funext u
    exact propext ⟨And.left, fun hu => ⟨hu, hbudget u hu⟩⟩
  have hrows : (fun bound => (d.rows bound).filter (fun u =>
      idealNorm K u * A.exteriorNorm (support u) ≤ budget)) = d.rows := by
    funext bound
    apply Finset.filter_eq_self.mpr
    intro u hu
    exact hbudget u ((d.rows_spec bound u).mp hu).1
  simp only [jointRowBudgetData, hallowed, hrows]

namespace CompleteMovingRowRecipe

variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable {X : Type*} {data : X → MomentData K ω ψ}
variable (Q : CompleteMovingRowRecipe A P R data)

/-- The complete original budget supplies the exact effective deletion
mask, so no further original moment row is removed. -/
theorem effectiveJointRowBudgetData_eq_self (Z width : ℝ)
    (hfull : Q.FullJointBudget Z width) (ξ : X) :
    jointRowBudgetData (data ξ) Q.effectiveMovingMaskRecipe.support (Z ^ width) =
      data ξ :=
  jointRowBudgetData_eq_self (data ξ) Q.effectiveMovingMaskRecipe.support (Z ^ width)
    (Q.effectiveMovingMaskRecipe_jointBudget Z width hfull ξ)

end CompleteMovingRowRecipe

namespace ActualAllocatedSource.Calibration

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {k : ℕ}
variable {source : ActualAllocatedSource A V H k}
variable (D : source.Calibration (σ := σ) ω ψ)

/-- Replacing the already satisfied row predicate preserves the entire
calibration. All its other computational fields were kept by the
existing restriction constructor. -/
theorem withJointRowBudget_eq_self (M : ActualMovingMaskRecipe A D.data)
    (hsource : ∀ h ∈ source.rows,
      A.exteriorNorm (source.originalIdeal h) *
        A.exteriorNorm (M.support (source.row h).momentIdeal) ≤
          source.normFactor h * source.base ^ (D.parameters.m + D.parameters.q))
    (hbudget : ∀ ξ u, (D.data ξ).allowedRow u →
      idealNorm K u * A.exteriorNorm (M.support u) ≤
        source.base ^ (D.parameters.m + D.parameters.q)) :
    D.withJointRowBudget M hsource = D := by
  have hdata : (fun ξ => jointRowBudgetData (D.data ξ) M.support
      (source.base ^ (D.parameters.m + D.parameters.q))) = D.data := by
    funext ξ
    exact jointRowBudgetData_eq_self (D.data ξ) M.support _ (hbudget ξ)
  simp only [withJointRowBudget, hdata]

variable {P : ProbeData K (A.Sf : Set (HeightOneSpectrum (𝓞 K)))}
variable {R : RowCharacterInput K (A.Sf : Set (HeightOneSpectrum (𝓞 K))) P}
variable (Q : CompleteMovingRowRecipe A P R D.data)

/-- Restore the genuine extracted norm factor to the full joint budget
of the same original allowed row. The complete effective deletion
mask is used on both sides of this exact factorization. -/
theorem effectiveJointRowBudget_source
    (hfull : Q.FullJointBudget source.base (D.parameters.m + D.parameters.q))
    (h : H) (hh : h ∈ source.rows) :
    A.exteriorNorm (source.originalIdeal h) *
      A.exteriorNorm (Q.effectiveMovingMaskRecipe.support (source.row h).momentIdeal) ≤
        source.normFactor h * source.base ^ (D.parameters.m + D.parameters.q) := by
  have hrow := Q.effectiveMovingMaskRecipe_jointBudget source.base
    (D.parameters.m + D.parameters.q) hfull (0 : V) (source.row h).momentIdeal
    (D.allowed 0 h hh)
  have hmul := mul_le_mul_of_nonneg_left hrow (source.row h).factor_pos.le
  change source.normFactor h *
    (A.exteriorNorm (source.row h).ideal *
      A.exteriorNorm (Q.effectiveMovingMaskRecipe.support (source.row h).momentIdeal)) ≤ _ at hmul
  rw [← mul_assoc, ← (source.row h).norm_factor] at hmul
  exact hmul

/-- Both the original source budget and the filtering identity are
derived internally from its actual complete moving recipe. -/
theorem withEffectiveJointRowBudget_eq_self
    (hfull : Q.FullJointBudget source.base (D.parameters.m + D.parameters.q)) :
    D.withJointRowBudget Q.effectiveMovingMaskRecipe
      (D.effectiveJointRowBudget_source Q hfull) = D :=
  D.withJointRowBudget_eq_self Q.effectiveMovingMaskRecipe
    (D.effectiveJointRowBudget_source Q hfull)
    (Q.effectiveMovingMaskRecipe_jointBudget source.base
      (D.parameters.m + D.parameters.q) hfull)

end ActualAllocatedSource.Calibration
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.jointRowBudgetData_eq_self
#print axioms HeckeSkeleton.Moments.EngineStep.CompleteMovingRowRecipe.effectiveJointRowBudgetData_eq_self
#print axioms HeckeSkeleton.Moments.EngineStep.ActualAllocatedSource.Calibration.withJointRowBudget_eq_self
#print axioms HeckeSkeleton.Moments.EngineStep.ActualAllocatedSource.Calibration.effectiveJointRowBudget_source
#print axioms HeckeSkeleton.Moments.EngineStep.ActualAllocatedSource.Calibration.withEffectiveJointRowBudget_eq_self
