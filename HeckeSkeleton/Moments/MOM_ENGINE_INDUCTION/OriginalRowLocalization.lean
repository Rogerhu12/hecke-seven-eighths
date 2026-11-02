import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ParentMoment

/-!
# Localizing the original parent to its actual finite rows

The primitive engine requires its joint row and mask budget on every
allowed row. The original source has an unrestricted exterior-ideal
predicate, whereas the induction's arithmetic calibration supplies that
budget on the rows actually used by the current moment. Restricting the
allowed predicate to this same finite set connects the two statements.

All ideal and prime polynomials, both centered rectangles, the common
mask, and the actual finite parent energy are unchanged. The operation
does not discard any summand of the parent moment. It takes place before
the engine produces its strictly smaller children.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open scoped Classical BigOperators

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}

/-- Restrict only the allowed rows and their exhaustive enumeration.
Every character, test, slot coefficient and Boolean mask is retained. -/
def restrictOriginalRows (d : MomentData K ω ψ)
    (keep : NonzeroIdeal K → Prop) : MomentData K ω ψ :=
  { d with
    allowedRow := fun u => d.allowedRow u ∧ keep u
    rows := fun X => (d.rows X).filter keep
    rows_spec := by
      intro X u
      rw [Finset.mem_filter, d.rows_spec]
      tauto }

@[simp] theorem restrictOriginalRows_plainPolynomial
    (d : MomentData K ω ψ) (keep : NonzeroIdeal K → Prop)
    (W : IdealTest K) (u : NonzeroIdeal K) (N t : ℝ) :
    plainPolynomial (restrictOriginalRows d keep) W u N t =
      plainPolynomial d W u N t := rfl

@[simp] theorem restrictOriginalRows_inversePolynomial
    (d : MomentData K ω ψ) (keep : NonzeroIdeal K → Prop)
    (u : NonzeroIdeal K) (D t : ℝ) :
    inversePolynomial (restrictOriginalRows d keep) u D t =
      inversePolynomial d u D t := rfl

@[simp] theorem restrictOriginalRows_primePolynomial
    (d : MomentData K ω ψ) (keep : NonzeroIdeal K → Prop)
    (j : Fin d.geometry.slotCount) (u : NonzeroIdeal K) (U t : ℝ) :
    primePolynomial (restrictOriginalRows d keep) j u U t =
      primePolynomial d j u U t := rfl

@[simp] theorem restrictOriginalRows_slotProduct
    (d : MomentData K ω ψ) (keep : NonzeroIdeal K → Prop)
    (u : NonzeroIdeal K) (U t : ℝ) :
    slotProduct (restrictOriginalRows d keep) u U t = slotProduct d u U t := rfl

/-- The original exceptional-row filter commutes with the new arithmetic
restriction. This covers both zero and positive slot parameters. -/
theorem pairedRows_restrictOriginalRows
    (d : MomentData K ω ψ) (keep : NonzeroIdeal K → Prop)
    (a : RealParameters) (U : ℝ) :
    pairedRows (restrictOriginalRows d keep) a U = (pairedRows d a U).filter keep := by
  dsimp only [pairedRows, restrictOriginalRows]
  exact Finset.filter_comm _ _ _

theorem pairedRows_restrictOriginalRows_eq
    (d : MomentData K ω ψ) (keep : NonzeroIdeal K → Prop)
    (a : RealParameters) (U : ℝ)
    (hkeep : ∀ u ∈ pairedRows d a U, keep u) :
    pairedRows (restrictOriginalRows d keep) a U = pairedRows d a U := by
  rw [pairedRows_restrictOriginalRows]
  exact Finset.filter_eq_self.mpr hkeep

/-- A finite row localization at the parameters of this actual parent. -/
def localizeOriginalParent (d : MomentData K ω ψ) (a : RealParameters) (U : ℝ) :
    MomentData K ω ψ := restrictOriginalRows d (fun u => u ∈ pairedRows d a U)

@[simp] theorem localizeOriginalParent_pairedRows
    (d : MomentData K ω ψ) (a : RealParameters) (U : ℝ) :
    pairedRows (localizeOriginalParent d a U) a U = pairedRows d a U :=
  pairedRows_restrictOriginalRows_eq d _ a U (fun _ hu => hu)

/-- The full finite moment is preserved for every height, including
after both plain profiles have been frozen and Mellin normalized. -/
@[simp] theorem localizeOriginalParent_pairedEnergy
    (d : MomentData K ω ψ) (a : RealParameters) (U t : ℝ) :
    pairedEnergy (localizeOriginalParent d a U) a U t = pairedEnergy d a U t := by
  unfold pairedEnergy
  rw [localizeOriginalParent_pairedRows]
  rfl

@[simp] theorem restrictOriginalRows_pairedStagePolynomial
    (d : MomentData K ω ψ) (keep : NonzeroIdeal K → Prop) (centered : Bool)
    (u : NonzeroIdeal K) (X₁ X₂ Y₁ Y₂ U t : ℝ) :
    EngineStep.pairedStagePolynomial centered (restrictOriginalRows d keep)
        u X₁ X₂ Y₁ Y₂ U t =
      EngineStep.pairedStagePolynomial centered d u X₁ X₂ Y₁ Y₂ U t := rfl

/-- Centering uses the same retained rows, tests and common mask in
both rectangles; its comparison scales need no modification. -/
@[simp] theorem localizeOriginalParent_pairedStageEnergy
    (d : MomentData K ω ψ) (a : RealParameters) (centered : Bool)
    (U t Y₁ Y₂ : ℝ) :
    EngineStep.pairedStageEnergy centered (localizeOriginalParent d a U) a U t Y₁ Y₂ =
      EngineStep.pairedStageEnergy centered d a U t Y₁ Y₂ := by
  unfold EngineStep.pairedStageEnergy
  rw [localizeOriginalParent_pairedRows]
  rfl

/-- Every allowed row of the localized parent is one of the original
paired rows. Thus a genuine paired-row arithmetic estimate can be used
by a producer which requires it on the entire allowed-row predicate. -/
theorem localizeOriginalParent_allowed
    (d : MomentData K ω ψ) (a : RealParameters) (U : ℝ)
    (u : NonzeroIdeal K)
    (hu : (localizeOriginalParent d a U).allowedRow u) :
    u ∈ pairedRows d a U := hu.2

theorem localizeOriginalParent_jointBudget
    (d : MomentData K ω ψ) (a : RealParameters) (U : ℝ)
    (extra : NonzeroIdeal K → NonzeroIdeal K)
    (hbudget : ∀ u ∈ pairedRows d a U,
      idealNorm K u * idealNorm K (extra u) ≤ U ^ (a.m + a.q)) :
    ∀ u, (localizeOriginalParent d a U).allowedRow u →
      idealNorm K u * idealNorm K (extra u) ≤ U ^ (a.m + a.q) := by
  intro u hu
  exact hbudget u hu.2

/-- The common comparison changes only the two plain lengths. Its row
localization is therefore literally the same at every comparison split. -/
@[simp] theorem localizeOriginalParent_comparison
    (d : MomentData K ω ψ) (a : RealParameters) (U L : ℝ) :
    localizeOriginalParent d (EngineStep.comparisonParameters a L) U =
      localizeOriginalParent d a U := rfl

end HeckeSkeleton.Moments.EngineInduction
