import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.ParameterPrimitiveExtension
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.LocalizedCompleteSource
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.FrozenEngineOutput
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.PrimeProfileSupport

/-!
# One original moving recipe with both of its arithmetic budgets

The displayed-support and joint row/mask bounds belong to the same
complete moving recipe used to form the canonical arithmetic atoms.
They are retained together through equal-product comparisons, actual
ordinary reflection, Mellin normalization and the next strict call.

The joint bound is required on the current paired rows. The original
source has precisely this bound; its exact finite-row localization
supplies the stronger allowed-row premise of the primitive engine.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField HeckeGeneral.Characters HeckeGeneral.Analysis MeasureTheory
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.ThetaSkeleton.Global
open scoped Classical

variable {K : Type} [Field K] [NumberField K]

/-- These are the actual recipe and its two distinct arithmetic bounds.
There is no energy, analytic inequality or engine output among the fields. -/
structure CompleteSourceBudgetData (c : TargetContext K)
    (theta : Finset (HeckeCharacter K)) (U : ℝ)
    (d : MomentData K c.family.omega (targetCharacter K c))
    (p : PairedInvariantParameters) where
  source : CompleteSourceData c theta d
  primeSupport : PrimeProfileSupport d
  supportBudget : source.recipe.SupportBudget U p.q
  pairedJointBudget : ∀ u ∈ pairedRows d p.parameters U,
    idealNorm K u * idealNorm K
      (source.recipe.moving.fullMaskSupport source.recipe.remaining) ≤ U ^ (p.m + p.q)

def completeSourceBudgetPrimitive (c : TargetContext K)
    (theta : Finset (HeckeCharacter K)) (U : ℝ)
    (d : MomentData K c.family.omega (targetCharacter K c))
    (p : PairedInvariantParameters) : Prop :=
  Nonempty (CompleteSourceBudgetData c theta U d p)

namespace CompleteSourceBudgetData

variable {c : TargetContext K} {theta : Finset (HeckeCharacter K)} {U : ℝ}
variable {d : MomentData K c.family.omega (targetCharacter K c)}
variable {p : PairedInvariantParameters}

/-- The same prime tests and both numerical budgets survive the exact
finite-row restriction which is used immediately before a strict call. -/
def localized (D : CompleteSourceBudgetData c theta U d p) :
    CompleteSourceBudgetData c theta U (localizeOriginalParent d p.parameters U) p where
  source := D.source.localized p.parameters U
  primeSupport := D.primeSupport
  supportBudget := D.supportBudget
  pairedJointBudget := by
    intro u hu
    exact D.pairedJointBudget u ((localizeOriginalParent_pairedRows d p.parameters U) ▸ hu)

/-- The producer receives the same recipe after an energy-preserving
localization to the actual finite parent rows. -/
theorem localizedFullJointBudget (D : CompleteSourceBudgetData c theta U d p) :
    (D.source.localized p.parameters U).recipe.FullJointBudget U (p.m + p.q) :=
  D.source.localized_fullJointBudget p.parameters U D.pairedJointBudget

/-- Frozen and Mellin-normalized tests do not change the original
allowed rows, complete character or full common mask. -/
def mellinStrictModel {Ω : Type*} [MeasurableSpace Ω]
    (n : Node K c.family.omega (targetCharacter K c))
    (D : CompleteSourceBudgetData c theta U n.data (pairedInvariantParameters n.parameters))
    (cap J : ℕ) (A lower upper : ℝ) (hA : 0 ≤ A) (hlower : 0 < lower)
    (hinterval : lower ≤ upper) (P : ℝ) (hP : 1 ≤ P) (frequency : ℝ × ℝ) :
    CompleteSourceBudgetData c theta U
      (n.mellinStrictModel (Ω := Ω) cap J A lower upper hA hlower hinterval P hP frequency).data
      (pairedInvariantParameters n.parameters) where
  source := D.source.mellinStrictModel (Ω := Ω) n cap J A lower upper
    hA hlower hinterval P hP frequency
  primeSupport := by
    exact (D.primeSupport.freezeMomentTime 0).normalizedMellinPlainData _ _ _ _ _ _ _ _
  supportBudget := D.supportBudget
  pairedJointBudget := D.pairedJointBudget

/-- Ordinary reflection keeps m, q, z, the actual rows and the same
recipe. Its change to one plain length cannot detach either budget. -/
def fixedLineReflectionChild
    (n : Node K c.family.omega (targetCharacter K c))
    (D : CompleteSourceBudgetData c theta U n.data (pairedInvariantParameters n.parameters))
    (first : Bool) (scale E : ℝ) (hE : 1 ≤ E) (J : ℕ) (x : (ℕ × Bool) × ℝ) :
    CompleteSourceBudgetData c theta U
      (n.fixedLineReflectionChild first scale E hE J x).data
      (pairedInvariantParameters (n.fixedLineReflectionChild first scale E hE J x).parameters) where
  source := D.source.fixedLineReflectionChild n first scale E hE J x
  primeSupport := D.primeSupport.normalizedOrdinaryPowerChild
    first (reflectionFixedLine x.1.2) (-x.2) E hE J
  supportBudget := D.supportBudget
  pairedJointBudget := D.pairedJointBudget

end CompleteSourceBudgetData

/-- Closure is verified on the literal fixed-line constructor before
the reflection factory forms a child label or recursive inequality. -/
theorem completeSourceBudgetPrimitive_fixedLine
    (c : TargetContext K) (theta : Finset (HeckeCharacter K)) (U : ℝ) :
    FixedLineParameterPreserved (completeSourceBudgetPrimitive c theta U) := by
  rintro n first scale E hE J x ⟨D⟩
  exact ⟨D.fixedLineReflectionChild n first scale E hE J x⟩

section ActualMovingChild

variable {c : TargetContext K} {theta : Finset (HeckeCharacter K)}
variable {Q : Type*} {parent d : MomentData K c.family.omega (targetCharacter K c)}
variable {a : RealParameters} {U : ℝ}
variable {rowDomain : Set (NonzeroIdeal K)} {window : Set ℝ}
variable {orders : Finset (ℕ × ℕ)}

/-- The very same chosen strict child carries its actual recipe and
both budgets into the next recursive source primitive. -/
def frozenMovingChildCompleteSourceBudgetData
    (child : EngineStep.MovingEngineChildAdmissible
      (axiomChoice K c).A (probeData K c) (momentRowCharacters K c) Q
      parent rowDomain window orders U d a)
    (htheta : d.theta = theta) (hslots : ∀ j, d.slotCoefficient j ∈ theta)
    (hprime : PrimeProfileSupport d) :
    CompleteSourceBudgetData c theta U (freezeMomentTime d 0) (pairedInvariantParameters a) where
  source := frozenMovingChildCompleteSourceData child htheta hslots
  primeSupport := hprime.freezeMomentTime 0
  supportBudget := child.supportBudget
  pairedJointBudget u hu := by
    exact child.fullJointBudget PUnit.unit u
      (((d.rows_spec _ u).mp (Finset.mem_filter.mp hu).1).1)

end ActualMovingChild

namespace Source

variable {c : TargetContext K}
variable (R : ExpansionRecipe.RecipeExpansion K (places K c) (targetCharacter K c)
  c.geometry (expansionShellAllowance K c))

/-- The empty moving recipe and remaining ideal one have exactly unit
full mask support, without inferring a norm bound from mask equality. -/
private theorem emptyMoving_fullMaskSupport_one :
    (EngineStep.OriginalMovingFactors.empty
      (A := (axiomChoice K c).A) (P := probeData K c)
      (R := momentRowCharacters K c)).fullMaskSupport 1 = 1 := by
  apply Subtype.ext
  simp [EngineStep.OriginalMovingFactors.fullMaskSupport,
    EngineStep.OriginalMovingFactors.empty_support,
    EngineStep.unitExterior, EngineStep.CommonSupportMass.commonRadical,
    HeckePort.IdealMobiusDivisorSum.primeSupport, ← Ideal.one_eq_top]

/-- The original source supplies the two budgets from its actual empty
moving list and original finite row cutoff. No producer is assumed. -/
def recipeRootCompleteSourceBudgetData {Z T : ℝ}
    (i : SourceMomentIndexFor K c (recipeMomentSourceData K c R) Z T)
    (s : SixthUnitClasses K (places K c)) (theta : Finset (HeckeCharacter K))
    (htheta : (recipeRoot R i s).data.theta = theta)
    (hslots : ∀ j, (recipeRoot R i s).data.slotCoefficient j ∈ theta) :
    CompleteSourceBudgetData c theta (momentBaseFor i) (recipeRoot R i s).data
      (pairedInvariantParameters (recipeRoot R i s).parameters) where
  source := recipeRootCompleteSourceData R i s theta htheta hslots
  primeSupport := recipeRoot_primeSupport R i s
  supportBudget := by
    change (axiomChoice K c).A.exteriorNorm
      EngineStep.OriginalMovingFactors.empty.support ≤ momentBaseFor i ^ (0 : ℝ)
    rw [EngineStep.OriginalMovingFactors.empty_support, Real.rpow_zero]
    change (Ideal.absNorm (1 : Ideal (𝓞 K)) : ℝ) ≤ 1
    simp only [map_one, Nat.cast_one, le_refl]
  pairedJointBudget := by
    intro u hu
    change idealNorm K u * idealNorm K
      (EngineStep.OriginalMovingFactors.empty.fullMaskSupport 1) ≤
      momentBaseFor i ^ (recipeRoot R i s).width
    rw [emptyMoving_fullMaskSupport_one]
    exact (recipeRoot_reflectionCalibration R i s).product_budget u hu

end Source

end HeckeSkeleton.Moments.EngineInduction
