import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.RestorationRows
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.RecipeRoot
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.OrdinaryProfileNormalization
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.PowerWindowEnergy
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.RowNonNorm
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.StepOutputAdapter
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.ProfileScaling

/-!
# Primitive arithmetic calibration at actual roots and reflection children

The fixed recipe enumerates the complete exterior-ideal ball. Its row
character and full mask are literal complete-ideal data, including every
redundant sixth power; no argument is restricted to physical source fibers.
Thus the initial remaining ideal one supplies the required joint row norm
budget without a new arithmetic or analytic assumption.

Time freezing, positive profile scaling, the actual one-frequency power
child and its actual normalization preserve all arithmetic data involved
in reflection. The transferred facts include the row/conductor calibration,
the complete remaining mask, and the original non-norm condition. The two
primitive ingredients for proving the latter at an actual root are stated
explicitly: a radial anchor for the fixed target and finite-background
absorption for every original recipe presentation. Neither is inferred
from the older packet decomposition or its finite physical row fibers.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open scoped Classical BigOperators nonZeroDivisors

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}

/-- The exact arithmetic fields used by ordinary reflection. These are
verified by reduction for the concrete transformations below. -/
structure ReflectionArithmeticPreserved (parent child : Node K ω ψ) (U : ℝ) : Prop where
  rows : pairedRows child.data child.parameters U = pairedRows parent.data parent.parameters U
  rowCharacter : child.data.rowCharacter = parent.data.rowCharacter
  plainBackground : child.data.plainBackground = parent.data.plainBackground
  theta : child.data.theta = parent.data.theta
  commonMask : child.data.commonMask = parent.data.commonMask
  width : child.width = parent.width

namespace ReflectionArithmeticPreserved

/-- The complete exterior row and primitive joint norm budget survive. -/
theorem calibration {parent child : Node K ω ψ} {U : ℝ}
    (h : ReflectionArithmeticPreserved parent child U)
    {S : Set (HeightOneSpectrum (𝓞 K))} [Fintype S]
    {P : ProbeData K S} {R : RowCharacterInput K S P}
    {extra : NonzeroIdeal K → NonzeroIdeal K}
    (cal : ReflectionRowCalibration S P R parent extra U) :
    ReflectionRowCalibration S P R child extra U := by
  constructor
  · intro u hu
    obtain ⟨v, hv, ξ, hξ⟩ := cal.identify u (h.rows ▸ hu)
    exact ⟨v, hv, ξ, by simpa only [h.rowCharacter] using hξ⟩
  · intro u hu
    simpa only [h.width] using cal.product_budget u (h.rows ▸ hu)

/-- The mask is the same full S/6, complete-row and remaining-ideal mask. -/
theorem remainingMask {parent child : Node K ω ψ} {U : ℝ}
    (h : ReflectionArithmeticPreserved parent child U)
    {S : Set (HeightOneSpectrum (𝓞 K))} [Fintype S]
    {extra : NonzeroIdeal K → NonzeroIdeal K}
    (hmask : ∀ u I, parent.data.commonMask u I =
      (completeIdealCommonMask K S u I && decide (IsCoprime I (extra u).val))) :
    ∀ u I, child.data.commonMask u I =
      (completeIdealCommonMask K S u I && decide (IsCoprime I (extra u).val)) := by
  simpa only [h.commonMask] using hmask

theorem radial_zero {parent child : Node K ω ψ} {U : ℝ}
    (h : ReflectionArithmeticPreserved parent child U) (w : InfinitePlace K)
    (hzero : heckeRadialParameter K w parent.data.plainBackground = 0) :
    heckeRadialParameter K w child.data.plainBackground = 0 := by
  simpa only [h.plainBackground] using hzero

theorem finite_background {parent child : Node K ω ψ} {U : ℝ}
    (h : ReflectionArithmeticPreserved parent child U)
    (hfinite : FiniteOrder parent.data.plainBackground →
      parent.data.plainBackground⁻¹ ∈ parent.data.theta) :
    FiniteOrder child.data.plainBackground → child.data.plainBackground⁻¹ ∈ child.data.theta := by
  simpa only [h.plainBackground, h.theta] using hfinite

/-- This transfers the original condition, rather than replacing the row
filter by a new non-norm filter. -/
theorem nonNorm {parent child : Node K ω ψ} {U : ℝ}
    (h : ReflectionArithmeticPreserved parent child U)
    (hnonNorm : ∀ u ∈ pairedRows parent.data parent.parameters U, ∀ t : ℝ,
      parent.data.plainBackground * parent.data.rowCharacter u ≠ heckeNormTwist K t) :
    ∀ u ∈ pairedRows child.data child.parameters U, ∀ t : ℝ,
      child.data.plainBackground * child.data.rowCharacter u ≠ heckeNormTwist K t := by
  simpa only [h.rows, h.plainBackground, h.rowCharacter] using hnonNorm

end ReflectionArithmeticPreserved

/-- Exact node corresponding to the actual replaced power-window test. -/
def Node.ordinaryPowerChildNode (n : Node K ω ψ) (first : Bool)
    (σ frequency length : ℝ) : Node K ω ψ :=
  Node.ordinary (ordinaryPowerChild K n.data first σ frequency)
    (ordinaryPowerParameters n.parameters first length)

/-- The same actual child, after extracting its positive profile envelope. -/
def Node.normalizedOrdinaryPowerChildNode (n : Node K ω ψ) (first : Bool)
    (σ frequency length E0 : ℝ) (hE0 : 1 ≤ E0) (J : ℕ) : Node K ω ψ :=
  Node.ordinary (normalizedOrdinaryPowerChild n.data first σ frequency E0 hE0 J)
    (ordinaryPowerParameters n.parameters first length)

theorem Node.freezeTime_reflectionArithmetic (n : Node K ω ψ) (time U : ℝ) :
    ReflectionArithmeticPreserved n (n.freezeTime time) U :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Node.scaleProfiles_reflectionArithmetic (n : Node K ω ψ)
    (a : ℝ) (ha : 0 < a) (U : ℝ) :
    ReflectionArithmeticPreserved n (n.scaleProfiles a ha) U :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Node.normalizeProfiles_reflectionArithmetic (n : Node K ω ψ)
    (A : ℝ) (hA : 0 < A) (U : ℝ) :
    ReflectionArithmeticPreserved n (n.normalizeProfiles A hA) U :=
  n.scaleProfiles_reflectionArithmetic A⁻¹ (inv_pos.mpr hA) U

theorem Node.ordinaryPowerChildNode_reflectionArithmetic (n : Node K ω ψ)
    (first : Bool) (σ frequency length U : ℝ) :
    ReflectionArithmeticPreserved n (n.ordinaryPowerChildNode first σ frequency length) U :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Node.normalizedOrdinaryPowerChildNode_reflectionArithmetic (n : Node K ω ψ)
    (first : Bool) (σ frequency length E0 : ℝ) (hE0 : 1 ≤ E0) (J : ℕ) (U : ℝ) :
    ReflectionArithmeticPreserved n
      (n.normalizedOrdinaryPowerChildNode first σ frequency length E0 hE0 J) U :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

namespace Source

variable {c : TargetContext K}
variable (recipe : ExpansionRecipe.RecipeExpansion K (places K c) (targetCharacter K c)
  c.geometry (expansionShellAllowance K c))
variable {Z T : ℝ}
variable (i : SourceMomentIndexFor K c (recipeMomentSourceData K c recipe) Z T)
variable (s : SixthUnitClasses K (places K c))

/-- Every complete ideal in the model ball, not merely a witness row. -/
theorem recipeRoot_complete_rows :
    (recipeRoot recipe i s).data.rows = completeExteriorIdealRows K (places K c) := rfl

theorem recipeRoot_complete_rowCharacter :
    (recipeRoot recipe i s).data.rowCharacter =
      completeIdealRowCharacter K (places K c) (probeData K c) (momentRowCharacters K c) s := rfl

theorem recipeRoot_complete_mask :
    (recipeRoot recipe i s).data.commonMask = completeIdealCommonMask K (places K c) := rfl

/-- The initial remaining ideal is one, so the exact model row cutoff is
already the required joint budget. No physical-fiber premise is needed. -/
theorem recipeRoot_reflectionCalibration :
    ReflectionRowCalibration (places K c) (probeData K c) (momentRowCharacters K c)
      (recipeRoot recipe i s) (fun _ => 1) (momentBaseFor i) := by
  constructor
  · intro u hu
    have hallowed := (((recipeRoot recipe i s).data.rows_spec _ u).1
      (Finset.mem_filter.mp hu).1).1
    have hexterior : completeIdealIsExterior K (places K c) u := hallowed
    exact ⟨⟨u, hexterior⟩, rfl, s, rfl⟩
  · intro u hu
    have h := (recipeRoot recipe i s).paired_row_norm_le hu
    have hone : idealNorm K (1 : NonzeroIdeal K) = 1 := by
      change (Ideal.absNorm (1 : Ideal (𝓞 K)) : ℝ) = 1
      simp only [map_one, Nat.cast_one]
    simpa only [hone, mul_one] using h

/-- Removing all slots changes neither the complete row construction nor
the initial remaining ideal. The zero-slot filter is used literally. -/
theorem recipeRoot_noSlots_reflectionCalibration :
    ReflectionRowCalibration (places K c) (probeData K c) (momentRowCharacters K c)
      (recipeRoot recipe i.noSlots s) (fun _ => 1) (momentBaseFor i) :=
  recipeRoot_reflectionCalibration recipe i.noSlots s

/-- The actual root satisfies the full remaining-mask formula at R=1. -/
theorem recipeRoot_remainingMask :
    ∀ u I, (recipeRoot recipe i s).data.commonMask u I =
      (completeIdealCommonMask K (places K c) u I &&
        decide (IsCoprime I (1 : NonzeroIdeal K).val)) := by
  intro u I
  rw [recipeRoot_complete_mask]
  change completeIdealCommonMask K (places K c) u I =
    (completeIdealCommonMask K (places K c) u I && decide (IsCoprime I (1 : Ideal (𝓞 K))))
  simp only [isCoprime_one_right, decide_true, Bool.and_true]

theorem recipeRoot_noSlots_remainingMask :
    ∀ u I, (recipeRoot recipe i.noSlots s).data.commonMask u I =
      (completeIdealCommonMask K (places K c) u I &&
        decide (IsCoprime I (1 : NonzeroIdeal K).val)) :=
  recipeRoot_remainingMask recipe i.noSlots s

/-- The weaker zero-slot non-norm entrance uses only the actual target
radial anchor; it needs no exceptional-set enlargement. -/
theorem recipeRoot_nonNorm_zero (w : InfinitePlace K)
    (hψ : heckeRadialParameter K w (targetCharacter K c) = 0)
    (hzero : (recipeRoot recipe i s).parameters.z = 0) :
    ∀ u ∈ pairedRows (recipeRoot recipe i s).data (recipeRoot recipe i s).parameters
      (momentBaseFor i), ∀ t : ℝ,
      (recipeRoot recipe i s).data.plainBackground *
        (recipeRoot recipe i s).data.rowCharacter u ≠ heckeNormTwist K t :=
  pairedRows_actualPlain_nonNorm_zero (recipeRoot recipe i s).data w
    (plainBackground_radial_zero (recipeRoot recipe i s).data w hψ)
    (recipeRoot recipe i s).parameters (momentBaseFor i) hzero

theorem recipeRoot_noSlots_nonNorm (w : InfinitePlace K)
    (hψ : heckeRadialParameter K w (targetCharacter K c) = 0) :
    ∀ u ∈ pairedRows (recipeRoot recipe i.noSlots s).data
      (recipeRoot recipe i.noSlots s).parameters (momentBaseFor i), ∀ t : ℝ,
      (recipeRoot recipe i.noSlots s).data.plainBackground *
        (recipeRoot recipe i.noSlots s).data.rowCharacter u ≠ heckeNormTwist K t :=
  recipeRoot_nonNorm_zero recipe i.noSlots s w hψ rfl

/-- A primitive fixed-family statement supplies finite-background
absorption for every selected model, including labels not realized by a
physical source witness. No final non-norm assertion is an argument. -/
theorem recipeRoot_nonNorm (w : InfinitePlace K)
    (hψ : heckeRadialParameter K w (targetCharacter K c) = 0)
    (hfinite : ∀ j : Fin recipe.family.presentationCount,
      FiniteOrder (recipe.family.presentation j).plainBackground →
        (recipe.family.presentation j).plainBackground⁻¹ ∈
          (recipe.family.presentation j).theta) :
    ∀ u ∈ pairedRows (recipeRoot recipe i s).data (recipeRoot recipe i s).parameters
      (momentBaseFor i), ∀ t : ℝ,
      (recipeRoot recipe i s).data.plainBackground *
        (recipeRoot recipe i s).data.rowCharacter u ≠ heckeNormTwist K t := by
  refine pairedRows_actualPlain_nonNorm_of_target (recipeRoot recipe i s).data w hψ ?_
    (recipeRoot recipe i s).parameters (momentBaseFor i)
  exact hfinite (_root_.ExpansionRecipe.decodePresentation recipe.family.presentationCount
    recipe.family.presentationCount_pos ((recipeMomentModels K c recipe).heights Z T i (4 : Fin 6)))

end Source
end HeckeSkeleton.Moments.EngineInduction
