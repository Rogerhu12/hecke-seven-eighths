import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ExceptionalOriginalIntegral
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ConstantCommonLeaf

/-!
# The actual exceptional leaf is the original centered row sum

The binding consists only of finite row/column identities and individual
coefficient/location identities.  The engine proves the resulting
magnitude and integral equalities.  Correlation-zero rows are removed
by their actual zero coefficient, while the full centered subtraction
and the right-hand conjugation remain inside the same two column norms.

Both original Fourier measures are retained.  Constant common-atom
extraction transports the identity back to the original parent leaf
without changing the outer scalar or choosing a second finite carrier.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap
open MeasureTheory

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckePort.Moments

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η hS}
variable {H ι U V : Type*} [Fintype ι] [DecidableEq ι]
variable [NormedAddCommGroup U] [InnerProductSpace ℝ U]
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {R : ActualSecondCorrelationRows A σ H ι}
variable {Ray : Type*} [CommGroup Ray] [Fintype Ray]
local notation "W" => WithLp 2 (U × V)

namespace ActualHybridLeaf

variable (leaf : ActualHybridLeaf K H U V)
variable (left : SecondSideFrame (V := (WithLp 2 (U × V))) C R Ray .left leaf.leftSlots)
variable (right : SecondSideFrame (V := (WithLp 2 (U × V))) C R Ray .right leaf.rightSlots)
variable (EL : SecondCoefficientComparison left.dictionary)
variable (ER : SecondCoefficientComparison right.dictionary)
variable {theta : Finset (HeckeCharacter K)} (Q : PairedFiniteCharacters theta H)

/-- These fields identify only raw finite atoms.  There is no magnitude,
integral, parent inequality, or terminal estimate among the premises. -/
structure ExceptionalBinding : Prop where
  rows : R.rows ⊆ leaf.rows
  rows_zero : ∀ h ∈ leaf.rows, h ∉ R.rows → leaf.rowWeight h = 0
  left_columns : leaf.left = left.allocation.columns
  right_columns : leaf.right = right.allocation.columns
  exceptional : ∀ h ∈ leaf.rows, leaf.exceptional h ↔ Q.exceptional h
  rowWeight : ∀ h ∈ leaf.rows, leaf.rowWeight h = R.weight h * R.correlation h
  leftCoefficient : ∀ h ∈ leaf.rows, ∀ i ∈ leaf.left,
    leaf.leftCoefficient h i = left.centeredCoefficient EL h i
  rightCoefficient : ∀ h ∈ leaf.rows, ∀ j ∈ leaf.right,
    star (leaf.rightCoefficient h j) = right.centeredCoefficient ER h j
  leftPoint : ∀ h ∈ leaf.rows, ∀ i ∈ leaf.left,
    WithLp.toLp 2 (leaf.leftFirst h i, leaf.leftSecond h i) =
      rawSourceLocation (left.leftLocation h) (left.rightLocation h) (left.slotLocation h) i
  rightPoint : ∀ h ∈ leaf.rows, ∀ j ∈ leaf.right,
    WithLp.toLp 2 (-leaf.rightFirst h j, leaf.rightSecond h j) =
      rawSourceLocation (right.leftLocation h) (right.rightLocation h) (right.slotLocation h) j

namespace ExceptionalBinding

variable {leaf left right EL ER Q} (b : leaf.ExceptionalBinding left right EL ER Q)

include b

theorem exceptional_rows_subset :
    R.rows.filter Q.exceptional ⊆ leaf.rows.filter leaf.exceptional := by
  intro h hh
  obtain ⟨hm, he⟩ := Finset.mem_filter.mp hh
  have hl : h ∈ leaf.rows := b.rows hm
  exact Finset.mem_filter.mpr ⟨hl, (b.exceptional h hl).mpr he⟩

theorem exceptional_rows_zero :
    ∀ h ∈ leaf.rows.filter leaf.exceptional,
      h ∉ R.rows.filter Q.exceptional → leaf.rowWeight h = 0 := by
  intro h hh hn
  obtain ⟨hm, he⟩ := Finset.mem_filter.mp hh
  apply b.rows_zero h hm
  intro hr
  exact hn (Finset.mem_filter.mpr ⟨hr, (b.exceptional h hm).mp he⟩)

/-- The two complete centered columns are compared before taking their
norms.  No Cauchy estimate is applied to the exceptional rows. -/
theorem exceptionalIntegrand_eq (z : U × V) :
    leaf.exceptionalIntegrand z =
      left.exceptionalMagnitude right EL ER Q (WithLp.toLp 2 z) := by
  have hfull : leaf.exceptionalIntegrand z =
      jointColumnPairMagnitude (R.rows.filter Q.exceptional)
        left.allocation.columns right.allocation.columns
        (fun h => R.weight h * R.correlation h)
        (left.centeredCoefficient EL) (right.centeredCoefficient ER)
        (fun h => rawSourceLocation (left.leftLocation h) (left.rightLocation h)
          (left.slotLocation h))
        (fun h => rawSourceLocation (right.leftLocation h) (right.rightLocation h)
          (right.slotLocation h)) (WithLp.toLp 2 z) := by
    unfold ActualHybridLeaf.exceptionalIntegrand
    calc
      _ = jointColumnPairMagnitude (R.rows.filter Q.exceptional) leaf.left leaf.right
          leaf.rowWeight leaf.leftCoefficient (fun h j => star (leaf.rightCoefficient h j))
          (fun h i => WithLp.toLp 2 (leaf.leftFirst h i, leaf.leftSecond h i))
          (fun h j => WithLp.toLp 2 (-leaf.rightFirst h j, leaf.rightSecond h j))
          (WithLp.toLp 2 z) :=
        jointColumnPairMagnitude_eq_on_zero_rows _ _ _ _ _ _ _ _ _ _
          b.exceptional_rows_subset b.exceptional_rows_zero
      _ = _ := by
        rw [← b.left_columns, ← b.right_columns]
        unfold jointColumnPairMagnitude
        apply Finset.sum_congr rfl
        intro h hh
        have hm : h ∈ leaf.rows := b.rows (Finset.mem_filter.mp hh).1
        have hl :
            jointFourierColumn leaf.left (leaf.leftCoefficient h)
              (fun i => WithLp.toLp 2 (leaf.leftFirst h i, leaf.leftSecond h i))
              (WithLp.toLp 2 z) =
            jointFourierColumn leaf.left (left.centeredCoefficient EL h)
              (rawSourceLocation (left.leftLocation h) (left.rightLocation h)
                (left.slotLocation h)) (WithLp.toLp 2 z) := by
          unfold jointFourierColumn
          apply Finset.sum_congr rfl
          intro i hi
          dsimp only
          rw [b.leftCoefficient h hm i hi, b.leftPoint h hm i hi]
        have hr :
            jointFourierColumn leaf.right (fun j => star (leaf.rightCoefficient h j))
              (fun j => WithLp.toLp 2 (-leaf.rightFirst h j, leaf.rightSecond h j))
              (WithLp.toLp 2 z) =
            jointFourierColumn leaf.right (right.centeredCoefficient ER h)
              (rawSourceLocation (right.leftLocation h) (right.rightLocation h)
                (right.slotLocation h)) (WithLp.toLp 2 z) := by
          unfold jointFourierColumn
          apply Finset.sum_congr rfl
          intro j hj
          dsimp only
          rw [b.rightCoefficient h hm j hj, b.rightPoint h hm j hj]
        rw [b.rowWeight h hm, hl, hr]
  exact hfull.trans (R.pair_magnitude_live
    left.allocation.columns right.allocation.columns
    (left.centeredCoefficient EL) (right.centeredCoefficient ER)
    (fun h => rawSourceLocation (left.leftLocation h) (left.rightLocation h)
      (left.slotLocation h))
    (fun h => rawSourceLocation (right.leftLocation h) (right.rightLocation h)
      (right.slotLocation h)) Q.exceptional (WithLp.toLp 2 z))

variable [FiniteDimensional ℝ U] [MeasurableSpace U] [BorelSpace U]
variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- The literal exceptional cost is integrated against its own two
original kernels.  This equality is available before any volume bound. -/
theorem exceptionalCost_eq :
    leaf.exceptionalCost = leaf.weight *
      ∫ z : U × V, left.exceptionalMagnitude right EL ER Q (WithLp.toLp 2 z)
        ∂nestedFourierMeasure leaf.firstKernel leaf.secondKernel := by
  unfold ActualHybridLeaf.exceptionalCost ActualHybridLeaf.measure
  congr 1
  exact integral_congr_ae (Filter.Eventually.of_forall b.exceptionalIntegrand_eq)

end ExceptionalBinding

/-- The exact support restriction has the same original centered
coefficients and locations. Its omitted-row proof is derived from the
original single-row correlation identity, not supplied as a bound. -/
def exceptionalBindingOnCorrelationSupport
    (hrows : leaf.rows = R.rows)
    (hleft : leaf.left = left.allocation.columns)
    (hright : leaf.right = right.allocation.columns)
    (hexceptional : ∀ h ∈ leaf.rows, leaf.exceptional h ↔ Q.exceptional h)
    (hweight : ∀ h ∈ leaf.rows, leaf.rowWeight h = R.weight h * R.correlation h)
    (hleftCoefficient : ∀ h ∈ leaf.rows, ∀ i ∈ leaf.left,
      leaf.leftCoefficient h i = left.centeredCoefficient EL h i)
    (hrightCoefficient : ∀ h ∈ leaf.rows, ∀ i ∈ leaf.right,
      star (leaf.rightCoefficient h i) = right.centeredCoefficient ER h i)
    (hleftPoint : ∀ h ∈ leaf.rows, ∀ i ∈ leaf.left,
      WithLp.toLp 2 (leaf.leftFirst h i, leaf.leftSecond h i) =
        rawSourceLocation (left.leftLocation h) (left.rightLocation h) (left.slotLocation h) i)
    (hrightPoint : ∀ h ∈ leaf.rows, ∀ i ∈ leaf.right,
      WithLp.toLp 2 (-leaf.rightFirst h i, leaf.rightSecond h i) =
        rawSourceLocation (right.leftLocation h) (right.rightLocation h) (right.slotLocation h) i) :
    leaf.ExceptionalBinding
      (left.restrictRows (fun h => R.correlation h ≠ 0))
      (right.restrictRows (fun h => R.correlation h ≠ 0)) EL ER Q where
  rows := by
    intro h hh
    have hh' : h ∈ R.rows ∧ R.correlation h ≠ 0 := by
      simpa only [ActualSecondCorrelationRows.restrictRows, Finset.mem_filter] using hh
    exact hrows.symm ▸ hh'.1
  rows_zero h hh hn := by
    rw [hweight h hh]
    exact R.weight_correlation_eq_zero_of_not_live h (hrows ▸ hh)
      (R.restrictRows_correlationSupport_rows ▸ hn)
  left_columns := hleft
  right_columns := hright
  exceptional := hexceptional
  rowWeight := hweight
  leftCoefficient := hleftCoefficient
  rightCoefficient := hrightCoefficient
  leftPoint := hleftPoint
  rightPoint := hrightPoint

namespace ConstantAtomExtraction

variable {leaf} (X : leaf.ConstantAtomExtraction)
variable (left : SecondSideFrame (V := (WithLp 2 (U × V))) C R Ray .left X.leaf.leftSlots)
variable (right : SecondSideFrame (V := (WithLp 2 (U × V))) C R Ray .right X.leaf.rightSlots)
variable (EL : SecondCoefficientComparison left.dictionary)
variable (ER : SecondCoefficientComparison right.dictionary)
variable [FiniteDimensional ℝ U] [MeasurableSpace U] [BorelSpace U]
variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- Exact constant-atom extraction and the raw atom binding reach the
same original exceptional cost.  The outer weight and both measures
are unchanged by this already proved extraction. -/
theorem exceptionalCost_eq_frames
    (b : X.leaf.ExceptionalBinding left right EL ER Q) :
    leaf.exceptionalCost = leaf.weight *
      ∫ z : U × V, left.exceptionalMagnitude right EL ER Q (WithLp.toLp 2 z)
        ∂nestedFourierMeasure leaf.firstKernel leaf.secondKernel :=
  X.exceptionalCost_eq.trans b.exceptionalCost_eq

end ConstantAtomExtraction
end ActualHybridLeaf

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualHybridLeaf.ExceptionalBinding.exceptionalIntegrand_eq
#print axioms HeckeSkeleton.Moments.EngineStep.ActualHybridLeaf.ExceptionalBinding.exceptionalCost_eq
#print axioms HeckeSkeleton.Moments.EngineStep.ActualHybridLeaf.exceptionalBindingOnCorrelationSupport
#print axioms HeckeSkeleton.Moments.EngineStep.ActualHybridLeaf.ConstantAtomExtraction.exceptionalCost_eq_frames
