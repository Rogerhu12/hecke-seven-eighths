import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalExceptionalBinding
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.HybridLeafOrdinaryBinding

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The original exceptional whole columns and their row translations

The first and second common ideals contribute one translation for each
row.  Its phase has norm one, so it can be removed after the complete
original main/comparison subtraction.  The two Fourier polynomials below
retain the same allocation, divisor, residual character and comparison
source.  No bound for either separate comparison rectangle is used.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckePort.Moments

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {H ι : Type*} [Fintype ι] [DecidableEq ι]
variable {R : ActualSecondCorrelationRows A σ H ι}
variable {Ray : Type*} [CommGroup Ray] [Fintype Ray]
variable {U V : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

namespace ActualHybridLeaf

variable (leaf : ActualHybridLeaf K H U V)

/-- The exceptional analogue of the primitive whole-column binding,
allowing the actual common row translations on both original sides. -/
theorem t3b_exceptionalIntegrand_eq_centered_frames
    (C : A.GeneralArithmeticContext σ η hS)
    (left : SecondSideFrame (V := WithLp 2 (U × V)) C R Ray .left leaf.leftSlots)
    (right : SecondSideFrame (V := WithLp 2 (U × V)) C R Ray .right leaf.rightSlots)
    (EL : SecondCoefficientComparison left.dictionary)
    (ER : SecondCoefficientComparison right.dictionary)
    {theta : Finset (HeckeCharacter K)} (Q : PairedFiniteCharacters theta H)
    (hrows : leaf.rows = R.rows)
    (hleft : leaf.left = left.allocation.columns)
    (hright : leaf.right = right.allocation.columns)
    (hpredicate : leaf.exceptional = Q.exceptional)
    (hweight : ∀ h ∈ leaf.rows, leaf.rowWeight h = R.weight h * R.correlation h)
    (hleftAtom : ∀ h ∈ leaf.rows, ∀ i ∈ leaf.left,
      leaf.leftCoefficient h i = left.centeredCoefficient EL h i)
    (hrightAtom : ∀ h ∈ leaf.rows, ∀ i ∈ leaf.right,
      star (leaf.rightCoefficient h i) = right.centeredCoefficient ER h i)
    (hleftPoint : ∀ h ∈ leaf.rows, ∃ a : WithLp 2 (U × V), ∀ i ∈ leaf.left,
      WithLp.toLp 2 (leaf.leftFirst h i, leaf.leftSecond h i) = a +
        rawSourceLocation (left.leftLocation h) (left.rightLocation h)
          (left.slotLocation h) i)
    (hrightPoint : ∀ h ∈ leaf.rows, ∃ a : WithLp 2 (U × V), ∀ i ∈ leaf.right,
      WithLp.toLp 2 (-leaf.rightFirst h i, leaf.rightSecond h i) = a +
        rawSourceLocation (right.leftLocation h) (right.rightLocation h)
          (right.slotLocation h) i)
    (z : U × V) :
    leaf.exceptionalIntegrand z =
      jointColumnPairMagnitude (R.exceptionalRows Q)
        left.allocation.columns right.allocation.columns
        (fun h : R.live => R.weight h.val * R.correlation h.val)
        (fun h => left.centeredCoefficient EL h.val)
        (fun h => right.centeredCoefficient ER h.val)
        (fun h => rawSourceLocation (left.leftLocation h.val)
          (left.rightLocation h.val) (left.slotLocation h.val))
        (fun h => rawSourceLocation (right.leftLocation h.val)
          (right.rightLocation h.val) (right.slotLocation h.val))
        (WithLp.toLp 2 z) := by
  change leaf.exceptionalIntegrand z =
    jointColumnPairMagnitude
      (Finset.univ.filter (fun h : R.live => Q.exceptional h.val))
      left.allocation.columns right.allocation.columns
      (fun h : R.live => R.weight h.val * R.correlation h.val)
      (fun h => left.centeredCoefficient EL h.val)
      (fun h => right.centeredCoefficient ER h.val)
      (fun h => rawSourceLocation (left.leftLocation h.val)
        (left.rightLocation h.val) (left.slotLocation h.val))
      (fun h => rawSourceLocation (right.leftLocation h.val)
        (right.rightLocation h.val) (right.slotLocation h.val))
      (WithLp.toLp 2 z)
  rw [← R.pair_magnitude_live left.allocation.columns right.allocation.columns
    (left.centeredCoefficient EL) (right.centeredCoefficient ER)
    (fun h => rawSourceLocation (left.leftLocation h) (left.rightLocation h)
      (left.slotLocation h))
    (fun h => rawSourceLocation (right.leftLocation h) (right.rightLocation h)
      (right.slotLocation h)) Q.exceptional (WithLp.toLp 2 z)]
  unfold exceptionalIntegrand jointColumnPairMagnitude
  rw [hrows, hpredicate]
  apply Finset.sum_congr rfl
  intro h hh
  have hrow : h ∈ leaf.rows := by
    rw [hrows]
    exact (Finset.mem_filter.mp hh).1
  obtain ⟨a, ha⟩ := hleftPoint h hrow
  obtain ⟨b, hb⟩ := hrightPoint h hrow
  have hl : jointFourierColumn leaf.left (leaf.leftCoefficient h)
      (fun i => WithLp.toLp 2 (leaf.leftFirst h i, leaf.leftSecond h i))
        (WithLp.toLp 2 z) =
      jointPhase (WithLp.toLp 2 z) a *
        jointFourierColumn left.allocation.columns (left.centeredCoefficient EL h)
          (rawSourceLocation (left.leftLocation h) (left.rightLocation h)
            (left.slotLocation h)) (WithLp.toLp 2 z) := by
    rw [← jointFourierColumn_rowTranslation, ← hleft]
    unfold jointFourierColumn
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only
    rw [hleftAtom h hrow i hi, ha i hi]
  have hr : jointFourierColumn leaf.right (fun i => star (leaf.rightCoefficient h i))
      (fun i => WithLp.toLp 2 (-leaf.rightFirst h i, leaf.rightSecond h i))
        (WithLp.toLp 2 z) =
      jointPhase (WithLp.toLp 2 z) b *
        jointFourierColumn right.allocation.columns (right.centeredCoefficient ER h)
          (rawSourceLocation (right.leftLocation h) (right.rightLocation h)
            (right.slotLocation h)) (WithLp.toLp 2 z) := by
    rw [← jointFourierColumn_rowTranslation, ← hright]
    unfold jointFourierColumn
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only
    rw [hrightAtom h hrow i hi, hb i hi]
  rw [hweight h hrow, hl, hr]
  simp only [norm_mul, norm_jointPhase, one_mul]

end ActualHybridLeaf
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualHybridLeaf.t3b_exceptionalIntegrand_eq_centered_frames
