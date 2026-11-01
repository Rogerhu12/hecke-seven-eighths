import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualExceptionalTerminal
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.HybridFiniteLeaf
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondClassProduction
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondFactorIdentification

/-!
# Original centered atoms bind the canonical exceptional leaf

The comparison rectangle is identified one original factor at a time.
Its two original Gauss scales may differ from the main rectangle; only
their product must agree.  The complete subtraction is then transported
to the actual side frame before taking any polynomial norm.

The final leaf identity consumes only its literal row/column carriers,
individual coefficient and location identities, and the original paired
finite-character predicate.  Zero correlations are removed by equality.
No polynomial, exceptional energy, or terminal inequality is an input.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckePort.IdealMobiusDivisorSum
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckePort.Moments WholeAllocation

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {H ι V : Type*} [Fintype ι] [DecidableEq ι]
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {R : ActualSecondCorrelationRows A σ H ι}
variable {Ray : Type*} [CommGroup Ray] [Fintype Ray]
variable {side : SecondColumnSide} {k : ℕ}
variable {S₁ S₂ : Finset (Ideal (𝓞 K))}
variable {S : Fin k → Finset (HeightOneSpectrum (𝓞 K))}
variable {ideal : AllocationColumn K k → A.Exterior}
variable {ray : AllocationColumn K k → Ray} {c : AllocationColumn K k → ℂ}
variable {point : H → AllocationColumn K k → V} {χ : (Ray × Ray) →* Circle}

/-- Original comparison-factor data.  All identifications are of one
plain or prime factor; the centered polynomial is constructed below. -/
structure SecondOriginalComparison
    (f : SecondRectangularFactors R Ray side S₁ S₂ S ideal ray c point χ) where
  comparison : SecondCoefficientComparison f.dictionary
  original : SecondColumnFactors K Ray k
  factors : comparison.dictionary.FactorIdentification original
  gaussScale₁ : ℝ
  gaussScale₂ : ℝ
  gaussScale₁_nonneg : 0 ≤ gaussScale₁
  leftNormalizer : original.leftNormalizer = (Real.sqrt gaussScale₁ : ℂ)⁻¹
  rightNormalizer : original.rightNormalizer = (Real.sqrt gaussScale₂ : ℂ)⁻¹
  slotNormalizer : original.slotNormalizer =
    (fun i => (Real.sqrt (f.gaussSlotScale i) : ℂ)⁻¹)
  plain_product : f.gaussScale₁ * f.gaussScale₂ = gaussScale₁ * gaussScale₂

namespace SecondOriginalComparison

variable {f : SecondRectangularFactors R Ray side S₁ S₂ S ideal ray c point χ}
variable (E : SecondOriginalComparison f)

/-- This is the literal two-rectangle coefficient from the original
factor expansion, still before any residual character is applied. -/
def wholeCoefficient (i : AllocationColumn K k) : ℂ := c i - E.original.coefficient i

theorem centeredCoefficient_eq_original (i : AllocationColumn K k)
    (hi : i ∈ childCartesianColumns S₁ S₂ S) :
    E.comparison.centeredCoefficient (Real.sqrt f.gaussScale₁ : ℂ)⁻¹
        (Real.sqrt f.gaussScale₂ : ℂ)⁻¹
        (fun j => (Real.sqrt (f.gaussSlotScale j) : ℂ)⁻¹) i = E.wholeCoefficient i := by
  rw [E.comparison.centeredCoefficient_original_scales
    f.gaussScale₁ f.gaussScale₂ E.gaussScale₁ E.gaussScale₂ f.gaussSlotScale
    f.gaussScale₁_pos.le E.gaussScale₁_nonneg E.plain_product]
  have hcomparison := E.factors.coefficient_eq i hi
  rw [E.leftNormalizer, E.rightNormalizer, E.slotNormalizer] at hcomparison
  rw [← f.coefficient_factor i hi, hcomparison]
  rfl

/-- The original residual character and finite phase are attached only
after the complete two-rectangle subtraction has been identified. -/
theorem frame_centeredCoefficient_eq_original
    (C : A.GeneralArithmeticContext σ η hS)
    (L : Ideal (𝓞 K)) (a : primeSupport L → Finset (Fin (k + 2)))
    (hne : (pairedAllocatedColumns L a S₁ S₂ S id id HeightOneSpectrum.asIdeal).Nonempty)
    (h : H) (i : AllocationColumn K k)
    (hi : i ∈ childCartesianColumns S₁ S₂ S) :
    (f.frame C L a hne).centeredCoefficient E.comparison h i =
      side.actualCoefficient (σ := σ) Ray ideal R.frequency ray χ E.wholeCoefficient h i := by
  cases side with
  | left =>
    change E.comparison.centeredCoefficient (Real.sqrt f.gaussScale₁ : ℂ)⁻¹
        (Real.sqrt f.gaussScale₂ : ℂ)⁻¹
        (fun j => (Real.sqrt (f.gaussSlotScale j) : ℂ)⁻¹) i *
          (fixedLeftPhase Ray χ (f.dictionary.ray i) : ℂ) *
          σ (A.sexticResidue (ideal i) (R.frequency h)) =
      E.wholeCoefficient i * (fixedLeftPhase Ray χ (ray i) : ℂ) *
        σ (A.sexticResidue (ideal i) (R.frequency h))
    rw [E.centeredCoefficient_eq_original i hi, f.ray_factor i hi]
  | right =>
    change star (E.comparison.centeredCoefficient (Real.sqrt f.gaussScale₁ : ℂ)⁻¹
        (Real.sqrt f.gaussScale₂ : ℂ)⁻¹
        (fun j => (Real.sqrt (f.gaussSlotScale j) : ℂ)⁻¹) i *
          (fixedRightPhase Ray χ (f.dictionary.ray i) : ℂ) *
          σ (A.sexticResidue (ideal i) (-R.frequency h))) =
      star (E.wholeCoefficient i * (fixedRightPhase Ray χ (ray i) : ℂ) *
        σ (A.sexticResidue (ideal i) (-R.frequency h)))
    rw [E.centeredCoefficient_eq_original i hi, f.ray_factor i hi]

/-- This equality is obtained by summing the original individual
coefficient and location identities. -/
theorem frame_centeredColumn_eq_original
    (C : A.GeneralArithmeticContext σ η hS)
    (L : Ideal (𝓞 K)) (a : primeSupport L → Finset (Fin (k + 2)))
    (hne : (pairedAllocatedColumns L a S₁ S₂ S id id HeightOneSpectrum.asIdeal).Nonempty)
    (h : H) (hh : h ∈ R.rows) (ξ : V) :
    jointFourierColumn (f.frame C L a hne).allocation.columns
      ((f.frame C L a hne).centeredCoefficient E.comparison h)
      (rawSourceLocation (f.leftLocation h) (f.rightLocation h) (f.slotLocation h)) ξ =
    jointFourierColumn (pairedAllocatedColumns L a S₁ S₂ S id id HeightOneSpectrum.asIdeal)
      (side.actualCoefficient (σ := σ) Ray ideal R.frequency ray χ E.wholeCoefficient h)
      (point h) ξ := by
  unfold jointFourierColumn
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ∈ childCartesianColumns S₁ S₂ S := by
    change i ∈ pairedAllocatedColumns L a S₁ S₂ S id id HeightOneSpectrum.asIdeal at hi
    rw [paired_allocated_columns_eq_filter] at hi
    exact (Finset.mem_filter.mp hi).1
  rw [E.frame_centeredCoefficient_eq_original C L a hne h i hi',
    f.point_factor h hh i hi']

end SecondOriginalComparison

section Leaves

variable {U W : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]

namespace ActualHybridLeaf

variable (B : ActualHybridLeaf K H U W)

theorem exceptionalIntegrand_eq_zero_of_left_empty (hleft : B.left = ∅) (z : U × W) :
    B.exceptionalIntegrand z = 0 := by
  simp only [exceptionalIntegrand, jointColumnPairMagnitude, jointFourierColumn,
    hleft, Finset.sum_empty, norm_zero, mul_zero, zero_mul, Finset.sum_const_zero]

theorem exceptionalIntegrand_eq_zero_of_right_empty (hright : B.right = ∅) (z : U × W) :
    B.exceptionalIntegrand z = 0 := by
  simp only [exceptionalIntegrand, jointColumnPairMagnitude, jointFourierColumn,
    hright, Finset.sum_empty, norm_zero, mul_zero, Finset.sum_const_zero]

theorem exceptionalCost_eq_zero_of_left_empty (hleft : B.left = ∅) : B.exceptionalCost = 0 := by
  simp only [exceptionalCost, B.exceptionalIntegrand_eq_zero_of_left_empty hleft,
    MeasureTheory.integral_zero, mul_zero]

theorem exceptionalCost_eq_zero_of_right_empty (hright : B.right = ∅) : B.exceptionalCost = 0 := by
  simp only [exceptionalCost, B.exceptionalIntegrand_eq_zero_of_right_empty hright,
    MeasureTheory.integral_zero, mul_zero]

/-- The canonical leaf and the terminal theorem have the same actual
rowwise integrand.  The hypotheses concern only original carriers and
single coefficient/location entries, never their finite polynomials. -/
theorem exceptionalIntegrand_eq_centered_frames
    (C : A.GeneralArithmeticContext σ η hS)
    (left : SecondSideFrame (V := WithLp 2 (U × W)) C R Ray .left B.leftSlots)
    (right : SecondSideFrame (V := WithLp 2 (U × W)) C R Ray .right B.rightSlots)
    (EL : SecondCoefficientComparison left.dictionary)
    (ER : SecondCoefficientComparison right.dictionary)
    {theta : Finset (HeckeCharacter K)} (Q : PairedFiniteCharacters theta H)
    (hrows : B.rows = R.rows) (hleft : B.left = left.allocation.columns)
    (hright : B.right = right.allocation.columns) (hpredicate : B.exceptional = Q.exceptional)
    (hweight : ∀ h ∈ B.rows, B.rowWeight h = R.weight h * R.correlation h)
    (hleftAtom : ∀ h ∈ B.rows, ∀ i ∈ B.left,
      B.leftCoefficient h i = left.centeredCoefficient EL h i)
    (hrightAtom : ∀ h ∈ B.rows, ∀ i ∈ B.right,
      star (B.rightCoefficient h i) = right.centeredCoefficient ER h i)
    (hleftPoint : ∀ h ∈ B.rows, ∀ i ∈ B.left,
      WithLp.toLp 2 (B.leftFirst h i, B.leftSecond h i) =
        rawSourceLocation (left.leftLocation h) (left.rightLocation h) (left.slotLocation h) i)
    (hrightPoint : ∀ h ∈ B.rows, ∀ i ∈ B.right,
      WithLp.toLp 2 (-B.rightFirst h i, B.rightSecond h i) =
        rawSourceLocation (right.leftLocation h) (right.rightLocation h) (right.slotLocation h) i)
    (z : U × W) :
    B.exceptionalIntegrand z =
      jointColumnPairMagnitude (R.exceptionalRows Q)
        left.allocation.columns right.allocation.columns
        (fun h : R.live => R.weight h.val * R.correlation h.val)
        (fun h => left.centeredCoefficient EL h.val)
        (fun h => right.centeredCoefficient ER h.val)
        (fun h => rawSourceLocation (left.leftLocation h.val) (left.rightLocation h.val)
          (left.slotLocation h.val))
        (fun h => rawSourceLocation (right.leftLocation h.val) (right.rightLocation h.val)
          (right.slotLocation h.val)) (WithLp.toLp 2 z) := by
  change B.exceptionalIntegrand z =
    jointColumnPairMagnitude (Finset.univ.filter (fun h : R.live => Q.exceptional h.val))
      left.allocation.columns right.allocation.columns
      (fun h : R.live => R.weight h.val * R.correlation h.val)
      (fun h => left.centeredCoefficient EL h.val)
      (fun h => right.centeredCoefficient ER h.val)
      (fun h => rawSourceLocation (left.leftLocation h.val) (left.rightLocation h.val)
        (left.slotLocation h.val))
      (fun h => rawSourceLocation (right.leftLocation h.val) (right.rightLocation h.val)
        (right.slotLocation h.val)) (WithLp.toLp 2 z)
  rw [← R.pair_magnitude_live left.allocation.columns right.allocation.columns
    (left.centeredCoefficient EL) (right.centeredCoefficient ER)
    (fun h => rawSourceLocation (left.leftLocation h) (left.rightLocation h) (left.slotLocation h))
    (fun h => rawSourceLocation (right.leftLocation h) (right.rightLocation h) (right.slotLocation h))
    Q.exceptional (WithLp.toLp 2 z)]
  unfold exceptionalIntegrand jointColumnPairMagnitude
  rw [hrows, hpredicate]
  apply Finset.sum_congr rfl
  intro h hh
  have hrow : h ∈ B.rows := by rw [hrows]; exact (Finset.mem_filter.mp hh).1
  rw [hweight h hrow]
  have hl : jointFourierColumn B.left (B.leftCoefficient h)
      (fun i => WithLp.toLp 2 (B.leftFirst h i, B.leftSecond h i)) (WithLp.toLp 2 z) =
      jointFourierColumn left.allocation.columns (left.centeredCoefficient EL h)
        (rawSourceLocation (left.leftLocation h) (left.rightLocation h) (left.slotLocation h))
        (WithLp.toLp 2 z) := by
    unfold jointFourierColumn
    rw [← hleft]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only
    rw [hleftAtom h hrow i hi, hleftPoint h hrow i hi]
  have hr : jointFourierColumn B.right (fun i => star (B.rightCoefficient h i))
      (fun i => WithLp.toLp 2 (-B.rightFirst h i, B.rightSecond h i)) (WithLp.toLp 2 z) =
      jointFourierColumn right.allocation.columns (right.centeredCoefficient ER h)
        (rawSourceLocation (right.leftLocation h) (right.rightLocation h) (right.slotLocation h))
        (WithLp.toLp 2 z) := by
    unfold jointFourierColumn
    rw [← hright]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only
    rw [hrightAtom h hrow i hi, hrightPoint h hrow i hi]
  rw [hl, hr]

end ActualHybridLeaf
end Leaves
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.SecondOriginalComparison.frame_centeredColumn_eq_original
#print axioms HeckeSkeleton.Moments.EngineStep.ActualHybridLeaf.exceptionalIntegrand_eq_centered_frames
