import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CurriedNormalizedSource
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalDirectParentWeights

/-!
# The original arithmetic index of a computed family

The literal index theorem fixes its first allowance and its original
Poisson weight before the individual analytic certificates. This
record retains those computed quantities and the same old allocation
cost. Attaching the exact parent weight changes neither the family nor
any of its selected children.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField DedekindZetaZeroFree MeasureTheory
open HeckeGeneral.Characters HeckeGeneral.Analysis.ConditionalMoments

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {H : Type*} {U V : Type}
variable [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable [MeasurableSpace (WithLp 2 (U × V))] [BorelSpace (WithLp 2 (U × V))]
variable {ω ψ : HeckeCharacter K} {Z : ℝ}

namespace CurriedNormalizedFamily.SourceIntegral

variable {f : CurriedNormalizedFamily A σ (WithLp 2 (U × V)) ω ψ Z}
variable {leaf : ActualHybridLeaf K H U V}

structure IndexedWeight (S : f.SourceIntegral leaf)
    (branch : TwoDivisorCommonBranch (K := K)) (index : branch.Index) where
  firstFactor : ℝ
  normalization : ℝ
  cost : ℝ
  bound : ∀ (input : f.Input) (b : (f.family input).active Finset.univ),
    firstFactor *
      (S.frozen * (f.family input).weight Finset.univ 0 b / normalization) ≤
        cost * branch.indexWeight index

namespace IndexedWeight

/-- The three real quantities are read from the literal theorem; no
first-profile or aggregate-weight estimate is supplied separately. -/
def ofCurried {Λ L R : Type} [Fintype Λ]
    {hl : L → Prop} {hr : R → Prop}
    {make : ∀ l r, hl l → hr r →
      ActualNormalizedPairFamily A σ (WithLp 2 (U × V)) Λ ω ψ Z}
    {S : (CurriedNormalizedFamily.ofCurried make).SourceIntegral leaf}
    {branch : TwoDivisorCommonBranch (K := K)} {index : branch.Index}
    {firstFactor normalization cost : ℝ}
    (estimate : ∀ l r hleft hright
      (b : (make l r hleft hright).active Finset.univ),
      firstFactor *
        (S.frozen * (make l r hleft hright).weight Finset.univ 0 b / normalization) ≤
          cost * branch.indexWeight index) :
    S.IndexedWeight branch index where
  firstFactor := firstFactor
  normalization := normalization
  cost := cost
  bound input :=
    estimate input.1.val input.2.val input.1.property input.2.property

variable {S : f.SourceIntegral leaf}
variable {branch : TwoDivisorCommonBranch (K := K)} {index : branch.Index}

/-- The old allocation cost remains outside the family exactly once.
Only the original parent-weight identity is used to attach the outer
scalar to the already proved pointwise index estimate. -/
theorem outer_bound (I : S.IndexedWeight branch index)
    (input : f.Input) (parentWidth outerWeight factor : ℝ)
    (hfactor : 0 ≤ factor)
    (houter : outerWeight / Z ^ parentWidth =
      factor * I.firstFactor / I.normalization)
    (b : (f.family input).active Finset.univ) :
    outerWeight * S.frozen * (f.family input).weight Finset.univ parentWidth b ≤
      factor * (I.cost * branch.indexWeight index) := by
  have hpw : (f.family input).weight Finset.univ parentWidth b =
      (f.family input).weight Finset.univ 0 b / Z ^ parentWidth := by
    simp only [ActualNormalizedPairFamily.weight, normalizedCapacityPairWeight,
      Real.rpow_zero, div_one]
  calc
    _ = (outerWeight / Z ^ parentWidth) *
        (S.frozen * (f.family input).weight Finset.univ 0 b) := by rw [hpw]; ring
    _ = factor * (I.firstFactor *
        (S.frozen * (f.family input).weight Finset.univ 0 b / I.normalization)) := by
      rw [houter]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (I.bound input b) hfactor

end IndexedWeight
end CurriedNormalizedFamily.SourceIntegral
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CurriedNormalizedFamily.SourceIntegral.IndexedWeight.ofCurried
#print axioms HeckeSkeleton.Moments.EngineStep.CurriedNormalizedFamily.SourceIntegral.IndexedWeight.outer_bound
