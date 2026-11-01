import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CurriedNormalizedSource

/-!
# Kernel mass on the same computed source measure

The source certificate fixes its old allocation factor. The finite
kernel estimate below uses that factor and the existing family,
including its individual analytic input and chosen children.
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

structure KernelMass (S : f.SourceIntegral leaf) (parentWidth : ℝ) where
  coefficient : ℝ
  finite : ∀ (input : f.Input) (b : (f.family input).active Finset.univ),
    IsFiniteMeasure ((f.family input).kernel Finset.univ S.measure parentWidth b)
  bound : ∀ input : f.Input,
    (∑ b : (f.family input).active Finset.univ,
      ((f.family input).kernel Finset.univ S.measure parentWidth b).real Set.univ) ≤
      coefficient * ∑ b : (f.family input).active Finset.univ,
        (leaf.weight * S.frozen) * (f.family input).weight Finset.univ parentWidth b

namespace KernelMass

/-- Read the original curried estimate without changing the source
measure or the analytic certificates of its already fixed factory. -/
def ofCurried {Λ L R : Type} [Fintype Λ]
    {hl : L → Prop} {hr : R → Prop}
    {make : ∀ l r, hl l → hr r →
      ActualNormalizedPairFamily A σ (WithLp 2 (U × V)) Λ ω ψ Z}
    {S : (CurriedNormalizedFamily.ofCurried make).SourceIntegral leaf}
    {parentWidth coefficient : ℝ}
    (estimate : ∀ l r hleft hright,
      (∀ b : (make l r hleft hright).active Finset.univ,
        IsFiniteMeasure ((make l r hleft hright).kernel Finset.univ S.measure parentWidth b)) ∧
      (∑ b : (make l r hleft hright).active Finset.univ,
        ((make l r hleft hright).kernel Finset.univ S.measure parentWidth b).real Set.univ) ≤
        coefficient * ∑ b : (make l r hleft hright).active Finset.univ,
          (leaf.weight * S.frozen) * (make l r hleft hright).weight Finset.univ parentWidth b) :
    S.KernelMass parentWidth where
  coefficient := coefficient
  finite input :=
    (estimate input.1.val input.2.val input.1.property input.2.property).1
  bound input :=
    (estimate input.1.val input.2.val input.1.property input.2.property).2

end KernelMass
end CurriedNormalizedFamily.SourceIntegral
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CurriedNormalizedFamily.SourceIntegral.KernelMass.ofCurried
