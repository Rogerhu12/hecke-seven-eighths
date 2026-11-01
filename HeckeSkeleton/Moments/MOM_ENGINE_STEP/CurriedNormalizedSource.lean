import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CurriedNormalizedFamily
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalParentKernelFamily

/-!
# The source inequality for an already constructed family

The finite family and all its analytic input types are fixed first.
This certificate records the old allocation cost and the original
source inequality for exactly that family. Its constructor reads a
literal producer's curried proof; it does not choose another child.
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

namespace CurriedNormalizedFamily

structure SourceIntegral
    (f : CurriedNormalizedFamily A σ (WithLp 2 (U × V)) ω ψ Z)
    (leaf : ActualHybridLeaf K H U V) where
  frozen : ℝ
  bound : ∀ (input : f.Input) (parentWidth : ℝ),
    leaf.ordinaryCost / Z ^ parentWidth ≤
      ∑ b : (f.family input).active Finset.univ,
        ∫ ξ, (f.family input).childPair Finset.univ b ξ
          ∂(f.family input).kernel Finset.univ
            (actualNestedLabelMeasure (fun _ : f.Label => leaf.firstKernel)
              (fun _ : f.Label => leaf.secondKernel)
              (fun _ : f.Label => leaf.weight * frozen)) parentWidth b

namespace SourceIntegral

variable {f : CurriedNormalizedFamily A σ (WithLp 2 (U × V)) ω ψ Z}
variable {leaf : ActualHybridLeaf K H U V}

/-- The scalar is inferred from the literal source theorem's measure.
The factory in the result is the same curried constructor. -/
def ofCurried {Λ L R : Type} [Fintype Λ]
    {hl : L → Prop} {hr : R → Prop}
    {make : ∀ l r, hl l → hr r →
      ActualNormalizedPairFamily A σ (WithLp 2 (U × V)) Λ ω ψ Z}
    {frozen : ℝ}
    (bound : ∀ l r hleft hright (parentWidth : ℝ),
      leaf.ordinaryCost / Z ^ parentWidth ≤
        ∑ b : (make l r hleft hright).active Finset.univ,
          ∫ ξ, (make l r hleft hright).childPair Finset.univ b ξ
            ∂(make l r hleft hright).kernel Finset.univ
              (actualNestedLabelMeasure (fun _ : Λ => leaf.firstKernel)
                (fun _ : Λ => leaf.secondKernel)
                (fun _ : Λ => leaf.weight * frozen)) parentWidth b) :
    (CurriedNormalizedFamily.ofCurried make).SourceIntegral leaf where
  frozen := frozen
  bound input parentWidth :=
    bound input.1.val input.2.val input.1.property input.2.property parentWidth

/-- Both Fourier kernels and the original old-allocation factor. -/
def measure (S : f.SourceIntegral leaf) : f.Label → Measure (WithLp 2 (U × V)) :=
  actualNestedLabelMeasure (fun _ : f.Label => leaf.firstKernel)
    (fun _ : f.Label => leaf.secondKernel) (fun _ : f.Label => leaf.weight * S.frozen)

theorem ordinaryCost_le (S : f.SourceIntegral leaf)
    (input : f.Input) (parentWidth : ℝ) :
    leaf.ordinaryCost / Z ^ parentWidth ≤
      ∑ b : (f.family input).active Finset.univ,
        ∫ ξ, (f.family input).childPair Finset.univ b ξ
          ∂(f.family input).kernel Finset.univ S.measure parentWidth b :=
  S.bound input parentWidth

end SourceIntegral
end CurriedNormalizedFamily
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CurriedNormalizedFamily.SourceIntegral.ofCurried
#print axioms HeckeSkeleton.Moments.EngineStep.CurriedNormalizedFamily.SourceIntegral.ordinaryCost_le
