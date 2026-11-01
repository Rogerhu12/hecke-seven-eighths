import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalAmplifiedCarrier
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DependentNormalizedFibres

/-!
# The original arithmetic index of dependent passive families

Forgetting a passive allocation retains the exact original live source
label. Its first common pair, both original divisors, second common
pair and two occurrence allocations are read from the existing source
dictionary. In the amplified case its prime and valuation are also
unchanged. No new arithmetic image or chosen child is introduced.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Characters HeckeGeneral.Analysis.ConditionalMoments
open CommonSupportMass ActualNormalizedPairFamily

namespace OriginalArithmeticLabels

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {σ : K →+* ℂ} {ω ψ : HeckeCharacter K}
variable {I V : Type*} [Fintype I]
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {Λ : I → Type*} {cap : ℕ} {Z : ℝ}
variable (L : OriginalArithmeticLabels K I cap)
variable (families : ∀ i, ActualNormalizedPairFamily A σ V (Λ i) ω ψ Z)
variable (outer : Finset I) (labels : ∀ i, Finset (Λ i))

/-- Only the new passive label is forgotten. Every original arithmetic
coordinate is kept in its original carrier. -/
def dependentIndex
    (b : (sigmaCombine families).active (outer.sigma labels)) : L.carrier.Index :=
  L.index b.val.1

@[simp] theorem dependentIndex_first
    (b : (sigmaCombine families).active (outer.sigma labels)) :
    (L.dependentIndex families outer labels b).1.val = L.first b.val.1 := rfl

@[simp] theorem dependentIndex_firstDivisor
    (b : (sigmaCombine families).active (outer.sigma labels)) :
    (L.dependentIndex families outer labels b).2.1.val = L.firstDivisor b.val.1 := rfl

@[simp] theorem dependentIndex_second
    (b : (sigmaCombine families).active (outer.sigma labels)) :
    (L.dependentIndex families outer labels b).2.2.1.val = L.second b.val.1 := rfl

@[simp] theorem dependentIndex_allocation
    (b : (sigmaCombine families).active (outer.sigma labels)) :
    L.indexAllocation (L.dependentIndex families outer labels b) =
      L.allocation b.val.1 := rfl

variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {ell eps : ℝ}
variable (pool : PowerScaleExteriorPool A bad Z ell eps)
variable (tag : I → Option (ℕ × ExteriorPrime A))
variable (tag_mem : ∀ i n p, tag i = some (n, p) →
  n ∈ ({1, 6, 7} : Finset ℕ) ∧ p ∈ pool.primes)

/-- The dependent family uses the genuine original amplifier tag,
including the original exponent six branch. -/
def dependentAmplifiedIndex
    (b : (sigmaCombine families).active (outer.sigma labels)) :
    AmplifiedCommonIndex pool (L.mainCarrier tag) (L.errorCarrier tag) :=
  L.amplifiedIndex tag pool tag_mem b.val.1

@[simp] theorem dependentAmplifiedIndex_tag
    (b : (sigmaCombine families).active (outer.sigma labels)) :
    L.amplifiedTag tag pool
        (L.dependentAmplifiedIndex families outer labels pool tag tag_mem b) =
      tag b.val.1 :=
  L.amplifiedIndex_tag tag pool tag_mem _

@[simp] theorem dependentAmplifiedIndex_allocation
    (b : (sigmaCombine families).active (outer.sigma labels)) :
    L.amplifiedAllocation tag pool
        (L.dependentAmplifiedIndex families outer labels pool tag tag_mem b) =
      L.allocation b.val.1 :=
  L.amplifiedIndex_allocation tag pool tag_mem _

end OriginalArithmeticLabels
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.OriginalArithmeticLabels.dependentIndex_allocation
#print axioms HeckeSkeleton.Moments.EngineStep.OriginalArithmeticLabels.dependentAmplifiedIndex_tag
#print axioms HeckeSkeleton.Moments.EngineStep.OriginalArithmeticLabels.dependentAmplifiedIndex_allocation
