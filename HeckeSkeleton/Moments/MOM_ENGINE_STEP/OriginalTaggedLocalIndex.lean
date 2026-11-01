import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalAmplifiedCarrier

/-!
# The local arithmetic branch of the original amplifier tag

These are projections of the existing tagged arithmetic image. A local
literal source can use its branch index before the same index is put
into the full amplified sum. Every original coordinate and occurrence
allocation is retained.
-/

noncomputable section
open scoped Classical NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open CommonSupportMass

variable {K : Type} [Field K] [NumberField K]
variable {A : SArithmeticData K} {I : Type*} [Fintype I] {cap : ℕ}

namespace OriginalArithmeticLabels

variable (L : OriginalArithmeticLabels K I cap)
variable (tag : I → Option (ℕ × ExteriorPrime A))

def localBranch (i : I) : TwoDivisorCommonBranch (K := K) :=
  match tag i with
  | none => L.mainCarrier tag
  | some q => L.errorCarrier tag q.1 q.2

def localIndex (i : I) : (L.localBranch tag i).Index :=
  match h : tag i with
  | none => (L.mainLabels tag).index ⟨i, h⟩
  | some q => (L.errorLabels tag q.1 q.2).index ⟨i, h⟩

@[simp] theorem localIndex_first (i : I) :
    (L.localIndex tag i).1.val = L.first i := by
  unfold localIndex
  split <;> rfl

@[simp] theorem localIndex_firstDivisor (i : I) :
    (L.localIndex tag i).2.1.val = L.firstDivisor i := by
  unfold localIndex
  split <;> rfl

@[simp] theorem localIndex_second (i : I) :
    (L.localIndex tag i).2.2.1.val = L.second i := by
  unfold localIndex
  split <;> rfl

@[simp] theorem localIndex_secondDivisor (i : I) :
    (L.localIndex tag i).2.2.2.1.val = (L.allocation i).1 := by
  unfold localIndex
  split <;> rfl

variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable (P : PowerScaleExteriorPool A bad Z ell eps)
variable (tag_mem : ∀ i n p, tag i = some (n, p) →
  n ∈ ({1, 6, 7} : Finset ℕ) ∧ p ∈ P.primes)

/-- This is the same weight used by the full amplified index; the
pool density and original valuation weight occur exactly once. -/
theorem amplifiedIndexWeight_local (M B : ℝ) (i : I) :
    amplifiedIndexWeight P M B (L.mainCarrier tag) (L.errorCarrier tag)
      (L.amplifiedIndex tag P tag_mem i) =
    (4 / P.rowDensity M B) *
      (match tag i with
       | none => ((M + 6 * ell) / (ell / 2)) * Z ^ ell
       | some q => FirstGaussPoolData.localErrorWeight q.2 q.1 *
           (Ideal.absNorm q.2.val.asIdeal : ℝ) ^ amplifierMovingExponent q.1) *
        (L.localBranch tag i).indexWeight (L.localIndex tag i) := by
  cases h : tag i with
  | none => simp only [amplifiedIndex, h, amplifiedIndexWeight, localBranch, localIndex]; ring
  | some q => simp only [amplifiedIndex, h, amplifiedIndexWeight, localBranch, localIndex]; ring

end OriginalArithmeticLabels
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.OriginalArithmeticLabels.localIndex_first
#print axioms HeckeSkeleton.Moments.EngineStep.OriginalArithmeticLabels.localIndex_secondDivisor
#print axioms HeckeSkeleton.Moments.EngineStep.OriginalArithmeticLabels.amplifiedIndexWeight_local
