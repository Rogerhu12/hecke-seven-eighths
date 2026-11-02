import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalAmplifiedCarrier

set_option linter.unusedSectionVars false

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

private theorem option_dependent_match_property
    {α : Type*} {β : Option α → Sort*}
    (o : Option α) (f0 : o = none → β none)
    (fs : ∀ a, o = some a → β (some a))
    (P : ∀ q, β q → Prop)
    (h0 : ∀ h, P none (f0 h))
    (hs : ∀ a h, P (some a) (fs a h)) :
    P o (match (generalizing := false) h : o with
      | none => f0 h
      | some a => fs a h) := by
  sorry

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
  show (match tag i with
    | none => L.mainCarrier tag
    | some q => L.errorCarrier tag q.1 q.2).Index from
  match h : tag i with
  | none => (L.mainLabels tag).index ⟨i, h⟩
  | some q => (L.errorLabels tag q.1 q.2).index ⟨i, h⟩

@[simp] theorem localIndex_first (i : I) :
    (L.localIndex tag i).1.val = L.first i := by
  sorry

@[simp] theorem localIndex_firstDivisor (i : I) :
    (L.localIndex tag i).2.1.val = L.firstDivisor i := by
  sorry

@[simp] theorem localIndex_second (i : I) :
    (L.localIndex tag i).2.2.1.val = L.second i := by
  sorry

@[simp] theorem localIndex_secondDivisor (i : I) :
    (L.localIndex tag i).2.2.2.1.val = (L.allocation i).1 := by
  sorry

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
  sorry

end OriginalArithmeticLabels
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.OriginalArithmeticLabels.localIndex_first
#print axioms HeckeSkeleton.Moments.EngineStep.OriginalArithmeticLabels.localIndex_secondDivisor
#print axioms HeckeSkeleton.Moments.EngineStep.OriginalArithmeticLabels.amplifiedIndexWeight_local
