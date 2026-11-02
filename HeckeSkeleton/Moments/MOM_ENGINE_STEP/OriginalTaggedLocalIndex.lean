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

private theorem option_eq_none_or_some
    {α : Type*} (o : Option α) : o = none ∨ ∃ a, o = some a := by
  cases o with
  | none => exact Or.inl rfl
  | some a => exact Or.inr ⟨a, rfl⟩

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
  unfold localIndex
  dsimp only
  split <;> rfl

@[simp] theorem localIndex_firstDivisor (i : I) :
    (L.localIndex tag i).2.1.val = L.firstDivisor i := by
  unfold localIndex
  dsimp only
  split <;> rfl

@[simp] theorem localIndex_second (i : I) :
    (L.localIndex tag i).2.2.1.val = L.second i := by
  unfold localIndex
  dsimp only
  split <;> rfl

@[simp] theorem localIndex_secondDivisor (i : I) :
    (L.localIndex tag i).2.2.2.1.val = (L.allocation i).1 := by
  unfold localIndex
  dsimp only
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
  have hlocal : (L.localBranch tag i).indexWeight (L.localIndex tag i) =
      L.carrier.indexWeight (L.index i) := by
    rw [L.indexWeight_eq i]
    simp only [TwoDivisorCommonBranch.indexWeight, L.localIndex_first tag i,
      L.localIndex_firstDivisor tag i, L.localIndex_second tag i,
      L.localIndex_secondDivisor tag i]
  have hmain (hi : tag i = none) :
      (L.mainCarrier tag).indexWeight ((L.mainLabels tag).index ⟨i, hi⟩) =
        L.carrier.indexWeight (L.index i) :=
    ((L.mainLabels tag).indexWeight_eq ⟨i, hi⟩).trans (L.indexWeight_eq i).symm
  have herror (n : ℕ) (p : ExteriorPrime A) (hi : tag i = some (n, p)) :
      (L.errorCarrier tag n p).indexWeight ((L.errorLabels tag n p).index ⟨i, hi⟩) =
        L.carrier.indexWeight (L.index i) :=
    ((L.errorLabels tag n p).indexWeight_eq ⟨i, hi⟩).trans (L.indexWeight_eq i).symm
  have hQ (p : ExteriorPrime A) : Q p = (Ideal.absNorm p.val.asIdeal : ℝ) := rfl
  rw [hlocal]
  unfold amplifiedIndex
  split <;> simp_all only [amplifiedIndexWeight] <;> ring

end OriginalArithmeticLabels
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.OriginalArithmeticLabels.localIndex_first
#print axioms HeckeSkeleton.Moments.EngineStep.OriginalArithmeticLabels.localIndex_secondDivisor
#print axioms HeckeSkeleton.Moments.EngineStep.OriginalArithmeticLabels.amplifiedIndexWeight_local
