import HeckePort.Moments.Descent.MarkedFourier
import HeckePort.Moments.Descent.LocalReflection

/-!
# Frequency rows of marked and unmarked slots

Port of openai/math `OAI/NumberTheory/DirichletL/Descent/MarkedStratum.lean`
(revision `fd4aeeb2`).

The `Local` section (statements over an arbitrary finite field `F`) is verbatim.  The two
definitions `frequencyMultiplier` and `frequencyRow` come from openai's
`Eisenstein/FixedCuspArrays.lean` (generic over a finite field; not part of the shared set), and
are copied here because the mixed rows are built from them.

The theorems `actual_mixed_frequency_units` / `actual_mixed_frequency_zero` evaluate the rows at
the residue field `𝓞 / P` for the sextic residue character `actualSextic P hg`, using the
closed-form values of the unmarked rows (`canonical_frequencyRow_units`, `canonical_frequencyRow_zero`,
from `CanonicalRowCompletion`) and of the marked active sum (`actual_marked_active_formula`).
These closed forms are character-specific, so they are the explicit hypotheses `hunits`,
`hzero`, `hmarked` of `mixed_frequency_units` and `mixed_frequency_zero`, which are otherwise the
verbatim case split.  `actual_mixed_active_stratum` additionally uses the stratum sum
`FixedRayActiveSet.sum_active_stratum` of `Moments/FixedRay`; it is not stated here.
-/

namespace HeckePort.Moments

open scoped BigOperators Classical

noncomputable section

section Local

variable {F : Type*} [Field F] [Fintype F]

def frequencyMultiplier (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (σ ε : Fˣ) (x h : F) : ℂ :=
  if h = 0 then 1 else (((χ⁻¹) ^ 2) ((σ : F) * h)) * ψ (((ε : F) * x) * h⁻¹)

def frequencyRow (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (j : ℕ) (σ ε : Fˣ) (x h : F) : ℂ :=
  finiteAdditiveFourierCoeff ψ (fun t => (χ ^ j) t) h * frequencyMultiplier χ ψ σ ε x h

def markedFrequencyRow (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (σ ε : Fˣ) (x h : F) : ℂ :=
  finiteAdditiveFourierCoeff ψ zeroMark h * frequencyMultiplier χ ψ σ ε x h

theorem markedFrequencyRow_zero (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (σ ε : Fˣ) (x : F) :
    markedFrequencyRow χ ψ σ ε x 0 = (Fintype.card F : ℂ)⁻¹ := by
  simp [markedFrequencyRow, frequencyMultiplier, finiteAdditiveFourierCoeff, zeroMark]

theorem markedFrequencyRow_units (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (σ ε : Fˣ) (x : F) :
    (∑ h : Fˣ, markedFrequencyRow χ ψ σ ε x h) =
      localReflectionActive zeroMark χ ψ σ ε x := by
  unfold markedFrequencyRow finiteAdditiveFourierCoeff frequencyMultiplier
    localReflectionActive localFourier
  simp only [Units.ne_zero, ite_false, Units.val_inv_eq_inv_val,
    Finset.mul_sum, neg_mul]
  apply Finset.sum_congr rfl
  intro h hh
  ring

def mixedFrequencyRow (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (marked : Bool) (j : ℕ) (σ ε : Fˣ) (x h : F) : ℂ :=
  if marked then markedFrequencyRow χ ψ σ ε x h else frequencyRow χ ψ j σ ε x h

/-- openai `actual_mixed_frequency_units`, with the closed forms of the two row sums as the
hypotheses `hmarked` (openai `actual_marked_active_formula`) and `hunits`
(`canonical_frequencyRow_units`). -/
theorem mixed_frequency_units (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (j : ℕ) (σ ε : Fˣ) (x : F) (Am Au : ℂ)
    (hmarked : localReflectionActive zeroMark χ ψ σ ε x = Am)
    (hunits : (∑ h : Fˣ, frequencyRow χ ψ j σ ε x h) = Au) (marked : Bool) :
    (∑ h : Fˣ, mixedFrequencyRow χ ψ marked j σ ε x h) = if marked then Am else Au := by
  cases marked
  · simp only [mixedFrequencyRow, Bool.false_eq_true, ite_false]
    exact hunits
  · simp only [mixedFrequencyRow, ite_true]
    rw [markedFrequencyRow_units, hmarked]

/-- openai `actual_mixed_frequency_zero`, with the zero frequency of the unmarked row `Zu`
(openai `canonical_frequencyRow_zero`) as hypothesis. -/
theorem mixed_frequency_zero (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (j : ℕ) (σ ε : Fˣ) (x : F) (Zu : ℂ)
    (hzero : frequencyRow χ ψ j σ ε x 0 = Zu) (marked : Bool) :
    mixedFrequencyRow χ ψ marked j σ ε x 0 =
      if marked then (Fintype.card F : ℂ)⁻¹ else Zu := by
  cases marked
  · simp only [mixedFrequencyRow, Bool.false_eq_true, ite_false]
    exact hzero
  · simp only [mixedFrequencyRow, ite_true]
    exact markedFrequencyRow_zero _ _ _ _ _

end Local

end

end HeckePort.Moments
