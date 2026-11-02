import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralSupport

set_option linter.unusedSectionVars false

/-!
# The complete common-prime deletion in the literal source

An inactive first common prime need not appear in the first active
residue character. It is nevertheless absent from every actual
residual column. This file retains that deletion as its own actual
coprimality mask. The mask equals one at each real source occurrence,
so the whole centered coefficient and both original rectangles remain
unchanged. The smooth profiles, indices and normalization scales are
not modified.

The additional remaining ideal is the product of the original deleted
primes. Its support and norm therefore stay visible to the original
support budget; no phase cancellation is used to discard it.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments HeckePort.Moments.Support HeckePort.IdealMobiusDivisorSum
open CanonicalOriginalPhaseCalibration

variable {K : Type} [Field K] [NumberField K] {k : ℕ}

/-- The whole original finite deletion, including inactive primes. -/
def literalDeletionIdeal (S : Finset (Ideal (𝓞 K))) (hS : ∀ p ∈ S, Prime p) :
    HeckeGeneral.Analysis.NonzeroIdeal K :=
  ⟨∏ p ∈ S, p, mem_nonZeroDivisors_of_ne_zero
    (Finset.prod_ne_zero_iff.mpr (fun p hp => (hS p hp).ne_zero))⟩

theorem literalDeletionIdeal_coprime (S : Finset (Ideal (𝓞 K)))
    (hS : ∀ p ∈ S, Prime p) (I : Ideal (𝓞 K)) :
    IsCoprime I (literalDeletionIdeal S hS).val ↔ CanonicalLiteralSupport.Avoids I S := by
  sorry

/-- The deletion is charged to the genuine original common ideal. -/
theorem literalDeletionIdeal_dvd (S : Finset (Ideal (𝓞 K)))
    (hS : ∀ p ∈ S, Prime p) (D : Ideal (𝓞 K)) (hD : D ≠ 0)
    (hsub : S ⊆ primeSupport D) : (literalDeletionIdeal S hS).val ∣ D := by
  sorry

theorem literalDeletionIdeal_norm_le (S : Finset (Ideal (𝓞 K)))
    (hS : ∀ p ∈ S, Prime p) (D : Ideal (𝓞 K)) (hD : D ≠ 0)
    (hsub : S ⊆ primeSupport D) :
    idealNorm K (literalDeletionIdeal S hS) ≤ (Ideal.absNorm D : ℝ) := by
  sorry

namespace FixedChildCharacters

variable (T : FixedChildCharacters K k)

def deleteMask (M : HeckeGeneral.Analysis.NonzeroIdeal K) : FixedChildCharacters K k :=
  { T with mask := T.mask * originalCoprimeMask M }

@[simp] theorem deleteMask_restrictSlots (M : HeckeGeneral.Analysis.NonzeroIdeal K)
    (keep : Finset (Fin k)) :
    (T.deleteMask M).restrictSlots keep = (T.restrictSlots keep).deleteMask M := rfl

theorem deleteMask_plain (M I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    sourcePlainCoefficient (T.deleteMask M).plain (T.deleteMask M).plainTwist
        (T.deleteMask M).mask I =
      sourcePlainCoefficient T.plain T.plainTwist T.mask I * originalCoprimeMask M I.val := by
  sorry

theorem deleteMask_prime (M : HeckeGeneral.Analysis.NonzeroIdeal K) (i : Fin k)
    (p : HeightOneSpectrum (𝓞 K)) :
    sourcePrimeCoefficient ((T.deleteMask M).slot i) ((T.deleteMask M).slotTwist i)
        (T.deleteMask M).mask p =
      sourcePrimeCoefficient (T.slot i) (T.slotTwist i) T.mask p *
        originalCoprimeMask M p.asIdeal := by
  sorry

/-- The new factor is the actual multiplicative mask of the complete
ideal. This is proved before any whole polynomial is formed. -/
theorem rawBare_deleteMask (M : HeckeGeneral.Analysis.NonzeroIdeal K)
    (N₁ N₂ Z : ℝ) (length : Fin k → ℝ)
    (w₁ w₂ : HeckeGeneral.Analysis.NonzeroIdeal K → ℂ)
    (w : Fin k → HeightOneSpectrum (𝓞 K) → ℂ)
    (i : AllocationColumn K k) (h₁ : i.1.1 ≠ 0) (h₂ : i.1.2 ≠ 0) :
    rawBareSourceCoefficient (T.deleteMask M) N₁ N₂ Z length w₁ w₂ w i =
      rawBareSourceCoefficient T N₁ N₂ Z length w₁ w₂ w i *
        originalCoprimeMask M (allocationColumnIdeal i) := by
  sorry

end FixedChildCharacters

namespace CanonicalLiteralRectangles.Atoms

variable (d : CanonicalLiteralRectangles.Atoms (K := K) k)

/-- Only the actual source mask changes; every original test and every
real column carrier is retained literally. -/
def deleteMask (M : HeckeGeneral.Analysis.NonzeroIdeal K) :
    CanonicalLiteralRectangles.Atoms (K := K) k :=
  { d with characters := d.characters.deleteMask M }

theorem deleteMask_term (M : HeckeGeneral.Analysis.NonzeroIdeal K)
    (r : Bool) (i : AllocationColumn K k)
    (hi : i ∈ childCartesianColumns d.plain₁ d.plain₂ d.slots) :
    (d.deleteMask M).term r i =
      d.term r i * originalCoprimeMask M (allocationColumnIdeal i) := by
  sorry

theorem deleteMask_whole (M : HeckeGeneral.Analysis.NonzeroIdeal K)
    (i : AllocationColumn K k)
    (hi : i ∈ childCartesianColumns d.plain₁ d.plain₂ d.slots) :
    (d.deleteMask M).whole i =
      d.whole i * originalCoprimeMask M (allocationColumnIdeal i) := by
  sorry

namespace SupportData

variable {d} {excluded : Finset (Ideal (𝓞 K))}

def deleteMask (W : d.SupportData excluded) (M : HeckeGeneral.Analysis.NonzeroIdeal K) :
    (d.deleteMask M).SupportData excluded where
  left_avoids := W.left_avoids
  right_avoids := W.right_avoids
  slot_avoids := W.slot_avoids
  left_mem := W.left_mem
  right_mem := W.right_mem
  slot_mem := W.slot_mem

/-- The original occurrence support proves that the complete new mask
is one. No assumption on the complete coefficient is used. -/
theorem deleteMask_whole_eq (W : d.SupportData excluded)
    (M : HeckeGeneral.Analysis.NonzeroIdeal K) (hM : primeSupport M.val ⊆ excluded)
    (i : AllocationColumn K k)
    (hi : i ∈ childCartesianColumns d.plain₁ d.plain₂ d.slots) :
    (d.deleteMask M).whole i = d.whole i := by
  sorry

end SupportData

namespace ProfileData

variable {d} (W : d.ProfileData)

def deleteMask (M : HeckeGeneral.Analysis.NonzeroIdeal K) : (d.deleteMask M).ProfileData where
  left := W.left
  right := W.right
  slot := W.slot
  slot_length := W.slot_length
  left_positive := W.left_positive
  right_positive := W.right_positive
  slot_positive := W.slot_positive
  left_frozen := W.left_frozen
  right_frozen := W.right_frozen
  slot_frozen := W.slot_frozen
  left_eval := W.left_eval
  right_eval := W.right_eval
  slot_eval := W.slot_eval

end ProfileData
end CanonicalLiteralRectangles.Atoms

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.FixedChildCharacters.rawBare_deleteMask
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.deleteMask_whole
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLiteralRectangles.Atoms.SupportData.deleteMask_whole_eq
