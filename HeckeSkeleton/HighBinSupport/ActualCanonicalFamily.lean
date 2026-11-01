import HeckeSkeleton.HighBinSupport.ActualCanonicalHighBin
import HeckeSkeleton.HighBinSupport.ActualDyadicRows

/-!
The actual retained HIGHBIN family, with one dependent finite index for
a dyadic shell and a nonempty canonical detector fiber.  Its block count
is proved from this very index type, and its row sum is exactly the
original moderate source sum.  Amplitude labels are introduced only
after this fixed arithmetic row partition.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.HighBinCanonicalFamily

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.HighBinActualEuler HeckeSkeleton.HighBinDetectorGeometry
open HeckeSkeleton.HighBinActualBoundaryGeometry HeckeSkeleton.HighBinCanonicalBoundary
open HeckeSkeleton.HighBinCanonical HeckeSkeleton.HighBinDyadicRows
open HighBinVerified.Dyadic
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (P : ProbeData K S) (ψ : HeckeCharacter K)
variable (Θ : Finset (HeckeCharacter K))
variable (B e : ℝ) (he : 0 < e) (hB : 51 / 100 ≤ B)
variable (hcommon : ∀ u : FrequencyRow K S, ∀ height : ℝ,
  rowZeroBelow K S ψ Θ P (arithmeticHighEulerData K S P ψ) u height B)

/-- Only nonempty detector fibers of the literal dyadic source survive. -/
abbrev CanonicalFamilyIndex (Z T κ upper : ℝ) :=
  Σ j : Fin (shellCount Z (1 / 16) upper),
    CanonicalBlockIndex K S P ψ Θ (moderateSource K S Z upper)
      B e he hB hcommon Z T κ (shellExponent Z (1 / 16) j.val)

def canonicalFamilyRows (Z T κ upper : ℝ)
    (b : CanonicalFamilyIndex K S P ψ Θ B e he hB hcommon Z T κ upper) :
    Finset (FrequencyRow K S) :=
  canonicalRows K S P ψ Θ (moderateSource K S Z upper)
    B e he hB hcommon Z T κ (shellExponent Z (1 / 16) b.1.val) b.2.val

theorem canonicalFamilyRows_nonempty (Z T κ upper : ℝ)
    (b : CanonicalFamilyIndex K S P ψ Θ B e he hB hcommon Z T κ upper) :
    (canonicalFamilyRows K S P ψ Θ B e he hB hcommon Z T κ upper b).Nonempty :=
  canonicalRows_nonempty K S P ψ Θ (moderateSource K S Z upper)
    B e he hB hcommon Z T κ (shellExponent Z (1 / 16) b.1.val) b.2

/-- The count is a property of the actual dependent index type. -/
theorem canonicalFamilyIndex_card (Z T κ upper : ℝ) :
    Fintype.card (CanonicalFamilyIndex K S P ψ Θ B e he hB hcommon Z T κ upper) ≤
      shellCount Z (1 / 16) upper * (detectorDepth e + 1) ^ 2 := by
  rw [Fintype.card_sigma]
  calc
    _ ≤ ∑ _j : Fin (shellCount Z (1 / 16) upper), (detectorDepth e + 1) ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      simpa only [CanonicalBlockIndex, Fintype.card_coe] using
        canonicalChoices_card K S P ψ Θ (moderateSource K S Z upper)
          B e he hB hcommon Z T κ (shellExponent Z (1 / 16) j.val)
    _ = _ := by simp

/-- Every positive scale loss absorbs the literal retained block count,
with height degree zero. -/
theorem canonicalFamilyIndex_subpower {Z upper η : ℝ} (T κ : ℝ)
    (hZ : 1 ≤ Z) (hupper : 1 / 16 ≤ upper) (hη : 0 < η) :
    (Fintype.card (CanonicalFamilyIndex K S P ψ Θ B e he hB hcommon Z T κ upper) : ℝ) ≤
      (((detectorDepth e + 1 : ℕ) : ℝ) ^ 2 *
        (2 + ((upper - 1 / 16) / Real.log 2) / η)) * Z ^ η := by
  have hc :
      (Fintype.card (CanonicalFamilyIndex K S P ψ Θ B e he hB hcommon Z T κ upper) : ℝ) ≤
        (shellCount Z (1 / 16) upper : ℝ) * ((detectorDepth e + 1 : ℕ) : ℝ) ^ 2 := by
    exact_mod_cast canonicalFamilyIndex_card K S P ψ Θ B e he hB hcommon Z T κ upper
  apply hc.trans
  calc
    _ ≤ ((2 + ((upper - 1 / 16) / Real.log 2) / η) * Z ^ η) *
        ((detectorDepth e + 1 : ℕ) : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right (shellCount_subpower hZ hupper hη) (by positivity)
    _ = _ := by ring

/-- Removing empty detector choices changes neither coverage nor the
source sum. The last shell remains restricted by the original cutoff. -/
theorem sum_canonicalFamilyRows (Z T κ upper : ℝ) (hZ : 1 < Z)
    (value : FrequencyRow K S → ℂ) :
    (∑ b : CanonicalFamilyIndex K S P ψ Θ B e he hB hcommon Z T κ upper,
      ∑ u ∈ canonicalFamilyRows K S P ψ Θ B e he hB hcommon Z T κ upper b, value u) =
      ∑ u ∈ moderateSource K S Z upper, value u := by
  rw [Fintype.sum_sigma]
  change (∑ j : Fin (shellCount Z (1 / 16) upper),
    ∑ k : ↥(canonicalChoices K S P ψ Θ (moderateSource K S Z upper)
      B e he hB hcommon Z T κ (shellExponent Z (1 / 16) j.val)),
      ∑ u ∈ canonicalRows K S P ψ Θ (moderateSource K S Z upper)
        B e he hB hcommon Z T κ (shellExponent Z (1 / 16) j.val) k.val, value u) = _
  calc
    _ = ∑ j : Fin (shellCount Z (1 / 16) upper),
        ∑ u ∈ maskedShellRows K S (moderateSource K S Z upper) Z
          (shellExponent Z (1 / 16) j.val), value u := by
      apply Finset.sum_congr rfl
      intro j _
      refine
        (Finset.sum_coe_sort
          (canonicalChoices K S P ψ Θ (moderateSource K S Z upper)
            B e he hB hcommon Z T κ (shellExponent Z (1 / 16) j.val))
          (fun k : DetectorIndex (detectorDepth e) =>
            ∑ u ∈ canonicalRows K S P ψ Θ (moderateSource K S Z upper)
              B e he hB hcommon Z T κ (shellExponent Z (1 / 16) j.val) k,
              value u)).trans ?_
      exact sum_retainedChoices K S P ψ Θ (arithmeticHighEulerData K S P ψ)
        B e (2 * HighBinVerified.NormForm.internalHeight Z T κ) he hB hcommon
        (maskedShellRows K S (moderateSource K S Z upper) Z
          (shellExponent Z (1 / 16) j.val)) value
    _ = _ := sum_maskedShellRows K S Z upper hZ value

end HeckeSkeleton.HighBinCanonicalFamily

#print axioms HeckeSkeleton.HighBinCanonicalFamily.canonicalFamilyIndex_subpower
#print axioms HeckeSkeleton.HighBinCanonicalFamily.sum_canonicalFamilyRows
