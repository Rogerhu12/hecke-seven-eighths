import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstCommonTupleFibers
import HeckePort.Moments.Descent.IdealMasks

/-!
# The actual Boolean mask labels have a small-power cost

Each original mask prime is identified with its genuine exterior prime
ideal, injectively, and that prime divides the original mask ideal.
These are primitive prime identifications. They imply the cardinality
bound internally; no bound on the whole finite source carrier is input.
The resulting loss is a divisor small power, not the much larger norm
bound used for the physical truncation error.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open DedekindZetaZeroFree.LargeSieve HeckePort.Moments HeckePort.IdealMobiusDivisorSum
open UniqueFactorizationMonoid

variable {K : Type} [Field K] [NumberField K]
variable {α : Type*}

/-- Original single-prime identities, before a mask is expanded into
Boolean divisors. For S-integer masks `prime` is the original exterior
prime corresponding to each height-one S-integer prime. -/
structure OriginalMaskPrimeData (M : Finset α) (R : Ideal (𝓞 K)) where
  prime : α → HeightOneSpectrum (𝓞 K)
  injective : Set.InjOn prime (M : Set α)
  divides : ∀ a ∈ M, (prime a).asIdeal ∣ R

namespace OriginalMaskPrimeData

variable {M : Finset α} {R : Ideal (𝓞 K)}
variable (W : OriginalMaskPrimeData M R)

include W

theorem card_le_primeSupport (hR : R ≠ 0) : M.card ≤ (primeSupport R).card := by
  apply Finset.card_le_card_of_injOn (fun a => (W.prime a).asIdeal)
  · intro a ha
    exact (prime_mem_support_iff_dvd _ R (W.prime a).prime hR).mpr (W.divides a ha)
  · intro a ha b hb he
    exact W.injective ha hb (HeightOneSpectrum.asIdeal_injective he)

/-- Every actual subset label is charged by a different squarefree
divisor of the original mask ideal. The empty mask is included. -/
theorem powerset_card_le_divisorCount (hR : R ≠ 0) :
    M.powerset.card ≤ idealDivisorCount R := by
  have hdiv : 2 ^ (primeSupport R).card ≤ (idealDivisors R).card := by
    have hs : ((idealDivisors R).filter Squarefree).card ≤ (idealDivisors R).card :=
      Finset.card_filter_le _ _
    rw [squarefree_divisors_eq_image R hR, Finset.card_image_of_injOn,
      Finset.card_powerset] at hs
    · exact hs
    · intro S hS T hT he
      exact support_product_injective (Finset.mem_powerset.mp hS)
        (Finset.mem_powerset.mp hT) he
  rw [Finset.card_powerset]
  exact (Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (W.card_le_primeSupport hR)).trans hdiv

/-- Actual submasks inherit the original prime identification; no new
finite size estimate is supplied for a common-block submask. -/
def restrict (M' : Finset α) (hM : M' ⊆ M) : OriginalMaskPrimeData M' R where
  prime := W.prime
  injective := fun a ha b hb he => W.injective (hM ha) (hM hb) he
  divides := fun a ha => W.divides a (hM ha)

end OriginalMaskPrimeData

/-- A single small-power constant controls every original Boolean
mask with the stated raw norm window. It is chosen before the scale,
mask carrier, original ideal and per-prime identification. -/
theorem original_mask_labels_subpower (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Z : ℝ), 1 ≤ Z →
    ∀ {α : Type*} (M : Finset α) (R : Ideal (𝓞 K)), R ≠ 0 →
      (Ideal.absNorm R : ℝ) ≤ Z ^ B →
      OriginalMaskPrimeData M R → (M.powerset.card : ℝ) ≤ C * Z ^ ε := by
  obtain ⟨C, hC, hbound⟩ := support_tuple_multiplicity_subpower (K := K) 1 B ε hB hε
  refine ⟨C, hC, ?_⟩
  intro Z hZ α M R hR hN W
  have hc : (M.powerset.card : ℝ) ≤ (idealDivisorCount R : ℝ) := by
    exact_mod_cast W.powerset_card_le_divisorCount hR
  exact hc.trans (by simpa only [pow_one] using hbound Z hZ R hN)

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.OriginalMaskPrimeData.powerset_card_le_divisorCount
#print axioms HeckeSkeleton.Moments.EngineStep.original_mask_labels_subpower
