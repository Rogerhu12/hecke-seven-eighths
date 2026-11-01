import HeckeSkeleton.Moments.MOM_INV_STEP.AssignedMarkSource
import HeckeSkeleton.Moments.MOM_INV_STEP.ActualSecondTuple

/-!
# The actual doubled marks construct reconstruction choices

For one fixed arithmetic source, the two Poisson divisors range over the
powersets of their actual masks. Each squared extracted mark chooses two
independent prime tuples from its original lists. These finite choices
construct `ActualSecondTuple.Choices`; its original-list and divisibility
proofs are consequences of the actual mark expansion.

The finite choice map is injective. Both the signed expansion and its
reindexing retain the original individual coefficients and every divisor
choice. This concerns the assigned marks at one fixed arithmetic source;
it makes no identification of four historical columns with two fresh
inverse columns.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.ActualMarkChoices

open NumberField IsDedekindDomain AssignedMarkSource
open HeckeSkeleton.Moments.MOMInvStep
open scoped Classical BigOperators nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K] {Sector : Type*} {Jo Jn : ℕ}

abbrev PrimePair (J : ℕ) :=
  (Fin J → HeightOneSpectrum (𝓞 K)) × (Fin J → HeightOneSpectrum (𝓞 K))

def doubledLists {J : ℕ} (lists : Fin J → Finset (HeightOneSpectrum (𝓞 K))) :
    Fin (J + J) → Finset (HeightOneSpectrum (𝓞 K)) := Fin.addCases lists lists

variable (B : ActualSecondTuple.Source K Sector)
variable (oldLists : Fin Jo → Finset (HeightOneSpectrum (𝓞 K)))
variable (newLists : Fin Jn → Finset (HeightOneSpectrum (𝓞 K)))

def rawChoices : Finset
    ((Finset (HeightOneSpectrum (𝓞 K)) × Finset (HeightOneSpectrum (𝓞 K))) ×
      (PrimePair (K := K) Jo × PrimePair (K := K) Jn)) :=
  (B.firstMaskSupport.powerset ×ˢ B.secondCommonSupport.powerset) ×ˢ
    (pairedChoices oldLists B.oldExtracted ×ˢ pairedChoices newLists B.newExtracted)

abbrev PairedSource := ↥(rawChoices B oldLists newLists)

theorem oldPair_mem (a : PairedSource B oldLists newLists) :
    a.val.2.1 ∈ pairedChoices oldLists B.oldExtracted :=
  (Finset.mem_product.mp (Finset.mem_product.mp a.property).2).1

theorem newPair_mem (a : PairedSource B oldLists newLists) :
    a.val.2.2 ∈ pairedChoices newLists B.newExtracted :=
  (Finset.mem_product.mp (Finset.mem_product.mp a.property).2).2

/-- The two independent copies of each original slot supply the actual
reconstruction assignments. No child divisibility condition is assumed. -/
def reconstruction (a : PairedSource B oldLists newLists) :
    ActualSecondTuple.Choices B (doubledLists oldLists) (doubledLists newLists) := by
  have hd := Finset.mem_product.mp (Finset.mem_product.mp a.property).1
  exact {
    firstDivisor := ⟨a.val.1.1, Finset.mem_powerset.mp hd.1⟩
    secondDivisor := ⟨a.val.1.2, Finset.mem_powerset.mp hd.2⟩
    oldAssigned := fun i => ⟨pairedAssignment a.val.2.1 i,
      pairedAssignment_source oldLists B.oldExtracted a.val.2.1
        (oldPair_mem B oldLists newLists a) i⟩
    newAssigned := fun i => ⟨pairedAssignment a.val.2.2 i,
      pairedAssignment_source newLists B.newExtracted a.val.2.2
        (newPair_mem B oldLists newLists a) i⟩ }

theorem reconstruction_injective :
    Function.Injective (reconstruction B oldLists newLists) := by
  intro a b hab
  apply Subtype.ext
  apply Prod.ext
  · apply Prod.ext
    · exact congrArg (fun q => q.firstDivisor.val) hab
    · exact congrArg (fun q => q.secondDivisor.val) hab
  · apply Prod.ext
    · apply pairedAssignment_injective
      funext i
      exact congrArg (fun q => (q.oldAssigned i).val) hab
    · apply pairedAssignment_injective
      funext i
      exact congrArg (fun q => (q.newAssigned i).val) hab

def reconstructionRange : Finset
    (ActualSecondTuple.Choices B (doubledLists oldLists) (doubledLists newLists)) :=
  Finset.univ.image (reconstruction B oldLists newLists)

/-- Exact signed reindexing: no two independent prime choices or
Poisson divisors are silently merged. -/
theorem signed_source_reindex (w : PairedSource B oldLists newLists → ℂ) :
    (∑ a : PairedSource B oldLists newLists, w a) =
      ∑ q ∈ reconstructionRange B oldLists newLists,
        Function.extend (reconstruction B oldLists newLists) w (fun _ => 0) q := by
  rw [reconstructionRange, Finset.sum_image
    (fun _ _ _ _ h => reconstruction_injective B oldLists newLists h)]
  apply Finset.sum_congr rfl
  intro a ha
  exact ((reconstruction_injective B oldLists newLists).extend_apply _ _ _).symm

def scalar (aold : Fin Jo → Ideal (𝓞 K) → ℂ)
    (anew : Fin Jn → Ideal (𝓞 K) → ℂ) (a : PairedSource B oldLists newLists) : ℂ :=
  pairedWeight aold a.val.2.1 * pairedWeight anew a.val.2.2

theorem scalar_norm_le_one (aold : Fin Jo → Ideal (𝓞 K) → ℂ)
    (anew : Fin Jn → Ideal (𝓞 K) → ℂ)
    (ho : ∀ i, ∀ p ∈ oldLists i, ‖aold i p.asIdeal‖ ≤ 1)
    (hn : ∀ i, ∀ p ∈ newLists i, ‖anew i p.asIdeal‖ ≤ 1)
    (a : PairedSource B oldLists newLists) :
    ‖scalar B oldLists newLists aold anew a‖ ≤ 1 := by
  rw [scalar, norm_mul]
  calc
    _ ≤ 1 * 1 := mul_le_mul
      (pairedWeight_norm_le_one oldLists aold B.oldExtracted ho a.val.2.1
        (oldPair_mem B oldLists newLists a))
      (pairedWeight_norm_le_one newLists anew B.newExtracted hn a.val.2.2
        (newPair_mem B oldLists newLists a)) (norm_nonneg _) (by norm_num)
    _ = 1 := by norm_num

/-- Both actual squared extracted marks are expanded with their own
independent original prime choices. The signed divisor coefficient v
is retained, so it can include the original Poisson Moebius signs. -/
theorem actual_marks_expansion (aold : Fin Jo → Ideal (𝓞 K) → ℂ)
    (anew : Fin Jn → Ideal (𝓞 K) → ℂ)
    (v : Finset (HeightOneSpectrum (𝓞 K)) → Finset (HeightOneSpectrum (𝓞 K)) → ℂ) :
    (∑ d₁ ∈ B.firstMaskSupport.powerset, ∑ d₂ ∈ B.secondCommonSupport.powerset,
      v d₁ d₂ *
        ((‖divisorMark Finset.univ (fun i => (oldLists i).image HeightOneSpectrum.asIdeal)
          aold B.oldExtracted‖ ^ 2 : ℝ) : ℂ) *
        ((‖divisorMark Finset.univ (fun i => (newLists i).image HeightOneSpectrum.asIdeal)
          anew B.newExtracted‖ ^ 2 : ℝ) : ℂ)) =
      ∑ a : PairedSource B oldLists newLists,
        v a.val.1.1 a.val.1.2 * scalar B oldLists newLists aold anew a := by
  change _ = ∑ a : ↥(rawChoices B oldLists newLists),
    v a.val.1.1 a.val.1.2 * (pairedWeight aold a.val.2.1 * pairedWeight anew a.val.2.2)
  rw [Finset.sum_coe_sort (rawChoices B oldLists newLists)
    (fun a => v a.1.1 a.1.2 * (pairedWeight aold a.2.1 * pairedWeight anew a.2.2))]
  simp only [rawChoices, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro d₁ hd₁
  apply Finset.sum_congr rfl
  intro d₂ hd₂
  rw [divisorMark_norm_sq_eq_pairedChoices oldLists aold B.oldExtracted,
    divisorMark_norm_sq_eq_pairedChoices newLists anew B.newExtracted,
    Finset.mul_sum (pairedChoices oldLists B.oldExtracted) (pairedWeight aold) (v d₁ d₂),
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  ring

end HeckeSkeleton.Moments.MOM_INV_STEP.ActualMarkChoices

end
