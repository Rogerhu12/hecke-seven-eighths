module

public import HeckeSkeleton.Moments.MOM_INV_STEP.MarkPriority
public import HeckeSkeleton.Moments.MOM_INV_STEP.FixedTripleFibers

/-!
# Actual prime choices in a squared extracted mark

After the first Cauchy inequality, an extracted mark occurs as its norm
squared. Its two copies choose primes independently from the original
lists. This module expands that actual ideal-divisibility mark into its
finite choice source, retains the original individual coefficients, and
proves the original-list and extracted-factor conditions of every choice.

The resulting `Fin (J + J)` assignment can be appended to the old slot
assignment before the fresh inverse column is squared. No extra choice
multiplicity is silently erased and no residual column coefficient is
introduced by this reindexing.
-/

@[expose] public section

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.AssignedMarkSource

open NumberField IsDedekindDomain
open HeckeSkeleton.Moments.MOMInvStep
open scoped Classical BigOperators NumberField

variable {K : Type*} [Field K] [NumberField K] {J : ℕ}

def primeChoices (lists : Fin J → Finset (HeightOneSpectrum (𝓞 K)))
    (E : Ideal (𝓞 K)) : Finset (Fin J → HeightOneSpectrum (𝓞 K)) :=
  Fintype.piFinset fun i => (lists i).filter fun p => p.asIdeal ∣ E

theorem mem_primeChoices (lists : Fin J → Finset (HeightOneSpectrum (𝓞 K)))
    (E : Ideal (𝓞 K)) (q : Fin J → HeightOneSpectrum (𝓞 K)) :
    q ∈ primeChoices lists E ↔ ∀ i, q i ∈ lists i ∧ (q i).asIdeal ∣ E := by
  simp only [primeChoices, Fintype.mem_piFinset, Finset.mem_filter]

def choiceWeight (a : Fin J → Ideal (𝓞 K) → ℂ)
    (q : Fin J → HeightOneSpectrum (𝓞 K)) : ℂ := ∏ i, a i (q i).asIdeal

/-- This is the same literal divisibility mark used in the canonical
column, with the original prime ideals and original coefficients. -/
theorem divisorMark_eq_primeChoices
    (lists : Fin J → Finset (HeightOneSpectrum (𝓞 K)))
    (a : Fin J → Ideal (𝓞 K) → ℂ) (E : Ideal (𝓞 K)) :
    divisorMark Finset.univ (fun i => (lists i).image HeightOneSpectrum.asIdeal) a E =
      ∑ q ∈ primeChoices lists E, choiceWeight a q := by
  unfold divisorMark
  calc
    _ = ∏ i, ∑ p ∈ (lists i).filter (fun p => p.asIdeal ∣ E), a i p.asIdeal := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [Finset.sum_image (fun _ _ _ _ h => HeightOneSpectrum.asIdeal_injective h),
        Finset.sum_filter]
    _ = _ := Finset.prod_univ_sum _ _

def pairedChoices (lists : Fin J → Finset (HeightOneSpectrum (𝓞 K)))
    (E : Ideal (𝓞 K)) := primeChoices lists E ×ˢ primeChoices lists E

def pairedWeight (a : Fin J → Ideal (𝓞 K) → ℂ)
    (q : (Fin J → HeightOneSpectrum (𝓞 K)) × (Fin J → HeightOneSpectrum (𝓞 K))) : ℂ :=
  star (choiceWeight a q.1) * choiceWeight a q.2

theorem divisorMark_star_mul_eq_pairedChoices
    (lists : Fin J → Finset (HeightOneSpectrum (𝓞 K)))
    (a : Fin J → Ideal (𝓞 K) → ℂ) (E : Ideal (𝓞 K)) :
    star (divisorMark Finset.univ (fun i => (lists i).image HeightOneSpectrum.asIdeal) a E) *
      divisorMark Finset.univ (fun i => (lists i).image HeightOneSpectrum.asIdeal) a E =
        ∑ q ∈ pairedChoices lists E, pairedWeight a q := by
  calc
    _ = star (∑ q ∈ primeChoices lists E, choiceWeight a q) *
        (∑ q ∈ primeChoices lists E, choiceWeight a q) :=
      congrArg (fun z : ℂ => star z * z) (divisorMark_eq_primeChoices lists a E)
    _ = _ := by
      rw [pairedChoices, Finset.sum_product, star_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro q hq
      exact Finset.mul_sum _ _ _

theorem divisorMark_norm_sq_eq_pairedChoices
    (lists : Fin J → Finset (HeightOneSpectrum (𝓞 K)))
    (a : Fin J → Ideal (𝓞 K) → ℂ) (E : Ideal (𝓞 K)) :
    ((‖divisorMark Finset.univ
      (fun i => (lists i).image HeightOneSpectrum.asIdeal) a E‖ ^ 2 : ℝ) : ℂ) =
        ∑ q ∈ pairedChoices lists E, pairedWeight a q := by
  simpa only [Complex.sq_norm, Complex.normSq_eq_conj_mul_self, starRingEnd_apply] using
    divisorMark_star_mul_eq_pairedChoices lists a E

def pairedAssignment
    (q : (Fin J → HeightOneSpectrum (𝓞 K)) × (Fin J → HeightOneSpectrum (𝓞 K))) :
    Fin (J + J) → HeightOneSpectrum (𝓞 K) := Fin.addCases q.1 q.2

theorem pairedAssignment_injective :
    Function.Injective (pairedAssignment (K := K) (J := J)) := by
  intro q r h
  apply Prod.ext
  · funext i
    simpa only [pairedAssignment, Fin.addCases_left] using congrFun h (Fin.castAdd J i)
  · funext i
    simpa only [pairedAssignment, Fin.addCases_right] using congrFun h (Fin.natAdd J i)

/-- Each of the doubled slots still belongs to its original list and
divides the actual extracted ideal. These are precisely the source
conditions needed by the arithmetic reconstruction choices. -/
theorem pairedAssignment_source
    (lists : Fin J → Finset (HeightOneSpectrum (𝓞 K))) (E : Ideal (𝓞 K))
    (q : (Fin J → HeightOneSpectrum (𝓞 K)) × (Fin J → HeightOneSpectrum (𝓞 K)))
    (hq : q ∈ pairedChoices lists E) (i : Fin (J + J)) :
    pairedAssignment q i ∈
        (Fin.addCases lists lists i : Finset (HeightOneSpectrum (𝓞 K))) ∧
      (pairedAssignment q i).asIdeal ∣ E := by
  obtain ⟨hl, hr⟩ := Finset.mem_product.mp hq
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [pairedAssignment, Fin.addCases_left] using
      (mem_primeChoices lists E q.1).mp hl j
  · simpa only [pairedAssignment, Fin.addCases_right] using
      (mem_primeChoices lists E q.2).mp hr j

theorem choiceWeight_norm_le_one
    (lists : Fin J → Finset (HeightOneSpectrum (𝓞 K)))
    (a : Fin J → Ideal (𝓞 K) → ℂ) (E : Ideal (𝓞 K))
    (ha : ∀ i, ∀ p ∈ lists i, ‖a i p.asIdeal‖ ≤ 1)
    (q : Fin J → HeightOneSpectrum (𝓞 K)) (hq : q ∈ primeChoices lists E) :
    ‖choiceWeight a q‖ ≤ 1 := by
  rw [choiceWeight, norm_prod]
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
    (fun i _ => ha i (q i) ((mem_primeChoices lists E q).mp hq i).1)

theorem pairedWeight_norm_le_one
    (lists : Fin J → Finset (HeightOneSpectrum (𝓞 K)))
    (a : Fin J → Ideal (𝓞 K) → ℂ) (E : Ideal (𝓞 K))
    (ha : ∀ i, ∀ p ∈ lists i, ‖a i p.asIdeal‖ ≤ 1)
    (q : (Fin J → HeightOneSpectrum (𝓞 K)) × (Fin J → HeightOneSpectrum (𝓞 K)))
    (hq : q ∈ pairedChoices lists E) : ‖pairedWeight a q‖ ≤ 1 := by
  obtain ⟨hl, hr⟩ := Finset.mem_product.mp hq
  rw [pairedWeight, norm_mul, norm_star]
  calc
    _ ≤ 1 * 1 := mul_le_mul (choiceWeight_norm_le_one lists a E ha q.1 hl)
      (choiceWeight_norm_le_one lists a E ha q.2 hr) (norm_nonneg _) (by norm_num)
    _ = 1 := by norm_num

/-- The positive first-stage mark square has an exact signed finite
choice expansion before it is attached to the second Poisson source. -/
theorem first_cauchy_mark_expansion {ι : Type*} (T : Finset ι)
    (lists : Fin J → Finset (HeightOneSpectrum (𝓞 K)))
    (a : Fin J → Ideal (𝓞 K) → ℂ) (E : ι → Ideal (𝓞 K)) (w H : ι → ℂ) :
    (∑ x ∈ T, w x * ((‖divisorMark Finset.univ
      (fun i => (lists i).image HeightOneSpectrum.asIdeal) a (E x)‖ ^ 2 : ℝ) : ℂ) * H x) =
      ∑ x ∈ T, ∑ q ∈ pairedChoices lists (E x), (w x * pairedWeight a q) * H x := by
  apply Finset.sum_congr rfl
  intro x hx
  rw [divisorMark_norm_sq_eq_pairedChoices, Finset.mul_sum, Finset.sum_mul]

end HeckeSkeleton.Moments.MOM_INV_STEP.AssignedMarkSource

end
