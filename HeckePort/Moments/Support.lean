import HeckePort.Moments.SupportedCorrelation
import HeckePort.Moments.ReflectionDeletion

/-!
# Extracting the common prime support

Port of openai/math `OAI/NumberTheory/DirichletL/Moments/Support.lean` (revision `fd4aeeb2`)
from `ℤ[ω]` to `𝓞 K`.

`supportExtract I S` / `supportResidual I S` are the S0 `extract S I` / `residual S I` of
`ReflectionDeletion` (the `S`-part and the prime-to-`S` part of an ideal).  The lemmas on
factors, support, counts, multiplicativity and the extracted/residual coprimality are ported
verbatim in shape.

`idealCorrelation_complete_extraction` unfolds `idealCorrelation I J = actualCorrelation
(primaryGenerator I) (primaryGenerator J)` through `actual_complete_common_support`.  The
correlation of two ideals is the abstract family `corr : Ideal → Ideal → A → ℂ` (over a general
field: the correlation of the generator characters, through `D.generator`) and the common
support formula for coprime pieces (openai `actual_complete_common_support`) is the hypothesis
`hcommon`; the extraction is then the formal consequence below (it supplies the coprimality
of the pieces and the reconstruction `D * A = I`).  The notion `Supported I` (all primes
above the bad prime) is not used.
-/

noncomputable section

namespace HeckePort.Moments.Support

open scoped NumberField Classical BigOperators
open UniqueFactorizationMonoid HeckePort.IdealMobiusDivisorSum HeckePort.Moments

variable {K : Type*} [Field K] [NumberField K]

abbrev supportExtract (I : Ideal (𝓞 K)) (S : Finset (Ideal (𝓞 K))) : Ideal (𝓞 K) := extract S I

abbrev supportResidual (I : Ideal (𝓞 K)) (S : Finset (Ideal (𝓞 K))) : Ideal (𝓞 K) := residual S I

theorem supportExtract_factors (I : Ideal (𝓞 K)) (S : Finset (Ideal (𝓞 K))) :
    normalizedFactors (supportExtract I S) = (normalizedFactors I).filter (fun P => P ∈ S) :=
  extract_factors S I

theorem supportResidual_factors (I : Ideal (𝓞 K)) (S : Finset (Ideal (𝓞 K))) :
    normalizedFactors (supportResidual I S) = (normalizedFactors I).filter (fun P => P ∉ S) :=
  residual_factors S I

theorem supportExtract_ne_zero (I : Ideal (𝓞 K)) (S : Finset (Ideal (𝓞 K))) :
    supportExtract I S ≠ ⊥ := extract_ne_zero S I

theorem supportResidual_ne_zero (I : Ideal (𝓞 K)) (S : Finset (Ideal (𝓞 K))) :
    supportResidual I S ≠ ⊥ := residual_ne_zero S I

theorem support_reconstruct (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (S : Finset (Ideal (𝓞 K))) :
    supportExtract I S * supportResidual I S = I :=
  reconstruct S ⟨I, hI⟩

theorem supportExtract_support (I : Ideal (𝓞 K)) (S : Finset (Ideal (𝓞 K))) :
    primeSupport (supportExtract I S) = primeSupport I ∩ S := by
  ext P
  simp [primeSupport, supportExtract_factors]

theorem supportResidual_support (I : Ideal (𝓞 K)) (S : Finset (Ideal (𝓞 K))) :
    primeSupport (supportResidual I S) = primeSupport I \ S := by
  ext P
  simp [primeSupport, supportResidual_factors]

theorem supportExtract_count (I P : Ideal (𝓞 K)) (S : Finset (Ideal (𝓞 K))) :
    (normalizedFactors (supportExtract I S)).count P =
      if P ∈ S then (normalizedFactors I).count P else 0 := by
  rw [supportExtract_factors, Multiset.count_filter]

theorem supportResidual_count (I P : Ideal (𝓞 K)) (S : Finset (Ideal (𝓞 K))) :
    (normalizedFactors (supportResidual I S)).count P =
      if P ∈ S then 0 else (normalizedFactors I).count P := by
  rw [supportResidual_factors, Multiset.count_filter]
  split_ifs <;> rfl

theorem extracted_residual_coprime (I J : Ideal (𝓞 K)) (S : Finset (Ideal (𝓞 K))) :
    IsCoprime (supportExtract I S) (supportResidual J S) := by
  apply (primeSupport_disjoint_iff
    (supportExtract_ne_zero I S) (supportResidual_ne_zero J S)).mp
  rw [supportExtract_support, supportResidual_support]
  exact Finset.disjoint_left.mpr (by
    intro P hP hQ
    exact (Finset.mem_sdiff.mp hQ).2 (Finset.mem_inter.mp hP).2)

theorem common_support_residual_coprime (I J : Ideal (𝓞 K)) :
    let S := primeSupport I ∩ primeSupport J
    IsCoprime (supportResidual I S) (supportResidual J S) := by
  dsimp only
  apply (primeSupport_disjoint_iff
    (supportResidual_ne_zero I _) (supportResidual_ne_zero J _)).mp
  rw [supportResidual_support, supportResidual_support]
  apply Finset.disjoint_left.mpr
  intro P hP hQ
  exact (Finset.mem_sdiff.mp hP).2
    (Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp hP).1, (Finset.mem_sdiff.mp hQ).1⟩)

theorem supportExtract_mul (I J : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hJ : J ≠ ⊥)
    (S : Finset (Ideal (𝓞 K))) :
    supportExtract (I * J) S = supportExtract I S * supportExtract J S := by
  simp only [extract, normalizedFactors_mul hI hJ, Multiset.filter_add, Multiset.prod_add]

theorem supportResidual_mul (I J : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hJ : J ≠ ⊥)
    (S : Finset (Ideal (𝓞 K))) :
    supportResidual (I * J) S = supportResidual I S * supportResidual J S := by
  simp only [residual, normalizedFactors_mul hI hJ, Multiset.filter_add, Multiset.prod_add]

theorem supportExtract_prime (P : Ideal (𝓞 K)) (hP : Prime P) (S : Finset (Ideal (𝓞 K))) :
    supportExtract P S = if P ∈ S then P else 1 := by
  have hf : normalizedFactors P = {P} := by
    simpa using (normalizedFactors_prod_of_prime (m := ({P} : Multiset (Ideal (𝓞 K))))
      (by intro Q hQ; simpa only [Multiset.mem_singleton.mp hQ] using hP))
  simp only [extract, hf, Multiset.filter_singleton]
  split_ifs <;> simp

theorem supportResidual_prime (P : Ideal (𝓞 K)) (hP : Prime P) (S : Finset (Ideal (𝓞 K))) :
    supportResidual P S = if P ∈ S then 1 else P := by
  have hf : normalizedFactors P = {P} := by
    simpa using (normalizedFactors_prod_of_prime (m := ({P} : Multiset (Ideal (𝓞 K))))
      (by intro Q hQ; simpa only [Multiset.mem_singleton.mp hQ] using hP))
  simp only [residual, hf, Multiset.filter_singleton]
  split_ifs <;> simp_all

theorem shared_prime_slot_freeze (P I : Ideal (𝓞 K)) (hP : Prime P) (hI : I ≠ ⊥)
    (S : Finset (Ideal (𝓞 K))) (hPS : P ∈ S) :
    supportExtract (P * I) S = P * supportExtract I S ∧
      supportResidual (P * I) S = supportResidual I S := by
  rw [supportExtract_mul P I hP.ne_zero hI S, supportResidual_mul P I hP.ne_zero hI S,
    supportExtract_prime P hP S, supportResidual_prime P hP S]
  simp only [hPS, ite_true, one_mul, and_self]

theorem supportExtract_prod {ι : Type*} (T : Finset ι) (p : ι → Ideal (𝓞 K))
    (hp : ∀ i ∈ T, p i ≠ ⊥) (S : Finset (Ideal (𝓞 K))) :
    supportExtract (∏ i ∈ T, p i) S = ∏ i ∈ T, supportExtract (p i) S := by
  induction T using Finset.cons_induction with
  | empty =>
    simp only [Finset.prod_empty, extract, normalizedFactors_one, Multiset.filter_zero,
      Multiset.prod_zero]
  | cons i T hi ih =>
    rw [Finset.prod_cons, Finset.prod_cons,
      supportExtract_mul _ _ (hp i (Finset.mem_cons_self _ _))
        (Finset.prod_ne_zero_iff.mpr (fun j hj => hp j (Finset.mem_cons_of_mem hj))) S,
      ih (fun j hj => hp j (Finset.mem_cons_of_mem hj))]

theorem supportResidual_prod {ι : Type*} (T : Finset ι) (p : ι → Ideal (𝓞 K))
    (hp : ∀ i ∈ T, p i ≠ ⊥) (S : Finset (Ideal (𝓞 K))) :
    supportResidual (∏ i ∈ T, p i) S = ∏ i ∈ T, supportResidual (p i) S := by
  induction T using Finset.cons_induction with
  | empty =>
    simp only [Finset.prod_empty, residual, normalizedFactors_one, Multiset.filter_zero,
      Multiset.prod_zero]
  | cons i T hi ih =>
    rw [Finset.prod_cons, Finset.prod_cons,
      supportResidual_mul _ _ (hp i (Finset.mem_cons_self _ _))
        (Finset.prod_ne_zero_iff.mpr (fun j hj => hp j (Finset.mem_cons_of_mem hj))) S,
      ih (fun j hj => hp j (Finset.mem_cons_of_mem hj))]

/-- openai `idealCorrelation_complete_extraction`, with the common support formula for coprime
pieces as the hypothesis `hcommon`.  Here `corr I J j` is the correlation of the ideals `I, J`,
`φ A E` the reciprocity phase and `ψ A j` the residue character value of `j` modulo `A`. -/
theorem idealCorrelation_complete_extraction (corr : Ideal (𝓞 K) → Ideal (𝓞 K) → 𝓞 K → ℂ)
    (φ : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ) (ψ : Ideal (𝓞 K) → 𝓞 K → ℂ)
    (hcommon : ∀ D E A B : Ideal (𝓞 K), D ≠ ⊥ → E ≠ ⊥ → A ≠ ⊥ → B ≠ ⊥ →
      IsCoprime (D * E) A → IsCoprime (D * E) B → IsCoprime A B → ∀ j,
      corr (D * A) (E * B) j = corr D E j * φ A E * star (φ B D) * φ A B *
        ψ A j * star (ψ B (-j)))
    (I J : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hJ : J ≠ ⊥) (j : 𝓞 K) :
    let S := primeSupport I ∩ primeSupport J
    let D := supportExtract I S
    let E := supportExtract J S
    let A := supportResidual I S
    let B := supportResidual J S
    corr I J j = corr D E j * φ A E * star (φ B D) * φ A B * ψ A j * star (ψ B (-j)) := by
  intro S D E A B
  have hDA : D * A = I := support_reconstruct I hI S
  have hEB : E * B = J := support_reconstruct J hJ S
  have hcpA : IsCoprime (D * E) A :=
    (extracted_residual_coprime I I S).mul_left (extracted_residual_coprime J I S)
  have hcpB : IsCoprime (D * E) B :=
    (extracted_residual_coprime I J S).mul_left (extracted_residual_coprime J J S)
  have hcpAB : IsCoprime A B := common_support_residual_coprime I J
  have h := hcommon D E A B (supportExtract_ne_zero I S) (supportExtract_ne_zero J S)
    (supportResidual_ne_zero I S) (supportResidual_ne_zero J S) hcpA hcpB hcpAB j
  rwa [hDA, hEB] at h

end HeckePort.Moments.Support

end
