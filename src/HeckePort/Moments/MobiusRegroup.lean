import HeckePort.Moments.SupportedCorrelation

/-!
# Möbius regrouping of coprimality masks over finite families

Port of openai/math `OAI/NumberTheory/DirichletL/Moments/MobiusRegroup.lean`
(revision `fd4aeeb2`) from `ℤ[ω]` to `𝓞 K`.

`divisorPool`, `mobius_on_pool` and `finite_pair_mobius` are verbatim in shape.  In
`finite_correlation_mobius` the correlation `actualCorrelation (D * a i) (E * b j)` and its
common-support extension `completeSupportExtension` are abstract families `Corr i j`,
`Ext i j`, linked by the hypothesis `hext` (openai `actual_complete_common_support`, here the
conclusion of `SupportedCorrelation.supported_complete_common_support`), and the principal ideals
`Ideal.span {a i}` are arbitrary ideals `A i`, `B j`.
-/

noncomputable section

namespace HeckePort.Moments.MobiusRegroup

open scoped NumberField BigOperators Classical
open UniqueFactorizationMonoid DedekindZetaZeroFree.LargeSieve HeckePort.CenteredMomentMask

variable {K : Type*} [Field K] [NumberField K]

def divisorPool {β : Type*} (T : Finset β) (B : β → Ideal (𝓞 K)) : Finset (Ideal (𝓞 K)) :=
  T.biUnion (fun j => idealDivisors (B j))

theorem mobius_on_pool {β : Type*} (T : Finset β) (B : β → Ideal (𝓞 K))
    (hB : ∀ j ∈ T, B j ≠ ⊥) (j : β) (hj : j ∈ T) (I : Ideal (𝓞 K)) :
    (if IsCoprime I (B j) then (1 : ℂ) else 0) =
      ∑ D ∈ divisorPool T B, if D ∣ I ∧ D ∣ B j then (moebius D : ℂ) else 0 := by
  rw [ideal_coprime_mobius I (B j) (hB j hj)]
  have hsub : idealDivisors (B j) ⊆ divisorPool T B :=
    fun D hD => Finset.mem_biUnion.mpr ⟨j, hj, hD⟩
  calc
    _ = ∑ D ∈ idealDivisors (B j), if D ∣ I ∧ D ∣ B j then (moebius D : ℂ) else 0 := by
      apply Finset.sum_congr rfl
      intro D hD
      simp only [(mem_idealDivisors (hB j hj)).mp hD, and_true]
    _ = _ := Finset.sum_subset hsub (by
      intro D hD hn
      have hnd : ¬ D ∣ B j := fun hd => hn ((mem_idealDivisors (hB j hj)).mpr hd)
      simp only [hnd, and_false, ite_false])

theorem finite_pair_mobius {α β : Type*} (S : Finset α) (T : Finset β)
    (A : α → Ideal (𝓞 K)) (B : β → Ideal (𝓞 K)) (hB : ∀ j ∈ T, B j ≠ ⊥)
    (F : α → β → ℂ) :
    (∑ i ∈ S, ∑ j ∈ T, if IsCoprime (A i) (B j) then F i j else 0) =
      ∑ D ∈ divisorPool T B, (moebius D : ℂ) *
        ∑ i ∈ S, ∑ j ∈ T, if D ∣ A i ∧ D ∣ B j then F i j else 0 := by
  have ht (i : α) (j : β) (hj : j ∈ T) :
      (if IsCoprime (A i) (B j) then F i j else 0) =
        ∑ D ∈ divisorPool T B, (moebius D : ℂ) *
          (if D ∣ A i ∧ D ∣ B j then F i j else 0) := by
    have hm := congrArg (fun z : ℂ => z * F i j) (mobius_on_pool T B hB j hj (A i))
    simpa only [ite_mul, one_mul, zero_mul, Finset.sum_mul, mul_ite, mul_zero] using hm
  calc
    _ = ∑ i ∈ S, ∑ j ∈ T, ∑ D ∈ divisorPool T B, (moebius D : ℂ) *
        (if D ∣ A i ∧ D ∣ B j then F i j else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact ht i j hj
    _ = _ := by
      simp_rw [Finset.sum_comm (s := T) (t := divisorPool T B)]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro D hD
      simp only [Finset.mul_sum]

/-- openai `finite_correlation_mobius`, for abstract correlation `Corr` and its common-support
extension `Ext`. -/
theorem finite_correlation_mobius {α β : Type*} (S : Finset α) (T : Finset β)
    (A : α → Ideal (𝓞 K)) (B : β → Ideal (𝓞 K)) (hB : ∀ j ∈ T, B j ≠ ⊥)
    (Corr Ext : α → β → ℂ) (hext : ∀ i j, IsCoprime (A i) (B j) → Corr i j = Ext i j)
    (c : α → ℂ) (d : β → ℂ) (Kr : α → β → ℂ) :
    (∑ i ∈ S, ∑ j ∈ T,
      (if IsCoprime (A i) (B j) then Corr i j else 0) * (c i * star (d j)) * Kr i j) =
      ∑ L ∈ divisorPool T B, (moebius L : ℂ) *
        ∑ i ∈ S, ∑ j ∈ T,
          if L ∣ A i ∧ L ∣ B j then Ext i j * (c i * star (d j)) * Kr i j else 0 := by
  have he (i : α) (j : β) :
      (if IsCoprime (A i) (B j) then Corr i j else 0) * (c i * star (d j)) * Kr i j =
      if IsCoprime (A i) (B j) then Ext i j * (c i * star (d j)) * Kr i j else 0 := by
    by_cases hab : IsCoprime (A i) (B j)
    · simp only [hab, if_true, hext i j hab]
    · simp only [hab, if_false, zero_mul]
  simp_rw [he]
  exact finite_pair_mobius S T A B hB _

end HeckePort.Moments.MobiusRegroup

end
