import HeckePort.Moments.Descent.Quotients

/-!
# Extracting a pair of divisors

Port of openai/math `OAI/NumberTheory/DirichletL/Descent/DivisorExtraction.lean`
(revision `fd4aeeb2`) from `ℤ[ω]` to `𝓞 K`.

`double_divisor_row_reindex` and `double_column_divisor_reindex` are verbatim.  In
`inverseCubicKernel_divisor_overlap_zero` the kernel is the abstract `CubicKernelAxioms` kernel
(its vanishing on non-coprime exterior pairs is `eq_zero_of_not_coprime`); "the primary generator
is nonzero" becomes the predicate `Ext`.
-/

noncomputable section

namespace HeckePort.Moments

open scoped NumberField Classical BigOperators
open DedekindZetaZeroFree.LargeSieve

variable {K : Type} [Field K] [NumberField K]

theorem inverseCubicKernel_divisor_overlap_zero {Ext : Ideal (𝓞 K) → Prop}
    {κ : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ} (hκ : CubicKernelAxioms Ext κ)
    (R r P c m : Ideal (𝓞 K))
    (hP : Ext P) (hcm : Ext (c * m))
    (hRP : R ∣ P) (hrc : r ∣ c) (hRr : ¬ IsCoprime R r) :
    κ P (c * m) = 0 := by
  apply hκ.eq_zero_of_not_coprime P (c * m) hP hcm
  intro hcop
  have hPc := hcop.of_isCoprime_of_dvd_right (dvd_mul_right c m)
  exact hRr ((hPc.of_isCoprime_of_dvd_left hRP).of_isCoprime_of_dvd_right hrc)

theorem double_divisor_row_reindex {A : Type*} [AddCommMonoid A]
    (rows : Finset (Ideal (𝓞 K))) (hrows : ∀ k ∈ rows, k ≠ ⊥)
    (R r : Ideal (𝓞 K)) (hRr : IsCoprime R r) (F : Ideal (𝓞 K) → A) :
    (∑ k ∈ rows, if (R, r) ∈ (idealDivisors k) ×ˢ (idealDivisors k) then F k else 0) =
      ∑ k ∈ quotientSupport (R * r) rows, F ((R * r) * k) := by
  have hsel (k : Ideal (𝓞 K)) (hk : k ∈ rows) :
      ((R, r) ∈ (idealDivisors k) ×ˢ (idealDivisors k)) ↔ R * r ∣ k := by
    rw [Finset.mem_product, mem_idealDivisors (hrows k hk), mem_idealDivisors (hrows k hk)]
    exact ⟨fun h => hRr.mul_dvd h.1 h.2,
      fun h => ⟨dvd_trans (dvd_mul_right R r) h, dvd_trans (dvd_mul_left r R) h⟩⟩
  calc
    _ = ∑ k ∈ rows, if R * r ∣ k then F k else 0 := by
      apply Finset.sum_congr rfl
      intro k hk
      simp only [hsel k hk]
    _ = ∑ k ∈ rows with R * r ∣ k, F k := (Finset.sum_filter _ _).symm
    _ = _ := sum_quotientSupport (R * r) rows F

theorem double_column_divisor_reindex {A : Type*} [AddCommMonoid A]
    (Pset cset : Finset (Ideal (𝓞 K))) (R r : Ideal (𝓞 K))
    (F : Ideal (𝓞 K) → Ideal (𝓞 K) → A) :
    (∑ P ∈ Pset, ∑ c ∈ cset, if R ∣ P ∧ r ∣ c then F P c else 0) =
      ∑ P ∈ quotientSupport R Pset, ∑ c ∈ quotientSupport r cset, F (R * P) (r * c) := by
  calc
    _ = ∑ P ∈ Pset with R ∣ P, ∑ c ∈ cset with r ∣ c, F P c := by
      simp only [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro P hP
      by_cases hd : R ∣ P
      · simp [hd]
      · simp [hd]
    _ = ∑ P ∈ quotientSupport R Pset, ∑ c ∈ cset with r ∣ c, F (R * P) c :=
      sum_quotientSupport R Pset (fun P => ∑ c ∈ cset with r ∣ c, F P c)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro P hP
      exact sum_quotientSupport r cset (F (R * P))

end HeckePort.Moments

end
