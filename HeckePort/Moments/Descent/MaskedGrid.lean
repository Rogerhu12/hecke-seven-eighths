import HeckePort.Moments.Descent.ExtractedGrid

/-!
# Masked grid rows

Port of openai/math `OAI/NumberTheory/DirichletL/Descent/MaskedGrid.lean`
(revision `fd4aeeb2`) from `ℤ[ω]` to `𝓞 K`, with the abstract quadratic row `q` and cubic kernel
`κ` (`CubicKernelAxioms Ext κ`) of `Descent/ExtractedGrid`; "the primary generator is nonzero" is
`Ext`.  The divisor-count bound is the upstream `ideal_divisor_count_le_rpow`.
-/

noncomputable section

namespace HeckePort.Moments

open scoped NumberField Classical BigOperators
open UniqueFactorizationMonoid DedekindZetaZeroFree.LargeSieve HeckePort.IdealMobiusDivisorSum

variable {K : Type} [Field K] [NumberField K]

def maskedGridHybridRow (q κ : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ) (T : Grid K)
    (Pset : Finset (Ideal (𝓞 K))) (a : Ideal (𝓞 K) → ℂ)
    (beta : Ideal (𝓞 K) → Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (t k : Ideal (𝓞 K)) : ℂ :=
  ∑ u ∈ T, ∑ P ∈ Pset, (if IsCoprime k (P * u.2) then 1 else 0) *
    (a P / (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ) * beta u.2 u.1.1 u.1.2 *
      (q k (u.1.1 * u.1.2) * κ P (u.2 * u.1.1)) *
        (if IsCoprime P (u.1.2 * t) then 1 else 0))

theorem maskedGridHybridRow_mobius (q κ : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ) (T : Grid K)
    (Pset : Finset (Ideal (𝓞 K)))
    (a : Ideal (𝓞 K) → ℂ) (beta : Ideal (𝓞 K) → Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (t k : Ideal (𝓞 K)) (hk : k ≠ ⊥) :
    maskedGridHybridRow q κ T Pset a beta t k =
      ∑ D ∈ (idealDivisors k) ×ˢ (idealDivisors k),
        ((moebius D.1 : ℂ) * (moebius D.2 : ℂ)) *
          gridDivisorHybridBlock q κ T Pset a beta t k D.1 D.2 := by
  have hm (P c : Ideal (𝓞 K)) :
      (if IsCoprime k (P * c) then (1 : ℂ) else 0) =
      ∑ D ∈ (idealDivisors k) ×ˢ (idealDivisors k),
        if D.1 ∣ P ∧ D.2 ∣ c then (moebius D.1 : ℂ) * (moebius D.2 : ℂ) else 0 := by
    rw [hybrid_double_mask_mobius k P c hk, Finset.sum_product]
  unfold maskedGridHybridRow
  simp_rw [hm, Finset.sum_mul]
  conv_lhs =>
    arg 2
    ext u
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro D hD
  unfold gridDivisorHybridBlock
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  by_cases hrc : D.2 ∣ u.2
  · simp only [hrc, ite_true, and_true, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro P hP
    by_cases hRP : D.1 ∣ P <;> simp [hRP]
  · simp [hrc]

theorem gridDivisorHybridBlock_zero_of_not_coprime {Ext : Ideal (𝓞 K) → Prop}
    {q κ : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ} (hκ : CubicKernelAxioms Ext κ)
    (T : Grid K) (Pset : Finset (Ideal (𝓞 K)))
    (a : Ideal (𝓞 K) → ℂ) (beta : Ideal (𝓞 K) → Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (t k R r : Ideal (𝓞 K)) (hRr : ¬ IsCoprime R r)
    (hP : ∀ P ∈ Pset, Ext P)
    (hT : ∀ u ∈ T, Ext (u.2 * u.1.1)) :
    gridDivisorHybridBlock q κ T Pset a beta t k R r = 0 := by
  unfold gridDivisorHybridBlock
  apply Finset.sum_eq_zero
  intro u hu
  by_cases hrc : r ∣ u.2
  · simp only [hrc, ite_true]
    apply Finset.sum_eq_zero
    intro P hPP
    by_cases hRP : R ∣ P
    · simp only [hRP, ite_true]
      rw [inverseCubicKernel_divisor_overlap_zero hκ R r P u.2 u.1.1
        (hP P hPP) (hT u hu) hRP hrc hRr]
      simp
    · simp only [hRP, ite_false]
  · simp only [hrc, ite_false]

theorem maskedGridHybridRow_divisor_energy (q κ : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ A : ℝ, 1 ≤ A →
    ∀ (rows : Finset (Ideal (𝓞 K))) (T : Grid K) (Pset : Finset (Ideal (𝓞 K)))
      (a : Ideal (𝓞 K) → ℂ) (beta : Ideal (𝓞 K) → Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
      (t : Ideal (𝓞 K)),
      (∀ k ∈ rows, k ≠ ⊥ ∧ (Ideal.absNorm k : ℝ) ≤ A) →
      (∑ k ∈ rows, ‖maskedGridHybridRow q κ T Pset a beta t k‖ ^ 2) ≤
        C * A ^ ε *
          ∑ D ∈ rows.biUnion (fun k => (idealDivisors k) ×ˢ (idealDivisors k)),
            ∑ k ∈ rows, if D ∈ (idealDivisors k) ×ˢ (idealDivisors k) then
              ‖gridDivisorHybridBlock q κ T Pset a beta t k D.1 D.2‖ ^ 2 else 0 := by
  obtain ⟨C, hC1, hdiv⟩ := ideal_divisor_count_le_rpow K (ε / 2) (by positivity)
  have hC : 0 < C := zero_lt_one.trans_le hC1
  refine ⟨C ^ 2, pow_pos hC 2, ?_⟩
  intro A hA rows T Pset a beta t hrows
  have he (k : Ideal (𝓞 K)) (hk : k ∈ rows) :=
    maskedGridHybridRow_mobius q κ T Pset a beta t k (hrows k hk).1
  simp_rw [Finset.sum_congr rfl (fun k hk => congrArg (fun z : ℂ => ‖z‖ ^ 2) (he k hk))]
  apply finite_expansion_energy rows
    (rows.biUnion (fun k => (idealDivisors k) ×ˢ (idealDivisors k)))
    (fun k => (idealDivisors k) ×ˢ (idealDivisors k))
    (fun _ D => (moebius D.1 : ℂ) * (moebius D.2 : ℂ))
    (fun k D => gridDivisorHybridBlock q κ T Pset a beta t k D.1 D.2) (C ^ 2 * A ^ ε)
  · intro k hk D hD
    exact Finset.mem_biUnion.mpr ⟨k, hk, hD⟩
  · intro k hk D hD
    rw [norm_mul]
    calc
      _ ≤ 1 * 1 := mul_le_mul
        (norm_ideal_moebius_le_one D.1)
        (norm_ideal_moebius_le_one D.2) (norm_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  · intro k hk
    have hd := (hdiv k).trans
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (hrows k hk).2 (by positivity)) hC.le)
    calc
      _ = ((idealDivisors k).card : ℝ) ^ 2 := by simp [Finset.card_product, pow_two]
      _ ≤ (C * A ^ (ε / 2)) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hd 2
      _ = C ^ 2 * A ^ ε := by
        rw [mul_pow, pow_two (A ^ (ε / 2)), ← Real.rpow_add (by linarith : 0 < A)]
        congr 1
        congr 1
        ring

end HeckePort.Moments

end
