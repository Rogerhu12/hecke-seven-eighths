import HeckeSkeleton.LowEnergy.OriginalRowNormalForm
import HeckeSkeleton.LowEnergy.IdealMass

/-!
# Inherited support and coefficient budgets for the actual normal form

The support fields below describe the actual unique square extraction.
They are arithmetic statements about a nonzero coefficient, not operator
or energy bounds. Both product supports and the weighted budget are
derived before a coefficient support is removed from a positive sum.
-/

namespace HeckeSkeleton.LowEnergy.KeepOriginalRow

open NumberField Ideal UniqueFactorizationMonoid
open scoped BigOperators NumberField Classical
noncomputable section

variable {K : Type*} [Field K] [NumberField K]

structure ReconstructedSupport
    (beta : Ideal (𝓞 K) → Ideal (𝓞 K) → Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (N B : ℝ) : Prop where
  n_squarefree : ∀ t c m h, beta t c m h ≠ 0 → Squarefree (c * m)
  g_squarefree : ∀ t c m h, beta t c m h ≠ 0 → Squarefree (c * h)
  residual_coprime : ∀ t c m h, beta t c m h ≠ 0 → IsCoprime m h
  square_nezero : ∀ t c m h, beta t c m h ≠ 0 → t ≠ ⊥
  n_bound : ∀ t c m h, beta t c m h ≠ 0 → (Ideal.absNorm (c * m) : ℝ) ≤ N
  b_bound : ∀ t c m h, beta t c m h ≠ 0 →
    (Ideal.absNorm ((c * h) * t ^ 2) : ℝ) ≤ B

theorem ideal_norm_le_of_dvd (I J : Ideal (𝓞 K)) (hJ : J ≠ ⊥) (hIJ : I ∣ J) :
    (Ideal.absNorm I : ℝ) ≤ (Ideal.absNorm J : ℝ) := by
  exact_mod_cast Nat.le_of_dvd
    (Nat.pos_of_ne_zero (fun h => hJ (Ideal.absNorm_eq_zero_iff.mp h)))
    (map_dvd Ideal.absNorm hIJ)

theorem quotientSupport_nezero (D : Ideal (𝓞 K)) (hD : D ≠ ⊥)
    (s : Finset (Ideal (𝓞 K))) (hs : ∀ P ∈ s, P ≠ ⊥)
    (P : Ideal (𝓞 K)) (hP : P ∈ quotientSupport D s) : P ≠ ⊥ := by
  have h := hs (D * P) ((mem_quotientSupport D P hD s).mp hP)
  exact (mul_ne_zero_iff.mp h).2

theorem quotientSupport_squarefree (D : Ideal (𝓞 K)) (hD : D ≠ ⊥)
    (s : Finset (Ideal (𝓞 K))) (hs : ∀ P ∈ s, Squarefree P)
    (P : Ideal (𝓞 K)) (hP : P ∈ quotientSupport D s) : Squarefree P := by
  have h := hs (D * P) ((mem_quotientSupport D P hD s).mp hP)
  exact Squarefree.squarefree_of_dvd (dvd_mul_left P D) h

theorem quotientSupport_norm_le (D : Ideal (𝓞 K)) (hD : D ≠ ⊥)
    (s : Finset (Ideal (𝓞 K))) (X : ℝ)
    (hs : ∀ P ∈ s, P ≠ ⊥ ∧ (Ideal.absNorm P : ℝ) ≤ X)
    (P : Ideal (𝓞 K)) (hP : P ∈ quotientSupport D s) :
    (Ideal.absNorm P : ℝ) ≤ X := by
  have h := hs (D * P) ((mem_quotientSupport D P hD s).mp hP)
  exact (ideal_norm_le_of_dvd P (D * P) h.1 (dvd_mul_left P D)).trans h.2

theorem blockBeta_ne_zero
    (cubic : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (beta : Ideal (𝓞 K) → Ideal (𝓞 K) → Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (D r t c m h : Ideal (𝓞 K))
    (hb : blockBeta cubic beta D r t c m h ≠ 0) : beta t (r * c) m h ≠ 0 := by
  intro hz
  exact hb (by simp [blockBeta, hz])

theorem blockBeta_norm_le_one
    (cubic : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (hcubic : ∀ P n, ‖cubic P n‖ ≤ 1)
    (beta : Ideal (𝓞 K) → Ideal (𝓞 K) → Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (hbeta : ∀ t c m h, ‖beta t c m h‖ ≤ 1)
    (D r t c m h : Ideal (𝓞 K)) : ‖blockBeta cubic beta D r t c m h‖ ≤ 1 := by
  simp only [blockBeta, norm_mul]
  have hn : ‖beta t (r * c) m h‖ * ‖cubic D ((r * c) * m)‖ ≤ 1 := by
    exact (mul_le_mul (hbeta t (r * c) m h) (hcubic D ((r * c) * m))
      (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
  exact (mul_le_mul hn (mask_norm_le D (h * t))
    (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)

theorem blockColumn_sq_le_reciprocal
    (cubic : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (hcubic : ∀ P n, ‖cubic P n‖ ≤ 1)
    (a : Ideal (𝓞 K) → ℂ) (D r t h P : Ideal (𝓞 K))
    (ha : ‖a (D * P)‖ ≤ 1) :
    ‖blockColumn cubic a D r t h P‖ ^ 2 ≤ 1 / (Ideal.absNorm P : ℝ) := by
  apply HeckeSkeleton.LowEnergy.normalized_ideal_coefficient_le
  rw [norm_mul, norm_mul]
  have hn : ‖a (D * P)‖ * ‖cubic P r‖ ≤ 1 := by
    exact (mul_le_mul ha (hcubic P r) (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
  exact (mul_le_mul hn (mask_norm_le P (h * t))
    (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)

theorem ReconstructedSupport.quadratic_product
    {beta : Ideal (𝓞 K) → Ideal (𝓞 K) → Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ}
    {N B : ℝ} (hs : ReconstructedSupport beta N B)
    (t c m h : Ideal (𝓞 K)) (hb : beta t c m h ≠ 0) :
    Squarefree (m * h) ∧ (Ideal.absNorm (m * h) : ℝ) ≤ N * B := by
  have hn := hs.n_squarefree t c m h hb
  have hg := hs.g_squarefree t c m h hb
  have ht := hs.square_nezero t c m h hb
  have hm := Squarefree.squarefree_of_dvd (dvd_mul_left m c) hn
  have hh := Squarefree.squarefree_of_dvd (dvd_mul_left h c) hg
  have hsf : Squarefree (m * h) :=
    squarefree_mul_iff.mpr ⟨(hs.residual_coprime t c m h hb).isRelPrime, hm, hh⟩
  have hbn : (c * h) * t ^ 2 ≠ ⊥ := mul_ne_zero hg.ne_zero (pow_ne_zero 2 ht)
  have hmN := (ideal_norm_le_of_dvd m (c * m) hn.ne_zero
    (dvd_mul_left m c)).trans (hs.n_bound t c m h hb)
  have hhB := (ideal_norm_le_of_dvd h ((c * h) * t ^ 2) hbn
    (dvd_trans (dvd_mul_left h c) (dvd_mul_right (c * h) (t ^ 2)))).trans
      (hs.b_bound t c m h hb)
  refine ⟨hsf, ?_⟩
  rw [map_mul, Nat.cast_mul]
  exact mul_le_mul hmN hhB (Nat.cast_nonneg _)
    ((Nat.cast_nonneg (Ideal.absNorm m)).trans hmN)

theorem ReconstructedSupport.cubic_product
    {beta : Ideal (𝓞 K) → Ideal (𝓞 K) → Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ}
    {N B : ℝ} (hs : ReconstructedSupport beta N B)
    (r t c m h : Ideal (𝓞 K)) (hb : beta t (r * c) m h ≠ 0) :
    Squarefree (c * m) ∧ (Ideal.absNorm (c * m) : ℝ) ≤ N := by
  have hn := hs.n_squarefree t (r * c) m h hb
  have hd : c * m ∣ (r * c) * m := ⟨r, by ac_rfl⟩
  exact ⟨Squarefree.squarefree_of_dvd hd hn,
    (ideal_norm_le_of_dvd (c * m) ((r * c) * m) hn.ne_zero hd).trans
      (hs.n_bound t (r * c) m h hb)⟩

theorem ReconstructedSupport.block_products
    {beta : Ideal (𝓞 K) → Ideal (𝓞 K) → Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ}
    {N B : ℝ} (hs : ReconstructedSupport beta N B)
    (cubic : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (D r t c m h : Ideal (𝓞 K))
    (hb : blockBeta cubic beta D r t c m h ≠ 0) :
    (Squarefree (m * h) ∧ (Ideal.absNorm (m * h) : ℝ) ≤ N * B) ∧
      (Squarefree (c * m) ∧ (Ideal.absNorm (c * m) : ℝ) ≤ N) := by
  have hb0 := blockBeta_ne_zero cubic beta D r t c m h hb
  exact ⟨hs.quadratic_product t (r * c) m h hb0, hs.cubic_product r t c m h hb0⟩

/-- The true cube support supplies the full pointwise weighted budget. -/
theorem ReconstructedSupport.block_budget
    {beta : Ideal (𝓞 K) → Ideal (𝓞 K) → Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ}
    {N B : ℝ} (hs : ReconstructedSupport beta N B)
    (cubic : Ideal (𝓞 K) → Ideal (𝓞 K) → ℂ)
    (hcubic : ∀ P n, ‖cubic P n‖ ≤ 1)
    (hbeta : ∀ t c m h, ‖beta t c m h‖ ≤ 1)
    (D r t c m h : Ideal (𝓞 K))
    (hr : r ≠ ⊥) (ht : t ≠ ⊥) (hh : h ≠ ⊥) (hB : 0 ≤ B) :
    (Ideal.absNorm t : ℝ) * (Ideal.absNorm c : ℝ) *
        ‖blockBeta cubic beta D r t c m h‖ ^ 2 ≤
      (B / (Ideal.absNorm r : ℝ)) /
        ((Ideal.absNorm t : ℝ) * (Ideal.absNorm h : ℝ)) := by
  have hr0 := HeckeSkeleton.LowEnergy.ideal_norm_pos K r hr
  have ht0 := HeckeSkeleton.LowEnergy.ideal_norm_pos K t ht
  have hh0 := HeckeSkeleton.LowEnergy.ideal_norm_pos K h hh
  by_cases hz : blockBeta cubic beta D r t c m h = 0
  · simp only [hz, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero]
    positivity
  · have hsup := hs.b_bound t (r * c) m h
      (blockBeta_ne_zero cubic beta D r t c m h hz)
    simp only [map_mul, map_pow, Nat.cast_mul, Nat.cast_pow] at hsup
    have hnorm := blockBeta_norm_le_one cubic hcubic beta hbeta D r t c m h
    have hsq : ‖blockBeta cubic beta D r t c m h‖ ^ 2 ≤ 1 := by
      nlinarith [norm_nonneg (blockBeta cubic beta D r t c m h)]
    calc
      _ ≤ (Ideal.absNorm t : ℝ) * (Ideal.absNorm c : ℝ) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hsq
          (mul_nonneg ht0.le (Nat.cast_nonneg _))
      _ ≤ _ := by
        apply (le_div_iff₀ (mul_pos ht0 hh0)).mpr
        apply (le_div_iff₀ hr0).mpr
        nlinarith [hsup]

#print axioms blockColumn_sq_le_reciprocal
#print axioms ReconstructedSupport.block_products
#print axioms ReconstructedSupport.block_budget

end
end HeckeSkeleton.LowEnergy.KeepOriginalRow
