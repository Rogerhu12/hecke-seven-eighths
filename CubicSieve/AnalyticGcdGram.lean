import CubicSieve.AnalyticMoebius

/-!
Finite exact column-gcd descent for the literal cubic kernel.  Multiplication
preimages implement division without arbitrary inverse choices in the new
coefficients.  Both the common-prime zero mask and the signed Möbius terms
are preserved.
-/

set_option autoImplicit false
noncomputable section
namespace CubicSieve.AnalyticGcd

open NumberField IsDedekindDomain UniqueFactorizationMonoid
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open CubicSieve.ExteriorKernel CubicSieve.AnalyticRowDecomposition
open scoped Classical BigOperators ComplexConjugate nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

theorem exteriorMul_left_injective (d : ExteriorIdeal K S) :
    Function.Injective (exteriorMul K S d) := by
  intro a b h
  apply Subtype.ext
  apply Subtype.ext
  exact mul_left_cancel₀ (nonZeroDivisors.coe_ne_zero d.val)
    (congrArg (fun I : ExteriorIdeal K S => I.val.val) h)

def dividedSet (T : Finset (ExteriorIdeal K S)) (d : ExteriorIdeal K S) :
    Finset (ExteriorIdeal K S) :=
  T.preimage (exteriorMul K S d) (exteriorMul_left_injective K S d).injOn

@[simp] theorem mem_dividedSet (T : Finset (ExteriorIdeal K S)) (d a : ExteriorIdeal K S) :
    a ∈ dividedSet K S T d ↔ exteriorMul K S d a ∈ T := Finset.mem_preimage

theorem dividedSet_image (T : Finset (ExteriorIdeal K S)) (d : ExteriorIdeal K S) :
    (dividedSet K S T d).image (exteriorMul K S d) =
      T.filter (fun I => d.val.val ∣ I.val.val) := by
  ext I
  constructor
  · intro h
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp h
    exact Finset.mem_filter.mpr ⟨(mem_dividedSet K S T d a).mp ha, dvd_mul_right _ _⟩
  · intro h
    obtain ⟨hI, hd⟩ := Finset.mem_filter.mp h
    exact Finset.mem_image.mpr ⟨quotient K S d I hd,
      (mem_dividedSet K S T d _).mpr (by rw [quotient_product]; exact hI),
      quotient_product K S d I hd⟩

theorem quotient_product_right (d a : ExteriorIdeal K S)
    (h : d.val.val ∣ (exteriorMul K S d a).val.val) :
    quotient K S d (exteriorMul K S d a) h = a := by
  apply exteriorMul_left_injective K S d
  exact quotient_product K S d (exteriorMul K S d a) h

theorem dividedSet_squarefree (T : Finset (ExteriorIdeal K S)) (d : ExteriorIdeal K S)
    (hT : ∀ I ∈ T, Squarefree I.val.val) :
    ∀ a ∈ dividedSet K S T d, Squarefree a.val.val := by
  intro a ha
  exact (hT _ ((mem_dividedSet K S T d a).mp ha)).squarefree_of_dvd (dvd_mul_left _ _)

theorem dividedSet_norm (T : Finset (ExteriorIdeal K S)) (d : ExteriorIdeal K S)
    (N : ℝ) (hT : ∀ I ∈ T, exteriorNorm K S I ≤ N) :
    ∀ a ∈ dividedSet K S T d, exteriorNorm K S a ≤ N / exteriorNorm K S d := by
  intro a ha
  have hn := hT _ ((mem_dividedSet K S T d a).mp ha)
  apply (le_div_iff₀ (by linarith [AnalyticDyadic.one_le_norm K S d])).mpr
  have he : exteriorNorm K S (exteriorMul K S d a) =
      exteriorNorm K S d * exteriorNorm K S a := by
    dsimp only [exteriorNorm, exteriorMul]
    simp only [Submonoid.coe_mul, map_mul, Nat.cast_mul]
  rw [he] at hn
  simpa only [mul_comm] using hn

theorem sum_divisible_pullback {A : Type} [AddCommMonoid A]
    (T : Finset (ExteriorIdeal K S)) (d : ExteriorIdeal K S) (f : ExteriorIdeal K S → A) :
    (∑ I ∈ T, if d.val.val ∣ I.val.val then f I else 0) =
      ∑ a ∈ dividedSet K S T d, f (exteriorMul K S d a) := by
  rw [← Finset.sum_filter, ← dividedSet_image K S T d,
    Finset.sum_image (exteriorMul_left_injective K S d).injOn]

def pulledCoefficient (d e : ExteriorIdeal K S) (z : ExteriorIdeal K S → ℂ)
    (a : ExteriorIdeal K S) : ℂ :=
  z (exteriorMul K S d a) * positiveKernel K S D e a

theorem pulledCoefficient_energy (T : Finset (ExteriorIdeal K S))
    (d e : ExteriorIdeal K S) (z : ExteriorIdeal K S → ℂ) :
    (∑ a ∈ dividedSet K S T d, ‖pulledCoefficient K S D d e z a‖ ^ 2) =
      divisorEnergy K S D T d e z := by
  rw [divisorEnergy]
  calc
    _ = ∑ a ∈ dividedSet K S T d,
        if h : d.val.val ∣ (exteriorMul K S d a).val.val then
          ‖z (exteriorMul K S d a) *
            positiveKernel K S D e (quotient K S d (exteriorMul K S d a) h)‖ ^ 2 else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      have hd : d.val.val ∣ (exteriorMul K S d a).val.val := dvd_mul_right _ _
      have hq : quotient K S d (exteriorMul K S d a) hd = a :=
        quotient_product_right K S d a hd
      rw [dite_eq_left hd, hq]
      rfl
    _ = _ := by
      have he := sum_divisible_pullback K S T d (fun I =>
        if h : d.val.val ∣ I.val.val then
          ‖z I * positiveKernel K S D e (quotient K S d I h)‖ ^ 2 else 0)
      apply he.symm.trans
      apply Finset.sum_congr rfl
      intro I hI
      by_cases h : d.val.val ∣ I.val.val <;> simp [h]

def pair (R a b : ExteriorIdeal K S) (z : ExteriorIdeal K S → ℂ) : ℂ :=
  conj (positiveKernel K S D R a * z a) * (positiveKernel K S D R b * z b)

def coprimeGram (T : Finset (ExteriorIdeal K S)) (R : ExteriorIdeal K S)
    (z : ExteriorIdeal K S → ℂ) : ℂ :=
  ∑ a ∈ T, ∑ b ∈ T, if IsCoprime a.val.val b.val.val then pair K S D R a b z else 0

/-- Pulling a row through a divisor moves its cubic character into the coefficients. -/
theorem pulled_pair (hD : AllowedGeneratorInput K S D) (R d e a b : ExteriorIdeal K S)
    (z : ExteriorIdeal K S → ℂ) :
    conj (positiveKernel K S D (exteriorMul K S e R) a * z (exteriorMul K S d a)) *
      (positiveKernel K S D (exteriorMul K S e R) b * z (exteriorMul K S d b)) =
      pair K S D R a b (pulledCoefficient K S D d e z) := by
  rw [positiveKernel_row_mul K S D hD, positiveKernel_row_mul K S D hD]
  simp only [pair, pulledCoefficient, map_mul]
  ring

def gcdImage (T : Finset (ExteriorIdeal K S)) : Finset (ExteriorIdeal K S) :=
  (T.product T).image (fun p => exteriorGcd K S p.1 p.2)

theorem gcd_mem_image (T : Finset (ExteriorIdeal K S)) (a b : ExteriorIdeal K S)
    (ha : a ∈ T) (hb : b ∈ T) : exteriorGcd K S a b ∈ gcdImage K S T :=
  Finset.mem_image.mpr ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, rfl⟩

theorem norm_le_of_dvd (d I : ExteriorIdeal K S) (hd : d.val.val ∣ I.val.val) :
    exteriorNorm K S d ≤ exteriorNorm K S I := by
  have he := quotient_norm_mul K S d I hd
  have hd1 := AnalyticDyadic.one_le_norm K S d
  have hq1 := AnalyticDyadic.one_le_norm K S (quotient K S d I hd)
  nlinarith

theorem gcdImage_norm (T : Finset (ExteriorIdeal K S)) (N : ℝ)
    (hT : ∀ J ∈ T, exteriorNorm K S J ≤ N) :
    ∀ d ∈ gcdImage K S T, exteriorNorm K S d ≤ N := by
  intro d hd
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hd
  exact (norm_le_of_dvd K S _ a (exteriorGcd_dvd_left K S a b)).trans
    (hT a (Finset.mem_product.mp hab).1)

theorem gcdImage_squarefree (T : Finset (ExteriorIdeal K S))
    (hT : ∀ J ∈ T, Squarefree J.val.val) :
    ∀ d ∈ gcdImage K S T, Squarefree d.val.val := by
  intro d hd
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hd
  exact (hT a (Finset.mem_product.mp hab).1).squarefree_of_dvd
    (exteriorGcd_dvd_left K S a b)

theorem descendant_scales (T : Finset (ExteriorIdeal K S)) (N : ℝ)
    (hT : ∀ J ∈ T, exteriorNorm K S J ≤ N)
    (d : ExteriorIdeal K S) (hd : d ∈ gcdImage K S T)
    (e : ExteriorIdeal K S) (he : e ∈ divisors K S d) :
    1 ≤ N / exteriorNorm K S d ∧ exteriorNorm K S e ≤ exteriorNorm K S d := by
  have hd0 : 0 < exteriorNorm K S d := by linarith [AnalyticDyadic.one_le_norm K S d]
  exact ⟨(one_le_div hd0).mpr (gcdImage_norm K S T N hT d hd),
    norm_le_of_dvd K S e d ((mem_divisors K S d e).mp he)⟩

def gcdGram (T : Finset (ExteriorIdeal K S)) (d R : ExteriorIdeal K S)
    (z : ExteriorIdeal K S → ℂ) : ℂ :=
  ∑ a ∈ T, ∑ b ∈ T, if exteriorGcd K S a b = d then pair K S D R a b z else 0

theorem row_gram_partition (T : Finset (ExteriorIdeal K S)) (R : ExteriorIdeal K S)
    (z : ExteriorIdeal K S → ℂ) :
    ((‖∑ J ∈ T, positiveKernel K S D R J * z J‖ ^ 2 : ℝ) : ℂ) =
      ∑ d ∈ gcdImage K S T, gcdGram K S D T d R z := by
  have he : ((‖∑ J ∈ T, positiveKernel K S D R J * z J‖ ^ 2 : ℝ) : ℂ) =
      ∑ a ∈ T, ∑ b ∈ T, pair K S D R a b z := by
    rw [Complex.ofReal_pow, ← Complex.conj_mul']
    simp only [map_sum, Finset.sum_mul, Finset.mul_sum, pair]
    exact Finset.sum_comm
  have hg : (∑ d ∈ gcdImage K S T, gcdGram K S D T d R z) =
      ∑ a ∈ T, ∑ b ∈ T, ∑ d ∈ gcdImage K S T,
        if exteriorGcd K S a b = d then pair K S D R a b z else 0 := by
    simp only [gcdGram]
    calc
      _ = ∑ a ∈ T, ∑ d ∈ gcdImage K S T, ∑ b ∈ T,
          if exteriorGcd K S a b = d then pair K S D R a b z else 0 := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro a ha
        exact Finset.sum_comm
  rw [he, hg]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  symm
  exact Finset.sum_ite_eq_of_mem _ _ (fun _ => pair K S D R a b z)
    (gcd_mem_image K S T a b ha hb)

theorem gcd_eq_forces_left (d a b : ExteriorIdeal K S)
    (h : exteriorGcd K S a b = d) : d.val.val ∣ a.val.val :=
  h ▸ exteriorGcd_dvd_left K S a b

theorem gcd_eq_forces_right (d a b : ExteriorIdeal K S)
    (h : exteriorGcd K S a b = d) : d.val.val ∣ b.val.val :=
  h ▸ exteriorGcd_dvd_right K S a b

theorem gcdGram_restrict (T : Finset (ExteriorIdeal K S)) (d R : ExteriorIdeal K S)
    (z : ExteriorIdeal K S → ℂ) :
    gcdGram K S D T d R z =
      ∑ a ∈ T.filter (fun a => d.val.val ∣ a.val.val),
        ∑ b ∈ T.filter (fun b => d.val.val ∣ b.val.val),
          if exteriorGcd K S a b = d then pair K S D R a b z else 0 := by
  simp only [gcdGram, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hd : d.val.val ∣ a.val.val
  · rw [ite_eq_left hd]
    apply Finset.sum_congr rfl
    intro b hb
    by_cases he : d.val.val ∣ b.val.val
    · rw [ite_eq_left he]
    · rw [ite_eq_right he, ite_eq_right (fun hg => he (gcd_eq_forces_right K S d a b hg))]
  · rw [ite_eq_right hd]
    apply Finset.sum_eq_zero
    intro b hb
    exact ite_eq_right (fun hg => hd (gcd_eq_forces_left K S d a b hg))

theorem gcdGram_factor (hD : AllowedGeneratorInput K S D)
    (T : Finset (ExteriorIdeal K S)) (d R : ExteriorIdeal K S)
    (z : ExteriorIdeal K S → ℂ) :
    gcdGram K S D T d R z =
      (if IsCoprime R.val.val d.val.val then (1 : ℂ) else 0) *
        coprimeGram K S D (dividedSet K S T d) R
          (fun a => z (exteriorMul K S d a)) := by
  rw [gcdGram_restrict, ← dividedSet_image K S T d,
    Finset.sum_image (exteriorMul_left_injective K S d).injOn]
  simp_rw [Finset.sum_image (exteriorMul_left_injective K S d).injOn]
  simp only [coprimeGram, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  have hda : d.val.val ∣ (exteriorMul K S d a).val.val := dvd_mul_right _ _
  have hdb : d.val.val ∣ (exteriorMul K S d b).val.val := dvd_mul_right _ _
  have hqa : quotient K S d (exteriorMul K S d a) hda = a :=
    quotient_product_right K S d a hda
  have hqb : quotient K S d (exteriorMul K S d b) hdb = b :=
    quotient_product_right K S d b hdb
  have hh := gcd_pair_factor K S D hD R d
    (exteriorMul K S d a) (exteriorMul K S d b) hda hdb
    (z (exteriorMul K S d a)) (z (exteriorMul K S d b))
  rw [hqa, hqb] at hh
  simpa only [pair] using hh

/-- The two exact finite descents: column gcd, then common-prime Möbius removal. -/
theorem row_gram_moebius (hD : AllowedGeneratorInput K S D)
    (T : Finset (ExteriorIdeal K S)) (R : ExteriorIdeal K S)
    (z : ExteriorIdeal K S → ℂ) :
    ((‖∑ J ∈ T, positiveKernel K S D R J * z J‖ ^ 2 : ℝ) : ℂ) =
      ∑ d ∈ gcdImage K S T, ∑ e ∈ divisors K S d, (moebius e.val.val : ℂ) *
        (if e.val.val ∣ R.val.val then coprimeGram K S D (dividedSet K S T d) R
          (fun a => z (exteriorMul K S d a)) else 0) := by
  rw [row_gram_partition]
  apply Finset.sum_congr rfl
  intro d hd
  rw [gcdGram_factor K S D hD]
  exact common_mask_sum K S R d
    (fun R => coprimeGram K S D (dividedSet K S T d) R
      (fun a => z (exteriorMul K S d a)))

theorem pulled_coprimeGram (hD : AllowedGeneratorInput K S D)
    (T : Finset (ExteriorIdeal K S)) (R d e : ExteriorIdeal K S)
    (z : ExteriorIdeal K S → ℂ) :
    coprimeGram K S D (dividedSet K S T d) (exteriorMul K S e R)
      (fun a => z (exteriorMul K S d a)) =
        coprimeGram K S D (dividedSet K S T d) R (pulledCoefficient K S D d e z) := by
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hc : IsCoprime a.val.val b.val.val
  · rw [ite_eq_left hc, ite_eq_left hc]
    exact pulled_pair K S D hD R d e a b z
  · rw [ite_eq_right hc, ite_eq_right hc]

/-- Exact row-divisor pullback for an arbitrary finite row weight. -/
theorem weighted_gram_descent (hD : AllowedGeneratorInput K S D)
    (A T : Finset (ExteriorIdeal K S)) (w : ExteriorIdeal K S → ℂ)
    (z : ExteriorIdeal K S → ℂ) :
    (∑ R ∈ A, w R * ((‖∑ J ∈ T, positiveKernel K S D R J * z J‖ ^ 2 : ℝ) : ℂ)) =
      ∑ d ∈ gcdImage K S T, ∑ e ∈ divisors K S d, (moebius e.val.val : ℂ) *
        ∑ R ∈ dividedSet K S A e, w (exteriorMul K S e R) *
          coprimeGram K S D (dividedSet K S T d) R (pulledCoefficient K S D d e z) := by
  simp_rw [row_gram_moebius K S D hD, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  have hp := sum_divisible_pullback K S A e (fun R =>
    w R * coprimeGram K S D (dividedSet K S T d) R
      (fun a => z (exteriorMul K S d a)))
  have hleft : (∑ R ∈ A, w R * ((moebius e.val.val : ℂ) *
      (if e.val.val ∣ R.val.val then coprimeGram K S D (dividedSet K S T d) R
        (fun a => z (exteriorMul K S d a)) else 0))) =
      (moebius e.val.val : ℂ) *
        ∑ R ∈ A, if e.val.val ∣ R.val.val then w R *
          coprimeGram K S D (dividedSet K S T d) R
            (fun a => z (exteriorMul K S d a)) else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro R hR
    by_cases h : e.val.val ∣ R.val.val <;> simp [h, mul_left_comm]
  rw [hleft, hp, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro R hR
  rw [pulled_coprimeGram K S D hD]

theorem pulledCoefficient_epsilon_budget (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℝ, 1 ≤ N →
      ∀ W T : Finset (ExteriorIdeal K S),
        (∀ J ∈ T, exteriorNorm K S J ≤ N) → ∀ z : ExteriorIdeal K S → ℂ,
      (∑ d ∈ W, ∑ e ∈ divisors K S d,
        ∑ a ∈ dividedSet K S T d, ‖pulledCoefficient K S D d e z a‖ ^ 2) ≤
        C * N ^ ε * ∑ J ∈ T, ‖z J‖ ^ 2 := by
  obtain ⟨C, hC, hb⟩ := exists_divisorEnergy_epsilon_budget K S D ε hε
  refine ⟨C, hC, fun N hN W T hT z => ?_⟩
  simp_rw [pulledCoefficient_energy]
  exact hb N hN W T hT z

end CubicSieve.AnalyticGcd
