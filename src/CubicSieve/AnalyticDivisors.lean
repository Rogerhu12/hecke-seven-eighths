import CubicSieve.AnalyticGcdDefs
import CubicSieve.ExteriorSieve
import DedekindZetaZeroFree.Arithmetic.Ideals.DivisorEpsilonBounds

/-!
Actual exterior divisor sets and the coefficient-energy cost of two divisor
descents.  The budget is a genuine ideal divisor bound, uniform in both the
allowed section and all coefficient choices.
-/

set_option autoImplicit false
noncomputable section
namespace CubicSieve.AnalyticGcd

open NumberField IsDedekindDomain
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open CubicSieve.ExteriorKernel CubicSieve.ExteriorSieve
open DedekindZetaZeroFree.LargeSieve
open scoped Classical BigOperators ComplexConjugate nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

def divisors (I : ExteriorIdeal K S) : Finset (ExteriorIdeal K S) :=
  (idealDivisors I.val.val).preimage (underlyingIdeal K S)
    (underlyingIdeal_injective K S).injOn

@[simp] theorem mem_divisors (I d : ExteriorIdeal K S) :
    d ∈ divisors K S I ↔ d.val.val ∣ I.val.val := by
  simp only [divisors, Finset.mem_preimage, underlyingIdeal]
  exact mem_idealDivisors (nonZeroDivisors.coe_ne_zero I.val)

def ofDivisor (I : ExteriorIdeal K S) (d : Ideal (𝓞 K)) (hd : d ∣ I.val.val) :
    ExteriorIdeal K S := by
  have hn : d ≠ 0 := by
    intro hz
    exact nonZeroDivisors.coe_ne_zero I.val (zero_dvd_iff.mp (hz ▸ hd))
  exact ⟨⟨d, mem_nonZeroDivisors_of_ne_zero hn⟩,
    fun p hp => I.property p (hp.trans hd)⟩

@[simp] theorem ofDivisor_val (I : ExteriorIdeal K S) (d : Ideal (𝓞 K))
    (hd : d ∣ I.val.val) : (ofDivisor K S I d hd).val.val = d := rfl

theorem divisors_image (I : ExteriorIdeal K S) :
    (divisors K S I).image (underlyingIdeal K S) = idealDivisors I.val.val := by
  apply Finset.Subset.antisymm
  · intro d hd
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hd
    exact (mem_idealDivisors (nonZeroDivisors.coe_ne_zero I.val)).mpr
      ((mem_divisors K S I e).mp he)
  · intro d hd
    have he := (mem_idealDivisors (nonZeroDivisors.coe_ne_zero I.val)).mp hd
    exact Finset.mem_image.mpr ⟨ofDivisor K S I d he,
      (mem_divisors K S I _).mpr he, rfl⟩

theorem divisors_card (I : ExteriorIdeal K S) :
    (divisors K S I).card = idealDivisorCount I.val.val := by
  rw [← Finset.card_image_of_injective _ (underlyingIdeal_injective K S), divisors_image]
  rfl

theorem divisors_subset (d I : ExteriorIdeal K S) (hd : d.val.val ∣ I.val.val) :
    divisors K S d ⊆ divisors K S I := by
  intro e he
  exact (mem_divisors K S I e).mpr (((mem_divisors K S d e).mp he).trans hd)

/-- Pullback energy before quotient reindexing; the exact cubic phase is retained. -/
def divisorEnergy (T : Finset (ExteriorIdeal K S)) (d e : ExteriorIdeal K S)
    (z : ExteriorIdeal K S → ℂ) : ℝ :=
  ∑ J ∈ T, if h : d.val.val ∣ J.val.val then
    ‖z J * positiveKernel K S D e (quotient K S d J h)‖ ^ 2 else 0

theorem divisorEnergy_nonneg (T : Finset (ExteriorIdeal K S)) (d e : ExteriorIdeal K S)
    (z : ExteriorIdeal K S → ℂ) : 0 ≤ divisorEnergy K S D T d e z := by
  apply Finset.sum_nonneg
  intro J hJ
  split_ifs <;> positivity

theorem divisorEnergy_le (T : Finset (ExteriorIdeal K S)) (d e : ExteriorIdeal K S)
    (z : ExteriorIdeal K S → ℂ) :
    divisorEnergy K S D T d e z ≤
      ∑ J ∈ T, if d.val.val ∣ J.val.val then ‖z J‖ ^ 2 else 0 := by
  apply Finset.sum_le_sum
  intro J hJ
  by_cases h : d.val.val ∣ J.val.val
  · simp only [dif_pos h, if_pos h]
    rw [norm_mul, mul_pow]
    have hn := norm_kernel_le_one K S D 2 (Or.inl rfl) e (quotient K S d J h)
    have hs : ‖positiveKernel K S D e (quotient K S d J h)‖ ^ 2 ≤ 1 := by
      nlinarith [norm_nonneg (positiveKernel K S D e (quotient K S d J h))]
    nlinarith [sq_nonneg ‖z J‖]
  · simp only [dif_neg h, if_neg h, le_refl]

theorem divisorEnergy_budget (W T : Finset (ExteriorIdeal K S))
    (z : ExteriorIdeal K S → ℂ) :
    ∑ d ∈ W, ∑ e ∈ divisors K S d, divisorEnergy K S D T d e z ≤
      ∑ J ∈ T, ((divisors K S J).card : ℝ) ^ 2 * ‖z J‖ ^ 2 := by
  have hle : (∑ d ∈ W, ∑ e ∈ divisors K S d, divisorEnergy K S D T d e z) ≤
      ∑ d ∈ W, ∑ e ∈ divisors K S d,
        ∑ J ∈ T, if d.val.val ∣ J.val.val then ‖z J‖ ^ 2 else 0 := by
    exact Finset.sum_le_sum (fun d hd => Finset.sum_le_sum
      (fun e he => divisorEnergy_le K S D T d e z))
  apply hle.trans
  simp_rw [Finset.sum_comm (s := divisors K S _) (t := T)]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro J hJ
  have heq : (∑ d ∈ W, ∑ e ∈ divisors K S d,
      if d.val.val ∣ J.val.val then ‖z J‖ ^ 2 else 0) =
      ∑ d ∈ W.filter (fun d => d.val.val ∣ J.val.val),
        ((divisors K S d).card : ℝ) * ‖z J‖ ^ 2 := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d hd
    by_cases h : d.val.val ∣ J.val.val <;> simp [h]
  rw [heq]
  have hsub : W.filter (fun d => d.val.val ∣ J.val.val) ⊆ divisors K S J := by
    intro d hd
    exact (mem_divisors K S J d).mpr (Finset.mem_filter.mp hd).2
  calc
    _ ≤ ∑ d ∈ W.filter (fun d => d.val.val ∣ J.val.val),
        ((divisors K S J).card : ℝ) * ‖z J‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro d hd
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact_mod_cast Finset.card_le_card
        (divisors_subset K S d J (Finset.mem_filter.mp hd).2)
    _ ≤ ∑ d ∈ divisors K S J, ((divisors K S J).card : ℝ) * ‖z J‖ ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro d hd hnd
      positivity
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

theorem exists_divisorEnergy_epsilon_budget (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℝ, 1 ≤ N →
      ∀ W T : Finset (ExteriorIdeal K S),
        (∀ J ∈ T, exteriorNorm K S J ≤ N) → ∀ z : ExteriorIdeal K S → ℂ,
      ∑ d ∈ W, ∑ e ∈ divisors K S d, divisorEnergy K S D T d e z ≤
        C * N ^ ε * ∑ J ∈ T, ‖z J‖ ^ 2 := by
  obtain ⟨A, hA1, hA⟩ := ideal_divisor_count_le_rpow K (ε / 2) (by linarith)
  refine ⟨A ^ 2, by positivity, fun N hN W T hT z => ?_⟩
  apply (divisorEnergy_budget K S D W T z).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro J hJ
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  have hcount : ((divisors K S J).card : ℝ) ≤ A * N ^ (ε / 2) := by
    rw [divisors_card]
    exact (hA J.val.val).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) (hT J hJ) (by linarith)) (by linarith))
  calc
    _ ≤ (A * N ^ (ε / 2)) ^ 2 := by
      exact pow_le_pow_left₀ (by positivity) hcount 2
    _ = A ^ 2 * N ^ ε := by
      rw [mul_pow, ← Real.rpow_natCast (N ^ (ε / 2)),
        ← Real.rpow_mul (by linarith : 0 ≤ N)]
      congr 1
      congr 1
      ring

end CubicSieve.AnalyticGcd
