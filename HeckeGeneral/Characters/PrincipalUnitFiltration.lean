import HeckeGeneral.Characters.LocalUniformizer
import HeckeGeneral.Characters.Unramified
import Mathlib.Analysis.Normed.Group.Ultra

/-!
# Normalized norm and the principal-unit filtration

At positive depth `n`, the conductor norm bound is exactly the standard
discrete multiplicative valuation bound `v(u - 1) ≤ exp(-n)`.
It automatically implies that `u` is an integral unit.
-/

noncomputable section

namespace HeckeGeneral.Characters

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NNReal Classical

variable (K : Type*) [Field K] [NumberField K]

theorem localNorm_le_inv_residueCard_pow_iff (v : HeightOneSpectrum (𝓞 K))
    (x : v.adicCompletion K) (n : ℕ) :
    ‖x‖ ≤ (residueCard K v : ℝ)⁻¹ ^ n ↔
      (Valued.v x : WithZero (Multiplicative ℤ)) ≤ WithZero.exp (-(n : ℤ)) := by
  have hq : (1 : ℝ≥0) < (Ideal.absNorm v.asIdeal : ℝ≥0) := by
    exact_mod_cast one_lt_residueCard K v
  have heq : (↑(WithZeroMulInt.toNNReal (NumberField.HeightOneSpectrum.absNorm_ne_zero v)
      (WithZero.exp (-(n : ℤ)))) : ℝ) = (residueCard K v : ℝ)⁻¹ ^ n := by
    rw [WithZeroMulInt.toNNReal_neg_apply (NumberField.HeightOneSpectrum.absNorm_ne_zero v)
      (WithZero.exp_ne_zero (a := -(n : ℤ)))]
    change (↑((Ideal.absNorm v.asIdeal : ℝ≥0) ^ (-(n : ℤ))) : ℝ) = _
    simp [residueCard, zpow_neg, zpow_natCast, inv_pow]
  rw [NumberField.FinitePlace.norm_def, ← heq]
  exact_mod_cast (WithZeroMulInt.toNNReal_strictMono hq).le_iff_le

theorem principalUnit_norm_iff_valuation (v : HeightOneSpectrum (𝓞 K))
    (u : (v.adicCompletion K)ˣ) (n : ℕ) :
    ‖u.val - 1‖ ≤ (residueCard K v : ℝ)⁻¹ ^ n ↔
      (Valued.v (u.val - 1) : WithZero (Multiplicative ℤ)) ≤ WithZero.exp (-(n : ℤ)) :=
  localNorm_le_inv_residueCard_pow_iff K v (u.val - 1) n

theorem principalUnit_norm_one (v : HeightOneSpectrum (𝓞 K))
    (u : (v.adicCompletion K)ˣ) (n : ℕ) (hn : 0 < n)
    (hu : ‖u.val - 1‖ ≤ (residueCard K v : ℝ)⁻¹ ^ n) : ‖u.val‖ = 1 := by
  have hq : (1 : ℝ) < residueCard K v := by exact_mod_cast one_lt_residueCard K v
  have hlt : ‖u.val - 1‖ < 1 := hu.trans_lt
    (pow_lt_one₀ (inv_nonneg.mpr (le_trans zero_le_one hq.le))
      (inv_lt_one_of_one_lt₀ hq) hn.ne')
  calc
    ‖u.val‖ = ‖(u.val - 1) + 1‖ := by rw [sub_add_cancel]
    _ = max ‖u.val - 1‖ ‖(1 : v.adicCompletion K)‖ :=
      IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by simpa using hlt.ne)
    _ = 1 := by simpa using max_eq_right hlt.le

theorem principalUnit_mem_integral_units (v : HeightOneSpectrum (𝓞 K))
    (u : (v.adicCompletion K)ˣ) (n : ℕ) (hn : 0 < n)
    (hu : ‖u.val - 1‖ ≤ (residueCard K v : ℝ)⁻¹ ^ n) :
    u ∈ (v.adicCompletionIntegers K).units :=
  (local_norm_one_iff_integral_unit K v u).mp (principalUnit_norm_one K v u n hn hu)

/-- The chosen local uniformizer regarded as an integer in the completion. -/
def localUniformizerInteger (v : HeightOneSpectrum (𝓞 K)) : v.adicCompletionIntegers K :=
  ⟨localUniformizer K v, by
    rw [mem_adicCompletionIntegers]
    exact (localUniformizer_isUniformizer K v).val_lt_one.le⟩

@[simp] theorem localUniformizerInteger_coe (v : HeightOneSpectrum (𝓞 K)) :
    (localUniformizerInteger K v : v.adicCompletion K) = localUniformizer K v := rfl

theorem localUniformizerInteger_isUniformizer (v : HeightOneSpectrum (𝓞 K)) :
    (Valued.v : Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ))).IsUniformizer
      (localUniformizerInteger K v) := localUniformizer_isUniformizer K v

theorem local_maximalIdeal_eq_span_uniformizer (v : HeightOneSpectrum (𝓞 K)) :
    IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) =
      Ideal.span {localUniformizerInteger K v} :=
  (localUniformizerInteger_isUniformizer K v).is_generator

theorem local_maximalIdeal_pow_eq_span_uniformizer_pow (v : HeightOneSpectrum (𝓞 K))
    (n : ℕ) :
    IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n =
      Ideal.span {localUniformizerInteger K v ^ n} := by
  rw [local_maximalIdeal_eq_span_uniformizer, Ideal.span_singleton_pow]

theorem local_mem_maximalIdeal_pow_iff_valuation (v : HeightOneSpectrum (𝓞 K))
    (x : v.adicCompletionIntegers K) (n : ℕ) :
    x ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n ↔
      (Valued.v (x : v.adicCompletion K) : WithZero (Multiplicative ℤ)) ≤
        WithZero.exp (-(n : ℤ)) := by
  rw [local_maximalIdeal_pow_eq_span_uniformizer_pow]
  have hs := (adicCompletionIntegers.integers K v).coe_span_singleton_eq_setOfPred_le_v_algebraMap
    (localUniformizerInteger K v ^ n)
  rw [show x ∈ Ideal.span {localUniformizerInteger K v ^ n} ↔
      x ∈ (Ideal.span {localUniformizerInteger K v ^ n} : Set (v.adicCompletionIntegers K))
      from Iff.rfl, hs]
  change Valued.v (x : v.adicCompletion K) ≤
    Valued.v ((localUniformizer K v) ^ n) ↔ _
  rw [map_pow, localUniformizer_valuation, ← WithZero.exp_nsmul]
  simp only [nsmul_eq_mul, mul_neg, mul_one]

theorem local_mem_maximalIdeal_pow_iff_norm (v : HeightOneSpectrum (𝓞 K))
    (x : v.adicCompletionIntegers K) (n : ℕ) :
    x ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n ↔
      ‖(x : v.adicCompletion K)‖ ≤ (residueCard K v : ℝ)⁻¹ ^ n := by
  rw [local_mem_maximalIdeal_pow_iff_valuation, localNorm_le_inv_residueCard_pow_iff]

/-- The positive-depth conductor condition is membership of `u - 1` in the actual
power of the maximal ideal of the local integer ring. -/
theorem integral_principalUnit_iff_maximalIdeal_pow (v : HeightOneSpectrum (𝓞 K))
    (u : (v.adicCompletionIntegers K)ˣ) (n : ℕ) :
    u.val - 1 ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n ↔
      ‖((u.val : v.adicCompletionIntegers K) : v.adicCompletion K) - 1‖ ≤
        (residueCard K v : ℝ)⁻¹ ^ n := by
  exact local_mem_maximalIdeal_pow_iff_norm K v (u.val - 1) n

theorem localNorm_lt_iff_valuation_lt (v : HeightOneSpectrum (𝓞 K))
    (x y : v.adicCompletion K) :
    ‖x‖ < ‖y‖ ↔ (Valued.v x : WithZero (Multiplicative ℤ)) < Valued.v y := by
  have hq : (1 : ℝ≥0) < (Ideal.absNorm v.asIdeal : ℝ≥0) := by
    exact_mod_cast one_lt_residueCard K v
  rw [NumberField.FinitePlace.norm_def, NumberField.FinitePlace.norm_def]
  exact_mod_cast (WithZeroMulInt.toNNReal_strictMono hq).lt_iff_lt

theorem localNorm_lt_inv_residueCard_pow_iff (v : HeightOneSpectrum (𝓞 K))
    (x : v.adicCompletion K) (n : ℕ) :
    ‖x‖ < (residueCard K v : ℝ)⁻¹ ^ n ↔
      (Valued.v x : WithZero (Multiplicative ℤ)) < WithZero.exp (-(n : ℤ)) := by
  rw [← localUniformizer_norm, ← norm_pow, localNorm_lt_iff_valuation_lt]
  rw [map_pow, localUniformizer_valuation, ← WithZero.exp_nsmul]
  simp only [nsmul_eq_mul, mul_neg, mul_one]

end HeckeGeneral.Characters
