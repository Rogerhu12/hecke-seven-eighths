import HeckeGeneral.Analysis.PrimeCalibrationIdealAssembly
import HeckeGeneral.Analysis.ActualSIntegerAmplifierRows

/-!
# Actual multiplicative coefficients for the canonical moments

The prime values below are the specified sextic residue symbols, extended
by zero at the excluded primes. Their ideal extension is a genuine monoid
homomorphism, with no coprimality assumption between denominator ideals.
The puncture is kept as its original completely multiplicative indicator.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_BASE

open NumberField IsDedekindDomain UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.PrimeCalibrationDraft
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open AlgebraicNumberTheory.PowerResidueSymbols
open scoped Classical BigOperators ComplexConjugate nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

/-- Actual exterior prime symbol, with the original excluded-prime zero. -/
def exteriorSymbolPrime (m : S.integer K) (p : HeightOneSpectrum (𝓞 K)) : ℂ :=
  if hp : p ∉ S then
    sIntegerSexticEvaluation K S p hp D.root6 D.primitive6 D.embedding
      (D.away_six p hp) m
  else 0

/-- Complete multiplicativity in the denominator, including common primes. -/
def exteriorSymbolHom (m : S.integer K) : Ideal (𝓞 K) →*₀ ℂ :=
  idealCoefficientHom (exteriorSymbolPrime K S D m)

theorem exteriorSymbolHom_apply (m : S.integer K) (I : ExteriorIdeal K S) :
    exteriorSymbolHom K S D m I.val.val = idealSymbol K S D I m := by
  change idealCoefficient (exteriorSymbolPrime K S D m) I.val.val = _
  rw [idealCoefficient_eq_prod_idealPrimeDivisors K _ I.val]
  unfold idealSymbol sIntegerSexticIdealEvaluation
  apply Finset.prod_congr rfl
  intro p _
  simp only [exteriorSymbolPrime, dif_pos (I.property p.val p.property)]

theorem exteriorSymbolHom_eq_zero_of_excluded (m : S.integer K)
    (I : Ideal (𝓞 K)) (p : HeightOneSpectrum (𝓞 K))
    (hp : p ∈ S) (hdiv : p.asIdeal ∣ I) :
    exteriorSymbolHom K S D m I = 0 := by
  obtain ⟨J, rfl⟩ := hdiv
  rw [map_mul]
  have hz : exteriorSymbolHom K S D m p.asIdeal = 0 := by
    change idealCoefficient (exteriorSymbolPrime K S D m) p.asIdeal = 0
    rw [idealCoefficient_prime]
    simp [exteriorSymbolPrime, hp]
  rw [hz, zero_mul]

theorem idealSymbol_mul_denominator (I J : ExteriorIdeal K S) (m : S.integer K) :
    idealSymbol K S D (exteriorMul K S I J) m =
      idealSymbol K S D I m * idealSymbol K S D J m := by
  rw [← exteriorSymbolHom_apply, ← exteriorSymbolHom_apply,
    ← exteriorSymbolHom_apply]
  exact map_mul (exteriorSymbolHom K S D m) I.val.val J.val.val

theorem idealSymbol_mul_numerator (I : ExteriorIdeal K S) (a b : S.integer K) :
    idealSymbol K S D I (a * b) =
      idealSymbol K S D I a * idealSymbol K S D I b :=
  sIntegerSexticIdealEvaluation_mul K S D.root6 D.primitive6 D.embedding
    I.val.val (nonZeroDivisors.coe_ne_zero I.val) I.property
    (fun p hp => D.away_six p (I.property p hp)) a b

@[simp] theorem idealSymbol_one_numerator (I : ExteriorIdeal K S) :
    idealSymbol K S D I 1 = 1 :=
  sIntegerSexticIdealEvaluation_one K S D.root6 D.primitive6 D.embedding
    I.val.val (nonZeroDivisors.coe_ne_zero I.val) I.property
    (fun p hp => D.away_six p (I.property p hp))

theorem idealSymbol_pow_numerator (I : ExteriorIdeal K S)
    (a : S.integer K) (n : ℕ) :
    idealSymbol K S D I (a ^ n) = idealSymbol K S D I a ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, idealSymbol_mul_numerator, ih, pow_succ]

theorem norm_idealSymbol_le_one (I : ExteriorIdeal K S) (a : S.integer K) :
    ‖idealSymbol K S D I a‖ ≤ 1 :=
  norm_sIntegerSexticIdealEvaluation_le_one K S D.root6 D.primitive6 D.embedding
    I.val.val (nonZeroDivisors.coe_ne_zero I.val) I.property
    (fun p hp => D.away_six p (I.property p hp)) a

/-- A sixth power keeps its entire original coprimality indicator. -/
theorem idealSymbol_sixth_power_mask (I : ExteriorIdeal K S) (a : S.integer K) :
    idealSymbol K S D I a ^ 6 =
      if IsCoprime I.val.val (sIntegerModulusContraction K S a) then 1 else 0 := by
  rw [← idealSymbol_pow_numerator]
  exact sIntegerSexticIdealEvaluation_sixth_power_coprime_mask
    K S D.root6 D.primitive6 D.embedding I.val.val
      (nonZeroDivisors.coe_ne_zero I.val) I.property
      (fun p hp => D.away_six p (I.property p hp)) a

/-- The label factor in cube extraction is still the same zero/one mask. -/
theorem idealSymbol_twelfth_power_mask (I : ExteriorIdeal K S) (a : S.integer K) :
    idealSymbol K S D I a ^ 12 =
      if IsCoprime I.val.val (sIntegerModulusContraction K S a) then 1 else 0 := by
  rw [show 12 = 6 * 2 from rfl, pow_mul, idealSymbol_sixth_power_mask]
  split_ifs <;> norm_num

/-- The original puncture, defined on all ideals for the cube inversion. -/
def punctureHom (r : Ideal (𝓞 K)) : Ideal (𝓞 K) →* ℂ where
  toFun I := if IsCoprime I r then 1 else 0
  map_one' := ite_eq_left isCoprime_one_left
  map_mul' I J := by
    by_cases hI : IsCoprime I r <;> by_cases hJ : IsCoprime J r <;>
      simp [IsCoprime.mul_left_iff, hI, hJ]

/-- The actual completed coefficient tau = theta * residue symbol * puncture. -/
def canonicalTau (θ : HeckeCharacter K) (m : S.integer K)
    (r : Ideal (𝓞 K)) : Ideal (𝓞 K) →* ℂ :=
  (idealCoefficientHom (primeCoefficient K θ)).toMonoidHom *
    (exteriorSymbolHom K S D m).toMonoidHom * punctureHom K r

theorem canonicalTau_apply (θ : HeckeCharacter K) (m : S.integer K)
    (r : Ideal (𝓞 K)) (I : ExteriorIdeal K S) :
    canonicalTau K S D θ m r I.val.val =
      heckeIdealCoefficient K θ I.val * idealSymbol K S D I m *
        (if IsCoprime I.val.val r then 1 else 0) := by
  change idealCoefficient (primeCoefficient K θ) I.val.val *
    exteriorSymbolHom K S D m I.val.val * _ = _
  rw [exteriorSymbolHom_apply] <;> rfl

theorem canonicalTau_eq_zero_of_excluded (θ : HeckeCharacter K)
    (m : S.integer K) (r I : Ideal (𝓞 K))
    (p : HeightOneSpectrum (𝓞 K)) (hp : p ∈ S) (hdiv : p.asIdeal ∣ I) :
    canonicalTau K S D θ m r I = 0 := by
  change idealCoefficient (primeCoefficient K θ) I *
    exteriorSymbolHom K S D m I * _ = 0
  rw [exteriorSymbolHom_eq_zero_of_excluded K S D m I p hp hdiv, mul_zero, zero_mul]

/-- The row k*f^4 gives exactly the two symbols in the canonical coefficient. -/
theorem canonicalTau_label (θ : HeckeCharacter K) (k : S.integer K)
    (f I : ExteriorIdeal K S) (r : Ideal (𝓞 K)) :
    canonicalTau K S D θ (k * D.generator f ^ 4) r I.val.val =
      heckeIdealCoefficient K θ I.val * idealSymbol K S D I k *
        idealSymbol K S D I (D.generator f) ^ 4 *
          (if IsCoprime I.val.val r then 1 else 0) := by
  rw [canonicalTau_apply, idealSymbol_mul_numerator, idealSymbol_pow_numerator]
  ring

/-- Exact separated row/label phase after freezing the cube variable. -/
theorem canonicalTau_cube_phase (θ : HeckeCharacter K) (k : S.integer K)
    (f H : ExteriorIdeal K S) (r : Ideal (𝓞 K)) :
    canonicalTau K S D θ (k * D.generator f ^ 4) r H.val.val ^ 3 =
      heckeIdealCoefficient K θ H.val ^ 3 * idealSymbol K S D H k ^ 3 *
        idealSymbol K S D H (D.generator f) ^ 12 *
          (if IsCoprime H.val.val r then 1 else 0) := by
  rw [canonicalTau_label]
  by_cases h : IsCoprime H.val.val r <;> simp only [h, if_true, if_false]
  · ring
  · simp

/-- Pointwise multiplier bound used in the joint row-label Hilbert sum. -/
theorem norm_frozen_phase_le_one (θ : HeckeCharacter K) (k : S.integer K)
    (f H : ExteriorIdeal K S) (r : Ideal (𝓞 K)) :
    ‖canonicalTau K S D θ (k * D.generator f ^ 4) r H.val.val ^ 3‖ ≤ 1 := by
  rw [norm_pow, canonicalTau_apply, norm_mul, norm_mul]
  have hc := norm_heckeIdealCoefficient_le_one K θ H.val
  have hs := norm_idealSymbol_le_one K S D H (k * D.generator f ^ 4)
  have hm : ‖(if IsCoprime H.val.val r then 1 else 0 : ℂ)‖ ≤ 1 := by
    split_ifs <;> norm_num
  have hp := mul_le_mul hc hs (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have ht := mul_le_mul hp hm (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 * 1)
  exact pow_le_one₀ (by positivity) (by simpa using ht)

end HeckeSkeleton.Moments.MOM_BASE
