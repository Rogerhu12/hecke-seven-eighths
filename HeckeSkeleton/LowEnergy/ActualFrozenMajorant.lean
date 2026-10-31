import HeckeSkeleton.LowEnergy.ActualLocalWeylTable
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-!
# Actual normalized frozen majorant

The only character hypothesis is exterior unramifiedness, already a field of
MarkedCoefficientReflectionInput.  All local scalar estimates come from the
proved finite residue table.  In particular the norm of the normalized Omega
is bounded by a finite product whose inverse-square-root charges are explicit.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.LowEnergy.ActualFrozenMajorant

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.LowFrozenCube
open HeckeSkeleton.LowEnergy.IdealRows HeckeSkeleton.LowEnergy.FrozenIdealRows
open HeckeSkeleton.LowEnergy.ActualReflection HeckeSkeleton.LowEnergy.ActualSymbols
open HeckeSkeleton.LowEnergy.ActualFrozenCube HeckeSkeleton.LowEnergy.ActualLocalWeylTable
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

theorem primeEvaluation_norm_zero_or_one (p : ExteriorPrime K S) (a : S.integer K) :
    ‖primeEvaluation K S D p a‖ = 0 ∨ ‖primeEvaluation K S D p a‖ = 1 := by
  by_cases ha : sIntegerSexticResidueMap K S p.val p.property a = 0
  · left
    simp only [primeEvaluation, sIntegerSexticEvaluation, ha,
      sexticResidueCharacter_zero, norm_zero]
  · right
    exact sexticResidueCharacter_norm K D.root6 D.primitive6 D.embedding p.val
      (D.away_six p.val p.property) _ ha

theorem primeEvaluation_norm_le_one (p : ExteriorPrime K S) (a : S.integer K) :
    ‖primeEvaluation K S D p a‖ ≤ 1 := by
  rcases primeEvaluation_norm_zero_or_one K S D p a with h | h <;> simp [h]

theorem primeEvaluation_zpow_norm_le_one (p : ExteriorPrime K S) (a : S.integer K)
    (n : ℤ) : ‖primeEvaluation K S D p a ^ n‖ ≤ 1 := by
  rw [norm_zpow]
  rcases primeEvaluation_norm_zero_or_one K S D p a with h | h
  · rw [h]
    by_cases hn : n = 0
    · simp [hn]
    · rw [zero_zpow _ hn]
      exact zero_le_one
  · simp [h]

theorem primeEvaluation_pow_norm_le_one (p : ExteriorPrime K S) (a : S.integer K)
    (n : ℕ) : ‖primeEvaluation K S D p a ^ n‖ ≤ 1 := by
  rw [norm_pow]
  exact pow_le_one₀ (norm_nonneg _) (primeEvaluation_norm_le_one K S D p a)

theorem mul_norm_le_one (a b : ℂ) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    ‖a * b‖ ≤ 1 := by
  rw [norm_mul]
  simpa only [one_mul] using mul_le_mul ha hb (norm_nonneg b) (by norm_num : (0 : ℝ) ≤ 1)

theorem prod_norm_le_one {ι : Type*} (T : Finset ι) (f : ι → ℂ)
    (hf : ∀ t ∈ T, ‖f t‖ ≤ 1) : ‖∏ t ∈ T, f t‖ ≤ 1 := by
  rw [norm_prod]
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) hf

/-- An exterior unramified character has norm one on every actual exterior ideal. -/
theorem heckeIdealCoefficient_exterior_norm (θ : HeckeCharacter K)
    (hθ : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K θ p)
    (I : ExteriorIdeal K S) : ‖heckeIdealCoefficient K θ I.val‖ = 1 := by
  have he : heckeIdealCoefficient K θ I.val =
      (primeExponents I.val).prod (fun p e => primeCoefficient K θ p ^ e) := by
    have h := map_idealOfPrimeExponents
      (idealCoefficientHom (primeCoefficient K θ)).toMonoidHom (primeExponents I.val)
    rw [idealOfPrimeExponents_primeExponents] at h
    change idealCoefficient (primeCoefficient K θ) I.val.val =
      (primeExponents I.val).prod (fun p e =>
        idealCoefficient (primeCoefficient K θ) p.asIdeal ^ e) at h
    simpa only [heckeIdealCoefficient, nonzeroIdealCoefficient, idealCoefficient_prime] using h
  rw [he, Finsupp.prod, norm_prod]
  apply Finset.prod_eq_one
  intro p hp
  have hdiv := (exponent_ne_zero_iff_dvd I.val p).mp (Finsupp.mem_support_iff.mp hp)
  rw [norm_pow, primeCoefficient_of_unramified K θ p (hθ p (I.property p hdiv))]
  simp

theorem idealSymbol_unit_norm (I : ExteriorIdeal K S) (u : S.unit K) :
    ‖idealSymbol K S D I (S.unitEquivUnitsInteger K u).val‖ = 1 := by
  have h6 : idealSymbol K S D I (S.unitEquivUnitsInteger K u).val ^ 6 = 1 := by
    change (elementSymbolHom K S D I) (S.unitEquivUnitsInteger K u).val ^ 6 = 1
    rw [← (elementSymbolHom K S D I).map_pow]
    exact sIntegerSexticIdealEvaluation_sixth_power_unit K S D.root6 D.primitive6
      D.embedding _ _ _ _ u
  exact Complex.norm_eq_one_of_pow_eq_one h6 (by decide : (6 : ℕ) ≠ 0)

theorem periodValue_norm (d : MarkedDatum K S) (θ : HeckeCharacter K)
    (hθ : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K θ p)
    (I : ExteriorIdeal K S) : ‖periodValue K S D d θ I‖ = 1 := by
  rw [periodValue, norm_mul, heckeIdealCoefficient_exterior_norm K S θ hθ I,
    idealSymbol_unit_norm, one_mul]

theorem norm_one_sub_prime_inv_le_one (p : ExteriorPrime K S) :
    ‖1 - (p.val.asIdeal.absNorm : ℂ)⁻¹‖ ≤ 1 := by
  have hq : (1 : ℝ) ≤ p.val.asIdeal.absNorm := by
    exact_mod_cast (NumberField.HeightOneSpectrum.one_lt_absNorm p.val).le
  have hi0 : (0 : ℝ) ≤ (p.val.asIdeal.absNorm : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hi1 : (p.val.asIdeal.absNorm : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hq
  have hc : 1 - (p.val.asIdeal.absNorm : ℂ)⁻¹ =
      ((1 - (p.val.asIdeal.absNorm : ℝ)⁻¹ : ℝ) : ℂ) := by
    simp only [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_inv,
      Complex.ofReal_natCast]
  rw [hc, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  linarith

variable (d : MarkedDatum K S) (i : ReflectionIndex K S d)

private theorem frozen_phase_norm_le_one (p : ExteriorPrime K S) :
    ‖primeEvaluation K S D p (S.unitEquivUnitsInteger K (frequencyUnit K S d i)).val *
      primeEvaluation K S D p (D.generator (removePrime K S i.numeratorFrozen p)) *
      primeEvaluation K S D p (D.generator i.n) ^ 3 *
      primeEvaluation K S D p (D.generator (removePrime K S (activeFrozenIdeal K S d i) p)) ^
        (-2 : ℤ)‖ ≤ 1 := by
  apply mul_norm_le_one
  · apply mul_norm_le_one
    · exact mul_norm_le_one _ _
        (primeEvaluation_norm_le_one K S D p _) (primeEvaluation_norm_le_one K S D p _)
    · exact primeEvaluation_pow_norm_le_one K S D p _ 3
  · exact primeEvaluation_zpow_norm_le_one K S D p _ (-2)

/-- All nonlocal factors in literal Omega are contractions. -/
theorem frozenOmega_norm_le_local_product (θ : HeckeCharacter K)
    (hθ : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K θ p) :
    ‖frozenOmega K S D d i θ‖ ≤
      ∏ p ∈ i.activeFrozen,
        ‖localWeylScalar K S D p (rowDigit K S d p)
          (primeExponents i.numeratorFrozen.val p.val)‖ := by
  have hinactive : ‖Finset.prod (frozenPrimes K S d \ i.activeFrozen)
      (fun (p : ExteriorPrime K S) => 1 - (p.val.asIdeal.absNorm : ℂ)⁻¹)‖ ≤ 1 :=
    prod_norm_le_one _ _ (fun p _ => norm_one_sub_prime_inv_le_one K S p)
  have hlocal :
      ‖∏ p ∈ i.activeFrozen,
        localWeylScalar K S D p (rowDigit K S d p)
          (primeExponents i.numeratorFrozen.val p.val) *
        (primeEvaluation K S D p (S.unitEquivUnitsInteger K (frequencyUnit K S d i)).val *
         primeEvaluation K S D p (D.generator (removePrime K S i.numeratorFrozen p)) *
         primeEvaluation K S D p (D.generator i.n) ^ 3 *
         primeEvaluation K S D p (D.generator (removePrime K S (activeFrozenIdeal K S d i) p)) ^
           (-2 : ℤ)) ^ localWeylExponent (rowDigit K S d p)
             (primeExponents i.numeratorFrozen.val p.val)‖ ≤
      ∏ p ∈ i.activeFrozen, ‖localWeylScalar K S D p (rowDigit K S d p)
        (primeExponents i.numeratorFrozen.val p.val)‖ := by
    rw [norm_prod]
    apply Finset.prod_le_prod₀
    · intro p _
      exact norm_nonneg _
    · intro p _
      rw [norm_mul, norm_pow]
      have hp := pow_le_one₀ (norm_nonneg _)
        (frozen_phase_norm_le_one K S D d i p)
        (n := localWeylExponent (rowDigit K S d p) (primeExponents i.numeratorFrozen.val p.val))
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hp (norm_nonneg _)
  unfold frozenOmega
  simp only [norm_mul, norm_inv, norm_zpow, norm_pow,
    periodValue_norm K S D d θ hθ, inv_one, one_zpow, one_pow, mul_one]
  simpa only [one_mul] using
    mul_le_mul hinactive hlocal (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)

/-- The cube's norm is the actual prime product over the active frozen support. -/
theorem numeratorCubeNorm_prime_product :
    (exteriorNorm K S (numeratorCube K S d i) : ℂ) =
      ∏ p ∈ i.activeFrozen, (p.val.asIdeal.absNorm : ℂ) ^
        frozenCubeExp (primeExponents i.numeratorFrozen.val p.val) := by
  have hs : (primeExponents (numeratorCube K S d i).val).support ⊆
      i.activeFrozen.image Subtype.val := by
    intro p hp
    have hdiv := (exponent_ne_zero_iff_dvd (numeratorCube K S d i).val p).mp
      (Finsupp.mem_support_iff.mp hp)
    let ep : ExteriorPrime K S := ⟨p, (numeratorCube K S d i).property p hdiv⟩
    have hep := numeratorCube_support K S d i ((mem_exteriorSupport_iff K S _ ep).mpr hdiv)
    exact Finset.mem_image.mpr ⟨ep, hep, rfl⟩
  have hn := norm_eq_prime_product (numeratorCube K S d i).val _ hs
  rw [Finset.prod_image] at hn
  · simpa only [exteriorNorm, Complex.ofReal_natCast, numeratorCube, exponent_cubePart] using hn
  · intro p _ q _ h
    exact Subtype.ext h

/-- Exact product scaling; the local phases have not been estimated here. -/
theorem localScalar_product_frozen :
    (∏ p ∈ i.activeFrozen, localWeylScalar K S D p (rowDigit K S d p)
      (primeExponents i.numeratorFrozen.val p.val)) =
    (exteriorNorm K S (numeratorCube K S d i) : ℂ)⁻¹ *
      ∏ p ∈ i.activeFrozen, localWeylScalar K S D p (rowDigit K S d p)
        (frozenMin (primeExponents i.numeratorFrozen.val p.val)) := by
  have hlocal (p : ExteriorPrime K S) := localWeylScalar_frozen K S D p
    (rowDigit K S d p) (primeExponents i.numeratorFrozen.val p.val)
      (numerator_admissible K S d i p.val)
  simp_rw [hlocal]
  rw [Finset.prod_mul_distrib, numeratorCubeNorm_prime_product]
  simp only [inv_pow, Finset.prod_inv_distrib]

def frozenMajorant : ℝ :=
  ∏ p ∈ i.activeFrozen, minimumMajorant K S p (rowDigit K S d p)
    (frozenMin (primeExponents i.numeratorFrozen.val p.val))

theorem frozenMajorant_nonneg : 0 ≤ frozenMajorant K S d i :=
  Finset.prod_nonneg (fun p _ => minimumMajorant_nonneg K S p _ _)

/-- The normalized actual Omega has exactly the charged finite-state bound. -/
theorem normalizedFrozenOmega_norm_le (θ : HeckeCharacter K)
    (hθ : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K θ p) :
    ‖normalizedFrozenOmega K S D d i θ‖ ≤ frozenMajorant K S d i := by
  have hx := exteriorNorm_pos K S (numeratorCube K S d i)
  have hlocal : ‖∏ p ∈ i.activeFrozen, localWeylScalar K S D p (rowDigit K S d p)
      (frozenMin (primeExponents i.numeratorFrozen.val p.val))‖ ≤ frozenMajorant K S d i := by
    rw [norm_prod]
    apply Finset.prod_le_prod₀
    · intro p _
      exact norm_nonneg _
    · intro p _
      exact localWeylScalar_minimum_norm_le K S D p _ _
  calc
    _ = exteriorNorm K S (numeratorCube K S d i) * ‖frozenOmega K S D d i θ‖ := by
      rw [normalizedFrozenOmega, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx]
    _ ≤ exteriorNorm K S (numeratorCube K S d i) *
        ‖∏ p ∈ i.activeFrozen, localWeylScalar K S D p (rowDigit K S d p)
          (primeExponents i.numeratorFrozen.val p.val)‖ := by
      rw [norm_prod]
      exact mul_le_mul_of_nonneg_left (frozenOmega_norm_le_local_product K S D d i θ hθ) hx.le
    _ = ‖∏ p ∈ i.activeFrozen, localWeylScalar K S D p (rowDigit K S d p)
        (frozenMin (primeExponents i.numeratorFrozen.val p.val))‖ := by
      rw [localScalar_product_frozen, norm_mul, norm_inv,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx,
        ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hx), one_mul]
    _ ≤ _ := hlocal

theorem prime_word_norm_le_one (p : ExteriorPrime K S)
    (a b c e : S.integer K) (m n : ℤ) :
    ‖primeEvaluation K S D p a * primeEvaluation K S D p b *
      primeEvaluation K S D p c ^ m * primeEvaluation K S D p e ^ n‖ ≤ 1 := by
  apply mul_norm_le_one
  · apply mul_norm_le_one
    · exact mul_norm_le_one _ _ (primeEvaluation_norm_le_one K S D p a)
        (primeEvaluation_norm_le_one K S D p b)
    · exact primeEvaluation_zpow_norm_le_one K S D p c m
  · exact primeEvaluation_zpow_norm_le_one K S D p e n

/-- Literal mark coefficients are contractions, with their zeros retained. -/
theorem reflectedMarkFactor_norm_le_one (θ : HeckeCharacter K)
    (hθ : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K θ p) :
    ‖reflectedMarkFactor K S D d i θ‖ ≤ 1 := by
  unfold reflectedMarkFactor
  apply mul_norm_le_one
  · apply mul_norm_le_one
    · rw [norm_pow, periodValue_norm K S D d θ hθ, one_pow]
    · apply prod_norm_le_one
      intro p _
      apply mul_norm_le_one
      · exact (thetaGamma_exteriorPrime_two_norm K S D p).le
      · rw [norm_pow]
        exact pow_le_one₀ (norm_nonneg _)
          (prime_word_norm_le_one K S D p _ _ _ _ (-2) (-2))
  · apply prod_norm_le_one
    intro p _
    exact primeEvaluation_zpow_norm_le_one K S D p _ _

/-- The squarefree-column factor has no analytic growth hidden in it. -/
theorem reflectedColumnFactor_norm_le_one (θ : HeckeCharacter K)
    (hθ : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K θ p) :
    ‖reflectedColumnFactor K S D d i θ‖ ≤ 1 := by
  unfold reflectedColumnFactor
  apply mul_norm_le_one
  · apply mul_norm_le_one
    · rw [norm_inv, periodValue_norm K S D d θ hθ, inv_one]
    · apply prod_norm_le_one
      intro p _
      exact primeEvaluation_pow_norm_le_one K S D p _ _
  · apply prod_norm_le_one
    intro p _
    apply mul_norm_le_one
    · exact (thetaGamma_exteriorPrime_two_norm K S D p).le
    · rw [norm_pow]
      apply pow_le_one₀ (norm_nonneg _)
      simpa only [zpow_one] using prime_word_norm_le_one K S D p _ _ _ _ 1 (-2)

/-- The residual-row factor is a pointwise contraction; no row extension is
used to establish this bound. -/
theorem reflectedRowFactor_norm_le_one (θ : HeckeCharacter K)
    (hθ : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K θ p) :
    ‖reflectedRowFactor K S D d i θ‖ ≤ 1 := by
  unfold reflectedRowFactor
  apply mul_norm_le_one
  · apply mul_norm_le_one
    · rw [norm_pow, periodValue_norm K S D d θ hθ, one_pow]
    · apply prod_norm_le_one
      intro p _
      apply mul_norm_le_one
      · rw [localWeylScalar_zero_norm]
        norm_num
      · exact prime_word_norm_le_one K S D p _ _ _ _ (-2) (-2)
  · apply prod_norm_le_one
    intro p _
    exact primeEvaluation_zpow_norm_le_one K S D p _ _

/-- Actual dual coefficient before the common Mellin/Fourier profile is
inserted.  Its bound has exactly the squarefree and full-cube denominators. -/
def fullCubeCoefficient (θ : HeckeCharacter K) : ℂ :=
  (normalizedFrozenOmega K S D d i θ *
    reflectedColumnFactor K S D d (minimumIndex K S d i) θ) /
      ((Real.sqrt (exteriorNorm K S i.c) : ℂ) *
        (exteriorNorm K S (fullCubeIdeal K S d i) : ℂ))

theorem fullCubeCoefficient_norm_le (θ : HeckeCharacter K)
    (hθ : ∀ p : HeightOneSpectrum (𝓞 K), p ∉ S → UnramifiedAt K θ p) :
    ‖fullCubeCoefficient K S D d i θ‖ ≤ frozenMajorant K S d i /
      (Real.sqrt (exteriorNorm K S i.c) * exteriorNorm K S (fullCubeIdeal K S d i)) := by
  have hc : 0 ≤ Real.sqrt (exteriorNorm K S i.c) := Real.sqrt_nonneg _
  have hb := exteriorNorm_pos K S (fullCubeIdeal K S d i)
  have hnum : ‖normalizedFrozenOmega K S D d i θ *
      reflectedColumnFactor K S D d (minimumIndex K S d i) θ‖ ≤ frozenMajorant K S d i := by
    rw [norm_mul]
    simpa only [mul_one] using mul_le_mul
      (normalizedFrozenOmega_norm_le K S D d i θ hθ)
      (reflectedColumnFactor_norm_le_one K S D d (minimumIndex K S d i) θ hθ)
      (norm_nonneg _) (frozenMajorant_nonneg K S d i)
  have hden : ‖(Real.sqrt (exteriorNorm K S i.c) : ℂ) *
      (exteriorNorm K S (fullCubeIdeal K S d i) : ℂ)‖ =
      Real.sqrt (exteriorNorm K S i.c) * exteriorNorm K S (fullCubeIdeal K S d i) := by
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hc, abs_of_pos hb]
  rw [fullCubeCoefficient, norm_div, hden]
  exact div_le_div_of_nonneg_right hnum (mul_nonneg hc hb.le)

#print axioms heckeIdealCoefficient_exterior_norm
#print axioms periodValue_norm
#print axioms localScalar_product_frozen
#print axioms normalizedFrozenOmega_norm_le
#print axioms reflectedMarkFactor_norm_le_one
#print axioms reflectedColumnFactor_norm_le_one
#print axioms reflectedRowFactor_norm_le_one
#print axioms fullCubeCoefficient_norm_le

end HeckeSkeleton.LowEnergy.ActualFrozenMajorant
