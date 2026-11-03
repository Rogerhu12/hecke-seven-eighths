import HeckeSkeleton.HighBinSupport.ActualEulerCRT

/-!
# Multiplicativity of the literal initial four-ideal term

The unmarked term is the original `initialRowEulerTerm` with `Q = ∅`.
The theorem below combines the actual CRT phase cancellation, the actual
Hecke ideal coefficient, positive ideal-norm complex powers, and the
squarefree indicator. The marked term is then related to this same term
by its literal completed-index divisibility mask; it is not asserted to
be multiplicative with the same nonempty mask in both factors.

AI-assisted: ChatGPT / GPT-6 Astra Pro, 2026-10-30.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace HeckeSkeleton.HighBinActualInitial

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.Analysis.SquarefreeAmplification
open HeckeGeneral.Arithmetic.IdealMobiusMask
open HeckeSkeleton.HighBinActualAbsolute HeckeSkeleton.HighBinActualCRT
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

local instance initialThetaFintype (I : ExteriorIdeal K S) :
    Fintype (ThetaQuotient K S I) := by
  letI : Finite (ThetaQuotient K S I) := finite_sIntegerSexticIdealQuotient K S
    I.val.val (nonZeroDivisors.coe_ne_zero I.val) I.property
  exact Fintype.ofFinite _

/-- Componentwise multiplication of the four original exterior ideals. -/
def fourIdealMul (I J : FourIdealIndex K S) : FourIdealIndex K S :=
  ((exteriorMul K S I.1.1 J.1.1, exteriorMul K S I.1.2 J.1.2),
    (exteriorMul K S I.2.1 J.2.1, exteriorMul K S I.2.2 J.2.2))

/-- This ideal has exactly the prime support of the four original variables. -/
def fourIdealSupportIdeal (I : FourIdealIndex K S) : ExteriorIdeal K S :=
  exteriorMul K S (exteriorMul K S I.2.1 (completedIdeal K S I.1.1 I.1.2)) I.2.2

@[simp] theorem primeSetIdeal_empty_val :
    (primeSetIdeal K S ∅).val.val = (1 : Ideal (𝓞 K)) := by
  simp only [primeSetIdeal, Finset.image_empty, squarefreeIdeal, primeProduct, Finset.prod_empty]

/-- The complex power identity uses positivity of the actual ideal norms. -/
theorem exteriorNorm_cpow_mul (I J : ExteriorIdeal K S) (z : ℂ) :
    (exteriorNorm K S (exteriorMul K S I J) : ℂ) ^ z =
      (exteriorNorm K S I : ℂ) ^ z * (exteriorNorm K S J : ℂ) ^ z := by
  rw [exteriorNorm_mul, Complex.ofReal_mul]
  exact Complex.mul_cpow_ofReal_nonneg (idealNorm_pos K I.val).le
    (idealNorm_pos K J.val).le z

/-- The remaining actual Hecke coefficient and Mellin weights. -/
def rowEulerWeight (P : ProbeData K S) (ψ : HeckeCharacter K)
    (s w z : ℂ) (I : FourIdealIndex K S) : ℂ :=
  heckeIdealCoefficient K (thetaPeriod K S P ψ) (completedIdeal K S I.1.1 I.1.2).val *
    (exteriorNorm K S I.1.1 : ℂ) ^ (-(1 / 2 : ℂ) - s) *
    (exteriorNorm K S I.1.2 : ℂ) ^ (-1 - 3 * s) *
    (exteriorNorm K S I.2.1 : ℂ) ^ (-w) *
    (exteriorNorm K S I.2.2 : ℂ) ^ (-6 * z)

/-- The original summand before applying its squarefree and marked masks. -/
def rowEulerUnmaskedTerm (P : ProbeData K S) (ψ : HeckeCharacter K)
    (u : FrequencyRow K S) (s w z : ℂ) (I : FourIdealIndex K S) : ℂ :=
  (thetaGamma K S P.arithmetic I.1.1 2 *
    finitePoissonFactor K S P I.2.1 (completedIdeal K S I.1.1 I.1.2)
      (poissonFrequency K S P u I.2.2)) * rowEulerWeight K S P ψ s w z I

theorem rowEulerWeight_mul (P : ProbeData K S) (ψ : HeckeCharacter K)
    (s w z : ℂ) (I J : FourIdealIndex K S) :
    rowEulerWeight K S P ψ s w z (fourIdealMul K S I J) =
      rowEulerWeight K S P ψ s w z I * rowEulerWeight K S P ψ s w z J := by
  have hcoef : heckeIdealCoefficient K (thetaPeriod K S P ψ)
      (completedIdeal K S (exteriorMul K S I.1.1 J.1.1)
        (exteriorMul K S I.1.2 J.1.2)).val =
      heckeIdealCoefficient K (thetaPeriod K S P ψ) (completedIdeal K S I.1.1 I.1.2).val *
      heckeIdealCoefficient K (thetaPeriod K S P ψ) (completedIdeal K S J.1.1 J.1.2).val := by
    rw [completedIdeal_mul]
    exact heckeIdealCoefficient_mul K _ _ _
  simp only [rowEulerWeight, fourIdealMul]
  rw [hcoef, exteriorNorm_cpow_mul, exteriorNorm_cpow_mul,
    exteriorNorm_cpow_mul, exteriorNorm_cpow_mul]
  ring

theorem rowEulerUnmaskedTerm_coprime_mul (P : ProbeData K S)
    (hP : AllowedGeneratorInput K S P.arithmetic) (ψ : HeckeCharacter K)
    (u : FrequencyRow K S) (s w z : ℂ) (I J : FourIdealIndex K S)
    (hIJ : IsCoprime (fourIdealSupportIdeal K S I).val.val
      (fourIdealSupportIdeal K S J).val.val) :
    rowEulerUnmaskedTerm K S P ψ u s w z (fourIdealMul K S I J) =
      rowEulerUnmaskedTerm K S P ψ u s w z I * rowEulerUnmaskedTerm K S P ψ u s w z J := by
  have hfinite := fourIdeal_finite_coefficient_coprime_product K S P hP u
    I.1.1 J.1.1 I.1.2 J.1.2 I.2.1 J.2.1 I.2.2 J.2.2 hIJ
  unfold rowEulerUnmaskedTerm
  rw [rowEulerWeight_mul]
  change (thetaGamma K S P.arithmetic (exteriorMul K S I.1.1 J.1.1) 2 *
    finitePoissonFactor K S P (exteriorMul K S I.2.1 J.2.1)
      (completedIdeal K S (exteriorMul K S I.1.1 J.1.1) (exteriorMul K S I.1.2 J.1.2))
      (poissonFrequency K S P u (exteriorMul K S I.2.2 J.2.2))) * _ = _
  rw [hfinite]
  ring

/-- An exact bridge back to the original definition, retaining its mask. -/
theorem initialRowEulerTerm_eq_masked (P : ProbeData K S) (ψ : HeckeCharacter K)
    (Q : Finset (ExteriorPrime K S)) (u : FrequencyRow K S)
    (s w z : ℂ) (I : FourIdealIndex K S) :
    initialRowEulerTerm K S P ψ Q u s w z I =
      if Squarefree I.1.1.val.val ∧
          (∀ p ∈ Q, p.val.asIdeal ∣ (completedIdeal K S I.1.1 I.1.2).val.val) then
        rowEulerUnmaskedTerm K S P ψ u s w z I else 0 := by
  simp only [initialRowEulerTerm, wholeIndexMask, primeSetIdeal_empty_val,
    isCoprime_one_right, true_and]
  split_ifs
  · unfold rowEulerUnmaskedTerm rowEulerWeight
    ring
  · rfl

theorem initialRowEulerTerm_empty (P : ProbeData K S) (ψ : HeckeCharacter K)
    (u : FrequencyRow K S) (s w z : ℂ) (I : FourIdealIndex K S) :
    initialRowEulerTerm K S P ψ ∅ u s w z I =
      if Squarefree I.1.1.val.val then rowEulerUnmaskedTerm K S P ψ u s w z I else 0 := by
  rw [initialRowEulerTerm_eq_masked]
  simp

/-- Multiplicativity of the original unmarked four-ideal term. -/
theorem initialRowEulerTerm_empty_coprime_mul (P : ProbeData K S)
    (hP : AllowedGeneratorInput K S P.arithmetic) (ψ : HeckeCharacter K)
    (u : FrequencyRow K S) (s w z : ℂ) (I J : FourIdealIndex K S)
    (hIJ : IsCoprime (fourIdealSupportIdeal K S I).val.val
      (fourIdealSupportIdeal K S J).val.val) :
    initialRowEulerTerm K S P ψ ∅ u s w z (fourIdealMul K S I J) =
      initialRowEulerTerm K S P ψ ∅ u s w z I * initialRowEulerTerm K S P ψ ∅ u s w z J := by
  have hA : IsCoprime (completedIdeal K S I.1.1 I.1.2).val.val
      (completedIdeal K S J.1.1 J.1.2).val.val :=
    hIJ.of_mul_left_left.of_mul_right_left.of_mul_left_right.of_mul_right_right
  have hc : IsCoprime I.1.1.val.val J.1.1.val.val := hA.of_mul_left_left.of_mul_right_left
  have hsq : Squarefree (fourIdealMul K S I J).1.1.val.val ↔
      Squarefree I.1.1.val.val ∧ Squarefree J.1.1.val.val := by
    change Squarefree (I.1.1.val.val * J.1.1.val.val) ↔ _
    rw [squarefree_mul_iff]
    simp only [hc.isRelPrime, true_and]
  rw [initialRowEulerTerm_empty, initialRowEulerTerm_empty, initialRowEulerTerm_empty]
  by_cases hI : Squarefree I.1.1.val.val <;> by_cases hJ : Squarefree J.1.1.val.val
  · rw [if_pos (hsq.mpr ⟨hI, hJ⟩), if_pos hI, if_pos hJ]
    exact rowEulerUnmaskedTerm_coprime_mul K S P hP ψ u s w z I J hIJ
  · rw [if_neg (fun h => hJ (hsq.mp h).2), if_neg hJ, mul_zero]
  · rw [if_neg (fun h => hI (hsq.mp h).1), if_neg hI, zero_mul]
  · rw [if_neg (fun h => hI (hsq.mp h).1), if_neg hI, zero_mul]

/-- Nonempty marks are a literal finite-support filter on the proved
unmarked term; they are never imposed independently on both CRT blocks. -/
theorem initialRowEulerTerm_eq_filter_empty (P : ProbeData K S)
    (ψ : HeckeCharacter K) (Q : Finset (ExteriorPrime K S)) (u : FrequencyRow K S)
    (s w z : ℂ) (I : FourIdealIndex K S) :
    initialRowEulerTerm K S P ψ Q u s w z I =
      if ∀ p ∈ Q, p.val.asIdeal ∣ (completedIdeal K S I.1.1 I.1.2).val.val then
        initialRowEulerTerm K S P ψ ∅ u s w z I else 0 := by
  rw [initialRowEulerTerm_eq_masked, initialRowEulerTerm_empty]
  by_cases hQ : ∀ p ∈ Q, p.val.asIdeal ∣ (completedIdeal K S I.1.1 I.1.2).val.val <;>
    by_cases hc : Squarefree I.1.1.val.val <;> simp [hQ, hc]

/-- The four unit ideals, in the existing index type. -/
def fourIdealOne : FourIdealIndex K S :=
  ((primeSetIdeal K S ∅, primeSetIdeal K S ∅),
    (primeSetIdeal K S ∅, primeSetIdeal K S ∅))

theorem thetaQuotient_subsingleton_of_val_one (I : ExteriorIdeal K S)
    (hI : I.val.val = 1) : Subsingleton (ThetaQuotient K S I) := by
  apply Ideal.Quotient.subsingleton_iff.mpr
  rw [hI, Ideal.one_eq_top, Ideal.map_top]

theorem exteriorNorm_eq_one_of_val_one (I : ExteriorIdeal K S)
    (hI : I.val.val = 1) : exteriorNorm K S I = 1 := by
  simp [exteriorNorm, hI]

/-- The inner Gauss sum over the unit quotient is one, at every frequency. -/
theorem probeGaussOnQuotient_unit_ideal (P : ProbeData K S)
    (I : ExteriorIdeal K S) (hI : I.val.val = 1) (h : ThetaQuotient K S I) :
    probeGaussOnQuotient K S P I h = 1 := by
  letI := thetaQuotient_subsingleton_of_val_one K S I hI
  change (∑ x : ThetaQuotient K S I, quotientSymbol K S P.arithmetic I x *
    thetaPrincipalAddCharacter K S P.arithmetic I (h * x)) = 1
  rw [Fintype.sum_subsingleton _ (1 : ThetaQuotient K S I), quotientSymbol_one, one_mul,
    Subsingleton.elim (h * 1) (0 : ThetaQuotient K S I), AddChar.map_zero_eq_one]

/-- The normalization of thetaGamma is also one at the unit ideal. -/
theorem thetaGamma_unit_ideal (D : ThetaArithmeticData K S)
    (I : ExteriorIdeal K S) (hI : I.val.val = 1) (j : ℕ) : thetaGamma K S D I j = 1 := by
  letI := thetaQuotient_subsingleton_of_val_one K S I hI
  have hN := exteriorNorm_eq_one_of_val_one K S I hI
  change (Real.sqrt (exteriorNorm K S I) : ℂ)⁻¹ *
    (∑ x : ThetaQuotient K S I, quotientSymbol K S D I x ^ j *
      thetaPrincipalAddCharacter K S D I x) = 1
  rw [hN, Real.sqrt_one, Complex.ofReal_one, inv_one, one_mul,
    Fintype.sum_subsingleton _ (1 : ThetaQuotient K S I), quotientSymbol_one,
    one_pow, one_mul, Subsingleton.elim (1 : ThetaQuotient K S I) 0,
    AddChar.map_zero_eq_one]

/-- The original two-layer finite Poisson factor on two unit ideals is one.
The zero residue remains the unique element of the unit quotient. -/
theorem finitePoissonFactor_unit_ideals (P : ProbeData K S)
    (den A : ExteriorIdeal K S) (hden : den.val.val = 1) (hA : A.val.val = 1)
    (h : S.integer K) : finitePoissonFactor K S P den A h = 1 := by
  have hB : (exteriorMul K S den A).val.val = 1 := by
    change den.val.val * A.val.val = 1
    rw [hden, hA, one_mul]
  letI := thetaQuotient_subsingleton_of_val_one K S (exteriorMul K S den A) hB
  rw [finitePoissonFactor_eq_fourier, exteriorNorm_eq_one_of_val_one K S den hden,
    Complex.ofReal_one, inv_one, one_mul]
  unfold HighBin.FiniteResidueFourier.fourier
  rw [Fintype.sum_subsingleton _ (1 : ThetaQuotient K S (exteriorMul K S den A))]
  simp only [poissonCore, map_one]
  rw [probeGaussOnQuotient_unit_ideal K S P den hden, quotientSymbol_one, one_mul, one_mul,
    Subsingleton.elim (Ideal.Quotient.mk _ h * 1)
      (0 : ThetaQuotient K S (exteriorMul K S den A)), AddChar.map_zero_eq_one]

theorem rowEulerWeight_one (P : ProbeData K S) (ψ : HeckeCharacter K)
    (s w z : ℂ) : rowEulerWeight K S P ψ s w z (fourIdealOne K S) = 1 := by
  have hunit : (primeSetIdeal K S ∅).val = (1 : NonzeroIdeal K) :=
    Subtype.ext (primeSetIdeal_empty_val K S)
  have hA : (completedIdeal K S (primeSetIdeal K S ∅) (primeSetIdeal K S ∅)).val =
      (1 : NonzeroIdeal K) := by
    change (primeSetIdeal K S ∅).val * ((primeSetIdeal K S ∅).val *
      ((primeSetIdeal K S ∅).val * (primeSetIdeal K S ∅).val)) = 1
    rw [hunit]
    simp
  have hN : exteriorNorm K S (primeSetIdeal K S ∅) = 1 :=
    exteriorNorm_eq_one_of_val_one K S _ (primeSetIdeal_empty_val K S)
  simp only [rowEulerWeight, fourIdealOne, hA, hN, Complex.ofReal_one,
    Complex.one_cpow, mul_one]
  exact idealCoefficient_one (primeCoefficient K (thetaPeriod K S P ψ))

/-- The zero exponent vector has the required original unmarked term 1. -/
theorem initialRowEulerTerm_empty_one (P : ProbeData K S) (ψ : HeckeCharacter K)
    (u : FrequencyRow K S) (s w z : ℂ) :
    initialRowEulerTerm K S P ψ ∅ u s w z (fourIdealOne K S) = 1 := by
  have hI := primeSetIdeal_empty_val K S
  have hA : (completedIdeal K S (primeSetIdeal K S ∅) (primeSetIdeal K S ∅)).val.val = 1 := by
    change (primeSetIdeal K S ∅).val.val * ((primeSetIdeal K S ∅).val.val *
      ((primeSetIdeal K S ∅).val.val * (primeSetIdeal K S ∅).val.val)) = 1
    rw [hI]
    simp
  rw [initialRowEulerTerm_empty]
  have hsquare : Squarefree (fourIdealOne K S).1.1.val.val := by
    change Squarefree (primeSetIdeal K S ∅).val.val
    rw [hI]
    exact squarefree_one
  rw [if_pos hsquare]
  unfold rowEulerUnmaskedTerm
  rw [rowEulerWeight_one]
  change (thetaGamma K S P.arithmetic (primeSetIdeal K S ∅) 2 *
    finitePoissonFactor K S P (primeSetIdeal K S ∅)
      (completedIdeal K S (primeSetIdeal K S ∅) (primeSetIdeal K S ∅)) _) * 1 = 1
  rw [thetaGamma_unit_ideal K S P.arithmetic _ hI,
    finitePoissonFactor_unit_ideals K S P _ _ hI hA, one_mul, one_mul]

/-- Prime exponents in the mask are the actual c and n exponents. -/
theorem completedIdeal_primeExponents (c n : ExteriorIdeal K S)
    (p : HeightOneSpectrum (𝓞 K)) :
    primeExponents (completedIdeal K S c n).val p =
      primeExponents c.val p + 3 * primeExponents n.val p := by
  change primeExponents (c.val * (n.val * (n.val * n.val))) p = _
  simp only [primeExponents_mul, Finsupp.add_apply]
  omega

/-- The mark condition is the same positive completed exponent used by
local Euler masks, without dropping any completed cube. -/
theorem completedIdeal_prime_dvd_iff (c n : ExteriorIdeal K S)
    (p : ExteriorPrime K S) :
    p.val.asIdeal ∣ (completedIdeal K S c n).val.val ↔
      0 < primeExponents c.val p.val + 3 * primeExponents n.val p.val := by
  rw [← mem_idealPrimeSupport_iff K (completedIdeal K S c n).val p.val]
  change p.val ∈ (primeExponents (completedIdeal K S c n).val).support ↔ _
  rw [Finsupp.mem_support_iff, completedIdeal_primeExponents]
  exact Nat.pos_iff_ne_zero.symm

/-- The precise exponent-mask form needed by finite-support Euler assembly. -/
theorem initialRowEulerTerm_eq_exponent_filter (P : ProbeData K S)
    (ψ : HeckeCharacter K) (Q : Finset (ExteriorPrime K S)) (u : FrequencyRow K S)
    (s w z : ℂ) (I : FourIdealIndex K S) :
    initialRowEulerTerm K S P ψ Q u s w z I =
      if ∀ p ∈ Q, 0 < primeExponents I.1.1.val p.val + 3 * primeExponents I.1.2.val p.val then
        initialRowEulerTerm K S P ψ ∅ u s w z I else 0 := by
  rw [initialRowEulerTerm_eq_filter_empty]
  simp_rw [completedIdeal_prime_dvd_iff]

#print axioms rowEulerUnmaskedTerm_coprime_mul
#print axioms initialRowEulerTerm_empty_coprime_mul
#print axioms initialRowEulerTerm_eq_filter_empty
#print axioms initialRowEulerTerm_empty_one
#print axioms initialRowEulerTerm_eq_exponent_filter
end HeckeSkeleton.HighBinActualInitial
