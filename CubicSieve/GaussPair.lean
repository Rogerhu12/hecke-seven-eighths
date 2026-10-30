import CubicSieve.GaussPairCRT
import CubicSieve.GaussPoissonFinite

/-!
The actual mixed pair Gauss sum with literal denominator generator(I)*generator(J).
No multiplicativity of the chosen generator as an equality of elements is used.
The two reciprocal cubic factors cancel by the allowed-section reciprocity;
the inverse cubic character has the conjugate Gauss sum because it is even.
-/

set_option autoImplicit false
noncomputable section
namespace CubicSieve.GaussPair

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.ThetaSkeleton
open HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.Arithmetic.ResidueTraceCharacters
open CubicSieve.GaussCharacters
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

abbrev principalIdeal (I : ExteriorIdeal K S) : Ideal (S.integer K) :=
  Ideal.span ({D.generator I} : Set (S.integer K))

abbrev PrincipalQuotient (I : ExteriorIdeal K S) := S.integer K ⧸ principalIdeal K S D I
abbrev PairQuotient (I J : ExteriorIdeal K S) :=
  S.integer K ⧸ principalIdeal K S D I * principalIdeal K S D J

def literalEquiv (I J : ExteriorIdeal K S) :
    PairQuotient K S D I J ≃+*
      (S.integer K ⧸ Ideal.span ({D.generator I * D.generator J} : Set (S.integer K))) :=
  Ideal.quotEquivOfEq (Ideal.span_singleton_mul_span_singleton (D.generator I) (D.generator J))

instance principalFinite (I : ExteriorIdeal K S) : Finite (PrincipalQuotient K S D I) :=
  finite_sIntegerPrincipalResidue K S (D.generator I) (D.generator_ne_zero I)

instance principalFintype (I : ExteriorIdeal K S) : Fintype (PrincipalQuotient K S D I) :=
  Fintype.ofFinite _

instance pairFinite (I J : ExteriorIdeal K S) : Finite (PairQuotient K S D I J) := by
  letI := finite_sIntegerPrincipalResidue K S (D.generator I * D.generator J)
    (mul_ne_zero (D.generator_ne_zero I) (D.generator_ne_zero J))
  exact Finite.of_equiv _ (literalEquiv K S D I J).symm.toEquiv

instance pairFintype (I J : ExteriorIdeal K S) : Fintype (PairQuotient K S D I J) :=
  Fintype.ofFinite _

def principalPhase (I : ExteriorIdeal K S) : AddChar (PrincipalQuotient K S D I) ℂ :=
  sIntegerActualModulusAddCharacter K S D.different_outside
    (D.generator I) (D.generator_ne_zero I)

@[simp] theorem principalPhase_mk (I : ExteriorIdeal K S) (a : S.integer K) :
    principalPhase K S D I (Ideal.Quotient.mk _ a) =
      sLocalPrincipalPhase K S ((a : K) / (D.generator I : K)) :=
  sIntegerActualModulusAddCharacter_mk K S D.different_outside _ _ a

def pairPhase (I J : ExteriorIdeal K S) : AddChar (PairQuotient K S D I J) ℂ :=
  transportCharacter (literalEquiv K S D I J)
    (sIntegerActualModulusAddCharacter K S D.different_outside
      (D.generator I * D.generator J)
      (mul_ne_zero (D.generator_ne_zero I) (D.generator_ne_zero J)))

/-- The literal phase, retaining every local factor at the original S. -/
@[simp] theorem pairPhase_mk (I J : ExteriorIdeal K S) (a : S.integer K) :
    pairPhase K S D I J (Ideal.Quotient.mk _ a) =
      sLocalPrincipalPhase K S ((a : K) / ((D.generator I : K) * (D.generator J : K))) := by
  change sIntegerActualModulusAddCharacter K S D.different_outside
    (D.generator I * D.generator J)
    (mul_ne_zero (D.generator_ne_zero I) (D.generator_ne_zero J))
      ((Ideal.quotEquivOfEq
        (Ideal.span_singleton_mul_span_singleton (D.generator I) (D.generator J)))
          (Ideal.Quotient.mk _ a)) = _
  rw [Ideal.quotEquivOfEq_mk]
  exact sIntegerActualModulusAddCharacter_mk K S D.different_outside _ _ a

theorem principal_coprime (I J : ExteriorIdeal K S) (h : IsCoprime I.val.val J.val.val) :
    IsCoprime (principalIdeal K S D I) (principalIdeal K S D J) := by
  apply Ideal.isCoprime_iff_sup_eq.mpr
  change Ideal.span ({D.generator I} : Set (S.integer K)) ⊔
    Ideal.span ({D.generator J} : Set (S.integer K)) = ⊤
  rw [D.generator_span, D.generator_span, ← Ideal.map_sup, h.sup_eq, Ideal.map_top]

def normalizer (I : ExteriorIdeal K S) : ℂ :=
  (Real.sqrt (exteriorNorm K S I) : ℂ)⁻¹

theorem normalizer_mul (I J : ExteriorIdeal K S) :
    normalizer K S (exteriorMul K S I J) = normalizer K S I * normalizer K S J := by
  have hn : exteriorNorm K S (exteriorMul K S I J) =
      exteriorNorm K S I * exteriorNorm K S J := by
    simp only [exteriorNorm, exteriorMul, Submonoid.coe_mul, map_mul, Nat.cast_mul]
  have hi : 0 ≤ exteriorNorm K S I := by unfold exteriorNorm; positivity
  simp only [normalizer, hn, Real.sqrt_mul hi, Complex.ofReal_mul, mul_inv]

theorem normalizer_star (I : ExteriorIdeal K S) : star (normalizer K S I) = normalizer K S I := by
  simp [normalizer]

def pairRow (I J : ExteriorIdeal K S) (hI : Squarefree I.val.val)
    (hJ : Squarefree J.val.val) (x : PairQuotient K S D I J) : ℂ :=
  (principalCubicCharacter K S D I hI)⁻¹
      (Ideal.Quotient.factor (Ideal.mul_le_left : principalIdeal K S D I * principalIdeal K S D J ≤ _) x) *
    principalCubicCharacter K S D J hJ
      (Ideal.Quotient.factor (Ideal.mul_le_right : principalIdeal K S D I * principalIdeal K S D J ≤ _) x)

/-- This coefficient retains the actual shared-prime/nonunit zeros. -/
theorem pairRow_mk (I J : ExteriorIdeal K S) (hI : Squarefree I.val.val)
    (hJ : Squarefree J.val.val) (a : S.integer K) :
    pairRow K S D I J hI hJ (Ideal.Quotient.mk _ a) =
      star (idealSymbol K S D I a ^ 2) * idealSymbol K S D J a ^ 2 := by
  simp only [pairRow, Ideal.Quotient.factor_mk]
  change (principalCubicCharacter K S D I hI)⁻¹
      (Ideal.Quotient.mk (Ideal.span ({D.generator I} : Set (S.integer K))) a) *
    principalCubicCharacter K S D J hJ
      (Ideal.Quotient.mk (Ideal.span ({D.generator J} : Set (S.integer K))) a) = _
  rw [← MulChar.star_apply']
  simp only [principalCubicCharacter_mk, idealSymbol]

def pairNormalizedGauss (I J : ExteriorIdeal K S) (hI : Squarefree I.val.val)
    (hJ : Squarefree J.val.val) : ℂ :=
  normalizer K S (exteriorMul K S I J) *
    ∑ x : PairQuotient K S D I J, pairRow K S D I J hI hJ x * pairPhase K S D I J x

theorem crossfactor_cancel (hD : AllowedGeneratorInput K S D)
    (I J : ExteriorIdeal K S) (hI : Squarefree I.val.val) (hJ : Squarefree J.val.val)
    (hcop : IsCoprime I.val.val J.val.val) :
    (principalCubicCharacter K S D I hI)⁻¹ (Ideal.Quotient.mk _ (D.generator J)) *
      principalCubicCharacter K S D J hJ (Ideal.Quotient.mk _ (D.generator I)) = 1 := by
  rw [MulChar.inv_apply_eq_inv', principalCubicCharacter_mk, principalCubicCharacter_mk]
  change (idealSymbol K S D I (D.generator J) ^ 2)⁻¹ *
    idealSymbol K S D J (D.generator I) ^ 2 = 1
  rw [← hD.reciprocity I J]
  apply inv_mul_cancel₀
  apply pow_ne_zero
  intro hz
  exact ((ExteriorKernel.symbol_eq_zero_iff_not_coprime K S D J I).mp hz) hcop.symm

theorem normalized_principal_gauss_eq (I : ExteriorIdeal K S) (hI : Squarefree I.val.val) :
    normalizer K S I * gaussSum (principalCubicCharacter K S D I hI)
      (principalPhase K S D I) = thetaGamma K S D I 2 := by
  unfold principalPhase
  rw [GaussPoissonFinite.principal_gauss_eq K S D I hI]
  have hpos : 0 < (I.val.val.absNorm : ℝ) := by
    exact_mod_cast Ideal.absNorm_pos_of_nonZeroDivisors I.val
  have hsqrt : (Real.sqrt (I.val.val.absNorm : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hpos).ne'
  change (Real.sqrt (I.val.val.absNorm : ℝ) : ℂ)⁻¹ *
    ((Real.sqrt (I.val.val.absNorm : ℝ) : ℂ) * thetaGamma K S D I 2) = _
  rw [← mul_assoc, inv_mul_cancel₀ hsqrt, one_mul]

/-- The genuine normalized pair Gauss factor separates with its original phase. -/
theorem pairNormalizedGauss_eq (hD : AllowedGeneratorInput K S D)
    (I J : ExteriorIdeal K S) (hI : Squarefree I.val.val) (hJ : Squarefree J.val.val)
    (hcop : IsCoprime I.val.val J.val.val) :
    pairNormalizedGauss K S D I J hI hJ =
      star (thetaGamma K S D I 2) * thetaGamma K S D J 2 := by
  obtain ⟨u, v, hbez⟩ := GaussPairCRT.bezout_of_principal_coprime (principal_coprime K S D I J hcop)
  have ha : ((S.integer K).val.toRingHom (D.generator I)) ≠ 0 := by
    intro h
    exact D.generator_ne_zero I (Subtype.ext h)
  have hb : ((S.integer K).val.toRingHom (D.generator J)) ≠ 0 := by
    intro h
    exact D.generator_ne_zero J (Subtype.ext h)
  have hr := GaussPairCRT.gauss_sum_principal_crt
    (S.integer K).val.toRingHom (sLocalPrincipalPhase K S) hbez ha hb
    (principalPhase K S D I) (principalPhase K S D J) (pairPhase K S D I J)
    (principalPhase_mk K S D I) (principalPhase_mk K S D J) (pairPhase_mk K S D I J)
    (principalCubicCharacter K S D I hI)⁻¹ (principalCubicCharacter K S D J hJ)
  rw [crossfactor_cancel K S D hD I J hI hJ hcop, one_mul,
    GaussPairCRT.gauss_inverse_even _ _ (principalCubicCharacter_neg_one K S D I hI)] at hr
  unfold pairNormalizedGauss
  change normalizer K S (exteriorMul K S I J) * _ = _
  simp only [pairRow]
  rw [hr, normalizer_mul, ← normalized_principal_gauss_eq K S D I hI,
    ← normalized_principal_gauss_eq K S D J hJ, star_mul, normalizer_star]
  ring

end CubicSieve.GaussPair
