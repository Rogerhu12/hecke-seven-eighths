import HeckeSkeleton.Moments.MOM_INV_STEP.UnitGaussTransport
import HeckeSkeleton.Moments.MOM_INV_STEP.GaussConjugation
import HeckeSkeleton.Moments.MOM_INV_STEP.ActualFiniteSource
import HeckeGeneral.Analysis.MarkedThetaReflection

/-!
# Actual theta Gauss sums and signed coprime multiplication

Every sum below is the literal finite sum in `thetaGamma`. The bridge to
principal quotients is a proved equality-of-ideals transport. Coprime
multiplication uses the actual CRT, and the allowed generator discrepancy
is removed by its proved sixth-unit invariance.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.ThetaGaussCRT

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open PrincipalGaussCRT UnitGaussTransport GaussConjugation
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
local notation "OS" => Set.integer S K
variable (D : ThetaArithmeticData K S)

/-- An actual ideal quotient presented by any verified principal generator. -/
def idealQuotientAt (I : ExteriorIdeal K S) (c : OS)
    (hcspan : Ideal.span ({c} : Set OS) = I.val.val.map (algebraMap (𝓞 K) OS)) :
    QuotientRing OS c ≃+* ThetaQuotient K S I :=
  Ideal.quotEquivOfEq hcspan

@[simp] theorem idealQuotientAt_mk (I : ExteriorIdeal K S) (c : OS)
    (hcspan : Ideal.span ({c} : Set OS) = I.val.val.map (algebraMap (𝓞 K) OS)) (a : OS) :
    idealQuotientAt K S I c hcspan (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ a :=
  Ideal.quotEquivOfEq_mk hcspan a

/-- The actual ideal row raised as a scalar power, including its zeros. -/
def idealCharacterAt (I : ExteriorIdeal K S) (c : OS)
    (hcspan : Ideal.span ({c} : Set OS) = I.val.val.map (algebraMap (𝓞 K) OS))
    (j : ℕ) : QuotientRing OS c →* ℂ where
  toFun q := quotientRow K S D I (idealQuotientAt K S I c hcspan q) ^ j
  map_one' := by simp
  map_mul' x y := by simp only [map_mul, mul_pow]

@[simp] theorem idealCharacterAt_mk (I : ExteriorIdeal K S) (c : OS)
    (hcspan : Ideal.span ({c} : Set OS) = I.val.val.map (algebraMap (𝓞 K) OS))
    (j : ℕ) (a : OS) :
    idealCharacterAt K S D I c hcspan j (Ideal.Quotient.mk _ a) =
      idealSymbol K S D I a ^ j := by
  change quotientRow K S D I
    (idealQuotientAt K S I c hcspan (Ideal.Quotient.mk _ a)) ^ j = _
  rw [idealQuotientAt_mk, quotientRow_mk]

def idealGaussAt (I : ExteriorIdeal K S) (c : OS) (hc : c ≠ 0)
    (hcspan : Ideal.span ({c} : Set OS) = I.val.val.map (algebraMap (𝓞 K) OS))
    (j : ℕ) : ℂ :=
  principalGauss K S D.different_outside c hc (idealCharacterAt K S D I c hcspan j)

/-- The selected-generator principal sum is exactly thetaGamma's sum. -/
theorem thetaGamma_eq_principalGauss (I : ExteriorIdeal K S) (j : ℕ) :
    thetaGamma K S D I j =
      (Real.sqrt (I.val.val.absNorm : ℝ) : ℂ)⁻¹ *
        idealGaussAt K S D I (D.generator I) (D.generator_ne_zero I)
          (D.generator_span I) j := by
  letI : Finite (ThetaQuotient K S I) :=
    finite_sIntegerSexticIdealQuotient K S I.val.val
      (nonZeroDivisors.coe_ne_zero I.val) I.property
  letI : Fintype (ThetaQuotient K S I) := Fintype.ofFinite _
  letI := finite_sIntegerPrincipalResidue K S (D.generator I) (D.generator_ne_zero I)
  letI := Fintype.ofFinite (QuotientRing OS (D.generator I))
  change (Real.sqrt (I.val.val.absNorm : ℝ) : ℂ)⁻¹ *
      (∑ q : ThetaQuotient K S I,
        quotientRow K S D I q ^ j * thetaPrincipalAddCharacter K S D I q) =
    (Real.sqrt (I.val.val.absNorm : ℝ) : ℂ)⁻¹ *
      ∑ q : QuotientRing OS (D.generator I),
        idealCharacterAt K S D I (D.generator I) (D.generator_span I) j q *
          sIntegerActualModulusAddCharacter K S D.different_outside
            (D.generator I) (D.generator_ne_zero I) q
  congr 1
  let e := idealQuotientAt K S I (D.generator I) (D.generator_span I)
  refine Fintype.sum_bijective e.symm e.symm.bijective _ _ ?_
  intro q
  change quotientRow K S D I q ^ j * thetaPrincipalAddCharacter K S D I q =
    quotientRow K S D I (e (e.symm q)) ^ j *
      sIntegerActualModulusAddCharacter K S D.different_outside
        (D.generator I) (D.generator_ne_zero I) (e.symm q)
  rw [RingEquiv.apply_symm_apply]
  rfl

theorem thetaGamma_eq_idealGaussAt (I : ExteriorIdeal K S) (j : ℕ)
    (c : OS) (hc : c ≠ 0)
    (hcspan : Ideal.span ({c} : Set OS) = I.val.val.map (algebraMap (𝓞 K) OS))
    (hgen : D.generator I = c) :
    thetaGamma K S D I j = (Real.sqrt (I.val.val.absNorm : ℝ) : ℂ)⁻¹ *
      idealGaussAt K S D I c hc hcspan j := by
  subst c
  exact thetaGamma_eq_principalGauss K S D I j

theorem idealCharacterAt_sixth_unit (I : ExteriorIdeal K S) (c : OS)
    (hcspan : Ideal.span ({c} : Set OS) = I.val.val.map (algebraMap (𝓞 K) OS))
    (j : ℕ) (u : S.unit K) :
    idealCharacterAt K S D I c hcspan j
      (Ideal.Quotient.mk _ ((S.unitEquivUnitsInteger K u).val ^ 6)) = 1 := by
  rw [idealCharacterAt_mk]
  have h := sIntegerSexticIdealEvaluation_sixth_power_unit K S
    D.root6 D.primitive6 D.embedding I.val.val (nonZeroDivisors.coe_ne_zero I.val)
    I.property (fun p hp => D.away_six p (I.property p hp)) u
  change idealSymbol K S D I ((S.unitEquivUnitsInteger K u).val ^ 6) = 1 at h
  rw [h, one_pow]

/-- The actual ideal Gauss sum is unchanged by a sixth-power unit change
of generator; both principal quotient coefficients are constructed. -/
theorem idealGaussAt_sixth_unit (I : ExteriorIdeal K S) (c : OS) (hc : c ≠ 0)
    (hcspan : Ideal.span ({c} : Set OS) = I.val.val.map (algebraMap (𝓞 K) OS))
    (j : ℕ) (u : S.unit K)
    (hvspan : Ideal.span ({((S.unitEquivUnitsInteger K u) ^ 6).val * c} : Set OS) =
      I.val.val.map (algebraMap (𝓞 K) OS)) :
    idealGaussAt K S D I (((S.unitEquivUnitsInteger K u) ^ 6).val * c)
        (mul_ne_zero ((S.unitEquivUnitsInteger K u) ^ 6).ne_zero hc) hvspan j =
      idealGaussAt K S D I c hc hcspan j := by
  let v := (S.unitEquivUnitsInteger K u) ^ 6
  have hchar : idealCharacterAt K S D I (v.val * c) hvspan j =
      unitCharacter c v (idealCharacterAt K S D I c hcspan j) := by
    apply MonoidHom.ext
    intro q
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
    rw [idealCharacterAt_mk]
    change idealSymbol K S D I a ^ j =
      idealCharacterAt K S D I c hcspan j (unitQuotient c v (Ideal.Quotient.mk _ a))
    rw [unitQuotient_mk, idealCharacterAt_mk]
  unfold idealGaussAt
  rw [hchar, principalGauss_unit_of_value_one]
  simpa only [v, Units.val_pow_eq_pow_val] using
    idealCharacterAt_sixth_unit K S D I c hcspan j u

/-- Coprimality of actual ideals gives coprimality of their selected
S-integer generators, directly by mapping the ideal sum. -/
theorem generators_coprime (I J : ExteriorIdeal K S)
    (hcop : IsCoprime I.val.val J.val.val) : IsCoprime (D.generator I) (D.generator J) := by
  rw [← Ideal.isCoprime_span_singleton_iff, D.generator_span, D.generator_span,
    Ideal.isCoprime_iff_sup_eq, ← Ideal.map_sup, hcop.sup_eq, Ideal.map_top]

theorem productGenerator_span (I J : ExteriorIdeal K S) :
    Ideal.span ({D.generator I * D.generator J} : Set OS) =
      (exteriorMul K S I J).val.val.map (algebraMap (𝓞 K) OS) := by
  rw [← Ideal.span_singleton_mul_span_singleton, D.generator_span, D.generator_span]
  exact (Ideal.map_mul (algebraMap (𝓞 K) OS) I.val.val J.val.val).symm

theorem idealSymbol_mul_denominator (I J : ExteriorIdeal K S) (a : OS) :
    idealSymbol K S D (exteriorMul K S I J) a =
      idealSymbol K S D I a * idealSymbol K S D J a := by
  exact ActualFiniteSource.PrimeBlock.actual_ideal_mul_denominator K S
    D.root6 D.primitive6 D.embedding I.val.val J.val.val
    (nonZeroDivisors.coe_ne_zero I.val) (nonZeroDivisors.coe_ne_zero J.val)
    (fun p hp => hp.elim (I.property p) (J.property p))
    (fun p hp => D.away_six p (hp.elim (I.property p) (J.property p))) a

/-- The actual product-ideal row is the actual CRT product row. -/
theorem idealCharacterAt_product (I J : ExteriorIdeal K S)
    (hcop : IsCoprime I.val.val J.val.val) (j : ℕ) :
    idealCharacterAt K S D (exteriorMul K S I J) (D.generator I * D.generator J)
        (productGenerator_span K S D I J) j =
      compositeCharacter (D.generator I) (D.generator J) (generators_coprime K S D I J hcop)
        (idealCharacterAt K S D I (D.generator I) (D.generator_span I) j)
        (idealCharacterAt K S D J (D.generator J) (D.generator_span J) j) := by
  apply MonoidHom.ext
  intro q
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [idealCharacterAt_mk, idealSymbol_mul_denominator, mul_pow]
  change _ =
    idealCharacterAt K S D I (D.generator I) (D.generator_span I) j
      (quotientCRT (D.generator I) (D.generator J)
        (generators_coprime K S D I J hcop) (Ideal.Quotient.mk _ a)).1 *
    idealCharacterAt K S D J (D.generator J) (D.generator_span J) j
      (quotientCRT (D.generator I) (D.generator J)
        (generators_coprime K S D I J hcop) (Ideal.Quotient.mk _ a)).2
  rw [quotientCRT_mk, idealCharacterAt_mk, idealCharacterAt_mk]

/-- Proved signed CRT for the product generator before the allowed
generator section is applied. -/
theorem idealGaussAt_product (I J : ExteriorIdeal K S)
    (hcop : IsCoprime I.val.val J.val.val) (j : ℕ) :
    idealGaussAt K S D (exteriorMul K S I J) (D.generator I * D.generator J)
        (mul_ne_zero (D.generator_ne_zero I) (D.generator_ne_zero J))
        (productGenerator_span K S D I J) j =
      (idealSymbol K S D I (D.generator J) ^ j *
        idealSymbol K S D J (D.generator I) ^ j) *
      idealGaussAt K S D I (D.generator I) (D.generator_ne_zero I) (D.generator_span I) j *
      idealGaussAt K S D J (D.generator J) (D.generator_ne_zero J) (D.generator_span J) j := by
  unfold idealGaussAt
  rw [idealCharacterAt_product K S D I J hcop j,
    principalGauss_mul K S D.different_outside (D.generator I) (D.generator J)
      (D.generator_ne_zero I) (D.generator_ne_zero J)
      (generators_coprime K S D I J hcop), idealCharacterAt_mk, idealCharacterAt_mk]

/-- Exact normalized coprime multiplication for the actual theta Gauss
coefficients. The only arithmetic input is the explicit allowed section
from MOM_BASE; the finite CRT identity is proved in this module. -/
theorem thetaGamma_mul (hallowed : AllowedGeneratorInput K S D)
    (I J : ExteriorIdeal K S) (hcop : IsCoprime I.val.val J.val.val) (j : ℕ) :
    thetaGamma K S D (exteriorMul K S I J) j =
      (idealSymbol K S D I (D.generator J) ^ j *
        idealSymbol K S D J (D.generator I) ^ j) *
        thetaGamma K S D I j * thetaGamma K S D J j := by
  obtain ⟨u, hu⟩ := hallowed.multiplicative I J
  let c := D.generator I * D.generator J
  let v := (S.unitEquivUnitsInteger K u) ^ 6
  have hc : c ≠ 0 := mul_ne_zero (D.generator_ne_zero I) (D.generator_ne_zero J)
  have hgen : D.generator (exteriorMul K S I J) = v.val * c := by
    simpa only [v, c, Units.val_pow_eq_pow_val, mul_assoc] using hu
  have hvspan : Ideal.span ({v.val * c} : Set OS) =
      (exteriorMul K S I J).val.val.map (algebraMap (𝓞 K) OS) := by
    rw [← hgen]
    exact D.generator_span _
  rw [thetaGamma_eq_idealGaussAt K S D (exteriorMul K S I J) j
    (v.val * c) (mul_ne_zero v.ne_zero hc) hvspan hgen]
  rw [idealGaussAt_sixth_unit K S D (exteriorMul K S I J) c hc
    (productGenerator_span K S D I J) j u hvspan]
  rw [idealGaussAt_product K S D I J hcop j,
    thetaGamma_eq_principalGauss K S D I j, thetaGamma_eq_principalGauss K S D J j]
  have hnorm : (Real.sqrt ((exteriorMul K S I J).val.val.absNorm : ℝ) : ℂ) =
      (Real.sqrt (I.val.val.absNorm : ℝ) : ℂ) *
        (Real.sqrt (J.val.val.absNorm : ℝ) : ℂ) := by
    change (Real.sqrt ((I.val.val * J.val.val).absNorm : ℝ) : ℂ) = _
    rw [map_mul, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _), Complex.ofReal_mul]
  rw [hnorm, mul_inv_rev]
  ring

end HeckeSkeleton.Moments.MOM_INV_STEP.ThetaGaussCRT
