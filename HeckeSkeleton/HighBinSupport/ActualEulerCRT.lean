import HeckeSkeleton.HighBinSupport.ActualPrimePowerSymbols
import HeckeSkeleton.HighBinSupport.ActualInitialAbsolute
import HeckeSkeleton.HighBinSupport.GeneratorUnitInvariance

/-!
# CRT for the actual finite arithmetic functions

The ideal symbol, the chosen principal additive character, and the quotient
rings in this module are the original project objects. A scaled CRT map
retains the cross phases explicitly. In particular, a raw Gauss transform
has two cross-symbol factors; none is silently replaced by one.

AI-assisted: ChatGPT / GPT-6 Astra Pro, 2026-10-30.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace HeckeSkeleton.HighBinActualCRT

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.HighBinActualAbsolute HeckeSkeleton.HighBinActualSymbols
open HighBin.FiniteResidueFourier
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

local instance crtThetaFintype (I : ExteriorIdeal K S) :
    Fintype (ThetaQuotient K S I) := by
  letI : Finite (ThetaQuotient K S I) := finite_sIntegerSexticIdealQuotient K S
    I.val.val (nonZeroDivisors.coe_ne_zero I.val) I.property
  exact Fintype.ofFinite _

@[simp] theorem quotientSymbol_mk (D : ThetaArithmeticData K S)
    (I : ExteriorIdeal K S) (a : S.integer K) :
    quotientSymbol K S D I (Ideal.Quotient.mk _ a) = idealSymbol K S D I a :=
  sIntegerSexticIdealQuotientFunction_mk K S D.root6 D.primitive6 D.embedding
    I.val.val (nonZeroDivisors.coe_ne_zero I.val) I.property
    (fun p hp => D.away_six p (I.property p hp)) a

theorem quotientSymbol_mul (D : ThetaArithmeticData K S)
    (I : ExteriorIdeal K S) (x y : ThetaQuotient K S I) :
    quotientSymbol K S D I (x * y) =
      quotientSymbol K S D I x * quotientSymbol K S D I y := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [← map_mul, quotientSymbol_mk, quotientSymbol_mk, quotientSymbol_mk]
  exact sIntegerSexticIdealEvaluation_mul K S D.root6 D.primitive6 D.embedding
    I.val.val (nonZeroDivisors.coe_ne_zero I.val) I.property
    (fun p hp => D.away_six p (I.property p hp)) a b

@[simp] theorem quotientSymbol_one (D : ThetaArithmeticData K S)
    (I : ExteriorIdeal K S) : quotientSymbol K S D I 1 = 1 := by
  rw [← map_one (Ideal.Quotient.mk _), quotientSymbol_mk]
  exact sIntegerSexticIdealEvaluation_one K S D.root6 D.primitive6 D.embedding
    I.val.val (nonZeroDivisors.coe_ne_zero I.val) I.property
    (fun p hp => D.away_six p (I.property p hp))

theorem quotientSymbol_sixth_global_unit (D : ThetaArithmeticData K S)
    (I : ExteriorIdeal K S) (u : S.unit K) (x : ThetaQuotient K S I) :
    quotientSymbol K S D I
        (Ideal.Quotient.mk _ (S.unitEquivUnitsInteger K u).val ^ 6 * x) =
      quotientSymbol K S D I x := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [← map_pow, ← map_mul, quotientSymbol_mk, quotientSymbol_mk]
  exact sIntegerSexticIdealEvaluation_mul_sixth_power_unit K S D.root6 D.primitive6
    D.embedding I.val.val (nonZeroDivisors.coe_ne_zero I.val) I.property
    (fun p hp => D.away_six p (I.property p hp)) u a

/-- The zero-extended symbol still preserves multiplication and one. The
unit ideal is included; no assertion about preserving zero is required. -/
def quotientSymbolHom (D : ThetaArithmeticData K S) (I : ExteriorIdeal K S) :
    ThetaQuotient K S I →* ℂ where
  toFun := quotientSymbol K S D I
  map_one' := quotientSymbol_one K S D I
  map_mul' := quotientSymbol_mul K S D I

/-- Every quotient unit has an actual sixth-root symbol value. -/
theorem quotientSymbol_unit_sixth (D : ThetaArithmeticData K S)
    (I : ExteriorIdeal K S) (u : (ThetaQuotient K S I)ˣ) :
    quotientSymbol K S D I (u : ThetaQuotient K S I) ^ 6 = 1 := by
  letI : Fintype (AlgebraicNumberTheory.PowerResidueSymbols.idealPrimeDivisors K I.val.val) :=
    (AlgebraicNumberTheory.PowerResidueSymbols.idealPrimeDivisors_finite K I.val.val
      (nonZeroDivisors.coe_ne_zero I.val)).fintype
  unfold quotientSymbol sIntegerSexticIdealQuotientFunction
  rw [← Finset.prod_pow]
  apply Finset.prod_eq_one
  intro p _
  let χ := sexticResidueCharacter K D.root6 D.primitive6 D.embedding p.val
    (D.away_six p.val (I.property p.val p.property))
  let v := Units.map (sexticIdealPrimeQuotientMap K S I.val.val I.property p).toMonoidHom u
  have hχ : χ ^ 6 = 1 := by
    simpa only [χ, sexticResidueCharacter_order] using pow_orderOf_eq_one χ
  have hv : χ (v : 𝓞 K ⧸ p.val.asIdeal) ^ 6 = 1 := by
    rw [← MulChar.pow_apply_coe, hχ, MulChar.one_apply_coe]
  change (χ (v : 𝓞 K ⧸ p.val.asIdeal) ^ _) ^ 6 = 1
  rw [← pow_mul, Nat.mul_comm _ 6, pow_mul, hv, one_pow]

/-- The actual Gauss transform has the inverse-symbol unit covariance. -/
theorem probeGaussOnQuotient_unit_scale (P : ProbeData K S)
    (I : ExteriorIdeal K S) (v : (ThetaQuotient K S I)ˣ)
    (h : ThetaQuotient K S I) :
    probeGaussOnQuotient K S P I ((v : ThetaQuotient K S I) * h) =
      (quotientSymbol K S P.arithmetic I v)⁻¹ * probeGaussOnQuotient K S P I h := by
  let χ := quotientSymbolHom K S P.arithmetic I
  have hχ : χ (v : ThetaQuotient K S I) ≠ 0 :=
    (v.isUnit.map χ).ne_zero
  apply mul_left_cancel₀ hχ
  change χ (v : ThetaQuotient K S I) *
    probeGaussOnQuotient K S P I ((v : ThetaQuotient K S I) * h) =
      χ (v : ThetaQuotient K S I) *
        ((χ (v : ThetaQuotient K S I))⁻¹ * probeGaussOnQuotient K S P I h)
  rw [← mul_assoc, mul_inv_cancel₀ hχ, one_mul]
  change χ (v : ThetaQuotient K S I) *
    (∑ x : ThetaQuotient K S I, χ x * thetaPrincipalAddCharacter K S P.arithmetic I
      (((v : ThetaQuotient K S I) * h) * x)) =
    ∑ x : ThetaQuotient K S I, χ x * thetaPrincipalAddCharacter K S P.arithmetic I (h * x)
  rw [Finset.mul_sum]
  apply Fintype.sum_equiv (Units.mulLeft v)
  intro x
  change χ (v : ThetaQuotient K S I) *
    (χ x * thetaPrincipalAddCharacter K S P.arithmetic I
      (((v : ThetaQuotient K S I) * h) * x)) =
    χ ((v : ThetaQuotient K S I) * x) * thetaPrincipalAddCharacter K S P.arithmetic I
      (h * ((v : ThetaQuotient K S I) * x))
  rw [map_mul χ]
  have he : ((v : ThetaQuotient K S I) * h) * x =
      h * ((v : ThetaQuotient K S I) * x) := by ring
  rw [he]
  ring

/-- Locally invertible sixth powers preserve the actual Gauss transform. -/
theorem probeGaussOnQuotient_sixth_unit (P : ProbeData K S)
    (I : ExteriorIdeal K S) (v : (ThetaQuotient K S I)ˣ)
    (h : ThetaQuotient K S I) :
    probeGaussOnQuotient K S P I ((v : ThetaQuotient K S I) ^ 6 * h) =
      probeGaussOnQuotient K S P I h := by
  have hv : quotientSymbol K S P.arithmetic I ((v ^ 6 : (ThetaQuotient K S I)ˣ) : _) = 1 := by
    change quotientSymbolHom K S P.arithmetic I ((v : ThetaQuotient K S I) ^ 6) = 1
    rw [map_pow]
    exact quotientSymbol_unit_sixth K S P.arithmetic I v
  have hscale := probeGaussOnQuotient_unit_scale K S P I (v ^ 6) h
  rw [hv, inv_one, one_mul] at hscale
  simpa only [Units.val_pow_eq_pow_val] using hscale

/-- Multiplication of moduli, including every nonunit zero. -/
theorem quotientSymbol_product (D : ThetaArithmeticData K S)
    (I J : ExteriorIdeal K S) (x : ThetaQuotient K S (exteriorMul K S I J)) :
    quotientSymbol K S D (exteriorMul K S I J) x =
      quotientSymbol K S D I (productQuotientLeft K S I J x) *
      quotientSymbol K S D J (productQuotientRight K S I J x) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [productQuotientLeft, productQuotientRight, Ideal.quotientMap_mk,
    RingHom.id_apply, quotientSymbol_mk]
  exact idealSymbol_exteriorMul K S D I J a

/-- The actual S-local phase is an additive character on the field. -/
theorem principalPhase_add (x y : K) :
    sLocalPrincipalPhase K S (x + y) =
      sLocalPrincipalPhase K S x * sLocalPrincipalPhase K S y := by
  simp only [sLocalPrincipalPhase, map_add, Rat.cast_add, mul_add, Complex.exp_add,
    AddChar.map_add_eq_mul, Finset.prod_mul_distrib]
  ring

/-- The complementary generator is a genuine unit in the current quotient. -/
theorem generator_isUnit_mod (D : ThetaArithmeticData K S)
    (I J : ExteriorIdeal K S) (hIJ : IsCoprime I.val.val J.val.val) :
    IsUnit (Ideal.Quotient.mk (I.val.val.map (algebraMap (𝓞 K) (S.integer K)))
      (D.generator J)) := by
  have hgen : IsCoprime (D.generator I) (D.generator J) := by
    apply (Ideal.sup_eq_top_iff_isCoprime _ _).mp
    rw [D.generator_span, D.generator_span, ← Ideal.map_sup,
      Ideal.isCoprime_iff_sup_eq.mp hIJ, Ideal.map_top]
  obtain ⟨r, s, hrs⟩ := hgen
  have hz : Ideal.Quotient.mk (I.val.val.map (algebraMap (𝓞 K) (S.integer K)))
      (D.generator I) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [← D.generator_span]
    exact Ideal.subset_span (Set.mem_singleton _)
  apply IsUnit.of_mul_eq_one
    (Ideal.Quotient.mk (I.val.val.map (algebraMap (𝓞 K) (S.integer K))) s)
  have hh := congrArg
    (Ideal.Quotient.mk (I.val.val.map (algebraMap (𝓞 K) (S.integer K)))) hrs
  simpa only [map_add, map_mul, map_one, hz, zero_mul, zero_add, mul_comm] using hh

/-- Ordinary CRT, before scaling each component by the complementary generator. -/
def quotientCRT (I J : ExteriorIdeal K S) (hIJ : IsCoprime I.val.val J.val.val) :
    ThetaQuotient K S (exteriorMul K S I J) ≃+*
      (ThetaQuotient K S I × ThetaQuotient K S J) :=
  (Ideal.quotEquivOfEq (by
    change (I.val.val * J.val.val).map (algebraMap (𝓞 K) (S.integer K)) = _
    exact Ideal.map_mul _ _ _)).trans
      (Ideal.quotientMulEquivQuotientProd _ _ (by
        apply Ideal.isCoprime_iff_sup_eq.mpr
        rw [← Ideal.map_sup, Ideal.isCoprime_iff_sup_eq.mp hIJ, Ideal.map_top]))

@[simp] theorem quotientCRT_mk (I J : ExteriorIdeal K S)
    (hIJ : IsCoprime I.val.val J.val.val) (a : S.integer K) :
    quotientCRT K S I J hIJ (Ideal.Quotient.mk _ a) =
      (Ideal.Quotient.mk _ a, Ideal.Quotient.mk _ a) := rfl

/-- The CRT coordinates used by the literal phase are b*x+a*y. -/
def scaledCRT (D : ThetaArithmeticData K S) (I J : ExteriorIdeal K S)
    (hIJ : IsCoprime I.val.val J.val.val) :
    (ThetaQuotient K S I × ThetaQuotient K S J) ≃
      ThetaQuotient K S (exteriorMul K S I J) :=
  ((Units.mulLeft (generator_isUnit_mod K S D I J hIJ).unit).prodCongr
    (Units.mulLeft (generator_isUnit_mod K S D J I hIJ.symm).unit)).trans
      (quotientCRT K S I J hIJ).symm.toEquiv

@[simp] theorem scaledCRT_mk (D : ThetaArithmeticData K S)
    (I J : ExteriorIdeal K S) (hIJ : IsCoprime I.val.val J.val.val)
    (x y : S.integer K) :
    scaledCRT K S D I J hIJ (Ideal.Quotient.mk _ x, Ideal.Quotient.mk _ y) =
      Ideal.Quotient.mk _ (D.generator J * x + D.generator I * y) := by
  apply (quotientCRT K S I J hIJ).injective
  have hI : Ideal.Quotient.mk (I.val.val.map (algebraMap (𝓞 K) (S.integer K)))
      (D.generator I) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [← D.generator_span]
    exact Ideal.subset_span (Set.mem_singleton _)
  have hJ : Ideal.Quotient.mk (J.val.val.map (algebraMap (𝓞 K) (S.integer K)))
      (D.generator J) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [← D.generator_span]
    exact Ideal.subset_span (Set.mem_singleton _)
  change quotientCRT K S I J hIJ ((quotientCRT K S I J hIJ).symm _) = _
  rw [RingEquiv.apply_symm_apply, quotientCRT_mk]
  simp only [Equiv.prodCongr_apply, Units.mulLeft_apply, IsUnit.unit_spec,
    map_add, map_mul, hI, hJ, zero_mul, mul_zero, add_zero, zero_add] <;> rfl

/-- Symbol CRT is exact for arbitrary exterior ideals. -/
theorem quotientSymbol_scaledCRT (D : ThetaArithmeticData K S)
    (I J : ExteriorIdeal K S) (hIJ : IsCoprime I.val.val J.val.val)
    (x : ThetaQuotient K S I) (y : ThetaQuotient K S J) :
    quotientSymbol K S D (exteriorMul K S I J) (scaledCRT K S D I J hIJ (x, y)) =
      (idealSymbol K S D I (D.generator J) * quotientSymbol K S D I x) *
      (idealSymbol K S D J (D.generator I) * quotientSymbol K S D J y) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [scaledCRT_mk, quotientSymbol_product]
  have hI : Ideal.Quotient.mk (I.val.val.map (algebraMap (𝓞 K) (S.integer K)))
      (D.generator I) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [← D.generator_span]
    exact Ideal.subset_span (Set.mem_singleton _)
  have hJ : Ideal.Quotient.mk (J.val.val.map (algebraMap (𝓞 K) (S.integer K)))
      (D.generator J) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [← D.generator_span]
    exact Ideal.subset_span (Set.mem_singleton _)
  change quotientSymbol K S D I
      (Ideal.Quotient.mk _ (D.generator J * a + D.generator I * b)) *
    quotientSymbol K S D J
      (Ideal.Quotient.mk _ (D.generator J * a + D.generator I * b)) = _
  simp only [map_add, map_mul, hI, hJ, zero_mul, mul_zero, add_zero,
    zero_add, quotientSymbol_mul, quotientSymbol_mk]

/-- The product denominator gives exactly the two original principal phases. -/
theorem productPrincipalCharacter_scaledCRT (D : ThetaArithmeticData K S)
    (I J : ExteriorIdeal K S) (hIJ : IsCoprime I.val.val J.val.val)
    (h : S.integer K) (x : ThetaQuotient K S I) (y : ThetaQuotient K S J) :
    productPrincipalCharacter K S D I J
        (Ideal.Quotient.mk _ h * scaledCRT K S D I J hIJ (x, y)) =
      thetaPrincipalAddCharacter K S D I (Ideal.Quotient.mk _ h * x) *
      thetaPrincipalAddCharacter K S D J (Ideal.Quotient.mk _ h * y) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [scaledCRT_mk, ← map_mul, productPrincipalCharacter_mk, ← map_mul,
    thetaPrincipalAddCharacter_mk, ← map_mul, thetaPrincipalAddCharacter_mk,
    ← principalPhase_add]
  apply congrArg (sLocalPrincipalPhase K S)
  have hI : (D.generator I : K) ≠ 0 := fun hz =>
    D.generator_ne_zero I (Subtype.ext hz)
  have hJ : (D.generator J : K) ≠ 0 := fun hz =>
    D.generator_ne_zero J (Subtype.ext hz)
  simp only [Subalgebra.coe_mul, Subalgebra.coe_add]
  field_simp [hI, hJ] <;> ring

/-- Exact character transport for a specified allowed-generator correction. -/
theorem product_character_sixth_shift (D : ThetaArithmeticData K S)
    (I J : ExteriorIdeal K S) (u : S.unit K)
    (hu : D.generator (exteriorMul K S I J) =
      (S.unitEquivUnitsInteger K u).val ^ 6 * D.generator I * D.generator J)
    (x : ThetaQuotient K S (exteriorMul K S I J)) :
    thetaPrincipalAddCharacter K S D (exteriorMul K S I J)
        (Ideal.Quotient.mk _ (S.unitEquivUnitsInteger K u).val ^ 6 * x) =
      productPrincipalCharacter K S D I J x := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [← map_pow, ← map_mul, thetaPrincipalAddCharacter_mk,
    productPrincipalCharacter_mk]
  apply congrArg (sLocalPrincipalPhase K S)
  have huK : ((S.unitEquivUnitsInteger K u).val : K) ≠ 0 := fun hz =>
    (S.unitEquivUnitsInteger K u).ne_zero (Subtype.ext hz)
  have hI : (D.generator I : K) ≠ 0 := fun hz => D.generator_ne_zero I (Subtype.ext hz)
  have hJ : (D.generator J : K) ≠ 0 := fun hz => D.generator_ne_zero J (Subtype.ext hz)
  rw [hu]
  simp only [Subalgebra.coe_mul, Subalgebra.coe_pow]
  field_simp [huK, hI, hJ] <;> ring

/-- An invariant actual quotient function sees the same Fourier transform
for the chosen product generator and for the literal product of generators. -/
theorem fourier_chosen_product_character (D : ThetaArithmeticData K S)
    (hD : AllowedGeneratorInput K S D) (I J : ExteriorIdeal K S)
    (f : ThetaQuotient K S (exteriorMul K S I J) → ℂ)
    (hf : ∀ (u : S.unit K) (x : ThetaQuotient K S (exteriorMul K S I J)),
      f (Ideal.Quotient.mk _ (S.unitEquivUnitsInteger K u).val ^ 6 * x) = f x)
    (h : ThetaQuotient K S (exteriorMul K S I J)) :
    HighBin.FiniteResidueFourier.fourier (thetaPrincipalAddCharacter K S D (exteriorMul K S I J)) f h =
      HighBin.FiniteResidueFourier.fourier (productPrincipalCharacter K S D I J) f h := by
  let B := exteriorMul K S I J
  obtain ⟨u, hu⟩ := hD.multiplicative I J
  let U : (ThetaQuotient K S B)ˣ := Units.map
    (Ideal.Quotient.mk (B.val.val.map (algebraMap (𝓞 K) (S.integer K)))).toMonoidHom
      (S.unitEquivUnitsInteger K u)
  have hphase (x : ThetaQuotient K S B) :
      thetaPrincipalAddCharacter K S D B ((U : ThetaQuotient K S B) ^ 6 * x) =
        productPrincipalCharacter K S D I J x :=
    product_character_sixth_shift K S D I J u hu x
  have hfU (x : ThetaQuotient K S B) :
      f ((U : ThetaQuotient K S B) ^ 6 * x) = f x := hf u x
  unfold HighBin.FiniteResidueFourier.fourier
  symm
  apply Fintype.sum_equiv (Units.mulLeft (U ^ 6))
  intro x
  change f x * _ = f ((U : ThetaQuotient K S B) ^ 6 * x) *
    thetaPrincipalAddCharacter K S D B (h * ((U : ThetaQuotient K S B) ^ 6 * x))
  rw [hfU]
  rw [show h * ((U : ThetaQuotient K S B) ^ 6 * x) =
    (U : ThetaQuotient K S B) ^ 6 * (h * x) by ring, hphase]

/-- The normalized actual theta Gauss sum with its literal product denominator. -/
theorem thetaGamma_product_character (D : ThetaArithmeticData K S)
    (hD : AllowedGeneratorInput K S D) (I J : ExteriorIdeal K S) (j : ℕ) :
    thetaGamma K S D (exteriorMul K S I J) j =
      (Real.sqrt (exteriorNorm K S (exteriorMul K S I J)) : ℂ)⁻¹ *
        HighBin.FiniteResidueFourier.fourier (productPrincipalCharacter K S D I J)
          (fun x => quotientSymbol K S D (exteriorMul K S I J) x ^ j) 1 := by
  have hf (u : S.unit K) (x : ThetaQuotient K S (exteriorMul K S I J)) :
      quotientSymbol K S D (exteriorMul K S I J)
          (Ideal.Quotient.mk _ (S.unitEquivUnitsInteger K u).val ^ 6 * x) ^ j =
        quotientSymbol K S D (exteriorMul K S I J) x ^ j := by
    rw [quotientSymbol_sixth_global_unit]
  have h := fourier_chosen_product_character K S D hD I J
    (fun x => quotientSymbol K S D (exteriorMul K S I J) x ^ j) hf 1
  change (Real.sqrt (exteriorNorm K S (exteriorMul K S I J)) : ℂ)⁻¹ *
    (∑ x, quotientSymbol K S D (exteriorMul K S I J) x ^ j *
      thetaPrincipalAddCharacter K S D (exteriorMul K S I J) x) = _
  congr 1
  simpa only [HighBin.FiniteResidueFourier.fourier, one_mul] using h

/-- Actual normalized Gauss CRT. At j=2 the two cross symbols are squared. -/
theorem thetaGamma_coprime_product (D : ThetaArithmeticData K S)
    (hD : AllowedGeneratorInput K S D)
    (I J : ExteriorIdeal K S) (hIJ : IsCoprime I.val.val J.val.val) (j : ℕ) :
    thetaGamma K S D (exteriorMul K S I J) j =
      idealSymbol K S D I (D.generator J) ^ j *
      idealSymbol K S D J (D.generator I) ^ j *
      thetaGamma K S D I j * thetaGamma K S D J j := by
  have hsum : HighBin.FiniteResidueFourier.fourier (productPrincipalCharacter K S D I J)
      (fun x => quotientSymbol K S D (exteriorMul K S I J) x ^ j) 1 =
      (idealSymbol K S D I (D.generator J) ^ j *
        idealSymbol K S D J (D.generator I) ^ j) *
      (∑ x : ThetaQuotient K S I, quotientSymbol K S D I x ^ j *
        thetaPrincipalAddCharacter K S D I x) *
      (∑ y : ThetaQuotient K S J, quotientSymbol K S D J y ^ j *
        thetaPrincipalAddCharacter K S D J y) := by
    unfold HighBin.FiniteResidueFourier.fourier
    rw [← (scaledCRT K S D I J hIJ).sum_comp, Fintype.sum_prod_type]
    have hp (x : ThetaQuotient K S I) (y : ThetaQuotient K S J) :
        productPrincipalCharacter K S D I J (scaledCRT K S D I J hIJ (x, y)) =
          thetaPrincipalAddCharacter K S D I x * thetaPrincipalAddCharacter K S D J y := by
      simpa only [map_one, one_mul] using
        productPrincipalCharacter_scaledCRT K S D I J hIJ 1 x y
    simp only [one_mul]
    simp_rw [quotientSymbol_scaledCRT, hp]
    conv_rhs => rw [mul_assoc, Fintype.sum_mul_sum]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    simp only [mul_pow]
    ring
  rw [thetaGamma_product_character K S D hD, hsum]
  have hnorm : (Real.sqrt (exteriorNorm K S (exteriorMul K S I J)) : ℂ) =
      (Real.sqrt (exteriorNorm K S I) : ℂ) *
        (Real.sqrt (exteriorNorm K S J) : ℂ) := by
    have hI : 0 ≤ exteriorNorm K S I := (idealNorm_pos K I.val).le
    rw [exteriorNorm_mul, Real.sqrt_mul hI, Complex.ofReal_mul]
  rw [hnorm, mul_inv]
  change _ = _ * _ *
    ((Real.sqrt (exteriorNorm K S I) : ℂ)⁻¹ *
      ∑ x : ThetaQuotient K S I, quotientSymbol K S D I x ^ j *
        thetaPrincipalAddCharacter K S D I x) *
    ((Real.sqrt (exteriorNorm K S J) : ℂ)⁻¹ *
      ∑ y : ThetaQuotient K S J, quotientSymbol K S D J y ^ j *
        thetaPrincipalAddCharacter K S D J y)
  ring

/-- The actual generator of I*J differs from the product only by the
allowed sixth-unit correction. The finite-variable change removes it. -/
theorem probeGauss_product_character (P : ProbeData K S)
    (hP : AllowedGeneratorInput K S P.arithmetic)
    (I J : ExteriorIdeal K S) (h : S.integer K) :
    probeGauss K S P (exteriorMul K S I J) h =
      HighBin.FiniteResidueFourier.fourier (productPrincipalCharacter K S P.arithmetic I J)
        (quotientSymbol K S P.arithmetic (exteriorMul K S I J))
        (Ideal.Quotient.mk _ h) := by
  change HighBin.FiniteResidueFourier.fourier
    (thetaPrincipalAddCharacter K S P.arithmetic (exteriorMul K S I J))
    (quotientSymbol K S P.arithmetic (exteriorMul K S I J)) (Ideal.Quotient.mk _ h) = _
  apply fourier_chosen_product_character K S P.arithmetic hP I J
  exact quotientSymbol_sixth_global_unit K S P.arithmetic (exteriorMul K S I J)

/-- Actual Gauss CRT, valid for every denominator multiplicity and every
frequency, including nonunit and zero frequencies. -/
theorem probeGauss_coprime_product (P : ProbeData K S)
    (hP : AllowedGeneratorInput K S P.arithmetic)
    (I J : ExteriorIdeal K S) (hIJ : IsCoprime I.val.val J.val.val)
    (h : S.integer K) :
    probeGauss K S P (exteriorMul K S I J) h =
      idealSymbol K S P.arithmetic I (P.arithmetic.generator J) *
      idealSymbol K S P.arithmetic J (P.arithmetic.generator I) *
      probeGauss K S P I h * probeGauss K S P J h := by
  rw [probeGauss_product_character K S P hP]
  unfold HighBin.FiniteResidueFourier.fourier
  rw [← (scaledCRT K S P.arithmetic I J hIJ).sum_comp, Fintype.sum_prod_type]
  simp_rw [quotientSymbol_scaledCRT, productPrincipalCharacter_scaledCRT]
  change (∑ x : ThetaQuotient K S I, ∑ y : ThetaQuotient K S J, _) = _
  simp only [probeGauss]
  simp only [quotientSymbol]
  conv_rhs => rw [mul_assoc, Fintype.sum_mul_sum]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

/-- The actual two-factor kernel before the outer additive character. -/
def poissonCore (P : ProbeData K S) (den A : ExteriorIdeal K S)
    (x : ThetaQuotient K S (exteriorMul K S den A)) : ℂ :=
  probeGaussOnQuotient K S P den (-(productQuotientLeft K S den A x)) *
    quotientSymbol K S P.arithmetic A (productQuotientRight K S den A x)

@[simp] theorem poissonCore_mk (P : ProbeData K S)
    (den A : ExteriorIdeal K S) (m : S.integer K) :
    poissonCore K S P den A (Ideal.Quotient.mk _ m) =
      probeGauss K S P den (-m) * idealSymbol K S P.arithmetic A m := by
  simp only [poissonCore, productQuotientLeft, productQuotientRight,
    Ideal.quotientMap_mk, RingHom.id_apply, ← map_neg, probeGaussOnQuotient_mk,
    quotientSymbol_mk]

/-- The complete two-layer core, including both zero extensions, is
invariant under every sixth power that is a unit in the product quotient. -/
theorem poissonCore_sixth_unit (P : ProbeData K S)
    (den A : ExteriorIdeal K S)
    (v : (ThetaQuotient K S (exteriorMul K S den A))ˣ)
    (x : ThetaQuotient K S (exteriorMul K S den A)) :
    poissonCore K S P den A ((v : ThetaQuotient K S (exteriorMul K S den A)) ^ 6 * x) =
      poissonCore K S P den A x := by
  let vd := Units.map (productQuotientLeft K S den A).toMonoidHom v
  let va := Units.map (productQuotientRight K S den A).toMonoidHom v
  have hg := probeGaussOnQuotient_sixth_unit K S P den vd
    (-(productQuotientLeft K S den A x))
  have ha : quotientSymbol K S P.arithmetic A
      ((va : ThetaQuotient K S A) ^ 6 * productQuotientRight K S den A x) =
      quotientSymbol K S P.arithmetic A (productQuotientRight K S den A x) := by
    change quotientSymbolHom K S P.arithmetic A
      ((va : ThetaQuotient K S A) ^ 6 * productQuotientRight K S den A x) = _
    rw [map_mul, map_pow, show quotientSymbolHom K S P.arithmetic A va ^ 6 = 1 from
      quotientSymbol_unit_sixth K S P.arithmetic A va, one_mul]
    rfl
  unfold poissonCore
  rw [map_mul, map_pow, map_mul, map_pow]
  have he : -((productQuotientLeft K S den A v) ^ 6 * productQuotientLeft K S den A x) =
      (productQuotientLeft K S den A v) ^ 6 * (-(productQuotientLeft K S den A x)) := by ring
  rw [he]
  change probeGaussOnQuotient K S P den
      ((vd : ThetaQuotient K S den) ^ 6 * (-(productQuotientLeft K S den A x))) *
    quotientSymbol K S P.arithmetic A
      ((va : ThetaQuotient K S A) ^ 6 * productQuotientRight K S den A x) = _
  rw [hg, ha]

/-- Exact quotient form of the original finite Poisson definition. -/
theorem finitePoissonFactor_eq_fourier (P : ProbeData K S)
    (den A : ExteriorIdeal K S) (h : S.integer K) :
    finitePoissonFactor K S P den A h = (exteriorNorm K S den : ℂ)⁻¹ *
      HighBin.FiniteResidueFourier.fourier (productPrincipalCharacter K S P.arithmetic den A)
        (poissonCore K S P den A) (Ideal.Quotient.mk _ h) := by
  unfold finitePoissonFactor HighBin.FiniteResidueFourier.fourier
  apply congrArg (fun z : ℂ => (exteriorNorm K S den : ℂ)⁻¹ * z)
  apply Finset.sum_congr rfl
  intro x _
  have hker := poissonKernelOnQuotient_mk K S P den A h (Quotient.out x)
  rw [Ideal.Quotient.mk_out] at hker
  exact hker.symm

/-- The full finite Poisson factor can use the chosen generator of den*A;
this is a proved sixth-unit change of its original finite variable. -/
theorem finitePoissonFactor_eq_theta_fourier (P : ProbeData K S)
    (hP : AllowedGeneratorInput K S P.arithmetic)
    (den A : ExteriorIdeal K S) (h : S.integer K) :
    finitePoissonFactor K S P den A h = (exteriorNorm K S den : ℂ)⁻¹ *
      HighBin.FiniteResidueFourier.fourier (thetaPrincipalAddCharacter K S P.arithmetic (exteriorMul K S den A))
        (poissonCore K S P den A) (Ideal.Quotient.mk _ h) := by
  rw [finitePoissonFactor_eq_fourier]
  congr 1
  symm
  apply fourier_chosen_product_character K S P.arithmetic hP den A
  intro u x
  exact poissonCore_sixth_unit K S P den A
    (Units.map (Ideal.Quotient.mk _).toMonoidHom (S.unitEquivUnitsInteger K u)) x

/-- Transport only across equality of actual product ideals. -/
def poissonCoreOn (P : ProbeData K S) (den A C : ExteriorIdeal K S)
    (hC : exteriorMul K S den A = C) (x : ThetaQuotient K S C) : ℂ :=
  poissonCore K S P den A
    (Ideal.quotEquivOfEq (congrArg (fun I : ExteriorIdeal K S =>
      I.val.val.map (algebraMap (𝓞 K) (S.integer K))) hC).symm x)

@[simp] theorem poissonCoreOn_mk (P : ProbeData K S)
    (den A C : ExteriorIdeal K S) (hC : exteriorMul K S den A = C)
    (m : S.integer K) :
    poissonCoreOn K S P den A C hC (Ideal.Quotient.mk _ m) =
      probeGauss K S P den (-m) * idealSymbol K S P.arithmetic A m := by
  rw [poissonCoreOn, Ideal.quotEquivOfEq_mk, poissonCore_mk]

/-- Transport along reflexive equality preserves the actual quotient function. -/
@[simp] theorem poissonCoreOn_self (P : ProbeData K S) (den A : ExteriorIdeal K S) :
    poissonCoreOn K S P den A (exteriorMul K S den A) rfl =
      poissonCore K S P den A := by
  funext x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

theorem poissonCoreOn_sixth_unit (P : ProbeData K S)
    (den A C : ExteriorIdeal K S) (hC : exteriorMul K S den A = C)
    (v : (ThetaQuotient K S C)ˣ) (x : ThetaQuotient K S C) :
    poissonCoreOn K S P den A C hC ((v : ThetaQuotient K S C) ^ 6 * x) =
      poissonCoreOn K S P den A C hC x := by
  subst C
  simpa only [poissonCoreOn_self] using poissonCore_sixth_unit K S P den A v x

theorem finitePoissonFactor_eq_theta_fourier_on (P : ProbeData K S)
    (hP : AllowedGeneratorInput K S P.arithmetic)
    (den A C : ExteriorIdeal K S) (hC : exteriorMul K S den A = C)
    (h : S.integer K) :
    finitePoissonFactor K S P den A h = (exteriorNorm K S den : ℂ)⁻¹ *
      HighBin.FiniteResidueFourier.fourier (thetaPrincipalAddCharacter K S P.arithmetic C)
        (poissonCoreOn K S P den A C hC) (Ideal.Quotient.mk _ h) := by
  subst C
  simpa only [poissonCoreOn_self] using finitePoissonFactor_eq_theta_fourier K S P hP den A h

/-- This equality only reorders the original ideal factors. -/
theorem exteriorMul_exchange (d₁ d₂ a₁ a₂ : ExteriorIdeal K S) :
    exteriorMul K S (exteriorMul K S d₁ d₂) (exteriorMul K S a₁ a₂) =
      exteriorMul K S (exteriorMul K S d₁ a₁) (exteriorMul K S d₂ a₂) := by
  apply Subtype.ext
  change (d₁.val * d₂.val) * (a₁.val * a₂.val) =
    (d₁.val * a₁.val) * (d₂.val * a₂.val)
  ac_rfl

theorem generator_zero_mod_of_dvd (D : ThetaArithmeticData K S)
    (I J : ExteriorIdeal K S) (hIJ : I.val.val ∣ J.val.val) :
    Ideal.Quotient.mk (I.val.val.map (algebraMap (𝓞 K) (S.integer K)))
      (D.generator J) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply Ideal.map_mono (f := algebraMap (𝓞 K) (S.integer K)) (Ideal.dvd_iff_le.mp hIJ)
  rw [← D.generator_span]
  exact Ideal.subset_span (Set.mem_singleton _)

/-- Gauss covariance in the exact CRT coordinates. -/
theorem probeGauss_scaled_sum (P : ProbeData K S)
    (I J L : ExteriorIdeal K S) (hIJ : I.val.val ∣ J.val.val)
    (hIL : IsCoprime I.val.val L.val.val) (x y : S.integer K) :
    probeGauss K S P I (-(P.arithmetic.generator L * x + P.arithmetic.generator J * y)) =
      (idealSymbol K S P.arithmetic I (P.arithmetic.generator L))⁻¹ *
        probeGauss K S P I (-x) := by
  let v := (generator_isUnit_mod K S P.arithmetic I L hIL).unit
  have hv : (v : ThetaQuotient K S I) = Ideal.Quotient.mk _ (P.arithmetic.generator L) :=
    (generator_isUnit_mod K S P.arithmetic I L hIL).unit_spec
  have hq : Ideal.Quotient.mk (I.val.val.map (algebraMap (𝓞 K) (S.integer K)))
      (-(P.arithmetic.generator L * x + P.arithmetic.generator J * y)) =
      (v : ThetaQuotient K S I) * Ideal.Quotient.mk _ (-x) := by
    rw [hv, map_neg, map_add, map_mul, map_mul,
      generator_zero_mod_of_dvd K S P.arithmetic I J hIJ, zero_mul, add_zero, map_neg]
    ring
  rw [← probeGaussOnQuotient_mk, hq, probeGaussOnQuotient_unit_scale, hv,
    quotientSymbol_mk, probeGaussOnQuotient_mk]

/-- Symbol covariance in the exact CRT coordinates. -/
theorem idealSymbol_scaled_sum (D : ThetaArithmeticData K S)
    (I J L : ExteriorIdeal K S) (hIJ : I.val.val ∣ J.val.val) (x y : S.integer K) :
    idealSymbol K S D I (D.generator L * x + D.generator J * y) =
      idealSymbol K S D I (D.generator L) * idealSymbol K S D I x := by
  rw [← quotientSymbol_mk, map_add, map_mul, map_mul,
    generator_zero_mod_of_dvd K S D I J hIJ, zero_mul, add_zero,
    quotientSymbol_mul, quotientSymbol_mk, quotientSymbol_mk]

theorem idealSymbol_generator_product (D : ThetaArithmeticData K S)
    (hD : AllowedGeneratorInput K S D) (I J L : ExteriorIdeal K S) :
    idealSymbol K S D I (D.generator (exteriorMul K S J L)) =
      idealSymbol K S D I (D.generator J) * idealSymbol K S D I (D.generator L) := by
  obtain ⟨u, hu⟩ := hD.multiplicative J L
  rw [hu, mul_assoc]
  rw [show idealSymbol K S D I
      ((S.unitEquivUnitsInteger K u).val ^ 6 * (D.generator J * D.generator L)) =
      idealSymbol K S D I (D.generator J * D.generator L) from
    sIntegerSexticIdealEvaluation_mul_sixth_power_unit K S D.root6 D.primitive6 D.embedding
      I.val.val (nonZeroDivisors.coe_ne_zero I.val) I.property
      (fun p hp => D.away_six p (I.property p hp)) u _]
  exact sIntegerSexticIdealEvaluation_mul K S D.root6 D.primitive6 D.embedding
    I.val.val (nonZeroDivisors.coe_ne_zero I.val) I.property
    (fun p hp => D.away_six p (I.property p hp)) _ _

theorem idealSymbol_generator_ne_zero (D : ThetaArithmeticData K S)
    (I J : ExteriorIdeal K S) (hIJ : IsCoprime I.val.val J.val.val) :
    idealSymbol K S D I (D.generator J) ≠ 0 := by
  rw [← quotientSymbol_mk]
  exact ((generator_isUnit_mod K S D I J hIJ).map (quotientSymbolHom K S D I)).ne_zero

theorem idealSymbol_generator_sixth (D : ThetaArithmeticData K S)
    (I J : ExteriorIdeal K S) (hIJ : IsCoprime I.val.val J.val.val) :
    idealSymbol K S D I (D.generator J) ^ 6 = 1 := by
  let v := (generator_isUnit_mod K S D I J hIJ).unit
  have hv := (generator_isUnit_mod K S D I J hIJ).unit_spec
  have h := quotientSymbol_unit_sixth K S D I v
  rw [hv, quotientSymbol_mk] at h
  exact h

/-- The uncollected cross phase from the two finite Fourier layers. -/
def rawPoissonCrossPhase (D : ThetaArithmeticData K S)
    (d₁ d₂ a₁ a₂ : ExteriorIdeal K S) : ℂ :=
  idealSymbol K S D d₁ (D.generator d₂) * idealSymbol K S D d₂ (D.generator d₁) *
    (idealSymbol K S D d₁ (D.generator (exteriorMul K S d₂ a₂)))⁻¹ *
    (idealSymbol K S D d₂ (D.generator (exteriorMul K S d₁ a₁)))⁻¹ *
    idealSymbol K S D a₁ (D.generator (exteriorMul K S d₂ a₂)) *
    idealSymbol K S D a₂ (D.generator (exteriorMul K S d₁ a₁))

/-- Reciprocity cancels the denominator/completed-index cross terms.
The completed-index/completed-index phase remains present. -/
theorem rawPoissonCrossPhase_eq (D : ThetaArithmeticData K S)
    (hD : AllowedGeneratorInput K S D) (d₁ d₂ a₁ a₂ : ExteriorIdeal K S)
    (hc : IsCoprime (exteriorMul K S d₁ a₁).val.val
      (exteriorMul K S d₂ a₂).val.val) :
    rawPoissonCrossPhase K S D d₁ d₂ a₁ a₂ =
      idealSymbol K S D a₁ (D.generator a₂) * idealSymbol K S D a₂ (D.generator a₁) := by
  have hdd : IsCoprime d₁.val.val d₂.val.val := hc.of_mul_left_left.of_mul_right_left
  have hda : IsCoprime d₁.val.val a₂.val.val := hc.of_mul_left_left.of_mul_right_right
  have had : IsCoprime d₂.val.val a₁.val.val := hc.symm.of_mul_left_left.of_mul_right_right
  have hdd₁ := idealSymbol_generator_ne_zero K S D d₁ d₂ hdd
  have hdd₂ := idealSymbol_generator_ne_zero K S D d₂ d₁ hdd.symm
  have hda₁ := idealSymbol_generator_ne_zero K S D d₁ a₂ hda
  have hda₂ := idealSymbol_generator_ne_zero K S D d₂ a₁ had
  unfold rawPoissonCrossPhase
  rw [idealSymbol_generator_product K S D hD,
    idealSymbol_generator_product K S D hD,
    idealSymbol_generator_product K S D hD,
    idealSymbol_generator_product K S D hD,
    hD.reciprocity a₁ d₂, hD.reciprocity a₂ d₁]
  field_simp [hdd₁, hdd₂, hda₁, hda₂]
  <;> ring

/-- The raw core factorization on the actual CRT quotient. -/
theorem poissonCoreOn_scaledCRT (P : ProbeData K S)
    (hP : AllowedGeneratorInput K S P.arithmetic)
    (d₁ d₂ a₁ a₂ : ExteriorIdeal K S)
    (hc : IsCoprime (exteriorMul K S d₁ a₁).val.val
      (exteriorMul K S d₂ a₂).val.val)
    (x : ThetaQuotient K S (exteriorMul K S d₁ a₁))
    (y : ThetaQuotient K S (exteriorMul K S d₂ a₂)) :
    poissonCoreOn K S P (exteriorMul K S d₁ d₂) (exteriorMul K S a₁ a₂)
        (exteriorMul K S (exteriorMul K S d₁ a₁) (exteriorMul K S d₂ a₂))
        (exteriorMul_exchange K S d₁ d₂ a₁ a₂)
        (scaledCRT K S P.arithmetic (exteriorMul K S d₁ a₁) (exteriorMul K S d₂ a₂) hc (x, y)) =
      rawPoissonCrossPhase K S P.arithmetic d₁ d₂ a₁ a₂ *
        poissonCore K S P d₁ a₁ x * poissonCore K S P d₂ a₂ y := by
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
  let B₁ := exteriorMul K S d₁ a₁
  let B₂ := exteriorMul K S d₂ a₂
  have hd₁ : d₁.val.val ∣ B₁.val.val := ⟨a₁.val.val, rfl⟩
  have hd₂ : d₂.val.val ∣ B₂.val.val := ⟨a₂.val.val, rfl⟩
  have ha₁ : a₁.val.val ∣ B₁.val.val := ⟨d₁.val.val, mul_comm _ _⟩
  have ha₂ : a₂.val.val ∣ B₂.val.val := ⟨d₂.val.val, mul_comm _ _⟩
  have hd₁B₂ : IsCoprime d₁.val.val B₂.val.val := hc.of_mul_left_left
  have hd₂B₁ : IsCoprime d₂.val.val B₁.val.val := hc.symm.of_mul_left_left
  have hdd : IsCoprime d₁.val.val d₂.val.val := hc.of_mul_left_left.of_mul_right_left
  rw [scaledCRT_mk, poissonCoreOn_mk, probeGauss_coprime_product K S P hP d₁ d₂ hdd,
    idealSymbol_exteriorMul, probeGauss_scaled_sum K S P d₁ B₁ B₂ hd₁ hd₁B₂,
    idealSymbol_scaled_sum K S P.arithmetic a₁ B₁ B₂ ha₁]
  have hg₂ := probeGauss_scaled_sum K S P d₂ B₂ B₁ hd₂ hd₂B₁ s r
  have hs₂ := idealSymbol_scaled_sum K S P.arithmetic a₂ B₂ B₁ ha₂ s r
  rw [add_comm (P.arithmetic.generator B₁ * s)] at hg₂ hs₂
  rw [hg₂, hs₂, poissonCore_mk, poissonCore_mk]
  unfold rawPoissonCrossPhase
  ring

/-- Exact CRT for the literal finite Poisson factor. It includes the
cross phase; finitePoissonFactor alone is not multiplicative. -/
theorem finitePoissonFactor_coprime_product (P : ProbeData K S)
    (hP : AllowedGeneratorInput K S P.arithmetic)
    (d₁ d₂ a₁ a₂ : ExteriorIdeal K S)
    (hc : IsCoprime (exteriorMul K S d₁ a₁).val.val
      (exteriorMul K S d₂ a₂).val.val) (h : S.integer K) :
    finitePoissonFactor K S P (exteriorMul K S d₁ d₂) (exteriorMul K S a₁ a₂) h =
      (idealSymbol K S P.arithmetic a₁ (P.arithmetic.generator a₂) *
        idealSymbol K S P.arithmetic a₂ (P.arithmetic.generator a₁)) *
      finitePoissonFactor K S P d₁ a₁ h * finitePoissonFactor K S P d₂ a₂ h := by
  let B₁ := exteriorMul K S d₁ a₁
  let B₂ := exteriorMul K S d₂ a₂
  let C := exteriorMul K S B₁ B₂
  let f := poissonCoreOn K S P (exteriorMul K S d₁ d₂) (exteriorMul K S a₁ a₂) C
    (exteriorMul_exchange K S d₁ d₂ a₁ a₂)
  have hf (u : S.unit K) (x : ThetaQuotient K S C) :
      f (Ideal.Quotient.mk _ (S.unitEquivUnitsInteger K u).val ^ 6 * x) = f x :=
    poissonCoreOn_sixth_unit K S P _ _ C _
      (Units.map (Ideal.Quotient.mk _).toMonoidHom (S.unitEquivUnitsInteger K u)) x
  rw [finitePoissonFactor_eq_theta_fourier_on K S P hP _ _ C
    (exteriorMul_exchange K S d₁ d₂ a₁ a₂)]
  change (exteriorNorm K S (exteriorMul K S d₁ d₂) : ℂ)⁻¹ *
    HighBin.FiniteResidueFourier.fourier (thetaPrincipalAddCharacter K S P.arithmetic C) f (Ideal.Quotient.mk _ h) = _
  rw [fourier_chosen_product_character K S P.arithmetic hP B₁ B₂ f hf]
  have hsum : HighBin.FiniteResidueFourier.fourier (productPrincipalCharacter K S P.arithmetic B₁ B₂) f
      (Ideal.Quotient.mk _ h) =
      rawPoissonCrossPhase K S P.arithmetic d₁ d₂ a₁ a₂ *
        HighBin.FiniteResidueFourier.fourier (thetaPrincipalAddCharacter K S P.arithmetic B₁) (poissonCore K S P d₁ a₁)
          (Ideal.Quotient.mk _ h) *
        HighBin.FiniteResidueFourier.fourier (thetaPrincipalAddCharacter K S P.arithmetic B₂) (poissonCore K S P d₂ a₂)
          (Ideal.Quotient.mk _ h) := by
    unfold HighBin.FiniteResidueFourier.fourier
    rw [← (scaledCRT K S P.arithmetic B₁ B₂ hc).sum_comp, Fintype.sum_prod_type]
    simp_rw [show ∀ x y, f (scaledCRT K S P.arithmetic B₁ B₂ hc (x, y)) =
      rawPoissonCrossPhase K S P.arithmetic d₁ d₂ a₁ a₂ *
        poissonCore K S P d₁ a₁ x * poissonCore K S P d₂ a₂ y from
      fun x y => poissonCoreOn_scaledCRT K S P hP d₁ d₂ a₁ a₂ hc x y,
      productPrincipalCharacter_scaledCRT]
    conv_rhs => rw [mul_assoc, Fintype.sum_mul_sum]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    ring
  rw [hsum, rawPoissonCrossPhase_eq K S P.arithmetic hP d₁ d₂ a₁ a₂ hc,
    finitePoissonFactor_eq_theta_fourier K S P hP d₁ a₁,
    finitePoissonFactor_eq_theta_fourier K S P hP d₂ a₂,
    exteriorNorm_mul, Complex.ofReal_mul, mul_inv]
  ring

/-- The completed cube factors are retained when splitting coprime blocks. -/
theorem completedIdeal_mul (c₁ c₂ n₁ n₂ : ExteriorIdeal K S) :
    completedIdeal K S (exteriorMul K S c₁ c₂) (exteriorMul K S n₁ n₂) =
      exteriorMul K S (completedIdeal K S c₁ n₁) (completedIdeal K S c₂ n₂) := by
  apply Subtype.ext
  change (c₁.val * c₂.val) *
      ((n₁.val * n₂.val) * ((n₁.val * n₂.val) * (n₁.val * n₂.val))) =
    (c₁.val * (n₁.val * (n₁.val * n₁.val))) *
      (c₂.val * (n₂.val * (n₂.val * n₂.val)))
  ac_rfl

/-- The four actual cross symbols and their exact exponents. -/
theorem completedIdeal_cross_symbol (D : ThetaArithmeticData K S)
    (hD : AllowedGeneratorInput K S D) (c₁ c₂ n₁ n₂ : ExteriorIdeal K S) :
    idealSymbol K S D (completedIdeal K S c₁ n₁)
        (D.generator (completedIdeal K S c₂ n₂)) =
      idealSymbol K S D c₁ (D.generator c₂) *
      idealSymbol K S D c₁ (D.generator n₂) ^ 3 *
      idealSymbol K S D n₁ (D.generator c₂) ^ 3 *
      idealSymbol K S D n₁ (D.generator n₂) ^ 9 := by
  simp only [completedIdeal, idealSymbol_exteriorMul,
    idealSymbol_generator_product K S D hD]
  ring

/-- The fourth-power theta phase cancels the second-power completed-index
phase. Every sixth-root identity follows from actual quotient invertibility. -/
theorem completedIdeal_cross_phase_cancel (D : ThetaArithmeticData K S)
    (hD : AllowedGeneratorInput K S D) (c₁ c₂ n₁ n₂ : ExteriorIdeal K S)
    (hc : IsCoprime (completedIdeal K S c₁ n₁).val.val
      (completedIdeal K S c₂ n₂).val.val) :
    idealSymbol K S D c₁ (D.generator c₂) ^ 4 *
      idealSymbol K S D (completedIdeal K S c₁ n₁)
        (D.generator (completedIdeal K S c₂ n₂)) ^ 2 = 1 := by
  have hcc : IsCoprime c₁.val.val c₂.val.val := hc.of_mul_left_left.of_mul_right_left
  have hcn : IsCoprime c₁.val.val n₂.val.val :=
    hc.of_mul_left_left.of_mul_right_right.of_mul_right_left
  have hnc : IsCoprime n₁.val.val c₂.val.val :=
    hc.of_mul_left_right.of_mul_left_left.of_mul_right_left
  have hnn : IsCoprime n₁.val.val n₂.val.val :=
    hc.of_mul_left_right.of_mul_left_left.of_mul_right_right.of_mul_right_left
  have hcc6 := idealSymbol_generator_sixth K S D c₁ c₂ hcc
  have hcn6 := idealSymbol_generator_sixth K S D c₁ n₂ hcn
  have hnc6 := idealSymbol_generator_sixth K S D n₁ c₂ hnc
  have hnn6 := idealSymbol_generator_sixth K S D n₁ n₂ hnn
  calc
    _ = idealSymbol K S D c₁ (D.generator c₂) ^ 6 *
        idealSymbol K S D c₁ (D.generator n₂) ^ 6 *
        idealSymbol K S D n₁ (D.generator c₂) ^ 6 *
        (idealSymbol K S D n₁ (D.generator n₂) ^ 6) ^ 3 := by
      rw [completedIdeal_cross_symbol K S D hD]
      ring
    _ = 1 := by rw [hcc6, hcn6, hnc6, hnn6]; norm_num

/-- The actual normalized finite coefficient is multiplicative across
coprime blocks. This is the theta-Gauss/Fourier phase cancellation required
by the original four-ideal Euler series, with no Euler identity premise. -/
theorem thetaGamma_finitePoisson_coprime_product (P : ProbeData K S)
    (hP : AllowedGeneratorInput K S P.arithmetic)
    (c₁ c₂ n₁ n₂ d₁ d₂ : ExteriorIdeal K S)
    (hc : IsCoprime (exteriorMul K S d₁ (completedIdeal K S c₁ n₁)).val.val
      (exteriorMul K S d₂ (completedIdeal K S c₂ n₂)).val.val)
    (h : S.integer K) :
    thetaGamma K S P.arithmetic (exteriorMul K S c₁ c₂) 2 *
      finitePoissonFactor K S P (exteriorMul K S d₁ d₂)
        (completedIdeal K S (exteriorMul K S c₁ c₂) (exteriorMul K S n₁ n₂)) h =
      (thetaGamma K S P.arithmetic c₁ 2 *
        finitePoissonFactor K S P d₁ (completedIdeal K S c₁ n₁) h) *
      (thetaGamma K S P.arithmetic c₂ 2 *
        finitePoissonFactor K S P d₂ (completedIdeal K S c₂ n₂) h) := by
  let A₁ := completedIdeal K S c₁ n₁
  let A₂ := completedIdeal K S c₂ n₂
  have hAA : IsCoprime A₁.val.val A₂.val.val := hc.of_mul_left_right.of_mul_right_right
  have hcc : IsCoprime c₁.val.val c₂.val.val := hAA.of_mul_left_left.of_mul_right_left
  have hcancel := completedIdeal_cross_phase_cancel K S P.arithmetic hP c₁ c₂ n₁ n₂ hAA
  rw [completedIdeal_mul, thetaGamma_coprime_product K S P.arithmetic hP c₁ c₂ hcc 2,
    finitePoissonFactor_coprime_product K S P hP d₁ d₂ A₁ A₂ hc,
    hP.reciprocity c₂ c₁, hP.reciprocity A₂ A₁]
  calc
    _ = (idealSymbol K S P.arithmetic c₁ (P.arithmetic.generator c₂) ^ 4 *
        idealSymbol K S P.arithmetic A₁ (P.arithmetic.generator A₂) ^ 2) *
      (thetaGamma K S P.arithmetic c₁ 2 * finitePoissonFactor K S P d₁ A₁ h) *
      (thetaGamma K S P.arithmetic c₂ 2 * finitePoissonFactor K S P d₂ A₂ h) := by ring
    _ = _ := by rw [hcancel, one_mul]

/-- The original finite Poisson factor is invariant under a locally
invertible sixth-power frequency change, including nonunit base frequencies. -/
theorem finitePoissonFactor_frequency_sixth_unit (P : ProbeData K S)
    (den A : ExteriorIdeal K S) (a h : S.integer K)
    (ha : IsUnit (Ideal.Quotient.mk
      ((exteriorMul K S den A).val.val.map (algebraMap (𝓞 K) (S.integer K))) a)) :
    finitePoissonFactor K S P den A (a ^ 6 * h) = finitePoissonFactor K S P den A h := by
  let B := exteriorMul K S den A
  let v := ha.unit
  have hv : (v : ThetaQuotient K S B) = Ideal.Quotient.mk _ a := ha.unit_spec
  have hf (x : ThetaQuotient K S B) :
      poissonCore K S P den A (((v ^ 6 : (ThetaQuotient K S B)ˣ) : _) * x) =
        poissonCore K S P den A x := by
    simpa only [Units.val_pow_eq_pow_val] using poissonCore_sixth_unit K S P den A v x
  have hF := HighBin.GeneratorUnitInvariance.fourier_unit_invariant
    (productPrincipalCharacter K S P.arithmetic den A)
    (poissonCore K S P den A) (v ^ 6) hf (Ideal.Quotient.mk _ h)
  rw [finitePoissonFactor_eq_fourier, finitePoissonFactor_eq_fourier]
  exact congrArg ((exteriorNorm K S den : ℂ)⁻¹ * ·)
    (by simpa only [Units.val_pow_eq_pow_val, hv, map_mul, map_pow] using hF)

/-- A prime block of r outside the current finite quotient is removed by
the proved sixth-power invariance; all actual row sectors are retained. -/
theorem finitePoissonFactor_poissonFrequency_mul_right (P : ProbeData K S)
    (hP : AllowedGeneratorInput K S P.arithmetic) (u : FrequencyRow K S)
    (den A r₁ r₂ : ExteriorIdeal K S)
    (hr₂ : IsCoprime (exteriorMul K S den A).val.val r₂.val.val) :
    finitePoissonFactor K S P den A (poissonFrequency K S P u (exteriorMul K S r₁ r₂)) =
      finitePoissonFactor K S P den A (poissonFrequency K S P u r₁) := by
  let B := exteriorMul K S den A
  obtain ⟨v, hv⟩ := hP.multiplicative r₁ r₂
  let a := (S.unitEquivUnitsInteger K v).val ^ 6 * P.arithmetic.generator r₂
  have ha : IsUnit (Ideal.Quotient.mk (B.val.val.map (algebraMap (𝓞 K) (S.integer K))) a) := by
    change IsUnit (Ideal.Quotient.mk _
      ((S.unitEquivUnitsInteger K v).val ^ 6 * P.arithmetic.generator r₂))
    rw [map_mul, map_pow]
    exact (((S.unitEquivUnitsInteger K v).isUnit.map (Ideal.Quotient.mk _)).pow 6).mul
      (generator_isUnit_mod K S P.arithmetic B r₂ hr₂)
  have hfreq : poissonFrequency K S P u (exteriorMul K S r₁ r₂) =
      a ^ 6 * poissonFrequency K S P u r₁ := by
    unfold poissonFrequency
    rw [hv]
    dsimp only [a]
    ring
  rw [hfreq]
  exact finitePoissonFactor_frequency_sixth_unit K S P den A a _ ha

/-- The finite arithmetic numerator of the original four-ideal term
splits across coprime blocks, including its sixth-power r descendants. -/
theorem fourIdeal_finite_coefficient_coprime_product (P : ProbeData K S)
    (hP : AllowedGeneratorInput K S P.arithmetic) (u : FrequencyRow K S)
    (c₁ c₂ n₁ n₂ d₁ d₂ r₁ r₂ : ExteriorIdeal K S)
    (hc : IsCoprime
      (exteriorMul K S (exteriorMul K S d₁ (completedIdeal K S c₁ n₁)) r₁).val.val
      (exteriorMul K S (exteriorMul K S d₂ (completedIdeal K S c₂ n₂)) r₂).val.val) :
    thetaGamma K S P.arithmetic (exteriorMul K S c₁ c₂) 2 *
      finitePoissonFactor K S P (exteriorMul K S d₁ d₂)
        (completedIdeal K S (exteriorMul K S c₁ c₂) (exteriorMul K S n₁ n₂))
        (poissonFrequency K S P u (exteriorMul K S r₁ r₂)) =
      (thetaGamma K S P.arithmetic c₁ 2 *
        finitePoissonFactor K S P d₁ (completedIdeal K S c₁ n₁)
          (poissonFrequency K S P u r₁)) *
      (thetaGamma K S P.arithmetic c₂ 2 *
        finitePoissonFactor K S P d₂ (completedIdeal K S c₂ n₂)
          (poissonFrequency K S P u r₂)) := by
  have hB : IsCoprime (exteriorMul K S d₁ (completedIdeal K S c₁ n₁)).val.val
      (exteriorMul K S d₂ (completedIdeal K S c₂ n₂)).val.val :=
    hc.of_mul_left_left.of_mul_right_left
  have hBr₂ : IsCoprime (exteriorMul K S d₁ (completedIdeal K S c₁ n₁)).val.val r₂.val.val :=
    hc.of_mul_left_left.of_mul_right_right
  have hBr₁ : IsCoprime (exteriorMul K S d₂ (completedIdeal K S c₂ n₂)).val.val r₁.val.val :=
    hc.symm.of_mul_left_left.of_mul_right_right
  have hrcomm : exteriorMul K S r₁ r₂ = exteriorMul K S r₂ r₁ := by
    apply Subtype.ext
    exact mul_comm _ _
  rw [thetaGamma_finitePoisson_coprime_product K S P hP c₁ c₂ n₁ n₂ d₁ d₂ hB,
    finitePoissonFactor_poissonFrequency_mul_right K S P hP u d₁ _ r₁ r₂ hBr₂]
  have hright := finitePoissonFactor_poissonFrequency_mul_right K S P hP u
    d₂ (completedIdeal K S c₂ n₂) r₂ r₁ hBr₁
  rw [← hrcomm] at hright
  rw [hright]

#print axioms quotientSymbol_scaledCRT
#print axioms probeGauss_product_character
#print axioms probeGauss_coprime_product
#print axioms thetaGamma_coprime_product
#print axioms finitePoissonFactor_coprime_product
#print axioms thetaGamma_finitePoisson_coprime_product
#print axioms finitePoissonFactor_frequency_sixth_unit
#print axioms fourIdeal_finite_coefficient_coprime_product
end HeckeSkeleton.HighBinActualCRT
