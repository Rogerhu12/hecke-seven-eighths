import HeckeSkeleton.HighBinSupport.ActualPrimePowerGauss
import HeckeSkeleton.HighBinSupport.ActualGaussSigns
import HeckeSkeleton.HighBinSupport.FourierInversion
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-!
# The literal prime-power finite Poisson convolution

The quotient, the two original generators in the phase denominator, the
negative inner frequency, and both symbol zero extensions are retained.
The denominator-one-prime branch is reduced to the actual principal-power
Fourier formula by a sixth-unit change of the outer finite variable.

AI-assisted: ChatGPT / GPT-6 Astra Pro, 2026-10-31.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HeckeSkeleton.HighBinActualPrimeGauss

open NumberField IsDedekindDomain
open AlgebraicNumberTheory.PowerResidueSymbols
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.HighBinActualGenerators HeckeSkeleton.HighBinActualSymbols
open HeckeSkeleton.HighBinActualAbsolute HeckeSkeleton.HighBinActualEuler
open HighBin.FiniteResidueFourier HighBin.PrincipalPowerSupport HighBin.FiniteLocalTable
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

local instance poissonPrimeField (p : ExteriorPrime K S) :
    Field (𝓞 K ⧸ p.val.asIdeal) := Ideal.Quotient.field _

local instance poissonPrimeFintype (p : ExteriorPrime K S) :
    Fintype (𝓞 K ⧸ p.val.asIdeal) := Fintype.ofFinite _

local instance poissonPowerFintype (D : ThetaArithmeticData K S)
    (p : ExteriorPrime K S) (n : ℕ) :
    Fintype (PowerQuotient (primeGenerator K S D p) n) := principalPowerFintype K S D p n

local instance poissonPrimeMaximal (D : ThetaArithmeticData K S) (p : ExteriorPrime K S) :
    (powerIdeal (primeGenerator K S D p) 1).IsMaximal := principalPrime_isMaximal K S D p

local instance poissonThetaFintype (I : ExteriorIdeal K S) : Fintype (ThetaQuotient K S I) := by
  letI : Finite (ThetaQuotient K S I) := finite_sIntegerSexticIdealQuotient K S I.val.val
    (nonZeroDivisors.coe_ne_zero I.val) I.property
  exact Fintype.ofFinite _

private theorem poissonPrincipalPowerAddCharacter_mk (D : ThetaArithmeticData K S)
    (p : ExteriorPrime K S) (n : ℕ) (a : S.integer K) :
    principalPowerAddCharacter K S D p n
        (Ideal.Quotient.mk (powerIdeal (primeGenerator K S D p) n) a) =
      sLocalPrincipalPhase K S
        ((a : K) / ((primeGenerator K S D p ^ n : S.integer K) : K)) := by
  exact sIntegerActualModulusAddCharacter_mk K S D.different_outside
    (primeGenerator K S D p ^ n) (pow_ne_zero n (primeGenerator_ne_zero K S D p)) a

/-- Replacing Quotient.out by the well-defined kernel changes no summand
of the original finite Poisson factor. -/
theorem finitePoissonFactor_eq_sum_kernel (P : ProbeData K S)
    (den A : ExteriorIdeal K S) (h : S.integer K) :
    finitePoissonFactor K S P den A h = (exteriorNorm K S den : ℂ)⁻¹ *
      ∑ x : ThetaQuotient K S (exteriorMul K S den A),
        poissonKernelOnQuotient K S P den A h x := by
  unfold finitePoissonFactor
  apply congrArg (fun v : ℂ => (exteriorNorm K S den : ℂ)⁻¹ * v)
  apply Finset.sum_congr rfl
  intro x _
  rw [← poissonKernelOnQuotient_mk, Ideal.Quotient.mk_out]

/-- The actual prime-level probe Gauss sum is its literal finite-field
Gauss transform, including zero frequency. -/
theorem probeGauss_prime_eq_gaussAt (P : ProbeData K S) (p : ExteriorPrime K S)
    (m : S.integer K) :
    probeGauss K S P (exteriorPrimeIdeal K S p) m =
      gaussAt (thetaPrimeCharacter K S P.arithmetic p) (primeAddCharacter K S P.arithmetic p)
        (sIntegerSexticResidueMap K S p.val p.property m) := by
  let e := thetaPrimeResidueEquiv K S p
  have he : e (sIntegerSexticResidueMap K S p.val p.property m) =
      Ideal.Quotient.mk _ m := e.apply_symm_apply _
  change (∑ x : ThetaQuotient K S (exteriorPrimeIdeal K S p),
    symbolOnQuotient K S P.arithmetic (exteriorPrimeIdeal K S p) x *
      thetaPrincipalAddCharacter K S P.arithmetic (exteriorPrimeIdeal K S p)
        (Ideal.Quotient.mk _ m * x)) = _
  calc
    _ = ∑ x : 𝓞 K ⧸ p.val.asIdeal,
        symbolOnQuotient K S P.arithmetic (exteriorPrimeIdeal K S p) (e x) *
          thetaPrincipalAddCharacter K S P.arithmetic (exteriorPrimeIdeal K S p)
            (Ideal.Quotient.mk _ m * e x) := (e.toEquiv.sum_comp _).symm
    _ = _ := by
      change _ = ∑ x : 𝓞 K ⧸ p.val.asIdeal,
        thetaPrimeCharacter K S P.arithmetic p x *
          primeAddCharacter K S P.arithmetic p
            (sIntegerSexticResidueMap K S p.val p.property m * x)
      apply Finset.sum_congr rfl
      intro x _
      rw [primeQuotientSymbol_equiv]
      change _ = thetaPrimeCharacter K S P.arithmetic p x *
        thetaPrincipalAddCharacter K S P.arithmetic (exteriorPrimeIdeal K S p)
          (e (sIntegerSexticResidueMap K S p.val p.property m * x))
      rw [map_mul e, he]

def principalResidue (D : ThetaArithmeticData K S) (p : ExteriorPrime K S)
    (n : ℕ) (hn : 1 ≤ n) :
    PowerQuotient (primeGenerator K S D p) n →+* (𝓞 K ⧸ p.val.asIdeal) :=
  (principalPrimeResidueEquiv K S D p).toRingHom.comp
    (residueMap (primeGenerator K S D p) n hn)

@[simp] theorem principalResidue_mk (D : ThetaArithmeticData K S) (p : ExteriorPrime K S)
    (n : ℕ) (hn : 1 ≤ n) (a : S.integer K) :
    principalResidue K S D p n hn (Ideal.Quotient.mk _ a) =
      sIntegerSexticResidueMap K S p.val p.property a := by
  change principalPrimeResidueEquiv K S D p (residueMap _ _ _ _) = _
  rw [residueMap_mk, principalPrimeResidueEquiv_mk]

theorem principalCharacter_power_residue (D : ThetaArithmeticData K S)
    (p : ExteriorPrime K S) (n : ℕ) (hn : 1 ≤ n) (r : ℕ)
    (x : PowerQuotient (primeGenerator K S D p) n) :
    (principalPrimeCharacter K S D p ^ r) (residueMap (primeGenerator K S D p) n hn x) =
      (thetaPrimeCharacter K S D p ^ r) (principalResidue K S D p n hn x) := by
  rw [principalPrimeCharacter, ← pullbackMulChar_pow]
  rfl

/-- Every inflated power has the required sixth-unit invariance; r=0
continues to be the unit mask, not the constant-one function. -/
theorem principalResidue_fourier_sixth_shift (D : ThetaArithmeticData K S)
    (p : ExteriorPrime K S) (n : ℕ) (hn : 1 ≤ n) (r : ℕ)
    (U : (PowerQuotient (primeGenerator K S D p) n)ˣ)
    (h : PowerQuotient (primeGenerator K S D p) n) :
    fourier ((principalPowerAddCharacter K S D p n).mulShift ((U : _) ^ 6))
        (fun x => (thetaPrimeCharacter K S D p ^ r) (principalResidue K S D p n hn x)) h =
      fourier (principalPowerAddCharacter K S D p n)
        (fun x => (thetaPrimeCharacter K S D p ^ r) (principalResidue K S D p n hn x)) h := by
  have h6 : thetaPrimeCharacter K S D p ^ 6 = 1 := by
    simpa only [thetaPrimeCharacter_order K S D p] using
      pow_orderOf_eq_one (thetaPrimeCharacter K S D p)
  have hr6 : (thetaPrimeCharacter K S D p ^ r) ^ 6 = 1 := by
    calc
      _ = (thetaPrimeCharacter K S D p ^ 6) ^ r := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm r 6]
      _ = 1 := by rw [h6, one_pow]
  have hf : ∀ x : PowerQuotient (primeGenerator K S D p) n,
      (thetaPrimeCharacter K S D p ^ r)
          (principalResidue K S D p n hn (((U ^ 6 : _) : _) * x)) =
        (thetaPrimeCharacter K S D p ^ r) (principalResidue K S D p n hn x) := by
    intro x
    rw [Units.val_pow_eq_pow_val, map_mul, map_pow]
    exact HighBin.GeneratorUnitInvariance.character_sixth_unit _ hr6
      (Units.map (principalResidue K S D p n hn).toMonoidHom U) _
  simpa only [HighBin.FiniteResidueFourier.fourier, AddChar.mulShift_apply,
    Units.val_pow_eq_pow_val, mul_assoc] using
    HighBin.GeneratorUnitInvariance.fourier_unit_invariant
      (principalPowerAddCharacter K S D p n)
      (fun x => (thetaPrimeCharacter K S D p ^ r) (principalResidue K S D p n hn x))
      (U ^ 6) hf h

def primeTimesPowerQuotientEquiv (D : ThetaArithmeticData K S)
    (p : ExteriorPrime K S) (t : ℕ) :
    PowerQuotient (primeGenerator K S D p) (t + 1) ≃+*
      ThetaQuotient K S (exteriorMul K S (exteriorPrimeIdeal K S p)
        (exteriorPower K S (exteriorPrimeIdeal K S p) t)) :=
  Ideal.quotEquivOfEq (by
    rw [primeGenerator_powerIdeal]
    change (p.val.asIdeal ^ (t + 1)).map (algebraMap (𝓞 K) (S.integer K)) =
      (p.val.asIdeal * p.val.asIdeal ^ t).map (algebraMap (𝓞 K) (S.integer K))
    rw [pow_succ'])

@[simp] theorem primeTimesPowerQuotientEquiv_mk (D : ThetaArithmeticData K S)
    (p : ExteriorPrime K S) (t : ℕ) (a : S.integer K) :
    primeTimesPowerQuotientEquiv K S D p t (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk _ a := rfl

theorem primeProduct_addCharacter_unitShift (D : ThetaArithmeticData K S)
    (p : ExteriorPrime K S) (t : ℕ) (U : (S.integer K)ˣ)
    (hgen : D.generator (exteriorPower K S (exteriorPrimeIdeal K S p) t) =
      (U : S.integer K) ^ 6 * primeGenerator K S D p ^ t)
    (x : PowerQuotient (primeGenerator K S D p) (t + 1)) :
    productPrincipalCharacter K S D (exteriorPrimeIdeal K S p)
        (exteriorPower K S (exteriorPrimeIdeal K S p) t)
        (primeTimesPowerQuotientEquiv K S D p t x) =
      principalPowerAddCharacter K S D p (t + 1)
        (((Units.map (Ideal.Quotient.mk (powerIdeal (primeGenerator K S D p) (t + 1))).toMonoidHom
          U⁻¹ : (PowerQuotient (primeGenerator K S D p) (t + 1))ˣ) : _) ^ 6 * x) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  change productPrincipalCharacter K S D (exteriorPrimeIdeal K S p)
      (exteriorPower K S (exteriorPrimeIdeal K S p) t)
      (primeTimesPowerQuotientEquiv K S D p t (Ideal.Quotient.mk _ a)) =
    principalPowerAddCharacter K S D p (t + 1)
      (Ideal.Quotient.mk _ ((U⁻¹ : (S.integer K)ˣ) : S.integer K) ^ 6 *
        Ideal.Quotient.mk _ a)
  rw [primeTimesPowerQuotientEquiv_mk, ← map_pow, ← map_mul,
    productPrincipalCharacter_mk, poissonPrincipalPowerAddCharacter_mk]
  apply congrArg (sLocalPrincipalPhase K S)
  have hπK : (primeGenerator K S D p : K) ≠ 0 := by
    intro h
    exact primeGenerator_ne_zero K S D p (Subtype.ext h)
  have huK : ((U : S.integer K) : K) ≠ 0 := by
    intro h
    exact U.ne_zero (Subtype.ext h)
  have huinv : (((U⁻¹ : (S.integer K)ˣ) : S.integer K) : K) =
      (((U : S.integer K) : K)⁻¹) :=
    map_units_inv (S.integer K).val U
  rw [hgen]
  change _ / ((primeGenerator K S D p : K) * _) = _
  simp only [Subalgebra.coe_mul, Subalgebra.coe_pow, huinv, pow_succ]
  field_simp [hπK, huK] <;> ring

/-- The normalized k=1 branch, before its prime-power Fourier evaluation. -/
theorem finitePoisson_prime_power_eq_fourier (P : ProbeData K S)
    (hP : AllowedGeneratorInput K S P.arithmetic)
    (p : ExteriorPrime K S) (t : ℕ) (ht : 1 ≤ t) (h : S.integer K) :
    finitePoissonFactor K S P (exteriorPrimeIdeal K S p)
        (exteriorPower K S (exteriorPrimeIdeal K S p) t) h =
      (HighBin.ActualGaussPhases.gaussFamily (thetaPrimeCharacter K S P.arithmetic p)
          (primeAddCharacter K S P.arithmetic p) 1 / (p.val.asIdeal.absNorm : ℂ)) *
        fourier (principalPowerAddCharacter K S P.arithmetic p (t + 1))
          (fun x => (principalPrimeCharacter K S P.arithmetic p ^ (t - 1))
            (residueMap (primeGenerator K S P.arithmetic p) (t + 1) (by omega) x))
          (Ideal.Quotient.mk _ h) := by
  let D := P.arithmetic
  let π := primeGenerator K S D p
  let A := exteriorPower K S (exteriorPrimeIdeal K S p) t
  let e := primeTimesPowerQuotientEquiv K S D p t
  let R := PowerQuotient π (t + 1)
  let ρ := principalResidue K S D p (t + 1) (by omega)
  let χ := thetaPrimeCharacter K S D p
  let φ := primeAddCharacter K S D p
  let ψ := principalPowerAddCharacter K S D p (t + 1)
  obtain ⟨v, hv⟩ := generator_power_eq_sixth_unit K S D hP (exteriorPrimeIdeal K S p) t
  let U : (S.integer K)ˣ := S.unitEquivUnitsInteger K v
  let V : Rˣ := Units.map (Ideal.Quotient.mk (powerIdeal π (t + 1))).toMonoidHom U⁻¹
  have hk (x : R) : poissonKernelOnQuotient K S P (exteriorPrimeIdeal K S p) A h (e x) =
      gaussAt χ φ (-(ρ x)) * (χ ^ t) (ρ x) * ψ ((V : R) ^ 6 * (Ideal.Quotient.mk _ h * x)) := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [primeTimesPowerQuotientEquiv_mk, poissonKernelOnQuotient_mk,
      probeGauss_prime_eq_gaussAt, idealSymbol_primePower_mulChar K S D p t ht,
      principalResidue_mk, map_neg]
    congr 1
    have hh := primeProduct_addCharacter_unitShift K S D p t U hv (Ideal.Quotient.mk _ (h * a))
    rw [primeTimesPowerQuotientEquiv_mk, productPrincipalCharacter_mk] at hh
    simpa only [Subalgebra.coe_mul, map_mul] using hh
  have hconv : finitePoissonFactor K S P (exteriorPrimeIdeal K S p) A h =
      HighBin.FourierInversion.liftedConvolution ρ χ (χ ^ t) φ
        (ψ.mulShift ((V : R) ^ 6)) (Ideal.Quotient.mk _ h) := by
    rw [finitePoissonFactor_eq_sum_kernel]
    have hsum : (∑ x : ThetaQuotient K S (exteriorMul K S (exteriorPrimeIdeal K S p) A),
        poissonKernelOnQuotient K S P (exteriorPrimeIdeal K S p) A h x) =
        ∑ x : R, gaussAt χ φ (-(ρ x)) * (χ ^ t) (ρ x) *
          ψ ((V : R) ^ 6 * (Ideal.Quotient.mk _ h * x)) := by
      rw [← e.toEquiv.sum_comp]
      exact Finset.sum_congr rfl (fun x _ => hk x)
    rw [hsum]
    unfold HighBin.FourierInversion.liftedConvolution
    rw [card_primeIdealResidueField]
    simp only [exteriorNorm, exteriorPrimeIdeal, Complex.ofReal_natCast,
      AddChar.mulShift_apply] <;> rfl
  have hχ : χ ≠ 1 := HighBin.ActualGaussPhases.character_nonprincipal χ
    (thetaPrimeCharacter_order K S D p)
  have hminus : χ⁻¹ (-1) = 1 := by
    rw [MulChar.inv_apply_eq_inv', thetaPrimeCharacter_neg_one K S D p, inv_one]
  have hpow : χ ^ t * χ⁻¹ = χ ^ (t - 1) := by
    simpa only [pow_one] using (pow_sub χ ht).symm
  rw [hconv, HighBin.FourierInversion.liftedConvolution_eq_of_neg_one ρ χ (χ ^ t)
    hχ hminus φ (ψ.mulShift ((V : R) ^ 6)), hpow,
    principalResidue_fourier_sixth_shift K S D p (t + 1) (by omega) (t - 1) V,
    card_primeIdealResidueField]
  simp only [HighBin.ActualGaussPhases.gaussFamily, pow_one,
    principalCharacter_power_residue] <;> rfl

/-- The k=1 valuation table for the actual finitePoissonFactor, retaining
the product of the two chosen ideal generators in its definition. -/
theorem finitePoisson_prime_power_eq_valuationGauss (P : ProbeData K S)
    (hP : AllowedGeneratorInput K S P.arithmetic)
    (p : ExteriorPrime K S) (t : ℕ) (ht : 1 ≤ t)
    (v : S.integer K) (hv : ¬primeGenerator K S P.arithmetic p ∣ v) (J : ℕ) :
    finitePoissonFactor K S P (exteriorPrimeIdeal K S p)
        (exteriorPower K S (exteriorPrimeIdeal K S p) t)
        (primeGenerator K S P.arithmetic p ^ J * v) =
      (HighBin.ActualGaussPhases.gaussFamily (thetaPrimeCharacter K S P.arithmetic p)
          (primeAddCharacter K S P.arithmetic p) 1 / (p.val.asIdeal.absNorm : ℂ)) *
        valuationGauss p.val.asIdeal.absNorm
          (HighBin.ActualGaussPhases.gaussFamily (thetaPrimeCharacter K S P.arithmetic p)
            (primeAddCharacter K S P.arithmetic p))
          (thetaPrimeCharacter K S P.arithmetic p (sIntegerSexticResidueMap K S p.val p.property v))
          (t + 1) (t - 1) J := by
  rw [finitePoisson_prime_power_eq_fourier K S P hP p t ht]
  rw [actualPrimePowerFourier_eq_tableGauss K S P.arithmetic p (t + 1) (by omega) v hv J (t - 1)]

/-- The unit ideal's symbol is the constant-one function. It is not the
zeroth power of a nontrivial prime residue character. -/
theorem symbolOnQuotient_primePower_zero (D : ThetaArithmeticData K S)
    (p : ExteriorPrime K S)
    (x : ThetaQuotient K S (exteriorPower K S (exteriorPrimeIdeal K S p) 0)) :
    symbolOnQuotient K S D (exteriorPower K S (exteriorPrimeIdeal K S p) 0) x = 1 := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [symbolOnQuotient, sIntegerSexticIdealQuotientFunction_mk]
  change idealSymbol K S D (exteriorPower K S (exteriorPrimeIdeal K S p) 0) a = 1
  rw [idealSymbol_primePower, pow_zero]

/-- The original unit-modulus Gauss sum has one summand of value one,
for its actual chosen unit-ideal generator. -/
theorem probeGauss_primePower_zero (P : ProbeData K S) (p : ExteriorPrime K S)
    (m : S.integer K) :
    probeGauss K S P (exteriorPower K S (exteriorPrimeIdeal K S p) 0) m = 1 := by
  let I := exteriorPower K S (exteriorPrimeIdeal K S p) 0
  have htop : I.val.val.map (algebraMap (𝓞 K) (S.integer K)) = ⊤ := by
    change (p.val.asIdeal ^ 0).map (algebraMap (𝓞 K) (S.integer K)) = ⊤
    rw [pow_zero, Ideal.one_eq_top, Ideal.map_top]
  letI : Subsingleton (ThetaQuotient K S I) := Ideal.Quotient.subsingleton_iff.mpr htop
  letI : Unique (ThetaQuotient K S I) :=
    { default := 0, uniq := fun x => Subsingleton.elim x 0 }
  change (∑ x : ThetaQuotient K S I, symbolOnQuotient K S P.arithmetic I x *
    thetaPrincipalAddCharacter K S P.arithmetic I (Ideal.Quotient.mk _ m * x)) = 1
  calc
    _ = ∑ _x : ThetaQuotient K S I, (1 : ℂ) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [symbolOnQuotient_primePower_zero, one_mul,
        Subsingleton.elim (Ideal.Quotient.mk _ m * x) 0, AddChar.map_zero_eq_one]
    _ = 1 := by simp

/-- A common helper for actual product denominators. Its generator
identity and quotient map are supplied by literal ideal arithmetic. -/
theorem productPrincipalCharacter_unitShift_of_generators (D : ThetaArithmeticData K S)
    (p : ExteriorPrime K S) (n : ℕ) (den A : ExteriorIdeal K S)
    (e : PowerQuotient (primeGenerator K S D p) n ≃+* ThetaQuotient K S (exteriorMul K S den A))
    (he : ∀ a : S.integer K, e (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ a)
    (U : (S.integer K)ˣ)
    (hgen : D.generator den * D.generator A =
      (U : S.integer K) ^ 6 * primeGenerator K S D p ^ n)
    (x : PowerQuotient (primeGenerator K S D p) n) :
    productPrincipalCharacter K S D den A (e x) =
      principalPowerAddCharacter K S D p n
        (((Units.map (Ideal.Quotient.mk (powerIdeal (primeGenerator K S D p) n)).toMonoidHom
          U⁻¹ : (PowerQuotient (primeGenerator K S D p) n)ˣ) : _) ^ 6 * x) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  change productPrincipalCharacter K S D den A (e (Ideal.Quotient.mk _ a)) =
    principalPowerAddCharacter K S D p n
      (Ideal.Quotient.mk _ ((U⁻¹ : (S.integer K)ˣ) : S.integer K) ^ 6 *
        Ideal.Quotient.mk _ a)
  rw [he, ← map_pow, ← map_mul, productPrincipalCharacter_mk,
    poissonPrincipalPowerAddCharacter_mk]
  apply congrArg (sLocalPrincipalPhase K S)
  have hπK : (primeGenerator K S D p : K) ≠ 0 := by
    intro h
    exact primeGenerator_ne_zero K S D p (Subtype.ext h)
  have huK : ((U : S.integer K) : K) ≠ 0 := by
    intro h
    exact U.ne_zero (Subtype.ext h)
  have huinv : (((U⁻¹ : (S.integer K)ˣ) : S.integer K) : K) =
      (((U : S.integer K) : K)⁻¹) :=
    map_units_inv (S.integer K).val U
  rw [← Subalgebra.coe_mul, hgen]
  simp only [Subalgebra.coe_mul, Subalgebra.coe_pow, huinv]
  field_simp [hπK, huK] <;> ring

def primeZeroTimesPowerQuotientEquiv (D : ThetaArithmeticData K S)
    (p : ExteriorPrime K S) (t : ℕ) :
    PowerQuotient (primeGenerator K S D p) t ≃+*
      ThetaQuotient K S (exteriorMul K S
        (exteriorPower K S (exteriorPrimeIdeal K S p) 0)
        (exteriorPower K S (exteriorPrimeIdeal K S p) t)) :=
  Ideal.quotEquivOfEq (by
    rw [primeGenerator_powerIdeal]
    change (p.val.asIdeal ^ t).map (algebraMap (𝓞 K) (S.integer K)) =
      (p.val.asIdeal ^ 0 * p.val.asIdeal ^ t).map (algebraMap (𝓞 K) (S.integer K))
    rw [pow_zero, one_mul])

@[simp] theorem primeZeroTimesPowerQuotientEquiv_mk (D : ThetaArithmeticData K S)
    (p : ExteriorPrime K S) (t : ℕ) (a : S.integer K) :
    primeZeroTimesPowerQuotientEquiv K S D p t (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk _ a := rfl

/-- The actual k=0 branch, with the chosen unit-ideal generator's sixth
unit phase removed by a finite variable bijection. -/
theorem finitePoisson_zero_power_eq_fourier (P : ProbeData K S)
    (hP : AllowedGeneratorInput K S P.arithmetic)
    (p : ExteriorPrime K S) (t : ℕ) (ht : 1 ≤ t) (h : S.integer K) :
    finitePoissonFactor K S P (exteriorPower K S (exteriorPrimeIdeal K S p) 0)
        (exteriorPower K S (exteriorPrimeIdeal K S p) t) h =
      fourier (principalPowerAddCharacter K S P.arithmetic p t)
        (fun x => (principalPrimeCharacter K S P.arithmetic p ^ t)
          (residueMap (primeGenerator K S P.arithmetic p) t ht x)) (Ideal.Quotient.mk _ h) := by
  let D := P.arithmetic
  let π := primeGenerator K S D p
  let den := exteriorPower K S (exteriorPrimeIdeal K S p) 0
  let A := exteriorPower K S (exteriorPrimeIdeal K S p) t
  let e := primeZeroTimesPowerQuotientEquiv K S D p t
  let R := PowerQuotient π t
  let ρ := principalResidue K S D p t ht
  let χ := thetaPrimeCharacter K S D p
  let ψ := principalPowerAddCharacter K S D p t
  obtain ⟨v₀, hv₀⟩ := generator_power_eq_sixth_unit K S D hP (exteriorPrimeIdeal K S p) 0
  obtain ⟨v₁, hv₁⟩ := generator_power_eq_sixth_unit K S D hP (exteriorPrimeIdeal K S p) t
  let U : (S.integer K)ˣ := S.unitEquivUnitsInteger K v₀ * S.unitEquivUnitsInteger K v₁
  let V : Rˣ := Units.map (Ideal.Quotient.mk (powerIdeal π t)).toMonoidHom U⁻¹
  have hgen : D.generator den * D.generator A = (U : S.integer K) ^ 6 * π ^ t := by
    rw [hv₀, hv₁]
    simp only [U, π, primeGenerator, Units.val_mul, mul_pow, pow_zero, mul_one]
    ring
  have hk (x : R) : poissonKernelOnQuotient K S P den A h (e x) =
      (χ ^ t) (ρ x) * ψ ((V : R) ^ 6 * (Ideal.Quotient.mk _ h * x)) := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [primeZeroTimesPowerQuotientEquiv_mk, poissonKernelOnQuotient_mk,
      probeGauss_primePower_zero, one_mul, idealSymbol_primePower_mulChar K S D p t ht,
      principalResidue_mk]
    congr 1
    have hh := productPrincipalCharacter_unitShift_of_generators K S D p t den A e
      (primeZeroTimesPowerQuotientEquiv_mk K S D p t) U hgen (Ideal.Quotient.mk _ (h * a))
    rw [primeZeroTimesPowerQuotientEquiv_mk, productPrincipalCharacter_mk] at hh
    simpa only [Subalgebra.coe_mul, map_mul] using hh
  have heq : finitePoissonFactor K S P den A h =
      fourier (ψ.mulShift ((V : R) ^ 6)) (fun x => (χ ^ t) (ρ x)) (Ideal.Quotient.mk _ h) := by
    rw [finitePoissonFactor_eq_sum_kernel]
    have hN : exteriorNorm K S den = 1 := by simp [den, exteriorNorm, exteriorPower]
    rw [hN, Complex.ofReal_one, inv_one, one_mul, ← e.toEquiv.sum_comp]
    exact Finset.sum_congr rfl (fun x _ => hk x)
  rw [heq, principalResidue_fourier_sixth_shift K S D p t ht t V]
  simp only [principalCharacter_power_residue] <;> rfl

theorem finitePoisson_zero_power_eq_valuationGauss (P : ProbeData K S)
    (hP : AllowedGeneratorInput K S P.arithmetic)
    (p : ExteriorPrime K S) (t : ℕ) (ht : 1 ≤ t)
    (v : S.integer K) (hv : ¬primeGenerator K S P.arithmetic p ∣ v) (J : ℕ) :
    finitePoissonFactor K S P (exteriorPower K S (exteriorPrimeIdeal K S p) 0)
        (exteriorPower K S (exteriorPrimeIdeal K S p) t)
        (primeGenerator K S P.arithmetic p ^ J * v) =
      valuationGauss p.val.asIdeal.absNorm
        (HighBin.ActualGaussPhases.gaussFamily (thetaPrimeCharacter K S P.arithmetic p)
          (primeAddCharacter K S P.arithmetic p))
        (thetaPrimeCharacter K S P.arithmetic p (sIntegerSexticResidueMap K S p.val p.property v))
        t t J := by
  rw [finitePoisson_zero_power_eq_fourier K S P hP p t ht]
  exact actualPrimePowerFourier_eq_tableGauss K S P.arithmetic p t ht v hv J t

/-- The complete positive-index local table now evaluates the literal
finitePoissonFactor for every denominator exponent, with k=0, k=1,
all k≥2 zeros, and every principal-character branch included. -/
theorem finitePoisson_primePowers_eq_positiveConvolution (P : ProbeData K S)
    (hP : AllowedGeneratorInput K S P.arithmetic)
    (p : ExteriorPrime K S) (t k : ℕ) (ht : 1 ≤ t)
    (v : S.integer K) (hv : ¬primeGenerator K S P.arithmetic p ∣ v) (J : ℕ) :
    finitePoissonFactor K S P (exteriorPower K S (exteriorPrimeIdeal K S p) k)
        (exteriorPower K S (exteriorPrimeIdeal K S p) t)
        (primeGenerator K S P.arithmetic p ^ J * v) =
      positiveConvolution p.val.asIdeal.absNorm
        (HighBin.ActualGaussPhases.gaussFamily (thetaPrimeCharacter K S P.arithmetic p)
          (primeAddCharacter K S P.arithmetic p))
        (thetaPrimeCharacter K S P.arithmetic p (sIntegerSexticResidueMap K S p.val p.property v))
        t k J := by
  by_cases hk₀ : k = 0
  · subst k
    rw [positiveConvolution, if_pos rfl]
    exact finitePoisson_zero_power_eq_valuationGauss K S P hP p t ht v hv J
  by_cases hk₁ : k = 1
  · subst k
    rw [positiveConvolution, if_neg (by norm_num), if_pos rfl, exteriorPower_one]
    exact finitePoisson_prime_power_eq_valuationGauss K S P hP p t ht v hv J
  · rw [positiveConvolution, if_neg hk₀, if_neg hk₁]
    exact finitePoisson_primePowers_zero_of_two_le K S P hP p k t (by omega) ht _

def primePowerTimesZeroQuotientEquiv (D : ThetaArithmeticData K S)
    (p : ExteriorPrime K S) (k : ℕ) :
    PowerQuotient (primeGenerator K S D p) k ≃+*
      ThetaQuotient K S (exteriorMul K S
        (exteriorPower K S (exteriorPrimeIdeal K S p) k)
        (exteriorPower K S (exteriorPrimeIdeal K S p) 0)) :=
  Ideal.quotEquivOfEq (by
    rw [primeGenerator_powerIdeal]
    change (p.val.asIdeal ^ k).map (algebraMap (𝓞 K) (S.integer K)) =
      (p.val.asIdeal ^ k * p.val.asIdeal ^ 0).map (algebraMap (𝓞 K) (S.integer K))
    rw [pow_zero, mul_one])

@[simp] theorem primePowerTimesZeroQuotientEquiv_mk (D : ThetaArithmeticData K S)
    (p : ExteriorPrime K S) (k : ℕ) (a : S.integer K) :
    primePowerTimesZeroQuotientEquiv K S D p k (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk _ a := rfl

/-- At completed index one, exact finite Fourier inversion recovers the
original denominator symbol, with its nonunit zeros. The original chosen
unit-ideal generator is accounted for by the sixth-unit frequency shift. -/
theorem finitePoisson_power_zero_eq_symbol (P : ProbeData K S)
    (hP : AllowedGeneratorInput K S P.arithmetic)
    (p : ExteriorPrime K S) (k : ℕ) (hk : 1 ≤ k) (h : S.integer K) :
    finitePoissonFactor K S P (exteriorPower K S (exteriorPrimeIdeal K S p) k)
        (exteriorPower K S (exteriorPrimeIdeal K S p) 0) h =
      idealSymbol K S P.arithmetic (exteriorPower K S (exteriorPrimeIdeal K S p) k) h := by
  let D := P.arithmetic
  let π := primeGenerator K S D p
  let den := exteriorPower K S (exteriorPrimeIdeal K S p) k
  let A := exteriorPower K S (exteriorPrimeIdeal K S p) 0
  let e := primePowerTimesZeroQuotientEquiv K S D p k
  let R := PowerQuotient π k
  let ψ := principalPowerAddCharacter K S D p k
  let f : R → ℂ := fun x => (principalPrimeCharacter K S D p ^ k) (residueMap π k hk x)
  obtain ⟨v₁, hv₁⟩ := generator_power_eq_sixth_unit K S D hP (exteriorPrimeIdeal K S p) k
  obtain ⟨v₀, hv₀⟩ := generator_power_eq_sixth_unit K S D hP (exteriorPrimeIdeal K S p) 0
  let U : (S.integer K)ˣ := S.unitEquivUnitsInteger K v₁ * S.unitEquivUnitsInteger K v₀
  let V : Rˣ := Units.map (Ideal.Quotient.mk (powerIdeal π k)).toMonoidHom U⁻¹
  have hgen : D.generator den * D.generator A = (U : S.integer K) ^ 6 * π ^ k := by
    rw [hv₁, hv₀]
    simp only [U, π, primeGenerator, Units.val_mul, mul_pow, pow_zero, mul_one]
    ring
  have hkernel (x : R) : poissonKernelOnQuotient K S P den A h (e x) =
      fourier ψ f (-x) * ψ ((V : R) ^ 6 * (Ideal.Quotient.mk _ h * x)) := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [primePowerTimesZeroQuotientEquiv_mk, poissonKernelOnQuotient_mk,
      probeGauss_primePower_eq_principal_fourier K S P hP p k hk,
      idealSymbol_primePower, pow_zero, mul_one, map_neg]
    congr 1
    have hh := productPrincipalCharacter_unitShift_of_generators K S D p k den A e
      (primePowerTimesZeroQuotientEquiv_mk K S D p k) U hgen (Ideal.Quotient.mk _ (h * a))
    rw [primePowerTimesZeroQuotientEquiv_mk, productPrincipalCharacter_mk] at hh
    simpa only [Subalgebra.coe_mul, map_mul] using hh
  have hN : (exteriorNorm K S den : ℂ) = (Fintype.card R : ℂ) := by
    rw [principalPower_card]
    simp only [den, exteriorNorm, exteriorPower, exteriorPrimeIdeal, SubmonoidClass.coe_pow,
      map_pow, Nat.cast_pow, Complex.ofReal_pow, Complex.ofReal_natCast]
  have heq : finitePoissonFactor K S P den A h = f ((V : R) ^ 6 * Ideal.Quotient.mk _ h) := by
    rw [finitePoissonFactor_eq_sum_kernel, hN, ← e.toEquiv.sum_comp]
    change (Fintype.card R : ℂ)⁻¹ *
      (∑ x : R, poissonKernelOnQuotient K S P den A h (e x)) =
        f ((V : R) ^ 6 * Ideal.Quotient.mk _ h)
    simp_rw [hkernel]
    simpa only [mul_assoc] using
      HighBin.FourierInversion.normalized_finite_fourier_inversion ψ
        (principalPowerAddCharacter_isPrimitive K S D p k) f
        ((V : R) ^ 6 * Ideal.Quotient.mk _ h)
  rw [heq]
  change (principalPrimeCharacter K S D p ^ k)
      (residueMap π k hk ((V : R) ^ 6 * Ideal.Quotient.mk _ h)) = _
  rw [principalPower_symbol_sixth_unit K S D p k hk V,
    principalCharacter_power_residue, principalResidue_mk,
    idealSymbol_primePower_mulChar K S D p k hk]

/-- Both unit ideals give the one-element finite sum, for every frequency. -/
theorem finitePoisson_zero_zero (P : ProbeData K S) (p : ExteriorPrime K S)
    (h : S.integer K) :
    finitePoissonFactor K S P (exteriorPower K S (exteriorPrimeIdeal K S p) 0)
      (exteriorPower K S (exteriorPrimeIdeal K S p) 0) h = 1 := by
  let A := exteriorPower K S (exteriorPrimeIdeal K S p) 0
  let B := exteriorMul K S A A
  have htop : B.val.val.map (algebraMap (𝓞 K) (S.integer K)) = ⊤ := by
    change (p.val.asIdeal ^ 0 * p.val.asIdeal ^ 0).map
      (algebraMap (𝓞 K) (S.integer K)) = ⊤
    rw [pow_zero, one_mul, Ideal.one_eq_top, Ideal.map_top]
  letI : Subsingleton (ThetaQuotient K S B) := Ideal.Quotient.subsingleton_iff.mpr htop
  letI : Unique (ThetaQuotient K S B) :=
    { default := 0, uniq := fun x => Subsingleton.elim x 0 }
  have hg (x : ThetaQuotient K S A) : probeGaussOnQuotient K S P A x = 1 := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact probeGauss_primePower_zero K S P p a
  have hs (x : ThetaQuotient K S A) : quotientSymbol K S P.arithmetic A x = 1 :=
    symbolOnQuotient_primePower_zero K S P.arithmetic p x
  have hkernel (x : ThetaQuotient K S B) : poissonKernelOnQuotient K S P A A h x = 1 := by
    unfold poissonKernelOnQuotient
    rw [hg, hs, one_mul, one_mul,
      Subsingleton.elim (Ideal.Quotient.mk _ h * x) 0, AddChar.map_zero_eq_one]
  rw [finitePoissonFactor_eq_sum_kernel]
  have hN : exteriorNorm K S A = 1 := by simp [A, exteriorNorm, exteriorPower]
  rw [hN, Complex.ofReal_one, inv_one, one_mul]
  change (∑ x : ThetaQuotient K S B, poissonKernelOnQuotient K S P A A h x) = 1
  simp only [hkernel, Finset.sum_const, Finset.card_univ, Fintype.card_unique, one_smul]

/-- The completed-unit row used by the Euler sum, with its exact zero
mask for every positive denominator and positive frequency valuation. -/
theorem finitePoisson_primePowers_completedUnit (P : ProbeData K S)
    (hP : AllowedGeneratorInput K S P.arithmetic)
    (p : ExteriorPrime K S) (k J : ℕ)
    (v : S.integer K) (hv : ¬primeGenerator K S P.arithmetic p ∣ v) :
    finitePoissonFactor K S P (exteriorPower K S (exteriorPrimeIdeal K S p) k)
        (exteriorPower K S (exteriorPrimeIdeal K S p) 0)
        (primeGenerator K S P.arithmetic p ^ J * v) =
      if k = 0 then 1 else if J = 0 then
        thetaPrimeCharacter K S P.arithmetic p (sIntegerSexticResidueMap K S p.val p.property v) ^ k
      else 0 := by
  by_cases hk : k = 0
  · subst k
    rw [if_pos rfl, finitePoisson_zero_zero]
  rw [if_neg hk, finitePoisson_power_zero_eq_symbol K S P hP p k (by omega)]
  by_cases hJ : J = 0
  · subst J
    rw [if_pos rfl, pow_zero, one_mul, idealSymbol_primePower]
    rfl
  · rw [if_neg hJ]
    exact idealSymbol_primePower_zero_of_dvd K S P.arithmetic p k (by omega) _
      (dvd_mul_of_dvd_left (dvd_pow_self _ hJ) v)

/-- A frequency multiplier prime to p is a unit in every actual p^n
quotient. It need not be a global S-unit. -/
theorem principalPower_mk_isUnit (D : ThetaArithmeticData K S)
    (p : ExteriorPrime K S) (n : ℕ) (a : S.integer K)
    (ha : ¬primeGenerator K S D p ∣ a) :
    IsUnit (Ideal.Quotient.mk (powerIdeal (primeGenerator K S D p) n) a) := by
  have hnot : a ∉ powerIdeal (primeGenerator K S D p) 1 := by
    simpa only [powerIdeal, pow_one, Ideal.mem_span_singleton] using ha
  have h := Ideal.Quotient.isUnit_mk_pow_of_notMem
    (powerIdeal (primeGenerator K S D p) 1) (n := n) hnot
  have hpow : powerIdeal (primeGenerator K S D p) 1 ^ n =
      powerIdeal (primeGenerator K S D p) n := by
    simp only [powerIdeal, pow_one, Ideal.span_singleton_pow]
  rwa [hpow] at h

theorem principalPower_fourier_frequency_sixth_unit (D : ThetaArithmeticData K S)
    (p : ExteriorPrime K S) (n : ℕ) (hn : 1 ≤ n) (r : ℕ)
    (U : (PowerQuotient (primeGenerator K S D p) n)ˣ)
    (h : PowerQuotient (primeGenerator K S D p) n) :
    fourier (principalPowerAddCharacter K S D p n)
        (fun x => (principalPrimeCharacter K S D p ^ r)
          (residueMap (primeGenerator K S D p) n hn x)) ((U : _) ^ 6 * h) =
      fourier (principalPowerAddCharacter K S D p n)
        (fun x => (principalPrimeCharacter K S D p ^ r)
          (residueMap (primeGenerator K S D p) n hn x)) h := by
  simp_rw [principalCharacter_power_residue]
  simpa only [HighBin.FiniteResidueFourier.fourier, AddChar.mulShift_apply, mul_assoc] using
    principalResidue_fourier_sixth_shift K S D p n hn r U h

theorem idealSymbol_primePower_sixth_invariant (D : ThetaArithmeticData K S)
    (p : ExteriorPrime K S) (k : ℕ) (a h : S.integer K)
    (ha : ¬primeGenerator K S D p ∣ a) :
    idealSymbol K S D (exteriorPower K S (exteriorPrimeIdeal K S p) k) (a ^ 6 * h) =
      idealSymbol K S D (exteriorPower K S (exteriorPrimeIdeal K S p) k) h := by
  obtain ⟨U, hU⟩ := principalPower_mk_isUnit K S D p 1 a ha
  have h6 : thetaPrimeCharacter K S D p ^ 6 = 1 := by
    simpa only [thetaPrimeCharacter_order K S D p] using
      pow_orderOf_eq_one (thetaPrimeCharacter K S D p)
  have hχ := HighBin.GeneratorUnitInvariance.character_sixth_unit
    (thetaPrimeCharacter K S D p) h6
    (Units.map (principalPrimeResidueEquiv K S D p).toMonoidHom U)
    (sIntegerSexticResidueMap K S p.val p.property h)
  have hval : thetaPrimeCharacter K S D p
      (sIntegerSexticResidueMap K S p.val p.property a ^ 6 *
        sIntegerSexticResidueMap K S p.val p.property h) =
      thetaPrimeCharacter K S D p (sIntegerSexticResidueMap K S p.val p.property h) := by
    change thetaPrimeCharacter K S D p
        (principalPrimeResidueEquiv K S D p (U : PowerQuotient (primeGenerator K S D p) 1) ^ 6 *
          sIntegerSexticResidueMap K S p.val p.property h) = _ at hχ
    rw [hU, principalPrimeResidueEquiv_mk] at hχ
    exact hχ
  rw [idealSymbol_primePower, idealSymbol_primePower]
  change thetaPrimeCharacter K S D p
      (sIntegerSexticResidueMap K S p.val p.property (a ^ 6 * h)) ^ k = _
  rw [map_mul, map_pow, hval]
  rfl

/-- Complete local sixth-unit compatibility, including the unit completed
index and all zero branches. The multiplier may be only locally a unit,
which is essential for generators from the other CRT prime block. -/
theorem finitePoisson_primePowers_frequency_sixth_invariant (P : ProbeData K S)
    (hP : AllowedGeneratorInput K S P.arithmetic)
    (p : ExteriorPrime K S) (k t : ℕ) (a h : S.integer K)
    (ha : ¬primeGenerator K S P.arithmetic p ∣ a) :
    finitePoissonFactor K S P (exteriorPower K S (exteriorPrimeIdeal K S p) k)
        (exteriorPower K S (exteriorPrimeIdeal K S p) t) (a ^ 6 * h) =
      finitePoissonFactor K S P (exteriorPower K S (exteriorPrimeIdeal K S p) k)
        (exteriorPower K S (exteriorPrimeIdeal K S p) t) h := by
  by_cases ht : t = 0
  · subst t
    by_cases hk : k = 0
    · subst k
      rw [finitePoisson_zero_zero, finitePoisson_zero_zero]
    · rw [finitePoisson_power_zero_eq_symbol K S P hP p k (by omega),
        finitePoisson_power_zero_eq_symbol K S P hP p k (by omega)]
      exact idealSymbol_primePower_sixth_invariant K S P.arithmetic p k a h ha
  have htpos : 1 ≤ t := by omega
  by_cases hk₀ : k = 0
  · subst k
    rw [finitePoisson_zero_power_eq_fourier K S P hP p t htpos,
      finitePoisson_zero_power_eq_fourier K S P hP p t htpos, map_mul, map_pow]
    obtain ⟨U, hU⟩ := principalPower_mk_isUnit K S P.arithmetic p t a ha
    rw [← hU]
    exact principalPower_fourier_frequency_sixth_unit K S P.arithmetic p t htpos t U _
  by_cases hk₁ : k = 1
  · subst k
    rw [exteriorPower_one, finitePoisson_prime_power_eq_fourier K S P hP p t htpos,
      finitePoisson_prime_power_eq_fourier K S P hP p t htpos, map_mul, map_pow]
    obtain ⟨U, hU⟩ := principalPower_mk_isUnit K S P.arithmetic p (t + 1) a ha
    rw [← hU, principalPower_fourier_frequency_sixth_unit K S P.arithmetic p
      (t + 1) (by omega) (t - 1) U]
  · rw [finitePoisson_primePowers_zero_of_two_le K S P hP p k t (by omega) htpos,
      finitePoisson_primePowers_zero_of_two_le K S P hP p k t (by omega) htpos]

#print axioms finitePoissonFactor_eq_sum_kernel
#print axioms probeGauss_prime_eq_gaussAt
#print axioms finitePoisson_prime_power_eq_fourier
#print axioms finitePoisson_prime_power_eq_valuationGauss
#print axioms finitePoisson_primePowers_eq_positiveConvolution
#print axioms finitePoisson_primePowers_completedUnit
#print axioms finitePoisson_primePowers_frequency_sixth_invariant

end HeckeSkeleton.HighBinActualPrimeGauss
