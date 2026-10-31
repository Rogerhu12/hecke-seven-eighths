import HeckeSkeleton.HighBinSupport.ActualInitialEulerProduct
import HeckeSkeleton.HighBinSupport.ActualFinitePoisson

/-!
# The original prime-block coefficient and the finite valuation table

The frequency is the actual row element in its actual sixth-unit sector.
The allowed-generator correction is removed by a proved finite-variable
bijection. The remaining unit phase is exactly `rowPrimeUnit`, and the
Gauss sums and norm powers have the original theta normalization.

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
open HeckeSkeleton.HighBinActualGenerators HeckeSkeleton.HighBinActualSymbols
open HeckeSkeleton.HighBinActualEuler HeckeSkeleton.HighBinActualPrimeGauss
open HeckeSkeleton.HighBinActualCRT HeckeSkeleton.HighBinActualAbsolute
open HighBin.PrincipalPowerSupport HighBin.FiniteLocalTable
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

local instance localPrimeField (p : ExteriorPrime K S) :
    Field (𝓞 K ⧸ p.val.asIdeal) := Ideal.Quotient.field _

local instance localPrimeFintype (p : ExteriorPrime K S) :
    Fintype (𝓞 K ⧸ p.val.asIdeal) := Fintype.ofFinite _

/-- The original sector times the generator with all p-factors removed. -/
def rowUnitPart (P : ProbeData K S) (u : FrequencyRow K S) (p : ExteriorPrime K S) :
    S.integer K :=
  (S.unitEquivUnitsInteger K (Quotient.out u.sector)).val *
    P.arithmetic.generator (removePrime K S u.ideal p)

@[simp] theorem rowUnitPart_residue (P : ProbeData K S) (u : FrequencyRow K S)
    (p : ExteriorPrime K S) :
    sIntegerSexticResidueMap K S p.val p.property (rowUnitPart K S P u p) =
      (rowPrimeUnit K S P u p : 𝓞 K ⧸ p.val.asIdeal) :=
  (rowPrimeUnit_val K S P u p).symm

theorem rowUnitPart_not_dvd (P : ProbeData K S) (u : FrequencyRow K S)
    (p : ExteriorPrime K S) : ¬primeGenerator K S P.arithmetic p ∣ rowUnitPart K S P u p := by
  intro hdiv
  have hm : Ideal.Quotient.mk (powerIdeal (primeGenerator K S P.arithmetic p) 1)
      (rowUnitPart K S P u p) = 0 :=
    (quotient_mk_zero_iff _ _ _).mpr (by simpa only [pow_one] using hdiv)
  have hres : sIntegerSexticResidueMap K S p.val p.property (rowUnitPart K S P u p) = 0 := by
    rw [← principalPrimeResidueEquiv_mk K S P.arithmetic p, hm, map_zero]
  rw [rowUnitPart_residue] at hres
  exact (rowPrimeUnit K S P u p).ne_zero hres

/-- The actual prime-block frequency has valuation j+6m and precisely the
row's unit part, up to a sixth power of a global S-unit. -/
theorem poissonFrequency_primePower_sixth_unit (P : ProbeData K S)
    (hP : AllowedGeneratorInput K S P.arithmetic)
    (u : FrequencyRow K S) (p : ExteriorPrime K S) (m : ℕ) :
    ∃ U : (S.integer K)ˣ,
      poissonFrequency K S P u (exteriorPower K S (exteriorPrimeIdeal K S p) m) =
        (U : S.integer K) ^ 6 *
          (primeGenerator K S P.arithmetic p ^ (primeExponents u.ideal.val p.val + 6 * m) *
            rowUnitPart K S P u p) := by
  obtain ⟨v, hv⟩ := frequencyRowElement_eq_prime_power_unitPart K S P hP u p
  obtain ⟨w, hw⟩ := generator_power_eq_sixth_unit K S P.arithmetic hP
    (exteriorPrimeIdeal K S p) m
  refine ⟨S.unitEquivUnitsInteger K v * (S.unitEquivUnitsInteger K w) ^ 6, ?_⟩
  unfold poissonFrequency
  rw [hv, hw]
  have hp : primeGenerator K S P.arithmetic p ^ (primeExponents u.ideal.val p.val + 6 * m) =
      primeGenerator K S P.arithmetic p ^ primeExponents u.ideal.val p.val *
        (primeGenerator K S P.arithmetic p ^ m) ^ 6 := by
    rw [pow_add, Nat.mul_comm 6 m, pow_mul]
  rw [hp]
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, rowUnitPart, primeGenerator]
  ring

/-- This removes the actual generator correction in the original F,
with no assumption on the row sector or on the base frequency. -/
theorem finitePoisson_primeBlock_frequency (P : ProbeData K S)
    (hP : AllowedGeneratorInput K S P.arithmetic)
    (u : FrequencyRow K S) (p : ExteriorPrime K S) (t k m : ℕ) :
    finitePoissonFactor K S P (exteriorPower K S (exteriorPrimeIdeal K S p) k)
        (exteriorPower K S (exteriorPrimeIdeal K S p) t)
        (poissonFrequency K S P u (exteriorPower K S (exteriorPrimeIdeal K S p) m)) =
      finitePoissonFactor K S P (exteriorPower K S (exteriorPrimeIdeal K S p) k)
        (exteriorPower K S (exteriorPrimeIdeal K S p) t)
        (primeGenerator K S P.arithmetic p ^ (primeExponents u.ideal.val p.val + 6 * m) *
          rowUnitPart K S P u p) := by
  obtain ⟨U, hU⟩ := poissonFrequency_primePower_sixth_unit K S P hP u p m
  rw [hU]
  exact finitePoissonFactor_frequency_sixth_unit K S P _ _ U _
    (U.isUnit.map (Ideal.Quotient.mk _))

/-- The positive completed-index convolution with the exact actual row phase. -/
theorem finitePoisson_primeBlock_positive (P : ProbeData K S)
    (hP : AllowedGeneratorInput K S P.arithmetic)
    (u : FrequencyRow K S) (p : ExteriorPrime K S) (t k m : ℕ) (ht : 1 ≤ t) :
    finitePoissonFactor K S P (exteriorPower K S (exteriorPrimeIdeal K S p) k)
        (exteriorPower K S (exteriorPrimeIdeal K S p) t)
        (poissonFrequency K S P u (exteriorPower K S (exteriorPrimeIdeal K S p) m)) =
      positiveConvolution p.val.asIdeal.absNorm
        (HighBin.ActualGaussPhases.gaussFamily (thetaPrimeCharacter K S P.arithmetic p)
          (primeAddCharacter K S P.arithmetic p))
        (thetaPrimeCharacter K S P.arithmetic p (rowPrimeUnit K S P u p))
        t k (primeExponents u.ideal.val p.val + 6 * m) := by
  rw [finitePoisson_primeBlock_frequency K S P hP u p t k m,
    finitePoisson_primePowers_eq_positiveConvolution K S P hP p t k ht
      (rowUnitPart K S P u p) (rowUnitPart_not_dvd K S P u p), rowUnitPart_residue]

theorem finitePoisson_primeBlock_completedUnit (P : ProbeData K S)
    (hP : AllowedGeneratorInput K S P.arithmetic)
    (u : FrequencyRow K S) (p : ExteriorPrime K S) (k m : ℕ) :
    finitePoissonFactor K S P (exteriorPower K S (exteriorPrimeIdeal K S p) k)
        (exteriorPower K S (exteriorPrimeIdeal K S p) 0)
        (poissonFrequency K S P u (exteriorPower K S (exteriorPrimeIdeal K S p) m)) =
      if k = 0 then 1 else if primeExponents u.ideal.val p.val + 6 * m = 0 then
        thetaPrimeCharacter K S P.arithmetic p (rowPrimeUnit K S P u p) ^ k else 0 := by
  rw [finitePoisson_primeBlock_frequency K S P hP u p 0 k m,
    finitePoisson_primePowers_completedUnit K S P hP p k _
      (rowUnitPart K S P u p) (rowUnitPart_not_dvd K S P u p), rowUnitPart_residue]

/-- No branch of the completed cube index is dropped. -/
theorem completedIdeal_primePowers (p : ExteriorPrime K S) (e l : ℕ) :
    completedIdeal K S (exteriorPower K S (exteriorPrimeIdeal K S p) e)
        (exteriorPower K S (exteriorPrimeIdeal K S p) l) =
      exteriorPower K S (exteriorPrimeIdeal K S p) (e + 3 * l) := by
  apply Subtype.ext
  change (exteriorPrimeIdeal K S p).val ^ e *
      ((exteriorPrimeIdeal K S p).val ^ l *
        ((exteriorPrimeIdeal K S p).val ^ l * (exteriorPrimeIdeal K S p).val ^ l)) =
      (exteriorPrimeIdeal K S p).val ^ (e + 3 * l)
  rw [← pow_add, ← pow_add, ← pow_add]
  congr 1
  omega

/-- Positive real ideal norms make powers commute with complex powers. -/
theorem exteriorPower_norm_cpow (I : ExteriorIdeal K S) (n : ℕ) (z : ℂ) :
    (exteriorNorm K S (exteriorPower K S I n) : ℂ) ^ z =
      ((exteriorNorm K S I : ℂ) ^ z) ^ n := by
  induction n with
  | zero => simp [exteriorNorm, exteriorPower]
  | succ n ih => rw [exteriorPower_succ, exteriorNorm_cpow_mul, ih, pow_succ]

theorem primePower_heckeCoefficient (χ : HeckeCharacter K)
    (p : ExteriorPrime K S) (n : ℕ) :
    heckeIdealCoefficient K χ (exteriorPower K S (exteriorPrimeIdeal K S p) n).val =
      primeCoefficient K χ p.val ^ n :=
  idealCoefficient_prime_pow (primeCoefficient K χ) p.val n

theorem squarefree_primePower_iff (p : ExteriorPrime K S) (e : ℕ) :
    Squarefree (exteriorPower K S (exteriorPrimeIdeal K S p) e).val.val ↔ e ≤ 1 := by
  change Squarefree (p.val.asIdeal ^ e) ↔ e ≤ 1
  constructor
  · intro hs
    rcases hs.eq_zero_or_one_of_pow_of_not_isUnit p.val.irreducible.not_isUnit with h | h <;> omega
  · intro he
    have h : e = 0 ∨ e = 1 := by omega
    rcases h with rfl | rfl
    · simpa only [pow_zero] using (squarefree_one : Squarefree (1 : Ideal (𝓞 K)))
    · simpa only [pow_one] using p.val.irreducible.squarefree

/-- The real square-root identity with the actual complex-power convention. -/
theorem positive_cpow_neg_half (q : ℝ) (hq : 0 < q) :
    (q : ℂ) ^ (-(1 / 2 : ℂ)) = (Real.sqrt q : ℂ)⁻¹ := by
  rw [Complex.cpow_neg]
  congr 1
  have h := Complex.ofReal_cpow hq.le (1 / 2 : ℝ)
  rw [← Real.sqrt_eq_rpow] at h
  simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using h.symm

/-- The c-part normalization is G₂/q at e=1, and one at e=0. -/
theorem thetaGamma_primePower_weight (D : ThetaArithmeticData K S)
    (p : ExteriorPrime K S) (s : ℂ) (e : ℕ) (he : e ≤ 1) :
    thetaGamma K S D (exteriorPower K S (exteriorPrimeIdeal K S p) e) 2 *
      (exteriorNorm K S (exteriorPower K S (exteriorPrimeIdeal K S p) e) : ℂ) ^
        (-(1 / 2 : ℂ) - s) =
      (HighBin.ActualGaussPhases.gaussFamily (thetaPrimeCharacter K S D p)
          (primeAddCharacter K S D p) 2 / (p.val.asIdeal.absNorm : ℂ)) ^ e *
        ((p.val.asIdeal.absNorm : ℂ) ^ (-s)) ^ e := by
  have hq : (0 : ℝ) < p.val.asIdeal.absNorm := by
    exact_mod_cast (Nat.zero_lt_one.trans (NumberField.HeightOneSpectrum.one_lt_absNorm p.val))
  have hqC : (p.val.asIdeal.absNorm : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hcases : e = 0 ∨ e = 1 := by omega
  rcases hcases with rfl | rfl
  · rw [thetaGamma_unit_ideal K S D _ (by simp [exteriorPower])]
    simp [exteriorNorm, exteriorPower]
  · rw [exteriorPower_one]
    simp only [pow_one]
    have hΓ := normalizedFamily_eq_thetaGamma K S D p 2 (by decide)
    unfold HighBin.ActualGaussPhases.normalizedFamily HighBin.FiniteResidueFourier.normalizedGauss at hΓ
    rw [AlgebraicNumberTheory.PowerResidueSymbols.card_primeIdealResidueField] at hΓ
    change HighBin.ActualGaussPhases.gaussFamily (thetaPrimeCharacter K S D p)
      (primeAddCharacter K S D p) 2 / (Real.sqrt (p.val.asIdeal.absNorm : ℝ) : ℂ) =
        thetaGamma K S D (exteriorPrimeIdeal K S p) 2 at hΓ
    rw [← hΓ]
    change _ * (p.val.asIdeal.absNorm : ℂ) ^ (-(1 / 2 : ℂ) - s) = _
    rw [sub_eq_add_neg, Complex.cpow_add _ _ hqC, positive_cpow_neg_half _ hq]
    have hs : (Real.sqrt (p.val.asIdeal.absNorm : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hq).ne'
    have hs2 : (Real.sqrt (p.val.asIdeal.absNorm : ℝ) : ℂ) ^ 2 =
        (p.val.asIdeal.absNorm : ℂ) := by exact_mod_cast Real.sq_sqrt hq.le
    rw [← hs2]
    field_simp [hs]
    <;> ring

/-- The completed cube weight is q^-l X^(3l), with X=q^-s. -/
theorem primePower_cube_weight (p : ExteriorPrime K S) (s : ℂ) (l : ℕ) :
    (exteriorNorm K S (exteriorPower K S (exteriorPrimeIdeal K S p) l) : ℂ) ^ (-1 - 3 * s) =
      ((p.val.asIdeal.absNorm : ℂ) ^ l)⁻¹ *
        ((p.val.asIdeal.absNorm : ℂ) ^ (-s)) ^ (3 * l) := by
  rw [exteriorPower_norm_cpow]
  have hq : (p.val.asIdeal.absNorm : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_one.trans
      (NumberField.HeightOneSpectrum.one_lt_absNorm p.val)))
  change ((p.val.asIdeal.absNorm : ℂ) ^ (-1 - 3 * s)) ^ l = _
  have he : (-1 - 3 * s : ℂ) = -1 + ((3 : ℕ) : ℂ) * (-s) := by push_cast; ring
  rw [he, Complex.cpow_add _ _ hq, Complex.cpow_neg_one, Complex.cpow_nat_mul,
    mul_pow, inv_pow, ← pow_mul]

/-- The scalar weight in the local table is exactly the original theta
normalization, Hecke coefficient, and all four norm powers. -/
theorem primeBlockWeight_eq (P : ProbeData K S) (ψ : HeckeCharacter K)
    (s w z : ℂ) (p : ExteriorPrime K S) (e l k m : ℕ) (he : e ≤ 1) :
    thetaGamma K S P.arithmetic (exteriorPower K S (exteriorPrimeIdeal K S p) e) 2 *
      rowEulerWeight K S P ψ s w z (primeFourIdealIndex K S p ((e, l), (k, m))) =
      (HighBin.ActualGaussPhases.gaussFamily (thetaPrimeCharacter K S P.arithmetic p)
          (primeAddCharacter K S P.arithmetic p) 2 / (p.val.asIdeal.absNorm : ℂ)) ^ e *
      primeCoefficient K (thetaPeriod K S P ψ) p.val ^ (e + 3 * l) /
        (p.val.asIdeal.absNorm : ℂ) ^ l *
      ((p.val.asIdeal.absNorm : ℂ) ^ (-s)) ^ (e + 3 * l) *
      ((p.val.asIdeal.absNorm : ℂ) ^ (-w)) ^ k *
      ((p.val.asIdeal.absNorm : ℂ) ^ (-6 * z)) ^ m := by
  have hcoef : heckeIdealCoefficient K (thetaPeriod K S P ψ)
      (completedIdeal K S (exteriorPower K S (exteriorPrimeIdeal K S p) e)
        (exteriorPower K S (exteriorPrimeIdeal K S p) l)).val =
      primeCoefficient K (thetaPeriod K S P ψ) p.val ^ (e + 3 * l) := by
    rw [completedIdeal_primePowers]
    exact primePower_heckeCoefficient K S _ p _
  simp only [rowEulerWeight, primeFourIdealIndex]
  calc
    _ = (thetaGamma K S P.arithmetic (exteriorPower K S (exteriorPrimeIdeal K S p) e) 2 *
        (exteriorNorm K S (exteriorPower K S (exteriorPrimeIdeal K S p) e) : ℂ) ^
          (-(1 / 2 : ℂ) - s)) *
      heckeIdealCoefficient K (thetaPeriod K S P ψ)
        (completedIdeal K S (exteriorPower K S (exteriorPrimeIdeal K S p) e)
          (exteriorPower K S (exteriorPrimeIdeal K S p) l)).val *
      (exteriorNorm K S (exteriorPower K S (exteriorPrimeIdeal K S p) l) : ℂ) ^ (-1 - 3 * s) *
      (exteriorNorm K S (exteriorPower K S (exteriorPrimeIdeal K S p) k) : ℂ) ^ (-w) *
      (exteriorNorm K S (exteriorPower K S (exteriorPrimeIdeal K S p) m) : ℂ) ^ (-6 * z) := by ring
    _ = _ := by
      rw [thetaGamma_primePower_weight K S P.arithmetic p s e he, hcoef,
        primePower_cube_weight, exteriorPower_norm_cpow, exteriorPower_norm_cpow]
      change _ = _
      simp only [exteriorNorm, exteriorPrimeIdeal, pow_add]
      ring

/-- The original prime-block term equals the actual positive local table. -/
theorem primeBlockBase_positive (P : ProbeData K S)
    (hP : AllowedGeneratorInput K S P.arithmetic) (ψ : HeckeCharacter K)
    (u : FrequencyRow K S) (s w z : ℂ) (p : ExteriorPrime K S)
    (e l k m : ℕ) (he : e ≤ 1) (ht : 1 ≤ e + 3 * l) :
    primeBlockBase K S P ψ u s w z p ((e, l), (k, m)) =
      weightedTerm p.val.asIdeal.absNorm (primeCoefficient K (thetaPeriod K S P ψ) p.val)
        (HighBin.ActualGaussPhases.gaussFamily (thetaPrimeCharacter K S P.arithmetic p)
          (primeAddCharacter K S P.arithmetic p))
        (thetaPrimeCharacter K S P.arithmetic p (rowPrimeUnit K S P u p))
        ((p.val.asIdeal.absNorm : ℂ) ^ (-s)) ((p.val.asIdeal.absNorm : ℂ) ^ (-w))
        ((p.val.asIdeal.absNorm : ℂ) ^ (-6 * z))
        (primeExponents u.ideal.val p.val) e l k m := by
  have hsq : Squarefree (primeFourIdealIndex K S p ((e, l), (k, m))).1.1.val.val :=
    (squarefree_primePower_iff K S p e).mpr he
  rw [primeBlockBase, initialRowEulerTerm_empty, if_pos hsq, rowEulerUnmaskedTerm]
  calc
    _ = (thetaGamma K S P.arithmetic (exteriorPower K S (exteriorPrimeIdeal K S p) e) 2 *
        rowEulerWeight K S P ψ s w z (primeFourIdealIndex K S p ((e, l), (k, m)))) *
      finitePoissonFactor K S P (exteriorPower K S (exteriorPrimeIdeal K S p) k)
        (completedIdeal K S (exteriorPower K S (exteriorPrimeIdeal K S p) e)
          (exteriorPower K S (exteriorPrimeIdeal K S p) l))
        (poissonFrequency K S P u (exteriorPower K S (exteriorPrimeIdeal K S p) m)) := by
      simp only [primeFourIdealIndex]
      ring
    _ = _ := by
      rw [primeBlockWeight_eq K S P ψ s w z p e l k m he, completedIdeal_primePowers,
        finitePoisson_primeBlock_positive K S P hP u p (e + 3 * l) k m ht]
      rfl

/-- The completed-unit row has the literal denominator-symbol zero mask. -/
theorem primeBlockBase_completedUnit (P : ProbeData K S)
    (hP : AllowedGeneratorInput K S P.arithmetic) (ψ : HeckeCharacter K)
    (u : FrequencyRow K S) (s w z : ℂ) (p : ExteriorPrime K S) (k m : ℕ) :
    primeBlockBase K S P ψ u s w z p ((0, 0), (k, m)) =
      ((p.val.asIdeal.absNorm : ℂ) ^ (-w)) ^ k *
        ((p.val.asIdeal.absNorm : ℂ) ^ (-6 * z)) ^ m *
      (if k = 0 then 1 else if primeExponents u.ideal.val p.val + 6 * m = 0 then
        thetaPrimeCharacter K S P.arithmetic p (rowPrimeUnit K S P u p) ^ k else 0) := by
  have hsq : Squarefree (primeFourIdealIndex K S p ((0, 0), (k, m))).1.1.val.val :=
    (squarefree_primePower_iff K S p 0).mpr (by omega)
  rw [primeBlockBase, initialRowEulerTerm_empty, if_pos hsq, rowEulerUnmaskedTerm]
  calc
    _ = (thetaGamma K S P.arithmetic (exteriorPower K S (exteriorPrimeIdeal K S p) 0) 2 *
        rowEulerWeight K S P ψ s w z (primeFourIdealIndex K S p ((0, 0), (k, m)))) *
      finitePoissonFactor K S P (exteriorPower K S (exteriorPrimeIdeal K S p) k)
        (completedIdeal K S (exteriorPower K S (exteriorPrimeIdeal K S p) 0)
          (exteriorPower K S (exteriorPrimeIdeal K S p) 0))
        (poissonFrequency K S P u (exteriorPower K S (exteriorPrimeIdeal K S p) m)) := by
      simp only [primeFourIdealIndex]
      ring
    _ = _ := by
      rw [primeBlockWeight_eq K S P ψ s w z p 0 0 k m (by omega), completedIdeal_primePowers]
      simp only [Nat.mul_zero, Nat.zero_add, pow_zero, div_one, mul_one, one_mul]
      rw [finitePoisson_primeBlock_completedUnit K S P hP u p k m]

/-- Higher c-exponents vanish by the original squarefree condition. -/
theorem primeBlockBase_zero_of_two_le (P : ProbeData K S) (ψ : HeckeCharacter K)
    (u : FrequencyRow K S) (s w z : ℂ) (p : ExteriorPrime K S)
    (e l k m : ℕ) (he : 2 ≤ e) :
    primeBlockBase K S P ψ u s w z p ((e, l), (k, m)) = 0 := by
  rw [primeBlockBase, initialRowEulerTerm_empty]
  apply if_neg
  intro hsq
  have he' := (squarefree_primePower_iff K S p e).mp hsq
  omega

/-- Uniform local identification of the original prime block, with the
unit row and every zero branch included. -/
theorem primeBlockBase_eq_localBlockValue (P : ProbeData K S)
    (hP : AllowedGeneratorInput K S P.arithmetic) (ψ : HeckeCharacter K)
    (u : FrequencyRow K S) (s w z : ℂ) (p : ExteriorPrime K S) (n : FourExponent) :
    primeBlockBase K S P ψ u s w z p n =
      localBlockValue p.val.asIdeal.absNorm (primeCoefficient K (thetaPeriod K S P ψ) p.val)
        (HighBin.ActualGaussPhases.gaussFamily (thetaPrimeCharacter K S P.arithmetic p)
          (primeAddCharacter K S P.arithmetic p))
        (thetaPrimeCharacter K S P.arithmetic p (rowPrimeUnit K S P u p))
        ((p.val.asIdeal.absNorm : ℂ) ^ (-s)) ((p.val.asIdeal.absNorm : ℂ) ^ (-w))
        ((p.val.asIdeal.absNorm : ℂ) ^ (-6 * z))
        (primeExponents u.ideal.val p.val) n := by
  rcases n with ⟨⟨e, l⟩, ⟨k, m⟩⟩
  by_cases he : e ≤ 1
  · by_cases ht : e + 3 * l = 0
    · have he₀ : e = 0 := by omega
      have hl₀ : l = 0 := by omega
      subst e l
      rw [primeBlockBase_completedUnit K S P hP ψ u s w z p k m]
      simp only [localBlockValue, Nat.zero_le, Nat.zero_add, Nat.mul_zero,
        zero_le_one, if_true]
    · rw [primeBlockBase_positive K S P hP ψ u s w z p e l k m he (by omega)]
      simp only [localBlockValue, he, ht, if_true, if_false]
  · rw [primeBlockBase_zero_of_two_le K S P ψ u s w z p e l k m (by omega)]
    simp only [localBlockValue, he, if_false]

/-- Actual marked prime blocks delete precisely the completed-unit row. -/
theorem primeBlockTerm_eq_localBlockValue (P : ProbeData K S)
    (hP : AllowedGeneratorInput K S P.arithmetic) (ψ : HeckeCharacter K)
    (Q : Finset (ExteriorPrime K S)) (u : FrequencyRow K S) (s w z : ℂ)
    (p : ExteriorPrime K S) (n : FourExponent) :
    primeBlockTerm K S P ψ Q u s w z p n =
      if p ∈ Q ∧ n.1.1 + 3 * n.1.2 = 0 then 0 else
        localBlockValue p.val.asIdeal.absNorm (primeCoefficient K (thetaPeriod K S P ψ) p.val)
          (HighBin.ActualGaussPhases.gaussFamily (thetaPrimeCharacter K S P.arithmetic p)
            (primeAddCharacter K S P.arithmetic p))
          (thetaPrimeCharacter K S P.arithmetic p (rowPrimeUnit K S P u p))
          ((p.val.asIdeal.absNorm : ℂ) ^ (-s)) ((p.val.asIdeal.absNorm : ℂ) ^ (-w))
          ((p.val.asIdeal.absNorm : ℂ) ^ (-6 * z))
          (primeExponents u.ideal.val p.val) n := by
  rw [primeBlockTerm, primeBlockBase_eq_localBlockValue K S P hP]

#print axioms finitePoisson_primeBlock_positive
#print axioms finitePoisson_primeBlock_completedUnit
#print axioms thetaGamma_primePower_weight
#print axioms primeBlockBase_eq_localBlockValue
#print axioms primeBlockTerm_eq_localBlockValue
end HeckeSkeleton.HighBinActualInitial
