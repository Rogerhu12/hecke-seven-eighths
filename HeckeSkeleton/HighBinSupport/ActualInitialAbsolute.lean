import HeckeGeneral.Analysis.PhysicalProbeRows
import HeckeGeneral.Analysis.IdealSummability
import Mathlib.Analysis.Normed.Ring.Finite
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
/-!
# Initial absolute convergence of the literal four-ideal Fourier series

PROJECT ADAPTER: this file references the actual project definitions. It is
not part of the Mathlib-only verified chain until its missing external project
imports are restored and this file is compiled. Every assertion has a proof
body; there are no admissions and no Euler-identity hypothesis.

The elementary theta-Gauss cardinality argument is adapted from the supplied
(uncompiled) `HeckeSkeleton/ActualProbeThetaAbsolute.lean`; the two-layer
finitePoisson estimate and the four-ideal summability are new here.

AI-assisted: ChatGPT / GPT-6 Astra Pro, 2026-10-30.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.HighBinActualAbsolute

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.Physical
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

def quotientSymbol (D : ThetaArithmeticData K S) (I : ExteriorIdeal K S) :
    ThetaQuotient K S I → ℂ :=
  sIntegerSexticIdealQuotientFunction K S D.root6 D.primitive6 D.embedding
    I.val.val (nonZeroDivisors.coe_ne_zero I.val) I.property
    (fun p hp => D.away_six p (I.property p hp))

theorem norm_quotientSymbol_le_one (D : ThetaArithmeticData K S)
    (I : ExteriorIdeal K S) (x : ThetaQuotient K S I) :
    ‖quotientSymbol K S D I x‖ ≤ 1 := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [quotientSymbol, sIntegerSexticIdealQuotientFunction_mk]
  exact norm_sIntegerSexticIdealEvaluation_le_one K S D.root6 D.primitive6 D.embedding
    I.val.val (nonZeroDivisors.coe_ne_zero I.val) I.property
    (fun p hp => D.away_six p (I.property p hp)) a

theorem quotient_card (I : ExteriorIdeal K S) [Fintype (ThetaQuotient K S I)] :
    Fintype.card (ThetaQuotient K S I) = I.val.val.absNorm := by
  simpa only [Nat.card_eq_fintype_card] using
    natCard_sIntegerResidue K S I.val.val (sexticIdeal_coprime_S K S I.val.val I.property)

/-- The literal denominator Gauss sum is bounded by its quotient size. -/
theorem norm_probeGauss_le_norm (P : ProbeData K S)
    (I : ExteriorIdeal K S) (k : S.integer K) :
    ‖probeGauss K S P I k‖ ≤ exteriorNorm K S I := by
  letI : Finite (ThetaQuotient K S I) := finite_sIntegerSexticIdealQuotient K S
    I.val.val (nonZeroDivisors.coe_ne_zero I.val) I.property
  letI : Fintype (ThetaQuotient K S I) := Fintype.ofFinite _
  change ‖∑ d : ThetaQuotient K S I,
    quotientSymbol K S P.arithmetic I d * thetaPrincipalAddCharacter K S P.arithmetic I
      ((Ideal.Quotient.mk _ k) * d)‖ ≤ _
  calc
    _ ≤ ∑ d : ThetaQuotient K S I,
      ‖quotientSymbol K S P.arithmetic I d * thetaPrincipalAddCharacter K S P.arithmetic I
        ((Ideal.Quotient.mk _ k) * d)‖ := norm_sum_le _ _
    _ ≤ ∑ _d : ThetaQuotient K S I, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro d _
      rw [norm_mul, AddChar.norm_apply, mul_one]
      exact norm_quotientSymbol_le_one K S P.arithmetic I d
    _ = exteriorNorm K S I := by simp [quotient_card K S I, exteriorNorm]

/-- The actual standard phase has modulus one at every principal fraction. -/
theorem norm_principal_fraction (D : ThetaArithmeticData K S)
    (c : S.integer K) (hc : c ≠ 0) (a : S.integer K) :
    ‖sLocalPrincipalPhase K S ((a : K) / (c : K))‖ = 1 := by
  letI : Finite (S.integer K ⧸ Ideal.span ({c} : Set (S.integer K))) :=
    finite_sIntegerPrincipalResidue K S c hc
  rw [← sIntegerActualModulusAddCharacter_mk K S D.different_outside c hc a]
  exact AddChar.norm_apply _ _

theorem exteriorNorm_mul (I J : ExteriorIdeal K S) :
    exteriorNorm K S (exteriorMul K S I J) = exteriorNorm K S I * exteriorNorm K S J := by
  simp only [exteriorNorm, exteriorMul, Submonoid.coe_mul, map_mul, Nat.cast_mul]

theorem exteriorNorm_completed (c n : ExteriorIdeal K S) :
    exteriorNorm K S (completedIdeal K S c n) =
      exteriorNorm K S c * exteriorNorm K S n ^ 3 := by
  simp only [completedIdeal, exteriorNorm_mul]
  ring

/-- Both finite sums are bounded directly, including intersecting d and A. -/
theorem norm_finitePoissonFactor_le (P : ProbeData K S)
    (den A : ExteriorIdeal K S) (h : S.integer K) :
    ‖finitePoissonFactor K S P den A h‖ ≤ exteriorNorm K S den * exteriorNorm K S A := by
  let B := exteriorMul K S den A
  letI : Finite (ThetaQuotient K S B) := finite_sIntegerSexticIdealQuotient K S
    B.val.val (nonZeroDivisors.coe_ne_zero B.val) B.property
  letI : Fintype (ThetaQuotient K S B) := Fintype.ofFinite _
  have hden : 0 < exteriorNorm K S den := idealNorm_pos K den.val
  have hB : (Fintype.card (ThetaQuotient K S B) : ℝ) =
      exteriorNorm K S den * exteriorNorm K S A := by
    rw [quotient_card K S B]
    exact exteriorNorm_mul K S den A
  have hphase (m : S.integer K) :
      ‖sLocalPrincipalPhase K S (((h : K) * (m : K)) /
        ((P.arithmetic.generator den : K) * (P.arithmetic.generator A : K)))‖ = 1 := by
    simpa only [map_mul] using norm_principal_fraction K S P.arithmetic
      (P.arithmetic.generator den * P.arithmetic.generator A)
      (mul_ne_zero (P.arithmetic.generator_ne_zero den) (P.arithmetic.generator_ne_zero A))
      (h * m)
  have hterm (m : S.integer K) :
      ‖probeGauss K S P den (-m) * idealSymbol K S P.arithmetic A m *
        sLocalPrincipalPhase K S (((h : K) * (m : K)) /
          ((P.arithmetic.generator den : K) * (P.arithmetic.generator A : K)))‖ ≤
        exteriorNorm K S den := by
    rw [norm_mul, norm_mul, hphase, mul_one]
    have hs : ‖idealSymbol K S P.arithmetic A m‖ ≤ 1 :=
      norm_sIntegerSexticIdealEvaluation_le_one K S P.arithmetic.root6
        P.arithmetic.primitive6 P.arithmetic.embedding A.val.val
        (nonZeroDivisors.coe_ne_zero A.val) A.property
        (fun p hp => P.arithmetic.away_six p (A.property p hp)) m
    exact (mul_le_mul (norm_probeGauss_le_norm K S P den (-m)) hs
      (norm_nonneg _) hden.le).trans_eq (mul_one _)
  change ‖(exteriorNorm K S den : ℂ)⁻¹ *
    ∑ x : ThetaQuotient K S B,
      probeGauss K S P den (-Quotient.out x) * idealSymbol K S P.arithmetic A (Quotient.out x) *
        sLocalPrincipalPhase K S (((h : K) * (Quotient.out x : S.integer K)) /
          ((P.arithmetic.generator den : K) * (P.arithmetic.generator A : K)))‖ ≤ _
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hden.le]
  calc
    _ ≤ (exteriorNorm K S den)⁻¹ *
        ∑ _x : ThetaQuotient K S B, exteriorNorm K S den := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hden.le)
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun x _ => hterm (Quotient.out x)))
    _ = exteriorNorm K S den * exteriorNorm K S A := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hB]
      field_simp [hden.ne'] <;> ring

/-- The normalization of Γ₂ saves exactly one half-power of N(c). -/
theorem norm_thetaGamma_two_le_sqrt (D : ThetaArithmeticData K S) (I : ExteriorIdeal K S) :
    ‖thetaGamma K S D I 2‖ ≤ Real.sqrt (exteriorNorm K S I) := by
  letI : Finite (ThetaQuotient K S I) := finite_sIntegerSexticIdealQuotient K S
    I.val.val (nonZeroDivisors.coe_ne_zero I.val) I.property
  letI : Fintype (ThetaQuotient K S I) := Fintype.ofFinite _
  have hsum : ‖∑ x : ThetaQuotient K S I,
      quotientSymbol K S D I x ^ 2 * thetaPrincipalAddCharacter K S D I x‖ ≤ exteriorNorm K S I := by
    calc
      _ ≤ ∑ x : ThetaQuotient K S I,
        ‖quotientSymbol K S D I x ^ 2 * thetaPrincipalAddCharacter K S D I x‖ := norm_sum_le _ _
      _ ≤ ∑ _x : ThetaQuotient K S I, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro x _
        rw [norm_mul, norm_pow, AddChar.norm_apply, mul_one]
        exact pow_le_one₀ (norm_nonneg _) (norm_quotientSymbol_le_one K S D I x)
      _ = exteriorNorm K S I := by simp [quotient_card K S I, exteriorNorm]
  have hN : 0 < exteriorNorm K S I := idealNorm_pos K I.val
  have hs := Real.sqrt_pos.mpr hN
  change ‖(Real.sqrt (exteriorNorm K S I) : ℂ)⁻¹ *
    ∑ x : ThetaQuotient K S I, quotientSymbol K S D I x ^ 2 *
      thetaPrincipalAddCharacter K S D I x‖ ≤ _
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  calc
    _ = ‖∑ x : ThetaQuotient K S I, quotientSymbol K S D I x ^ 2 *
        thetaPrincipalAddCharacter K S D I x‖ / Real.sqrt (exteriorNorm K S I) := by ring
    _ ≤ Real.sqrt (exteriorNorm K S I) := by
      apply (div_le_iff₀ hs).mpr
      nlinarith [Real.sq_sqrt hN.le]

/-- The literal denominator product is itself a generator of the product
ideal; no chosen-generator multiplicativity is needed at this step. -/
theorem product_generator_span (D : ThetaArithmeticData K S) (den A : ExteriorIdeal K S) :
    Ideal.span ({D.generator den * D.generator A} : Set (S.integer K)) =
      (exteriorMul K S den A).val.val.map (algebraMap (𝓞 K) (S.integer K)) := by
  rw [← Ideal.span_singleton_mul_span_singleton, D.generator_span, D.generator_span]
  simp only [exteriorMul, Submonoid.coe_mul, Ideal.map_mul]

/-- Actual character for the exact gen(d)gen(A) denominator occurring in F. -/
def productPrincipalCharacter (D : ThetaArithmeticData K S) (den A : ExteriorIdeal K S) :
    AddChar (ThetaQuotient K S (exteriorMul K S den A)) ℂ :=
  HeckeGeneral.Arithmetic.ResidueTraceCharacters.transportCharacter
    (Ideal.quotEquivOfEq (product_generator_span K S D den A).symm)
    (sIntegerActualModulusAddCharacter K S D.different_outside
      (D.generator den * D.generator A)
      (mul_ne_zero (D.generator_ne_zero den) (D.generator_ne_zero A)))

theorem productPrincipalCharacter_mk (D : ThetaArithmeticData K S)
    (den A : ExteriorIdeal K S) (m : S.integer K) :
    productPrincipalCharacter K S D den A (Ideal.Quotient.mk _ m) =
      sLocalPrincipalPhase K S ((m : K) / ((D.generator den : K) * (D.generator A : K))) := by
  unfold productPrincipalCharacter
  rw [HeckeGeneral.Arithmetic.ResidueTraceCharacters.transportCharacter_apply,
    Ideal.quotEquivOfEq_mk, sIntegerActualModulusAddCharacter_mk]
  simp only [map_mul]

theorem productPrincipalCharacter_isPrimitive (D : ThetaArithmeticData K S)
    (den A : ExteriorIdeal K S) : (productPrincipalCharacter K S D den A).IsPrimitive :=
  HeckeGeneral.Arithmetic.ResidueTraceCharacters.transportCharacter_isPrimitive _ _
    (sIntegerActualModulusAddCharacter_isPrimitive K S D.different_outside
      (D.generator den * D.generator A)
      (mul_ne_zero (D.generator_ne_zero den) (D.generator_ne_zero A)))

/-- Quotient projections exist even when den and A share prime factors. -/
def productQuotientLeft (den A : ExteriorIdeal K S) :
    ThetaQuotient K S (exteriorMul K S den A) →+* ThetaQuotient K S den :=
  Ideal.quotientMap _ (RingHom.id (S.integer K)) (by
    simpa only [Ideal.comap_id, exteriorMul, Submonoid.coe_mul] using
      Ideal.map_mono (f := algebraMap (𝓞 K) (S.integer K))
        (Ideal.mul_le_left : den.val.val * A.val.val ≤ den.val.val))

def productQuotientRight (den A : ExteriorIdeal K S) :
    ThetaQuotient K S (exteriorMul K S den A) →+* ThetaQuotient K S A :=
  Ideal.quotientMap _ (RingHom.id (S.integer K)) (by
    simpa only [Ideal.comap_id, exteriorMul, Submonoid.coe_mul] using
      Ideal.map_mono (f := algebraMap (𝓞 K) (S.integer K))
        (Ideal.mul_le_right : den.val.val * A.val.val ≤ A.val.val))

def probeGaussOnQuotient (P : ProbeData K S) (den : ExteriorIdeal K S)
    (k : ThetaQuotient K S den) : ℂ := by
  letI : Finite (ThetaQuotient K S den) := finite_sIntegerSexticIdealQuotient K S
    den.val.val (nonZeroDivisors.coe_ne_zero den.val) den.property
  letI : Fintype (ThetaQuotient K S den) := Fintype.ofFinite _
  exact ∑ d, quotientSymbol K S P.arithmetic den d *
    thetaPrincipalAddCharacter K S P.arithmetic den (k * d)

@[simp] theorem probeGaussOnQuotient_mk (P : ProbeData K S)
    (den : ExteriorIdeal K S) (k : S.integer K) :
    probeGaussOnQuotient K S P den (Ideal.Quotient.mk _ k) = probeGauss K S P den k := rfl

/-- The original summand is now a genuine function on the quotient. -/
def poissonKernelOnQuotient (P : ProbeData K S) (den A : ExteriorIdeal K S)
    (h : S.integer K) (x : ThetaQuotient K S (exteriorMul K S den A)) : ℂ :=
  probeGaussOnQuotient K S P den (-(productQuotientLeft K S den A x)) *
    quotientSymbol K S P.arithmetic A (productQuotientRight K S den A x) *
    productPrincipalCharacter K S P.arithmetic den A (Ideal.Quotient.mk _ h * x)

@[simp] theorem poissonKernelOnQuotient_mk (P : ProbeData K S)
    (den A : ExteriorIdeal K S) (h m : S.integer K) :
    poissonKernelOnQuotient K S P den A h (Ideal.Quotient.mk _ m) =
      probeGauss K S P den (-m) * idealSymbol K S P.arithmetic A m *
        sLocalPrincipalPhase K S (((h : K) * (m : K)) /
          ((P.arithmetic.generator den : K) * (P.arithmetic.generator A : K))) := by
  unfold poissonKernelOnQuotient productQuotientLeft productQuotientRight
  rw [Ideal.quotientMap_mk, Ideal.quotientMap_mk]
  simp only [RingHom.id_apply, ← map_neg, probeGaussOnQuotient_mk,
    quotientSymbol, sIntegerSexticIdealQuotientFunction_mk]
  rw [← map_mul, productPrincipalCharacter_mk]
  simp only [map_mul, idealSymbol]

/-- Any two representatives of a product-ideal residue give the same
literal finite Poisson summand, with no coprimality assumption. -/
theorem finitePoisson_summand_representative_independent (P : ProbeData K S)
    (den A : ExteriorIdeal K S) (h m n : S.integer K)
    (hmn : Ideal.Quotient.mk ((exteriorMul K S den A).val.val.map
      (algebraMap (𝓞 K) (S.integer K))) m = Ideal.Quotient.mk _ n) :
    probeGauss K S P den (-m) * idealSymbol K S P.arithmetic A m *
      sLocalPrincipalPhase K S (((h : K) * (m : K)) /
        ((P.arithmetic.generator den : K) * (P.arithmetic.generator A : K))) =
    probeGauss K S P den (-n) * idealSymbol K S P.arithmetic A n *
      sLocalPrincipalPhase K S (((h : K) * (n : K)) /
        ((P.arithmetic.generator den : K) * (P.arithmetic.generator A : K))) := by
  rw [← poissonKernelOnQuotient_mk, ← poissonKernelOnQuotient_mk, hmn]

/-- A generator power gives the literal principal quotient for the ideal
power. This statement does not identify the separately chosen generator of
that power and therefore does not discard its possible sixth-unit factor. -/
theorem generator_power_span (D : ThetaArithmeticData K S)
    (I : ExteriorIdeal K S) (n : ℕ) :
    Ideal.span ({D.generator I ^ n} : Set (S.integer K)) =
      (I.val.val ^ n).map (algebraMap (𝓞 K) (S.integer K)) := by
  rw [← Ideal.span_singleton_pow, D.generator_span, Ideal.map_pow]

/-- Actual prime-power additive-character compatibility: the same literal
S-local phase appears at every level, so the descended character is the
specified level-one character, not an unspecified primitive character. -/
theorem principalPower_character_compatible (D : ThetaArithmeticData K S)
    (π : S.integer K) (hπ : π ≠ 0) (n : ℕ) (hn : 1 ≤ n) (x : S.integer K) :
    sIntegerActualModulusAddCharacter K S D.different_outside (π ^ n)
        (pow_ne_zero n hπ)
        (Ideal.Quotient.mk (Ideal.span ({π ^ n} : Set (S.integer K)))
          (π ^ (n - 1) * x)) =
      sIntegerActualModulusAddCharacter K S D.different_outside π hπ
        (Ideal.Quotient.mk (Ideal.span ({π} : Set (S.integer K))) x) := by
  rw [sIntegerActualModulusAddCharacter_mk, sIntegerActualModulusAddCharacter_mk]
  apply congrArg (sLocalPrincipalPhase K S)
  have hπK : (π : K) ≠ 0 := by
    intro h
    apply hπ
    exact Subtype.ext h
  simp only [map_mul, map_pow]
  have hp : (π : K) ^ n = (π : K) ^ (n - 1) * (π : K) := by
    rw [← pow_succ, Nat.sub_add_cancel hn]
  rw [hp]
  field_simp [hπK, pow_ne_zero (n - 1) hπK] <;> ring

/-- The exact product majorant retains all four original ideal variables. -/
def initialMajorant (σ ν ζ : ℝ) (I : FourIdealIndex K S) : ℝ :=
  (exteriorNorm K S I.1.1) ^ (1 - σ) * (exteriorNorm K S I.1.2) ^ (2 - 3 * σ) *
    (exteriorNorm K S I.2.1) ^ (1 - ν) * (exteriorNorm K S I.2.2) ^ (-6 * ζ)

lemma initialMajorant_nonneg (σ ν ζ : ℝ) (I : FourIdealIndex K S) :
    0 ≤ initialMajorant K S σ ν ζ I := by
  unfold initialMajorant
  exact mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg (idealNorm_pos K _).le _)
    (Real.rpow_nonneg (idealNorm_pos K _).le _))
    (Real.rpow_nonneg (idealNorm_pos K _).le _)) (Real.rpow_nonneg (idealNorm_pos K _).le _)

private lemma sqrt_mul_rpow (x σ : ℝ) (hx : 0 < x) :
    Real.sqrt x * x * x ^ (-(1 / 2 : ℝ) - σ) = x ^ (1 - σ) := by
  calc
    _ = x ^ (1 / 2 : ℝ) * x ^ (1 : ℝ) * x ^ (-(1 / 2 : ℝ) - σ) := by
      rw [Real.rpow_one, Real.sqrt_eq_rpow]
    _ = x ^ (((1 / 2 : ℝ) + 1) + (-(1 / 2 : ℝ) - σ)) := by
      rw [← Real.rpow_add hx, ← Real.rpow_add hx]
    _ = _ := by congr 1; ring

private lemma cube_mul_rpow (x σ : ℝ) (hx : 0 < x) :
    x ^ 3 * x ^ (-1 - 3 * σ) = x ^ (2 - 3 * σ) := by
  rw [← Real.rpow_natCast x 3, ← Real.rpow_add hx]
  congr 1
  norm_num <;> ring

private lemma one_mul_rpow (x ν : ℝ) (hx : 0 < x) :
    x * x ^ (-ν) = x ^ (1 - ν) := by
  calc
    _ = x ^ (1 : ℝ) * x ^ (-ν) := by rw [Real.rpow_one]
    _ = x ^ ((1 : ℝ) + -ν) := by rw [← Real.rpow_add hx]
    _ = _ := by congr 1; ring

/-- A pointwise estimate for the literal original coefficient, before any
local calibration, CRT factorization, or Euler product theorem. -/
theorem norm_initialRowEulerTerm_le (P : ProbeData K S) (ψ : HeckeCharacter K)
    (Q : Finset (ExteriorPrime K S)) (u : FrequencyRow K S) (s w z : ℂ)
    (I : FourIdealIndex K S) :
    ‖initialRowEulerTerm K S P ψ Q u s w z I‖ ≤ initialMajorant K S s.re w.re z.re I := by
  let c := I.1.1
  let n := I.1.2
  let den := I.2.1
  let r := I.2.2
  have hc : 0 < exteriorNorm K S c := idealNorm_pos K c.val
  have hn : 0 < exteriorNorm K S n := idealNorm_pos K n.val
  have hd : 0 < exteriorNorm K S den := idealNorm_pos K den.val
  have hr : 0 < exteriorNorm K S r := idealNorm_pos K r.val
  have hcoef :
      ‖thetaGamma K S P.arithmetic c 2 *
        heckeIdealCoefficient K (thetaPeriod K S P ψ) (completedIdeal K S c n).val *
        finitePoissonFactor K S P den (completedIdeal K S c n) (poissonFrequency K S P u r)‖ ≤
      Real.sqrt (exteriorNorm K S c) *
        (exteriorNorm K S den * (exteriorNorm K S c * exteriorNorm K S n ^ 3)) := by
    rw [norm_mul, norm_mul]
    have hF := norm_finitePoissonFactor_le K S P den (completedIdeal K S c n)
      (poissonFrequency K S P u r)
    rw [exteriorNorm_completed] at hF
    have hh := mul_le_mul
      (mul_le_mul (norm_thetaGamma_two_le_sqrt K S P.arithmetic c)
        (norm_heckeIdealCoefficient_le_one K (thetaPeriod K S P ψ) _)
        (norm_nonneg _) (Real.sqrt_nonneg _)) hF (norm_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg _) zero_le_one)
    simpa only [mul_one] using hh
  have hp1 : ‖(exteriorNorm K S c : ℂ) ^ (-(1 / 2 : ℂ) - s)‖ =
      (exteriorNorm K S c) ^ (-(1 / 2 : ℝ) - s.re) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hc]
    congr 1
    norm_num
  have hp2 : ‖(exteriorNorm K S n : ℂ) ^ (-1 - 3 * s)‖ =
      (exteriorNorm K S n) ^ (-1 - 3 * s.re) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hn]
    congr 1
    simp [Complex.mul_re]
  have hp3 : ‖(exteriorNorm K S den : ℂ) ^ (-w)‖ = (exteriorNorm K S den) ^ (-w.re) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hd, Complex.neg_re]
  have hp4 : ‖(exteriorNorm K S r : ℂ) ^ (-6 * z)‖ = (exteriorNorm K S r) ^ (-6 * z.re) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hr]
    congr 1
    simp [Complex.mul_re]
  unfold initialRowEulerTerm
  dsimp only
  split_ifs with hmask
  · change ‖(thetaGamma K S P.arithmetic c 2 *
      heckeIdealCoefficient K (thetaPeriod K S P ψ) (completedIdeal K S c n).val *
      finitePoissonFactor K S P den (completedIdeal K S c n) (poissonFrequency K S P u r)) *
      (exteriorNorm K S c : ℂ) ^ (-(1 / 2 : ℂ) - s) *
      (exteriorNorm K S n : ℂ) ^ (-1 - 3 * s) *
      (exteriorNorm K S den : ℂ) ^ (-w) * (exteriorNorm K S r : ℂ) ^ (-6 * z)‖ ≤ _
    rw [norm_mul, norm_mul, norm_mul, norm_mul, hp1, hp2, hp3, hp4]
    have hb := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg hc.le _))
          (Real.rpow_nonneg hn.le _)) (Real.rpow_nonneg hd.le _)) (Real.rpow_nonneg hr.le _)
    apply hb.trans_eq
    calc
      _ = (Real.sqrt (exteriorNorm K S c) * exteriorNorm K S c *
          (exteriorNorm K S c) ^ (-(1 / 2 : ℝ) - s.re)) *
          (exteriorNorm K S n ^ 3 * (exteriorNorm K S n) ^ (-1 - 3 * s.re)) *
          (exteriorNorm K S den * (exteriorNorm K S den) ^ (-w.re)) *
          (exteriorNorm K S r) ^ (-6 * z.re) := by ring
      _ = initialMajorant K S s.re w.re z.re I := by
        rw [sqrt_mul_rpow _ _ hc, cube_mul_rpow _ _ hn, one_mul_rpow _ _ hd]
        rfl
  · rw [norm_zero]
    exact initialMajorant_nonneg K S s.re w.re z.re I

theorem summable_exterior_power {t : ℝ} (ht : t < -1) :
    Summable (fun I : ExteriorIdeal K S => exteriorNorm K S I ^ t) := by
  have hh := (summable_nonzeroIdeal_norm_rpow K (σ := -t) (by linarith)).subtype
    (fun I => ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I.val → p ∉ S)
  simpa only [Function.comp_def, neg_neg, exteriorNorm] using hh

/-- Product summability supplies genuine absolute convergence; no
rearrangement of possibly conditional local sums is used. -/
theorem summable_initialMajorant (σ ν ζ : ℝ)
    (hσ : 2 < σ) (hν : 2 < ν) (hζ : 1 / 6 < ζ) :
    Summable (initialMajorant K S σ ν ζ) := by
  have hc := summable_exterior_power K S (t := 1 - σ) (by linarith)
  have hn := summable_exterior_power K S (t := 2 - 3 * σ) (by linarith)
  have hd := summable_exterior_power K S (t := 1 - ν) (by linarith)
  have hr := summable_exterior_power K S (t := -6 * ζ) (by linarith)
  have hcn := hc.mul_of_nonneg hn
    (fun I => Real.rpow_nonneg (idealNorm_pos K I.val).le _)
    (fun I => Real.rpow_nonneg (idealNorm_pos K I.val).le _)
  have hdr := hd.mul_of_nonneg hr
    (fun I => Real.rpow_nonneg (idealNorm_pos K I.val).le _)
    (fun I => Real.rpow_nonneg (idealNorm_pos K I.val).le _)
  have hh := hcn.mul_of_nonneg hdr
    (fun I => mul_nonneg (Real.rpow_nonneg (idealNorm_pos K I.1.val).le _)
      (Real.rpow_nonneg (idealNorm_pos K I.2.val).le _))
    (fun I => mul_nonneg (Real.rpow_nonneg (idealNorm_pos K I.1.val).le _)
      (Real.rpow_nonneg (idealNorm_pos K I.2.val).le _))
  simpa only [initialMajorant, mul_assoc] using hh

/-- The exact absolute convergence assertion required in
RowEulerCalibrationInput, proved from the two literal finite sums. -/
theorem initial_absolute (P : ProbeData K S) (ψ : HeckeCharacter K)
    (Q : Finset (ExteriorPrime K S)) (u : FrequencyRow K S) (s w z : ℂ)
    (hs : 4 < s.re) (hw : 4 < w.re) (hz : 2 < z.re) :
    Summable (initialRowEulerTerm K S P ψ Q u s w z) := by
  have hmajor := summable_initialMajorant K S s.re w.re z.re
    (by linarith) (by linarith) (by linarith)
  exact (hmajor.of_nonneg_of_le (fun I => norm_nonneg _)
    (norm_initialRowEulerTerm_le K S P ψ Q u s w z)).of_norm

#print axioms norm_probeGauss_le_norm
#print axioms norm_finitePoissonFactor_le
#print axioms norm_initialRowEulerTerm_le
#print axioms initial_absolute
#print axioms productPrincipalCharacter_isPrimitive
#print axioms principalPower_character_compatible
#print axioms finitePoisson_summand_representative_independent
end HeckeSkeleton.HighBinActualAbsolute
