import ActualThetaOriginalFullFactorization
import ActualSexticZeroFrequencyDiagonal
import HeckeSkeleton.Moments.MOM_BASE.FiniteCoefficients
import SIntegerSexticPrimePowerCorrelation

/-!
# Actual supported correlations for the moment reductions

The columns below use the actual generators of `ThetaArithmeticData`.
The common-factor decomposition retains their literal quotient generators,
including the general unit discrepancies. All frequencies, original zeros,
and nonsquarefree moduli remain present.

The factorized expression is also defined on noncoprime residual ideals.
Its equality with the original full correlation is proved exactly where
the residual ideals are coprime, which is the interface needed before
inserting the ideal Möbius mask.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_BASE

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.ThetaSkeleton.ActualGeneratorDivisionDraft
open HeckeGeneral.ThetaSkeleton.Physical.ActualProbeGaussFourierDraft
open scoped Classical BigOperators ComplexConjugate nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (D : ThetaArithmeticData K S)

local notation "E" => ExteriorIdeal K S
local notation "R" => S.integer K
local notation "NZ" => NonzeroRingElements R

/-- The full-modulus correlation of the two actual canonical generators. -/
def actualFullCorrelation (I J : E) (j : R) : ℂ :=
  sIntegerSexticOriginalFullCorrelation K S D.root6 D.primitive6 D.embedding
    (probeArithmetic_six_support K S D)
    (probeGenerator K S D I) (probeGenerator K S D J) j

/-- Distinct ideal labels have no zero-frequency contribution. -/
theorem actualFullCorrelation_zero_off_diagonal (I J : E) (hIJ : I ≠ J) :
    actualFullCorrelation K S D I J 0 = 0 := by
  apply sIntegerSexticOriginalFullCorrelation_zero_of_contraction_ne
  intro h
  rw [probeGenerator_contraction K S D I,
    probeGenerator_contraction K S D J] at h
  exact hIJ (Subtype.ext (Subtype.ext h))

/-- The diagonal counts units in the actual ideal quotient, including the
unit ideal and its singleton quotient. -/
theorem actualFullCorrelation_zero_diagonal (I : E) :
    actualFullCorrelation K S D I I 0 =
      (Nat.card (ThetaQuotient K S I)ˣ : ℂ) := by
  unfold actualFullCorrelation
  rw [sIntegerSexticOriginalFullCorrelation_self_zero]
  exact_mod_cast Nat.card_congr (Units.mapEquiv
    (Ideal.quotEquivOfEq (D.generator_span I)).toMulEquiv).toEquiv

/-- One exact statement for the full zero-frequency matrix. -/
theorem actualFullCorrelation_zero_frequency (I J : E) :
    actualFullCorrelation K S D I J 0 =
      if I = J then (Nat.card (ThetaQuotient K S I)ˣ : ℂ) else 0 := by
  by_cases h : I = J
  · subst J
    simp [actualFullCorrelation_zero_diagonal]
  · rw [if_neg h, actualFullCorrelation_zero_off_diagonal K S D I J h]

/-- Every common exterior ideal divides every supported frequency. -/
theorem actualFullCorrelation_common_support
    (C N₁ N₂ I J : E)
    (hI : I = exteriorMul K S C N₁) (hJ : J = exteriorMul K S C N₂)
    (j : R) (hj : j ∉ C.val.val.map (algebraMap (𝓞 K) R)) :
    actualFullCorrelation K S D I J j = 0 :=
  thetaOriginalFullCorrelation_eq_zero_of_not_mem K S D C N₁ N₂ I J hI hJ j hj

/-- The element-divisibility form of the same common-ideal support. -/
theorem actualFullCorrelation_common_divisibility
    (C N₁ N₂ I J : E)
    (hI : I = exteriorMul K S C N₁) (hJ : J = exteriorMul K S C N₂)
    (j : R) (hj : ¬ D.generator C ∣ j) :
    actualFullCorrelation K S D I J j = 0 :=
  thetaOriginalFullCorrelation_eq_zero_of_not_dvd K S D C N₁ N₂ I J hI hJ j hj

/-- The residual column is the literal quotient of the supplied generators.
It is not replaced by the independently supplied generator of the residual
ideal. -/
def actualResidualGenerator (C N : E) : NZ :=
  thetaGeneratorDivision K S D C N (exteriorMul K S C N) rfl

theorem actualResidualGenerator_factor (C N : E) :
    D.generator (exteriorMul K S C N) =
      D.generator C * (actualResidualGenerator K S D C N).val :=
  thetaGeneratorDivision_factor K S D C N (exteriorMul K S C N) rfl

theorem actualResidualGenerator_span (C N : E) :
    Ideal.span ({(actualResidualGenerator K S D C N).val} : Set R) =
      N.val.val.map (algebraMap (𝓞 K) R) :=
  thetaGeneratorDivision_span K S D C N (exteriorMul K S C N) rfl

/-- Coprimality follows from the actual residual ideals; no element
coprimality or Bézout data is an additional input. -/
theorem actualResidualGenerator_isCoprime (C N₁ N₂ : E)
    (hcop : IsCoprime N₁.val.val N₂.val.val) :
    IsCoprime (actualResidualGenerator K S D C N₁).val
      (actualResidualGenerator K S D C N₂).val :=
  thetaGeneratorDivision_isCoprime K S D C N₁ N₂
    (exteriorMul K S C N₁) (exteriorMul K S C N₂) rfl rfl hcop

/-- The actual raw-symbol and local reciprocity phase, with its original
zeros on both residual columns. -/
def actualResidualPhase (C N₁ N₂ : E) (k : R) : ℂ :=
  let n₁ := actualResidualGenerator K S D C N₁
  let n₂ := actualResidualGenerator K S D C N₂
  let χ := sIntegerSexticSymbol K S D.root6 D.primitive6 D.embedding
    (probeArithmetic_six_support K S D)
  (χ k n₁ * conj (χ (-k) n₂)) *
    sIntegerSexticRCorrection K S D.root6 D.primitive6 D.embedding n₁ n₂

theorem actualResidualPhase_norm_le_one (C N₁ N₂ : E) (k : R) :
    ‖actualResidualPhase K S D C N₁ N₂ k‖ ≤ 1 := by
  have hn (x : R) (n : NZ) :
      ‖sIntegerSexticSymbol K S D.root6 D.primitive6 D.embedding
        (probeArithmetic_six_support K S D) x n‖ ≤ 1 := by
    unfold sIntegerSexticSymbol
    exact norm_sIntegerSexticIdealEvaluation_le_one K S D.root6 D.primitive6
      D.embedding _ _ _ _ x
  simp only [actualResidualPhase, norm_mul, Complex.norm_conj,
    norm_sIntegerSexticRCorrection, mul_one]
  exact (mul_le_mul (hn _ _) (hn _ _) (norm_nonneg _) (by norm_num)).trans_eq (one_mul 1)

/-- The exact raw-symbol, R-correction and common-ideal correlation product.
The definition is meaningful for every residual pair. -/
def actualResidualCorrelation (C N₁ N₂ : E) (k : R) : ℂ :=
  let n₁ := actualResidualGenerator K S D C N₁
  let n₂ := actualResidualGenerator K S D C N₂
  actualResidualPhase K S D C N₁ N₂ k *
    sIntegerSexticFiniteCorrelation K S D.root6 D.primitive6 D.embedding
      C.val.val (nonZeroDivisors.coe_ne_zero C.val) C.property
      (fun p hp => D.away_six p (C.property p hp))
      (Ideal.Quotient.mk _ n₁.val) (Ideal.Quotient.mk _ n₂.val)
      (Ideal.Quotient.mk _ k)

/-- Exact factorization at every divisible frequency, including zero. -/
theorem actualFullCorrelation_factorization (C N₁ N₂ : E)
    (hcop : IsCoprime N₁.val.val N₂.val.val) (k : R) :
    actualFullCorrelation K S D
      (exteriorMul K S C N₁) (exteriorMul K S C N₂) (D.generator C * k) =
      actualResidualCorrelation K S D C N₁ N₂ k :=
  thetaOriginalFullCorrelation_factorization K S D C N₁ N₂
    (exteriorMul K S C N₁) (exteriorMul K S C N₂) rfl rfl hcop k

/-- The same fixed residual expression, supported on the common ideal,
is defined before residual coprimality is expanded by Möbius inversion. -/
def actualSupportedCorrelation (C : E) (N : E × E) (j : R) : ℂ :=
  if h : D.generator C ∣ j then
    actualResidualCorrelation K S D C N.1 N.2 (Classical.choose h)
  else 0

/-- Its value at a specified divisible frequency does not depend on the
choice of the divisibility witness. -/
theorem actualSupportedCorrelation_mul_generator (C N₁ N₂ : E) (k : R) :
    actualSupportedCorrelation K S D C (N₁, N₂) (D.generator C * k) =
      actualResidualCorrelation K S D C N₁ N₂ k := by
  have hd : D.generator C ∣ D.generator C * k := dvd_mul_right _ _
  rw [actualSupportedCorrelation, dif_pos hd]
  have hk : Classical.choose hd = k := by
    exact mul_left_cancel₀ (D.generator_ne_zero C) (Classical.choose_spec hd).symm
  rw [hk]

theorem actualSupportedCorrelation_zero_off_support (C : E) (N : E × E)
    (j : R) (hj : j ∉ C.val.val.map (algebraMap (𝓞 K) R)) :
    actualSupportedCorrelation K S D C N j = 0 := by
  have hd : ¬ D.generator C ∣ j := by
    intro h
    apply hj
    rw [← D.generator_span C]
    exact Ideal.mem_span_singleton.mpr h
  rw [actualSupportedCorrelation, dif_neg hd]

/-- This is the consumer interface for the supported-correlation port.
The actual full correlation and the fixed extension agree on every
coprime residual pair, at every frequency. -/
theorem actualSupportedCorrelation_agrees (C N₁ N₂ : E)
    (hcop : IsCoprime N₁.val.val N₂.val.val) (j : R) :
    actualSupportedCorrelation K S D C (N₁, N₂) j =
      actualFullCorrelation K S D
        (exteriorMul K S C N₁) (exteriorMul K S C N₂) j := by
  by_cases hd : D.generator C ∣ j
  · obtain ⟨k, rfl⟩ := hd
    rw [actualSupportedCorrelation_mul_generator,
      actualFullCorrelation_factorization K S D C N₁ N₂ hcop]
  · rw [actualSupportedCorrelation, dif_neg hd]
    exact (actualFullCorrelation_common_divisibility K S D C N₁ N₂
      (exteriorMul K S C N₁) (exteriorMul K S C N₂) rfl rfl j hd).symm


/-- A residual ideal divisible by p has the original zero residue at p,
even though its supplied generator differs by a general S-unit. -/
theorem actualResidualGenerator_zero_mod_prime (C N : E)
    (p : ExteriorPrime K S) (hp : p.val.asIdeal ∣ N.val.val) :
    sIntegerSexticResidueMap K S p.val p.property
      (actualResidualGenerator K S D C N).val = 0 := by
  have hn : (actualResidualGenerator K S D C N).val ∈
      Ideal.span ({(actualResidualGenerator K S D C N).val} : Set R) :=
    Ideal.subset_span (Set.mem_singleton _)
  rw [actualResidualGenerator_span] at hn
  have hn' : (actualResidualGenerator K S D C N).val ∈
      p.val.asIdeal.map (algebraMap (𝓞 K) R) :=
    Ideal.map_mono (Ideal.dvd_iff_le.mp hp) hn
  change (sIntegerResidueEquiv K S p.val.asIdeal
    (sIntegerSexticResidue_coprime K S p.val p.property)).symm
    (Ideal.Quotient.mk _ (actualResidualGenerator K S D C N).val) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hn', map_zero]

/-- The unequal-multiplicity local factor with its actual raw/R phase.
The first residual ideal contains p; coprimality forces the second
residual column to be a unit at p. -/
theorem actualFullCorrelation_unequal_common_formula
    (p : ExteriorPrime K S) {b : ℕ} (hb : 1 ≤ b)
    (N₁ N₂ : E) (hcop : IsCoprime N₁.val.val N₂.val.val)
    (hp : p.val.asIdeal ∣ N₁.val.val) (k : R) :
    let C := actualPrimePowerIdeal K S p b
    actualFullCorrelation K S D
      (exteriorMul K S C N₁) (exteriorMul K S C N₂) (D.generator C * k) =
      actualResidualPhase K S D C N₁ N₂ k *
        ((p.val.asIdeal.absNorm : ℂ) ^ (b - 1) *
          (if 6 ∣ b then
            if sIntegerSexticResidueMap K S p.val p.property k = 0
              then 0 else (p.val.asIdeal.absNorm : ℂ) - 1
           else 0)) := by
  dsimp only
  let C := actualPrimePowerIdeal K S p b
  let n₁ := actualResidualGenerator K S D C N₁
  let n₂ := actualResidualGenerator K S D C N₂
  let Q := sIntegerPrimePowerQuotient K S p.val b
  let x : Q := Ideal.Quotient.mk _ n₁.val
  let y : Q := Ideal.Quotient.mk _ n₂.val
  let π := sIntegerPrimePowerReduction K S p.val p.property b hb
  have hn : IsCoprime x y :=
    (actualResidualGenerator_isCoprime K S D C N₁ N₂ hcop).map (Ideal.Quotient.mk _)
  have hx : π x = 0 := by
    rw [sIntegerPrimePowerReduction_mk]
    exact actualResidualGenerator_zero_mod_prime K S D C N₁ p hp
  have hy : π y ≠ 0 := by
    intro hy
    exact sIntegerSexticPrimePowerCorrelation_residual_columns_not_both_zero
      K S p.val p.property b hb x y hn ⟨hx, hy⟩
  have hf := sIntegerSexticPrimePowerCorrelation_first_zero
    K S p.val p.property b hb D.root6 D.primitive6 D.embedding
    (D.away_six p.val p.property) x y (Ideal.Quotient.mk _ k) hn hx hy
  have hcard : Nat.card (𝓞 K ⧸ p.val.asIdeal) = p.val.asIdeal.absNorm := rfl
  rw [actualFullCorrelation_factorization K S D C N₁ N₂ hcop]
  change actualResidualPhase K S D C N₁ N₂ k * _ = _
  exact congrArg (fun z => actualResidualPhase K S D C N₁ N₂ k * z)
    (by simpa only [C, Q, n₁, n₂, x, y, actualPrimePowerIdeal,
      sIntegerPrimePowerReduction_mk, hcard] using hf)

/-- Pure prime powers a>b, with the chosen generators of both full ideals.
No multiplicativity of the generator section is imposed. -/
theorem actualFullCorrelation_unequal_prime_power_formula
    (p : ExteriorPrime K S) (a b : ℕ) (hab : b < a) (hb : 1 ≤ b) (k : R) :
    actualFullCorrelation K S D
      (actualPrimePowerIdeal K S p a) (actualPrimePowerIdeal K S p b)
      (D.generator (actualPrimePowerIdeal K S p b) * k) =
      actualResidualPhase K S D (actualPrimePowerIdeal K S p b)
        (actualPrimePowerIdeal K S p (a - b)) (actualPrimePowerIdeal K S p 0) k *
        ((p.val.asIdeal.absNorm : ℂ) ^ (b - 1) *
          (if 6 ∣ b then
            if sIntegerSexticResidueMap K S p.val p.property k = 0
              then 0 else (p.val.asIdeal.absNorm : ℂ) - 1
           else 0)) := by
  have hcop : IsCoprime (actualPrimePowerIdeal K S p (a - b)).val.val
      (actualPrimePowerIdeal K S p 0).val.val := by
    change IsCoprime (p.val.asIdeal ^ (a - b)) (p.val.asIdeal ^ 0)
    simp only [pow_zero]
    exact isCoprime_one_right
  have hp : p.val.asIdeal ∣ (actualPrimePowerIdeal K S p (a - b)).val.val :=
    dvd_pow_self _ (by omega)
  have hsum : b + (a - b) = a := by omega
  simpa only [actualPrimePowerIdeal_mul, hsum, Nat.add_zero] using
    actualFullCorrelation_unequal_common_formula K S D p hb
      (actualPrimePowerIdeal K S p (a - b)) (actualPrimePowerIdeal K S p 0) hcop hp k

/-- The smaller exponent must be a multiple of six at every frequency. -/
theorem actualFullCorrelation_unequal_zero_of_not_six
    (p : ExteriorPrime K S) (a b : ℕ) (hab : b < a) (hb : 1 ≤ b)
    (hb6 : ¬ 6 ∣ b) (j : R) :
    actualFullCorrelation K S D
      (actualPrimePowerIdeal K S p a) (actualPrimePowerIdeal K S p b) j = 0 := by
  by_cases hd : D.generator (actualPrimePowerIdeal K S p b) ∣ j
  · obtain ⟨k, rfl⟩ := hd
    rw [actualFullCorrelation_unequal_prime_power_formula K S D p a b hab hb]
    simp [hb6]
  · have hsum : b + (a - b) = a := by omega
    apply actualFullCorrelation_common_divisibility K S D
      (actualPrimePowerIdeal K S p b)
      (actualPrimePowerIdeal K S p (a - b)) (actualPrimePowerIdeal K S p 0)
      _ _ _ _ j hd
    · rw [actualPrimePowerIdeal_mul, hsum]
    · rw [actualPrimePowerIdeal_mul, Nat.add_zero]

/-- The divided frequency must retain its original unit mask. -/
theorem actualFullCorrelation_unequal_zero_of_nonunit
    (p : ExteriorPrime K S) (a b : ℕ) (hab : b < a) (hb : 1 ≤ b)
    (k : R) (hk : sIntegerSexticResidueMap K S p.val p.property k = 0) :
    actualFullCorrelation K S D
      (actualPrimePowerIdeal K S p a) (actualPrimePowerIdeal K S p b)
      (D.generator (actualPrimePowerIdeal K S p b) * k) = 0 := by
  rw [actualFullCorrelation_unequal_prime_power_formula K S D p a b hab hb]
  simp [hk]

/-- The actual unequal-prime-power contribution is bounded by P^b. -/
theorem actualFullCorrelation_unequal_norm_le
    (p : ExteriorPrime K S) (a b : ℕ) (hab : b < a) (hb : 1 ≤ b) (j : R) :
    ‖actualFullCorrelation K S D
      (actualPrimePowerIdeal K S p a) (actualPrimePowerIdeal K S p b) j‖ ≤
      (p.val.asIdeal.absNorm : ℝ) ^ b := by
  by_cases hd : D.generator (actualPrimePowerIdeal K S p b) ∣ j
  · obtain ⟨k, rfl⟩ := hd
    rw [actualFullCorrelation_unequal_prime_power_formula K S D p a b hab hb, norm_mul]
    have hq : (1 : ℝ) ≤ p.val.asIdeal.absNorm := by
      exact_mod_cast (Nat.le_of_lt (NumberField.HeightOneSpectrum.one_lt_absNorm p.val))
    have hsub : ‖(p.val.asIdeal.absNorm : ℂ) - 1‖ ≤ (p.val.asIdeal.absNorm : ℝ) := by
      have he : (p.val.asIdeal.absNorm : ℂ) - 1 =
          (((p.val.asIdeal.absNorm : ℝ) - 1 : ℝ) : ℂ) := by push_cast; rfl
      rw [he, Complex.norm_real, Real.norm_of_nonneg (sub_nonneg.mpr hq)]
      linarith
    have htail : ‖(if 6 ∣ b then
          if sIntegerSexticResidueMap K S p.val p.property k = 0
            then 0 else (p.val.asIdeal.absNorm : ℂ) - 1
          else 0)‖ ≤ (p.val.asIdeal.absNorm : ℝ) := by
      split_ifs <;> first | exact hsub | simp
    have hlocal : ‖(p.val.asIdeal.absNorm : ℂ) ^ (b - 1) *
        (if 6 ∣ b then
          if sIntegerSexticResidueMap K S p.val p.property k = 0
            then 0 else (p.val.asIdeal.absNorm : ℂ) - 1
          else 0)‖ ≤ (p.val.asIdeal.absNorm : ℝ) ^ b := by
      have hnorm : ‖(p.val.asIdeal.absNorm : ℂ)‖ = (p.val.asIdeal.absNorm : ℝ) := by simp
      rw [norm_mul, norm_pow, hnorm]
      calc
        _ ≤ (p.val.asIdeal.absNorm : ℝ) ^ (b - 1) * p.val.asIdeal.absNorm :=
          mul_le_mul_of_nonneg_left htail (by positivity)
        _ = _ := by rw [← pow_succ, Nat.sub_add_cancel hb]
    simpa only [one_mul] using mul_le_mul
      (actualResidualPhase_norm_le_one K S D (actualPrimePowerIdeal K S p b)
        (actualPrimePowerIdeal K S p (a - b)) (actualPrimePowerIdeal K S p 0) k)
      hlocal (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  · have hsum : b + (a - b) = a := by omega
    have hz : actualFullCorrelation K S D
        (actualPrimePowerIdeal K S p a) (actualPrimePowerIdeal K S p b) j = 0 := by
      apply actualFullCorrelation_common_divisibility K S D
        (actualPrimePowerIdeal K S p b)
        (actualPrimePowerIdeal K S p (a - b)) (actualPrimePowerIdeal K S p 0)
        _ _ _ _ j hd
      · rw [actualPrimePowerIdeal_mul, hsum]
      · rw [actualPrimePowerIdeal_mul, Nat.add_zero]
    rw [hz, norm_zero]
    positivity


/-- Equal full prime-power moduli, evaluated on the original divided
frequency. The finite table is derived from the actual quotient function. -/
theorem actualFullCorrelation_equal_prime_power_formula
    (p : ExteriorPrime K S) (a : ℕ) (ha : 1 ≤ a) (k : R) :
    let C := actualPrimePowerIdeal K S p a
    let U := actualPrimePowerIdeal K S p 0
    actualFullCorrelation K S D C C (D.generator C * k) =
      actualResidualPhase K S D C U U k *
        ((p.val.asIdeal.absNorm : ℂ) ^ (a - 1) *
          (if sIntegerSexticResidueMap K S p.val p.property k = 0
            then (p.val.asIdeal.absNorm : ℂ) - 1
           else if 6 ∣ a then (p.val.asIdeal.absNorm : ℂ) - 2 else -1)) := by
  dsimp only
  letI : Field (𝓞 K ⧸ p.val.asIdeal) := Ideal.Quotient.field _
  let C := actualPrimePowerIdeal K S p a
  let U := actualPrimePowerIdeal K S p 0
  let n := actualResidualGenerator K S D C U
  let Q := sIntegerPrimePowerQuotient K S p.val a
  let x : Q := Ideal.Quotient.mk _ n.val
  let π := sIntegerPrimePowerReduction K S p.val p.property a ha
  have hcop : IsCoprime U.val.val U.val.val := by
    change IsCoprime (p.val.asIdeal ^ 0) (p.val.asIdeal ^ 0)
    simp only [pow_zero]
    exact isCoprime_one_right
  have hn : IsCoprime x x :=
    (actualResidualGenerator_isCoprime K S D C U U hcop).map (Ideal.Quotient.mk _)
  have hx : π x ≠ 0 := by
    intro h
    have hm := hn.map π
    rw [h] at hm
    exact not_isCoprime_zero_zero hm
  have hratio :
      sIntegerPrimePowerReduction K S p.val p.property a ha x /
        sIntegerPrimePowerReduction K S p.val p.property a ha x = 1 := div_self hx
  have hcard : Nat.card (𝓞 K ⧸ p.val.asIdeal) = p.val.asIdeal.absNorm := rfl
  have hf := actualFullCorrelation_factorization K S D C U U hcop k
  have hCU : exteriorMul K S C U = C := by
    exact actualPrimePowerIdeal_mul K S p a 0
  rw [hCU] at hf
  rw [hf]
  change actualResidualPhase K S D C U U k * _ = _
  congr 1
  by_cases hk : sIntegerSexticResidueMap K S p.val p.property k = 0
  · have hz := sIntegerSexticPrimePowerCorrelation_zero
      K S p.val p.property a ha D.root6 D.primitive6 D.embedding
      (D.away_six p.val p.property) x x (Ideal.Quotient.mk _ k) hn hx hx
      (by simpa only [sIntegerPrimePowerReduction_mk] using hk)
    simp only [hcard, hratio, map_one, one_mul] at hz
    simpa only [C, U, Q, n, x, actualPrimePowerIdeal, if_pos hk] using hz
  · have hz := sIntegerSexticPrimePowerCorrelation_nonzero
      K S p.val p.property a ha D.root6 D.primitive6 D.embedding
      (D.away_six p.val p.property) x x (Ideal.Quotient.mk _ k) hn hx hx
      (by simpa only [sIntegerPrimePowerReduction_mk] using hk)
    simp only [hcard, hratio, map_one] at hz
    simpa only [C, U, Q, n, x, actualPrimePowerIdeal, if_neg hk] using hz

/-- The improved equal-multiplicity bound at a unit divided frequency. -/
theorem actualFullCorrelation_equal_unit_frequency_norm_le
    (p : ExteriorPrime K S) (a : ℕ) (ha : 1 ≤ a) (ha6 : ¬ 6 ∣ a)
    (k : R) (hk : sIntegerSexticResidueMap K S p.val p.property k ≠ 0) :
    ‖actualFullCorrelation K S D
      (actualPrimePowerIdeal K S p a) (actualPrimePowerIdeal K S p a)
      (D.generator (actualPrimePowerIdeal K S p a) * k)‖ ≤
      (p.val.asIdeal.absNorm : ℝ) ^ (a - 1) := by
  rw [actualFullCorrelation_equal_prime_power_formula K S D p a ha]
  simp only [if_neg hk, if_neg ha6, norm_mul, norm_pow, norm_neg, norm_one, mul_one]
  have hnorm : ‖(p.val.asIdeal.absNorm : ℂ)‖ = (p.val.asIdeal.absNorm : ℝ) := by simp
  rw [hnorm]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right
    (actualResidualPhase_norm_le_one K S D (actualPrimePowerIdeal K S p a)
      (actualPrimePowerIdeal K S p 0) (actualPrimePowerIdeal K S p 0) k)
    (show 0 ≤ (p.val.asIdeal.absNorm : ℝ) ^ (a - 1) by positivity)

/-- The equal-multiplicity full correlation is bounded by the norm of its
modulus at every frequency, including unsupported and zero frequencies. -/
theorem actualFullCorrelation_equal_norm_le
    (p : ExteriorPrime K S) (a : ℕ) (ha : 1 ≤ a) (j : R) :
    ‖actualFullCorrelation K S D
      (actualPrimePowerIdeal K S p a) (actualPrimePowerIdeal K S p a) j‖ ≤
      (p.val.asIdeal.absNorm : ℝ) ^ a := by
  by_cases hd : D.generator (actualPrimePowerIdeal K S p a) ∣ j
  · obtain ⟨k, rfl⟩ := hd
    rw [actualFullCorrelation_equal_prime_power_formula K S D p a ha, norm_mul]
    have hP : (2 : ℝ) ≤ p.val.asIdeal.absNorm := by
      exact_mod_cast (show 2 ≤ p.val.asIdeal.absNorm from
        NumberField.HeightOneSpectrum.one_lt_absNorm p.val)
    have hsub (r : ℝ) (hr : 0 ≤ r) (hrP : r ≤ p.val.asIdeal.absNorm) :
        ‖(p.val.asIdeal.absNorm : ℂ) - (r : ℂ)‖ ≤ (p.val.asIdeal.absNorm : ℝ) := by
      have he : (p.val.asIdeal.absNorm : ℂ) - (r : ℂ) =
          (((p.val.asIdeal.absNorm : ℝ) - r : ℝ) : ℂ) := by push_cast; rfl
      rw [he, Complex.norm_real, Real.norm_of_nonneg (sub_nonneg.mpr hrP)]
      linarith
    have htail : ‖(if sIntegerSexticResidueMap K S p.val p.property k = 0
          then (p.val.asIdeal.absNorm : ℂ) - 1
          else if 6 ∣ a then (p.val.asIdeal.absNorm : ℂ) - 2 else -1)‖ ≤
        (p.val.asIdeal.absNorm : ℝ) := by
      split_ifs
      · simpa using hsub 1 (by norm_num) (by linarith)
      · simpa using hsub 2 (by norm_num) hP
      · simpa using (show (1 : ℝ) ≤ p.val.asIdeal.absNorm by linarith)
    have hlocal : ‖(p.val.asIdeal.absNorm : ℂ) ^ (a - 1) *
        (if sIntegerSexticResidueMap K S p.val p.property k = 0
          then (p.val.asIdeal.absNorm : ℂ) - 1
          else if 6 ∣ a then (p.val.asIdeal.absNorm : ℂ) - 2 else -1)‖ ≤
        (p.val.asIdeal.absNorm : ℝ) ^ a := by
      have hnorm : ‖(p.val.asIdeal.absNorm : ℂ)‖ = (p.val.asIdeal.absNorm : ℝ) := by simp
      rw [norm_mul, norm_pow, hnorm]
      calc
        _ ≤ (p.val.asIdeal.absNorm : ℝ) ^ (a - 1) * p.val.asIdeal.absNorm :=
          mul_le_mul_of_nonneg_left htail (by positivity)
        _ = _ := by rw [← pow_succ, Nat.sub_add_cancel ha]
    simpa only [one_mul] using mul_le_mul
      (actualResidualPhase_norm_le_one K S D (actualPrimePowerIdeal K S p a)
        (actualPrimePowerIdeal K S p 0) (actualPrimePowerIdeal K S p 0) k)
      hlocal (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  · have hz : actualFullCorrelation K S D
        (actualPrimePowerIdeal K S p a) (actualPrimePowerIdeal K S p a) j = 0 := by
      apply actualFullCorrelation_common_divisibility K S D
        (actualPrimePowerIdeal K S p a)
        (actualPrimePowerIdeal K S p 0) (actualPrimePowerIdeal K S p 0)
        _ _ _ _ j hd
      all_goals rw [actualPrimePowerIdeal_mul, Nat.add_zero]
    rw [hz, norm_zero]
    positivity

end HeckeSkeleton.Moments.MOM_BASE

