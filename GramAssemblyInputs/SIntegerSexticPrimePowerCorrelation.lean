import SIntegerSexticPrimePowerQuotient
import FiniteFieldAffineCorrelation
import SIntegerSexticFiniteCorrelation

/-! Source-only, uncompiled. Actual prime-power reduction and two
residue-unit and single-zero column formulas. Both residual columns
cannot vanish under the original quotient coprimality premise. -/
noncomputable section
namespace HeckeGeneral.Characters
open NumberField IsDedekindDomain HeckeGeneral.Arithmetic
open HeckeGeneral.Arithmetic.PeriodicFourier
open scoped Classical BigOperators
variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (p : HeightOneSpectrum (𝓞 K)) (hpS : p ∉ S)
variable (c : ℕ) (hc : 1 ≤ c)
variable (ζ : K) (hζ : IsPrimitiveRoot ζ 6) (σ : K →+* ℂ)
variable (hp6 : (6 : 𝓞 K) ∉ p.asIdeal)
local notation "Q" => sIntegerPrimePowerQuotient K S p c
local notation "F" => 𝓞 K ⧸ p.asIdeal
local instance primePowerCorrelation_residueField : Field F := Ideal.Quotient.field _
local instance primePowerCorrelation_residueFintype : Fintype F := Fintype.ofFinite F
local notation "π" => sIntegerPrimePowerReduction K S p hpS c hc
local notation "χ" => sexticResidueCharacter K ζ hζ σ p hp6
local notation "Φ" => sIntegerSexticIdealQuotientFunction K S ζ hζ σ (p.asIdeal ^ c)
  (pow_ne_zero _ p.ne_bot) (primePower_exterior K S p hpS c) (primePower_away_six K p c hp6)
local notation "LC" => sIntegerSexticFiniteCorrelation K S ζ hζ σ (p.asIdeal ^ c)
  (pow_ne_zero _ p.ne_bot) (primePower_exterior K S p hpS c) (primePower_away_six K p c hp6)

theorem sIntegerSexticPrimePowerCorrelation_reduction (n₁ n₂ k : Q)
    (hn : IsCoprime n₁ n₂) :
    LC n₁ n₂ k =
      (Nat.card F ^ (c - 1) : ℂ) * affineCorrelation (χ ^ c) (π n₁) (π n₂) (π k) := by
  letI : Finite Q := finite_sIntegerSexticIdealQuotient K S (p.asIdeal ^ c)
    (pow_ne_zero _ p.ne_bot) (primePower_exterior K S p hpS c)
  letI : Fintype Q := Fintype.ofFinite Q
  letI : Fintype F := Fintype.ofFinite F
  change affineCorrelation Φ n₁ n₂ k = _
  have hf : Φ = fun z => (χ ^ c) (π z) := funext
    (sIntegerSexticPrimePowerQuotientFunction_eq_pullback K S p hpS c hc ζ hζ σ hp6)
  rw [hf, affineCorrelation_comp_surjective_ringHom π
    (sIntegerPrimePowerReduction_surjective K S p hpS c hc) (⇑(χ ^ c)) n₁ n₂ k hn,
    natCard_sIntegerPrimePowerReduction_kernel K S p hpS c hc]
  simp only [Nat.cast_pow]

/-- The zero-frequency formula applies when both column reductions are
nonzero. Its character phase is retained, even for distinct associates. -/
theorem sIntegerSexticPrimePowerCorrelation_zero (n₁ n₂ k : Q)
    (hn : IsCoprime n₁ n₂) (h₁ : π n₁ ≠ 0) (h₂ : π n₂ ≠ 0) (hk : π k = 0) :
    LC n₁ n₂ k = (Nat.card F ^ (c - 1) : ℂ) *
      ((χ ^ c) (π n₁ / π n₂) * ((Nat.card F : ℂ) - 1)) := by
  letI : Finite Q := finite_sIntegerSexticIdealQuotient K S (p.asIdeal ^ c)
    (pow_ne_zero _ p.ne_bot) (primePower_exterior K S p hpS c)
  letI : Fintype Q := Fintype.ofFinite Q
  letI : Field F := Ideal.Quotient.field _
  letI : Fintype F := Fintype.ofFinite F
  rw [sIntegerSexticPrimePowerCorrelation_reduction K S p hpS c hc ζ hζ σ hp6 n₁ n₂ k hn,
    hk, affineCorrelation_mulChar_zero (χ ^ c) (π n₁) (π n₂) h₁ h₂]
  simp only [Nat.card_eq_fintype_card]

/-- Nonzero reduced frequency: the trivial/nontrivial distinction is
derived from the exact order six of the specified residue character. -/
theorem sIntegerSexticPrimePowerCorrelation_nonzero (n₁ n₂ k : Q)
    (hn : IsCoprime n₁ n₂) (h₁ : π n₁ ≠ 0) (h₂ : π n₂ ≠ 0) (hk : π k ≠ 0) :
    LC n₁ n₂ k = (Nat.card F ^ (c - 1) : ℂ) *
      (if 6 ∣ c then (Nat.card F : ℂ) - 2 else -(χ ^ c) (π n₁ / π n₂)) := by
  letI : Finite Q := finite_sIntegerSexticIdealQuotient K S (p.asIdeal ^ c)
    (pow_ne_zero _ p.ne_bot) (primePower_exterior K S p hpS c)
  letI : Fintype Q := Fintype.ofFinite Q
  letI : Field F := Ideal.Quotient.field _
  letI : Fintype F := Fintype.ofFinite F
  rw [sIntegerSexticPrimePowerCorrelation_reduction K S p hpS c hc ζ hζ σ hp6 n₁ n₂ k hn]
  by_cases hd : 6 ∣ c
  · have he : χ ^ c = 1 := (sexticResidueCharacter_pow_eq_one_iff K p c ζ hζ σ hp6).mpr hd
    rw [if_pos hd, he, affineCorrelation_trivial_nonzero (π n₁) (π n₂) (π k) h₁ h₂ hk]
    simp only [Nat.card_eq_fintype_card]
  · have he : χ ^ c ≠ 1 := mt (sexticResidueCharacter_pow_eq_one_iff K p c ζ hζ σ hp6).mp hd
    rw [if_neg hd, affineCorrelation_mulChar_nonzero (χ ^ c) he (π n₁) (π n₂) (π k) h₁ h₂ hk]

/-- A zero first residual column. The frequency mask remains literal;
the nontrivial character branch vanishes at every frequency. -/
theorem sIntegerSexticPrimePowerCorrelation_first_zero (n₁ n₂ k : Q)
    (hn : IsCoprime n₁ n₂) (h₁ : π n₁ = 0) (h₂ : π n₂ ≠ 0) :
    LC n₁ n₂ k = (Nat.card F ^ (c - 1) : ℂ) *
      (if 6 ∣ c then (if π k = 0 then 0 else (Nat.card F : ℂ) - 1) else 0) := by
  rw [sIntegerSexticPrimePowerCorrelation_reduction K S p hpS c hc ζ hζ σ hp6 n₁ n₂ k hn, h₁]
  by_cases hd : 6 ∣ c
  · have he : χ ^ c = 1 := (sexticResidueCharacter_pow_eq_one_iff K p c ζ hζ σ hp6).mpr hd
    rw [if_pos hd, he, affineCorrelation_trivial_first_zero (π n₂) (π k) h₂]
    simp only [Nat.card_eq_fintype_card]
  · have he : χ ^ c ≠ 1 := mt (sexticResidueCharacter_pow_eq_one_iff K p c ζ hζ σ hp6).mp hd
    rw [if_neg hd, affineCorrelation_mulChar_first_zero_nontrivial (χ ^ c) he (π n₂) (π k) h₂]

/-- A zero second residual column, with the same actual zero-frequency mask. -/
theorem sIntegerSexticPrimePowerCorrelation_second_zero (n₁ n₂ k : Q)
    (hn : IsCoprime n₁ n₂) (h₁ : π n₁ ≠ 0) (h₂ : π n₂ = 0) :
    LC n₁ n₂ k = (Nat.card F ^ (c - 1) : ℂ) *
      (if 6 ∣ c then (if π k = 0 then 0 else (Nat.card F : ℂ) - 1) else 0) := by
  rw [sIntegerSexticPrimePowerCorrelation_reduction K S p hpS c hc ζ hζ σ hp6 n₁ n₂ k hn, h₂]
  by_cases hd : 6 ∣ c
  · have he : χ ^ c = 1 := (sexticResidueCharacter_pow_eq_one_iff K p c ζ hζ σ hp6).mpr hd
    rw [if_pos hd, he, affineCorrelation_trivial_second_zero (π n₁) (π k) h₁]
    simp only [Nat.card_eq_fintype_card]
  · have he : χ ^ c ≠ 1 := mt (sexticResidueCharacter_pow_eq_one_iff K p c ζ hζ σ hp6).mp hd
    rw [if_neg hd, affineCorrelation_mulChar_second_zero_nontrivial (χ ^ c) he (π n₁) (π k) h₁]

theorem sIntegerSexticPrimePowerCorrelation_residual_columns_not_both_zero
    (n₁ n₂ : Q) (hn : IsCoprime n₁ n₂) : ¬ (π n₁ = 0 ∧ π n₂ = 0) := by
  intro h
  have hm := hn.map π
  rw [h.1, h.2] at hm
  exact not_isCoprime_zero_zero hm

end HeckeGeneral.Characters
