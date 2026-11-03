import ActualSexticOriginalChartMean
import SIntegerSexticRIdentification

/-! UNCOMPILED / native 0. The literal original coefficient is bounded by
the actual norm of C, uniformly in both columns, the same Mobius divisor,
and every frequency. The residual extension retains its common-zero mask.
No primitive-frequency or coprimality assumption is imposed. -/

noncomputable section
namespace HeckeGeneral.Characters.ActualGramCoefficientBoundDraft
open AlgebraicNumberTheory.PowerResidueSymbols
open NumberField IsDedekindDomain HeckeGeneral.Arithmetic
open HeckeGeneral.Arithmetic.PeriodicFourier
open ActualGramJointMeanDraft ActualGramJointChartDraft ActualGramJointChartCoverDraft
open scoped Classical BigOperators ComplexConjugate

variable (K : Type) [Field K] [NumberField K]
variable (ζ : K) (hζ : IsPrimitiveRoot ζ 6) (σ : K →+* ℂ)
variable (C J : Ideal (𝓞 K)) (hC : C ≠ 0) (hJ : J ≠ 0)
local notation "P" => jointPlaces K C J hC hJ
local notation "A" => jointResidues K C J hC hJ
local instance ActualSexticCoefficientBound_residueField (p : P) : Field (residue K C J hC hJ p) :=
  Ideal.Quotient.field _
local instance ActualSexticCoefficientBound_residueFintype (p : P) : Fintype (residue K C J hC hJ p) :=
  Fintype.ofFinite _
variable (h6 : ∀ p : jointPlaces K C J hC hJ, (6 : 𝓞 K) ∉ p.val.asIdeal)

private theorem norm_mulChar_le_one {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (x : F) : ‖χ x‖ ≤ 1 := by
  by_cases hx : x = 0
  · subst x
    simp only [χ.map_zero, norm_zero, zero_le_one]
  · obtain ⟨u, rfl⟩ := isUnit_iff_ne_zero.mpr hx
    apply le_of_eq
    simpa only [MulChar.coe_equivToUnitHom] using
      Complex.norm_eq_one_of_mem_rootsOfUnity (χ.apply_mem_rootsOfUnity u)

theorem norm_exteriorColumnFactor_le_one (p : P)
    (d x y : residue K C J hC hJ p) :
    ‖exteriorColumnFactor K ζ hζ σ C J hC hJ h6 p d x y‖ ≤ 1 := by
  unfold exteriorColumnFactor
  split_ifs
  · exact le_of_eq norm_one
  · rw [norm_mul, Complex.norm_conj]
    exact mul_le_one₀ (norm_mulChar_le_one _ _) (norm_nonneg _)
      (norm_mulChar_le_one _ _)

theorem norm_residualColumnFactor_le_primePower (p : P)
    (d k x y : residue K C J hC hJ p) :
    ‖residualColumnFactor K ζ hζ σ C J hC hJ h6 p d k x y‖ ≤
      (Ideal.absNorm p.val.asIdeal : ℝ) ^ idealPrimeMultiplicity K p.val C := by
  by_cases he : idealPrimeMultiplicity K p.val C = 0
  · simp [residualColumnFactor, he]
  · have hpos : 1 ≤ idealPrimeMultiplicity K p.val C := Nat.one_le_iff_ne_zero.mpr he
    have hq : (Nat.card (residue K C J hC hJ p) : ℝ) =
        (Ideal.absNorm p.val.asIdeal : ℝ) := rfl
    have hb := norm_finiteFieldResidualCorrelationExtension_le_card
      (sexticResidueCharacter K ζ hζ σ p.val (h6 p) ^
        idealPrimeMultiplicity K p.val C) (d * x) (d * y) k
    rw [residualColumnFactor, if_neg he, norm_mul, norm_pow, Complex.norm_natCast]
    calc
      _ ≤ (Nat.card (residue K C J hC hJ p) : ℝ) ^
          (idealPrimeMultiplicity K p.val C - 1) *
          (Fintype.card (residue K C J hC hJ p) : ℝ) :=
        mul_le_mul_of_nonneg_left hb (pow_nonneg (Nat.cast_nonneg _) _)
      _ = (Ideal.absNorm p.val.asIdeal : ℝ) ^ idealPrimeMultiplicity K p.val C := by
        rw [← Nat.card_eq_fintype_card, hq, ← pow_succ, Nat.sub_add_cancel hpos]

/-- Frequency primes absent from C contribute the literal factor 1. -/
theorem prod_joint_primePower_norm :
    (∏ p : P, (Ideal.absNorm p.val.asIdeal : ℝ) ^
      idealPrimeMultiplicity K p.val C) = (Ideal.absNorm C : ℝ) := by
  have hid : (∏ p : P, p.val.asIdeal ^ idealPrimeMultiplicity K p.val C) = C := by
    calc
      _ = ∏ p : sexticIdealPlaces K C hC,
          p.val.asIdeal ^ idealPrimeMultiplicity K p.val C := by
        have g : ∀ s : Finset (HeightOneSpectrum (𝓞 K)),
            (∏ p : s, p.val.asIdeal ^ idealPrimeMultiplicity K p.val C) =
              ∏ p ∈ s, p.asIdeal ^ idealPrimeMultiplicity K p C :=
          fun s => Finset.prod_coe_sort s (fun p => p.asIdeal ^ idealPrimeMultiplicity K p C)
        rw [g, g]
        symm
        apply Finset.prod_subset Finset.subset_union_left
        intro p _ hp
        have he : idealPrimeMultiplicity K p C = 0 := by
          by_contra he
          exact hp ((mem_sexticIdealPlaces_iff K C hC p).mpr
            ((Associates.count_ne_zero_iff_dvd hC p.irreducible).mp he))
        rw [he, pow_zero]
      _ = C := sexticIdeal_primePower_product K C hC
  calc
    _ = (Ideal.absNorm (∏ p : P,
        p.val.asIdeal ^ idealPrimeMultiplicity K p.val C) : ℝ) := by
      simp only [map_prod, map_pow, Nat.cast_prod, Nat.cast_pow]
    _ = _ := congrArg (fun I : Ideal (𝓞 K) => (Ideal.absNorm I : ℝ)) hid

theorem norm_jointCoefficient_le_absNorm (d k : A) (m : A × A) :
    ‖jointCoefficient K ζ hζ σ C J hC hJ h6 d k m‖ ≤ (Ideal.absNorm C : ℝ) := by
  rw [jointCoefficient, norm_prod, ← prod_joint_primePower_norm K C J hC hJ]
  apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
  intro p _
  rw [localJointCoefficient, norm_mul]
  calc
    _ ≤ 1 * ‖residualColumnFactor K ζ hζ σ C J hC hJ h6 p
        (d p) (k p) (m.1 p) (m.2 p)‖ :=
      mul_le_mul_of_nonneg_right
        (norm_exteriorColumnFactor_le_one K ζ hζ σ C J hC hJ h6 p _ _ _) (norm_nonneg _)
    _ ≤ _ := by
      rw [one_mul]
      exact norm_residualColumnFactor_le_primePower K ζ hζ σ C J hC hJ h6 p _ _ _ _

section ActualSIntegers
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (hCS : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ C → p ∉ S)
variable (hJS : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ J → p ∉ S)
variable (hS6 : integerPrimeSupport (6 : 𝓞 K) ⊆ S)

theorem norm_actualResidualExtension_le_absNorm (d k m₁ m₂ : S.integer K) :
    ‖actualResidualExtension K S ζ hζ σ C J hC hJ hCS hJS hS6 d k m₁ m₂‖ ≤
      (Ideal.absNorm C : ℝ) := by
  rw [actualResidualExtension, norm_prod, ← prod_joint_primePower_norm K C J hC hJ]
  exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
    (fun p _ => norm_residualColumnFactor_le_primePower K ζ hζ σ C J hC hJ
      (jointAwaySix K S C J hC hJ hCS hJS hS6) p _ _ _ _)

/-- The actual S-local phase costs exactly one, including at shared primes. -/
theorem norm_actualChartPhase (k b₁ b₂ : NonzeroRingElements (S.integer K)) :
    ‖actualChartPhase K S ζ hζ σ k b₁ b₂‖ = 1 := by
  simp only [actualChartPhase, norm_mul, Complex.norm_conj,
    norm_sIntegerSexticRCorrection, mul_one]

/-- This is the manuscript's q_C bound on the literal coefficient, without
restricting either column to a chart or deleting any zero mask. -/
theorem norm_originalChartCoefficient_le_absNorm
    (c k d m₁ m₂ : NonzeroRingElements (S.integer K)) :
    ‖originalChartCoefficient K S ζ hζ σ hS6 c k d m₁ m₂‖ ≤
      (Ideal.absNorm (actualFrequencyIdeal K S c) : ℝ) := by
  rw [originalChartCoefficient, norm_mul]
  calc
    _ ≤ 1 * ‖actualResidualExtension K S ζ hζ σ
        (actualFrequencyIdeal K S c) (actualFrequencyIdeal K S k)
        (actualFrequencyIdeal_ne_zero K S c) (actualFrequencyIdeal_ne_zero K S k)
        (actualFrequencyIdeal_exterior K S c) (actualFrequencyIdeal_exterior K S k)
        hS6 d.val k.val m₁.val m₂.val‖ :=
      mul_le_mul_of_nonneg_right
        (norm_sIntegerSexticRawCoefficient_mul_RCorrection_le_one
          K S ζ hζ σ hS6 _ _ k) (norm_nonneg _)
    _ ≤ _ := by
      rw [one_mul]
      exact norm_actualResidualExtension_le_absNorm K ζ hζ σ _ _ _ _ S
        (actualFrequencyIdeal_exterior K S c) (actualFrequencyIdeal_exterior K S k)
        hS6 d.val k.val m₁.val m₂.val

end ActualSIntegers
end HeckeGeneral.Characters.ActualGramCoefficientBoundDraft
