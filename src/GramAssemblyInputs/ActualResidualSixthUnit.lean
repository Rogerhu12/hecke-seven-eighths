import ActualSexticJointChartCRT
import HeckeGeneral.Arithmetic.SIntegerOrbitEnumeration

/-!
UNCOMPILED / native 0. Fixed-frequency invariance of the stipulated
residual extension under two independent original sixth-unit column
actions. The pair permutation below is the forward form of
(x,y) -> (v^-1*x,u^-1*y): from the scaled-column sum to the original sum
it sends (x,y) to (v*x,u*y). No frequency or cardinality factor changes.
The common-zero branch, absent-prime branch and all MulChar zero masks
are retained. No coprime-locus identification is used.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeGeneral.Characters.ActualResidualSixthUnitDraft

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic
open HeckeGeneral.Arithmetic.PeriodicFourier
open ActualGramJointMeanDraft ActualGramJointChartDraft
open AlgebraicNumberTheory.PowerResidueSymbols
open scoped Classical BigOperators ComplexConjugate

section FiniteField

variable {F : Type*} [Field F] [Fintype F]

/-- A literal pair permutation at fixed k, including all zero columns.
The character invariances apply also at zero and to principal powers. -/
theorem finiteFieldResidualCorrelationExtension_independent_unit_invariant
    (χ : MulChar F ℂ) (u v : Fˣ)
    (hu : ∀ x, χ ((u : F) * x) = χ x)
    (hv : ∀ x, χ ((v : F) * x) = χ x) (n₁ n₂ k : F) :
    finiteFieldResidualCorrelationExtension χ ((u : F) * n₁) ((v : F) * n₂) k =
      finiteFieldResidualCorrelationExtension χ n₁ n₂ k := by
  have haff : affineCorrelation χ ((u : F) * n₁) ((v : F) * n₂) k =
      affineCorrelation χ n₁ n₂ k := by
    unfold affineCorrelation
    refine Fintype.sum_bijective _
      ((Units.mulLeft v).prodCongr (Units.mulLeft u)).bijective _ _ (fun p => ?_)
    change (if (v : F) * n₂ * p.1 - (u : F) * n₁ * p.2 = k then
        χ p.1 * conj (χ p.2) else 0) =
      if n₂ * ((v : F) * p.1) - n₁ * ((u : F) * p.2) = k then
        χ ((v : F) * p.1) * conj (χ ((u : F) * p.2)) else 0
    have hlinear : (v : F) * n₂ * p.1 - (u : F) * n₁ * p.2 =
        n₂ * ((v : F) * p.1) - n₁ * ((u : F) * p.2) := by ring
    rw [hlinear, hv, hu]
  have hzero : ((u : F) * n₁ = 0 ∧ (v : F) * n₂ = 0) ↔
      (n₁ = 0 ∧ n₂ = 0) := by
    simp only [mul_eq_zero, u.ne_zero, v.ne_zero, false_or]
  unfold finiteFieldResidualCorrelationExtension
  simp only [hzero]
  split_ifs
  · rfl
  · exact haff

end FiniteField

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (ζ : K) (hζ : IsPrimitiveRoot ζ 6) (σ : K →+* ℂ)
local notation "OS" => S.integer K
local notation "NZ" => NonzeroRingElements OS
-- Definitionally the actual `sixthPowerUnits K S`.
local notation "Γ" => MonoidHom.range (powMonoidHom 6 : S.unit K →* S.unit K)

section SingleResidue

variable (p : HeightOneSpectrum (𝓞 K)) (hpS : p ∉ S)
local instance : Field (𝓞 K ⧸ p.asIdeal) := Ideal.Quotient.field _
local instance : Fintype (𝓞 K ⧸ p.asIdeal) := Fintype.ofFinite _

/-- Evaluation of a character power on an actual reduced sixth S-unit.
Using pow_apply_coe avoids replacing the principal character's zero mask
by the constant function one. -/
private theorem residueCharacter_pow_gamma_one
    (hp6 : (6 : 𝓞 K) ∉ p.asIdeal) (u : Γ) (e : ℕ) :
    (sexticResidueCharacter K ζ hζ σ p hp6 ^ e)
        (sUnitSexticResidueUnit K S p hpS u.val : 𝓞 K ⧸ p.asIdeal) = 1 := by
  rw [MulChar.pow_apply_coe]
  have hu : sexticResidueCharacter K ζ hζ σ p hp6
      (sUnitSexticResidueUnit K S p hpS u.val : 𝓞 K ⧸ p.asIdeal) = 1 := by
    have h := sIntegerSexticEvaluation_literal_invariant K S p hpS ζ hζ σ hp6
        Γ (le_refl _) u 1
    simp only [sIntegerSexticEvaluation, mul_one, map_one] at h
    exact h
  rw [hu, one_pow]

end SingleResidue

section GeneralIdeals

variable (C J : Ideal (𝓞 K)) (hC : C ≠ 0) (hJ : J ≠ 0)
variable (hCS : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ C → p ∉ S)
variable (hJS : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ J → p ∉ S)
variable (hS6 : integerPrimeSupport (6 : 𝓞 K) ⊆ S)
local notation "P" => jointPlaces K C J hC hJ
local notation "red" => jointReduction K S C J hC hJ hCS hJS
local notation "h6" => jointAwaySix K S C J hC hJ hCS hJS hS6
local instance residualSixth_residueField (p : P) :
    Field (residue K C J hC hJ p) := Ideal.Quotient.field _
local instance residualSixth_residueFintype (p : P) :
    Fintype (residue K C J hC hJ p) := Fintype.ofFinite _

/-- The actual finite product at the SAME divisor and frequency. Every
S-integer input may vanish; neither residual column is required coprime. -/
theorem actualResidualExtension_sixthPower_columns
    (d k m₁ m₂ : OS) (u v : Γ) :
    actualResidualExtension K S ζ hζ σ C J hC hJ hCS hJS hS6 d k
        ((S.unitEquivUnitsInteger K u.val).val * m₁)
        ((S.unitEquivUnitsInteger K v.val).val * m₂) =
      actualResidualExtension K S ζ hζ σ C J hC hJ hCS hJS hS6 d k m₁ m₂ := by
  unfold actualResidualExtension
  apply Finset.prod_congr rfl
  intro p _
  let π := sIntegerSexticResidueMap K S p.val
    (jointExterior K S C J hC hJ hCS hJS p)
  let U := sUnitSexticResidueUnit K S p.val
    (jointExterior K S C J hC hJ hCS hJS p) u.val
  let V := sUnitSexticResidueUnit K S p.val
    (jointExterior K S C J hC hJ hCS hJS p) v.val
  let χ := sexticResidueCharacter K ζ hζ σ p.val (h6 p) ^
    idealPrimeMultiplicity K p.val C
  have hU : χ (U : residue K C J hC hJ p) = 1 :=
    residueCharacter_pow_gamma_one K S ζ hζ σ p.val
      (jointExterior K S C J hC hJ hCS hJS p) (h6 p) u _
  have hV : χ (V : residue K C J hC hJ p) = 1 :=
    residueCharacter_pow_gamma_one K S ζ hζ σ p.val
      (jointExterior K S C J hC hJ hCS hJS p) (h6 p) v _
  have hprod₁ : red d p * red ((S.unitEquivUnitsInteger K u.val).val * m₁) p =
      (U : residue K C J hC hJ p) * (red d p * red m₁ p) := by
    change π d * π ((S.unitEquivUnitsInteger K u.val).val * m₁) =
      π (S.unitEquivUnitsInteger K u.val).val * (π d * π m₁)
    rw [map_mul]
    ring
  have hprod₂ : red d p * red ((S.unitEquivUnitsInteger K v.val).val * m₂) p =
      (V : residue K C J hC hJ p) * (red d p * red m₂ p) := by
    change π d * π ((S.unitEquivUnitsInteger K v.val).val * m₂) =
      π (S.unitEquivUnitsInteger K v.val).val * (π d * π m₂)
    rw [map_mul]
    ring
  have hlocal := finiteFieldResidualCorrelationExtension_independent_unit_invariant χ U V
    (fun x => by rw [map_mul, hU, one_mul])
    (fun x => by rw [map_mul, hV, one_mul]) (red d p * red m₁ p)
    (red d p * red m₂ p) (red k p)
  unfold residualColumnFactor
  rw [hprod₁, hprod₂]
  split_ifs
  · rfl
  · congr 1

end GeneralIdeals

end HeckeGeneral.Characters.ActualResidualSixthUnitDraft
