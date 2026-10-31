import ActualSexticJointChartCRT
import HeckeGeneral.Arithmetic.SIntegerFiniteLocalization
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.RingTheory.Coprime.Lemmas

/-! UNCOMPILED / native 0. Actual CRT independence of a fixed S residue
fiber and the exterior joint radical. The denominator is a power of the
proved exact-S localization denominator, with no enlargement of S.
All residue values, including zero and common-prime zeros, are retained.
This finite descent does not assert the subsequent Poisson bounds. -/

noncomputable section
namespace HeckeGeneral.Characters
namespace ActualGramJointChartCoverDraft
open AlgebraicNumberTheory.PowerResidueSymbols
open NumberField IsDedekindDomain HeckeGeneral.Arithmetic
open ActualGramJointMeanDraft ActualGramJointChartDraft
open scoped Classical BigOperators ComplexConjugate

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (ζ : K) (hζ : IsPrimitiveRoot ζ 6)
variable (C J : Ideal (𝓞 K)) (hC : C ≠ 0) (hJ : J ≠ 0)
variable (hCS : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ C → p ∉ S)
variable (hJS : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ J → p ∉ S)
local notation "P" => jointPlaces K C J hC hJ
local notation "A" => jointResidues K C J hC hJ
local notation "MS" => sIntegerSexticSPlaceModulus K S ζ hζ
local notation "D" => finiteSIntegerDenominator K S
local notation "red" => jointReduction K S C J hC hJ hCS hJS
local instance residueField (p : P) : Field (residue K C J hC hJ p) :=
  Ideal.Quotient.field _
local instance residueFintype (p : P) : Fintype (residue K C J hC hJ p) :=
  Fintype.ofFinite _

/-- Exactly the ordinary joint radical, with each exterior prime once. -/
def jointRadical : Ideal (𝓞 K) := ∏ p : P, p.val.asIdeal

/-- The actual common-denominator refinement of the genuine S modulus. -/
def clearedSModulus (N : ℕ) : Ideal (𝓞 K) :=
  Ideal.span ({D ^ N} : Set (𝓞 K)) * MS

theorem jointRadical_ne_zero : jointRadical K C J hC hJ ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun p _ => p.val.ne_bot

theorem clearedSModulus_ne_zero (N : ℕ) : clearedSModulus K S ζ hζ N ≠ 0 := by
  apply mul_ne_zero
  · exact Ideal.span_singleton_eq_bot.not.mpr
      (pow_ne_zero N (finiteSIntegerDenominator_ne_zero K S))
  · exact sIntegerSexticSPlaceModulus_ne_bot K S ζ hζ

include hCS hJS in
/-- Coprimality is proved from the original S and the actual exterior support. -/
theorem clearedSModulus_coprime_prime (N : ℕ) (p : P) :
    IsCoprime (clearedSModulus K S ζ hζ N) p.val.asIdeal := by
  have hpS := jointExterior K S C J hC hJ hCS hJS p
  have hD : IsCoprime (Ideal.span ({D} : Set (𝓞 K))) p.val.asIdeal := by
    apply Ideal.isCoprime_iff_sup_eq.mpr
    rw [sup_comm]
    exact sup_span_finiteSIntegerDenominator_eq_top K S p.val.asIdeal
      (sIntegerSexticResidue_coprime K S p.val hpS)
  have hDN : IsCoprime (Ideal.span ({D ^ N} : Set (𝓞 K))) p.val.asIdeal := by
    simpa only [← Ideal.span_singleton_pow] using (hD.pow_left (m := N))
  have hMS : IsCoprime MS p.val.asIdeal := by
    unfold sIntegerSexticSPlaceModulus sIntegerPrincipalUnitModulus
    apply IsCoprime.prod_left
    intro v _
    have hvp : v.val ≠ p.val := fun he => hpS (he ▸ v.property)
    simpa only [pow_one] using
      (v.val.isCoprime_pow_of_ne p.val hvp
        (sPlaceSexticCorrectionDepth K S ζ hζ v) 1)
  exact hDN.mul_left hMS

include hCS hJS in
theorem clearedSModulus_coprime_jointRadical (N : ℕ) :
    IsCoprime (clearedSModulus K S ζ hζ N) (jointRadical K C J hC hJ) := by
  apply IsCoprime.prod_right
  intro p _
  exact clearedSModulus_coprime_prime K S ζ hζ C J hC hJ hCS hJS N p

/-- The radical CRT uses actual residue fields, not abstract coordinates. -/
def jointRadicalCRT : (𝓞 K ⧸ jointRadical K C J hC hJ) ≃+* A :=
  (HeightOneSpectrum.quotientEquivPiOfProdEq _ (fun p : P => p.val)
    (fun _ => 1) (fun _ _ h => Subtype.val_injective.ne h)
    (by simp only [pow_one]; rfl)).trans
    (RingEquiv.piCongrRight fun p => Ideal.quotEquivOfEq (pow_one p.val.asIdeal))

set_option maxHeartbeats 2000000 in
@[simp] theorem jointRadicalCRT_mk (z : 𝓞 K) :
    jointRadicalCRT K C J hC hJ (Ideal.Quotient.mk _ z) =
      fun p : P => Ideal.Quotient.mk p.val.asIdeal z := rfl

/-- The genuine common-denominator period quotient. -/
abbrev periodQuotient (N : ℕ) :=
  𝓞 K ⧸ (clearedSModulus K S ζ hζ N * jointRadical K C J hC hJ)

set_option maxHeartbeats 1600000 in
def chartCRT (N : ℕ) : periodQuotient K S ζ hζ C J hC hJ N ≃+*
    (𝓞 K ⧸ clearedSModulus K S ζ hζ N) × A :=
  (Ideal.quotientMulEquivQuotientProd _ _
    (clearedSModulus_coprime_jointRadical K S ζ hζ C J hC hJ hCS hJS N)).trans
    (RingEquiv.prodCongr (RingEquiv.refl _) (jointRadicalCRT K C J hC hJ))

set_option maxHeartbeats 2000000 in
@[simp] theorem chartCRT_mk (N : ℕ) (z : 𝓞 K) :
    chartCRT K S ζ hζ C J hC hJ hCS hJS N (Ideal.Quotient.mk _ z) =
      (Ideal.Quotient.mk _ z, fun p : P => Ideal.Quotient.mk p.val.asIdeal z) := rfl

/-- A literal fixed ordinary S residue fiber, before choosing representatives. -/
def chartFiber (N : ℕ) (a : 𝓞 K ⧸ clearedSModulus K S ζ hζ N) :=
  {q : periodQuotient K S ζ hζ C J hC hJ N //
    (chartCRT K S ζ hζ C J hC hJ hCS hJS N q).1 = a}

/-- Every fixed S fiber has exactly one point for each exterior coordinate. -/
def chartFiberEquiv (N : ℕ) (a : 𝓞 K ⧸ clearedSModulus K S ζ hζ N) :
    chartFiber K S ζ hζ C J hC hJ hCS hJS N a ≃ A where
  toFun q := (chartCRT K S ζ hζ C J hC hJ hCS hJS N q.val).2
  invFun x := ⟨(chartCRT K S ζ hζ C J hC hJ hCS hJS N).symm (a, x), by simp⟩
  left_inv q := by
    apply Subtype.ext
    apply (chartCRT K S ζ hζ C J hC hJ hCS hJS N).injective
    have hq : ((a, (chartCRT K S ζ hζ C J hC hJ hCS hJS N q.val).2) :
        (𝓞 K ⧸ clearedSModulus K S ζ hζ N) × A) =
        chartCRT K S ζ hζ C J hC hJ hCS hJS N q.val := Prod.ext q.property.symm rfl
    simpa using hq
  right_inv x := by simp

/-- Explicit common-denominator scaling, a permutation even at zero. -/
def denominatorScale (N : ℕ) : A ≃ A where
  toFun x p := (Ideal.Quotient.mk p.val.asIdeal (D ^ N))⁻¹ * x p
  invFun x p := Ideal.Quotient.mk p.val.asIdeal (D ^ N) * x p
  left_inv x := by
    funext p
    have hn : Ideal.Quotient.mk p.val.asIdeal (D ^ N) ≠ 0 := by
      have hu := (sIntegerSexticResidue_denominator_isUnit K S p.val
        (jointExterior K S C J hC hJ hCS hJS p)).pow N
      simpa only [map_pow] using hu.ne_zero
    exact mul_inv_cancel_left₀ hn (x p)
  right_inv x := by
    funext p
    have hn : Ideal.Quotient.mk p.val.asIdeal (D ^ N) ≠ 0 := by
      have hu := (sIntegerSexticResidue_denominator_isUnit K S p.val
        (jointExterior K S C J hC hJ hCS hJS p)).pow N
      simpa only [map_pow] using hu.ne_zero
    exact inv_mul_cancel_left₀ hn (x p)

/-- The external coordinates of z/D^N are the actual S-integer reductions. -/
theorem denominatorScale_eq_jointReduction (N : ℕ) (z : 𝓞 K) (m : S.integer K)
    (hm : algebraMap (𝓞 K) (S.integer K) (D ^ N) * m =
      algebraMap (𝓞 K) (S.integer K) z) :
    denominatorScale K S C J hC hJ hCS hJS N
      (fun p => Ideal.Quotient.mk p.val.asIdeal z) = red m := by
  funext p
  have hu := (sIntegerSexticResidue_denominator_isUnit K S p.val
    (jointExterior K S C J hC hJ hCS hJS p)).pow N
  have hn : Ideal.Quotient.mk p.val.asIdeal (D ^ N) ≠ 0 := by
    simpa only [map_pow] using hu.ne_zero
  have he := congrArg
    (sIntegerSexticResidueMap K S p.val (jointExterior K S C J hC hJ hCS hJS p)) hm
  simp only [map_mul, sIntegerSexticResidueMap_algebraMap] at he
  change (Ideal.Quotient.mk p.val.asIdeal (D ^ N))⁻¹ *
    Ideal.Quotient.mk p.val.asIdeal z = _
  rw [← he]
  exact inv_mul_cancel_left₀ hn _

/-- A fixed S fiber parametrizes the actual denominator-scaled coordinates. -/
def scaledChartFiberEquiv (N M : ℕ) (a : 𝓞 K ⧸ clearedSModulus K S ζ hζ N) :
    chartFiber K S ζ hζ C J hC hJ hCS hJS N a ≃ A :=
  (chartFiberEquiv K S ζ hζ C J hC hJ hCS hJS N a).trans
    (denominatorScale K S C J hC hJ hCS hJS M)

local instance chartFiberFintype (N : ℕ)
    (a : 𝓞 K ⧸ clearedSModulus K S ζ hζ N) :
    Fintype (chartFiber K S ζ hζ C J hC hJ hCS hJS N a) :=
  Fintype.ofEquiv A (chartFiberEquiv K S ζ hζ C J hC hJ hCS hJS N a).symm

/-- Equal fibers are a conclusion, including zero external coordinates. -/
theorem card_chartFiber (N : ℕ) (a : 𝓞 K ⧸ clearedSModulus K S ζ hζ N) :
    Fintype.card (chartFiber K S ζ hζ C J hC hJ hCS hJS N a) = Fintype.card A :=
  Fintype.card_congr (chartFiberEquiv K S ζ hζ C J hC hJ hCS hJS N a)

variable (σ : K →+* ℂ) (hS6 : integerPrimeSupport (6 : 𝓞 K) ⊆ S)
local notation "h6" => jointAwaySix K S C J hC hJ hCS hJS hS6

/-- Complete finite averages on any two genuine fixed S fibers inherit the
actual joint zero mean. The same d enters both columns, and no common-prime
values are removed. Neither surjectivity nor zero mean is an input. -/
theorem sum_scaled_chart_jointCoefficient_eq_zero (N M : ℕ)
    (a b : 𝓞 K ⧸ clearedSModulus K S ζ hζ N)
    (p : P) (hpC : ¬ p.val.asIdeal ∣ C)
    (hpJ : ¬ 6 ∣ idealPrimeMultiplicity K p.val J)
    (d k : S.integer K) (phase : ℂ) :
    (∑ q : chartFiber K S ζ hζ C J hC hJ hCS hJS N a ×
        chartFiber K S ζ hζ C J hC hJ hCS hJS N b,
      phase * jointCoefficient K ζ hζ σ C J hC hJ h6 (red d) (red k)
        (scaledChartFiberEquiv K S ζ hζ C J hC hJ hCS hJS N M a q.1,
         scaledChartFiberEquiv K S ζ hζ C J hC hJ hCS hJS N M b q.2)) = 0 := by
  let e := Equiv.prodCongr
    (scaledChartFiberEquiv K S ζ hζ C J hC hJ hCS hJS N M a)
    (scaledChartFiberEquiv K S ζ hζ C J hC hJ hCS hJS N M b)
  calc
    _ = ∑ x : A × A,
        phase * jointCoefficient K ζ hζ σ C J hC hJ h6 (red d) (red k) x :=
      Fintype.sum_equiv e _ _ (fun _ => rfl)
    _ = 0 := by
      rw [← Finset.mul_sum, sum_jointCoefficient_eq_zero K ζ hζ σ C J hC hJ h6
        p hpC hpJ (red d) (red k), mul_zero]

end ActualGramJointChartCoverDraft
end HeckeGeneral.Characters
