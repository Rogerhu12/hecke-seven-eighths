import SIntegerSexticIdealCorrelationProduct
import SIntegerSexticPrimePowerCorrelation
import FiniteFieldResidualCorrelationExtension
import HeckeGeneral.Arithmetic.PeriodicFourier

/-! UNCOMPILED / native 0.

Finite residue-coordinate part of revised Proposition 3.8. The prime set
and both exponents come from actual ordinary ideals C and J (eventually
J is the exterior ideal of kR). The artificial residual extension retains
the common-zero mask, and the divisor pullback is kept in both columns.

This file does NOT identify the literal raw-symbol times RCorrection on
S-integer charts with this coefficient. That arithmetic chart/CRT identity
is still required before this endpoint applies to the original Gram sum.
In particular, no zero-mean hypothesis is introduced.
-/

noncomputable section
namespace HeckeGeneral.Characters.ActualGramJointMeanDraft
open NumberField IsDedekindDomain HeckeGeneral.Arithmetic
open HeckeGeneral.Arithmetic.PeriodicFourier
open AlgebraicNumberTheory.PowerResidueSymbols
open scoped Classical BigOperators ComplexConjugate

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (ζ : K) (hζ : IsPrimitiveRoot ζ 6) (σ : K →+* ℂ)

/-- The actual prime-power residual extension on every pair of columns.
It is a separately defined extension, not the full affine sum at a common
nonunit pair. -/
def primePowerResidualExtension
    (p : HeightOneSpectrum (𝓞 K)) (hpS : p ∉ S)
    (c : ℕ) (hc : 1 ≤ c) (hp6 : (6 : 𝓞 K) ∉ p.asIdeal)
    (n₁ n₂ k : sIntegerPrimePowerQuotient K S p c) : ℂ :=
  letI : Field (𝓞 K ⧸ p.asIdeal) := Ideal.Quotient.field _
  letI : Fintype (𝓞 K ⧸ p.asIdeal) := Fintype.ofFinite _
  let π := sIntegerPrimePowerReduction K S p hpS c hc
  (Nat.card (𝓞 K ⧸ p.asIdeal) ^ (c - 1) : ℂ) *
    finiteFieldResidualCorrelationExtension
      (sexticResidueCharacter K ζ hζ σ p hp6 ^ c) (π n₁) (π n₂) (π k)

theorem primePowerResidualExtension_eq_genuine
    (p : HeightOneSpectrum (𝓞 K)) (hpS : p ∉ S)
    (c : ℕ) (hc : 1 ≤ c) (hp6 : (6 : 𝓞 K) ∉ p.asIdeal)
    (n₁ n₂ k : sIntegerPrimePowerQuotient K S p c)
    (hn : IsCoprime n₁ n₂) :
    primePowerResidualExtension K S ζ hζ σ p hpS c hc hp6 n₁ n₂ k =
      sIntegerSexticFiniteCorrelation K S ζ hζ σ (p.asIdeal ^ c)
        (pow_ne_zero _ p.ne_bot) (primePower_exterior K S p hpS c)
        (primePower_away_six K p c hp6) n₁ n₂ k := by
  letI : Field (𝓞 K ⧸ p.asIdeal) := Ideal.Quotient.field _
  letI : Fintype (𝓞 K ⧸ p.asIdeal) := Fintype.ofFinite _
  dsimp only [primePowerResidualExtension]
  rw [finiteFieldResidualCorrelationExtension_eq_affineCorrelation _ _ _ _
    (hn.map (sIntegerPrimePowerReduction K S p hpS c hc))]
  exact (sIntegerSexticPrimePowerCorrelation_reduction
    K S p hpS c hc ζ hζ σ hp6 n₁ n₂ k hn).symm

variable (C J : Ideal (𝓞 K)) (hC : C ≠ 0) (hJ : J ≠ 0)

/-- The common radical's actual prime coordinates. -/
abbrev jointPlaces := sexticIdealPlaces K C hC ∪ sexticIdealPlaces K J hJ

abbrev residue (p : jointPlaces K C J hC hJ) := 𝓞 K ⧸ p.val.asIdeal

local instance residueField (p : jointPlaces K C J hC hJ) :
    Field (residue K C J hC hJ p) := Ideal.Quotient.field _
local instance residueFintype (p : jointPlaces K C J hC hJ) :
    Fintype (residue K C J hC hJ p) := Fintype.ofFinite _

abbrev jointResidues := ∀ p : jointPlaces K C J hC hJ, residue K C J hC hJ p

variable (h6 : ∀ p : jointPlaces K C J hC hJ, (6 : 𝓞 K) ∉ p.val.asIdeal)

/-- A zero exponent means that the prime is absent, so contributes 1 even
at residue zero. At a positive exponent the actual MulChar power retains
its zero extension, also when the exponent is divisible by six. -/
def exteriorColumnFactor (p : jointPlaces K C J hC hJ)
    (d x y : residue K C J hC hJ p) : ℂ :=
  if idealPrimeMultiplicity K p.val J = 0 then 1 else
    (sexticResidueCharacter K ζ hζ σ p.val (h6 p) ^
      idealPrimeMultiplicity K p.val J) (d * x) *
    conj ((sexticResidueCharacter K ζ hζ σ p.val (h6 p) ^
      idealPrimeMultiplicity K p.val J) (d * y))

/-- The manuscript's prime-power residual extension, pulled back by the
actual same divisor d in both columns. A prime absent from C contributes 1.
No coprimality of the new columns is imposed after the divisor substitution. -/
def residualColumnFactor (p : jointPlaces K C J hC hJ)
    (d k x y : residue K C J hC hJ p) : ℂ :=
  if idealPrimeMultiplicity K p.val C = 0 then 1 else
    (Nat.card (residue K C J hC hJ p) ^
      (idealPrimeMultiplicity K p.val C - 1) : ℂ) *
    finiteFieldResidualCorrelationExtension
      (sexticResidueCharacter K ζ hζ σ p.val (h6 p) ^
        idealPrimeMultiplicity K p.val C) (d * x) (d * y) k

def localJointCoefficient (p : jointPlaces K C J hC hJ)
    (d k x y : residue K C J hC hJ p) : ℂ :=
  exteriorColumnFactor K ζ hζ σ C J hC hJ h6 p d x y *
    residualColumnFactor K ζ hζ σ C J hC hJ h6 p d k x y

def jointCoefficient (d k : jointResidues K C J hC hJ)
    (m : jointResidues K C J hC hJ × jointResidues K C J hC hJ) : ℂ :=
  ∏ p : jointPlaces K C J hC hJ,
    localJointCoefficient K ζ hζ σ C J hC hJ h6 p (d p) (k p) (m.1 p) (m.2 p)

/-- Nontriviality is proved for the specified global-root residue character
and the actual ideal valuation. The divisor can even be zero at p: its
original zero extension then kills the complete column. -/
theorem sum_localJointCoefficient_eq_zero
    (p : jointPlaces K C J hC hJ) (hpC : ¬ p.val.asIdeal ∣ C)
    (hpJ : ¬ 6 ∣ idealPrimeMultiplicity K p.val J)
    (d k : residue K C J hC hJ p) :
    (∑ m : residue K C J hC hJ p × residue K C J hC hJ p,
      localJointCoefficient K ζ hζ σ C J hC hJ h6 p d k m.1 m.2) = 0 := by
  have hc : idealPrimeMultiplicity K p.val C = 0 := by
    by_contra hne
    exact hpC ((Associates.count_ne_zero_iff_dvd hC p.val.irreducible).mp hne)
  have hj : idealPrimeMultiplicity K p.val J ≠ 0 := by
    intro he
    apply hpJ
    rw [he]
    exact dvd_zero 6
  let χ := sexticResidueCharacter K ζ hζ σ p.val (h6 p) ^
    idealPrimeMultiplicity K p.val J
  have hχ : χ ≠ 1 := by
    exact mt (sexticResidueCharacter_pow_eq_one_iff
      K p.val (idealPrimeMultiplicity K p.val J) ζ hζ σ (h6 p)).mp hpJ
  have hsum : (∑ x : residue K C J hC hJ p, χ (d * x)) = 0 := by
    simp only [map_mul, ← Finset.mul_sum, MulChar.sum_eq_zero_of_ne_one hχ, mul_zero]
  simp only [localJointCoefficient, exteriorColumnFactor, residualColumnFactor,
    if_pos hc, if_neg hj, mul_one]
  rewrite [Fintype.sum_prod_type]
  change (∑ x : residue K C J hC hJ p, ∑ y : residue K C J hC hJ p,
    χ (d * x) * conj (χ (d * y))) = 0
  rw [← Fintype.sum_mul_sum, hsum, zero_mul]

private def pairPiEquiv {ι : Type*} {A : ι → Type*} :
    ((∀ i, A i) × (∀ i, A i)) ≃ (∀ i, A i × A i) where
  toFun m i := (m.1 i, m.2 i)
  invFun m := (fun i => (m i).1, fun i => (m i).2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Complete joint mean vanishes because one actual exterior local
character is nonprincipal. The residual extension at every other prime
remains in the sum, including all common-nonunit zero masks. -/
theorem sum_jointCoefficient_eq_zero
    (p : jointPlaces K C J hC hJ) (hpC : ¬ p.val.asIdeal ∣ C)
    (hpJ : ¬ 6 ∣ idealPrimeMultiplicity K p.val J)
    (d k : jointResidues K C J hC hJ) :
    (∑ m, jointCoefficient K ζ hζ σ C J hC hJ h6 d k m) = 0 := by
  unfold jointCoefficient
  calc
    _ = ∑ m : ∀ q : jointPlaces K C J hC hJ,
        residue K C J hC hJ q × residue K C J hC hJ q,
        ∏ q, localJointCoefficient K ζ hζ σ C J hC hJ h6 q
          (d q) (k q) (m q).1 (m q).2 :=
      Fintype.sum_equiv pairPiEquiv _ _ (fun _ => rfl)
    _ = ∏ q : jointPlaces K C J hC hJ,
        ∑ m : residue K C J hC hJ q × residue K C J hC hJ q,
          localJointCoefficient K ζ hζ σ C J hC hJ h6 q
            (d q) (k q) m.1 m.2 :=
      (Fintype.prod_sum (fun (q : jointPlaces K C J hC hJ)
        (m : residue K C J hC hJ q × residue K C J hC hJ q) =>
          localJointCoefficient K ζ hζ σ C J hC hJ h6 q (d q) (k q) m.1 m.2)).symm
    _ = 0 := Finset.prod_eq_zero (Finset.mem_univ p)
      (sum_localJointCoefficient_eq_zero K ζ hζ σ C J hC hJ h6 p hpC hpJ (d p) (k p))

/-- The actual finite Fourier transform at the joint zero frequency.
Primitivity is irrelevant at zero; any genuine additive character gives
the same vanishing. -/
theorem normalized_jointFourier_zero
    (p : jointPlaces K C J hC hJ) (hpC : ¬ p.val.asIdeal ∣ C)
    (hpJ : ¬ 6 ∣ idealPrimeMultiplicity K p.val J)
    (d k : jointResidues K C J hC hJ)
    (ψ : AddChar (jointResidues K C J hC hJ × jointResidues K C J hC hJ) ℂ) :
    (Fintype.card (jointResidues K C J hC hJ × jointResidues K C J hC hJ) : ℂ)⁻¹ *
      fourier ψ (jointCoefficient K ζ hζ σ C J hC hJ h6 d k) 0 = 0 := by
  rw [fourier_zero, sum_jointCoefficient_eq_zero
    K ζ hζ σ C J hC hJ h6 p hpC hpJ d k, mul_zero]

/-- The ordinary support assumptions used by the actual exterior ideals
construct every required good-residue-character proof. -/
def jointAwaySix
    (hCS : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ C → p ∉ S)
    (hJS : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ J → p ∉ S)
    (hS6 : integerPrimeSupport (6 : 𝓞 K) ⊆ S)
    (p : jointPlaces K C J hC hJ) : (6 : 𝓞 K) ∉ p.val.asIdeal := by
  have hpS : p.val ∉ S := by
    rcases Finset.mem_union.mp p.property with hp | hp
    · exact hCS p.val ((mem_sexticIdealPlaces_iff K C hC p.val).mp hp)
    · exact hJS p.val ((mem_sexticIdealPlaces_iff K J hJ p.val).mp hp)
  exact fun hp6 => hpS (hS6 hp6)

/-- Exterior-ideal version: the nonexceptional prime is an ordinary prime,
and its membership in the actual common radical is proved from its actual
valuation. No separate character-order or zero-mean input is supplied. -/
theorem normalized_jointFourier_zero_of_exterior
    (hCS : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ C → p ∉ S)
    (hJS : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ J → p ∉ S)
    (hS6 : integerPrimeSupport (6 : 𝓞 K) ⊆ S)
    (p : HeightOneSpectrum (𝓞 K)) (hpC : ¬ p.asIdeal ∣ C)
    (hpJ : ¬ 6 ∣ idealPrimeMultiplicity K p J)
    (d k : jointResidues K C J hC hJ)
    (ψ : AddChar (jointResidues K C J hC hJ × jointResidues K C J hC hJ) ℂ) :
    (Fintype.card (jointResidues K C J hC hJ × jointResidues K C J hC hJ) : ℂ)⁻¹ *
      fourier ψ (jointCoefficient K ζ hζ σ C J hC hJ
        (jointAwaySix K S C J hC hJ hCS hJS hS6) d k) 0 = 0 := by
  have he : idealPrimeMultiplicity K p J ≠ 0 := by
    intro he
    apply hpJ
    rw [he]
    exact dvd_zero 6
  have hpdiv : p.asIdeal ∣ J :=
    (Associates.count_ne_zero_iff_dvd hJ p.irreducible).mp he
  have hpin : p ∈ jointPlaces K C J hC hJ :=
    Finset.mem_union_right _ ((mem_sexticIdealPlaces_iff K J hJ p).mpr hpdiv)
  exact normalized_jointFourier_zero K ζ hζ σ C J hC hJ
    (jointAwaySix K S C J hC hJ hCS hJS hS6) ⟨p, hpin⟩ hpC hpJ d k ψ

end HeckeGeneral.Characters.ActualGramJointMeanDraft
