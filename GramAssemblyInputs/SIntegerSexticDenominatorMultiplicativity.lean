import SIntegerSexticIdealEvaluationFiniteSupport
import HeckeGeneral.Characters.SIntegerSexticSymbol
import HeckeGeneral.Arithmetic.SIntegerIdealSaturation

/-! SOURCE ONLY, UNRUN. Actual denominator multiplicativity, without
coprimality of the two denominator ideals. The contraction product is
proved by the genuine localization residue equivalence. Shared-prime
multiplicities add, retaining all zero factors and the unit-ideal case. -/

noncomputable section
namespace HeckeGeneral.Arithmetic
open NumberField IsDedekindDomain
open scoped Classical
variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Finite S]

theorem sIntegerModulusContraction_mul (c d : S.integer K) (hc : c ≠ 0) (hd : d ≠ 0) :
    sIntegerModulusContraction K S (c * d) =
      sIntegerModulusContraction K S c * sIntegerModulusContraction K S d := by
  have hcop : ∀ v ∈ S,
      (sIntegerModulusContraction K S c * sIntegerModulusContraction K S d) ⊔ v.asIdeal = ⊤ := by
    intro v hv
    rw [Ideal.mul_sup_eq_of_coprime_left (sIntegerModulusContraction_coprime K S c hc v hv)]
    exact sIntegerModulusContraction_coprime K S d hd v hv
  rw [← under_map_coprime_sIntegerIdeal K S _ hcop, Ideal.map_mul,
    map_sIntegerModulusContraction, map_sIntegerModulusContraction,
    Ideal.span_singleton_mul_span_singleton]
  rfl
end HeckeGeneral.Arithmetic

namespace HeckeGeneral.Characters
open NumberField IsDedekindDomain HeckeGeneral.Arithmetic
open AlgebraicNumberTheory.PowerResidueSymbols
open scoped Classical BigOperators
variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Finite S]
variable (ζ : K) (hζ : IsPrimitiveRoot ζ 6) (σ : K →+* ℂ)

private theorem prod_pow_of_add {α : Type*} [Fintype α]
    (z : α → ℂ) (m n r : α → ℕ) (h : ∀ i, r i = m i + n i) :
    (∏ i, z i ^ r i) = (∏ i, z i ^ m i) * (∏ i, z i ^ n i) := by
  calc
    _ = ∏ i, z i ^ m i * z i ^ n i := by
      apply Finset.prod_congr rfl
      intro i _
      exact (congrArg (fun k : ℕ => z i ^ k) (h i)).trans
        (pow_add (z i) (m i) (n i))
    _ = _ := Finset.prod_mul_distrib

theorem sIntegerSexticIdealEvaluation_mul_denominator
    (I J : Ideal (𝓞 K)) (hI : I ≠ 0) (hJ : J ≠ 0)
    (hS : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I ∨ p.asIdeal ∣ J → p ∉ S)
    (h6 : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I ∨ p.asIdeal ∣ J → (6 : 𝓞 K) ∉ p.asIdeal)
    (a : S.integer K) :
    sIntegerSexticIdealEvaluation K S ζ hζ σ (I * J) (mul_ne_zero hI hJ)
      (fun p hp => hS p ((p.prime.dvd_mul (a := I) (b := J)).mp hp))
      (fun p hp => h6 p ((p.prime.dvd_mul (a := I) (b := J)).mp hp)) a =
      sIntegerSexticIdealEvaluation K S ζ hζ σ I hI
        (fun p hp => hS p (Or.inl hp)) (fun p hp => h6 p (Or.inl hp)) a *
      sIntegerSexticIdealEvaluation K S ζ hζ σ J hJ
        (fun p hp => hS p (Or.inr hp)) (fun p hp => h6 p (Or.inr hp)) a := by
  let T := (idealPrimeDivisors_finite K (I * J) (mul_ne_zero hI hJ)).toFinset
  have hT (p : HeightOneSpectrum (𝓞 K)) : p ∈ T ↔ p.asIdeal ∣ I * J :=
    (idealPrimeDivisors_finite K (I * J) (mul_ne_zero hI hJ)).mem_toFinset
  have hTS (p : HeightOneSpectrum (𝓞 K)) (hp : p ∈ T) : p ∉ S :=
    hS p ((p.prime.dvd_mul (a := I) (b := J)).mp ((hT p).mp hp))
  have hT6 (p : HeightOneSpectrum (𝓞 K)) (hp : p ∈ T) : (6 : 𝓞 K) ∉ p.asIdeal :=
    h6 p ((p.prime.dvd_mul (a := I) (b := J)).mp ((hT p).mp hp))
  have hTI (p : HeightOneSpectrum (𝓞 K)) (hp : p.asIdeal ∣ I) : p ∈ T :=
    (hT p).mpr ((p.prime.dvd_mul (a := I) (b := J)).mpr (Or.inl hp))
  have hTJ (p : HeightOneSpectrum (𝓞 K)) (hp : p.asIdeal ∣ J) : p ∈ T :=
    (hT p).mpr ((p.prime.dvd_mul (a := I) (b := J)).mpr (Or.inr hp))
  have hTIJ (p : HeightOneSpectrum (𝓞 K)) (hp : p.asIdeal ∣ I * J) : p ∈ T := (hT p).mpr hp
  let e : T → ℂ := fun p => sIntegerSexticEvaluation K S p.val
    (hTS p.val p.property) ζ hζ σ (hT6 p.val p.property) a
  have hprodIJ := sIntegerSexticIdealEvaluation_eq_prod_finite_support K S ζ hζ σ
    (I * J) (mul_ne_zero hI hJ)
    (fun p hp => hS p ((p.prime.dvd_mul (a := I) (b := J)).mp hp))
    (fun p hp => h6 p ((p.prime.dvd_mul (a := I) (b := J)).mp hp)) T hTS hT6 hTIJ a
  have hprodI := sIntegerSexticIdealEvaluation_eq_prod_finite_support K S ζ hζ σ
    I hI (fun p hp => hS p (Or.inl hp)) (fun p hp => h6 p (Or.inl hp))
    T hTS hT6 hTI a
  have hprodJ := sIntegerSexticIdealEvaluation_eq_prod_finite_support K S ζ hζ σ
    J hJ (fun p hp => hS p (Or.inr hp)) (fun p hp => h6 p (Or.inr hp))
    T hTS hT6 hTJ a
  have halg := prod_pow_of_add e
    (fun p => idealPrimeMultiplicity K p.val I)
    (fun p => idealPrimeMultiplicity K p.val J)
    (fun p => idealPrimeMultiplicity K p.val (I * J))
    (fun p => idealPrimeMultiplicity_mul K p.val I J hI hJ)
  exact hprodIJ.symm.trans (halg.trans (congrArg₂ (fun x y : ℂ => x * y) hprodI hprodJ))

variable (hS6 : integerPrimeSupport (6 : 𝓞 K) ⊆ S)

/-- Multiplication is the literal nonzero S-integer product, not a
coprime-ideal surrogate. The numerator may be zero. -/
theorem sIntegerSexticSymbol_mul_denominator
    (a : S.integer K) (c d : NonzeroRingElements (S.integer K)) :
    sIntegerSexticSymbol K S ζ hζ σ hS6 a
      ⟨c.val * d.val, mul_ne_zero c.property d.property⟩ =
      sIntegerSexticSymbol K S ζ hζ σ hS6 a c *
        sIntegerSexticSymbol K S ζ hζ σ hS6 a d := by
  have hexterior (z : NonzeroRingElements (S.integer K)) (p : HeightOneSpectrum (𝓞 K))
      (hp : p.asIdeal ∣ sIntegerModulusContraction K S z.val) : p ∉ S := by
    intro hpS
    have hc := sIntegerModulusContraction_coprime K S z.val z.property p hpS
    rw [sup_eq_right.mpr (Ideal.dvd_iff_le.mp hp)] at hc
    exact p.isPrime.ne_top hc
  have hS (p : HeightOneSpectrum (𝓞 K))
      (hp : p.asIdeal ∣ sIntegerModulusContraction K S c.val ∨
        p.asIdeal ∣ sIntegerModulusContraction K S d.val) : p ∉ S :=
    hp.elim (hexterior c p) (hexterior d p)
  have h6 (p : HeightOneSpectrum (𝓞 K))
      (hp : p.asIdeal ∣ sIntegerModulusContraction K S c.val ∨
        p.asIdeal ∣ sIntegerModulusContraction K S d.val) : (6 : 𝓞 K) ∉ p.asIdeal :=
    fun h => hS p hp (hS6 h)
  unfold sIntegerSexticSymbol
  simp only [sIntegerModulusContraction_mul K S c.val d.val c.property d.property]
  exact sIntegerSexticIdealEvaluation_mul_denominator K S ζ hζ σ _ _
    (sIntegerModulusContraction_ne_bot K S c.val c.property)
    (sIntegerModulusContraction_ne_bot K S d.val d.property) hS h6 a

end HeckeGeneral.Characters
