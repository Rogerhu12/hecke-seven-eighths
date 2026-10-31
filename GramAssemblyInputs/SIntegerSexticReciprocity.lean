import SIntegerSexticSymbolZeroSupport
import SIntegerSexticLocalHilbertRatio
import SIntegerSexticIdealEvaluationFiniteSupport
import SIntegerExteriorHilbertSupport
import HeckeGeneral.Characters.SexticPowerResidueComparison

/-! SOURCE ONLY, UNRUN. General zero-extended S-integer sextic reciprocity
for the literal denominator contractions and the actual ALL-S correction.
All local ratios, product/support transports and zero masks are proved in
imports. No integrality, PID or reciprocity hypothesis is supplied. -/
noncomputable section
namespace HeckeGeneral.Characters
open NumberField IsDedekindDomain HeckeGeneral.Arithmetic KummerTheory
open GlobalClassFieldTheory.Reciprocity AlgebraicNumberTheory.PowerResidueSymbols
open scoped Classical BigOperators
variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (ζ : K) (hζ : IsPrimitiveRoot ζ 6) (σ : K →+* ℂ)
variable (hS6 : integerPrimeSupport (6 : 𝓞 K) ⊆ S)
local notation "NZI" => NonzeroRingElements (S.integer K)
local notation "U" => nonzeroSIntegerFieldUnit K S
local notation "χ" => sIntegerSexticSymbol K S ζ hζ σ hS6

set_option maxHeartbeats 800000 in
/-- All nonzero S-integers, including the common-prime zero locus. -/
theorem sIntegerSexticSymbol_reciprocity (a b : NZI) :
    χ a.val b =
      σ (((sIntegerSexticSPlaceCorrection K S ζ hζ (U a) (U b))⁻¹).val : K) *
        χ b.val a := by
  by_cases hz : χ a.val b = 0
  · have hs : χ b.val a = 0 :=
      (sIntegerSexticSymbol_eq_zero_swap_iff K S ζ hζ σ hS6 a b).mp hz
    rw [hz, hs, mul_zero]
  have hb : χ b.val a ≠ 0 := by
    intro hb
    exact hz ((sIntegerSexticSymbol_eq_zero_swap_iff K S ζ hζ σ hS6 a b).mpr hb)
  have hab (p : HeightOneSpectrum (𝓞 K)) :
      ¬ (p.asIdeal ∣ sIntegerModulusContraction K S a.val ∧
        p.asIdeal ∣ sIntegerModulusContraction K S b.val) := by
    rintro ⟨ha, hb⟩
    exact hz ((sIntegerSexticSymbol_eq_zero_iff_commonPrime K S ζ hζ σ hS6 a b).mpr
      ⟨p, hb, ha⟩)
  let T := sIntegerSexticHilbertTotalSupport K S (U a) (U b) \ S.toFinset
  have hTS (p : HeightOneSpectrum (𝓞 K)) (hp : p ∈ T) : p ∉ S := by
    exact fun h => (Finset.mem_sdiff.mp hp).2 (Set.mem_toFinset.mpr h)
  have hT6 (p : HeightOneSpectrum (𝓞 K)) (hp : p ∈ T) : (6 : 𝓞 K) ∉ p.asIdeal :=
    fun h => hTS p hp (hS6 h)
  let E : T → S.integer K → ℂ := fun p =>
    sIntegerSexticEvaluation K S p.val (hTS p.val p.property)
      ζ hζ σ (hT6 p.val p.property)
  have hprod (c : NZI)
      (hcT : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ sIntegerModulusContraction K S c.val → p ∈ T)
      (z : S.integer K) :
      (∏ p : T, E p z ^ idealPrimeMultiplicity K p
        (sIntegerModulusContraction K S c.val)) = χ z c := by
    have hcS (p : HeightOneSpectrum (𝓞 K)) (hp : p.asIdeal ∣ sIntegerModulusContraction K S c.val) : p ∉ S :=
      (sInteger_contraction_prime_mem_chosenHilbertSupport K S c p hp).1
    have hc6 (p : HeightOneSpectrum (𝓞 K)) (hp : p.asIdeal ∣ sIntegerModulusContraction K S c.val) :
        (6 : 𝓞 K) ∉ p.asIdeal := fun h => hcS p hp (hS6 h)
    exact sIntegerSexticIdealEvaluation_eq_prod_finite_support K S ζ hζ σ
      (sIntegerModulusContraction K S c.val)
      (sIntegerModulusContraction_ne_bot K S c.val c.property)
      hcS hc6 T hTS hT6 hcT z
  have haT (p : HeightOneSpectrum (𝓞 K)) (hp : p.asIdeal ∣ sIntegerModulusContraction K S a.val) : p ∈ T :=
    sInteger_contraction_primes_mem_exteriorHilbertSupport K S a b p (Or.inl hp)
  have hbT (p : HeightOneSpectrum (𝓞 K)) (hp : p.asIdeal ∣ sIntegerModulusContraction K S b.val) : p ∈ T :=
    sInteger_contraction_primes_mem_exteriorHilbertSupport K S a b p (Or.inr hp)
  have h6' : (((6 : ℕ+) : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (by norm_num)
  have hmu6 : (primitiveRoots (((6 : ℕ+) : ℕ)) K).Nonempty := sPlaceCorrectionSexticRoots K ζ hζ
  let Ψ : nthRootsSubgroup K (((6 : ℕ+) : ℕ)) →* ℂ :=
    σ.toMonoidHom.comp ((Units.coeHom K).comp (nthRootsSubgroup K (((6 : ℕ+) : ℕ))).subtype)
  have hratio : Ψ (sIntegerSexticExteriorHilbertProduct K S ζ hζ (U a) (U b)) =
      χ a.val b / χ b.val a := by
    calc
      _ = ∏ p : T, Ψ (finitePlaceHilbertSymbol K (6 : ℕ+) h6' hmu6 p.val (U a) (U b)) := by
        have h1 : sIntegerSexticExteriorHilbertProduct K S ζ hζ (U a) (U b) =
            ∏ p : T, finitePlaceHilbertSymbol K (6 : ℕ+) h6' hmu6 p.val (U a) (U b) :=
          (Finset.prod_coe_sort T _).symm
        rw [h1]
        exact map_prod Ψ _ _
      _ = (∏ p : T, E p a.val ^ idealPrimeMultiplicity K p
          (sIntegerModulusContraction K S b.val)) /
          (∏ p : T, E p b.val ^ idealPrimeMultiplicity K p
          (sIntegerModulusContraction K S a.val)) := by
        rw [← Finset.prod_div_distrib]
        apply Finset.prod_congr rfl
        intro p _
        exact sIntegerSextic_local_hilbert_ratio K S ζ hζ σ
          hmu6 p.val (hTS p.val p.property)
          (hT6 p.val p.property)
          (specifiedSexticNormCoprime K ζ hζ p.val (hT6 p.val p.property)) a b (hab p.val)
      _ = _ := by rw [hprod b hbT a.val, hprod a haT b.val]
  rw [sIntegerSexticExteriorHilbertProduct_eq_SPlaceCorrection_inv] at hratio
  calc
    χ a.val b = (χ a.val b / χ b.val a) * χ b.val a := (div_mul_cancel₀ _ hb).symm
    _ = _ := by rw [← hratio]; rfl
end HeckeGeneral.Characters

