import SIntegerSexticSymbolZeroSupport

/-! SOURCE ONLY, UNRUN. The actual absence of common contracted prime
divisors supplies Bezout coefficients in O_S. This is the coprimality
needed by the affine correlation parametrization; no PID assumption or
coprimality with its common modulus is added. -/
noncomputable section
namespace HeckeGeneral.Characters
open NumberField IsDedekindDomain HeckeGeneral.Arithmetic
open scoped Classical
variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Finite S]
local notation "N" => NonzeroRingElements (S.integer K)

theorem sInteger_isCoprime_iff_no_common_contracted_prime (a b : N) :
    IsCoprime a.val b.val ↔
      ∀ p : HeightOneSpectrum (𝓞 K),
        ¬ (p.asIdeal ∣ sIntegerModulusContraction K S a.val ∧
          p.asIdeal ∣ sIntegerModulusContraction K S b.val) := by
  constructor
  · rintro ⟨x, y, hxy⟩ p ⟨ha, hb⟩
    have hpS : p ∉ S := by
      intro hp
      have hc := sIntegerModulusContraction_coprime K S a.val a.property p hp
      have htop : (⊤ : Ideal (𝓞 K)) ≤ p.asIdeal := by
        rw [← hc]
        exact sup_le (Ideal.dvd_iff_le.mp ha) le_rfl
      exact p.isPrime.ne_top (top_le_iff.mp htop)
    letI coprimeColumns_residueField : Field (𝓞 K ⧸ p.asIdeal) := Ideal.Quotient.field _
    have ha0 := (sIntegerSexticResidueMap_eq_zero_iff_dvd_contraction K S p hpS a.val).mpr ha
    have hb0 := (sIntegerSexticResidueMap_eq_zero_iff_dvd_contraction K S p hpS b.val).mpr hb
    have hz : (0 : 𝓞 K ⧸ p.asIdeal) = 1 := by
      simpa only [map_add, map_mul, map_one, ha0, hb0, mul_zero, zero_add] using
        congrArg (sIntegerSexticResidueMap K S p hpS) hxy
    exact zero_ne_one hz
  · intro hab
    have hsup : sIntegerModulusContraction K S a.val ⊔
        sIntegerModulusContraction K S b.val = ⊤ := by
      by_contra hne
      obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
      have hP0 : P ≠ ⊥ := by
        intro hz
        apply sIntegerModulusContraction_ne_bot K S a.val a.property
        apply le_bot_iff.mp
        exact (le_sup_left.trans hle).trans_eq hz
      let p : HeightOneSpectrum (𝓞 K) := ⟨P, hP.isPrime, hP0⟩
      exact hab p ⟨Ideal.dvd_iff_le.mpr (le_sup_left.trans hle),
        Ideal.dvd_iff_le.mpr (le_sup_right.trans hle)⟩
    apply (Ideal.sup_eq_top_iff_isCoprime a.val b.val).mp
    have hmap := congrArg (Ideal.map (algebraMap (𝓞 K) (S.integer K))) hsup
    simpa only [Ideal.map_sup, Ideal.map_top, map_sIntegerModulusContraction] using hmap

/-- The signed Bezout identity used in the literal affine fibre. -/
theorem exists_sInteger_affine_bezout_of_no_common_prime (a b : N)
    (hab : ∀ p : HeightOneSpectrum (𝓞 K),
      ¬ (p.asIdeal ∣ sIntegerModulusContraction K S a.val ∧
        p.asIdeal ∣ sIntegerModulusContraction K S b.val)) :
    ∃ x y : S.integer K, x * b.val - y * a.val = 1 := by
  obtain ⟨u, v, huv⟩ := (sInteger_isCoprime_iff_no_common_contracted_prime K S a b).mpr hab
  refine ⟨v, -u, ?_⟩
  calc
    v * b.val - (-u) * a.val = u * a.val + v * b.val := by ring
    _ = 1 := huv

/-- Reduction to any common modulus preserves the needed coprimality. -/
theorem sInteger_quotient_isCoprime_of_no_common_prime
    (I : Ideal (S.integer K)) (a b : N)
    (hab : ∀ p : HeightOneSpectrum (𝓞 K),
      ¬ (p.asIdeal ∣ sIntegerModulusContraction K S a.val ∧
        p.asIdeal ∣ sIntegerModulusContraction K S b.val)) :
    IsCoprime (Ideal.Quotient.mk I a.val) (Ideal.Quotient.mk I b.val) :=
  ((sInteger_isCoprime_iff_no_common_contracted_prime K S a b).mpr hab).map
    (Ideal.Quotient.mk I)

variable (ζ : K) (hζ : IsPrimitiveRoot ζ 6) (σ : K →+* ℂ)
variable (hS6 : integerPrimeSupport (6 : 𝓞 K) ⊆ S)

/-- At frequency zero the symbol survives precisely at unit denominators.
This is a separate formula, with no use of a nonzero-frequency period. -/
theorem sIntegerSexticSymbol_zero_numerator (c : N) :
    sIntegerSexticSymbol K S ζ hζ σ hS6 0 c =
      if IsUnit c.val then 1 else 0 := by
  split_ifs with hc
  · exact sIntegerSexticSymbol_unit_denominator K S ζ hζ σ hS6 0 c hc
  · have hI : sIntegerModulusContraction K S c.val ≠ ⊤ := by
      intro htop
      have hmap := map_sIntegerModulusContraction K S c.val
      rw [htop, Ideal.map_top] at hmap
      exact hc (Ideal.span_singleton_eq_top.mp hmap.symm)
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hI
    have hP0 : P ≠ ⊥ := by
      intro hz
      exact sIntegerModulusContraction_ne_bot K S c.val c.property
        (le_bot_iff.mp (hle.trans_eq hz))
    let p : HeightOneSpectrum (𝓞 K) := ⟨P, hP.isPrime, hP0⟩
    exact sIntegerSexticSymbol_eq_zero_of_badPrime K S ζ hζ σ hS6 0 c p
      (Ideal.dvd_iff_le.mpr hle) (map_zero _)

theorem sIntegerSextic_zero_frequency_raw_support (a b : N) :
    sIntegerSexticSymbol K S ζ hζ σ hS6 0 a *
        starRingEnd ℂ (sIntegerSexticSymbol K S ζ hζ σ hS6 0 b) =
      if IsUnit a.val ∧ IsUnit b.val then 1 else 0 := by
  by_cases ha : IsUnit a.val <;> by_cases hb : IsUnit b.val <;>
    simp [sIntegerSexticSymbol_zero_numerator, ha, hb]
end HeckeGeneral.Characters
