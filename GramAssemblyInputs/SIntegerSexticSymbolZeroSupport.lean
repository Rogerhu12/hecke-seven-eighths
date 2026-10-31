import HeckeGeneral.Characters.SIntegerSexticSymbol
import HeckeGeneral.Characters.SIntegerSexticPowerMask

/-! SOURCE ONLY, UNRUN. Exact common-prime zero support of the actual
two-argument S-integer sextic symbol. Extension/contraction identifies the
actual exterior residue kernel with divisibility of the numerator ideal.
The zero branch of reciprocity is therefore symmetric, independently of
any Hilbert-symbol identity or nonzero-value reciprocity theorem. -/

noncomputable section
namespace HeckeGeneral.Characters
open NumberField IsDedekindDomain HeckeGeneral.Arithmetic
open scoped Classical

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Finite S]

-- `sIntegerSexticResidueMap_eq_zero_iff_dvd_contraction` is provided by
-- `HeckeGeneral.Characters.SIntegerSexticPowerMask` (identical statement).


variable (ζ : K) (hζ : IsPrimitiveRoot ζ 6) (σ : K →+* ℂ)
variable (hS6 : integerPrimeSupport (6 : 𝓞 K) ⊆ S)
local notation "N" => NonzeroRingElements (S.integer K)

/-- The literal symbol vanishes exactly on common exterior prime support.
Multiplicities divisible by six retain their zero factor. -/
theorem sIntegerSexticSymbol_eq_zero_iff_commonPrime (a b : N) :
    sIntegerSexticSymbol K S ζ hζ σ hS6 a.val b = 0 ↔
      ∃ p : HeightOneSpectrum (𝓞 K),
        p.asIdeal ∣ sIntegerModulusContraction K S b.val ∧
        p.asIdeal ∣ sIntegerModulusContraction K S a.val := by
  unfold sIntegerSexticSymbol
  rw [sIntegerSexticIdealEvaluation_eq_zero_iff]
  simp only [sIntegerSexticResidueMap_eq_zero_iff_dvd_contraction, exists_prop]

/-- The two sides of S-integer reciprocity have the SAME zero set, before
the reciprocity law on the complementary nonzero locus is supplied. -/
theorem sIntegerSexticSymbol_eq_zero_swap_iff (a b : N) :
    sIntegerSexticSymbol K S ζ hζ σ hS6 a.val b = 0 ↔
      sIntegerSexticSymbol K S ζ hζ σ hS6 b.val a = 0 := by
  rw [sIntegerSexticSymbol_eq_zero_iff_commonPrime,
    sIntegerSexticSymbol_eq_zero_iff_commonPrime]
  constructor
  · rintro ⟨p, hb, ha⟩
    exact ⟨p, ha, hb⟩
  · rintro ⟨p, ha, hb⟩
    exact ⟨p, hb, ha⟩

end HeckeGeneral.Characters
