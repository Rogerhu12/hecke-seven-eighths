import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.FieldTheory.Finite.Basic

/-!
# Reduction of a specified sixth root

The root in every residue field and the root in the complex numbers both
come from the same specified element of the number field. The excluded
primes are exactly those containing 6. Reduction preserves primitive order
by mapping the cyclotomic equation and using that 6 remains nonzero; the
quotient map itself is not assumed injective.
-/

noncomputable section

namespace HeckeGeneral.Characters

open NumberField IsDedekindDomain
open scoped Classical

/-- Cyclotomic roots remain primitive under a possibly noninjective ring map
when their order remains nonzero in the target domain. -/
theorem primitiveRoot_map_of_natCast_ne_zero
    {R T : Type*} [CommRing R] [IsDomain R] [CommRing T] [IsDomain T]
    {n : ℕ} {ζ : R} (hζ : IsPrimitiveRoot ζ n) (hn : 0 < n)
    (f : R →+* T) (hT : (n : T) ≠ 0) : IsPrimitiveRoot (f ζ) n := by
  letI : NeZero (n : T) := ⟨hT⟩
  apply Polynomial.isRoot_cyclotomic_iff.mp
  simpa only [Polynomial.map_cyclotomic] using
    (hζ.isRoot_cyclotomic hn).map (f := f)

variable (K : Type*) [Field K] [NumberField K]
variable (ζ : K) (hζ : IsPrimitiveRoot ζ 6)

/-- The specified root as an actual algebraic integer. -/
def sexticIntegerRoot : 𝓞 K :=
  ⟨ζ, hζ.isIntegral (by norm_num)⟩

@[simp] theorem coe_sexticIntegerRoot : (sexticIntegerRoot K ζ hζ : K) = ζ := rfl

theorem isPrimitiveRoot_sexticIntegerRoot :
    IsPrimitiveRoot (sexticIntegerRoot K ζ hζ) 6 :=
  hζ.of_map_of_injective (f := algebraMap (𝓞 K) K) RingOfIntegers.coe_injective

/-- The global integer unit supplies both residue and complex unit roots. -/
def sexticIntegerRootUnit : (𝓞 K)ˣ :=
  ((isPrimitiveRoot_sexticIntegerRoot K ζ hζ).isUnit (by norm_num)).unit

@[simp] theorem val_sexticIntegerRootUnit :
    (sexticIntegerRootUnit K ζ hζ : 𝓞 K) = sexticIntegerRoot K ζ hζ :=
  IsUnit.unit_spec _

theorem isPrimitiveRoot_sexticIntegerRootUnit :
    IsPrimitiveRoot (sexticIntegerRootUnit K ζ hζ) 6 :=
  (isPrimitiveRoot_sexticIntegerRoot K ζ hζ).isUnit_unit (by norm_num)

variable (p : HeightOneSpectrum (𝓞 K))

/-- Reduction uses the actual quotient map of the prime ideal. -/
def sexticResidueRootUnit : (𝓞 K ⧸ p.asIdeal)ˣ :=
  Units.map (Ideal.Quotient.mk p.asIdeal).toMonoidHom (sexticIntegerRootUnit K ζ hζ)

@[simp] theorem val_sexticResidueRootUnit :
    (sexticResidueRootUnit K ζ hζ p : 𝓞 K ⧸ p.asIdeal) =
      Ideal.Quotient.mk p.asIdeal (sexticIntegerRoot K ζ hζ) := by
  change Ideal.Quotient.mk p.asIdeal (sexticIntegerRootUnit K ζ hζ : 𝓞 K) = _
  rw [val_sexticIntegerRootUnit]

theorem residue_six_ne_zero (hp : (6 : 𝓞 K) ∉ p.asIdeal) :
    (6 : 𝓞 K ⧸ p.asIdeal) ≠ 0 := by
  intro h
  apply hp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  simpa only [map_ofNat] using h

/-- The bad-prime condition has its literal ideal-membership meaning. -/
theorem residue_characteristic_not_dvd_six_iff (ℓ : ℕ)
    [CharP (𝓞 K ⧸ p.asIdeal) ℓ] :
    ¬ ℓ ∣ 6 ↔ (6 : 𝓞 K) ∉ p.asIdeal := by
  have hzero : (6 : 𝓞 K ⧸ p.asIdeal) = 0 ↔ (6 : 𝓞 K) ∈ p.asIdeal := by
    simpa only [map_ofNat] using
      (Ideal.Quotient.eq_zero_iff_mem (I := p.asIdeal) (a := (6 : 𝓞 K)))
  exact not_congr ((CharP.cast_eq_zero_iff (𝓞 K ⧸ p.asIdeal) ℓ 6).symm.trans hzero)

theorem isPrimitiveRoot_sexticResidueRootUnit (hp : (6 : 𝓞 K) ∉ p.asIdeal) :
    IsPrimitiveRoot (sexticResidueRootUnit K ζ hζ p) 6 := by
  apply IsPrimitiveRoot.coe_units_iff.mp
  rw [val_sexticResidueRootUnit]
  exact primitiveRoot_map_of_natCast_ne_zero
    (isPrimitiveRoot_sexticIntegerRoot K ζ hζ) (by norm_num)
    (Ideal.Quotient.mk p.asIdeal) (residue_six_ne_zero K p hp)

include hζ in
/-- Existence of the specified primitive root supplies the required finite
field divisibility; it is not a separate arithmetic assumption. -/
theorem six_dvd_card_residue_sub_one [Fintype (𝓞 K ⧸ p.asIdeal)]
    (hp : (6 : 𝓞 K) ∉ p.asIdeal) :
    6 ∣ Fintype.card (𝓞 K ⧸ p.asIdeal) - 1 := by
  letI : Field (𝓞 K ⧸ p.asIdeal) := Ideal.Quotient.field p.asIdeal
  rw [← Fintype.card_units]
  rw [(isPrimitiveRoot_sexticResidueRootUnit K ζ hζ p hp).eq_orderOf]
  exact orderOf_dvd_card

variable (σ : K →+* ℂ)

/-- The complex root is the image of the same global unit under the specified
embedding, rather than a newly selected primitive sixth root. -/
def sexticComplexRootUnit : ℂˣ :=
  Units.map (σ.comp (algebraMap (𝓞 K) K)).toMonoidHom (sexticIntegerRootUnit K ζ hζ)

@[simp] theorem val_sexticComplexRootUnit :
    (sexticComplexRootUnit K ζ hζ σ : ℂ) = σ ζ := by
  change σ (algebraMap (𝓞 K) K (sexticIntegerRootUnit K ζ hζ : 𝓞 K)) = σ ζ
  rw [val_sexticIntegerRootUnit]
  rfl

theorem isPrimitiveRoot_sexticComplexRootUnit :
    IsPrimitiveRoot (sexticComplexRootUnit K ζ hζ σ) 6 := by
  apply IsPrimitiveRoot.coe_units_iff.mp
  rw [val_sexticComplexRootUnit]
  exact hζ.map_of_injective σ.injective

/-- The matching used by a power-residue character is indexed by the same
power of the specified global root on both sides. -/
theorem sexticRoot_reduction_embedding_powers (i : ℕ) :
    ((sexticResidueRootUnit K ζ hζ p) ^ i : (𝓞 K ⧸ p.asIdeal)ˣ) =
        Units.map (Ideal.Quotient.mk p.asIdeal).toMonoidHom
          (sexticIntegerRootUnit K ζ hζ ^ i) ∧
      (sexticComplexRootUnit K ζ hζ σ) ^ i =
        Units.map (σ.comp (algebraMap (𝓞 K) K)).toMonoidHom
          (sexticIntegerRootUnit K ζ hζ ^ i) := by
  constructor <;> exact (map_pow _ _ _).symm

end HeckeGeneral.Characters
