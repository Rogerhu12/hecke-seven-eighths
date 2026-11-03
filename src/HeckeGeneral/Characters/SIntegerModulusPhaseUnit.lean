import HeckeGeneral.Characters.SIntegerModulusPhase
import Mathlib.Algebra.Group.Pi.Units

/-!
# The actual unit correction for an S-integer principal phase

When S contains the different support, the h/c frequency at h = 1 is a
unit of the genuine quotient by c. Its local representative is
`-pi^n / c`, whose valuation is exactly one. The resulting unit shift of
the canonical primitive character is the literal positive S-local phase.
The frequency formula applies to every h, including nonunits.
-/

noncomputable section

namespace HeckeGeneral.Characters

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic
open IsDedekindDomain.HeightOneSpectrum
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → localDifferentExponent K v = 0)

/-- The actual quotient frequency at one is a unit, by the valuation of
each completed representative rather than a supplied invertibility input. -/
theorem isUnit_sIntegerDivModulusFrequency_one
    (c : S.integer K) (hc : c ≠ 0) :
    IsUnit (sIntegerDivModulusFrequency K S hS c hc 1) := by
  let e := sIntegerModulusCRT K S c hc
  have hlocal : ∀ v : sIntegerModulusPlaces K S c hc,
      IsUnit (e (sIntegerDivModulusFrequency K S hS c hc 1) v) := by
    intro v
    let n := sIntegerModulusPrimeExponents K S c hc v.val
    let ξ : v.val.adicCompletion K :=
      algebraMap K (v.val.adicCompletion K) ((1 : K) / (c : K))
    have hξ : Valued.v ξ ≤ WithZero.exp ((n : ℤ) + localDifferentExponent K v.val) := by
      rw [hS v.val (sIntegerModulusPlaces_not_mem K S c hc v), add_zero]
      exact sInteger_div_modulus_completion_valuation_le K S c hc 1 v.val
        (sIntegerModulusPlaces_not_mem K S c hc v)
    let b : LocalIntegerRing K v.val := localCanonicalFrequencyInteger K v.val n ξ hξ
    have hξeq : Valued.v ξ = WithZero.exp (n : ℤ) := by
      dsimp only [ξ]
      rw [one_div, map_inv₀, map_inv₀,
        sIntegerModulus_completion_valuation K S c hc v.val
          (sIntegerModulusPlaces_not_mem K S c hc v),
        ← WithZero.exp_neg, neg_neg]
    have hπ : Valued.v (localUniformizer K v.val ^ (n : ℤ)) =
        WithZero.exp (-(n : ℤ)) := by
      rw [map_zpow₀, localUniformizer_valuation, ← WithZero.exp_zsmul]
      congr 1
      simp
    have hbval : Valued.v (b : v.val.adicCompletion K) = 1 := by
      change Valued.v (-ξ * localUniformizer K v.val ^
        ((n : ℤ) + localDifferentExponent K v.val)) = 1
      rw [hS v.val (sIntegerModulusPlaces_not_mem K S c hc v), add_zero,
        map_mul, Valuation.map_neg, hξeq, hπ, ← WithZero.exp_add]
      simp
    have hb : IsUnit b :=
      adicCompletionIntegers.isUnit_iff_valued_eq_one.mpr hbval
    have hres : IsUnit (Ideal.Quotient.mk (localMaximalIdeal K v.val ^ n) b) :=
      hb.map (Ideal.Quotient.mk (localMaximalIdeal K v.val ^ n)).toMonoidHom
    change IsUnit (sIntegerModulusCRT K S c hc
      (sIntegerDivModulusFrequency K S hS c hc 1) v)
    unfold sIntegerDivModulusFrequency
    rw [sIntegerModulusCRT_frequency]
    exact hres
  have hpi : IsUnit (e (sIntegerDivModulusFrequency K S hS c hc 1)) :=
    Pi.isUnit_iff.mpr hlocal
  have hback := hpi.map e.symm.toMonoidHom
  change IsUnit (e.symm (e (sIntegerDivModulusFrequency K S hS c hc 1))) at hback
  simpa only [RingEquiv.symm_apply_apply] using hback

/-- The genuine residue unit correcting the canonical character to h/c. -/
def sIntegerModulusPhaseUnit (c : S.integer K) (hc : c ≠ 0) :
    (S.integer K ⧸ Ideal.span ({c} : Set (S.integer K)))ˣ :=
  (isUnit_sIntegerDivModulusFrequency_one K S hS c hc).unit

@[simp] theorem sIntegerModulusPhaseUnit_val (c : S.integer K) (hc : c ≠ 0) :
    (sIntegerModulusPhaseUnit K S hS c hc :
      S.integer K ⧸ Ideal.span ({c} : Set (S.integer K))) =
        sIntegerDivModulusFrequency K S hS c hc 1 :=
  (isUnit_sIntegerDivModulusFrequency_one K S hS c hc).unit_spec

/-- Every h/c frequency is the fixed unit correction times h modulo c.
There is no assumption that h itself is invertible. -/
theorem sIntegerDivModulusFrequency_eq_phaseUnit_mul
    (c : S.integer K) (hc : c ≠ 0) (h : S.integer K) :
    sIntegerDivModulusFrequency K S hS c hc h =
      (sIntegerModulusPhaseUnit K S hS c hc :
        S.integer K ⧸ Ideal.span ({c} : Set (S.integer K))) *
          Ideal.Quotient.mk (Ideal.span ({c} : Set (S.integer K))) h := by
  rw [sIntegerModulusPhaseUnit_val]
  apply AddChar.to_mulShift_inj_of_isPrimitive
    (sIntegerModulusAddCharacter_isPrimitive K S c hc)
  ext b
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
  simp only [AddChar.mulShift_apply]
  calc
    _ = sLocalPrincipalPhase K S (((h : K) * (a : K)) / (c : K)) :=
      (sLocalPrincipalPhase_eq_modulusCharacter K S hS c hc h a).symm
    _ = sIntegerModulusAddCharacter K S c hc
        (sIntegerDivModulusFrequency K S hS c hc 1 *
          Ideal.Quotient.mk (Ideal.span ({c} : Set (S.integer K))) (h * a)) := by
      simpa using sLocalPrincipalPhase_eq_modulusCharacter K S hS c hc 1 (h * a)
    _ = _ := by
      rw [map_mul (Ideal.Quotient.mk (Ideal.span ({c} : Set (S.integer K)))), mul_assoc]

/-- The actual principal-phase character, with its normalization correction retained. -/
def sIntegerActualModulusAddCharacter (c : S.integer K) (hc : c ≠ 0) :
    AddChar (S.integer K ⧸ Ideal.span ({c} : Set (S.integer K))) ℂ :=
  (sIntegerModulusAddCharacter K S c hc).mulShift
    (sIntegerModulusPhaseUnit K S hS c hc).val

/-- A genuine unit shift preserves primitivity, also for a trivial quotient ring. -/
theorem sIntegerActualModulusAddCharacter_isPrimitive
    (c : S.integer K) (hc : c ≠ 0) :
    (sIntegerActualModulusAddCharacter K S hS c hc).IsPrimitive := by
  intro a ha htrivial
  have hba : (sIntegerModulusPhaseUnit K S hS c hc).val * a ≠ 0 := by
    intro hzero
    exact ha ((Units.mul_right_eq_zero (sIntegerModulusPhaseUnit K S hS c hc)).mp hzero)
  apply (sIntegerModulusAddCharacter_isPrimitive K S c hc) hba
  simpa only [sIntegerActualModulusAddCharacter, AddChar.mulShift_mulShift] using htrivial

/-- Literal equality with the standard S-local principal phase, at every S-integer. -/
theorem sIntegerActualModulusAddCharacter_mk
    (c : S.integer K) (hc : c ≠ 0) (a : S.integer K) :
    sIntegerActualModulusAddCharacter K S hS c hc
        (Ideal.Quotient.mk (Ideal.span ({c} : Set (S.integer K))) a) =
      sLocalPrincipalPhase K S ((a : K) / (c : K)) := by
  rw [sIntegerActualModulusAddCharacter, AddChar.mulShift_apply,
    sIntegerModulusPhaseUnit_val]
  simpa using (sLocalPrincipalPhase_eq_modulusCharacter K S hS c hc 1 a).symm

end HeckeGeneral.Characters
