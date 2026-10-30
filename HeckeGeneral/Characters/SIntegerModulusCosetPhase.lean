import HeckeGeneral.Characters.SIntegerModulusPhaseUnit

/-!
# The actual exterior phase on modulus cosets

The negative local Fourier phase is the genuine principal quotient character.
The identities hold for all representatives, including zero and nonunits.
-/

noncomputable section

namespace HeckeGeneral.Characters

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic NumberField.StandardAddChar
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → localDifferentExponent K v = 0)

/-- The literal local Fourier phase equals the actual quotient character. -/
theorem sIntegerModulusCosetPhase_eq
    (c : S.integer K) (hc : c ≠ 0) (a b : S.integer K) :
    (∏ v : sIntegerModulusPlaces K S c hc,
      psiLocal K v.val
        (-(algebraMap K (v.val.adicCompletion K) (b : K) *
          algebraMap K (v.val.adicCompletion K) ((a : K) / (c : K))))) =
      sIntegerActualModulusAddCharacter K S hS c hc
        (Ideal.Quotient.mk (Ideal.span ({c} : Set (S.integer K))) a *
          Ideal.Quotient.mk (Ideal.span ({c} : Set (S.integer K))) b) := by
  calc
    _ = ∏ v : sIntegerModulusPlaces K S c hc,
        psiLocal K v.val
          (-(algebraMap K (v.val.adicCompletion K) (((a * b : S.integer K) : K) /
            (c : K)))) := by
      apply Finset.prod_congr rfl
      intro v _hv
      apply congrArg (psiLocal K v.val)
      apply congrArg Neg.neg
      rw [← map_mul]
      congr 1
      change (b : K) * ((a : K) / (c : K)) = ((a : K) * (b : K)) / (c : K)
      ring
    _ = sLocalPrincipalPhase K S (((a * b : S.integer K) : K) / (c : K)) :=
      (sLocalPrincipalPhase_div_modulus_eq_exterior K S c hc (a * b)).symm
    _ = sIntegerActualModulusAddCharacter K S hS c hc
        (Ideal.Quotient.mk (Ideal.span ({c} : Set (S.integer K))) (a * b)) :=
      (sIntegerActualModulusAddCharacter_mk K S hS c hc (a * b)).symm
    _ = _ := by rw [map_mul]

/-- A chosen representative of any residue class gives the same actual phase. -/
theorem sIntegerModulusCosetPhase_out_eq
    (c : S.integer K) (hc : c ≠ 0) (a : S.integer K)
    (r : S.integer K ⧸ Ideal.span ({c} : Set (S.integer K))) :
    (∏ v : sIntegerModulusPlaces K S c hc,
      psiLocal K v.val
        (-(algebraMap K (v.val.adicCompletion K) ((Quotient.out r : S.integer K) : K) *
          algebraMap K (v.val.adicCompletion K) ((a : K) / (c : K))))) =
      sIntegerActualModulusAddCharacter K S hS c hc
        (Ideal.Quotient.mk (Ideal.span ({c} : Set (S.integer K))) a * r) := by
  simpa only [Ideal.Quotient.mk_out] using
    sIntegerModulusCosetPhase_eq K S hS c hc a (Quotient.out r)

end HeckeGeneral.Characters
