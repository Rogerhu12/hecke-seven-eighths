import HeckeGeneral.Arithmetic.SIntegerModulus
import HeckeGeneral.Arithmetic.IdealFactorization

/-!
# Completed local residues of an actual S-integer modulus

The finite index set and exponents come from the actual contraction of
the principal modulus. The CRT coordinates are the literal completed
local reductions of every S-integer, including those with denominators.
-/

noncomputable section

namespace HeckeGeneral.Arithmetic

open NumberField IsDedekindDomain UniqueFactorizationMonoid HeckeGeneral.Characters
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Finite S]

def sIntegerModulusPrimeExponents (c : S.integer K) (hc : c ≠ 0) :
    HeightOneSpectrum (𝓞 K) →₀ ℕ :=
  primeExponents ⟨sIntegerModulusContraction K S c,
    mem_nonZeroDivisors_of_ne_zero (sIntegerModulusContraction_ne_bot K S c hc)⟩

abbrev sIntegerModulusPlaces (c : S.integer K) (hc : c ≠ 0) :=
  (sIntegerModulusPrimeExponents K S c hc).support

theorem sIntegerModulusPlaces_not_mem (c : S.integer K) (hc : c ≠ 0)
    (v : sIntegerModulusPlaces K S c hc) : v.val ∉ S := by
  intro hvS
  have hmem : v.val.asIdeal ∈
      normalizedFactors (sIntegerModulusContraction K S c) := by
    apply Multiset.count_ne_zero.mp
    exact Finsupp.mem_support_iff.mp v.property
  have hle := (Ideal.mem_normalizedFactors_iff
    (sIntegerModulusContraction_ne_bot K S c hc)).mp hmem
  have hcop := sIntegerModulusContraction_coprime K S c hc v.val hvS
  rw [sup_eq_right.mpr hle.2] at hcop
  exact v.val.isPrime.ne_top hcop

theorem sIntegerModulus_primePower_product (c : S.integer K) (hc : c ≠ 0) :
    (∏ v : sIntegerModulusPlaces K S c hc,
      v.val.asIdeal ^ sIntegerModulusPrimeExponents K S c hc v.val) =
        sIntegerModulusContraction K S c := by
  calc
    _ = (idealOfPrimeExponents (sIntegerModulusPrimeExponents K S c hc)).val :=
      Finset.prod_coe_sort (sIntegerModulusPrimeExponents K S c hc).support
        (fun v => v.asIdeal ^ sIntegerModulusPrimeExponents K S c hc v)
    _ = _ := congrArg Subtype.val (idealOfPrimeExponents_primeExponents _)

/-- The genuine product of the completed prime-power residue rings. -/
abbrev SIntegerModulusLocalResidues (c : S.integer K) (hc : c ≠ 0) :=
  ∀ v : sIntegerModulusPlaces K S c hc,
    LocalResidueRing K v.val (sIntegerModulusPrimeExponents K S c hc v.val)

/-- The CRT for the actual principal quotient, with no supplied factorization. -/
def sIntegerModulusCRT (c : S.integer K) (hc : c ≠ 0) :
    (S.integer K ⧸ Ideal.span ({c} : Set (S.integer K))) ≃+*
      SIntegerModulusLocalResidues K S c hc :=
  (Ideal.quotEquivOfEq (map_sIntegerModulusContraction K S c).symm).trans
    (sIntegerResidueCRT K S (sIntegerModulusContraction K S c)
      (sIntegerModulusContraction_coprime K S c hc)
      (fun v : sIntegerModulusPlaces K S c hc => v.val)
      (fun v => sIntegerModulusPrimeExponents K S c hc v.val)
      (fun _ _ h => Subtype.val_injective.ne h)
      (sIntegerModulus_primePower_product K S c hc))

@[simp] theorem sIntegerModulusCRT_mk (c : S.integer K) (hc : c ≠ 0)
    (a : S.integer K) (v : sIntegerModulusPlaces K S c hc) :
    sIntegerModulusCRT K S c hc
        (Ideal.Quotient.mk (Ideal.span ({c} : Set (S.integer K))) a) v =
      sIntegerToLocalResidue K S v.val (sIntegerModulusPlaces_not_mem K S c hc v)
        (sIntegerModulusPrimeExponents K S c hc v.val) a := by
  unfold sIntegerModulusCRT
  simp only [RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
  exact sIntegerResidueCRT_apply_mk K S _ _ _ _ _ _ a v
    (sIntegerModulusPlaces_not_mem K S c hc v)

end HeckeGeneral.Arithmetic
