import HeckeSkeleton.LowHybrid.ExteriorSymbol
import HeckeSkeleton.LowFrozenCube.FrozenReduction

/-!
# Frozen data on the actual exterior ideals

The arithmetic fields of `FrozenReduction.Data` are constructed from the
repository's exterior ideals, prime multiplicities and allowed generators.
Only the finite support, the ordinary subset, a genuine `Fin 6` digit at
each prime, and the frozen minimum remain to be chosen.  The constructor
`ofReflectionIndex` obtains these data directly from a `ReflectionIndex`.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.LowFrozenCube.Exterior

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.ThetaSkeleton
open HeckeGeneral.ThetaSkeleton.Global
open HeckeGeneral.Analysis.SquarefreeAmplification
open HeckeSkeleton.LowHybrid
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- The support used in marked reflection is precisely the nonzero prime
coordinate support used by the frozen-cube proof. -/
theorem mem_exteriorSupport_iff (I : ExteriorIdeal K S) (p : ExteriorPrime K S) :
    p ∈ exteriorSupport K S I ↔ primeExponents I.val p.val ≠ 0 := by
  constructor
  · intro hp
    obtain ⟨q, _, hq⟩ := Finset.mem_image.mp hp
    have he : q.val = p.val := congrArg Subtype.val hq
    have hqmem := q.property
    rw [he] at hqmem
    exact Finsupp.mem_support_iff.mp hqmem
  · intro hp
    let q : {p : HeightOneSpectrum (𝓞 K) // p ∈ idealPrimeSupport K I.val} :=
      ⟨p.val, Finsupp.mem_support_iff.mpr hp⟩
    exact Finset.mem_image.mpr ⟨q, Finset.mem_attach _ q, Subtype.ext rfl⟩

theorem supported_iff (s : Finset (ExteriorPrime K S)) (I : ExteriorIdeal K S) :
    PrimeCoordinates.Supported (ExteriorArithmetic.coords K S) s I ↔
      exteriorSupport K S I ⊆ s := by
  constructor
  · intro h p hp
    by_contra hps
    exact (mem_exteriorSupport_iff K S I p).mp hp (h p hps)
  · intro h p hp
    apply Classical.byContradiction
    intro hne
    exact hp (h ((mem_exteriorSupport_iff K S I p).mpr hne))

theorem avoids_iff (s : Finset (ExteriorPrime K S)) (I : ExteriorIdeal K S) :
    PrimeCoordinates.Avoids (ExteriorArithmetic.coords K S) s I ↔
      ∀ p ∈ s, ¬p.val.asIdeal ∣ I.val.val := by
  constructor
  · intro h p hp hdiv
    have hpos := (ExteriorArithmetic.primeExponents_pos_iff K I.val p.val).mpr hdiv
    have hz := h p hp
    change primeExponents I.val p.val = 0 at hz
    omega
  · intro h p hp
    change primeExponents I.val p.val = 0
    apply Nat.eq_zero_of_not_pos
    intro hpos
    exact h p hp ((ExteriorArithmetic.primeExponents_pos_iff K I.val p.val).mp hpos)

/-- Finite local choices only: all global arithmetic is supplied by the
actual exterior-ideal dictionary. -/
structure Data where
  support : Finset (ExteriorPrime K S)
  ordinary : Finset (ExteriorPrime K S)
  ordinary_subset : ordinary ⊆ support
  digit : ExteriorPrime K S → Fin 6
  minimum : ExteriorIdeal K S
  minimum_ordinary : exteriorSupport K S minimum ⊆ ordinary

variable (D : ThetaArithmeticData K S) (hD : AllowedGeneratorInput K S D)

namespace Data

/-- Actual ideal factorization and the actual allowed-generator symbol
discharge every arithmetic field in the frozen model. -/
def toFrozen (f : Data K S) :
    FrozenReduction.Data (ExteriorPrime K S) (ExteriorIdeal K S) where
  coords := ExteriorArithmetic.coords K S
  symbol := ExteriorSymbol.symbolHom K S D hD
  sixth := ExteriorSymbol.symbolHom_sixth K S D hD
  reciprocal := ExteriorSymbol.symbolHom_reciprocity K S D hD
  support := f.support
  ordinary := f.ordinary
  ordinary_subset := f.ordinary_subset
  digit p := (f.digit p).val
  minimum := f.minimum
  minimum_ordinary := (supported_iff K S f.ordinary f.minimum).mpr f.minimum_ordinary

@[simp] theorem toFrozen_coords (f : Data K S) :
    (f.toFrozen K S D hD).coords = ExteriorArithmetic.coords K S := rfl

@[simp] theorem toFrozen_symbol (f : Data K S) :
    (f.toFrozen K S D hD).symbol = ExteriorSymbol.symbolHom K S D hD := rfl

@[simp] theorem toFrozen_prime (f : Data K S) (p : ExteriorPrime K S) :
    (f.toFrozen K S D hD).prime p = exteriorPrimeIdeal K S p := by
  exact ExteriorArithmetic.prime_coords K S p

/-- The frozen ordinary-prime symbol is the original prime residue
evaluation on the allowed generator; reciprocity is used explicitly. -/
@[simp] theorem ordinarySymbol_eq (f : Data K S)
    (p : ExteriorPrime K S) (I : ExteriorIdeal K S) :
    (f.toFrozen K S D hD).ordinarySymbol p I =
      primeEvaluation K S D p (D.generator I) := by
  change ExteriorSymbol.symbol K S D I ((f.toFrozen K S D hD).prime p) = _
  rw [toFrozen_prime]
  exact ExteriorSymbol.symbol_prime_right K S D hD I p

@[simp] theorem valuation_eq (f : Data K S) (I : ExteriorIdeal K S)
    (p : ExteriorPrime K S) :
    PrimeCoordinates.valuation (f.toFrozen K S D hD).coords I p =
      primeExponents I.val p.val := rfl

end Data

/-- The original reflected index supplies a valid frozen datum.  Its
minimum is constructed coordinatewise; no splitting function is assumed. -/
def ofReflectionIndex (d : MarkedDatum K S) (i : ReflectionIndex K S d) : Data K S where
  support := frozenPrimes K S d
  ordinary := i.activeFrozen
  ordinary_subset := i.frozen_subset
  digit := rowDigit K S d
  minimum := PrimeCoordinates.minimumFactor (ExteriorArithmetic.coords K S) i.numeratorFrozen
  minimum_ordinary := (supported_iff K S _ _).mp
    (PrimeCoordinates.minimumFactor_supported (ExteriorArithmetic.coords K S) _ _
      ((supported_iff K S _ _).mpr i.frozen_support))

/-- The complete original numerator is the constructed minimum times its
constructed residual cube, using the actual reflected-index residue rule. -/
theorem numeratorFrozen_eq_minimum_mul_cube
    (d : MarkedDatum K S) (i : ReflectionIndex K S d) :
    i.numeratorFrozen = (ofReflectionIndex K S d i).minimum *
      PrimeCoordinates.residualCubeFactor (ExteriorArithmetic.coords K S)
        i.numeratorFrozen ^ 3 := by
  apply PrimeCoordinates.minimum_mul_residualCube
  intro p
  have h := i.frozen_digits p
  have hm := Nat.mod_lt (primeExponents i.numeratorFrozen.val p.val) (by decide : 0 < 3)
  change AdmissibleExponent (primeExponents i.numeratorFrozen.val p.val)
  unfold AdmissibleExponent
  omega

#print axioms Data.toFrozen
#print axioms ofReflectionIndex
#print axioms numeratorFrozen_eq_minimum_mul_cube

end HeckeSkeleton.LowFrozenCube.Exterior
