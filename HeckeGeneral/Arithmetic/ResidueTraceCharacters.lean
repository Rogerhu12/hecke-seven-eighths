import HeckeGeneral.Arithmetic.IdealMobiusMask
import HeckeGeneral.Arithmetic.FiniteFourierBounds
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Constructed trace characters on residue fields and squarefree quotients

The residue-field character is the standard complex character of the prime
field composed with the actual algebra trace. Its primitivity is proved
from the nondegenerate trace pairing. Products of these characters are
primitive, and Chinese remaindering transports them to the actual quotient
by a squarefree product of prime ideals.

This does not construct the inverse-different trace pairing for arbitrary
prime-power moduli or for the S-integer lattice. Residue-field trace and
that larger dual-lattice pairing are distinct constructions.
-/

noncomputable section

namespace HeckeGeneral.Arithmetic.ResidueTraceCharacters

open NumberField IsDedekindDomain IdealMobiusMask
open scoped BigOperators Classical

section FiniteField

variable (F : Type*) [Field F] [Finite F]

local instance primeFieldAlgebra : Algebra (ZMod (ringChar F)) F := ZMod.algebra _ _

local instance primeCharacteristic_neZero : NeZero (ringChar F) :=
  ⟨CharP.ringChar_ne_zero_of_finite F⟩

/-- An explicit trace construction, with complex values rather than an unspecified extension. -/
def traceCharacter : AddChar F ℂ :=
  (ZMod.stdAddChar (N := ringChar F)).compAddMonoidHom
    (Algebra.trace (ZMod (ringChar F)) F).toAddMonoidHom

@[simp] theorem traceCharacter_apply (a : F) :
    traceCharacter F a = ZMod.stdAddChar (Algebra.trace (ZMod (ringChar F)) F a) := rfl

/-- Every nonzero frequency is detected by an actual trace-pairing value. -/
theorem traceCharacter_detects {a : F} (ha : a ≠ 0) :
    ∃ b : F, traceCharacter F (a * b) ≠ 1 := by
  obtain ⟨b, hb⟩ := FiniteField.trace_to_zmod_nondegenerate F ha
  refine ⟨b, fun h => hb ?_⟩
  apply ZMod.injective_stdAddChar
  simpa only [traceCharacter_apply, AddChar.map_zero_eq_one] using h

theorem traceCharacter_isPrimitive : (traceCharacter F).IsPrimitive := by
  intro a ha h
  obtain ⟨b, hb⟩ := traceCharacter_detects F ha
  apply hb
  have hv := congrArg (fun ψ : AddChar F ℂ => ψ b) h
  simpa only [AddChar.mulShift_apply, AddChar.one_apply] using hv

end FiniteField

section Products

variable {ι : Type*} [Fintype ι] {A : ι → Type*} [∀ i, CommRing (A i)]

/-- The product of the actual coordinate additive characters. -/
def productCharacter (ψ : ∀ i, AddChar (A i) ℂ) : AddChar (∀ i, A i) ℂ where
  toFun x := ∏ i, ψ i (x i)
  map_zero_eq_one' := by simp
  map_add_eq_mul' x y := by simp [AddChar.map_add_eq_mul, Finset.prod_mul_distrib]

@[simp] theorem productCharacter_apply (ψ : ∀ i, AddChar (A i) ℂ) (x : ∀ i, A i) :
    productCharacter ψ x = ∏ i, ψ i (x i) := rfl

theorem productCharacter_single (ψ : ∀ i, AddChar (A i) ℂ) (i : ι) (a : A i) :
    productCharacter ψ (Pi.single i a) = ψ i a := by
  rw [productCharacter_apply, Finset.prod_eq_single i]
  · simp
  · intro j _ hji
    simp [Pi.single_eq_of_ne hji]
  · simp

/-- Coordinate-wise primitive pairings give a primitive product pairing. -/
theorem productCharacter_isPrimitive (ψ : ∀ i, AddChar (A i) ℂ)
    (hψ : ∀ i, (ψ i).IsPrimitive) : (productCharacter ψ).IsPrimitive := by
  intro a ha h
  obtain ⟨i, hi⟩ := Function.ne_iff.mp ha
  obtain ⟨b, hb⟩ := AddChar.ne_one_iff.mp (hψ i hi)
  have hmul : a * Pi.single i b = Pi.single i (a i * b) := by
    ext j
    by_cases hji : j = i
    · subst j
      simp
    · simp [Pi.single_eq_of_ne hji]
  have hv := congrArg (fun φ : AddChar (∀ i, A i) ℂ => φ (Pi.single i b)) h
  apply hb
  simpa only [AddChar.mulShift_apply, AddChar.one_apply, hmul,
    productCharacter_single] using hv

end Products

section Transport

variable {R T : Type*} [CommRing R] [CommRing T]

def transportCharacter (e : R ≃+* T) (ψ : AddChar T ℂ) : AddChar R ℂ :=
  ψ.compAddMonoidHom e.toAddMonoidHom

@[simp] theorem transportCharacter_apply (e : R ≃+* T) (ψ : AddChar T ℂ) (a : R) :
    transportCharacter e ψ a = ψ (e a) := rfl

theorem transportCharacter_isPrimitive (e : R ≃+* T) (ψ : AddChar T ℂ)
    (hψ : ψ.IsPrimitive) : (transportCharacter e ψ).IsPrimitive := by
  intro a ha h
  have hea : e a ≠ 0 := by
    intro hea
    apply ha
    apply e.injective
    simpa only [map_zero] using hea
  apply hψ hea
  ext b
  obtain ⟨c, rfl⟩ := e.surjective b
  have hv := congrArg (fun φ : AddChar R ℂ => φ c) h
  simpa only [AddChar.mulShift_apply, AddChar.one_apply, transportCharacter_apply,
    map_mul] using hv

end Transport

section ActualResidues

variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Ring.HasFiniteQuotients R]

abbrev Residue (p : HeightOneSpectrum R) := R ⧸ p.asIdeal

instance residueField (p : HeightOneSpectrum R) : Field (Residue p) := Ideal.Quotient.field _

instance finiteResidue (p : HeightOneSpectrum R) : Finite (Residue p) :=
  Ring.HasFiniteQuotients.finiteQuotient p.ne_bot

instance fintypeResidue (p : HeightOneSpectrum R) : Fintype (Residue p) := Fintype.ofFinite _

def residueCharacter (p : HeightOneSpectrum R) : AddChar (Residue p) ℂ :=
  traceCharacter (Residue p)

theorem residueCharacter_isPrimitive (p : HeightOneSpectrum R) :
    (residueCharacter p).IsPrimitive := traceCharacter_isPrimitive _

omit [Ring.HasFiniteQuotients R] in
theorem squarefree_quotient_eq (S : Finset (HeightOneSpectrum R)) :
    primeProduct S = ⨅ p : S, p.val.asIdeal := by
  ext k
  simp [primeProduct_eq_iInf]

/-- CRT uses actual residue quotients and the proven coprimality of distinct prime ideals. -/
def squarefreeCRT (S : Finset (HeightOneSpectrum R)) :
    (R ⧸ primeProduct S) ≃+* ∀ p : S, Residue p.val :=
  (Ideal.quotEquivOfEq (squarefree_quotient_eq S)).trans
    (Ideal.quotientInfRingEquivPiQuotient (fun p : S => p.val.asIdeal) (by
      intro p q hpq
      exact Ideal.isCoprime_of_isMaximal (fun h => hpq
        (Subtype.ext (HeightOneSpectrum.asIdeal_injective h)))))

def squarefreeCharacter (S : Finset (HeightOneSpectrum R)) :
    AddChar (R ⧸ primeProduct S) ℂ :=
  transportCharacter (squarefreeCRT S) (productCharacter (fun p : S => residueCharacter p.val))

/-- A constructed primitive character on the actual squarefree quotient. -/
theorem squarefreeCharacter_isPrimitive (S : Finset (HeightOneSpectrum R)) :
    (squarefreeCharacter S).IsPrimitive :=
  transportCharacter_isPrimitive _ _
    (productCharacter_isPrimitive _ (fun p => residueCharacter_isPrimitive p.val))

instance finiteSquarefreeQuotient (S : Finset (HeightOneSpectrum R)) :
    Finite (R ⧸ primeProduct S) := Ring.HasFiniteQuotients.finiteQuotient (primeProduct_ne_bot S)

instance fintypeSquarefreeQuotient (S : Finset (HeightOneSpectrum R)) :
    Fintype (R ⧸ primeProduct S) := Fintype.ofFinite _

/-- Parseval now has a constructed arithmetic character, with no pairing hypothesis left. -/
theorem squarefree_fourier_energy (S : Finset (HeightOneSpectrum R))
    (f : (R ⧸ primeProduct S) → ℂ) :
    PeriodicFourier.energy (PeriodicFourier.fourier (squarefreeCharacter S) f) =
      (Fintype.card (R ⧸ primeProduct S) : ℝ) * PeriodicFourier.energy f :=
  PeriodicFourier.energy_fourier _ (squarefreeCharacter_isPrimitive S) f

end ActualResidues

end HeckeGeneral.Arithmetic.ResidueTraceCharacters
