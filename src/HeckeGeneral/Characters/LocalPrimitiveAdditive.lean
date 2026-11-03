import HeckeGeneral.Characters.LocalResidueSocle
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

/-! Actual primitive additive characters and perfect pairings on completed local residue rings. -/

noncomputable section

namespace HeckeGeneral.Characters

open NumberField IsDedekindDomain
open scoped Classical

variable (K : Type*) [Field K] [NumberField K]

theorem exists_localAddCharacter_nontrivial_socle (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    ∃ η : AddChar (LocalResidueRing K v (n + 1)) Circle, η (localSocleGenerator K v n) ≠ 1 := by
  obtain ⟨χ, hχ⟩ := circleDual_separates (Multiplicative (LocalResidueRing K v (n + 1)))
    (x := Multiplicative.ofAdd (localSocleGenerator K v n)) (localSocleGenerator_ne_zero K v n)
  exact ⟨AddChar.toMonoidHomEquiv.symm χ, hχ⟩

theorem localAddCharacter_primitive_of_socle (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (η : AddChar (LocalResidueRing K v (n + 1)) Circle)
    (hη : η (localSocleGenerator K v n) ≠ 1) : η.IsPrimitive := by
  intro a ha he
  obtain ⟨b, hb⟩ := localResidue_mul_to_socle K v n a ha
  have hev := congrArg (fun θ : AddChar (LocalResidueRing K v (n + 1)) Circle => θ b) he
  change η (a * b) = 1 at hev
  rw [hb] at hev
  exact hη hev

/-- A choice proved primitive from the actual DVR socle, not from an input primitive hypothesis. -/
def localPrimitiveAddCharacter : (v : HeightOneSpectrum (𝓞 K)) → (n : ℕ) →
    AddChar (LocalResidueRing K v n) Circle
  | _, 0 => 1
  | v, n + 1 => (exists_localAddCharacter_nontrivial_socle K v n).choose

theorem localPrimitiveAddCharacter_socle (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    localPrimitiveAddCharacter K v (n + 1) (localSocleGenerator K v n) ≠ 1 :=
  (exists_localAddCharacter_nontrivial_socle K v n).choose_spec

theorem localPrimitiveAddCharacter_isPrimitive (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    (localPrimitiveAddCharacter K v n).IsPrimitive := by
  cases n with
  | zero =>
    intro a ha
    exact False.elim (ha (Ideal.Quotient.subsingleton_iff.mpr (by simp) |>.elim a 0))
  | succ n =>
    exact localAddCharacter_primitive_of_socle K v n _ (localPrimitiveAddCharacter_socle K v n)

def localResidueAdditivePairing (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    Multiplicative (LocalResidueRing K v n) →* AddChar (LocalResidueRing K v n) Circle where
  toFun a := (localPrimitiveAddCharacter K v n).mulShift a.toAdd
  map_one' := AddChar.mulShift_zero _
  map_mul' _a _b := (AddChar.mulShift_mul _ _ _).symm

@[simp] theorem localResidueAdditivePairing_apply (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (a b : LocalResidueRing K v n) :
    localResidueAdditivePairing K v n (Multiplicative.ofAdd a) b =
      localPrimitiveAddCharacter K v n (a * b) := rfl

theorem localResidueAdditivePairing_injective (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    Function.Injective (localResidueAdditivePairing K v n) := by
  intro a b hab
  apply Multiplicative.toAdd.injective
  exact AddChar.to_mulShift_inj_of_isPrimitive (localPrimitiveAddCharacter_isPrimitive K v n) hab

instance finite_localResidueAddCharacters (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    Finite (AddChar (LocalResidueRing K v n) Circle) :=
  Finite.of_equiv (Multiplicative (LocalResidueRing K v n) →* Circle)
    (AddChar.toMonoidHomEquiv : AddChar (LocalResidueRing K v n) Circle ≃ _).symm

theorem natCard_localResidueAddCharacters (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    Nat.card (AddChar (LocalResidueRing K v n) Circle) = Nat.card (LocalResidueRing K v n) := by
  rw [Nat.card_congr (AddChar.toMonoidHomEquiv : AddChar (LocalResidueRing K v n) Circle ≃ _),
    natCard_circleDual]
  exact Nat.card_congr Multiplicative.toAdd

theorem localResidueAdditivePairing_bijective (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    Function.Bijective (localResidueAdditivePairing K v n) := by
  apply (Nat.bijective_iff_injective_and_card _).mpr
  refine ⟨localResidueAdditivePairing_injective K v n, ?_⟩
  rw [natCard_localResidueAddCharacters]
  exact Nat.card_congr Multiplicative.toAdd

/-- Every additive character is a unique multiplicative frequency of the constructed character. -/
def localResidueAdditivePairingEquiv (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    Multiplicative (LocalResidueRing K v n) ≃* AddChar (LocalResidueRing K v n) Circle :=
  MulEquiv.ofBijective (localResidueAdditivePairing K v n)
    (localResidueAdditivePairing_bijective K v n)

theorem exists_unique_localResidue_additive_frequency (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (η : AddChar (LocalResidueRing K v n) Circle) :
    ∃! a : LocalResidueRing K v n, (localPrimitiveAddCharacter K v n).mulShift a = η := by
  obtain ⟨a, ha⟩ := (localResidueAdditivePairing_bijective K v n).surjective η
  refine ⟨a.toAdd, ha, fun b hb => ?_⟩
  exact congrArg Multiplicative.toAdd
    ((localResidueAdditivePairing_injective K v n) (hb.trans ha.symm))

end HeckeGeneral.Characters
