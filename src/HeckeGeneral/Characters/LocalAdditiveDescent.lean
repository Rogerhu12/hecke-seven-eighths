import HeckeGeneral.Characters.LocalPrimitiveFourier
import Mathlib.Algebra.Group.Units.Hom

/-! Scaling a genuine local additive character and descending to a prime-power residue ring.
The hypotheses here describe its additive conductor balls; no residue primitivity is assumed. -/

noncomputable section

namespace HeckeGeneral.Characters

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped Classical

variable (K : Type*) [Field K] [NumberField K]

def localAdditiveScale (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) (d : ℤ) : v.adicCompletion K :=
  localUniformizer K v ^ (-((n : ℤ) + d))

theorem localAdditiveScale_ne_zero (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) (d : ℤ) :
    localAdditiveScale K v n d ≠ 0 := zpow_ne_zero _ (localUniformizer_ne_zero K v)

theorem localAdditiveScale_valuation (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) (d : ℤ) :
    Valued.v (localAdditiveScale K v n d) = WithZero.exp ((n : ℤ) + d) := by
  rw [localAdditiveScale, map_zpow₀, localUniformizer_valuation, ← WithZero.exp_zsmul]
  congr 1
  simp

def localScaledIntegerAddCharacter (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) (d : ℤ)
    (ψ : AddChar (v.adicCompletion K) ℂ) : AddChar (LocalIntegerRing K v) ℂ :=
  (ψ.mulShift (localAdditiveScale K v n d)).compAddMonoidHom
    (v.adicCompletionIntegers K).subtype.toAddMonoidHom

@[simp] theorem localScaledIntegerAddCharacter_apply (v : HeightOneSpectrum (𝓞 K))
    (n : ℕ) (d : ℤ) (ψ : AddChar (v.adicCompletion K) ℂ) (x : LocalIntegerRing K v) :
    localScaledIntegerAddCharacter K v n d ψ x =
      ψ (localAdditiveScale K v n d * (x : v.adicCompletion K)) := rfl

theorem localScaledIntegerAddCharacter_trivial (v : HeightOneSpectrum (𝓞 K))
    (n : ℕ) (d : ℤ) (ψ : AddChar (v.adicCompletion K) ℂ)
    (hψ : ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp d → ψ x = 1)
    (x : LocalIntegerRing K v) (hx : x ∈ localMaximalIdeal K v ^ n) :
    localScaledIntegerAddCharacter K v n d ψ x = 1 := by
  apply hψ
  change Valued.v (localAdditiveScale K v n d * (x : v.adicCompletion K)) ≤ WithZero.exp d
  have hxv := (local_mem_maximalIdeal_pow_iff_valuation K v x n).mp hx
  rw [map_mul, localAdditiveScale_valuation]
  calc
    _ ≤ WithZero.exp ((n : ℤ) + d) * WithZero.exp (-(n : ℤ)) :=
      mul_le_mul_of_nonneg_left hxv zero_le
    _ = WithZero.exp d := by rw [← WithZero.exp_add]; congr 1; omega

/-- Additive descent uses the actual ideal quotient, without a ring-valued lift. -/
def localAdditiveQuotientLift (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (η : AddChar (LocalIntegerRing K v) ℂ)
    (hη : ∀ x : LocalIntegerRing K v, x ∈ localMaximalIdeal K v ^ n → η x = 1) :
    AddChar (LocalResidueRing K v n) ℂ :=
  AddChar.toAddMonoidHomEquiv.symm
    (QuotientAddGroup.lift (localMaximalIdeal K v ^ n).toAddSubgroup
      (AddChar.toAddMonoidHomEquiv η) (by
        intro x hx
        exact hη x hx))

@[simp] theorem localAdditiveQuotientLift_mk (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (η : AddChar (LocalIntegerRing K v) ℂ)
    (hη : ∀ x : LocalIntegerRing K v, x ∈ localMaximalIdeal K v ^ n → η x = 1)
    (x : LocalIntegerRing K v) :
    localAdditiveQuotientLift K v n η hη (Ideal.Quotient.mk _ x) = η x := rfl

def localScaledResidueAddCharacter (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) (d : ℤ)
    (ψ : AddChar (v.adicCompletion K) ℂ)
    (hψ : ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp d → ψ x = 1) :
    AddChar (LocalResidueRing K v n) ℂ :=
  localAdditiveQuotientLift K v n (localScaledIntegerAddCharacter K v n d ψ)
    (localScaledIntegerAddCharacter_trivial K v n d ψ hψ)

@[simp] theorem localScaledResidueAddCharacter_mk (v : HeightOneSpectrum (𝓞 K))
    (n : ℕ) (d : ℤ) (ψ : AddChar (v.adicCompletion K) ℂ)
    (hψ : ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp d → ψ x = 1)
    (x : LocalIntegerRing K v) :
    localScaledResidueAddCharacter K v n d ψ hψ (Ideal.Quotient.mk _ x) =
      ψ (localAdditiveScale K v n d * (x : v.adicCompletion K)) := rfl

/-- Detecting any element of the last ideal layer suffices for primitivity. -/
theorem localAddCharacter_primitive_of_last_layer (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (η : AddChar (LocalResidueRing K v (n + 1)) ℂ)
    (hη : ∃ x : LocalIntegerRing K v,
      x ∈ localMaximalIdeal K v ^ n ∧ η (Ideal.Quotient.mk _ x) ≠ 1) : η.IsPrimitive := by
  obtain ⟨x, hx, hηx⟩ := hη
  rw [localMaximalIdeal, local_maximalIdeal_pow_eq_span_uniformizer_pow,
    Ideal.mem_span_singleton] at hx
  obtain ⟨c, hc⟩ := hx
  intro a ha he
  obtain ⟨b, hb⟩ := localResidue_mul_to_socle K v n a ha
  have h := congrArg (fun θ : AddChar (LocalResidueRing K v (n + 1)) ℂ =>
    θ (b * Ideal.Quotient.mk _ c)) he
  change η (a * (b * Ideal.Quotient.mk _ c)) = 1 at h
  rw [← mul_assoc, hb] at h
  apply hηx
  simpa only [localSocleGenerator, ← map_mul, ← hc] using h

theorem localScaledResidueAddCharacter_isPrimitive (v : HeightOneSpectrum (𝓞 K))
    (n : ℕ) (d : ℤ) (ψ : AddChar (v.adicCompletion K) ℂ)
    (hψ : ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp d → ψ x = 1)
    (hψnext : ∃ y : v.adicCompletion K, Valued.v y ≤ WithZero.exp (d + 1) ∧ ψ y ≠ 1) :
    (localScaledResidueAddCharacter K v n d ψ hψ).IsPrimitive := by
  cases n with
  | zero =>
    intro a ha
    exact False.elim (ha (Ideal.Quotient.subsingleton_iff.mpr (by simp) |>.elim a 0))
  | succ n =>
    obtain ⟨y, hyv, hψy⟩ := hψnext
    let x : v.adicCompletion K := (localAdditiveScale K v (n + 1) d)⁻¹ * y
    have hxv : Valued.v x ≤ WithZero.exp (-(n : ℤ)) := by
      dsimp only [x]
      rw [map_mul, map_inv₀, localAdditiveScale_valuation]
      calc
        _ ≤ (WithZero.exp (((n + 1 : ℕ) : ℤ) + d))⁻¹ * WithZero.exp (d + 1) :=
          mul_le_mul_of_nonneg_left hyv zero_le
        _ = WithZero.exp (-(n : ℤ)) := by
          rw [← WithZero.exp_neg, ← WithZero.exp_add]
          congr 1
          push_cast
          omega
    have hxi : x ∈ v.adicCompletionIntegers K := by
      rw [mem_adicCompletionIntegers]
      exact hxv.trans (WithZero.exp_le_exp.mpr (show -(n : ℤ) ≤ 0 by omega))
    apply localAddCharacter_primitive_of_last_layer K v n
    refine ⟨⟨x, hxi⟩, (local_mem_maximalIdeal_pow_iff_valuation K v _ n).mpr hxv, ?_⟩
    rw [localScaledResidueAddCharacter_mk]
    change ψ (localAdditiveScale K v (n + 1) d * ((localAdditiveScale K v (n + 1) d)⁻¹ * y)) ≠ 1
    rw [mul_inv_cancel_left₀ (localAdditiveScale_ne_zero K v (n + 1) d)]
    exact hψy

/-- Every additive character of the finite residue ring has its genuine circle-valued form. -/
def localResidueComplexAddCharacterToCircle (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (η : AddChar (LocalResidueRing K v n) ℂ) : AddChar (LocalResidueRing K v n) Circle :=
  AddChar.toMonoidHomEquiv.symm (complexUnitCharacterToCircle
    (Multiplicative (LocalResidueRing K v n)) (AddChar.toMonoidHomEquiv η).toHomUnits)

@[simp] theorem localResidueComplexAddCharacterToCircle_coe (v : HeightOneSpectrum (𝓞 K))
    (n : ℕ) (η : AddChar (LocalResidueRing K v n) ℂ) (x : LocalResidueRing K v n) :
    (localResidueComplexAddCharacterToCircle K v n η x : ℂ) = η x := rfl

theorem localResidueComplexAddCharacterToCircle_isPrimitive (v : HeightOneSpectrum (𝓞 K))
    (n : ℕ) (η : AddChar (LocalResidueRing K v n) ℂ) (hη : η.IsPrimitive) :
    (localResidueComplexAddCharacterToCircle K v n η).IsPrimitive := by
  intro a ha he
  apply hη ha
  apply AddChar.ext
  intro b
  have h := congrArg (fun θ : AddChar (LocalResidueRing K v n) Circle => (θ b : ℂ)) he
  simpa only [AddChar.mulShift_apply, localResidueComplexAddCharacterToCircle_coe,
    AddChar.one_apply, Circle.coe_one] using h

end HeckeGeneral.Characters
