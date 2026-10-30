import HeckeGeneral.Characters.LocalAdditiveDescent
import FLTReuse.Ma9ad8acc40984aa2
import FLTReuse.Mcd898a60de22b19f
import FLTReuse.Mb4072e15f985c10c
import FLTReuse.Mdfdfd9c07e31f9bd

/-! The standard trace additive character, scaled by the actual different and residue depth.
This identifies a concrete normalization; it does not identify the earlier finite-duality
choice with the standard character without its proved unit-frequency correction. -/

noncomputable section

namespace HeckeGeneral.Characters

open NumberField IsDedekindDomain NumberField.StandardAddChar LanglandsTunnell.TateLocal
open scoped Classical nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]

theorem standardLocalAddCharacter_level (v : HeightOneSpectrum (𝓞 K)) :
    (∀ x : v.adicCompletion K,
      Valued.v x ≤ WithZero.exp (addCharLevel (psiLocal K v)) → psiLocal K v x = 1) ∧
    ∃ y : v.adicCompletion K,
      Valued.v y ≤ WithZero.exp (addCharLevel (psiLocal K v) + 1) ∧ psiLocal K v y ≠ 1 := by
  apply forall_eq_one_and_exists_ne_one_of_addCharLevel K v _ _ (psiLocal_ne_one K v)
  refine ⟨0, fun x hx => psiLocal_eq_one_of_mem_integers K v x ?_⟩
  rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
  simpa using hx

/-- The standard local trace character on `O_v / m_v^n`, scaled by `pi^(-n-d_v)`. -/
def localCanonicalAddCharacter (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    AddChar (LocalResidueRing K v n) ℂ :=
  localScaledResidueAddCharacter K v n (addCharLevel (psiLocal K v)) (psiLocal K v)
    (standardLocalAddCharacter_level K v).1

theorem localCanonicalAddCharacter_isPrimitive (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    (localCanonicalAddCharacter K v n).IsPrimitive :=
  localScaledResidueAddCharacter_isPrimitive K v n _ _ _ (standardLocalAddCharacter_level K v).2

/-- The exponent is the actual different valuation, as proved in the imported Tate theory. -/
theorem localCanonicalAddCharacter_mk (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (x : LocalIntegerRing K v) :
    localCanonicalAddCharacter K v n (Ideal.Quotient.mk _ x) =
      psiLocal K v (localUniformizer K v ^
        (-((n : ℤ) + FractionalIdeal.count K v
          (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K))) * (x : v.adicCompletion K)) := by
  rw [localCanonicalAddCharacter, localScaledResidueAddCharacter_mk, localAdditiveScale,
    addCharLevel_psiLocal_eq_count_differentIdeal]

def localCanonicalAddCharacterCircle (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    AddChar (LocalResidueRing K v n) Circle :=
  localResidueComplexAddCharacterToCircle K v n (localCanonicalAddCharacter K v n)

@[simp] theorem localCanonicalAddCharacterCircle_coe (v : HeightOneSpectrum (𝓞 K))
    (n : ℕ) (x : LocalResidueRing K v n) :
    (localCanonicalAddCharacterCircle K v n x : ℂ) = localCanonicalAddCharacter K v n x := rfl

theorem localCanonicalAddCharacterCircle_isPrimitive (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    (localCanonicalAddCharacterCircle K v n).IsPrimitive :=
  localResidueComplexAddCharacterToCircle_isPrimitive K v n _
    (localCanonicalAddCharacter_isPrimitive K v n)

theorem localCanonicalAddCharacter_norm (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (x : LocalResidueRing K v n) : ‖localCanonicalAddCharacter K v n x‖ = 1 := by
  rw [← localCanonicalAddCharacterCircle_coe, Circle.norm_coe]

/-- The correction to the finite-duality choice is a unique actual residue unit. -/
theorem localCanonicalAddCharacter_unique_unit (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    ∃! u : (LocalResidueRing K v n)ˣ,
      (localPrimitiveAddCharacter K v n).mulShift u.val = localCanonicalAddCharacterCircle K v n :=
  exists_unique_localPrimitiveAddCharacter_unit K v n _
    (localCanonicalAddCharacterCircle_isPrimitive K v n)

/-- The actual correction unit; it records the normalization change explicitly. -/
def localCanonicalAdditiveUnit (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    (LocalResidueRing K v n)ˣ :=
  Classical.choose (localCanonicalAddCharacter_unique_unit K v n)

theorem localCanonicalAdditiveUnit_shift (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    (localPrimitiveAddCharacter K v n).mulShift (localCanonicalAdditiveUnit K v n).val =
      localCanonicalAddCharacterCircle K v n :=
  (Classical.choose_spec (localCanonicalAddCharacter_unique_unit K v n)).1

theorem localCanonicalGauss_normalization (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (χ : LocalResidueDual K v n) :
    localResidueGauss K v n χ (localCanonicalAddCharacterCircle K v n) =
      (χ (localCanonicalAdditiveUnit K v n) : ℂ)⁻¹ *
        localResidueGauss K v n χ (localPrimitiveAddCharacter K v n) := by
  rw [← localCanonicalAdditiveUnit_shift]
  exact localResidueGauss_mulShift_eq K v n χ _ _

theorem localCanonicalGauss_norm (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (χ : LocalResidueDual K v n) (hχ : PrimitiveLocalResidueCharacter K v n χ) :
    ‖localResidueGauss K v n χ (localCanonicalAddCharacterCircle K v n)‖ =
      Real.sqrt ((residueCard K v : ℝ) ^ n) :=
  localResidueGauss_primitive_norm K v n χ hχ _ (localCanonicalAddCharacterCircle_isPrimitive K v n)

/-- No chosen finite-duality character remains in this standard trace-normalized Gauss sum. -/
def canonicalConductorResidueGauss (v : HeightOneSpectrum (𝓞 K))
    (χ : HeckeCharacter K) : ℂ :=
  localResidueGauss K v (localConductorExponent K χ v) (conductorResidueCharacter K v χ)
    (localCanonicalAddCharacterCircle K v (localConductorExponent K χ v))

theorem canonicalConductorResidueGauss_norm (v : HeightOneSpectrum (𝓞 K))
    (χ : HeckeCharacter K) :
    ‖canonicalConductorResidueGauss K v χ‖ =
      Real.sqrt ((residueCard K v : ℝ) ^ localConductorExponent K χ v) :=
  localCanonicalGauss_norm K v _ _ (conductorResidueCharacter_isPrimitive K v χ)

theorem canonicalConductorResidueGauss_ne_zero (v : HeightOneSpectrum (𝓞 K))
    (χ : HeckeCharacter K) : canonicalConductorResidueGauss K v χ ≠ 0 := by
  unfold canonicalConductorResidueGauss
  rw [localCanonicalGauss_normalization]
  exact mul_ne_zero (inv_ne_zero (Circle.coe_ne_zero _))
    (localPrimitiveGauss_ne_zero K v _ _ (conductorResidueCharacter_isPrimitive K v χ))

end HeckeGeneral.Characters
