import HeckeSkeleton.Moments.MOM_INV_STEP.LocalDigits
import HeckeGeneral.Characters.SIntegerSexticPowerMask

/-!
# Actual first-source digits and the surviving cube factor

The row is the repository's literal `sIntegerSexticIdealEvaluation`, with
the given global sixth root and complex embedding. Its existing sixth-power
theorem identifies the mask with coprimality of the actual modulus
contraction. The algebraic table therefore returns a squarefree label J and
the original q₀ puncture, including zero and nonunit numerators.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.LocalSource

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open CubeAlgebra LocalDigits
open scoped BigOperators Classical

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Finite S]
variable (ζ : K) (hζ : IsPrimitiveRoot ζ 6) (σ : K →+* ℂ)

theorem actual_prime_source_split (p : HeightOneSpectrum (𝓞 K)) (hpS : p ∉ S)
    (hp6 : (6 : 𝓞 K) ∉ p.asIdeal)
    (ε₁ ε₂ : Bool) (v₁ v₂ : ℕ) (hv : 0 < v₁ + v₂) (a : S.integer K) :
    sIntegerSexticEvaluation K S p hpS ζ hζ σ hp6 a ^ (bit ε₁ + 3 * v₁) *
      star (sIntegerSexticEvaluation K S p hpS ζ hζ σ hp6 a ^ (bit ε₂ + 3 * v₂)) =
      if conductorExponent (parity (v₁ + v₂)) ε₁ ε₂ = 0 then
        (if sIntegerSexticResidueMap K S p hpS a = 0 then 0 else 1)
      else (sexticResidueCharacter K ζ hζ σ p hp6 ^
        (conductorExponent (parity (v₁ + v₂)) ε₁ ε₂).val)
          (sIntegerSexticResidueMap K S p hpS a) := by
  letI : Field (𝓞 K ⧸ p.asIdeal) := Ideal.Quotient.field _
  letI : Fintype (𝓞 K ⧸ p.asIdeal) := Fintype.ofFinite _
  have h6 : sexticResidueCharacter K ζ hζ σ p hp6 ^ 6 = 1 := by
    rw [← sexticResidueCharacter_order K ζ hζ σ p hp6]
    exact pow_orderOf_eq_one _
  exact local_source_split _ h6 ε₁ ε₂ v₁ v₂ hv (sIntegerSexticResidueMap K S p hpS a)

theorem actual_prime_conductor_principal_iff
    (p : HeightOneSpectrum (𝓞 K)) (hp6 : (6 : 𝓞 K) ∉ p.asIdeal)
    (ε₁ ε₂ : Bool) (v₁ v₂ : ℕ) :
    sexticResidueCharacter K ζ hζ σ p hp6 ^
      (conductorExponent (parity (v₁ + v₂)) ε₁ ε₂).val = 1 ↔
      conductorExponent (parity (v₁ + v₂)) ε₁ ε₂ = 0 := by
  letI : Field (𝓞 K ⧸ p.asIdeal) := Ideal.Quotient.field _
  letI : Fintype (𝓞 K ⧸ p.asIdeal) := Fintype.ofFinite _
  exact local_conductor_principal_iff _
    (sexticResidueCharacter_order K ζ hζ σ p hp6) ε₁ ε₂ v₁ v₂

/-- The actual local zero frequency; the diagonal/principal coefficient
is present explicitly. This statement alone is not a global CRT theorem. -/
theorem actual_prime_zero_frequency
    (p : HeightOneSpectrum (𝓞 K)) (hp6 : (6 : 𝓞 K) ∉ p.asIdeal)
    [Fintype (𝓞 K ⧸ p.asIdeal)]
    (ε₁ ε₂ : Bool) (v₁ v₂ : ℕ) (hv : 0 < v₁ + v₂) :
    (∑ x : 𝓞 K ⧸ p.asIdeal,
      sexticResidueCharacter K ζ hζ σ p hp6 x ^ (bit ε₁ + 3 * v₁) *
      star (sexticResidueCharacter K ζ hζ σ p hp6 x ^ (bit ε₂ + 3 * v₂))) =
      if conductorExponent (parity (v₁ + v₂)) ε₁ ε₂ = 0 then
        (Fintype.card (𝓞 K ⧸ p.asIdeal)ˣ : ℂ) else 0 := by
  letI : Field (𝓞 K ⧸ p.asIdeal) := Ideal.Quotient.field _
  exact local_zero_frequency _ (sexticResidueCharacter_order K ζ hζ σ p hp6)
    ε₁ ε₂ v₁ v₂ hv

/-- Exact active/principal factorization of the finite cube-support
source using the actual S-integer residue maps and global root. -/
theorem actual_cube_source_split {ι : Type*}
    (P : ι → HeightOneSpectrum (𝓞 K)) (hPS : ∀ i, P i ∉ S)
    (hP6 : ∀ i, (6 : 𝓞 K) ∉ (P i).asIdeal)
    (B : Finset ι) (ε₁ ε₂ : ι → Bool) (v₁ v₂ : ι → ℕ)
    (hv : ∀ i ∈ B, 0 < v₁ i + v₂ i) (a : S.integer K) :
    let t := fun i => conductorExponent (parity (v₁ i + v₂ i)) (ε₁ i) (ε₂ i)
    (∏ i ∈ B,
      sIntegerSexticEvaluation K S (P i) (hPS i) ζ hζ σ (hP6 i) a ^
        (bit (ε₁ i) + 3 * v₁ i) *
      star (sIntegerSexticEvaluation K S (P i) (hPS i) ζ hζ σ (hP6 i) a ^
        (bit (ε₂ i) + 3 * v₂ i))) =
    (if ∃ i ∈ B, t i = 0 ∧ sIntegerSexticResidueMap K S (P i) (hPS i) a = 0
      then 0 else 1) *
      ∏ i ∈ B.filter (fun i => t i ≠ 0),
        (sexticResidueCharacter K ζ hζ σ (P i) (hP6 i) ^ (t i).val)
          (sIntegerSexticResidueMap K S (P i) (hPS i) a) := by
  letI : ∀ i, Field (𝓞 K ⧸ (P i).asIdeal) := fun i => Ideal.Quotient.field _
  letI : ∀ i, Fintype (𝓞 K ⧸ (P i).asIdeal) := fun i => Fintype.ofFinite _
  have horder (i : ι) : sexticResidueCharacter K ζ hζ σ (P i) (hP6 i) ^ 6 = 1 := by
    rw [← sexticResidueCharacter_order K ζ hζ σ (P i) (hP6 i)]
    exact pow_orderOf_eq_one _
  exact finite_source_split B (fun i => sexticResidueCharacter K ζ hζ σ (P i) (hP6 i))
    horder ε₁ ε₂ v₁ v₂ (fun i hi => by have := hv i hi; omega)
    (fun i => sIntegerSexticResidueMap K S (P i) (hPS i) a)

variable (I : Ideal (𝓞 K)) (hI : I ≠ 0)
variable (hS : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I → p ∉ S)
variable (h6 : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I → (6 : 𝓞 K) ∉ p.asIdeal)

/-- Multiplicativity of the actual ideal evaluation, packaged without
changing its values on nonunits. -/
def actualRow : S.integer K →* ℂ where
  toFun := sIntegerSexticIdealEvaluation K S ζ hζ σ I hI hS h6
  map_one' := sIntegerSexticIdealEvaluation_one K S ζ hζ σ I hI hS h6
  map_mul' := sIntegerSexticIdealEvaluation_mul K S ζ hζ σ I hI hS h6

@[simp] theorem actualRow_apply (a : S.integer K) :
    actualRow K S ζ hζ σ I hI hS h6 a =
      sIntegerSexticIdealEvaluation K S ζ hζ σ I hI hS h6 a := rfl

theorem actualRow_mask (a : S.integer K) :
    sixthMask (actualRow K S ζ hζ σ I hI hS h6) a =
      if IsCoprime I (sIntegerModulusContraction K S a) then 1 else 0 := by
  rw [sixthMask, ← map_pow]
  exact sIntegerSexticIdealEvaluation_sixth_power_coprime_mask K S ζ hζ σ I hI hS h6 a

theorem actualRow_zero_or_one (a : S.integer K) :
    actualRow K S ζ hζ σ I hI hS h6 a ^ 6 = 0 ∨
      actualRow K S ζ hζ σ I hI hS h6 a ^ 6 = 1 := by
  have h := actualRow_mask K S ζ hζ σ I hI hS h6 a
  by_cases hc : IsCoprime I (sIntegerModulusContraction K S a)
  · right
    simpa only [sixthMask, if_pos hc] using h
  · left
    simpa only [sixthMask, if_neg hc] using h

/-- Exact leftover column factor after the local CRT factors and dual
dilation have been multiplied. The new puncture is the original q₀. -/
theorem actual_first_pass_label_identity {ι : Type*}
    (p : ι → S.integer K) (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (hv : ∀ i ∈ B, 0 < v i) (side : Bool) :
    let χ := sIntegerSexticIdealEvaluation K S ζ hζ σ I hI hS h6
    (if IsCoprime I (sIntegerModulusContraction K S (cubeRadical p B)) then 1 else 0) *
      χ (aLabel p B (if side then ε₂ else ε₁)) ^ 4 *
      χ (crtLabel p B v ε₁ ε₂ side) * χ (dilationLabel p B v ε₁ ε₂) =
    χ (jLabel p B v ε₁ ε₂) ^ 4 *
      (if IsCoprime I (sIntegerModulusContraction K S (b0Label p B v ε₁ ε₂))
        then 1 else 0) := by
  have h := first_pass_label_identity (actualRow K S ζ hζ σ I hI hS h6)
    (actualRow_zero_or_one K S ζ hζ σ I hI hS h6) p B v ε₁ ε₂ hv side
  rw [actualRow_mask, actualRow_mask] at h
  exact h

/-- The inverse row is dilated at the same time as the cube factor is
reassembled, preserving every coprimality zero. -/
theorem actual_first_pass_after_dual_dilation {ι : Type*}
    (p : ι → S.integer K) (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (hv : ∀ i ∈ B, 0 < v i) (side : Bool) (z : S.integer K) :
    let χ := sIntegerSexticIdealEvaluation K S ζ hζ σ I hI hS h6
    ((if IsCoprime I (sIntegerModulusContraction K S (cubeRadical p B)) then 1 else 0) *
      χ (aLabel p B (if side then ε₂ else ε₁)) ^ 4 *
      χ (crtLabel p B v ε₁ ε₂ side)) * star (χ z) =
    (χ (jLabel p B v ε₁ ε₂) ^ 4 *
      (if IsCoprime I (sIntegerModulusContraction K S (b0Label p B v ε₁ ε₂))
        then 1 else 0)) * star (χ (z * dilationLabel p B v ε₁ ε₂)) := by
  have h := first_pass_after_dual_dilation (actualRow K S ζ hζ σ I hI hS h6)
    (actualRow_zero_or_one K S ζ hζ σ I hI hS h6) p B v ε₁ ε₂ hv side z
  rw [actualRow_mask, actualRow_mask] at h
  exact h

end HeckeSkeleton.Moments.MOM_INV_STEP.LocalSource

end
