import HeckeGeneral.Arithmetic.ResidueGaussSums
import Mathlib.Algebra.BigOperators.Pi

/-!
Finite Gauss transforms on products of actual residue fields. The additive
character is arbitrary, not restricted to a tensor trace chosen in advance.
The scalar formula includes every zero or nonunit frequency, as needed by
the genuine squarefree S-integer Poisson transform.
-/

set_option autoImplicit false
noncomputable section
namespace CubicSieve.Gauss

open HeckeGeneral.Arithmetic.PeriodicFourier
open HeckeGeneral.Arithmetic.ResidueTraceCharacters
open HeckeGeneral.Arithmetic.ProductResidueFourier
open HeckeGeneral.Arithmetic.ResidueGaussSums
open scoped Classical BigOperators

section Field
variable {F : Type*} [Field F] [Fintype F]

theorem field_fourier_scalar (χ : MulChar F ℂ) (hχ : χ ≠ 1)
    (ψ : AddChar F ℂ) (h : F) :
    fourier ψ χ h = (χ h)⁻¹ * gaussSum χ ψ := by
  by_cases hh : h = 0
  · subst h
    rw [fourier_zero, MulChar.sum_eq_zero_of_ne_one hχ, χ.map_zero]
    simp
  · have ht := gaussSum_mulShift_eq χ ψ (Units.mk0 h hh)
    simpa only [fourier, gaussSum, AddChar.mulShift_apply, Units.val_mk0,
      MulChar.inv_apply_eq_inv'] using ht

theorem field_fourier_conj (χ : MulChar F ℂ) (hχ : χ ≠ 1)
    (ψ : AddChar F ℂ) (h : F) :
    fourier ψ χ h = star (χ h) * gaussSum χ ψ := by
  rw [field_fourier_scalar χ hχ ψ h, MulChar.star_apply', MulChar.inv_apply_eq_inv']

end Field

section Product
variable {ι : Type*} [Fintype ι] {A : ι → Type*}
variable [∀ i, CommRing (A i)]

def coordinateCharacter (ψ : AddChar (∀ i, A i) ℂ) (i : ι) : AddChar (A i) ℂ where
  toFun a := ψ (Pi.single i a)
  map_zero_eq_one' := by simp
  map_add_eq_mul' a b := by
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ext j
    by_cases hji : j = i
    · subst j; simp
    · simp [Pi.single_eq_of_ne hji]

@[simp] theorem coordinateCharacter_apply (ψ : AddChar (∀ i, A i) ℂ)
    (i : ι) (a : A i) : coordinateCharacter ψ i a = ψ (Pi.single i a) := rfl

theorem product_coordinateCharacter (ψ : AddChar (∀ i, A i) ℂ) :
    productCharacter (coordinateCharacter ψ) = ψ := by
  ext x
  have hsum (s : Finset ι) :
      ψ (∑ i ∈ s, Pi.single i (x i)) = ∏ i ∈ s, ψ (Pi.single i (x i)) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih => simp [hi, AddChar.map_add_eq_mul, ih]
  have hx : (∑ i : ι, Pi.single i (x i)) = x := by
    ext j
    simp [Finset.sum_apply]
  change (∏ i, ψ (Pi.single i (x i))) = ψ x
  rw [← hsum, hx]

theorem coordinateCharacter_isPrimitive (ψ : AddChar (∀ i, A i) ℂ)
    (hψ : ψ.IsPrimitive) (i : ι) : (coordinateCharacter ψ i).IsPrimitive := by
  intro a ha hshift
  have hvec : (Pi.single i a : ∀ i, A i) ≠ 0 := by
    intro hz
    have h := congrFun hz i
    exact ha (by simpa using h)
  apply hψ hvec
  ext x
  have hmul : (Pi.single i a : ∀ i, A i) * x = Pi.single i (a * x i) := by
    ext j
    by_cases hji : j = i
    · subst j; simp
    · simp [Pi.single_eq_of_ne hji]
  change ψ ((Pi.single i a : ∀ i, A i) * x) = 1
  rw [hmul]
  have hv := congrArg (fun η : AddChar (A i) ℂ => η (x i)) hshift
  simpa only [AddChar.mulShift_apply, AddChar.one_apply, coordinateCharacter_apply] using hv

end Product

section ProductFields
variable {ι : Type*} [Fintype ι] {A : ι → Type*}
variable [∀ i, Field (A i)] [∀ i, Fintype (A i)]

def productCoefficient (χ : ∀ i, MulChar (A i) ℂ) (x : ∀ i, A i) : ℂ :=
  ∏ i, χ i (x i)

theorem product_fourier_factorization (χ : ∀ i, MulChar (A i) ℂ)
    (ψ : AddChar (∀ i, A i) ℂ) (h : ∀ i, A i) :
    fourier ψ (productCoefficient χ) h =
      ∏ i, fourier (coordinateCharacter ψ i) (χ i) (h i) := by
  calc
    _ = fourier (productCharacter (coordinateCharacter ψ))
        (tensorCoefficient (fun i => (χ i : A i → ℂ))) h := by
      rw [product_coordinateCharacter]
      rfl
    _ = _ := tensor_fourier (coordinateCharacter ψ) (fun i => (χ i : A i → ℂ)) h

theorem product_fourier_scalar (χ : ∀ i, MulChar (A i) ℂ)
    (hχ : ∀ i, χ i ≠ 1) (ψ : AddChar (∀ i, A i) ℂ) (h : ∀ i, A i) :
    fourier ψ (productCoefficient χ) h =
      (productCoefficient χ h)⁻¹ * fourier ψ (productCoefficient χ) 1 := by
  rw [product_fourier_factorization, product_fourier_factorization]
  simp_rw [field_fourier_scalar _ (hχ _) _]
  simp only [Pi.one_apply, MulChar.map_one, inv_one, one_mul,
    productCoefficient, Finset.prod_mul_distrib, Finset.prod_inv_distrib]

theorem product_fourier_conj (χ : ∀ i, MulChar (A i) ℂ)
    (hχ : ∀ i, χ i ≠ 1) (ψ : AddChar (∀ i, A i) ℂ) (h : ∀ i, A i) :
    fourier ψ (productCoefficient χ) h =
      star (productCoefficient χ h) * fourier ψ (productCoefficient χ) 1 := by
  have hinv : (productCoefficient χ h)⁻¹ = star (productCoefficient χ h) := by
    change (∏ i, χ i (h i))⁻¹ = (starRingEnd ℂ) (∏ i, χ i (h i))
    rw [← Finset.prod_inv_distrib, map_prod]
    apply Finset.prod_congr rfl
    intro i _
    change (χ i (h i))⁻¹ = star (χ i (h i))
    rw [MulChar.star_apply', MulChar.inv_apply_eq_inv']
  rw [product_fourier_scalar χ hχ ψ h, hinv]

theorem product_gauss_norm_sq (χ : ∀ i, MulChar (A i) ℂ)
    (hχ : ∀ i, χ i ≠ 1) (ψ : AddChar (∀ i, A i) ℂ) (hψ : ψ.IsPrimitive) :
    ‖fourier ψ (productCoefficient χ) 1‖ ^ 2 = (Fintype.card (∀ i, A i) : ℝ) := by
  have hi (i : ι) : ‖fourier (coordinateCharacter ψ i) (χ i) 1‖ ^ 2 =
      (Fintype.card (A i) : ℝ) := by
    simpa only [fourier, gaussSum, one_mul] using
      gauss_norm_sq _ (coordinateCharacter_isPrimitive ψ hψ i) (χ i) (hχ i)
  calc
    _ = ∏ i, ‖fourier (coordinateCharacter ψ i) (χ i) 1‖ ^ 2 := by
      rw [product_fourier_factorization, norm_prod, ← Finset.prod_pow]
      rfl
    _ = ∏ i, (Fintype.card (A i) : ℝ) :=
      Finset.prod_congr rfl (fun i _ => hi i)
    _ = _ := by rw [Fintype.card_pi, Nat.cast_prod]

end ProductFields

section Transport
variable {R : Type*} [CommRing R] [Fintype R]
variable {ι : Type*} [Fintype ι] {A : ι → Type*}
variable [∀ i, Field (A i)] [∀ i, Fintype (A i)]

theorem crt_fourier_conj (e : R ≃+* ∀ i, A i)
    (χ : ∀ i, MulChar (A i) ℂ) (hχ : ∀ i, χ i ≠ 1)
    (ψ : AddChar R ℂ) (h : R) :
    fourier ψ (fun x => productCoefficient χ (e x)) h =
      star (productCoefficient χ (e h)) *
        fourier ψ (fun x => productCoefficient χ (e x)) 1 := by
  let φ := transportCharacter e.symm ψ
  have hφ : transportCharacter e φ = ψ := by
    ext x
    simp only [φ, transportCharacter_apply, e.symm_apply_apply]
  have ht (a : R) := transport_fourier e φ (productCoefficient χ) a
  rw [hφ] at ht
  rw [ht h, product_fourier_conj χ hχ φ (e h), ht 1, map_one]

theorem crt_gauss_norm_sq (e : R ≃+* ∀ i, A i)
    (χ : ∀ i, MulChar (A i) ℂ) (hχ : ∀ i, χ i ≠ 1)
    (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) :
    ‖fourier ψ (fun x => productCoefficient χ (e x)) 1‖ ^ 2 = (Fintype.card R : ℝ) := by
  let φ := transportCharacter e.symm ψ
  have hφ : transportCharacter e φ = ψ := by
    ext x
    simp only [φ, transportCharacter_apply, e.symm_apply_apply]
  have ht := transport_fourier e φ (productCoefficient χ) (1 : R)
  rw [hφ, map_one] at ht
  rw [ht, product_gauss_norm_sq χ hχ φ (transportCharacter_isPrimitive e.symm ψ hψ)]
  exact_mod_cast (Fintype.card_congr e.toEquiv).symm

end Transport
end CubicSieve.Gauss
