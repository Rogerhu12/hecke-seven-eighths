import CubicSieve.GaussPairCRT

/-! Exact mixed Fourier factorization through two-factor CRT.
Frequencies are arbitrary elements; zero and nonunit frequencies are retained. -/

set_option autoImplicit false
noncomputable section
namespace CubicSieve.GaussPairFourierCRT

open HeckeGeneral.Arithmetic.PeriodicFourier
open CubicSieve.GaussPairCRT
open scoped Classical BigOperators

variable {T R V : Type*} [CommRing T] [CommRing R] [CommRing V]

def coefficient (e : T ≃+* R × V) (χ : MulChar R ℂ) (η : MulChar V ℂ) (x : T) : ℂ :=
  χ (e x).1 * η (e x).2

theorem leftAddChar_mulShift (e : T ≃+* R × V) (ψ : AddChar T ℂ) (h : T) :
    leftAddChar e (ψ.mulShift h) = (leftAddChar e ψ).mulShift (e h).1 := by
  ext r
  change ψ (h * e.symm (r, 0)) = ψ (e.symm ((e h).1 * r, 0))
  congr 1
  apply e.injective
  simp only [map_mul, e.apply_symm_apply, Prod.mul_def, mul_zero]

theorem rightAddChar_mulShift (e : T ≃+* R × V) (ψ : AddChar T ℂ) (h : T) :
    rightAddChar e (ψ.mulShift h) = (rightAddChar e ψ).mulShift (e h).2 := by
  ext r
  change ψ (h * e.symm (0, r)) = ψ (e.symm (0, (e h).2 * r))
  congr 1
  apply e.injective
  simp only [map_mul, e.apply_symm_apply, Prod.mul_def, mul_zero]

theorem product_fourier [Fintype T] [Fintype R] [Fintype V]
    (e : T ≃+* R × V) (χ : MulChar R ℂ) (η : MulChar V ℂ)
    (ψ : AddChar T ℂ) (h : T) :
    fourier ψ (coefficient e χ η) h =
      fourier (leftAddChar e ψ) χ (e h).1 * fourier (rightAddChar e ψ) η (e h).2 := by
  have hg := gauss_sum_crt e χ η (ψ.mulShift h)
  rw [leftAddChar_mulShift, rightAddChar_mulShift] at hg
  simpa only [fourier, coefficient, gaussSum, AddChar.mulShift_apply] using hg

theorem eigen_mulShift [Fintype R] (χ : MulChar R ℂ) (ψ : AddChar R ℂ)
    (H : ∀ h : R, fourier ψ χ h = star (χ h) * gaussSum χ ψ) (v h : R) :
    fourier (ψ.mulShift v) χ h = star (χ h) * gaussSum χ (ψ.mulShift v) := by
  have hs : fourier (ψ.mulShift v) χ h = fourier ψ χ (v * h) := by
    simp only [fourier, AddChar.mulShift_apply, mul_assoc]
  have h0 : gaussSum χ (ψ.mulShift v) = fourier ψ χ v := by
    simp only [gaussSum, fourier, AddChar.mulShift_apply]
  rw [hs, H, map_mul, star_mul, h0, H]
  ring

/-- The product eigenidentity follows from the two actual coordinate eigenidentities. -/
theorem product_eigen [Fintype T] [Fintype R] [Fintype V]
    (e : T ≃+* R × V) (χ : MulChar R ℂ) (η : MulChar V ℂ) (ψ : AddChar T ℂ)
    (Hχ : ∀ h : R, fourier (leftAddChar e ψ) χ h =
      star (χ h) * gaussSum χ (leftAddChar e ψ))
    (Hη : ∀ h : V, fourier (rightAddChar e ψ) η h =
      star (η h) * gaussSum η (rightAddChar e ψ)) (h : T) :
    fourier ψ (coefficient e χ η) h =
      star (coefficient e χ η h) * fourier ψ (coefficient e χ η) 1 := by
  have h0 : fourier ψ (coefficient e χ η) 1 =
      gaussSum χ (leftAddChar e ψ) * gaussSum η (rightAddChar e ψ) := by
    simpa only [fourier, coefficient, one_mul] using gauss_sum_crt e χ η ψ
  rw [product_fourier, Hχ, Hη, h0]
  simp only [coefficient, star_mul]
  ring

end CubicSieve.GaussPairFourierCRT
