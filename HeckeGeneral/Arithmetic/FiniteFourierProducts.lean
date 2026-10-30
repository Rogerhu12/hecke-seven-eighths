import HeckeGeneral.Arithmetic.FiniteFourierConvolution

/-!
# Products, injectivity and convolution algebra

The product rule follows from actual Fourier inversion. The cardinality
factor is retained, which is essential when ideal masks are transformed.
Convolution commutativity and associativity are then consequences of this
actual injective transform, rather than assumed algebraic laws.
-/

noncomputable section

namespace HeckeGeneral.Arithmetic.PeriodicFourier

open scoped BigOperators Classical

variable {R : Type*} [CommRing R] [Fintype R]

theorem fourier_injective (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) :
    Function.Injective (fourier ψ) := by
  intro f g hfg
  funext a
  calc
    f a = inverse ψ (fourier ψ f) a := (inverse_fourier ψ hψ f a).symm
    _ = inverse ψ (fourier ψ g) a := by rw [hfg]
    _ = g a := inverse_fourier ψ hψ g a

theorem fourier_eq_iff (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) (f g : R → ℂ) :
    fourier ψ f = fourier ψ g ↔ f = g := (fourier_injective ψ hψ).eq_iff

theorem fourier_product (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive)
    (f g : R → ℂ) (h : R) :
    fourier ψ (fun a => f a * g a) h =
      (Fintype.card R : ℂ)⁻¹ * convolution (fourier ψ f) (fourier ψ g) h := by
  have hf : (fun a => f a * g a) = fun a => (Fintype.card R : ℂ)⁻¹ *
      ∑ k : R, fourier ψ f k * (ψ (-(k * a)) * g a) := by
    funext a
    have hfa : f a = (Fintype.card R : ℂ)⁻¹ *
        ∑ k : R, fourier ψ f k * ψ (-(k * a)) := (inverse_fourier ψ hψ f a).symm
    conv_lhs => rw [hfa]
    rw [mul_assoc, Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hk (k : R) : fourier ψ (fun a => fourier ψ f k * (ψ (-(k * a)) * g a)) h =
      fourier ψ f k * fourier ψ g (h - k) := by
    rw [fourier_const_mul]
    unfold fourier
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    change (ψ (-(k * a)) * g a) * ψ (h * a) = g a * ψ ((h - k) * a)
    rw [mul_comm (ψ (-(k * a))) (g a), mul_assoc, ← ψ.map_add_eq_mul]
    congr 2
    ring
  rw [hf, fourier_const_mul, fourier_sum Finset.univ]
  simp only [hk, convolution]

theorem card_mul_fourier_product (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive)
    (f g : R → ℂ) (h : R) :
    (Fintype.card R : ℂ) * fourier ψ (fun a => f a * g a) h =
      convolution (fourier ψ f) (fourier ψ g) h := by
  rw [fourier_product ψ hψ]
  have hc : (Fintype.card R : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]

theorem convolution_comm (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) (f g : R → ℂ) :
    convolution f g = convolution g f := by
  apply fourier_injective ψ hψ
  funext h
  simp only [fourier_convolution, mul_comm]

theorem convolution_assoc (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) (f g k : R → ℂ) :
    convolution (convolution f g) k = convolution f (convolution g k) := by
  apply fourier_injective ψ hψ
  funext h
  simp only [fourier_convolution, mul_assoc]

def deltaZero (a : R) : ℂ := if a = 0 then 1 else 0

@[simp] theorem fourier_deltaZero (ψ : AddChar R ℂ) (h : R) :
    fourier ψ deltaZero h = 1 := by
  simp [fourier, deltaZero]

theorem convolution_deltaZero (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) (f : R → ℂ) :
    convolution f deltaZero = f := by
  apply fourier_injective ψ hψ
  funext h
  simp [fourier_convolution]

theorem deltaZero_convolution (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) (f : R → ℂ) :
    convolution deltaZero f = f := by
  rw [convolution_comm ψ hψ, convolution_deltaZero ψ hψ]

theorem fourier_fourier (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) (f : R → ℂ) (a : R) :
    fourier ψ (fourier ψ f) a = (Fintype.card R : ℂ) * f (-a) := by
  simpa only [fourier, mul_neg, neg_neg, mul_comm] using inversion_sum ψ hψ f (-a)

theorem fourier_surjective (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) :
    Function.Surjective (fourier ψ) := by
  intro g
  refine ⟨fun a => (Fintype.card R : ℂ)⁻¹ * fourier ψ g (-a), ?_⟩
  apply fourier_injective ψ hψ
  funext h
  rw [fourier_fourier ψ hψ]
  have hc : (Fintype.card R : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [neg_neg]
  rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]

end HeckeGeneral.Arithmetic.PeriodicFourier
