import HeckeGeneral.Arithmetic.SIntegerPeriodicFourier
import HeckePort.Moments.FullCorrelation

/-!
# The actual orbital divisor transform of a complete Gauss pair

This is the finite-algebra bridge used by the second orbital transform.
Its additive character is the proved primitive, positive S-local phase of
the genuine principal quotient.  Every nonunit mask divisor is retained:
its transform is the sum over the entire frequency fiber, with the exact
quotient cardinality.  The unit-divisor specialization is the full
nonprimitive correlation, including its zero frequency.

No Poisson identity, correlation factorization or energy estimate is an
assumption.  The only finite functions in the general identity are the
original complete coefficient arrays; specializing them to the genuine
sextic characters is literal substitution.
-/

noncomputable section
open scoped NumberField Classical BigOperators

namespace HeckeSkeleton.Moments.EngineStep

open HeckePort.Moments HeckeGeneral.Arithmetic HeckeGeneral.Characters
open NumberField IsDedekindDomain

section Finite

variable {R X Y : Type*} [CommRing R] [Fintype R] [Fintype X] [Fintype Y]

theorem fourierSum_frequency_dilate (ψ : AddChar R ℂ) (place : X → R)
    (f : X → ℂ) (d h : R) :
    fourierSum ψ place f (d * h) =
      fourierSum ψ (fun x => d * place x) f h := by
  unfold fourierSum
  apply Finset.sum_congr rfl
  intro x hx
  congr 2
  ring

/-- Nonunit dilation has its actual full frequency fiber, not a chosen inverse. -/
theorem fullCorrelation_dilate_fiber (left : X → R) (right : Y → R)
    (f : X → ℂ) (g : Y → ℂ) (d h : R) :
    fullCorrelation (fun x => d * left x) (fun y => d * right y) f g h =
      ∑ j : R with d * j = h, fullCorrelation left right f g j := by
  have he (x : X) (y : Y) :
      (if d * left x - d * right y = h then f x * star (g y) else 0) =
        ∑ j : R, if d * j = h then
          (if left x - right y = j then f x * star (g y) else 0) else 0 := by
    have hswap (j : R) :
        (if d * j = h then
          (if left x - right y = j then f x * star (g y) else 0) else 0) =
        (if left x - right y = j then
          (if d * j = h then f x * star (g y) else 0) else 0) := by
      by_cases hd : d * j = h <;> by_cases hj : left x - right y = j <;>
        simp only [hd, hj, ite_true, ite_false]
    simp_rw [hswap]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, mul_sub]
  simp only [fullCorrelation, Finset.sum_filter]
  simp_rw [he]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset Y))
    (t := (Finset.univ : Finset R))]
  rw [Finset.sum_comm (s := (Finset.univ : Finset X))
    (t := (Finset.univ : Finset R))]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hd : d * j = h <;> simp only [hd, ite_true, ite_false, Finset.sum_const_zero]

/-- Exact finite Fourier transform of a complete pair, for every divisor. -/
theorem gauss_pair_divisor_fourier (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive)
    (left : X → R) (right : Y → R) (f : X → ℂ) (g : Y → ℂ) (d h : R) :
    PeriodicFourier.divisorTransform ψ
      (fun a => fourierSum ψ left f a * star (fourierSum ψ right g a)) d h =
      (Fintype.card R : ℂ) *
        ∑ j : R with d * j = -h, fullCorrelation left right f g j := by
  have h := fullCorrelation_fourier ψ hψ (fun x => d * left x)
    (fun y => d * right y) f g (-h)
  rw [fullCorrelation_dilate_fiber] at h
  apply Eq.trans _ h
  simp only [PeriodicFourier.divisorTransform, PeriodicFourier.fourier,
    PeriodicFourier.dilate, fourierSum_frequency_dilate]
  apply Finset.sum_congr rfl
  intro a ha
  congr 2
  ring

/-- The unmasked transform has the precise negative-frequency convention. -/
theorem gauss_pair_fourier (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive)
    (left : X → R) (right : Y → R) (f : X → ℂ) (g : Y → ℂ) (h : R) :
    PeriodicFourier.divisorTransform ψ
      (fun a => fourierSum ψ left f a * star (fourierSum ψ right g a)) 1 h =
      (Fintype.card R : ℂ) * fullCorrelation left right f g (-h) := by
  simpa only [one_mul, Finset.sum_filter, Finset.sum_ite_eq', Finset.mem_univ, ite_true] using
    gauss_pair_divisor_fourier ψ hψ left right f g 1 h

end Finite

section Actual

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → localDifferentExponent K v = 0)
local notation "OS" => S.integer K

/-- The actual orbital finite coefficient, with every nonunit fiber retained. -/
theorem actual_orbital_gauss_pair_divisor_fourier {X Y : Type*}
    [Fintype X] [Fintype Y] (c : OS) (hc : c ≠ 0)
    (left : X → OS ⧸ Ideal.span ({c} : Set OS))
    (right : Y → OS ⧸ Ideal.span ({c} : Set OS))
    (f : X → ℂ) (g : Y → ℂ) (d h : OS) :
    letI := finite_sIntegerPrincipalResidue K S c hc
    letI := Fintype.ofFinite (OS ⧸ Ideal.span ({c} : Set OS))
    let ψ := sIntegerActualModulusAddCharacter K S hS c hc
    sIntegerPeriodicDivisorFourier K S hS c hc
      (fun a => fourierSum ψ left f a * star (fourierSum ψ right g a)) d
      (Ideal.Quotient.mk _ h) =
      (Fintype.card (OS ⧸ Ideal.span ({c} : Set OS)) : ℂ) *
        ∑ j : OS ⧸ Ideal.span ({c} : Set OS)
          with Ideal.Quotient.mk _ d * j = -Ideal.Quotient.mk _ h,
            fullCorrelation left right f g j := by
  letI := finite_sIntegerPrincipalResidue K S c hc
  letI := Fintype.ofFinite (OS ⧸ Ideal.span ({c} : Set OS))
  exact gauss_pair_divisor_fourier
    (sIntegerActualModulusAddCharacter K S hS c hc)
    (sIntegerActualModulusAddCharacter_isPrimitive K S hS c hc)
    left right f g (Ideal.Quotient.mk _ d) (Ideal.Quotient.mk _ h)

/-- At a product modulus the actual unmasked coefficient is the complete
nonprimitive correlation of its two original multiplicative characters. -/
theorem actual_orbital_full_correlation (u v : OS) (hu : u ≠ 0) (hv : v ≠ 0)
    (χu : MulChar (OS ⧸ Ideal.span ({u} : Set OS)) ℂ)
    (χv : MulChar (OS ⧸ Ideal.span ({v} : Set OS)) ℂ) (h : OS) :
    letI := finite_sIntegerPrincipalResidue K S u hu
    letI := finite_sIntegerPrincipalResidue K S v hv
    letI := finite_sIntegerPrincipalResidue K S (u * v) (mul_ne_zero hu hv)
    letI := Fintype.ofFinite (OS ⧸ Ideal.span ({u} : Set OS))
    letI := Fintype.ofFinite (OS ⧸ Ideal.span ({v} : Set OS))
    letI := Fintype.ofFinite (OS ⧸ Ideal.span ({u * v} : Set OS))
    let ψ := sIntegerActualModulusAddCharacter K S hS (u * v) (mul_ne_zero hu hv)
    sIntegerPeriodicDivisorFourier K S hS (u * v) (mul_ne_zero hu hv)
      (fun a => fourierSum ψ (scaledResidue u v (u * v) rfl) χu a *
        star (fourierSum ψ (scaledResidue v u (u * v) (mul_comm u v)) χv a)) 1
      (Ideal.Quotient.mk _ h) =
      (Fintype.card (OS ⧸ Ideal.span ({u * v} : Set OS)) : ℂ) *
        fullModulusCorrelation u v χu χv (-h) := by
  letI := finite_sIntegerPrincipalResidue K S u hu
  letI := finite_sIntegerPrincipalResidue K S v hv
  letI := finite_sIntegerPrincipalResidue K S (u * v) (mul_ne_zero hu hv)
  letI := Fintype.ofFinite (OS ⧸ Ideal.span ({u} : Set OS))
  letI := Fintype.ofFinite (OS ⧸ Ideal.span ({v} : Set OS))
  letI := Fintype.ofFinite (OS ⧸ Ideal.span ({u * v} : Set OS))
  simpa only [sIntegerPeriodicDivisorFourier, map_one, fullModulusCorrelation, map_neg]
    using gauss_pair_fourier
      (sIntegerActualModulusAddCharacter K S hS (u * v) (mul_ne_zero hu hv))
      (sIntegerActualModulusAddCharacter_isPrimitive K S hS (u * v) (mul_ne_zero hu hv))
      (scaledResidue u v (u * v) rfl)
      (scaledResidue v u (u * v) (mul_comm u v)) χu χv (Ideal.Quotient.mk _ h)

end Actual

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.gauss_pair_divisor_fourier
#print axioms HeckeSkeleton.Moments.EngineStep.actual_orbital_gauss_pair_divisor_fourier
#print axioms HeckeSkeleton.Moments.EngineStep.actual_orbital_full_correlation
