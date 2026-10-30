import HeckeGeneral.Arithmetic.ResidueTraceCharacters

/-!
# Tensor and CRT factorization of the finite transform

Both the coefficient and the additive character are genuine functions
on the product ring. The CRT transform is transported along the actual
ring equivalence. No CRT factorization is assumed as an input.
-/

noncomputable section

namespace HeckeGeneral.Arithmetic.ProductResidueFourier

open PeriodicFourier ResidueTraceCharacters IdealMobiusMask IsDedekindDomain
open scoped BigOperators ComplexConjugate Classical

section Tensor

variable {ι : Type*} [Fintype ι] {A : ι → Type*}
  [∀ i, CommRing (A i)] [∀ i, Fintype (A i)]

def tensorCoefficient (f : ∀ i, A i → ℂ) (a : ∀ i, A i) : ℂ := ∏ i, f i (a i)

omit [∀ i, CommRing (A i)] in
theorem tensor_sum (f : ∀ i, A i → ℂ) :
    ∑ a : ∀ i, A i, tensorCoefficient f a = ∏ i, ∑ a : A i, f i a :=
  (Fintype.prod_sum f).symm

theorem tensor_fourier (ψ : ∀ i, AddChar (A i) ℂ) (f : ∀ i, A i → ℂ)
    (h : ∀ i, A i) :
    fourier (productCharacter ψ) (tensorCoefficient f) h = ∏ i, fourier (ψ i) (f i) (h i) := by
  unfold fourier tensorCoefficient
  simp only [productCharacter_apply, Pi.mul_apply, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i a => f i a * ψ i (h i * a))).symm

omit [∀ i, Fintype (A i)] in
theorem tensor_dilate (f : ∀ i, A i → ℂ) (d : ∀ i, A i) :
    dilate d (tensorCoefficient f) = tensorCoefficient (fun i => dilate (d i) (f i)) := rfl

theorem tensor_divisorTransform (ψ : ∀ i, AddChar (A i) ℂ) (f : ∀ i, A i → ℂ)
    (d h : ∀ i, A i) :
    divisorTransform (productCharacter ψ) (tensorCoefficient f) d h =
      ∏ i, divisorTransform (ψ i) (f i) (d i) (h i) := by
  unfold divisorTransform
  rw [tensor_dilate]
  exact tensor_fourier ψ _ h

omit [∀ i, CommRing (A i)] in
theorem tensor_energy (f : ∀ i, A i → ℂ) :
    energy (tensorCoefficient f) = ∏ i, energy (f i) := by
  unfold energy tensorCoefficient
  simp only [norm_prod, ← Finset.prod_pow]
  exact (Fintype.prod_sum (fun i a => ‖f i a‖ ^ 2)).symm

omit [∀ i, CommRing (A i)] in
theorem tensor_l1Mass (f : ∀ i, A i → ℂ) :
    l1Mass (tensorCoefficient f) = ∏ i, l1Mass (f i) := by
  unfold l1Mass tensorCoefficient
  simp only [norm_prod]
  exact (Fintype.prod_sum (fun i a => ‖f i a‖)).symm

theorem tensor_gaussSum (ψ : ∀ i, AddChar (A i) ℂ) (χ : ∀ i, MulChar (A i) ℂ) :
    fourier (productCharacter ψ) (tensorCoefficient (fun i => χ i)) 1 =
      ∏ i, gaussSum (χ i) (ψ i) := by
  rw [tensor_fourier]
  apply Finset.prod_congr rfl
  intro i _
  simp [fourier, gaussSum]

end Tensor

section Transport

variable {R T : Type*} [CommRing R] [CommRing T] [Fintype R] [Fintype T]

theorem transport_fourier (e : R ≃+* T) (ψ : AddChar T ℂ) (f : T → ℂ) (h : R) :
    fourier (transportCharacter e ψ) (fun a => f (e a)) h = fourier ψ f (e h) := by
  unfold fourier
  refine Fintype.sum_bijective _ e.bijective _ _ (fun a => ?_)
  simp only [transportCharacter_apply, map_mul]

theorem transport_divisorTransform (e : R ≃+* T) (ψ : AddChar T ℂ)
    (f : T → ℂ) (d h : R) :
    divisorTransform (transportCharacter e ψ) (fun a => f (e a)) d h =
      divisorTransform ψ f (e d) (e h) := by
  unfold divisorTransform
  have hd : dilate d (fun a => f (e a)) = fun a => dilate (e d) f (e a) := by
    funext a
    simp only [dilate, map_mul]
  rw [hd, transport_fourier]

theorem transport_energy (e : R ≃+* T) (f : T → ℂ) :
    energy (fun a => f (e a)) = energy f := by
  unfold energy
  exact Fintype.sum_bijective _ e.bijective _ _ (fun _ => rfl)

theorem transport_l1Mass (e : R ≃+* T) (f : T → ℂ) :
    l1Mass (fun a => f (e a)) = l1Mass f := by
  unfold l1Mass
  exact Fintype.sum_bijective _ e.bijective _ _ (fun _ => rfl)

end Transport

section Squarefree

variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Ring.HasFiniteQuotients R]

def crtCoefficient (S : Finset (HeightOneSpectrum R))
    (f : ∀ p : S, Residue p.val → ℂ) (a : R ⧸ primeProduct S) : ℂ :=
  tensorCoefficient f (squarefreeCRT S a)

theorem squarefree_tensor_fourier (S : Finset (HeightOneSpectrum R))
    (f : ∀ p : S, Residue p.val → ℂ) (h : R ⧸ primeProduct S) :
    fourier (squarefreeCharacter S) (crtCoefficient S f) h =
      ∏ p : S, fourier (residueCharacter p.val) (f p) (squarefreeCRT S h p) := by
  let : DecidableEq S := Classical.decEq _
  unfold squarefreeCharacter crtCoefficient
  rw [transport_fourier]
  exact tensor_fourier (fun p : S => residueCharacter p.val) f (squarefreeCRT S h)

theorem squarefree_tensor_divisorTransform (S : Finset (HeightOneSpectrum R))
    (f : ∀ p : S, Residue p.val → ℂ) (d h : R ⧸ primeProduct S) :
    divisorTransform (squarefreeCharacter S) (crtCoefficient S f) d h =
      ∏ p : S, divisorTransform (residueCharacter p.val) (f p)
        (squarefreeCRT S d p) (squarefreeCRT S h p) := by
  let : DecidableEq S := Classical.decEq _
  unfold squarefreeCharacter crtCoefficient
  rw [transport_divisorTransform]
  exact tensor_divisorTransform (fun p : S => residueCharacter p.val) f
    (squarefreeCRT S d) (squarefreeCRT S h)

theorem squarefree_tensor_energy (S : Finset (HeightOneSpectrum R))
    (f : ∀ p : S, Residue p.val → ℂ) :
    energy (crtCoefficient S f) = ∏ p : S, energy (f p) := by
  let : DecidableEq S := Classical.decEq _
  unfold crtCoefficient
  rw [transport_energy]
  exact tensor_energy f

theorem squarefree_tensor_mass (S : Finset (HeightOneSpectrum R))
    (f : ∀ p : S, Residue p.val → ℂ) :
    l1Mass (crtCoefficient S f) = ∏ p : S, l1Mass (f p) := by
  let : DecidableEq S := Classical.decEq _
  unfold crtCoefficient
  rw [transport_l1Mass]
  exact tensor_l1Mass f

theorem squarefree_gauss_factorization (S : Finset (HeightOneSpectrum R))
    (χ : ∀ p : S, MulChar (Residue p.val) ℂ) :
    fourier (squarefreeCharacter S) (crtCoefficient S (fun p => χ p)) 1 =
      ∏ p : S, gaussSum (χ p) (residueCharacter p.val) := by
  rw [squarefree_tensor_fourier]
  apply Finset.prod_congr rfl
  intro p _
  simp [fourier, gaussSum]

end Squarefree

end HeckeGeneral.Arithmetic.ProductResidueFourier
