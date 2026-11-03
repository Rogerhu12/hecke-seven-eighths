import HeckeGeneral.Arithmetic.ProductResidueFourier

/-!
# Gauss sums for the constructed residue-field trace characters

The norm-square identity uses Mathlib's finite-field Gauss product and
complex conjugation. Nontriviality of each multiplicative character is
explicit: the principal character has a different Gauss sum. The CRT
formula then proves the norm square on an actual squarefree quotient.
It does not assert a primitive Gauss identity for a prime-power modulus.
-/

noncomputable section

namespace HeckeGeneral.Arithmetic.ResidueGaussSums

open PeriodicFourier ResidueTraceCharacters ProductResidueFourier IdealMobiusMask
  IsDedekindDomain
open scoped BigOperators ComplexConjugate Classical

section Fields

variable {F : Type*} [Field F] [Fintype F]

theorem gauss_norm_sq (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
    (χ : MulChar F ℂ) (hχ : χ ≠ 1) :
    ‖gaussSum χ ψ‖ ^ 2 = (Fintype.card F : ℝ) := by
  have h := gaussSum_mul_gaussSum_eq_card hχ hψ
  rw [← star_gaussSum_eq] at h
  have hr := congrArg Complex.re h
  simpa [Complex.mul_conj', pow_two] using hr

theorem gauss_norm (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
    (χ : MulChar F ℂ) (hχ : χ ≠ 1) :
    ‖gaussSum χ ψ‖ = Real.sqrt (Fintype.card F) := by
  have h := gauss_norm_sq ψ hψ χ hχ
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ Fintype.card F by positivity)
  have hn := norm_nonneg (gaussSum χ ψ)
  have hr := Real.sqrt_nonneg (Fintype.card F : ℝ)
  nlinarith

theorem gauss_nonzero (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive)
    (χ : MulChar F ℂ) (hχ : χ ≠ 1) : gaussSum χ ψ ≠ 0 := by
  apply gaussSum_ne_zero_of_nontrivial _ hχ hψ
  exact_mod_cast Fintype.card_ne_zero

theorem trace_gauss_norm_sq (χ : MulChar F ℂ) (hχ : χ ≠ 1) :
    ‖gaussSum χ (traceCharacter F)‖ ^ 2 = (Fintype.card F : ℝ) :=
  gauss_norm_sq _ (traceCharacter_isPrimitive F) χ hχ

theorem trace_gauss_nonzero (χ : MulChar F ℂ) (hχ : χ ≠ 1) :
    gaussSum χ (traceCharacter F) ≠ 0 :=
  gauss_nonzero _ (traceCharacter_isPrimitive F) χ hχ

theorem fourier_mulChar_zero (ψ : AddChar F ℂ) (χ : MulChar F ℂ) (hχ : χ ≠ 1) :
    fourier ψ χ 0 = 0 := by
  rw [fourier_zero]
  exact MulChar.sum_eq_zero_of_ne_one hχ

theorem trace_fourier_mulChar_ne_zero (χ : MulChar F ℂ) (hχ : χ ≠ 1) :
    fourier (traceCharacter F) χ 1 ≠ 0 := by
  simpa [fourier, gaussSum] using trace_gauss_nonzero χ hχ

end Fields

section ActualResidues

variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Ring.HasFiniteQuotients R]

theorem residue_gauss_norm_sq (p : HeightOneSpectrum R)
    (χ : MulChar (Residue p) ℂ) (hχ : χ ≠ 1) :
    ‖gaussSum χ (residueCharacter p)‖ ^ 2 = (Fintype.card (Residue p) : ℝ) :=
  gauss_norm_sq _ (residueCharacter_isPrimitive p) χ hχ

theorem residue_gauss_nonzero (p : HeightOneSpectrum R)
    (χ : MulChar (Residue p) ℂ) (hχ : χ ≠ 1) : gaussSum χ (residueCharacter p) ≠ 0 :=
  gauss_nonzero _ (residueCharacter_isPrimitive p) χ hχ

theorem squarefree_gauss_norm_sq (S : Finset (HeightOneSpectrum R))
    (χ : ∀ p : S, MulChar (Residue p.val) ℂ) (hχ : ∀ p, χ p ≠ 1) :
    ‖fourier (squarefreeCharacter S) (crtCoefficient S (fun p => χ p)) 1‖ ^ 2 =
      (Fintype.card (R ⧸ primeProduct S) : ℝ) := by
  rw [squarefree_gauss_factorization, norm_prod, ← Finset.prod_pow]
  simp_rw [residue_gauss_norm_sq _ _ (hχ _)]
  have hc : Fintype.card (R ⧸ primeProduct S) = ∏ p : S, Fintype.card (Residue p.val) := by
    rw [Fintype.card_congr (squarefreeCRT S).toEquiv, Fintype.card_pi]
  exact_mod_cast hc.symm

theorem squarefree_gauss_nonzero (S : Finset (HeightOneSpectrum R))
    (χ : ∀ p : S, MulChar (Residue p.val) ℂ) (hχ : ∀ p, χ p ≠ 1) :
    fourier (squarefreeCharacter S) (crtCoefficient S (fun p => χ p)) 1 ≠ 0 := by
  rw [squarefree_gauss_factorization]
  apply Finset.prod_ne_zero_iff.mpr
  intro p _
  exact residue_gauss_nonzero p.val (χ p) (hχ p)

theorem squarefree_gauss_norm (S : Finset (HeightOneSpectrum R))
    (χ : ∀ p : S, MulChar (Residue p.val) ℂ) (hχ : ∀ p, χ p ≠ 1) :
    ‖fourier (squarefreeCharacter S) (crtCoefficient S (fun p => χ p)) 1‖ =
      Real.sqrt (Fintype.card (R ⧸ primeProduct S)) := by
  have h := squarefree_gauss_norm_sq S χ hχ
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ Fintype.card (R ⧸ primeProduct S) by positivity)
  have hn := norm_nonneg (fourier (squarefreeCharacter S) (crtCoefficient S (fun p => χ p)) 1)
  have hr := Real.sqrt_nonneg (Fintype.card (R ⧸ primeProduct S) : ℝ)
  nlinarith

end ActualResidues

end HeckeGeneral.Arithmetic.ResidueGaussSums
