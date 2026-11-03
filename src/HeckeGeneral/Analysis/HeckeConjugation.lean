import HeckeGeneral.Analysis.HeckeDerivative

/-!
# Complex conjugation and inverse Hecke characters

The inverse is taken in the actual group of continuous unitary idèle class
characters. Its local coefficients are the complex conjugates, including
the zero extension at ramified places. Positive actual ideal norms ensure
that conjugating the complex power introduces no logarithm branch change.
The symmetry extends to all logarithmic moments and hence to all derivatives
on the proved half-plane of absolute convergence.
-/

noncomputable section

namespace HeckeGeneral.Characters

open NumberField IsDedekindDomain
open scoped ComplexConjugate Classical nonZeroDivisors

variable (K : Type*) [Field K] [NumberField K]

theorem unramifiedAt_inv_iff (χ : HeckeCharacter K) (p : HeightOneSpectrum (𝓞 K)) :
    UnramifiedAt K χ⁻¹ p ↔ UnramifiedAt K χ p := by
  constructor
  · intro h
    simpa only [inv_inv] using h.inv K
  · exact fun h => h.inv K

/-- Inversion preserves ramification and conjugates the genuine local Euler value. -/
theorem primeCoefficient_inv (χ : HeckeCharacter K) (p : HeightOneSpectrum (𝓞 K)) :
    primeCoefficient K χ⁻¹ p = conj (primeCoefficient K χ p) := by
  unfold primeCoefficient
  rw [unramifiedAt_inv_iff]
  split_ifs with h
  · change ((localComponent K p χ (localUniformizerUnit K p))⁻¹ : ℂ) = _
    exact Circle.coe_inv_eq_conj _
  · simp

end HeckeGeneral.Characters

namespace HeckeGeneral.Arithmetic

open IsDedekindDomain UniqueFactorizationMonoid
open scoped ComplexConjugate Classical nonZeroDivisors

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

theorem primeIdealValue_conjugate (a : HeightOneSpectrum R → ℂ) (P : Ideal R) :
    primeIdealValue (fun p => conj (a p)) P = conj (primeIdealValue a P) := by
  unfold primeIdealValue
  split_ifs <;> simp

/-- Conjugation commutes with actual ideal unique-factorization coefficients. -/
theorem idealCoefficient_conjugate (a : HeightOneSpectrum R → ℂ) (I : Ideal R) :
    idealCoefficient (fun p => conj (a p)) I = conj (idealCoefficient a I) := by
  by_cases hI : I = ⊥
  · subst I
    simp
  simp only [idealCoefficient, ite_eq_right hI]
  have hmap : primeIdealValue (fun p => conj (a p)) = fun P => conj (primeIdealValue a P) :=
    funext (primeIdealValue_conjugate a)
  rw [hmap]
  change ((normalizedFactors I).map ((starRingEnd ℂ) ∘ primeIdealValue a)).prod = _
  rw [← Multiset.map_map, ← map_multiset_prod (starRingEnd ℂ)]

theorem nonzeroIdealCoefficient_conjugate (a : HeightOneSpectrum R → ℂ)
    (I : (Ideal R)⁰) :
    nonzeroIdealCoefficient (fun p => conj (a p)) I = conj (nonzeroIdealCoefficient a I) :=
  idealCoefficient_conjugate a I.val

end HeckeGeneral.Arithmetic

namespace HeckeGeneral.Analysis

open NumberField HeckeGeneral.Characters HeckeGeneral.Arithmetic
open scoped ComplexConjugate Topology nonZeroDivisors

variable (K : Type*) [Field K] [NumberField K]

/-- Conjugation of the ideal term is exact because the base is positive real. -/
theorem idealDirichletTerm_conjugate (a : NonzeroIdeal K → ℂ) (s : ℂ)
    (I : NonzeroIdeal K) :
    dirichletTerm (idealNorm K) (fun J => conj (a J)) (conj s) I =
      conj (dirichletTerm (idealNorm K) a s I) := by
  have harg : Complex.arg (idealNorm K I : ℂ) ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg (idealNorm_pos K I).le]
    exact ne_of_lt Real.pi_pos
  have hpow : (idealNorm K I : ℂ) ^ (-(conj s)) =
      conj ((idealNorm K I : ℂ) ^ (-s)) := by
    simpa only [map_neg, Complex.conj_ofReal] using
      Complex.cpow_conj (idealNorm K I : ℂ) (-s) harg
  simp only [dirichletTerm, hpow, map_mul]

theorem idealDirichletSeries_conjugate (a : NonzeroIdeal K → ℂ) (s : ℂ) :
    idealDirichletSeries K (fun I => conj (a I)) (conj s) =
      conj (idealDirichletSeries K a s) := by
  unfold idealDirichletSeries dirichletSeries
  rw [Complex.conj_tsum]
  exact tsum_congr (idealDirichletTerm_conjugate K a s)

theorem idealLogTerm_conjugate (a : NonzeroIdeal K → ℂ) (k : ℕ) (s : ℂ)
    (I : NonzeroIdeal K) :
    idealLogTerm K (fun J => conj (a J)) k (conj s) I = conj (idealLogTerm K a k s I) := by
  simp only [idealLogTerm, idealDirichletTerm_conjugate, map_mul, map_pow,
    map_neg, Complex.conj_ofReal]

theorem idealLogSeries_conjugate (a : NonzeroIdeal K → ℂ) (k : ℕ) (s : ℂ) :
    idealLogSeries K (fun I => conj (a I)) k (conj s) = conj (idealLogSeries K a k s) := by
  unfold idealLogSeries
  rw [Complex.conj_tsum]
  exact tsum_congr (idealLogTerm_conjugate K a k s)

/-- The coefficient symmetry follows from actual local components and ideal factorization. -/
theorem heckeIdealCoefficient_inv (χ : HeckeCharacter K) (I : NonzeroIdeal K) :
    heckeIdealCoefficient K χ⁻¹ I = conj (heckeIdealCoefficient K χ I) := by
  have hp : primeCoefficient K χ⁻¹ = fun p => conj (primeCoefficient K χ p) :=
    funext (primeCoefficient_inv K χ)
  unfold heckeIdealCoefficient
  rw [hp, nonzeroIdealCoefficient_conjugate]

/-- In its convergence domain this is the ordinary conjugation symmetry of genuine sums. -/
theorem heckeLSeries_inv_conjugate (χ : HeckeCharacter K) (s : ℂ) :
    heckeLSeries K χ⁻¹ (conj s) = conj (heckeLSeries K χ s) := by
  unfold heckeLSeries
  rw [show heckeIdealCoefficient K χ⁻¹ = fun I => conj (heckeIdealCoefficient K χ I)
    from funext (heckeIdealCoefficient_inv K χ)]
  exact idealDirichletSeries_conjugate K _ s

theorem heckeDerivativeSeries_inv_conjugate (χ : HeckeCharacter K) (k : ℕ) (s : ℂ) :
    heckeDerivativeSeries K χ⁻¹ k (conj s) = conj (heckeDerivativeSeries K χ k s) := by
  unfold heckeDerivativeSeries
  rw [show heckeIdealCoefficient K χ⁻¹ = fun I => conj (heckeIdealCoefficient K χ I)
    from funext (heckeIdealCoefficient_inv K χ)]
  exact idealLogSeries_conjugate K _ k s

/-- The symmetry of higher derivatives uses convergent log-moment identities. -/
theorem iteratedDeriv_heckeLSeries_inv_conjugate (χ : HeckeCharacter K)
    (k : ℕ) {s : ℂ} (hs : 1 < s.re) :
    iteratedDeriv k (heckeLSeries K χ⁻¹) (conj s) =
      conj (iteratedDeriv k (heckeLSeries K χ) s) := by
  rw [iteratedDeriv_heckeLSeries K _ k (by simpa using hs),
    iteratedDeriv_heckeLSeries K χ k hs, heckeDerivativeSeries_inv_conjugate]

theorem heckeLogDerivative_inv_conjugate (χ : HeckeCharacter K)
    {s : ℂ} (hs : 1 < s.re) :
    heckeLogDerivative K χ⁻¹ (conj s) = conj (heckeLogDerivative K χ s) := by
  rw [heckeLogDerivative_eq_series_quotient K _ (by simpa using hs),
    heckeLogDerivative_eq_series_quotient K χ hs,
    heckeDerivativeSeries_inv_conjugate, heckeLSeries_inv_conjugate, map_div₀]

end HeckeGeneral.Analysis
