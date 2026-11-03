import Expansion.ActualAnnularIdentification
import Expansion.ActualDetectorSaturation
import Expansion.DetectorProductBudget
import Expansion.TerminalFourierTail
import HeckeGeneral.Analysis.DetectorSaturation

/-!
# Saturation of the actual pair selected from the terminal source

A quarter-sized terminal source is extracted into two complete smooth
annular polynomials at one Fourier frequency. The same literal factors
are identified with the deleted Hecke polynomials controlled by the
buffered Mellin estimates. Fixed constants and dyadic counts are absorbed
before any row or dyadic pair is selected. All upper estimates, the product
spike, individual saturation, and the short plain length are conclusions.

The remaining source premise is the output of the actual zero-to-terminal
construction. No polynomial upper bound or saturation is an assumption.
-/

set_option autoImplicit false
noncomputable section
namespace Expansion.ActualTerminalSaturation

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ExpansionBufferedPolynomials
open HeckeGeneral.Analysis.IdealMobiusReciprocal
open HeckeGeneral.Analysis.ExpansionScaleBounds
open HeckeGeneral.Bridge
open HeckeSkeleton.HeckeConductorNorm HeckeSkeleton.ExplicitHeckeFunctionalEquation
open HeckeSkeleton.HeckeBufferedReciprocal
open ExpansionDetector.Fourier ExpansionDetector.IdealCutoff
open Expansion.ActualAnnularIdentification Expansion.ActualDetectorSaturation
open scoped Classical BigOperators ContDiff

variable (K : Type) [Field K] [NumberField K]

/-- The literal inverse factor of the actual source extraction. -/
def inverseDetectorValue (χ : HeckeCharacter K)
    (E : Finset (HeightOneSpectrum (𝓞 K))) (V : ℝ → ℂ)
    (D U : ℝ) (j : ℕ) (β ν : ℝ) : ℂ :=
  normalizedPolynomial (nonzeroTerminalSet (6 * U ^ (21 : ℕ)))
    (Expansion.Dyadic.inverseRawCoefficient
      (idealCoefficientHom (deletePrimes K E (primeCoefficient K χ))) V D)
    Expansion.Dyadic.idealNorm Expansion.Dyadic.annularProfile ((2 : ℝ) ^ j) β ν

/-- The literal plain factor of the same actual source extraction. -/
def plainDetectorValue (χ : HeckeCharacter K)
    (E : Finset (HeightOneSpectrum (𝓞 K))) (U : ℝ) (k : ℕ) (β ν : ℝ) : ℂ :=
  normalizedPolynomial (nonzeroTerminalSet (6 * U ^ (21 : ℕ)))
    (idealCoefficientHom (deletePrimes K E (primeCoefficient K χ)))
    Expansion.Dyadic.idealNorm Expansion.Dyadic.annularProfile ((2 : ℝ) ^ k) β ν

/-- The common threshold precedes the arithmetic row, zero, physical
heights, source cutoff, dyadic pair, and Fourier frequency. The physical
padding includes the exact Fourier factor `2*pi`. -/
theorem exists_actual_terminal_saturation
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (arch : InfinitePlace K → ℝ) (weight : InfinitePlace K → ℤ)
    {e ε : ℝ} (he : 0 < e) (he' : e < 1 / 1000) (hε : 0 < ε)
    (V : ℝ → ℂ) (hV : ContDiff ℝ ∞ V)
    (hone : ∀ x : ℝ, x ≤ 1 → V x = 1)
    (hzero : ∀ x : ℝ, 2 ≤ x → V x = 0)
    (hVnorm : ∀ x : ℝ, ‖V x‖ ≤ 1)
    (R θ τ η : ℝ) (hR : 1 ≤ R) (hθ : 0 ≤ θ) (hτ : 0 < τ) (hη : 0 < η)
    (hforward : 132 * e + 2 * ε + heightDegree K * ε * θ ≤ η / 4)
    (hreflected : 12 * e + 2 * ε + heightDegree K * θ * (1 + ε) ≤ η / 4)
    (CZ : ℝ) (hCZ : 0 ≤ CZ)
    (hzeta : Summable (fun I : NonzeroIntegralIdeal (K := K) =>
      nonzeroIdealNorm I ^ (-2 : ℝ)))
    (hCZsum : (∑' I : NonzeroIntegralIdeal (K := K),
      nonzeroIdealNorm I ^ (-2 : ℝ)) ≤ CZ) :
    ∃ U₀ : ℝ, 6 ≤ U₀ ∧ ∀ (χ : HeckeCharacter K)
      (I : Ideal (𝓞 K)) (E : Finset (HeightOneSpectrum (𝓞 K)))
      (U a H Hupper D : ℝ) (s : ℂ),
      (∀ t : ℝ, χ ≠ heckeNormTwist K t) →
      (fun v => heckeRadialParameter K v χ) = arch → heckeArchWeight K χ = weight →
      I ≠ 0 → (∀ p ∈ E, p.asIdeal ∣ I) →
      U₀ ≤ U → 51 / 100 ≤ a → a ≤ s.re → s.re ≤ 1 → 0 < D →
      (Ideal.absNorm I : ℝ) ≤ R * U → heckeConductorScale K χ ≤ R * U →
      2 + Hupper ≤ R * U ^ θ → U ^ τ ≤ H →
      |s.im| + 2 * Real.pi * (U ^ τ / (8 * Real.pi + 8)) + H + 3 / 2 ≤ Hupper →
      ZeroUpperBound K χ Hupper (a + 2 * e) →
      (1 / 4 : ℝ) ≤ ‖∑ J ∈ terminalIdealSet (U ^ (21 : ℕ)),
        terminalTerm (idealCoefficientHom (deletePrimes K E (primeCoefficient K χ)))
          V V D (U ^ (21 : ℕ))
          (fun n => (n : ℂ) ^ (-s) *
            (Real.exp (-(n : ℝ) / U ^ (20 : ℕ)) : ℂ)) J‖ →
      let n := Expansion.Dyadic.dyadicCap (3 * U ^ (21 : ℕ))
      ∃ j ≤ n, ∃ k ≤ n, ∃ ξ : ℝ,
        ‖ξ‖ ≤ U ^ τ / (8 * Real.pi + 8) ∧
        ((2 : ℝ) ^ j < 4 * D ∧ D / 8 < (2 : ℝ) ^ j * (2 : ℝ) ^ k ∧
          (2 : ℝ) ^ j * (2 : ℝ) ^ k < 8 * U ^ (21 : ℕ)) ∧
        let r := Expansion.Dyadic.dyadicLength U j
        let m := Expansion.Dyadic.dyadicLength U k
        let ν := 2 * Real.pi * ξ - s.im
        let M := inverseDetectorValue K χ E V D U j s.re ν
        let S := plainDetectorValue K χ E U k s.re ν
        U ^ ((2 * a - 1) * (r + m) - η) ≤ ‖M * S‖ ^ 2 ∧
        ‖M‖ ^ 2 ≤ U ^ ((2 * a - 1) * r + η) ∧
        ‖S‖ ^ 2 ≤ U ^ ((2 * a - 1) * min m (1 - m) + η) ∧
        U ^ ((2 * a - 1) * r - 2 * η) ≤ ‖M‖ ^ 2 ∧
        U ^ ((2 * a - 1) * m - 2 * η) ≤ ‖S‖ ^ 2 ∧
        m ≤ 1 / 2 + 75 * η ∧
        Real.log D / Real.log U - 1 / 2 - 75 * η - Real.log 8 / Real.log U ≤ r := by
  obtain ⟨C, U₁, hC, hU₁, hsource⟩ :=
    Expansion.Dyadic.actual_terminal_product_eventually (K := K)
      V hV hone hzero τ hτ CZ hCZ hzeta hCZsum
  obtain ⟨U₂, hU₂, hupper⟩ := exists_actual_normalized_square_bounds K
    hcomplex arch weight he he' hε dyadicMellinProfile V hV hone hzero
    R θ τ η hR hθ hτ hη hforward hreflected
  obtain ⟨U₃, hU₃, hspike⟩ :=
    Expansion.Dyadic.exists_terminal_product_power_spike C η hC.le hη
  refine ⟨max 6 (max U₁ (max U₂ U₃)), le_max_left _ _, ?_⟩
  intro χ I E U a H Hupper D s hχ harch hweight hI hE hU ha hβ hβ'
    hD hnorm hconductor hheight hHlower hpadding hzeroUpper hterminal
  have hU6 : 6 ≤ U := (le_max_left _ _).trans hU
  have hUgt : 1 < U := by linarith
  have hUpos : 0 < U := by linarith
  have hUleft : U₁ ≤ U := (le_max_left _ _).trans ((le_max_right _ _).trans hU)
  have hUmid : U₂ ≤ U :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hU))
  have hUright : U₃ ≤ U :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hU))
  have hw : ∀ J : Ideal (𝓞 K),
      ‖idealCoefficientHom (deletePrimes K E (primeCoefficient K χ)) J‖ ≤ 1 := by
    intro J
    exact norm_idealCoefficient_le_one _
      (norm_deletePrimes_le_one K E _ (norm_primeCoefficient_le_one K χ)) J
  obtain ⟨j, hj, k, hk, hsupport, ξ, hξ, hproduct⟩ :=
    hsource U hUleft (idealCoefficientHom (deletePrimes K E (primeCoefficient K χ)))
      hw hVnorm D hD s (by linarith) hterminal
  let r := Expansion.Dyadic.dyadicLength U j
  let m := Expansion.Dyadic.dyadicLength U k
  let ν := 2 * Real.pi * ξ - s.im
  let M := inverseDetectorValue K χ E V D U j s.re ν
  let S := plainDetectorValue K χ E U k s.re ν
  have hr : 0 ≤ r := Expansion.Dyadic.dyadicLength_nonneg hUgt j
  have hm : 0 ≤ m := Expansion.Dyadic.dyadicLength_nonneg hUgt k
  have hr22 : r ≤ 22 := Expansion.Dyadic.terminal_dyadicLength_le hU6 hj
  have hm22 : m ≤ 22 := Expansion.Dyadic.terminal_dyadicLength_le hU6 hk
  have hUr : U ^ r = (2 : ℝ) ^ j := Expansion.Dyadic.rpow_dyadicLength hUgt j
  have hUm : U ^ m = (2 : ℝ) ^ k := Expansion.Dyadic.rpow_dyadicLength hUgt k
  have hnormξ : |ξ| ≤ U ^ τ / (8 * Real.pi + 8) := by simpa only [Real.norm_eq_abs] using hξ
  have hν : |ν| + H + 3 / 2 ≤ Hupper := by
    have ht : |2 * Real.pi * ξ - s.im| ≤ 2 * Real.pi * |ξ| + |s.im| := by
      calc
        _ ≤ |2 * Real.pi * ξ| + |s.im| := abs_sub _ _
        _ = _ := by rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    have hf := mul_le_mul_of_nonneg_left hnormξ (by positivity : 0 ≤ 2 * Real.pi)
    dsimp only [ν]
    linarith
  have hHterminal : 1 ≤ U ^ (21 : ℕ) := one_le_pow₀ hUgt.le
  have hSj : ∀ J : NonzeroIdeal K,
      idealNorm K J ≤ dyadicMellinProfile.upper * U ^ r →
        J ∈ finiteIdealNormWindow K (2 * (6 * U ^ (21 : ℕ))) := by
    intro J hJ
    rw [hUr] at hJ
    exact terminal_normWindow_contains_annular K hHterminal hj J hJ
  have hSk : ∀ J : NonzeroIdeal K,
      idealNorm K J ≤ dyadicMellinProfile.upper * U ^ m →
        J ∈ finiteIdealNormWindow K (2 * (6 * U ^ (21 : ℕ))) := by
    intro J hJ
    rw [hUm] at hJ
    exact terminal_normWindow_contains_annular K hHterminal hk J hJ
  have hM := (hupper χ I E U a H Hupper r s.re ν (U ^ r / D)
    hχ harch hweight hI hE hUmid (by linarith) (by linarith) hr hr22 (by positivity)
    (by linarith) hβ' hnorm hconductor hheight hHlower hν hzeroUpper
    (finiteIdealNormWindow K (2 * (6 * U ^ (21 : ℕ)))) hSj).1
  have hS := (hupper χ I E U a H Hupper m s.re ν 0
    hχ harch hweight hI hE hUmid (by linarith) (by linarith) hm hm22 (by norm_num)
    (by linarith) hβ' hnorm hconductor hheight hHlower hν hzeroUpper
    (finiteIdealNormWindow K (2 * (6 * U ^ (21 : ℕ)))) hSk).2
  rw [hUr, ← actual_inverse_normalized_eq_mellin K χ E V hV
    (6 * U ^ (21 : ℕ)) D ((2 : ℝ) ^ j) s.re ν hD (by positivity)] at hM
  rw [hUm, ← actual_plain_normalized_eq_mellin K χ E
    (6 * U ^ (21 : ℕ)) ((2 : ℝ) ^ k) s.re ν] at hS
  change ‖M‖ ^ 2 ≤ U ^ ((2 * a - 1) * r + η) at hM
  change ‖S‖ ^ 2 ≤ U ^ ((2 * a - 1) * min m (1 - m) + η) at hS
  have hp : U ^ ((2 * a - 1) * (r + m) - η) ≤ ‖M * S‖ ^ 2 := by
    apply hspike U hUright r m a s.re ‖M * S‖ hr hm hβ (norm_nonneg _)
    simpa only [hUr, hUm, pow_two, M, S, inverseDetectorValue, plainDetectorValue, ν]
      using hproduct
  have hlength := Expansion.Dyadic.source_length_le_dyadic_sum hUgt hD hsupport.2.1
  obtain ⟨hMl, hSl, hshort, hlong⟩ := detector_saturation_with_length
    hUgt (by linarith : (1 / 50 : ℝ) ≤ 2 * a - 1) hη.le hp hM hS hlength
  exact ⟨j, hj, k, hk, ξ, hξ, hsupport, hp, hM, hS, hMl, hSl, hshort, hlong⟩

end Expansion.ActualTerminalSaturation
