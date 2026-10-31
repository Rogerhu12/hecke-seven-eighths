import Expansion.TerminalFourierTail
import HeckeSkeleton.ExpansionDetectorBridge
import HeckeSkeleton.ExpansionModels.OriginalMaskBounds

/-!
# Actual Hecke zeros and the original complete ideal mask

The same coefficient map is used by the ordinary deleted Hecke series,
the terminal detector, and both normalized Fourier polynomials. The fixed
exceptional primes, primes over six, and every complete-row prime remain
in this map. Its norm and deletion-cardinality estimates are proved from
the original arithmetic definitions.

The constants and scale threshold precede the character, row, cutoff
length, and zero. Ordinary fixed infinity type, non-pure-norm status, a
conductor bound, and the original zero are the analytic inputs. No source
lower bound, Dirichlet calibration, zeta summability, Fourier tail estimate,
or polynomial spike is assumed by the final theorem.
-/

set_option autoImplicit false
noncomputable section

namespace Expansion.Project

open NumberField IsDedekindDomain
open Filter
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Bridge
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ExpansionRecipe
open HeckeSkeleton.ExpansionDetectorBridge
open ExpansionDetector.IdealCutoff ExpansionDetector.Hecke
open ExpansionDetector.Fourier Expansion.Dyadic
open scoped Classical BigOperators ContDiff Topology

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- The physical detector records positive meromorphic order.  For the
entire non-norm branch this is a zero of the actual continuation, so no
totalized value at a pole is used as a detector zero. -/
theorem heckeContinuation_zero_of_order_pos (χ : HeckeCharacter K)
    (hχ : ∀ t : ℝ, χ ≠ heckeNormTwist K t) (ρ : ℂ)
    (hρ : 0 < meromorphicOrderAt (heckeContinuation K χ) ρ) :
    heckeContinuation K χ ρ = 0 := by
  have hd := differentiable_heckeContinuation_of_nonNorm K χ hχ
  have hzero : Tendsto (heckeContinuation K χ) (𝓝[≠] ρ) (𝓝 0) :=
    (tendsto_zero_iff_meromorphicOrderAt_pos ((hd.analyticAt ρ).meromorphicAt)).mpr hρ
  have hvalue : Tendsto (heckeContinuation K χ) (𝓝[≠] ρ)
      (𝓝 (heckeContinuation K χ ρ)) :=
    (hd.continuous.continuousAt : ContinuousAt (heckeContinuation K χ) ρ).tendsto.mono_left
      nhdsWithin_le_nhds
  exact tendsto_nhds_unique hvalue hzero

/-- The complete source mask, rather than only the conductor primes, is
passed through the zero detector and the bounded-frequency extraction. -/
theorem exists_original_masked_product
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (radial : InfinitePlace K → ℝ) (weight : InfinitePlace K → ℤ)
    (R θ τ : ℝ) (hR : 0 ≤ R) (hθ : 0 ≤ θ) (hτ : 0 < τ)
    (hbudget : heightDegree K * θ ≤ 1)
    (V : ℝ → ℂ) (hV : ContDiff ℝ ∞ V)
    (hone : ∀ x : ℝ, x ≤ 1 → V x = 1)
    (hzero : ∀ x : ℝ, 2 ≤ x → V x = 0)
    (hVnorm : ∀ x : ℝ, ‖V x‖ ≤ 1)
    (hVcomp : ∀ x : ℝ, 0 ≤ x → ‖1 - V x‖ ≤ 1) :
    ∃ C U₀ : ℝ, 0 < C ∧ 2 ≤ U₀ ∧
      ∀ (χ : HeckeCharacter K) (u : NonzeroIdeal K) (U D : ℝ),
      U₀ ≤ U →
      (∀ t : ℝ, χ ≠ heckeNormTwist K t) →
      (fun v => heckeRadialParameter K v χ) = radial →
      heckeArchWeight K χ = weight →
      heckeConductorScale K χ ≤ R * U → HeckeGeneral.Analysis.idealNorm K u ≤ 2 * U →
      2 ≤ D → D ≤ U ^ (3 / 2 : ℝ) →
      ∀ ρ : ℂ, heckeContinuation K χ ρ = 0 →
      51 / 100 ≤ ρ.re → ρ.re ≤ 1 → |ρ.im| ≤ U ^ θ →
      let n := dyadicCap (3 * U ^ (21 : ℕ))
      ∃ j ≤ n, ∃ k ≤ n,
        (((2 : ℝ) ^ j < 4 * D) ∧
          D / 8 < (2 : ℝ) ^ j * (2 : ℝ) ^ k ∧
          (2 : ℝ) ^ j * (2 : ℝ) ^ k < 8 * U ^ (21 : ℕ)) ∧
        ∃ t : ℝ,
        ‖t‖ ≤ U ^ τ / (8 * Real.pi + 8) ∧
        (1 / 8 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) * (n + 1 : ℕ) * C *
          ((2 : ℝ) ^ j) ^ (1 / 2 - ρ.re) *
          ((2 : ℝ) ^ k) ^ (1 / 2 - ρ.re) *
          ‖normalizedPolynomial (nonzeroTerminalSet (6 * U ^ (21 : ℕ)))
              (inverseRawCoefficient (originalMaskedCoefficientHom K S χ u) V D)
              Expansion.Dyadic.idealNorm annularProfile
              ((2 : ℝ) ^ j) ρ.re (2 * Real.pi * t - ρ.im) *
            normalizedPolynomial (nonzeroTerminalSet (6 * U ^ (21 : ℕ)))
              (originalMaskedCoefficientHom K S χ u)
              Expansion.Dyadic.idealNorm annularProfile
              ((2 : ℝ) ^ k) ρ.re (2 * Real.pi * t - ρ.im)‖ := by
  let CD : ℝ := 2 * (Ideal.absNorm (fixedDeletedIdeal K S) : ℝ)
  have hCD : 0 ≤ CD := by dsimp [CD]; positivity
  obtain ⟨U₁, hU₁, hsource⟩ := exists_actual_deleted_terminal_source
    K hcomplex radial weight R CD θ hR hCD hθ hbudget
  let CZ : ℝ := 1 + ∑' I : NonzeroIntegralIdeal (K := K),
    nonzeroIdealNorm I ^ (-2 : ℝ)
  have hCZ : 0 ≤ CZ := by dsimp [CZ]; positivity
  have hzeta : Summable (fun I : NonzeroIntegralIdeal (K := K) =>
      nonzeroIdealNorm I ^ (-2 : ℝ)) := by
    simpa only [nonzeroIdealNorm] using
      (summable_nonzeroIdeal_norm_rpow K (σ := 2) (by norm_num))
  have hCZsum : (∑' I : NonzeroIntegralIdeal (K := K),
      nonzeroIdealNorm I ^ (-2 : ℝ)) ≤ CZ := by
    dsimp [CZ]
    linarith
  obtain ⟨C, U₂, hC, hU₂, hproduct⟩ := actual_terminal_product_eventually
    (K := K) V hV hone hzero τ hτ CZ hCZ hzeta hCZsum
  refine ⟨C, max U₁ U₂, hC, hU₁.trans (le_max_left _ _), ?_⟩
  intro χ u U D hU hχ hradial hweight hQ hu hD hDU ρ hρ hβ hβone hγ
  have hUleft : U₁ ≤ U := (le_max_left _ _).trans hU
  have hUright : U₂ ≤ U := (le_max_right _ _).trans hU
  have hdeletion : (2 : ℝ) ^ (originalDeletedPrimes K S u).card ≤ CD * U :=
    originalDeletion_card_bound_of_norm_le K S u hu
  have hs := hsource χ (originalDeletedPrimes K S u) U D hUleft
    hχ hradial hweight hQ hdeletion hD hDU V V hVnorm hVcomp hVcomp
    (fun x _ hx => hone x hx) (fun x _ hx => hone x hx)
    hzero hzero ρ hρ hβ hβone hγ
  exact hproduct U hUright (originalMaskedCoefficientHom K S χ u)
    (originalMaskedCoefficientHom_norm_le K S χ u) hVnorm D (by linarith)
    ρ (by linarith) hs

end Expansion.Project
