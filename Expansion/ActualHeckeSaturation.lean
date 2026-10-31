import Expansion.ActualHeckeWitness
import Expansion.ActualTerminalSaturation

/-!
# Original Hecke zero to simultaneous saturated witnesses

This combines the ordinary Hecke zero detector, its literal complete-row
mask, the computed Fourier tail, and the actual finite Mellin bounds.
There is no terminal-source premise and no polynomial-bound premise.
The zero-height exponent and the Fourier-radius exponent are independent:
the latter must fit the physical buffer even after multiplying by `2*pi`.
-/

set_option autoImplicit false
noncomputable section
namespace Expansion.Project

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Bridge
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ExpansionRecipe
open HeckeSkeleton.ExpansionDetectorBridge HeckeSkeleton.HeckeBufferedReciprocal
open ExpansionDetector.IdealCutoff ExpansionDetector.Hecke
open Expansion.ActualTerminalSaturation
open scoped Classical BigOperators ContDiff

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- A positive-order ordinary Hecke zero produces the actual inverse and
plain witnesses at one bounded Fourier frequency. The scale threshold is
chosen before the character, complete ideal row, zero and buffered bin. -/
theorem exists_original_masked_saturation
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (arch : InfinitePlace K → ℝ) (weight : InfinitePlace K → ℤ)
    {e ε : ℝ} (he : 0 < e) (he' : e < 1 / 1000) (hε : 0 < ε)
    (V : ℝ → ℂ) (hV : ContDiff ℝ ∞ V)
    (hone : ∀ x : ℝ, x ≤ 1 → V x = 1)
    (hzero : ∀ x : ℝ, 2 ≤ x → V x = 0)
    (hVnorm : ∀ x : ℝ, ‖V x‖ ≤ 1)
    (hVcomp : ∀ x : ℝ, 0 ≤ x → ‖1 - V x‖ ≤ 1)
    (R θzero θ τ η : ℝ) (hR : 1 ≤ R)
    (hθzero : 0 ≤ θzero) (hθ : 0 ≤ θ) (hτ : 0 < τ) (hη : 0 < η)
    (hzeroBudget : heightDegree K * θzero ≤ 1)
    (hforward : 132 * e + 2 * ε + heightDegree K * ε * θ ≤ η / 4)
    (hreflected : 12 * e + 2 * ε + heightDegree K * θ * (1 + ε) ≤ η / 4) :
    ∃ U₀ : ℝ, 6 ≤ U₀ ∧ ∀ (χ : HeckeCharacter K) (u : NonzeroIdeal K)
      (U a H Hupper D : ℝ) (ρ : ℂ),
      (∀ t : ℝ, χ ≠ heckeNormTwist K t) →
      (fun v => heckeRadialParameter K v χ) = arch → heckeArchWeight K χ = weight →
      U₀ ≤ U → HeckeGeneral.Analysis.idealNorm K u ≤ 2 * U →
      heckeConductorScale K χ ≤ R * U → 2 ≤ D → D ≤ U ^ (3 / 2 : ℝ) →
      51 / 100 ≤ a → a ≤ ρ.re → ρ.re ≤ 1 →
      0 < meromorphicOrderAt (heckeContinuation K χ) ρ → |ρ.im| ≤ U ^ θzero →
      2 + Hupper ≤ R * U ^ θ → U ^ τ ≤ H →
      |ρ.im| + 2 * Real.pi * (U ^ τ / (8 * Real.pi + 8)) + H + 3 / 2 ≤ Hupper →
      ZeroUpperBound K χ Hupper (a + 2 * e) →
      let n := Expansion.Dyadic.dyadicCap (3 * U ^ (21 : ℕ))
      ∃ j ≤ n, ∃ k ≤ n, ∃ ξ : ℝ,
        ‖ξ‖ ≤ U ^ τ / (8 * Real.pi + 8) ∧
        ((2 : ℝ) ^ j < 4 * D ∧ D / 8 < (2 : ℝ) ^ j * (2 : ℝ) ^ k ∧
          (2 : ℝ) ^ j * (2 : ℝ) ^ k < 8 * U ^ (21 : ℕ)) ∧
        let r := Expansion.Dyadic.dyadicLength U j
        let m := Expansion.Dyadic.dyadicLength U k
        let ν := 2 * Real.pi * ξ - ρ.im
        let M := inverseDetectorValue K χ (originalDeletedPrimes K S u) V D U j ρ.re ν
        let P := plainDetectorValue K χ (originalDeletedPrimes K S u) U k ρ.re ν
        U ^ ((2 * a - 1) * (r + m) - η) ≤ ‖M * P‖ ^ 2 ∧
        ‖M‖ ^ 2 ≤ U ^ ((2 * a - 1) * r + η) ∧
        ‖P‖ ^ 2 ≤ U ^ ((2 * a - 1) * min m (1 - m) + η) ∧
        U ^ ((2 * a - 1) * r - 2 * η) ≤ ‖M‖ ^ 2 ∧
        U ^ ((2 * a - 1) * m - 2 * η) ≤ ‖P‖ ^ 2 ∧
        m ≤ 1 / 2 + 75 * η ∧
        Real.log D / Real.log U - 1 / 2 - 75 * η - Real.log 8 / Real.log U ≤ r := by
  let CD : ℝ := 2 * (Ideal.absNorm (fixedDeletedIdeal K S) : ℝ)
  let R' : ℝ := max R CD
  have hCD : 0 ≤ CD := by dsimp [CD]; positivity
  have hRzero : 0 ≤ R := zero_le_one.trans hR
  have hR' : 1 ≤ R' := hR.trans (le_max_left _ _)
  obtain ⟨U₁, hU₁, hsource⟩ := exists_actual_deleted_terminal_source
    K hcomplex arch weight R CD θzero hRzero hCD hθzero hzeroBudget
  let CZ : ℝ := 1 + ∑' I : NonzeroIntegralIdeal (K := K),
    nonzeroIdealNorm I ^ (-2 : ℝ)
  have hCZ : 0 ≤ CZ := by dsimp [CZ]; positivity
  have hzeta : Summable (fun I : NonzeroIntegralIdeal (K := K) =>
      nonzeroIdealNorm I ^ (-2 : ℝ)) := by
    simpa only [nonzeroIdealNorm] using
      (summable_nonzeroIdeal_norm_rpow K (σ := 2) (by norm_num))
  have hCZsum : (∑' I : NonzeroIntegralIdeal (K := K),
      nonzeroIdealNorm I ^ (-2 : ℝ)) ≤ CZ := by dsimp [CZ]; linarith
  obtain ⟨U₂, hU₂, hsaturation⟩ := exists_actual_terminal_saturation K
    hcomplex arch weight he he' hε V hV hone hzero hVnorm R' θ τ η
    hR' hθ hτ hη hforward hreflected CZ hCZ hzeta hCZsum
  refine ⟨max U₁ U₂, hU₂.trans (le_max_right _ _), ?_⟩
  intro χ u U a H Hupper D ρ hχ harch hweight hU hu hQ hD hDU ha hβ hβ'
    hρ hγ hheight hH hpadding hupper
  have hUleft : U₁ ≤ U := (le_max_left _ _).trans hU
  have hUright : U₂ ≤ U := (le_max_right _ _).trans hU
  have hUpos : 0 < U := by linarith [hU₂.trans hUright]
  have hdeletion : (2 : ℝ) ^ (originalDeletedPrimes K S u).card ≤ CD * U :=
    originalDeletion_card_bound_of_norm_le K S u hu
  have hvalue : heckeContinuation K χ ρ = 0 :=
    heckeContinuation_zero_of_order_pos K χ hχ ρ hρ
  have hterminal := hsource χ (originalDeletedPrimes K S u) U D hUleft
    hχ harch hweight hQ hdeletion hD hDU V V hVnorm hVcomp hVcomp
    (fun x _ hx => hone x hx) (fun x _ hx => hone x hx)
    hzero hzero ρ hvalue (ha.trans hβ) hβ' hγ
  have hnorm : (Ideal.absNorm (originalDeletionEnvelope K S u) : ℝ) ≤ R' * U := by
    rw [originalDeletionEnvelope_norm]
    calc
      _ ≤ (Ideal.absNorm (fixedDeletedIdeal K S) : ℝ) * (2 * U) :=
        mul_le_mul_of_nonneg_left hu (Nat.cast_nonneg _)
      _ = CD * U := by dsimp [CD]; ring
      _ ≤ R' * U := mul_le_mul_of_nonneg_right (le_max_right _ _) hUpos.le
  exact hsaturation χ (originalDeletionEnvelope K S u) (originalDeletedPrimes K S u)
    U a H Hupper D ρ hχ harch hweight (originalDeletionEnvelope_ne_zero K S u)
    (originalDeletedPrimes_dvd_envelope K S u) hUright ha hβ hβ' (by linarith)
    hnorm (hQ.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hUpos.le))
    (hheight.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg hUpos.le θ))) hH hpadding hupper hterminal

end Expansion.Project

#print axioms Expansion.Project.heckeContinuation_zero_of_order_pos
#print axioms Expansion.Project.exists_original_masked_saturation
