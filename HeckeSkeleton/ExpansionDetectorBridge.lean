import ExpansionDetector.HeckeGammaDetector
import HeckeGeneral.Analysis.ExpansionDetectorInitial

/-!
# Actual Hecke zeros give the finite expansion source

This specializes the verified ideal detector to the existing Hecke
continuation with literal finite Euler deletion. The only deletion-size
premise is the elementary finite-set bound `2^card(E) ≤ CD * U`; for the
original fixed-S/6/row mask it follows from `2^omega(u) ≤ N(u)`.

No Mellin identity, source lower bound, detector spike or saturated witness
is an input. The non-pure-norm condition is explicit, since the ordinary
continuation must be entire for the zero contour shift.
-/

noncomputable section
namespace HeckeSkeleton.ExpansionDetectorBridge
open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Bridge HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ExpansionDetectorInitial
open HeckeSkeleton.ExplicitHeckeFunctionalEquation
open ExpansionDetector.IdealCutoff ExpansionDetector.Hecke
open scoped NumberField Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]

theorem exists_actual_deleted_terminal_source
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (τ : InfinitePlace K → ℝ) (m : InfinitePlace K → ℤ)
    (R CD θ : ℝ) (hR : 0 ≤ R) (hCD : 0 ≤ CD) (hθ : 0 ≤ θ)
    (hbudget : heightDegree K * θ ≤ 1) :
    ∃ U₀ : ℝ, 2 ≤ U₀ ∧ ∀ (χ : HeckeCharacter K)
      (E : Finset (HeightOneSpectrum (𝓞 K))) (U D : ℝ), U₀ ≤ U →
      (∀ t : ℝ, χ ≠ heckeNormTwist K t) →
      (fun v => heckeRadialParameter K v χ) = τ → heckeArchWeight K χ = m →
      heckeConductorScale K χ ≤ R * U → (2 : ℝ) ^ E.card ≤ CD * U →
      2 ≤ D → D ≤ U ^ (3 / 2 : ℝ) → ∀ V T : ℝ → ℂ,
      (∀ x : ℝ, ‖V x‖ ≤ 1) →
      (∀ x : ℝ, 0 ≤ x → ‖1 - V x‖ ≤ 1) →
      (∀ x : ℝ, 0 ≤ x → ‖1 - T x‖ ≤ 1) →
      (∀ x : ℝ, 0 ≤ x → x ≤ 1 → V x = 1) →
      (∀ x : ℝ, 0 ≤ x → x ≤ 1 → T x = 1) →
      (∀ x : ℝ, 2 ≤ x → V x = 0) →
      (∀ x : ℝ, 2 ≤ x → T x = 0) → ∀ ρ : ℂ,
      heckeContinuation K χ ρ = 0 → 51 / 100 ≤ ρ.re → ρ.re ≤ 1 → |ρ.im| ≤ U ^ θ →
      (1 / 4 : ℝ) ≤ ‖∑ I ∈ terminalIdealSet (U ^ 21),
        terminalTerm (deletedCoefficientHom K χ E) V T D (U ^ 21)
          (fun n => (n : ℂ) ^ (-ρ) * (Real.exp (-(n : ℝ) / U ^ 20) : ℂ)) I‖ := by
  obtain ⟨CL, hCL, hstrip⟩ := exists_actual_detector_strip_bound K hcomplex τ m R hR
  let CZ : ℝ := 1 + ∑' I : NonzeroIntegralIdeal (K := K), nonzeroIdealNorm I ^ (-2 : ℝ)
  have hZnonneg : 0 ≤ ∑' I : NonzeroIntegralIdeal (K := K),
      nonzeroIdealNorm I ^ (-2 : ℝ) := by
    apply tsum_nonneg
    intro I
    apply Real.rpow_nonneg
    change (0 : ℝ) ≤ (Ideal.absNorm I.val : ℝ)
    exact Nat.cast_nonneg _
  have hCZ : 0 < CZ := by dsimp [CZ]; linarith
  have hA : 0 ≤ heightDegree K := by dsimp [heightDegree]; positivity
  have hzeta₃ : Summable (fun I : NonzeroIntegralIdeal (K := K) => nonzeroIdealNorm I ^ (-3 / 2 : ℝ)) := by
    convert (summable_nonzeroIdeal_norm_rpow K (σ := 3 / 2) (by norm_num)) using 1 <;>
      norm_num [nonzeroIdealNorm, idealNorm]
  have hzeta₂ : Summable (fun I : NonzeroIntegralIdeal (K := K) => nonzeroIdealNorm I ^ (-2 : ℝ)) := by
    simpa only [nonzeroIdealNorm, idealNorm] using
      (summable_nonzeroIdeal_norm_rpow K (σ := 2) (by norm_num))
  have hCZsum : (∑' I : NonzeroIntegralIdeal (K := K), nonzeroIdealNorm I ^ (-2 : ℝ)) ≤ CZ := by
    dsimp [CZ]
    linarith
  obtain ⟨U₀, hU₀, hsource⟩ := actualIdeal_terminal_lower_of_zero (K := K)
    (heightDegree K) θ (13 / 8) (CD * CL) CZ hA hθ (by norm_num)
    (mul_nonneg hCD hCL.le) hCZ.le hbudget hzeta₃ hzeta₂ hCZsum
  refine ⟨U₀, hU₀, ?_⟩
  intro χ E U D hU hχ hτ hm hQ hE hD hDU V T hV hVc hTc hVsmall hTsmall hVzero hTzero ρ hz hβ hβ1 hγ
  have hUtwo : 2 ≤ U := hU₀.trans hU
  have hUone : 1 ≤ U := by linarith
  have hUp : 0 < U := by linarith
  apply hsource U hU (deletedCoefficientHom K χ E) V T D
    (heckeDeletedContinuation K χ E) ρ
    (deletedCoefficientHom_norm_le K χ E) hV hVc hTc hVsmall hTsmall hVzero hTzero hD hDU
    (heckeDeletedContinuation_entire K χ hχ E)
    (fun s hs => heckeDeletedContinuation_eq_allIdeal_series K χ E hs)
    (fun s hs => deletedCoefficient_initial_absolutelySummable K χ E hs)
    _ (heckeDeletedContinuation_zero K χ E hz) hβ hβ1 hγ
  intro s hs hs'
  have hL := hstrip χ U hχ hτ hm hUone hQ s hs hs'
  have hdel := (heckeEulerDeletionPolynomial_norm_le_card K χ E s (by linarith)).trans hE
  have hp : U * U ^ (5 / 8 : ℝ) = U ^ (13 / 8 : ℝ) := by
    conv_lhs => lhs; rw [← Real.rpow_one U]
    rw [← Real.rpow_add hUp]
    norm_num
  rw [heckeDeletedContinuation, norm_mul]
  calc
    _ ≤ (CD * U) * (CL * U ^ (5 / 8 : ℝ) * (2 + |s.im|) ^ heightDegree K) :=
      mul_le_mul hdel hL (norm_nonneg _) (mul_nonneg hCD hUp.le)
    _ = (CD * CL) * (U * U ^ (5 / 8 : ℝ)) * (2 + |s.im|) ^ heightDegree K := by ring
    _ = _ := by rw [hp]

end HeckeSkeleton.ExpansionDetectorBridge
