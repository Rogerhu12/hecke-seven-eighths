import HeckeSkeleton.HighBinSupport.HighNormFormLogDerivative
import HeckeSkeleton.HeckePhysicalFamilyBufferedControl
import HeckeGeneral.Analysis.IdealDerivativeEulerLog
import ActualCanonicalRowConsumers
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Tactic.Positivity
/-!
Actual logarithmic-derivative control in the buffered row rectangle.

The estimate is derived from the existing bounds for the genuine Hecke
continuation and its reciprocal, using a complete Cauchy disc. Entirety
comes from exclusion of norm characters. The high-row theorem removes
that exclusion premise by the existing finite-fiber argument.

The continuation agrees with the genuine prime-power logarithmic series
on Re(s)>1. This does not yet perform the annular Mellin contour shift or
remove the higher prime powers required by NF-PRIME-DETECTOR.

This is a project-dependent candidate, excluded from the Mathlib aggregate.
-/

noncomputable section
namespace HighBinVerified.ActualRowLogDerivative

open NumberField IsDedekindDomain Filter
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.ExplicitHeckeFunctionalEquation
open HeckeSkeleton.HeckeBufferedReciprocal
open HeckeSkeleton.HeckePhysicalFamilyBufferedControl
open scoped Classical Topology

variable (K : Type) [Field K] [NumberField K]

def continuedLogDerivative (χ : HeckeCharacter K) (s : ℂ) : ℂ :=
  deriv (heckeContinuation K χ) s / heckeContinuation K χ s

theorem continuedLogDerivative_eq_primePowerSeries (χ : HeckeCharacter K)
    {s : ℂ} (hs : 1 < s.re) :
    continuedLogDerivative K χ s = -primePowerLogSeries K (primeCoefficient K χ) 1 s := by
  have heq : heckeContinuation K χ =ᶠ[𝓝 s] heckeLSeries K χ := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs]
      with z hz
    exact heckeContinuation_eq_series K χ hz
  unfold continuedLogDerivative
  rw [heq.deriv_eq, heckeContinuation_eq_series K χ hs]
  exact heckeLogDerivative_eq_primePowerSeries K χ hs

/-- Holomorphy throughout the actual retained zero-free rectangle, with
the possible norm-character poles explicitly excluded. -/
theorem continuedLogDerivative_analyticAt_of_upper (χ : HeckeCharacter K)
    (hnon : ∀ t : ℝ, χ ≠ heckeNormTwist K t)
    (H alpha : ℝ) (halpha : 1 / 2 ≤ alpha)
    (hupper : ZeroUpperBound K χ H alpha)
    (s : ℂ) (hs : alpha < s.re) (hheight : |s.im| ≤ H) :
    AnalyticAt ℂ (continuedLogDerivative K χ) s := by
  have ha := (differentiable_heckeContinuation_of_nonNorm K χ hnon).analyticAt s
  exact ha.deriv.div ha
    (continuation_ne_zero_of_upper K χ hnon H alpha halpha hupper s hs hheight)

variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- No L'/L bound is assumed: the input exponent is halved in the separate
L and 1/L bounds, and the Cauchy estimate returns the stated exponent. -/
theorem exists_uniform_physicalFamily_logDerivative_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (psi : HeckeCharacter K) (companions : Finset (HeckeCharacter K))
    (P : ProbeData K S) (E : RowEulerData K S P)
    {e eps : ℝ} (he : 0 < e) (he' : e < 1 / 1000) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : FrequencyRow K S) (a H Hupper : ℝ),
      (∀ eta ∈ physicalRowFamily K S psi companions P E u,
        ∀ t : ℝ, eta ≠ heckeNormTwist K t) →
      1 / 2 ≤ a → a ≤ 1 → 0 ≤ H → H + 2 ≤ Hupper →
      rowZeroBelow K S psi companions P E u Hupper (a + 2 * e) →
      ∀ eta ∈ physicalRowFamily K S psi companions P E u,
      ∀ s : ℂ, a + 8 * e ≤ s.re → s.re ≤ 3 / 2 → |s.im| ≤ H →
        ‖continuedLogDerivative K eta s‖ ≤
          C * heckeConductorScale K eta ^ eps *
            (2 + Hupper) ^ (((2 * Fintype.card (InfinitePlace K) : ℕ) : ℝ) * eps) := by
  obtain ⟨D, hD, hbuffer⟩ := exists_uniform_physicalFamily_buffered_control
    K S hcomplex psi companions P E he he' (show 0 < eps / 2 by linarith)
  refine ⟨D ^ 2 / e, by positivity, ?_⟩
  intro u a H Hupper hnon ha ha' hH hpadding hbelow eta heta s hslo hshi hsi
  let k : ℝ := ((2 * Fintype.card (InfinitePlace K) : ℕ) : ℝ)
  let M : ℝ := D * heckeConductorScale K eta ^ (eps / 2) *
    (2 + Hupper) ^ (k * (eps / 2))
  have hq : 0 < heckeConductorScale K eta := by
    unfold heckeConductorScale
    exact mul_pos (Nat.cast_pos.mpr (Int.natAbs_pos.mpr (NumberField.discr_ne_zero K)))
      (Nat.cast_pos.mpr (Ideal.absNorm_pos_of_nonZeroDivisors (finiteConductor K eta)))
  have ht : 0 < 2 + Hupper := by linarith
  have hdisc : ∀ z ∈ Metric.closedBall s e,
      ‖heckeContinuation K eta z‖ + ‖(heckeContinuation K eta z)⁻¹‖ ≤ M := by
    intro z hz
    obtain ⟨hzlo, hzhi, hzi⟩ := NormForm.closedBall_inside_buffered_strip
      a H e s z he.le (by linarith) hslo hshi hsi hz
    exact hbuffer u a (H + e) Hupper hnon ha ha' (by linarith)
      (by linarith) hbelow eta heta z hzlo hzhi hzi
  have hbound := NormForm.logDerivative_norm_le_of_disc
    (heckeContinuation K eta) s e M he
      (differentiable_heckeContinuation_of_nonNorm K eta (hnon eta heta)).diffContOnCl
      hdisc
  change ‖deriv (heckeContinuation K eta) s / heckeContinuation K eta s‖ ≤ _
  apply hbound.trans_eq
  calc
    M ^ 2 / e = (D ^ 2 / e) *
        (heckeConductorScale K eta ^ (eps / 2) * heckeConductorScale K eta ^ (eps / 2)) *
        ((2 + Hupper) ^ (k * (eps / 2)) * (2 + Hupper) ^ (k * (eps / 2))) := by
      dsimp only [M]
      ring
    _ = _ := by
      rw [← Real.rpow_add hq, ← Real.rpow_add ht,
        show eps / 2 + eps / 2 = eps by ring,
        show k * (eps / 2) + k * (eps / 2) = k * eps by ring]

/-- The fixed row cutoff precedes all moving contour and height variables.
Its finite-fiber argument is the existing actual background exclusion. -/
theorem exists_uniform_high_physicalFamily_logDerivative_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (psi : HeckeCharacter K) (companions : Finset (HeckeCharacter K))
    (P : ProbeData K S) (E : RowEulerData K S P)
    (hFib : ∀ chi : HeckeCharacter K, Finite {u : FrequencyRow K S // E.rows.character u = chi})
    (v : InfinitePlace K)
    {e eps : ℝ} (he : 0 < e) (he' : e < 1 / 1000) (heps : 0 < eps) :
    ∃ C Z0 : ℝ, 0 < C ∧ 1 ≤ Z0 ∧ ∀ Z : ℝ, Z0 ≤ Z →
      ∀ d : ℝ, (1 / 16 : ℝ) ≤ d → ∀ u : FrequencyRow K S,
      Z ^ d ≤ frequencyRowNorm K S u → ∀ a H Hupper : ℝ,
      1 / 2 ≤ a → a ≤ 1 → 0 ≤ H → H + 2 ≤ Hupper →
      rowZeroBelow K S psi companions P E u Hupper (a + 2 * e) →
      ∀ eta ∈ physicalRowFamily K S psi companions P E u,
      ∀ s : ℂ, a + 8 * e ≤ s.re → s.re ≤ 3 / 2 → |s.im| ≤ H →
        ‖continuedLogDerivative K eta s‖ ≤
          C * heckeConductorScale K eta ^ eps *
            (2 + Hupper) ^ (((2 * Fintype.card (InfinitePlace K) : ℕ) : ℝ) * eps) := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_physicalFamily_logDerivative_bound
    K S hcomplex psi companions P E he he' heps
  obtain ⟨Z0, hZ0, hnon⟩ :=
    HeckeSkeleton.HighNormBackgroundExclusion.high_rows_exclude_background_norm_twists
      K S P E.rows hFib v (physicalBackgrounds K psi companions)
  refine ⟨C, Z0, hC, hZ0, ?_⟩
  intro Z hZ d hd u hu a H Hupper ha ha' hH hpadding hbelow
  have hn := hnon Z hZ d hd u hu
  have hfamily : ∀ eta ∈ physicalRowFamily K S psi companions P E u,
      ∀ t : ℝ, eta ≠ heckeNormTwist K t := by
    intro eta heta
    obtain ⟨beta, hbeta, heq⟩ := physical_member_background_decomposition
      K S psi companions P E u eta heta
    rcases heq with heq | heq
    · rw [heq]
      exact (hn beta hbeta).1
    · rw [heq]
      exact (hn beta hbeta).2
  exact hbound u a H Hupper hfamily ha ha' hH hpadding hbelow

/-- Real-repository specialization: the original probe's primitive
twelfth root forces the field to be totally complex, and canonical row
uniqueness supplies every finite fiber. Neither fact is an extra premise. -/
theorem exists_uniform_actual_high_logDerivative_bound
    (psi : HeckeCharacter K) (companions : Finset (HeckeCharacter K))
    (P : ProbeData K S) (E : RowEulerData K S P)
    {e eps : ℝ} (he : 0 < e) (he' : e < 1 / 1000) (heps : 0 < eps) :
    ∃ C Z0 : ℝ, 0 < C ∧ 1 ≤ Z0 ∧ ∀ Z : ℝ, Z0 ≤ Z →
      ∀ d : ℝ, (1 / 16 : ℝ) ≤ d → ∀ u : FrequencyRow K S,
      Z ^ d ≤ frequencyRowNorm K S u → ∀ a H Hupper : ℝ,
      1 / 2 ≤ a → a ≤ 1 → 0 ≤ H → H + 2 ≤ Hupper →
      rowZeroBelow K S psi companions P E u Hupper (a + 2 * e) →
      ∀ eta ∈ physicalRowFamily K S psi companions P E u,
      ∀ s : ℂ, a + 8 * e ≤ s.re → s.re ≤ 3 / 2 → |s.im| ≤ H →
        ‖continuedLogDerivative K eta s‖ ≤
          C * heckeConductorScale K eta ^ eps *
            (2 + Hupper) ^ (((2 * Fintype.card (InfinitePlace K) : ℕ) : ℝ) * eps) := by
  exact exists_uniform_high_physicalFamily_logDerivative_bound K S
    (HeckeSkeleton.HeckeFiniteBackgroundControl.all_complex_of_primitive12 K P.arithmetic.primitive12)
    psi companions P E
    (HeckeSkeleton.ActualCanonicalRowConsumers.rowCharacter_fiber_finite K S P E)
    (Classical.choice inferInstance) he he' heps

end HighBinVerified.ActualRowLogDerivative

#print axioms HighBinVerified.ActualRowLogDerivative.continuedLogDerivative_eq_primePowerSeries
#print axioms HighBinVerified.ActualRowLogDerivative.continuedLogDerivative_analyticAt_of_upper
#print axioms HighBinVerified.ActualRowLogDerivative.exists_uniform_physicalFamily_logDerivative_bound
#print axioms HighBinVerified.ActualRowLogDerivative.exists_uniform_high_physicalFamily_logDerivative_bound
#print axioms HighBinVerified.ActualRowLogDerivative.exists_uniform_actual_high_logDerivative_bound
