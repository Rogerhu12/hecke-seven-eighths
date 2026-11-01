import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalFullKappaPrime
import HeckeGeneral.Analysis.IdealDerivativeEulerLog
import HeckeGeneral.Analysis.HeckeContinuation

/-!
# Actual Hecke data for the full-kappa prime adapter

Only the original zero-free analytic certificate is an input. The prime
count, coefficient bound, absolute prime-power convergence and Euler
identity are proved from the actual number-field ideal series. Thus the
capacity adapter does not ask a caller to rebuild these proved facts or
to supply any prime-polynomial estimate.
-/

noncomputable section
open scoped Classical BigOperators NumberField Topology SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep

namespace CanonicalHeckePrimeAnalytic

open NumberField IsDedekindDomain Filter
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.Analysis.SquarefreeAmplification
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open PrimeCancellation PrimeCancellation.Analytic PrimeCancellation.Paired

variable {K : Type} [Field K] [NumberField K]

/-- The original prime-count coefficient is fixed by the number field. -/
def degreeBound (K : Type) [Field K] [NumberField K] : ℝ :=
  Classical.choose (dyadicIdealSupport_linear_count K)

theorem degreeBound_pos : 0 < degreeBound K :=
  (Classical.choose_spec (dyadicIdealSupport_linear_count K)).1

/-- The actual prime arithmetic, including the finite-pool count, is
internal to the constructor. -/
def arithmetic (χ : HeckeCharacter K) :
    PrimeCancellationPrimeSeries.PrimeArithmetic
      (fun p : HeightOneSpectrum (𝓞 K) => (Ideal.absNorm p.asIdeal : ℝ))
      (primeCoefficient K χ) (degreeBound K) where
  d_nonneg := degreeBound_pos.le
  norm_ge_two p := by exact_mod_cast one_lt_primeIdeal_absNorm K p
  coeff_bound := norm_primeCoefficient_le_one K χ
  count pool Y hY := by
    by_cases hlarge : 1 ≤ Y
    · let f := pool.filter (fun p => (Ideal.absNorm p.asIdeal : ℝ) ≤ Y)
      have hsub : f.image (primeNonzeroIdeal K) ⊆ dyadicIdealSupport K (Y / 2) := by
        intro I hI
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hI
        apply (mem_dyadicIdealSupport_iff K (by positivity) (primeNonzeroIdeal K p)).mpr
        simpa only [idealNorm, primeNonzeroIdeal, show 2 * (Y / 2) = Y by ring]
          using (Finset.mem_filter.mp hp).2
      have hcard : f.card ≤ (dyadicIdealSupport K (Y / 2)).card := by
        rw [← Finset.card_image_of_injective f (primeNonzeroIdeal_injective K)]
        exact Finset.card_le_card hsub
      exact (Nat.cast_le.mpr hcard).trans
        ((Classical.choose_spec (dyadicIdealSupport_linear_count K)).2 Y hlarge)
    · have hempty : pool.filter (fun p => (Ideal.absNorm p.asIdeal : ℝ) ≤ Y) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro p hp
        have hpY := (Finset.mem_filter.mp hp).2
        have hp2 : (2 : ℝ) ≤ Ideal.absNorm p.asIdeal := by
          exact_mod_cast one_lt_primeIdeal_absNorm K p
        linarith
      rw [hempty, Finset.card_empty, Nat.cast_zero]
      exact mul_nonneg degreeBound_pos.le hY

/-- The independent analytic sum uses `(exponent, prime)`; the actual
ideal series uses `(prime, exponent)`. This is the literal term identity. -/
theorem primePowerTerm_eq (χ : HeckeCharacter K) (s : ℂ)
    (np : ℕ × HeightOneSpectrum (𝓞 K)) :
    primePowerCoefficient
        (fun p : HeightOneSpectrum (𝓞 K) => (Ideal.absNorm p.asIdeal : ℝ))
        (primeCoefficient K χ) np *
      (primePowerNorm
        (fun p : HeightOneSpectrum (𝓞 K) => (Ideal.absNorm p.asIdeal : ℝ)) np : ℂ) ^ (-s) =
      primePowerLogTerm K (primeCoefficient K χ) 1 s (np.2, np.1) := by
  simp only [primePowerCoefficient, primePowerNorm, primePowerLogTerm, pow_one,
    primeIdealRatio, Complex.ofReal_pow, Complex.ofReal_natCast]
  rw [← Complex.natCast_cpow_natCast_mul, Complex.cpow_nat_mul, mul_pow]
  ring

theorem primePowerNorm_pos (np : ℕ × HeightOneSpectrum (𝓞 K)) :
    0 < primePowerNorm
      (fun p : HeightOneSpectrum (𝓞 K) => (Ideal.absNorm p.asIdeal : ℝ)) np := by
  apply pow_pos
  exact_mod_cast lt_trans Nat.zero_lt_one (one_lt_primeIdeal_absNorm K np.2)

/-- At the actual absolute-convergence line, the analytic majorant is
the norm of the same ideal prime-power term. -/
theorem primePowerMajorant_eq (χ : HeckeCharacter K)
    (np : ℕ × HeightOneSpectrum (𝓞 K)) :
    ‖primePowerCoefficient
      (fun p : HeightOneSpectrum (𝓞 K) => (Ideal.absNorm p.asIdeal : ℝ))
      (primeCoefficient K χ) np‖ *
      (primePowerNorm
        (fun p : HeightOneSpectrum (𝓞 K) => (Ideal.absNorm p.asIdeal : ℝ)) np) ^ (-(2 : ℝ)) =
      ‖primePowerLogTerm K (primeCoefficient K χ) 1 (2 : ℂ) (np.2, np.1)‖ := by
  rw [← primePowerTerm_eq χ (2 : ℂ) np, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos (primePowerNorm_pos np)]
  norm_num

theorem absolutelySummable (χ : HeckeCharacter K) :
    Summable (fun np : ℕ × HeightOneSpectrum (𝓞 K) =>
      ‖primePowerCoefficient
        (fun p : HeightOneSpectrum (𝓞 K) => (Ideal.absNorm p.asIdeal : ℝ))
        (primeCoefficient K χ) np‖ *
      (primePowerNorm
        (fun p : HeightOneSpectrum (𝓞 K) => (Ideal.absNorm p.asIdeal : ℝ)) np) ^ (-(2 : ℝ))) := by
  have hs := (absolutelySummable_primePowerLogTerm K (primeCoefficient K χ)
    (norm_primeCoefficient_le_one K χ) 1 (s := (2 : ℂ)) (by norm_num)).comp_injective
      (Equiv.prodComm ℕ (HeightOneSpectrum (𝓞 K))).injective
  change Summable (fun np : ℕ × HeightOneSpectrum (𝓞 K) =>
    ‖primePowerLogTerm K (primeCoefficient K χ) 1 (2 : ℂ) (np.2, np.1)‖) at hs
  simpa only [← primePowerMajorant_eq χ] using hs

/-- The Euler identity is derived for the actual continuation using
its proved equality with the actual series on the convergence half-plane. -/
theorem euler (χ : HeckeCharacter K) (s : ℂ) (hs : 1 < s.re) :
    (∑' np : ℕ × HeightOneSpectrum (𝓞 K),
      primePowerCoefficient
        (fun p : HeightOneSpectrum (𝓞 K) => (Ideal.absNorm p.asIdeal : ℝ))
        (primeCoefficient K χ) np *
      (primePowerNorm
        (fun p : HeightOneSpectrum (𝓞 K) => (Ideal.absNorm p.asIdeal : ℝ)) np : ℂ) ^ (-s)) =
      -deriv (heckeContinuation K χ) s / heckeContinuation K χ s := by
  have heq : heckeContinuation K χ =ᶠ[𝓝 s] heckeLSeries K χ := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs]
      with z hz
    exact heckeContinuation_eq_series K χ hz
  have hlog := heckeLogDerivative_eq_primePowerSeries K χ hs
  rw [heckeLogDerivative] at hlog
  calc
    _ = primePowerLogSeries K (primeCoefficient K χ) 1 s := by
      simp_rw [primePowerTerm_eq χ s]
      exact (Equiv.prodComm ℕ (HeightOneSpectrum (𝓞 K))).tsum_eq
        (primePowerLogTerm K (primeCoefficient K χ) 1 s)
    _ = -(deriv (heckeLSeries K χ) s / heckeLSeries K χ s) := by
      simpa only [neg_neg] using (congrArg Neg.neg hlog).symm
    _ = _ := by
      rw [heq.deriv_eq, heckeContinuation_eq_series K χ hs, neg_div]

end CanonicalHeckePrimeAnalytic

namespace OriginalPrimeAnalyticData

open HeckeGeneral.Characters HeckeGeneral.Analysis PrimeCancellation.Analytic

variable {K : Type} [Field K] [NumberField K]

/-- Only the original zero-free analytic certificate remains a primitive
single-character input. All Euler and elementary arithmetic fields are
constructed from the proved actual Hecke series. -/
def ofHecke (χ : HeckeCharacter K) (β : ℝ)
    (analytic : ZeroFreeData (heckeContinuation K χ) β) :
    OriginalPrimeAnalyticData χ β (CanonicalHeckePrimeAnalytic.degreeBound K) where
  slot := {
    norm := fun p => (Ideal.absNorm p.asIdeal : ℝ)
    coefficient := primeCoefficient K χ
    function := heckeContinuation K χ
    arithmetic := CanonicalHeckePrimeAnalytic.arithmetic χ
    analytic := analytic
    absolute := CanonicalHeckePrimeAnalytic.absolutelySummable χ
    euler := CanonicalHeckePrimeAnalytic.euler χ }
  norm_eq _ := rfl
  coefficient_eq _ := rfl
  function_eq := rfl

@[simp] theorem ofHecke_analytic (χ : HeckeCharacter K) (β : ℝ)
    (analytic : ZeroFreeData (heckeContinuation K χ) β) :
    (ofHecke χ β analytic).slot.analytic = analytic := rfl

end OriginalPrimeAnalyticData

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalHeckePrimeAnalytic.arithmetic
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalHeckePrimeAnalytic.absolutelySummable
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalHeckePrimeAnalytic.euler
#print axioms HeckeSkeleton.Moments.EngineStep.OriginalPrimeAnalyticData.ofHecke
