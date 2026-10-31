import HeckeGeneral.Analysis.IdealDerivativeEulerLog
import HeckeGeneral.Analysis.HeckeContinuation
import HeckeGeneral.Analysis.IdealDerivativeSmoothing
import ExpansionInterfaces.AnnularMellinIdentity

/-!
# The actual continued negative logarithmic derivative on its initial line

The index is `(n,p)`, with positive exponent `n+1`.  Its norm is the norm of
that actual prime-power ideal.  `Prod.swap` connects this index to the proved
Hecke prime-power expansion.  The literal coefficients are also the ones
used by the finite Mellin interface.  The absolute majorant is chosen from
the number field and the initial abscissa alone, before the character,
frequency, smoothing scale or finite support is chosen.
-/

set_option autoImplicit false
noncomputable section
namespace Expansion.Project

open NumberField IsDedekindDomain Filter
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open scoped Classical Topology nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]

abbrev ActualPrimeLogIndex := ℕ × HeightOneSpectrum (𝓞 K)

instance countable_actualPrimeLogIndex : Countable (ActualPrimeLogIndex K) :=
  ((primePowerIdeal_injective K).comp
    (Equiv.prodComm ℕ (HeightOneSpectrum (𝓞 K))).injective).countable

/-- The actual norm of the positive prime power, with `(n,p)` indexing. -/
def actualPrimePowerNorm (np : ActualPrimeLogIndex K) : ℝ :=
  idealNorm K (primePowerIdeal K (Prod.swap np))

/-- The coefficient of the actual negative logarithmic derivative. -/
def actualPrimeLogCoefficient (χ : HeckeCharacter K) (np : ActualPrimeLogIndex K) : ℂ :=
  (Real.log (Ideal.absNorm np.2.asIdeal : ℝ) : ℂ) *
    primeCoefficient K χ np.2 ^ (np.1 + 1)

/-- The meromorphic continuation supplies the function on the finite rectangle. -/
def actualPrimeLogFunction (χ : HeckeCharacter K) (s : ℂ) : ℂ :=
  -deriv (heckeContinuation K χ) s / heckeContinuation K χ s

theorem actualPrimePowerNorm_pos (np : ActualPrimeLogIndex K) :
    0 < actualPrimePowerNorm K np :=
  idealNorm_pos K (primePowerIdeal K (Prod.swap np))

theorem actualPrimePowerNorm_eq (np : ActualPrimeLogIndex K) :
    actualPrimePowerNorm K np = (Ideal.absNorm np.2.asIdeal : ℝ) ^ (np.1 + 1) :=
  idealNorm_primePowerIdeal K (Prod.swap np)

/-- A concrete finite support window, pulled back from actual integral ideals. -/
def actualPrimeLogWindow (B : ℝ) : Finset (ActualPrimeLogIndex K) :=
  (Ideal.finite_setOfPred_absNorm_le ⌈B⌉₊).toFinset.preimage
    (fun np : ActualPrimeLogIndex K => (primePowerIdeal K (Prod.swap np)).val) (by
      intro np _ mp _ h
      apply (Equiv.prodComm ℕ (HeightOneSpectrum (𝓞 K))).injective
      apply primePowerIdeal_injective K
      exact Subtype.ext h)

theorem mem_actualPrimeLogWindow_of_le (B : ℝ) (np : ActualPrimeLogIndex K)
    (hN : actualPrimePowerNorm K np ≤ B) : np ∈ actualPrimeLogWindow K B := by
  unfold actualPrimeLogWindow
  apply Finset.mem_preimage.mpr
  apply (Set.Finite.mem_toFinset _).mpr
  change Ideal.absNorm (primePowerIdeal K (Prod.swap np)).val ≤ ⌈B⌉₊
  have h : (Ideal.absNorm (primePowerIdeal K (Prod.swap np)).val : ℝ) ≤ (⌈B⌉₊ : ℝ) :=
    hN.trans (Nat.le_ceil B)
  exact_mod_cast h

/-- The finite Mellin coefficient is exactly the genuine prime-power term. -/
theorem actualPrimeLogTerm_eq (χ : HeckeCharacter K) (s : ℂ)
    (np : ActualPrimeLogIndex K) :
    actualPrimeLogCoefficient K χ np * (actualPrimePowerNorm K np : ℂ) ^ (-s) =
      primePowerLogTerm K (primeCoefficient K χ) 1 s (Prod.swap np) := by
  rw [primePowerLogTerm, pow_one,
    ← primePower_dirichletTerm K (primeCoefficient K χ) s (Prod.swap np)]
  simp only [actualPrimeLogCoefficient, actualPrimePowerNorm, dirichletTerm,
    nonzeroIdealCoefficient, primePowerIdeal_val, idealCoefficient_prime_pow,
    Prod.swap, mul_assoc]

theorem actualPrimeLogTerm_norm (χ : HeckeCharacter K) (s : ℂ)
    (np : ActualPrimeLogIndex K) :
    ‖primePowerLogTerm K (primeCoefficient K χ) 1 s (Prod.swap np)‖ =
      ‖actualPrimeLogCoefficient K χ np‖ * actualPrimePowerNorm K np ^ (-s.re) := by
  rw [← actualPrimeLogTerm_eq K χ s np]
  exact norm_dirichletTerm (actualPrimePowerNorm K) (actualPrimeLogCoefficient K χ)
    s np (actualPrimePowerNorm_pos K np)

/-- Initial-line calibration uses equality of the actual continuations on an
open neighborhood, so it also identifies their derivatives. -/
theorem actualPrimeLogFunction_eq_primePowerLogSeries (χ : HeckeCharacter K)
    {s : ℂ} (hs : 1 < s.re) :
    actualPrimeLogFunction K χ s =
      primePowerLogSeries K (primeCoefficient K χ) 1 s := by
  have heq : heckeContinuation K χ =ᶠ[𝓝 s] heckeLSeries K χ := by
    have hnhds : {z : ℂ | 1 < z.re} ∈ 𝓝 s :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs
    filter_upwards [hnhds] with z hz
    exact heckeContinuation_eq_series K χ hz
  rw [actualPrimeLogFunction, heq.deriv_eq, heckeContinuation_eq_series K χ hs,
    neg_div]
  change -heckeLogDerivative K χ s = _
  rw [heckeLogDerivative_eq_primePowerSeries K χ hs, neg_neg]

/-- Exact calibration with the coefficient-first finite Mellin interface. -/
theorem actualPrimeLogFunction_eq_dirichletSeries (χ : HeckeCharacter K)
    {s : ℂ} (hs : 1 < s.re) :
    actualPrimeLogFunction K χ s = ExpansionInterfaces.Mellin.dirichletSeries
      (actualPrimeLogCoefficient K χ) (actualPrimePowerNorm K) s := by
  rw [actualPrimeLogFunction_eq_primePowerLogSeries K χ hs]
  unfold primePowerLogSeries ExpansionInterfaces.Mellin.dirichletSeries
  calc
    _ = ∑' np : ActualPrimeLogIndex K,
        primePowerLogTerm K (primeCoefficient K χ) 1 s (Prod.swap np) :=
      ((Equiv.prodComm ℕ (HeightOneSpectrum (𝓞 K))).tsum_eq
        (primePowerLogTerm K (primeCoefficient K χ) 1 s)).symm
    _ = _ := tsum_congr fun np => (actualPrimeLogTerm_eq K χ s np).symm

/-- A character-independent pullback of the proved ideal logarithmic majorant. -/
def actualPrimeLogMajorant (σ : ℝ) (np : ActualPrimeLogIndex K) : ℝ :=
  Real.log (actualPrimePowerNorm K np) * actualPrimePowerNorm K np ^ (-σ)

theorem actualPrimeLogMajorant_nonneg (σ : ℝ) (np : ActualPrimeLogIndex K) :
    0 ≤ actualPrimeLogMajorant K σ np :=
  mul_nonneg (Real.log_nonneg (one_le_idealNorm K (primePowerIdeal K (Prod.swap np))))
    (Real.rpow_nonneg (actualPrimePowerNorm_pos K np).le _)

theorem summable_actualPrimeLogMajorant {σ : ℝ} (hσ : 1 < σ) :
    Summable (actualPrimeLogMajorant K σ) := by
  have h := (summable_ideal_logPower_rpow K 1 hσ).comp_injective
    ((primePowerIdeal_injective K).comp
      (Equiv.prodComm ℕ (HeightOneSpectrum (𝓞 K))).injective)
  refine h.congr ?_
  intro np
  change Real.log (actualPrimePowerNorm K np) ^ 1 * actualPrimePowerNorm K np ^ (-σ) =
    Real.log (actualPrimePowerNorm K np) * actualPrimePowerNorm K np ^ (-σ)
  rw [pow_one]

theorem actualPrimeLog_mass_term_le (χ : HeckeCharacter K) (σ : ℝ)
    (np : ActualPrimeLogIndex K) :
    ‖actualPrimeLogCoefficient K χ np‖ * actualPrimePowerNorm K np ^ (-σ) ≤
      actualPrimeLogMajorant K σ np := by
  have h := (norm_primePowerLogTerm_le_idealLogTerm K (primeCoefficient K χ)
    1 (σ : ℂ) (Prod.swap np)).trans
      (norm_idealLogTerm_le K (nonzeroIdealCoefficient (primeCoefficient K χ))
        (norm_nonzeroIdealCoefficient_le_one (primeCoefficient K χ)
          (norm_primeCoefficient_le_one K χ)) 1 (σ : ℂ)
        (primePowerIdeal K (Prod.swap np)))
  rw [actualPrimeLogTerm_norm K χ (σ : ℂ) np] at h
  simpa only [actualPrimeLogMajorant, actualPrimePowerNorm, Complex.ofReal_re,
    pow_one] using h

/-- Absolute initial-line summability has no analytic hypothesis on the character. -/
theorem actualPrimeLog_absolutelySummable (χ : HeckeCharacter K)
    {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun np : ActualPrimeLogIndex K =>
      ‖actualPrimeLogCoefficient K χ np‖ * actualPrimePowerNorm K np ^ (-σ)) :=
  Summable.of_nonneg_of_le
    (fun np => mul_nonneg (norm_nonneg _)
      (Real.rpow_nonneg (actualPrimePowerNorm_pos K np).le _))
    (actualPrimeLog_mass_term_le K χ σ) (summable_actualPrimeLogMajorant K hσ)

/-- This mass is chosen before the character, height, scale and smoothing data. -/
def actualPrimeLogMass (σ : ℝ) : ℝ := ∑' np, actualPrimeLogMajorant K σ np

theorem actualPrimeLogMass_nonneg (σ : ℝ) : 0 ≤ actualPrimeLogMass K σ :=
  tsum_nonneg (actualPrimeLogMajorant_nonneg K σ)

theorem actualPrimeLog_absMass_le (χ : HeckeCharacter K)
    {σ : ℝ} (hσ : 1 < σ) :
    (∑' np : ActualPrimeLogIndex K,
      ‖actualPrimeLogCoefficient K χ np‖ * actualPrimePowerNorm K np ^ (-σ)) ≤
        actualPrimeLogMass K σ :=
  Summable.tsum_le_tsum (actualPrimeLog_mass_term_le K χ σ)
    (actualPrimeLog_absolutelySummable K χ hσ) (summable_actualPrimeLogMajorant K hσ)

end Expansion.Project

#print axioms Expansion.Project.mem_actualPrimeLogWindow_of_le
#print axioms Expansion.Project.actualPrimeLogTerm_eq
#print axioms Expansion.Project.actualPrimeLogFunction_eq_dirichletSeries
#print axioms Expansion.Project.actualPrimeLog_absolutelySummable
#print axioms Expansion.Project.actualPrimeLog_absMass_le
