import FLTReuse.M1d4e501986eb161a
import FLTReuse.M1c722af550c2b699
import FLTReuse.Mad950c02a4314b2a
import FLTReuse.M1868db956c866c8d
namespace P2MW.S_LanglandsTunnell_TateLocal_localZeta_stdTestFunAt_ne_zero_of_unramified
attribute [-instance] NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers     IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal   

set_option autoImplicit false

open LanglandsTunnell.TateLocal NumberField NumberField.StandardAddChar NumberField.AdelicLevel IsDedekindDomain MeasureTheory

attribute [local instance] LanglandsTunnell.TateLocal.localBorel
  LanglandsTunnell.TateLocal.borelSpace_localBorel

theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (RingOfIntegers K))
    (χ : (v.adicCompletion K)ˣ →* ℂˣ) (s : ℂ) (hχ : HasConductorExponentAt K v χ 0)
    (hs : ‖(χ (uniformizerUnit K v) : ℂ)‖ * (Ideal.absNorm v.asIdeal : ℝ) ^ (-s.re) < 1) :
    localZeta (selfDualHaarAt K v) (stdTestFunAt K v χ) χ s ≠ 0 := by
  have hq0 : Ideal.absNorm v.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot
  have hq1' : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact v.isPrime.ne_top
  have hq1 : 1 < Ideal.absNorm v.asIdeal := by omega
  have hq : 0 < Ideal.absNorm v.asIdeal := by omega
  have hqR : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by exact_mod_cast hq1
  have hqR0 : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by linarith
  rw [LanglandsTunnell.TateLocal.localZeta_stdTestFunAt_eq_of_unramified K v χ s hχ hs,
    LanglandsTunnell.TateLocal.selfDualHaarAt_real_units_eq K v,
    localLFactorAt_of_hasConductorExponentAt_zero K v hχ]
  refine mul_ne_zero ?_ (inv_ne_zero ?_)
  · rw [Complex.ofReal_ne_zero]
    refine mul_ne_zero (sub_ne_zero.mpr ?_) (Real.rpow_pos_of_pos hqR0 _).ne'
    exact (inv_lt_one_of_one_lt₀ hqR).ne'
  · refine sub_ne_zero.mpr fun h => ?_
    have hn : ‖(χ (uniformizerUnit K v) : ℂ) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)‖ < 1 := by
      rw [norm_mul, Complex.norm_natCast_cpow_of_pos hq, Complex.neg_re]
      exact hs
    rw [← h, norm_one] at hn
    exact lt_irrefl _ hn

#print axioms solution
