import ActualGramMellinCoefficient

/-!
UNCOMPILED / native 0. The actual T endpoint uses the fixed nonnegative,
real-valued denominator of P. Its two inverse norm powers are absorbed
into one real smooth annular weight b(t)=Re(W(t))/t. The apparent singularity
at zero is removed by W's original support gap, rather than by a new
smoothness assumption. The positive first-column Mellin phase and negative
second-column phase are retained exactly.

This identifies the actual c=1 pair coefficient. It does not assert the
remaining ideal-to-column partition identity or a Gram estimate.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HeckeGeneral.ThetaSkeleton.Physical.ActualDenominatorGramWeightDraft

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Global
open ActualAdditiveGramDraft ActualProbePairNormDraft
open scoped Classical ContDiff ComplexConjugate Topology

/-- The real annular weight of the actual additive Gram pair. -/
def denominatorGramWeight (W : DenominatorTest) (t : ℝ) : ℝ :=
  (W.toFun t).re / t

theorem denominator_toFun_eq_ofReal (W : DenominatorTest) (t : ℝ) :
    W.toFun t = ((W.toFun t).re : ℂ) := by
  apply Complex.ext
  · simp
  · simpa only [Complex.ofReal_im] using W.real_valued t

theorem support_denominatorGramWeight (W : DenominatorTest) :
    Function.support (denominatorGramWeight W) ⊆ Set.Icc W.lower W.upper := by
  intro t ht
  apply W.support
  intro hz
  exact ht (by simp only [denominatorGramWeight, hz, Complex.zero_re, zero_div])

/-- The original support interval is unchanged by the reciprocal factor. -/
theorem tsupport_denominatorGramWeight (W : DenominatorTest) :
    tsupport (denominatorGramWeight W) ⊆ Set.Icc W.lower W.upper :=
  closure_minimal (support_denominatorGramWeight W) isClosed_Icc

theorem hasCompactSupport_denominatorGramWeight (W : DenominatorTest) :
    HasCompactSupport (denominatorGramWeight W) :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _)
    (tsupport_denominatorGramWeight W)

/-- The totalized quotient is locally zero near zero, since lower>0. -/
theorem denominatorGramWeight_eventually_zero (W : DenominatorTest) :
    denominatorGramWeight W =ᶠ[𝓝 (0 : ℝ)] 0 := by
  apply notMem_tsupport_iff_eventuallyEq.mp
  intro hzero
  have hlo := (tsupport_denominatorGramWeight W hzero).1
  exact (not_le_of_gt W.lower_pos) hlo

theorem contDiff_denominatorGramWeight (W : DenominatorTest) :
    ContDiff ℝ ∞ (denominatorGramWeight W) := by
  have hre : ContDiff ℝ ∞ (fun t : ℝ => (W.toFun t).re) :=
    Complex.reCLM.contDiff.comp W.smooth
  apply contDiff_iff_contDiffAt.mpr
  intro t
  by_cases ht : t = 0
  · subst t
    exact contDiffAt_const.congr_of_eventuallyEq
      (denominatorGramWeight_eventually_zero W)
  · exact hre.contDiffAt.div contDiffAt_id ht

theorem denominatorGramWeight_nonnegative (W : DenominatorTest) (t : ℝ) :
    0 ≤ denominatorGramWeight W t := by
  by_cases hz : denominatorGramWeight W t = 0
  · exact hz.symm.le
  · have ht := W.lower_pos.trans_le (support_denominatorGramWeight W hz).1
    exact div_nonneg (W.nonnegative t) ht.le

/-- The provider's real cutoff hypotheses follow from the original W. -/
theorem denominatorGramWeight_annular_data (W : DenominatorTest) :
    ContDiff ℝ ∞ (denominatorGramWeight W) ∧
      HasCompactSupport (denominatorGramWeight W) ∧
      tsupport (denominatorGramWeight W) ⊆ Set.Icc W.lower W.upper :=
  ⟨contDiff_denominatorGramWeight W, hasCompactSupport_denominatorGramWeight W,
    tsupport_denominatorGramWeight W⟩

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- Exact pair weight at the actual T endpoint. There is no extra Y factor:
Y^(-3) remains the separate outer central Gram normalization. -/
theorem actualDenominator_pairCoefficient_eq_realWeight_phase
    (P : ProbeData K S) (Y η : ℝ) (hY : 0 < Y)
    (I J : ExteriorIdeal K S) :
    actualAdditiveGramPairCoefficient K S (fun _ => 1)
        P.denominator.toSmoothAnnularTest Y η I J =
      (denominatorGramWeight P.denominator (exteriorNorm K S I / Y) : ℂ) *
        (denominatorGramWeight P.denominator (exteriorNorm K S J / Y) : ℂ) *
        traceRealMovingPhase η
          (Real.log (exteriorNorm K S I / Y) -
            Real.log (exteriorNorm K S J / Y)) := by
  have hI : 0 < exteriorNorm K S I / Y :=
    div_pos (exteriorNorm_pos_of_probeGenerator K S P.arithmetic I) hY
  have hJ : 0 < exteriorNorm K S J / Y :=
    div_pos (exteriorNorm_pos_of_probeGenerator K S P.arithmetic J) hY
  unfold actualAdditiveGramPairCoefficient
  rw [positiveReal_cpow_pair_eq_reciprocal_movingPhase
    (exteriorNorm K S I / Y) (exteriorNorm K S J / Y) η hI hJ]
  change (1 * conj (1 : ℂ)) *
      (P.denominator.toFun (exteriorNorm K S I / Y) *
        conj (P.denominator.toFun (exteriorNorm K S J / Y))) *
      (((((exteriorNorm K S I / Y) *
        (exteriorNorm K S J / Y))⁻¹ : ℝ) : ℂ) *
        traceRealMovingPhase η
          (Real.log (exteriorNorm K S I / Y) -
            Real.log (exteriorNorm K S J / Y))) = _
  rw [denominator_toFun_eq_ofReal P.denominator (exteriorNorm K S I / Y),
    denominator_toFun_eq_ofReal P.denominator (exteriorNorm K S J / Y)]
  simp only [map_one, one_mul, Complex.conj_ofReal, Complex.ofReal_re, denominatorGramWeight,
    div_eq_mul_inv, Complex.ofReal_mul, Complex.ofReal_inv, mul_inv_rev]
  ring

end HeckeGeneral.ThetaSkeleton.Physical.ActualDenominatorGramWeightDraft
