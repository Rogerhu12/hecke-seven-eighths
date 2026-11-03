import ActualAdditiveGramResidueExpansion
import ActualGramJointKernelIdentification
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
UNCOMPILED / native 0. The actual two-column complex powers have reciprocal
absolute weight and phase +nu (log x - log y). The minus sign in the second
column comes from complex conjugation. The annular test is arbitrary and
complex-valued. The actual S-unit phase retains both finite coordinates;
no archimedean-only phase identification is assumed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeGeneral.ThetaSkeleton.Physical.ActualAdditiveGramDraft

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Global
open ActualGramJointKernelDraft
open ActualProbePairNormDraft
open scoped Classical ComplexConjugate

/-- A positive real base has the literal inverse amplitude and positive
moving phase, without any branch choice. -/
theorem positiveReal_cpow_minus_one_add_I_mul (x ν : ℝ) (hx : 0 < x) :
    (x : ℂ) ^ ((-1 : ℂ) + Complex.I * (ν : ℂ)) =
      ((x⁻¹ : ℝ) : ℂ) * traceRealMovingPhase ν (Real.log x) := by
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  calc
    _ = (x : ℂ)⁻¹ *
        Complex.exp ((Real.log x : ℂ) * (Complex.I * (ν : ℂ))) := by
      rw [Complex.cpow_add (-1 : ℂ) (Complex.I * (ν : ℂ)) hx0,
        Complex.cpow_neg_one, Complex.cpow_def_of_ne_zero hx0,
        ← Complex.ofReal_log hx.le]
    _ = _ := by
      rw [Complex.ofReal_inv]
      exact congrArg (fun z : ℂ => (x : ℂ)⁻¹ * Complex.exp z)
        (by ring : (Real.log x : ℂ) * (Complex.I * (ν : ℂ)) =
          Complex.I * (ν : ℂ) * (Real.log x : ℂ))

/-- The genuine cpow pair has positive nu on the first logarithm and
negative nu on the second. The reciprocal is a real scalar. -/
theorem positiveReal_cpow_pair_eq_reciprocal_movingPhase
    (x y ν : ℝ) (hx : 0 < x) (hy : 0 < y) :
    (x : ℂ) ^ ((-1 : ℂ) + Complex.I * (ν : ℂ)) *
        conj ((y : ℂ) ^ ((-1 : ℂ) + Complex.I * (ν : ℂ))) =
      (((x * y)⁻¹ : ℝ) : ℂ) *
        traceRealMovingPhase ν (Real.log x - Real.log y) := by
  have hphase :
      traceRealMovingPhase ν (Real.log x) *
          conj (traceRealMovingPhase ν (Real.log y)) =
        traceRealMovingPhase ν (Real.log x - Real.log y) := by
    unfold traceRealMovingPhase
    rw [← Complex.exp_conj, ← Complex.exp_add]
    congr 1
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_sub]
    ring
  rw [positiveReal_cpow_minus_one_add_I_mul x ν hx,
    positiveReal_cpow_minus_one_add_I_mul y ν hy]
  calc
    _ = (((x * y)⁻¹ : ℝ) : ℂ) *
        (traceRealMovingPhase ν (Real.log x) *
          conj (traceRealMovingPhase ν (Real.log y))) := by
      simp only [map_mul, map_inv₀, Complex.conj_ofReal, Complex.ofReal_inv,
        Complex.ofReal_mul, mul_inv_rev]
      ring
    _ = _ := by rw [hphase]

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))

local notation "SS" => (S : Set (HeightOneSpectrum (𝓞 K)))

/-- The original coefficient, with its complex test still fully
conjugated, is the reciprocal weight times the actual total S-unit phase
on the literal normalized columns. -/
theorem actualAdditiveGramPairCoefficient_eq_totalMellinPhase
    (D : ThetaArithmeticData K SS) (c : ExteriorIdeal K SS → ℂ)
    (W : SmoothAnnularTest) (Y ν : ℝ) (hY : 0 < Y)
    (I J : ExteriorIdeal K SS) :
    actualAdditiveGramPairCoefficient K SS c W Y ν I J =
      (c I * conj (c J)) *
        (W.toFun (exteriorNorm K SS I / Y) *
          conj (W.toFun (exteriorNorm K SS J / Y))) *
        (((((exteriorNorm K SS I / Y) *
          (exteriorNorm K SS J / Y))⁻¹ : ℝ) : ℂ)) *
        sUnitMellinPhase K SS ν
          (additiveGramColumnFinite K S D I Y hY)
          (additiveGramColumnFinite K S D J Y hY)
          ((additiveGramColumnArch K S D I Y hY).val,
            (additiveGramColumnArch K S D J Y hY).val) := by
  have hI : 0 < exteriorNorm K SS I / Y :=
    div_pos (exteriorNorm_pos_of_probeGenerator K SS D I) hY
  have hJ : 0 < exteriorNorm K SS J / Y :=
    div_pos (exteriorNorm_pos_of_probeGenerator K SS D J) hY
  unfold actualAdditiveGramPairCoefficient
  rw [positiveReal_cpow_pair_eq_reciprocal_movingPhase
      (exteriorNorm K SS I / Y) (exteriorNorm K SS J / Y) ν hI hJ,
    ← additiveGramColumn_mellinPhase K S D I J Y ν hY]
  ring

end HeckeGeneral.ThetaSkeleton.Physical.ActualAdditiveGramDraft
