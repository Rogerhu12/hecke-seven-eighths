import HeckeGeneral.Analysis.ActualSIntegerSobolevTests
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-! Actual smooth log-scale/Mellin rows, with the fixed S/6 zero extension.
Local equality with a concrete finite envelope proves joint smoothness;
no smoothness of a changing finite index set is assumed. -/

noncomputable section

namespace HeckeGeneral.Analysis.ActualSIntegerMoments

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.Analysis.SquarefreeAmplification
open scoped BigOperators Classical Topology ContDiff

theorem mellinLogTest_log_scale (m : ℕ) (s : ℂ) {q : ℝ} (hq : 0 < q) (t : ℝ) :
    mellinLogTest m s (q * Real.exp (-t)) =
      (-(Real.log q - t : ℝ) : ℂ) ^ m *
        (fixedDyadicWeight (q * Real.exp (-t)) : ℂ) *
        Complex.exp ((Real.log q - t : ℝ) * (-s)) := by
  have hy : 0 < q * Real.exp (-t) := mul_pos hq (Real.exp_pos _)
  have hl : Real.log (q * Real.exp (-t)) = Real.log q - t := by
    rw [Real.log_mul hq.ne' (Real.exp_ne_zero _), Real.log_exp]
    ring
  simp only [mellinLogTest, dyadicMellinWeight, sexticDyadicWeight,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hy.ne'),
    ← Complex.ofReal_log hy.le, hl]
  ring

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (ζ : K) (hζ : IsPrimitiveRoot ζ 6) (σ : K →+* ℂ)

def actualLogTestLogPolynomial (η : HeckeCharacter K)
    (q : ActualSIntegerOrbit K S) (m : ℕ) (p : ℝ × ℂ) : ℂ :=
  sIntegerSexticInverseIdealPolynomial K S ζ hζ σ η
    (dyadicIdealSupport K (Real.exp p.1)) q.out.val (Real.exp p.1)
    (mellinLogTest m p.2)

def actualEulerLogTestLogPolynomial (η : HeckeCharacter K)
    (q : ActualSIntegerOrbit K S) (m : ℕ) (p : ℝ × ℂ) : ℂ :=
  sIntegerSexticInverseIdealPolynomial K S ζ hζ σ η
    (dyadicIdealSupport K (Real.exp p.1)) q.out.val (Real.exp p.1)
    (scaleEulerTest (mellinLogTest m p.2))

theorem contDiff_fixedFiniteMellinLogPolynomial (η : HeckeCharacter K)
    (F : Finset (NonzeroIdeal K)) (u : S.integer K) (m : ℕ) :
    ContDiff ℝ ∞ (fun p : ℝ × ℂ =>
      actualFiniteInverseLogPolynomial K S ζ hζ σ η F u (mellinLogTest m p.2) p.1) := by
  simp only [actualFiniteInverseLogPolynomial]
  simp_rw [mellinLogTest_log_scale m _ (idealNorm_pos K _)]
  apply ContDiff.mul
  · have hn : ContDiff ℝ ∞ (fun p : ℝ × ℂ => Real.exp (-p.1 / 2)) :=
      Real.contDiff_exp.comp (contDiff_fst.neg.div_const 2)
    exact Complex.ofRealCLM.contDiff.comp hn
  · apply ContDiff.sum
    intro I _
    have hW : ContDiff ℝ ∞ (fun p : ℝ × ℂ =>
        (fixedDyadicWeight (idealNorm K I * Real.exp (-p.1)) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp
        (contDiff_fixedDyadicWeight.comp (by fun_prop))
    have hr : ContDiff ℝ ∞ (fun p : ℝ × ℂ => Real.log (idealNorm K I) - p.1) :=
      contDiff_const.sub contDiff_fst
    have hL : ContDiff ℝ ∞ (fun p : ℝ × ℂ => ((Real.log (idealNorm K I) - p.1 : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp hr
    have hExp : ContDiff ℝ ∞ Complex.exp := Complex.contDiff_exp
    exact contDiff_const.mul (((hL.neg.pow m).mul hW).mul
      (hExp.comp (hL.mul contDiff_snd.neg)))

theorem contDiff_actualLogTestLogPolynomial (η : HeckeCharacter K)
    (q : ActualSIntegerOrbit K S) (m : ℕ) :
    ContDiff ℝ ∞ (actualLogTestLogPolynomial K S ζ hζ σ η q m) := by
  apply contDiff_iff_contDiffAt.mpr
  intro p
  apply (contDiff_fixedFiniteMellinLogPolynomial K S ζ hζ σ η
    (dyadicIdealSupport K (2 * Real.exp p.1)) q.out.val m).contDiffAt.congr_of_eventuallyEq
  have hwindow : ∀ᶠ v : ℝ × ℂ in 𝓝 p, Real.exp v.1 < 2 * Real.exp p.1 :=
    (Real.continuous_exp.comp continuous_fst).continuousAt.eventually_lt_const
      (by change Real.exp p.1 < 2 * Real.exp p.1; linarith [Real.exp_pos p.1])
  filter_upwards [hwindow] with v hv
  rw [actualFiniteInverseLogPolynomial_eq]
  exact sIntegerInversePolynomial_eq_largerEnvelope K S ζ hζ σ η q.out.val
    (mellinLogTest m v.2) (fun y hy => mellinLogTest_zero_of_ge m v.2 hy)
    (Real.exp_pos v.1) hv.le

theorem hasDerivAt_actualLogTestLogPolynomial_scale
    (η : HeckeCharacter K) (q : ActualSIntegerOrbit K S) (m : ℕ)
    (t : ℝ) (s : ℂ) :
    HasDerivAt (fun v : ℝ => actualLogTestLogPolynomial K S ζ hζ σ η q m (v, s))
      (actualEulerLogTestLogPolynomial K S ζ hζ σ η q m (t, s)) t := by
  let R := 2 * Real.exp t
  have hd := hasDerivAt_actualFiniteInverseLogPolynomial K S ζ hζ σ η
    (dyadicIdealSupport K R) q.out.val (mellinLogTest m s) t
    (fun I _ => differentiableAt_mellinLogTest m s
      (mul_pos (idealNorm_pos K I) (Real.exp_pos _)))
  have heuler : actualEulerLogTestLogPolynomial K S ζ hζ σ η q m (t, s) =
      actualFiniteInverseLogPolynomial K S ζ hζ σ η (dyadicIdealSupport K R)
        q.out.val (scaleEulerTest (mellinLogTest m s)) t := by
    rw [actualFiniteInverseLogPolynomial_eq]
    apply sIntegerInversePolynomial_eq_largerEnvelope
    · intro y hy
      simp only [scaleEulerTest, mellinLogTest_zero_of_ge m s hy,
        deriv_mellinLogTest_zero_of_ge m s hy, mul_zero, sub_self]
    · exact Real.exp_pos t
    · dsimp [R]
      linarith [Real.exp_pos t]
  rw [heuler]
  apply hd.congr_of_eventuallyEq
  have hwindow : ∀ᶠ v : ℝ in 𝓝 t, Real.exp v < R :=
    Real.continuous_exp.continuousAt.eventually_lt_const (by dsimp [R]; linarith [Real.exp_pos t])
  filter_upwards [hwindow] with v hv
  rw [actualFiniteInverseLogPolynomial_eq]
  exact sIntegerInversePolynomial_eq_largerEnvelope K S ζ hζ σ η q.out.val
    (mellinLogTest m s) (fun y hy => mellinLogTest_zero_of_ge m s hy)
    (Real.exp_pos v) hv.le

theorem continuous_actualEulerLogTestLogPolynomial
    (η : HeckeCharacter K) (q : ActualSIntegerOrbit K S) (m : ℕ) :
    Continuous (actualEulerLogTestLogPolynomial K S ζ hζ σ η q m) := by
  let F := actualLogTestLogPolynomial K S ζ hζ σ η q m
  have hF : ContDiff ℝ ∞ F := contDiff_actualLogTestLogPolynomial K S ζ hζ σ η q m
  have heq (p : ℝ × ℂ) : actualEulerLogTestLogPolynomial K S ζ hζ σ η q m p =
      fderiv ℝ F p (1, 0) := by
    have hp : HasDerivAt (fun t : ℝ => (t, p.2)) (1, 0) p.1 :=
      (hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2)
    have hd := (hF.differentiable (by norm_num)).differentiableAt.hasFDerivAt.comp_hasDerivAt p.1 hp
    exact (hasDerivAt_actualLogTestLogPolynomial_scale K S ζ hζ σ η q m p.1 p.2).unique hd
  apply ((hF.continuous_fderiv_apply (by norm_num)).comp
    (continuous_id.prodMk (show Continuous (fun _ : ℝ × ℂ => ((1 : ℝ), (0 : ℂ))) from
      continuous_const))).congr
  exact fun p => (heq p).symm

theorem hasDerivAt_actualLogTestLogPolynomial_parameter
    (η : HeckeCharacter K) (q : ActualSIntegerOrbit K S) (m : ℕ)
    (t : ℝ) (s : ℂ) :
    HasDerivAt (fun z : ℂ => actualLogTestLogPolynomial K S ζ hζ σ η q m (t, z))
      (actualLogTestLogPolynomial K S ζ hζ σ η q (m + 1) (t, s)) s := by
  unfold actualLogTestLogPolynomial sIntegerSexticInverseIdealPolynomial
  have hi (I : NonzeroIdeal K) (_hI : I ∈ dyadicIdealSupport K (Real.exp t)) :=
    (hasDerivAt_mellinLogTest_parameter m s
      (div_pos (idealNorm_pos K I) (Real.exp_pos t))).const_mul
      (actualInverseIdealCoefficient K S ζ hζ σ η q.out.val I)
  convert (HasDerivAt.fun_sum hi).const_mul ((Real.sqrt (Real.exp t) : ℂ)⁻¹) using 1
  all_goals rfl

end HeckeGeneral.Analysis.ActualSIntegerMoments
