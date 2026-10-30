import HeckeGeneral.Analysis.ActualSIntegerZeroSlotMI
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
The genuine log-scale derivative of the actual sextic inverse polynomial,
first on a fixed finite ideal envelope. The fixed S/6 deletion and actual
Hecke/sextic coefficients are retained. No moment bound is proved here.

Q's rowwise Sobolev argument uses the Euler-derived test and a uniform range
of independent scales. The frozen ActualZeroSlotMI only gives one fixed
test family at D=H^rho, with constants allowed to depend on rho. Its reverse
implication to ActualZeroSlotScaleSupInput is therefore not supplied.
-/

noncomputable section

namespace HeckeGeneral.Analysis.ActualSIntegerMoments

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckeGeneral.Analysis.SquarefreeAmplification
open HeckeGeneral.Arithmetic.IdealMobiusMask
open UniqueFactorizationMonoid
open scoped BigOperators Classical Topology

/-- The test obtained by differentiating the normalized row in log scale. -/
def scaleEulerTest (W : ℝ → ℂ) (y : ℝ) : ℂ :=
  -(1 / 2 : ℂ) * W y - (y : ℂ) * deriv W y

/-- The actual fixed dyadic Mellin family is differentiable on the positive axis. -/
theorem differentiableAt_dyadicMellinWeight (s : ℂ) {y : ℝ} (hy : 0 < y) :
    DifferentiableAt ℝ (dyadicMellinWeight s) y := by
  have hr : DifferentiableAt ℝ fixedDyadicWeight y :=
    (contDiff_fixedDyadicWeight.differentiable (by norm_num)).differentiableAt
  have hW : DifferentiableAt ℝ sexticDyadicWeight y :=
    hr.hasDerivAt.ofReal_comp.differentiableAt
  have hp : DifferentiableAt ℝ (fun x : ℝ => (x : ℂ) ^ (-s)) y := by
    by_cases hs : s = 0
    · simp only [hs, neg_zero, Complex.cpow_zero]
      exact differentiableAt_const _
    · exact (hasDerivAt_ofReal_cpow_const hy.ne' (neg_ne_zero.mpr hs)).differentiableAt
  exact hW.mul hp

variable (K : Type*) [Field K] [NumberField K]
variable (S : Set (HeightOneSpectrum (𝓞 K))) [Fintype S]
variable (ζ : K) (hζ : IsPrimitiveRoot ζ 6) (σ : K →+* ℂ)

/-- Literal, scale-independent arithmetic coefficient of an actual ideal term. -/
def actualInverseIdealCoefficient (η : HeckeCharacter K)
    (u : S.integer K) (I : NonzeroIdeal K) : ℂ :=
  (moebius I.val : ℂ) * heckeIdealCoefficient K η I *
    zeroExtendedSexticIdealEvaluation K S ζ hζ σ I u ^ (-1 : ℤ)

/-- The same actual finite ideal polynomial, expressed in logarithmic scale. -/
def actualFiniteInverseLogPolynomial (η : HeckeCharacter K)
    (F : Finset (NonzeroIdeal K)) (u : S.integer K) (W : ℝ → ℂ) (t : ℝ) : ℂ :=
  (Real.exp (-t / 2) : ℂ) *
    ∑ I ∈ F, actualInverseIdealCoefficient K S ζ hζ σ η u I *
      W (idealNorm K I * Real.exp (-t))

/-- This is the existing normalized finite ideal polynomial, not a new row model. -/
theorem actualFiniteInverseLogPolynomial_eq (η : HeckeCharacter K)
    (F : Finset (NonzeroIdeal K)) (u : S.integer K) (W : ℝ → ℂ) (t : ℝ) :
    actualFiniteInverseLogPolynomial K S ζ hζ σ η F u W t =
      sIntegerSexticInverseIdealPolynomial K S ζ hζ σ η F u (Real.exp t) W := by
  simp only [actualFiniteInverseLogPolynomial, sIntegerSexticInverseIdealPolynomial,
    sIntegerSexticInverseIdealTerm, actualInverseIdealCoefficient,
    ← Real.exp_half, ← Complex.ofReal_inv, ← Real.exp_neg,
    div_eq_mul_inv, ← Real.exp_neg, neg_mul]

/-- The precise Euler test in Q's scale-Sobolev step, on an actual finite envelope. -/
theorem hasDerivAt_actualFiniteInverseLogPolynomial
    (η : HeckeCharacter K) (F : Finset (NonzeroIdeal K))
    (u : S.integer K) (W : ℝ → ℂ) (t : ℝ)
    (hW : ∀ I ∈ F, DifferentiableAt ℝ W (idealNorm K I * Real.exp (-t))) :
    HasDerivAt (actualFiniteInverseLogPolynomial K S ζ hζ σ η F u W)
      (actualFiniteInverseLogPolynomial K S ζ hζ σ η F u (scaleEulerTest W) t) t := by
  have hn : HasDerivAt (fun x : ℝ => (Real.exp (-x / 2) : ℂ))
      (-(1 / 2 : ℂ) * (Real.exp (-t / 2) : ℂ)) t := by
    convert (((hasDerivAt_id t).neg.div_const 2).exp).ofReal_comp using 1
    all_goals simp
    all_goals ring
  have hi (I : NonzeroIdeal K) (hI : I ∈ F) :
      HasDerivAt (fun x : ℝ =>
        actualInverseIdealCoefficient K S ζ hζ σ η u I *
          W (idealNorm K I * Real.exp (-x)))
        (actualInverseIdealCoefficient K S ζ hζ σ η u I *
          (-(idealNorm K I * Real.exp (-t) : ℝ) : ℂ) *
          deriv W (idealNorm K I * Real.exp (-t))) t := by
    have hx : HasDerivAt (fun x : ℝ => idealNorm K I * Real.exp (-x))
        (-(idealNorm K I * Real.exp (-t))) t := by
      convert (((hasDerivAt_id t).neg.exp).const_mul (idealNorm K I)) using 1 <;>
        simp
    convert ((hW I hI).hasDerivAt.scomp t hx).const_mul
      (actualInverseIdealCoefficient K S ζ hζ σ η u I) using 1
    all_goals simp [Complex.real_smul]
    all_goals ring
  have hsum := HasDerivAt.fun_sum hi
  convert hn.mul hsum using 1
  · rfl
  · simp only [actualFiniteInverseLogPolynomial, scaleEulerTest]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro I hI
    ring

/-- No differentiability premise remains for the concrete W_s family. -/
theorem hasDerivAt_actualFiniteInverseLogPolynomial_mellin
    (η : HeckeCharacter K) (F : Finset (NonzeroIdeal K))
    (u : S.integer K) (s : ℂ) (t : ℝ) :
    HasDerivAt
      (actualFiniteInverseLogPolynomial K S ζ hζ σ η F u (dyadicMellinWeight s))
      (actualFiniteInverseLogPolynomial K S ζ hζ σ η F u
        (scaleEulerTest (dyadicMellinWeight s)) t) t := by
  apply hasDerivAt_actualFiniteInverseLogPolynomial
  intro I _
  apply differentiableAt_dyadicMellinWeight
  exact mul_pos (idealNorm_pos K I) (Real.exp_pos _)

/-- Every positive scale r<=R uses the SAME literal finite support F(R). -/
theorem actualSIntegerInversePolynomial_eq_fixedEnvelope
    (η : HeckeCharacter K) (q : ActualSIntegerOrbit K S) (s : ℂ)
    {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
    actualSIntegerInversePolynomial K S ζ hζ σ η q r s =
      sIntegerSexticInverseIdealPolynomial K S ζ hζ σ η
        (dyadicIdealSupport K R) q.out.val r (dyadicMellinWeight s) := by
  rw [← actualSIntegerInversePolynomial_out]
  unfold sIntegerSexticInverseIdealPolynomial
  congr 1
  apply Finset.sum_subset
  · intro I hI
    exact (mem_dyadicIdealSupport_iff K (hr.le.trans hrR) I).mpr
      (((mem_dyadicIdealSupport_iff K hr.le I).mp hI).trans (by linarith))
  · intro I _ hI
    have hn : 2 * r < idealNorm K I :=
      lt_of_not_ge (fun h => hI ((mem_dyadicIdealSupport_iff K hr.le I).mpr h))
    have hy : 2 ≤ idealNorm K I / r :=
      (le_div_iff₀ hr).mpr (by linarith)
    simp [sIntegerSexticInverseIdealTerm, dyadicMellinWeight_zero_of_ge s hy]

/-- The original quotient polynomial, including its varying finite cutoff,
has the proved actual derivative. The fixed envelope F(2 exp t) is valid
on a neighborhood, so no differentiation of a changing index set occurs. -/
theorem hasDerivAt_actualSIntegerInversePolynomial_exp
    (η : HeckeCharacter K) (q : ActualSIntegerOrbit K S) (s : ℂ) (t : ℝ) :
    HasDerivAt
      (fun x : ℝ => actualSIntegerInversePolynomial K S ζ hζ σ η q (Real.exp x) s)
      (actualFiniteInverseLogPolynomial K S ζ hζ σ η
        (dyadicIdealSupport K (2 * Real.exp t)) q.out.val
        (scaleEulerTest (dyadicMellinWeight s)) t) t := by
  apply (hasDerivAt_actualFiniteInverseLogPolynomial_mellin K S ζ hζ σ η
    (dyadicIdealSupport K (2 * Real.exp t)) q.out.val s t).congr_of_eventuallyEq
  have hwindow : ∀ᶠ x : ℝ in 𝓝 t, Real.exp x < 2 * Real.exp t :=
    Real.continuous_exp.continuousAt.eventually_lt_const (by linarith [Real.exp_pos t])
  filter_upwards [hwindow] with x hx
  rw [actualFiniteInverseLogPolynomial_eq]
  exact actualSIntegerInversePolynomial_eq_fixedEnvelope K S ζ hζ σ η q s
    (Real.exp_pos x) hx.le

/-- The finitely many log factors needed for compact Mellin-parameter Sobolev. -/
def mellinLogTest (m : ℕ) (s : ℂ) (y : ℝ) : ℂ :=
  (-(Real.log y : ℂ)) ^ m * dyadicMellinWeight s y

/-- Six explicit tests cover alpha in {0,1}^3 for log scale, Re s, Im s,
up to complex factors of norm one. No extra arithmetic mask is introduced. -/
def scaleSobolevTest (i : Fin 2) (m : Fin 3) (s : ℂ) : ℝ → ℂ :=
  if i.val = 0 then mellinLogTest m.val s else scaleEulerTest (mellinLogTest m.val s)

/-- Q's finite-test/uniform-scale specialization on the actual rows.
This is an ANALYTIC INPUT, not an unconditional theorem or a consequence
of frozen fixed-W_s MI. K,S,zeta,sigma,omega are fixed first; delta,epsilon
and the compact Mellin parameter set precede eta. Constants and threshold
may depend on the target eta. Source allowed-section calibration is separate.
The unused small scales are included literally; uniform seminorm theory
and the rowwise Sobolev consumer still have to be established. -/
def ActualZeroSlotSobolevMomentInput (ω : HeckeCharacter K) : Prop :=
  ∀ δ ε : ℝ, 0 < δ → δ < 1 → 0 < ε →
    ∀ T : Set ℂ, IsCompact T →
      ∀ η : HeckeCharacter K, η ∈ HeckePacket K ω →
        ∃ C H₀ : ℝ, 0 < C ∧ 1 ≤ H₀ ∧
          ∀ H : ℝ, H₀ ≤ H → ∀ D : ℝ, 0 < D → D ≤ H ^ (1 - δ) →
            ∀ s ∈ T, ∀ i : Fin 2, ∀ m : Fin 3,
              (∑ q : ActualBoundedSIntegerOrbits K S H,
                ‖sIntegerSexticInverseIdealPolynomial K S ζ hζ σ η
                  (dyadicIdealSupport K D) q.val.out.val D
                  (scaleSobolevTest i m s)‖ ^ 2) ≤ C * H ^ (1 + ε)

end HeckeGeneral.Analysis.ActualSIntegerMoments
