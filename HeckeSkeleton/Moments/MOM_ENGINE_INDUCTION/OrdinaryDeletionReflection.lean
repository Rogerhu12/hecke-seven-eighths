import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.OrdinaryReflectionDecay
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.MaskDeletion
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.ProfileSupremum

/-!
# The actual ordinary reflection consumed by finite Euler deletion

The port's normalized ideal polynomial is identified exactly with the
proved Mellin-reflected polynomial, using the equivalence of the two
nonzero-ideal representations.  The genuine functional equation selects
one unit phase before all tests and scales.  Square-root normalization
then cancels the conductor coefficient exactly, giving the `hreflect`
input of the existing finite-deletion/restoration theorem by proof.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField MeasureTheory Set Filter
open HeckeGeneral.Analysis HeckeGeneral.Characters HeckeGeneral.Bridge
open HeckeGeneral.ThetaSkeleton.Global HeckeSkeleton.ThetaKernel
open HeckeSkeleton.ExplicitHeckeFunctionalEquation HeckeSkeleton.HeckeGammaReciprocal
open HeckeSkeleton.HeckeUniformStripGrowth
open scoped BigOperators Classical Topology

variable (K : Type) [Field K] [NumberField K]

/-- This is only a change between equal ideal representatives, retaining
actual Hecke coefficients, actual norms and square-root normalization. -/
theorem plainPoly_hecke_eq_nonzeroSum (χ : HeckeCharacter K) (F : ℝ → ℂ) (X : ℝ) :
    HeckePort.Moments.plainPoly (idealCoefficient (primeCoefficient K χ)) F X =
      (Real.sqrt X : ℂ)⁻¹ * ∑' I : NonzeroIdeal K,
        heckeIdealCoefficient K χ I * F (idealNorm K I / X) := by
  unfold HeckePort.Moments.plainPoly
  congr 1
  symm
  simpa only [nonzeroIdealDeletionEquiv, HeckePort.Moments.inorm,
    heckeIdealCoefficient, nonzeroIdealCoefficient, idealNorm] using
    (nonzeroIdealDeletionEquiv (K := K)).tsum_eq
      (fun I : HeckePort.Moments.NI K =>
        idealCoefficient (primeCoefficient K χ) I.val * F (HeckePort.Moments.inorm I / X))

/-- Compact support identifies the normalized port polynomial with the
actual finite annular Hecke polynomial used in Mellin inversion. -/
theorem plainPoly_hecke_eq_annular (χ : HeckeCharacter K) (V : SmoothAnnularTest)
    {X : ℝ} (hX : 0 < X) :
    HeckePort.Moments.plainPoly (idealCoefficient (primeCoefficient K χ)) V.toFun X =
      (Real.sqrt X : ℂ)⁻¹ * annularIdealSum K (heckeIdealCoefficient K χ) V X := by
  rw [plainPoly_hecke_eq_nonzeroSum, annularIdealSum_eq_tsum K _ V hX]

private theorem deletion_conductor_reflection_cpow {X Q : ℝ} (hX : 0 < X) (hQ : 0 < Q)
    (s : ℂ) :
    (X : ℂ) ^ s / (Q : ℂ) ^ (s - 1 / 2) =
      ((X : ℂ) / (Q : ℂ) ^ (1 / 2 : ℂ)) * ((Q / X : ℝ) : ℂ) ^ (1 - s) := by
  have hratio := div_pos hQ hX
  have hc (x : ℝ) (hx : 0 < x) (z : ℂ) :
      (x : ℂ) ^ z = Complex.exp ((Real.log x : ℂ) * z) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
      ← Complex.ofReal_log hx.le]
  have hxexp : Complex.exp (Real.log X : ℂ) = (X : ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_log hX]
  rw [hc X hX s, hc Q hQ (s - 1 / 2), hc Q hQ (1 / 2), hc (Q / X) hratio (1 - s),
    Real.log_div hQ.ne' hX.ne', Complex.ofReal_sub]
  calc
    _ = Complex.exp ((Real.log X : ℂ) * s - (Real.log Q : ℂ) * (s - 1 / 2)) :=
      (Complex.exp_sub _ _).symm
    _ = Complex.exp ((Real.log X : ℂ) - (Real.log Q : ℂ) * (1 / 2)) *
        Complex.exp (((Real.log Q : ℂ) - (Real.log X : ℂ)) * (1 - s)) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    _ = _ := by rw [Complex.exp_sub, hxexp]

private theorem annularHeckeSum_reflection_with_phase
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (χ : HeckeCharacter K) (hχ : ∀ t : ℝ, χ ≠ heckeNormTwist K t)
    (ε : ℂ) (hQ : 0 < heckeConductorScale K χ)
    (hFE : ∀ s : ℂ, s.re < 1 →
      heckeContinuation K χ s =
        ((canonicalHeckeGammaProfile K χ s)⁻¹ *
          canonicalHeckeGammaProfile K χ⁻¹ (1 - s) * heckeContinuation K χ⁻¹ (1 - s)) /
            (ε * (heckeConductorScale K χ : ℂ) ^ (s - 1 / 2)))
    (V : SmoothAnnularTest) {X δ : ℝ} (hX : 0 < X)
    (hδ : 0 < δ) (hδsmall : δ < 1 / 4) :
    annularIdealSum K (heckeIdealCoefficient K χ) V X =
        (ε⁻¹ * (X : ℂ) / (heckeConductorScale K χ : ℂ) ^ (1 / 2 : ℂ)) *
          ∑' I, heckeIdealCoefficient K χ⁻¹ I * ordinaryReflectedProfile K χ V δ
            (idealNorm K I / (heckeConductorScale K χ / X)) := by
  let A : ℂ := ε⁻¹ * (X : ℂ) / (heckeConductorScale K χ : ℂ) ^ (1 / 2 : ℂ)
  have hpoint (t : ℝ) :
      annularHeckeContour K χ V X (idealVerticalPoint (-δ) (-t)) =
        A * ((ordinaryReflectionKernel K χ V δ t *
          ((heckeConductorScale K χ / X : ℝ) : ℂ) ^ idealVerticalPoint (1 + δ) t) *
            heckeLSeries K χ⁻¹ (idealVerticalPoint (1 + δ) t)) := by
    let s := 1 - idealVerticalPoint (1 + δ) t
    have hs : idealVerticalPoint (-δ) (-t) = s := by
      dsimp [s, idealVerticalPoint]
      push_cast
      ring
    have hsre : s.re < 1 := by simp [s, idealVerticalPoint]; linarith
    have hdual : 1 - s = idealVerticalPoint (1 + δ) t := by dsimp [s]; ring
    rw [hs, annularHeckeContour, hFE s hsre, hdual,
      heckeContinuation_eq_series K χ⁻¹ (by simp only [idealVerticalPoint_re]; linarith)]
    have hp := deletion_conductor_reflection_cpow hX hQ s
    rw [hdual] at hp
    calc
      _ = ε⁻¹ * ((X : ℂ) ^ s / (heckeConductorScale K χ : ℂ) ^ (s - 1 / 2)) *
          (mellin V.toFun s * ((canonicalHeckeGammaProfile K χ s)⁻¹ *
            canonicalHeckeGammaProfile K χ⁻¹ (idealVerticalPoint (1 + δ) t))) *
              heckeLSeries K χ⁻¹ (idealVerticalPoint (1 + δ) t) := by
        simp only [div_eq_mul_inv, mul_inv]
        ring
      _ = _ := by
        rw [hp]
        dsimp [A, ordinaryReflectionKernel]
        rw [show 1 - (1 - idealVerticalPoint (1 + δ) t) =
          idealVerticalPoint (1 + δ) t by ring]
        dsimp [s]
        ring
  calc
    _ = (2 * (Real.pi : ℂ))⁻¹ *
        ∫ t : ℝ, annularHeckeContour K χ V X (idealVerticalPoint (-δ) t) :=
      annularHeckeSum_shift K hcomplex χ hχ V hX hδ hδsmall
    _ = (2 * (Real.pi : ℂ))⁻¹ *
        ∫ t : ℝ, annularHeckeContour K χ V X (idealVerticalPoint (-δ) (-t)) := by
      congr 1
      exact (integral_neg_eq_self _ volume).symm
    _ = A * ((2 * (Real.pi : ℂ))⁻¹ *
        ∫ t : ℝ, (ordinaryReflectionKernel K χ V δ t *
          ((heckeConductorScale K χ / X : ℝ) : ℂ) ^ idealVerticalPoint (1 + δ) t) *
            heckeLSeries K χ⁻¹ (idealVerticalPoint (1 + δ) t)) := by
      simp_rw [hpoint]
      rw [integral_const_mul]
      ring
    _ = _ := by
      rw [ordinaryReflectedProfile_sum K hcomplex χ V hδ hδsmall (div_pos hQ hX)]


/-- One phase is selected from the genuine functional equation before
all tests and all positive scales.  The normalized conductor coefficient
cancels exactly, so this is the actual `hreflect` of finite deletion. -/
theorem plainPoly_ordinary_reflection_uniform
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (χ : HeckeCharacter K) (hχ : ∀ t : ℝ, χ ≠ heckeNormTwist K t) :
    ∃ G : ℂ, ‖G‖ = 1 ∧ 0 < heckeConductorScale K χ ∧
      ∀ (V : SmoothAnnularTest) (δ : ℝ), 0 < δ → δ < 1 / 4 →
      ∀ X : ℝ, 0 < X →
        HeckePort.Moments.plainPoly (idealCoefficient (primeCoefficient K χ)) V.toFun X =
          G * HeckePort.Moments.plainPoly (idealCoefficient (primeCoefficient K χ⁻¹))
            (ordinaryReflectedProfile K χ V δ) (heckeConductorScale K χ / X) := by
  obtain ⟨ε, hε, hQ, hFE⟩ := exists_uncompleted_functionalEquation_left_of_one K χ hχ
  refine ⟨ε⁻¹, by rw [norm_inv, hε, inv_one], hQ, ?_⟩
  intro V δ hδ hδsmall X hX
  have hrootX : Real.sqrt X ≠ 0 := (Real.sqrt_pos.mpr hX).ne'
  have hrootQ : Real.sqrt (heckeConductorScale K χ) ≠ 0 := (Real.sqrt_pos.mpr hQ).ne'
  have hQpower : (heckeConductorScale K χ : ℂ) ^ (1 / 2 : ℂ) =
      (Real.sqrt (heckeConductorScale K χ) : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hQ.le]
    norm_num
  have hscaleR : (Real.sqrt X)⁻¹ *
      (X / Real.sqrt (heckeConductorScale K χ)) =
        (Real.sqrt (heckeConductorScale K χ / X))⁻¹ := by
    rw [Real.sqrt_div hQ.le]
    field_simp [hrootX, hrootQ]
    nlinarith [Real.sq_sqrt hX.le]
  have hscale : (Real.sqrt X : ℂ)⁻¹ *
      ((X : ℂ) / (heckeConductorScale K χ : ℂ) ^ (1 / 2 : ℂ)) =
        (Real.sqrt (heckeConductorScale K χ / X) : ℂ)⁻¹ := by
    rw [hQpower]
    simpa only [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_div] using
      congrArg (fun x : ℝ => (x : ℂ)) hscaleR
  rw [plainPoly_hecke_eq_annular K χ V hX,
    annularHeckeSum_reflection_with_phase K hcomplex χ hχ ε hQ hFE V hX hδ hδsmall,
    plainPoly_hecke_eq_nonzeroSum]
  calc
    _ = ε⁻¹ * ((Real.sqrt X : ℂ)⁻¹ *
        ((X : ℂ) / (heckeConductorScale K χ : ℂ) ^ (1 / 2 : ℂ))) *
          ∑' I, heckeIdealCoefficient K χ⁻¹ I * ordinaryReflectedProfile K χ V δ
            (idealNorm K I / (heckeConductorScale K χ / X)) := by ring
    _ = _ := by rw [hscale]; ring

/-- Every actual compact smooth annular test has the decay hypothesis
of the arithmetic finite-deletion formula, by the proved Euler C0 bound. -/
theorem smoothAnnular_decayTwo (V : SmoothAnnularTest) :
    HeckePort.Moments.DecayTwo V.toFun := by
  let S : ℝ := testSeminorm V.toFun 1 0
  have hS : 0 ≤ S := (norm_nonneg (V.toFun 0)).trans
    (smoothAnnular_norm_le_testSeminorm V 1 le_rfl 0)
  refine ⟨V.upper ^ 2 * S, mul_nonneg (sq_nonneg _) hS, ?_⟩
  intro x hx
  by_cases hz : V.toFun x = 0
  · simp only [hz, norm_zero, mul_zero]
    exact mul_nonneg (sq_nonneg _) hS
  · exact mul_le_mul (pow_le_pow_left₀ hx.le (V.support hz).2 2)
      (smoothAnnular_norm_le_testSeminorm V 1 le_rfl x)
      (norm_nonneg _) (sq_nonneg _)

/-- The genuine reflected profile has the actual global decay-two
property required for restoration of the same deleted primes. -/
theorem ordinaryReflectedProfile_decayTwo
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (χ : HeckeCharacter K) (V : SmoothAnnularTest) {δ : ℝ}
    (hδ : 0 < δ) (hδsmall : δ < 1 / 4) :
    HeckePort.Moments.DecayTwo (ordinaryReflectedProfile K χ V δ) := by
  obtain ⟨J, C, hC, hbound⟩ := ordinaryReflectedProfile_decay_seminorm K hcomplex χ
    hδ (A := 1) (by linarith)
  have hS : 0 ≤ testSeminorm V.toFun J 1 :=
    (Iint_nonneg V 0 (-1 / 4)).trans (Iint_left_le V 0 J (Nat.zero_le _) 1)
  refine ⟨C * testSeminorm V.toFun J 1, mul_nonneg hC hS, ?_⟩
  intro y hy
  have hp : y ^ 2 * y ^ (-(1 + (1 : ℝ))) = 1 := by
    rw [show -(1 + (1 : ℝ)) = -(2 : ℝ) by norm_num,
      Real.rpow_neg hy.le, Real.rpow_two, mul_inv_cancel₀ (pow_ne_zero _ hy.ne')]
  calc
    _ ≤ y ^ 2 * (C * testSeminorm V.toFun J 1 * y ^ (-(1 + (1 : ℝ)))) :=
      mul_le_mul_of_nonneg_left (hbound V y hy) (sq_nonneg _)
    _ = (C * testSeminorm V.toFun J 1) * (y ^ 2 * y ^ (-(1 + (1 : ℝ)))) := by ring
    _ = _ := by rw [hp, mul_one]

/-- The genuine ordinary functional equation now closes the analytic
hypothesis in the proved finite-deletion and infinite-restoration identity.
Both source and dual retain the same literal deleted prime set. -/
theorem deletedHeckePlainPoly_ordinary_reflection
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (χ : HeckeCharacter K) (hχ : ∀ t : ℝ, χ ≠ heckeNormTwist K t)
    (S : Finset (Ideal (𝓞 K))) (hS : ∀ P ∈ S, Prime P)
    (V : SmoothAnnularTest) {δ : ℝ} (hδ : 0 < δ) (hδsmall : δ < 1 / 4) :
    ∃ G : ℂ, ‖G‖ = 1 ∧ ∀ X : ℝ, 0 < X →
      (∀ D ∈ S.powerset, Summable (HeckePort.Moments.reflectedTerm
        (idealCoefficient (primeCoefficient K χ))
        (idealCoefficient (primeCoefficient K χ⁻¹)) S
        (ordinaryReflectedProfile K χ V δ) X (heckeConductorScale K χ) D)) ∧
      HeckePort.Moments.plainPoly
        (HeckePort.Moments.excl S (idealCoefficient (primeCoefficient K χ))) V.toFun X =
        G * ∑ D ∈ S.powerset, ∑' H : HeckePort.Moments.SmoothIdeal S,
          HeckePort.Moments.reflectedTerm (idealCoefficient (primeCoefficient K χ))
            (idealCoefficient (primeCoefficient K χ⁻¹)) S
            (ordinaryReflectedProfile K χ V δ) X (heckeConductorScale K χ) D H := by
  obtain ⟨G, hG, hQ, hreflect⟩ := plainPoly_ordinary_reflection_uniform K hcomplex χ hχ
  refine ⟨G, hG, ?_⟩
  intro X hX
  exact HeckePort.Moments.deletion_reflection (heckeIdealCoeff_for_deletion χ⁻¹)
    S (heckeIdealCoeff_for_deletion χ) hS V.toFun (ordinaryReflectedProfile K χ V δ)
    (smoothAnnular_decayTwo V) (ordinaryReflectedProfile_decayTwo K hcomplex χ V hδ hδsmall)
    G (heckeConductorScale K χ) hQ (hreflect V δ hδ hδsmall) X hX

end HeckeSkeleton.Moments.EngineInduction
