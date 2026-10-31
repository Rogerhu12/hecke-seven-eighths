import ExpansionDetector.DetectorPower
import HeckeSkeleton.HeckeUniformStripGrowth
import HeckeGeneral.Analysis.IdealMobiusReciprocal

/-! Specialization of the fixed-line detector to the genuine ordinary Hecke
continuation and genuine ideal Moebius coefficients. The conductor exponent
5/8 is obtained by evaluating the supplied fixed-type strip theorem at 1/8.
This module depends on the supplied project in addition to Mathlib. -/
noncomputable section
namespace ExpansionDetector.Hecke
open NumberField IsDedekindDomain AutomorphicForm
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Bridge HeckeGeneral.Analysis
open HeckeSkeleton.ExplicitHeckeFunctionalEquation
open HeckeSkeleton.HeckeUniformStripGrowth
open UniqueFactorizationMonoid
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]

def heightDegree : ℝ := (2 * Fintype.card (InfinitePlace K) : ℕ)

/-- The whole detector strip, including its absolutely convergent right end. -/
theorem exists_actual_detector_strip_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (τ : InfinitePlace K → ℝ) (m : InfinitePlace K → ℤ)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (χ : HeckeCharacter K) (U : ℝ),
      (∀ t : ℝ, χ ≠ heckeNormTwist K t) →
      (fun v => heckeRadialParameter K v χ) = τ → heckeArchWeight K χ = m →
      1 ≤ U → heckeConductorScale K χ ≤ R * U →
      ∀ s : ℂ, 1 / 100 ≤ s.re → s.re ≤ 3 →
        ‖heckeContinuation K χ s‖ ≤ C * U ^ (5 / 8 : ℝ) *
          (2 + |s.im|) ^ heightDegree K := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_fixedType_strip_bound K hcomplex τ m
    (1 / 8) (by norm_num) (by norm_num)
  obtain ⟨E, hE, he⟩ := exists_uniform_rightHalfPlane_bound K (9 / 8) (by norm_num)
  refine ⟨C * R ^ (5 / 8 : ℝ) + E, by positivity, ?_⟩
  intro χ U hχ hτ hm hU hQ s hs hs'
  have hUp : 0 < U := zero_lt_one.trans_le hU
  have hdegree : 0 ≤ heightDegree K := by dsimp [heightDegree]; positivity
  have hheight : 1 ≤ (2 + |s.im|) ^ heightDegree K :=
    Real.one_le_rpow (by linarith [abs_nonneg s.im]) hdegree
  have hUpow : 1 ≤ U ^ (5 / 8 : ℝ) := Real.one_le_rpow hU (by norm_num)
  by_cases hleft : s.re ≤ 9 / 8
  · obtain ⟨ε, Λ, Λd, hQpos, _, _, _, _, _, _, _, _⟩ :=
      exists_completed_functionalEquation_explicitScale_of_nonNorm K χ hχ
    have hx := hb χ hχ hτ hm s ⟨by linarith, by linarith⟩
    norm_num only [show (1 / 2 + 1 / 8 : ℝ) = 5 / 8 by norm_num] at hx
    have hpow : heckeConductorScale K χ ^ (5 / 8 : ℝ) ≤
        R ^ (5 / 8 : ℝ) * U ^ (5 / 8 : ℝ) := by
      calc
        _ ≤ (R * U) ^ (5 / 8 : ℝ) := Real.rpow_le_rpow hQpos.le hQ (by norm_num)
        _ = _ := Real.mul_rpow hR hUp.le
    rw [← Real.rpow_natCast] at hx
    change ‖heckeContinuation K χ s‖ ≤
      C * heckeConductorScale K χ ^ (5 / 8 : ℝ) * (2 + |s.im|) ^ heightDegree K at hx
    calc
      _ ≤ C * heckeConductorScale K χ ^ (5 / 8 : ℝ) * (2 + |s.im|) ^ heightDegree K := hx
      _ ≤ C * (R ^ (5 / 8 : ℝ) * U ^ (5 / 8 : ℝ)) * (2 + |s.im|) ^ heightDegree K := by gcongr
      _ ≤ _ := by
        nlinarith [mul_nonneg hE.le (Real.rpow_nonneg hUp.le (5 / 8)),
          mul_nonneg (mul_nonneg hE.le (Real.rpow_nonneg hUp.le (5 / 8)))
            (Real.rpow_nonneg (by positivity : 0 ≤ 2 + |s.im|) (heightDegree K))]
  · have hx := he χ s (lt_of_not_ge hleft).le
    have hfactor : 1 ≤ U ^ (5 / 8 : ℝ) * (2 + |s.im|) ^ heightDegree K :=
      one_le_mul_of_one_le_of_one_le hUpow hheight
    calc
      _ ≤ E := hx
      _ ≤ E * (U ^ (5 / 8 : ℝ) * (2 + |s.im|) ^ heightDegree K) :=
        le_mul_of_one_le_right hE.le hfactor
      _ ≤ _ := by
        have hp : 0 ≤ C * R ^ (5 / 8 : ℝ) := by positivity
        nlinarith [mul_nonneg hp
          (mul_nonneg (Real.rpow_nonneg hUp.le (5 / 8))
            (Real.rpow_nonneg (by positivity : 0 ≤ 2 + |s.im|) (heightDegree K)))]

def inverseCoefficient (χ : HeckeCharacter K) (V : ℝ → ℂ)
    (D : ℝ) (I : NonzeroIdeal K) : ℂ :=
  (moebius I.val : ℂ) * heckeIdealCoefficient K χ I * V (idealNorm K I / D)

lemma inverseCoefficient_norm (χ : HeckeCharacter K) (V : ℝ → ℂ)
    (hV : ∀ x : ℝ, ‖V x‖ ≤ 1) (D : ℝ) (I : NonzeroIdeal K) :
    ‖inverseCoefficient K χ V D I‖ ≤ 1 := by
  unfold inverseCoefficient
  rw [norm_mul, norm_mul]
  calc
    _ ≤ 1 * 1 * 1 := by
      gcongr
      · exact IdealMobiusReciprocal.norm_moebius_le_one K I
      · exact norm_heckeIdealCoefficient_le_one K χ I
      · exact hV _
    _ = 1 := by ring

/-- A genuine family-uniform zero-to-small-integral theorem. The support S
may be any finite subset below 2D; the later exact convolution uses the full
cutoff support. The theorem assumes neither a detector witness nor a spike. -/
theorem exists_actual_gamma_detector_bound
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (τ : InfinitePlace K → ℝ) (m : InfinitePlace K → ℤ)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (χ : HeckeCharacter K) (U D : ℝ),
      (∀ t : ℝ, χ ≠ heckeNormTwist K t) →
      (fun v => heckeRadialParameter K v χ) = τ → heckeArchWeight K χ = m →
      2 ≤ U → 0 ≤ D → D ≤ U ^ (3 / 2 : ℝ) →
      heckeConductorScale K χ ≤ R * U →
      ∀ (V : ℝ → ℂ), (∀ x, ‖V x‖ ≤ 1) →
      ∀ (S : Finset (NonzeroIdeal K)), (∀ I ∈ S, idealNorm K I ≤ 2 * D) →
      ∀ ρ : ℂ, 51 / 100 ≤ ρ.re → ρ.re ≤ 1 → heckeContinuation K χ ρ = 0 →
      ‖ExpansionDetector.Analytic.gammaDetector (heckeContinuation K χ)
        (ExpansionDetector.Analytic.dirichletPolynomial S (inverseCoefficient K χ V D) (idealNorm K))
        ρ (U ^ 20)‖ ≤ C * U ^ (-51 / 8 : ℝ) * (2 + |ρ.im|) ^ heightDegree K := by
  obtain ⟨CL, hCL, hLbound⟩ := exists_actual_detector_strip_bound K hcomplex τ m R hR
  have hA : 0 ≤ heightDegree K := by dsimp [heightDegree]; positivity
  obtain ⟨G, hG, hGbound⟩ := ExpansionDetector.Analytic.gammaDetector_power_bound (heightDegree K) hA
  let CZ : ℝ := 1 + ∑' I : NonzeroIdeal K, idealNorm K I ^ (-2 : ℝ)
  have hCZ : 0 < CZ := by dsimp [CZ]; positivity
  have hzeta := summable_nonzeroIdeal_norm_rpow K (σ := 2) (by norm_num)
  refine ⟨4 * G * CL * CZ, by positivity, ?_⟩
  intro χ U D hχ hτ hm hU hD hDU hQ V hV S hS ρ hβ hβ' hz
  have hsum : (∑ I ∈ S, idealNorm K I ^ (-2 : ℝ)) ≤ CZ := by
    apply (hzeta.sum_le_tsum S (fun I _ => Real.rpow_nonneg (idealNorm_pos K I).le _)).trans
    dsimp [CZ]
    linarith
  have h := hGbound S (inverseCoefficient K χ V D) (idealNorm K)
    (heckeContinuation K χ) ρ U D CL CZ (5 / 8) hU hD hDU hCL.le hCZ.le
    (differentiable_heckeContinuation_of_nonNorm K χ hχ) hz hβ hβ'
    (fun I hI => ⟨one_le_idealNorm K I, hS I hI⟩)
    (fun I _ => inverseCoefficient_norm K χ V hV D I) hsum
    (hLbound χ U hχ hτ hm (by linarith) hQ)
  norm_num only [show (5 / 8 - 7 : ℝ) = -51 / 8 by norm_num] at h
  exact h

end ExpansionDetector.Hecke
