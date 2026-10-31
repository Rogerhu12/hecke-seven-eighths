import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.NormalizedReflectionDensity

/-!
# A moving profile budget with constants chosen before height

The original literal root need not belong to a unit profile ball.  A
family budget P at least one is included in every child normalization.
The required source Euler order and all analytic constants are chosen
before P.  After the exact child amplitude is paid, the density has the
explicit budget power P^(cap+3): cap+2 from the actual child amplitude
and one from the original profile seminorm.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField MeasureTheory Set Filter
open HeckeGeneral.Analysis HeckeGeneral.Characters
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global HeckeSkeleton.ThetaKernel
open HeckeSkeleton.Moments.UniformAmplify HeckePort.Moments
open scoped Classical BigOperators

theorem ordinaryProfileEnvelope_scale (P E0 : ℝ) (J : ℕ) (t : ℝ) :
    ordinaryProfileEnvelope (P * E0) J t = P * ordinaryProfileEnvelope E0 J t := by
  simp only [ordinaryProfileEnvelope, mul_assoc]

variable {K : Type} [Field K] [NumberField K]
variable {omegaCharacter psiCharacter : HeckeCharacter K}

/-- The envelope constant is selected before the moving profile budget,
the actual node and the common Fourier frequency. -/
theorem exists_normalizedOrdinaryPowerChild_budget_control (J : ℕ) (A : ℝ) :
    ∃ E0 : ℝ, ∃ hE0 : 1 ≤ E0,
      ∀ (P : ℝ) (hP : 1 ≤ P),
      ∀ (d : MomentData K omegaCharacter psiCharacter) (first : Bool)
      (sigma frequency a b : ℝ),
      ModelProfileControl d J A P 0 a b 0 → a ≤ 1 / 2 → 2 ≤ b →
      sigma ∈ Icc (1 / 4) (3 / 4) →
      ModelProfileControl
        (normalizedOrdinaryPowerChild d first sigma frequency (P * E0)
          (one_le_mul_of_one_le_of_one_le hP hE0) J) J A 1 0 a b 0 := by
  obtain ⟨C, hC, hwindow⟩ := ordinaryPowerWindow_sliceControl J A
  let E0 := max 1 C
  have hE0 : 1 ≤ E0 := le_max_left _ _
  refine ⟨E0, hE0, ?_⟩
  intro P hP d first sigma frequency a b hparent ha hb hsigma
  have hP0 : 0 ≤ P := zero_le_one.trans hP
  have hE00 : 0 ≤ E0 := zero_le_one.trans hE0
  have hPE : 1 ≤ P * E0 := one_le_mul_of_one_le_of_one_le hP hE0
  have henv : P ≤ ordinaryProfileEnvelope (P * E0) J frequency := by
    rw [ordinaryProfileEnvelope_scale]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (one_le_ordinaryProfileEnvelope hE0 J frequency) hP0
  have raise {f : ℝ → ℂ} (h : SliceControl J A P 0 a b 0 f) :
      SliceControl J A (P * E0) (J : ℝ) a b |frequency| f := by
    refine ⟨h.1, h.2.1, ?_⟩
    have hi : testSeminorm f J A ≤ P := by
      simpa only [Real.rpow_zero, mul_one] using h.2.2
    simpa only [ordinaryProfileEnvelope, Real.rpow_natCast] using hi.trans henv
  have hnew : SliceControl J A (P * E0) (J : ℝ) a b |frequency|
      (ordinaryPowerWindow sigma frequency) := by
    have h := hwindow sigma hsigma frequency
    have hCP : C ≤ P * E0 := (le_max_right 1 C).trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hP hE00)
    refine ⟨h.1, fun y hy => ⟨ha.trans (h.2.1 y hy).1, (h.2.1 y hy).2.trans hb⟩,
      h.2.2.trans ?_⟩
    exact mul_le_mul_of_nonneg_right hCP (Real.rpow_nonneg (by positivity) _)
  have hc : ModelProfileControl (ordinaryPowerChild K d first sigma frequency)
      J A (P * E0) (J : ℝ) a b |frequency| := by
    intro q
    cases q with
    | inverse u => exact raise (modelProfileControl_inverse hparent u)
    | plain₁ u =>
      cases first with
      | false => exact raise (modelProfileControl_plain₁ hparent u)
      | true =>
        simpa [modelProfile, ordinaryPowerChild, IdealTest.freezeTwist,
          ordinaryPowerWindowIdealTest, profilePower_zero] using hnew
    | plain₂ u =>
      cases first with
      | false =>
        simpa [modelProfile, ordinaryPowerChild, IdealTest.freezeTwist,
          ordinaryPowerWindowIdealTest, profilePower_zero] using hnew
      | true => exact raise (modelProfileControl_plain₂ hparent u)
    | prime j => exact raise (modelProfileControl_prime hparent j)
  exact normalizedMomentProfiles_unit_control hc
    (zero_lt_one.trans_le (one_le_ordinaryProfileEnvelope hPE J frequency))
      (by simp only [ordinaryProfileEnvelope, Real.rpow_natCast])

variable (K)

/-- The added family budget has its literal amplitude degree; no
frequency derivative or final energy estimate is an input. -/
theorem normalizedOrdinaryReflectionDensity_scale (P E0 : ℝ) (J slots : ℕ)
    (χ : HeckeCharacter K) (V : SmoothAnnularTest)
    (a ai : Ideal (𝓞 K) → ℂ) (S : Finset (Ideal (𝓞 K)))
    (Q X N sigma t : ℝ) :
    normalizedOrdinaryReflectionDensity K (P * E0) J slots χ V a ai S Q X N sigma t =
      ((P ^ (slots + 2) : ℝ) : ℂ) *
        normalizedOrdinaryReflectionDensity K E0 J slots χ V a ai S Q X N sigma t := by
  simp only [normalizedOrdinaryReflectionDensity, ordinaryProfileEnvelope_scale,
    mul_pow, Complex.ofReal_mul, mul_assoc]

/-- The Euler order and constant precede every P at least one.  This
keeps polynomial height growth visible when P = Cp*(1+T)^Hp, while
preserving the original literal root and normalizing every actual child. -/
theorem normalizedOrdinaryReflectionDensity_budget_uniform
    (hcomplex : ∀ v : InfinitePlace K, v.IsComplex)
    (background : HeckeCharacter K) {δ A B ε E0 : ℝ}
    (hδ : 0 < δ) (hδA : δ ≤ A) (hB : 0 < B) (hε : 0 < ε)
    (hE0 : 1 ≤ E0) (J cap : ℕ) :
    ∃ L : ℕ, J ≤ L ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ (P : ℝ), 1 ≤ P → ∀ (deletionBound : ℝ), 0 ≤ deletionBound →
      ∀ (row : HeckeCharacter K), FiniteOrder row →
      ∀ (V : SmoothAnnularTest), V.upper ≤ B → testSeminorm V.toFun L A ≤ P →
      ∀ (a ai : Ideal (𝓞 K) → ℂ), IdealCoeff a → IdealCoeff ai →
      ∀ (S : Finset (Ideal (𝓞 K))) (hS : ∀ Q ∈ S, Prime Q),
      (Ideal.absNorm (∏ Q ∈ S, Q) : ℝ) ^ ε ≤ deletionBound →
      ∀ (slots : ℕ), slots ≤ cap → ∀ (Q X N : ℝ), 0 < Q → 0 < X → 0 < N →
      let density := normalizedOrdinaryReflectionDensity K (P * E0) J slots
        (background * row) V a ai S Q X N (ordinaryReflectionLine (N * X / Q))
      (∀ t, ‖density t‖ ≤ ordinaryReflectionEnvelope C (P ^ (cap + 3)) deletionBound t) ∧
      Integrable density ∧
      (∫ t : ℝ, ‖density t‖) ≤
        C * P ^ (cap + 3) * deletionBound * ∫ t : ℝ, (1 + |t|) ^ (-(2 : ℝ)) := by
  obtain ⟨L, hJL, C, hC, hbound⟩ := normalizedOrdinaryReflectionDensity_L1_uniform
    K hcomplex background hδ hδA hB hε hE0 J cap
  refine ⟨L, hJL, C, hC, ?_⟩
  intro P hP deletionBound hdeletion row hrow V hupper hV a ai ha hai S hS hdeleted
    slots hslots Q X N hQ hX hN
  dsimp only
  have hP0 : 0 ≤ P := zero_le_one.trans hP
  obtain ⟨hpoint, hint, hmass⟩ := hbound P deletionBound hP0 hdeletion row hrow V hupper hV
    a ai ha hai S hS hdeleted slots hslots Q X N hQ hX hN
  have hnormalized (t : ℝ) :
      ‖normalizedOrdinaryReflectionDensity K (P * E0) J slots (background * row) V a ai S
        Q X N (ordinaryReflectionLine (N * X / Q)) t‖ ≤
          ordinaryReflectionEnvelope C (P ^ (cap + 3)) deletionBound t := by
    rw [normalizedOrdinaryReflectionDensity_scale, norm_mul,
      Complex.norm_of_nonneg (pow_nonneg hP0 _)]
    have hp : P ^ (slots + 2) ≤ P ^ (cap + 2) := pow_le_pow_right₀ hP (by omega)
    calc
      _ ≤ P ^ (cap + 2) *
          ordinaryReflectionEnvelope C P deletionBound t :=
        mul_le_mul hp (hpoint t) (norm_nonneg _) (pow_nonneg hP0 _)
      _ = ordinaryReflectionEnvelope C (P ^ (cap + 3)) deletionBound t := by
        rw [show cap + 3 = (cap + 2) + 1 by omega, pow_succ]
        unfold ordinaryReflectionEnvelope
        ring
  have hi : Integrable (normalizedOrdinaryReflectionDensity K (P * E0) J slots
      (background * row) V a ai S Q X N (ordinaryReflectionLine (N * X / Q))) :=
    (hint.const_mul ((P ^ (slots + 2) : ℝ) : ℂ)).congr
      (Eventually.of_forall (fun t =>
        (normalizedOrdinaryReflectionDensity_scale K P E0 J slots
          (background * row) V a ai S Q X N (ordinaryReflectionLine (N * X / Q)) t).symm))
  refine ⟨hnormalized, hi, ?_⟩
  have hg := ordinaryReflectionEnvelope_data hC (pow_nonneg hP0 (cap + 3)) hdeletion
  rw [← hg.2.2.2]
  exact integral_mono hi.norm hg.2.2.1 hnormalized

/-- The moving height costs one fixed exponent.  Squaring the L1 mass
in the common positive row kernel doubles this displayed degree. -/
theorem ordinaryReflectionEnvelope_height (C Cp X H deletionBound frequency : ℝ)
    (cap : ℕ) (hX : 0 ≤ X) :
    ordinaryReflectionEnvelope C ((Cp * X ^ H) ^ (cap + 3)) deletionBound frequency =
      ordinaryReflectionEnvelope (C * Cp ^ (cap + 3)) 1 deletionBound frequency *
        X ^ (H * (cap + 3 : ℕ)) := by
  have hpow : (X ^ H) ^ (cap + 3) = X ^ (H * (cap + 3 : ℕ)) := by
    rw [← Real.rpow_natCast (X ^ H) (cap + 3), ← Real.rpow_mul hX]
  rw [mul_pow, hpow]
  unfold ordinaryReflectionEnvelope
  ring

end HeckeSkeleton.Moments.EngineInduction
