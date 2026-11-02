import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.WeightedReflectionMass

/-!
# Exact weights of the ordinary reflected Mellin operator

The coefficient is the existing finite-deletion/restoration coefficient.
Its complex phase is evaluated at the actual ratio between a common child
scale and the reflected scale Q N(D)/(X N(H)).  The square-root factors
give the two mixed ideal-norm exponents exactly; no energy estimate or
row-dependent majorant is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField HeckePort.Moments HeckePort.Moments.ReflectionMass
open scoped Classical BigOperators

variable {K : Type} [Field K] [NumberField K]

/-- The exact real factor left by square-root normalization. -/
theorem reflection_ratio_weight (a b r σ : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    (Real.sqrt (a * b))⁻¹ * (r * b / a) ^ (σ - 1 / 2) =
      r ^ (σ - 1 / 2) * a ^ (-σ) * b ^ (σ - 1) := by
  have hs : (Real.sqrt (a * b))⁻¹ =
      a ^ (-(1 / 2 : ℝ)) * b ^ (-(1 / 2 : ℝ)) := by
    rw [Real.sqrt_mul ha.le, Real.rpow_neg ha.le, Real.rpow_neg hb.le,
      ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, mul_inv_rev]
    ring
  have ht : (r * b / a) ^ (σ - 1 / 2) =
      r ^ (σ - 1 / 2) * b ^ (σ - 1 / 2) * a ^ (-(σ - 1 / 2)) := by
    rw [Real.div_rpow (mul_pos hr hb).le ha.le, Real.mul_rpow hr.le hb.le,
      Real.rpow_neg ha.le, div_eq_mul_inv]
  rw [hs, ht]
  calc
    _ = r ^ (σ - 1 / 2) *
        (a ^ (-(1 / 2 : ℝ)) * a ^ (-(σ - 1 / 2))) *
        (b ^ (-(1 / 2 : ℝ)) * b ^ (σ - 1 / 2)) := by ring
    _ = _ := by
      rw [← Real.rpow_add ha, ← Real.rpow_add hb,
        show -(1 / 2 : ℝ) + -(σ - 1 / 2) = -σ by ring,
        show -(1 / 2 : ℝ) + (σ - 1 / 2) = σ - 1 by ring]

/-- Actual complex Mellin phase, at the actual restored scale.  This
holds on every vertical line; the subsequent summability theorem uses
the closed strip whose two sides are 1/4 and 3/4. -/
theorem reflection_coefficient_phase_norm_le
    {a ai : Ideal (𝓞 K) → ℂ} (ha : IdealCoeff a) (hai : IdealCoeff ai)
    (S : Finset (Ideal (𝓞 K))) (hS : ∀ P ∈ S, Prime P)
    (D : Finset (Ideal (𝓞 K))) (hD : D ∈ S.powerset) (H : SmoothIdeal S)
    (Q X N : ℝ) (hQ : 0 < Q) (hX : 0 < X) (hN : 0 < N) (s : ℂ) :
    ‖coefficient a ai S D H *
        ((N / (Q * (Ideal.absNorm (∏ P ∈ D, P) : ℝ) / (X * inorm H.val)) : ℝ) : ℂ) ^
          (s - ((1 / 2 : ℝ) : ℂ))‖ ≤
      (N * X / Q) ^ (s.re - 1 / 2) *
        (Ideal.absNorm (∏ P ∈ D, P) : ℝ) ^ (-s.re) *
          (inorm H.val) ^ (s.re - 1) := by
  have hDS : ∀ P ∈ D, Prime P := fun P hP => hS P ((Finset.mem_powerset.mp hD) hP)
  have hd := subset_product_norm_pos D hDS
  have hh := inorm_pos H.val
  have hr : 0 < N * X / Q := div_pos (mul_pos hN hX) hQ
  have hratio : N / (Q * (Ideal.absNorm (∏ P ∈ D, P) : ℝ) / (X * inorm H.val)) =
      (N * X / Q) * inorm H.val / (Ideal.absNorm (∏ P ∈ D, P) : ℝ) := by
    field_simp [hQ.ne', hX.ne', hd.ne', hh.ne'] <;> ring
  have hratioPos : 0 < N / (Q * (Ideal.absNorm (∏ P ∈ D, P) : ℝ) / (X * inorm H.val)) :=
    div_pos hN (div_pos (mul_pos hQ hd) (mul_pos hX hh))
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hratioPos,
    Complex.sub_re, Complex.ofReal_re]
  apply (mul_le_mul_of_nonneg_right
    (coefficient_norm_le ha hai S D hDS H)
    (Real.rpow_nonneg hratioPos.le _)).trans_eq
  have hs : weight (∏ P ∈ D, P) * weight H.val.val =
      (Real.sqrt ((Ideal.absNorm (∏ P ∈ D, P) : ℝ) * inorm H.val))⁻¹ := by
    simp only [weight, inorm, Real.sqrt_mul hd.le, mul_inv_rev]
    ring
  rw [hs, hratio]
  exact reflection_ratio_weight _ _ _ s.re hd hh hr

/-- Absolute convergence of every actual restored Mellin coefficient
column, before integration in the common frequency. -/
theorem reflection_coefficient_phase_summable
    {a ai : Ideal (𝓞 K) → ℂ} (ha : IdealCoeff a) (hai : IdealCoeff ai)
    (β : ℝ) (hβ : 0 < β)
    (S : Finset (Ideal (𝓞 K))) (hS : ∀ P ∈ S, Prime P)
    (D : Finset (Ideal (𝓞 K))) (hD : D ∈ S.powerset)
    (Q X N : ℝ) (hQ : 0 < Q) (hX : 0 < X) (hN : 0 < N)
    (s : ℂ) (hlower : β ≤ s.re) (hupper : s.re ≤ 1 - β) :
    Summable (fun H : SmoothIdeal S =>
      ‖coefficient a ai S D H *
        ((N / (Q * (Ideal.absNorm (∏ P ∈ D, P) : ℝ) / (X * inorm H.val)) : ℝ) : ℂ) ^
          (s - ((1 / 2 : ℝ) : ℂ))‖) := by
  have hDS : ∀ P ∈ D, Prime P := fun P hP => hS P ((Finset.mem_powerset.mp hD) hP)
  have hr : 0 ≤ (N * X / Q) ^ (s.re - 1 / 2) :=
    Real.rpow_nonneg (div_pos (mul_pos hN hX) hQ).le _
  apply ((weightedSmoothSummable β hβ S hS).mul_left
    ((N * X / Q) ^ (s.re - 1 / 2) * reflectionPowerWeight β (∏ P ∈ D, P))).of_nonneg_of_le
  · exact fun _ => norm_nonneg _
  · intro H
    apply (reflection_coefficient_phase_norm_le ha hai S hS D hD H
      Q X N hQ hX hN s).trans
    have hw := mixedReflectionWeight_le β s.re hlower hupper
      ⟨∏ P ∈ D, P, subset_product_nonzero D hDS⟩ H.val
    simpa only [inorm, mul_assoc] using mul_le_mul_of_nonneg_left hw hr

/-- One common Euler constant controls the complete actual complex-phase
mass.  It is chosen before prime set, coefficients, row conductor,
physical scale, child scale and vertical frequency. -/
theorem reflection_coefficient_phase_mass_subpower (β ε : ℝ) (hβ : 0 < β) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset (Ideal (𝓞 K)))
      (hS : ∀ P ∈ S, Prime P) (a ai : Ideal (𝓞 K) → ℂ)
      (ha : IdealCoeff a) (hai : IdealCoeff ai)
      (Q X N : ℝ), 0 < Q → 0 < X → 0 < N →
      ∀ s : ℂ, β ≤ s.re → s.re ≤ 1 - β →
        Summable (fun H : SmoothIdeal S => ∑ D ∈ S.powerset,
          ‖coefficient a ai S D H *
            ((N / (Q * (Ideal.absNorm (∏ P ∈ D, P) : ℝ) / (X * inorm H.val)) : ℝ) : ℂ) ^
              (s - ((1 / 2 : ℝ) : ℂ))‖) ∧
        (∑ D ∈ S.powerset, ∑' H : SmoothIdeal S,
          ‖coefficient a ai S D H *
            ((N / (Q * (Ideal.absNorm (∏ P ∈ D, P) : ℝ) / (X * inorm H.val)) : ℝ) : ℂ) ^
              (s - ((1 / 2 : ℝ) : ℂ))‖) ≤
          C * (N * X / Q) ^ (s.re - 1 / 2) *
            (Ideal.absNorm (∏ P ∈ S, P) : ℝ) ^ ε := by
  obtain ⟨C, hC, hbound⟩ := weightedMixedMass_subpower (K := K) β ε hβ hε
  refine ⟨C, hC, ?_⟩
  intro S hS a ai ha hai Q X N hQ hX hN s hlower hupper
  have hr : 0 ≤ (N * X / Q) ^ (s.re - 1 / 2) :=
    Real.rpow_nonneg (div_pos (mul_pos hN hX) hQ).le _
  have hs (D : Finset (Ideal (𝓞 K))) (hD : D ∈ S.powerset) :=
    reflection_coefficient_phase_summable ha hai β hβ S hS D hD Q X N hQ hX hN s hlower hupper
  have hm (D : Finset (Ideal (𝓞 K))) (hD : D ∈ S.powerset) :
      Summable (fun H : SmoothIdeal S =>
        (Ideal.absNorm (∏ P ∈ D, P) : ℝ) ^ (-s.re) * (inorm H.val) ^ (s.re - 1)) := by
    apply ((weightedSmoothSummable β hβ S hS).mul_left
      (reflectionPowerWeight β (∏ P ∈ D, P))).of_nonneg_of_le
    · exact fun _ => mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        (Real.rpow_nonneg (inorm_pos _).le _)
    · intro H
      exact mixedReflectionWeight_le β s.re hlower hupper
        ⟨∏ P ∈ D, P, subset_product_nonzero D
          (fun P hP => hS P ((Finset.mem_powerset.mp hD) hP))⟩ H.val
  refine ⟨summable_sum hs, ?_⟩
  calc
    _ ≤ ∑ D ∈ S.powerset, ∑' H : SmoothIdeal S,
        (N * X / Q) ^ (s.re - 1 / 2) *
          ((Ideal.absNorm (∏ P ∈ D, P) : ℝ) ^ (-s.re) * (inorm H.val) ^ (s.re - 1)) := by
      apply Finset.sum_le_sum
      intro D hD
      apply (hs D hD).tsum_le_tsum
      · intro H
        simpa only [mul_assoc] using reflection_coefficient_phase_norm_le ha hai S hS D hD H
          Q X N hQ hX hN s
      · exact (hm D hD).mul_left _
    _ = (N * X / Q) ^ (s.re - 1 / 2) *
        (∑ D ∈ S.powerset, ∑' H : SmoothIdeal S,
          (Ideal.absNorm (∏ P ∈ D, P) : ℝ) ^ (-s.re) * (inorm H.val) ^ (s.re - 1)) := by
      simp only [tsum_mul_left, ← Finset.mul_sum]
    _ ≤ _ := (mul_le_mul_of_nonneg_left (hbound S hS s.re hlower hupper).2 hr).trans_eq
      (by ring)

end HeckeSkeleton.Moments.EngineInduction
