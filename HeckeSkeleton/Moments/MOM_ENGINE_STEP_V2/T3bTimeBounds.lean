import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3bSources

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The actual exceptional time in the two fixed Fourier variables

Each original first sign has norm one. The second orientation negates
the Fourier vector and changes the first sign, so both original times
are bounded by the same sum of the two coordinate norms. Their powers
therefore have exactly the product form consumed by the fixed kernels.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep
open NumberField HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Global

variable {K : Type} [Field K] [NumberField K]

namespace T3b

theorem norm_time_neg (sign : ℝ) (ξ : EngineParameter) :
    ‖time sign (-ξ)‖ = ‖time sign ξ‖ := by
  have he : time sign (-ξ) = -time sign ξ := by
    simp only [time, inner_neg_left]
    ring
  rw [he, norm_neg]

theorem norm_time_pair_le (sign : ℝ) (hsign : ‖sign‖ = 1) (z : ℝ × ℝ) :
    ‖time sign (WithLp.toLp 2 z)‖ ≤ 2 * Real.pi * (‖z.1‖ + ‖z.2‖) := by
  have hπ : 0 ≤ 2 * Real.pi := mul_nonneg (by norm_num) Real.pi_pos.le
  have hi : ‖inner ℝ (WithLp.toLp 2 z) (CanonicalLiteralLocations.direction sign)‖ ≤
      ‖z.1‖ + ‖z.2‖ := by
    simp only [CanonicalLiteralLocations.direction, WithLp.prod_inner_apply,
      WithLp.ofLp_toLp]
    calc
      _ ≤ ‖inner ℝ z.1 sign‖ + ‖inner ℝ z.2 (1 : ℝ)‖ := norm_add_le _ _
      _ = _ := by simp only [Real.inner_apply, norm_mul, hsign, norm_one, one_mul, mul_one]
  calc
    _ = (2 * Real.pi) *
        ‖inner ℝ (WithLp.toLp 2 z) (CanonicalLiteralLocations.direction sign)‖ := by
      simp only [time, norm_neg, norm_mul, Real.norm_eq_abs, abs_of_nonneg hπ]
    _ ≤ _ := mul_le_mul_of_nonneg_left hi hπ

theorem one_add_scaled_sum_le_product (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    1 + 2 * Real.pi * (a + b) ≤ (1 + 2 * Real.pi) * (1 + a) * (1 + b) := by
  have hab := mul_nonneg ha hb
  have hπab := mul_nonneg Real.pi_pos.le hab
  have hπ := Real.pi_pos
  nlinarith

end T3b

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

namespace RawLeafPacket

variable (packet : RawLeafPacket call p)

theorem t3b_firstSign_norm : ‖packet.firstSign‖ = 1 := by
  unfold firstSign
  split_ifs <;> norm_num

theorem t3b_time_norm_le (side : Bool) (z : ℝ × ℝ) :
    ‖T3b.time (packet.t3bFourierSign side)
      (t3bFourierMode side (WithLp.toLp 2 z))‖ ≤
        2 * Real.pi * (‖z.1‖ + ‖z.2‖) := by
  cases side with
  | false => exact T3b.norm_time_pair_le packet.firstSign packet.t3b_firstSign_norm z
  | true =>
    change ‖T3b.time (-packet.firstSign) (-(WithLp.toLp 2 z))‖ ≤ _
    rw [T3b.norm_time_neg]
    exact T3b.norm_time_pair_le (-packet.firstSign)
      (by rw [norm_neg, packet.t3b_firstSign_norm]) z

theorem t3b_time_one_add_le (side : Bool) (z : ℝ × ℝ) :
    1 + ‖T3b.time (packet.t3bFourierSign side)
      (t3bFourierMode side (WithLp.toLp 2 z))‖ ≤
        (1 + 2 * Real.pi) * (1 + ‖z.1‖) * (1 + ‖z.2‖) :=
  (add_le_add_left (packet.t3b_time_norm_le side z) 1).trans
    (T3b.one_add_scaled_sum_le_product _ _ (norm_nonneg _) (norm_nonneg _))

theorem t3b_time_power_le (side : Bool) (z : ℝ × ℝ) (degree : ℕ) :
    (1 + ‖T3b.time (packet.t3bFourierSign side)
      (t3bFourierMode side (WithLp.toLp 2 z))‖) ^ degree ≤
        (1 + 2 * Real.pi) ^ degree * (1 + ‖z.1‖) ^ degree * (1 + ‖z.2‖) ^ degree := by
  simpa only [mul_pow] using pow_le_pow_left₀
    (add_nonneg zero_le_one (norm_nonneg _)) (packet.t3b_time_one_add_le side z) degree

theorem t3b_time_power_pair_le (z : ℝ × ℝ) (leftDegree rightDegree : ℕ) :
    (1 + ‖T3b.time (packet.t3bFourierSign false)
      (t3bFourierMode false (WithLp.toLp 2 z))‖) ^ leftDegree *
    (1 + ‖T3b.time (packet.t3bFourierSign true)
      (t3bFourierMode true (WithLp.toLp 2 z))‖) ^ rightDegree ≤
      (1 + 2 * Real.pi) ^ (leftDegree + rightDegree) *
        ((1 + ‖z.1‖) ^ (leftDegree + rightDegree) *
          (1 + ‖z.2‖) ^ (leftDegree + rightDegree)) := by
  have hright : 0 ≤ (1 + ‖T3b.time (packet.t3bFourierSign true)
      (t3bFourierMode true (WithLp.toLp 2 z))‖) ^ rightDegree :=
    pow_nonneg (add_nonneg zero_le_one (norm_nonneg _)) _
  have hleft : 0 ≤
      (1 + 2 * Real.pi) ^ leftDegree * (1 + ‖z.1‖) ^ leftDegree *
        (1 + ‖z.2‖) ^ leftDegree := by positivity
  have h := mul_le_mul (packet.t3b_time_power_le false z leftDegree)
    (packet.t3b_time_power_le true z rightDegree) hright hleft
  apply h.trans_eq
  simp only [pow_add]
  ring

end RawLeafPacket

end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.t3b_time_power_pair_le
