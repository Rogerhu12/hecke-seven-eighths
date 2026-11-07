module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondTailBudget

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Fixed positive physical cutoffs pay any fixed polynomial source degree

The source parameters have already fixed the two positive cutoff
exponents. This helper chooses the decay order from those exponents,
before the source or scale, without changing either physical cutoff.
-/

noncomputable section

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails

open HeckeSkeleton.Moments.EngineStep

/-- A larger prescribed cutoff only improves the negative tail power. -/
theorem fixed_cutoff_power (Z degree bound saving minimum cutoff : ℝ)
    (hZ : 1 ≤ Z) (hminimum : 0 < minimum)
    (hcutoff : minimum ≤ cutoff) (hdegree : degree ≤ bound) :
    (Z ^ cutoff) ^ (1 - tailDecayForWidth bound saving minimum) * Z ^ degree ≤
      Z ^ (-saving) := by
  have hZpos : 0 < Z := zero_lt_one.trans_le hZ
  have hdecay : 1 < tailDecayForWidth bound saving minimum :=
    tailDecayForWidth_gt_one bound saving minimum hminimum
  have he : minimum * (1 - tailDecayForWidth bound saving minimum) =
      -(1 + max 0 (bound + saving)) := by
    unfold tailDecayForWidth
    field_simp [ne_of_gt hminimum]
    <;> ring
  have hexponent : cutoff * (1 - tailDecayForWidth bound saving minimum) + degree ≤
      -saving := by
    have hc := mul_le_mul_of_nonpos_right hcutoff (sub_nonpos.mpr hdecay.le)
    rw [he] at hc
    linarith [le_max_right (0 : ℝ) (bound + saving)]
  rw [← Real.rpow_mul hZpos.le, ← Real.rpow_add hZpos]
  exact Real.rpow_le_rpow_of_exponent_le hZ hexponent

/-- One decay and integer order work for both cutoffs, all source
degrees in the fixed box, and every scale at least one. -/
theorem exists_common_fixed_cutoff_order
    (rank : ℕ) (fieldDegree bound saving firstCutoff secondCutoff : ℝ)
    (hfirst : 0 < firstCutoff) (hsecond : 0 < secondCutoff) :
    ∃ decay : ℝ, 1 < decay ∧ ∃ order : ℕ,
      rank < order ∧ fieldDegree * decay ≤ (order : ℝ) ∧
      ∀ Z degree : ℝ, 1 ≤ Z → degree ≤ bound →
        (Z ^ firstCutoff) ^ (1 - decay) * Z ^ degree ≤ Z ^ (-saving) ∧
        (Z ^ secondCutoff) ^ (1 - decay) * Z ^ degree ≤ Z ^ (-saving) := by
  let minimum := min firstCutoff secondCutoff
  have hminimum : 0 < minimum := lt_min hfirst hsecond
  let decay := tailDecayForWidth bound saving minimum
  have hdecay : 1 < decay := tailDecayForWidth_gt_one bound saving minimum hminimum
  obtain ⟨order, horder⟩ := exists_nat_gt (max (rank : ℝ) (fieldDegree * decay))
  have hrank : (rank : ℝ) < (order : ℝ) :=
    lt_of_le_of_lt (le_max_left _ _) horder
  refine ⟨decay, hdecay, order, ?_, ?_, ?_⟩
  · exact_mod_cast hrank
  · exact (lt_of_le_of_lt (le_max_right _ _) horder).le
  · intro Z degree hZ hdegree
    exact ⟨fixed_cutoff_power Z degree bound saving minimum firstCutoff
        hZ hminimum (min_le_left _ _) hdegree,
      fixed_cutoff_power Z degree bound saving minimum secondCutoff
        hZ hminimum (min_le_right _ _) hdegree⟩

/-- The same cutoff calculation absorbs a genuine nonnegative source
mass with its already proved polynomial bound. -/
theorem fixed_cutoff_mass_bound
    (Z degree bound saving minimum cutoff raw coefficient amplitude Ctail : ℝ)
    (hZ : 1 ≤ Z) (hminimum : 0 < minimum)
    (hcutoff : minimum ≤ cutoff) (hdegree : degree ≤ bound)
    (hcoefficient : 0 ≤ coefficient) (hamplitude : 0 ≤ amplitude)
    (hCtail : 0 ≤ Ctail)
    (hraw : raw ≤ coefficient * amplitude * Z ^ degree) :
    Ctail * (Z ^ cutoff) ^ (1 - tailDecayForWidth bound saving minimum) * raw ≤
      (Ctail * coefficient) * amplitude * Z ^ (-saving) := by
  have hZpos : 0 < Z := zero_lt_one.trans_le hZ
  calc
    _ ≤ Ctail * (Z ^ cutoff) ^ (1 - tailDecayForWidth bound saving minimum) *
        (coefficient * amplitude * Z ^ degree) :=
      mul_le_mul_of_nonneg_left hraw
        (mul_nonneg hCtail (Real.rpow_nonneg (Real.rpow_nonneg hZpos.le _) _))
    _ = ((Ctail * coefficient) * amplitude) *
        ((Z ^ cutoff) ^ (1 - tailDecayForWidth bound saving minimum) * Z ^ degree) := by
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (fixed_cutoff_power Z degree bound saving minimum cutoff
        hZ hminimum hcutoff hdegree)
      (mul_nonneg (mul_nonneg hCtail hcoefficient) hamplitude)

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails.fixed_cutoff_power
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails.exists_common_fixed_cutoff_order
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.Tails.fixed_cutoff_mass_bound
