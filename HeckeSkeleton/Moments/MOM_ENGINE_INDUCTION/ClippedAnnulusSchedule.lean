import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# A finite positive annulus schedule including actual clipping

A strict call first enlarges `[lo, hi]` to `[lo / 2, 2 * hi]`
by Mellin preprocessing. Its active actual child then has support in
`[(lo / 2) / (2 * hi), 2 * hi]`, by the literal clipping bound.

For a fixed outer rank bound `N`, every upper endpoint is at most
`upper * 2 ^ N`. The single factor `max 2 (4 * (upper * 2 ^ N))`
therefore pays the lower-endpoint loss at every strict decrease.
It is fixed before the node, scale, height and Fourier parameters.
All supports remain inside one fixed positive maximal annulus.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open Set

/-- The fixed cost of one lower-endpoint enlargement. -/
def clippedAnnulusStep (upper : ℝ) (N : ℕ) : ℝ :=
  max 2 (4 * (upper * (2 : ℝ) ^ N))

theorem clippedAnnulusStep_two_le (upper : ℝ) (N : ℕ) :
    2 ≤ clippedAnnulusStep upper N := le_max_left _ _

theorem clippedAnnulusStep_one_le (upper : ℝ) (N : ℕ) :
    1 ≤ clippedAnnulusStep upper N :=
  (show (1 : ℝ) ≤ 2 by norm_num).trans (clippedAnnulusStep_two_le upper N)

theorem clippedAnnulusStep_pos (upper : ℝ) (N : ℕ) :
    0 < clippedAnnulusStep upper N :=
  zero_lt_one.trans_le (clippedAnnulusStep_one_le upper N)

/-- The lower endpoint pays both Mellin enlargement and active clipping. -/
def clippedAnnulusLower (lower upper : ℝ) (N rank : ℕ) : ℝ :=
  lower / clippedAnnulusStep upper N ^ (N - rank)

theorem clippedAnnulusLower_pos {lower upper : ℝ} (hlower : 0 < lower)
    (N rank : ℕ) : 0 < clippedAnnulusLower lower upper N rank :=
  div_pos hlower (pow_pos (clippedAnnulusStep_pos upper N) _)

theorem clippedAnnulusLower_le {lower upper : ℝ} (hlower : 0 ≤ lower)
    (N rank : ℕ) : clippedAnnulusLower lower upper N rank ≤ lower := by
  have hp := one_le_pow₀ (n := N - rank) (clippedAnnulusStep_one_le upper N)
  simpa only [clippedAnnulusLower, div_one] using
    div_le_div_of_nonneg_left hlower (show (0 : ℝ) < 1 by norm_num) hp

theorem clippedAnnulus_original_subset {lower upper : ℝ}
    (hlower : 0 ≤ lower) (hupper : 0 ≤ upper) (N rank : ℕ) :
    Icc lower upper ⊆ Icc (clippedAnnulusLower lower upper N rank)
      (upper * (2 : ℝ) ^ (N - rank)) := by
  have hhigh : upper ≤ upper * (2 : ℝ) ^ (N - rank) :=
    le_mul_of_one_le_right hupper (one_le_pow₀ (by norm_num))
  intro y hy
  exact ⟨(clippedAnnulusLower_le hlower N rank).trans hy.1, hy.2.trans hhigh⟩

theorem clippedAnnulus_bounds {lower upper : ℝ}
    (hlower : 0 < lower) (hinterval : lower ≤ upper) (N rank : ℕ) :
    0 < clippedAnnulusLower lower upper N rank ∧
      clippedAnnulusLower lower upper N rank ≤ upper * (2 : ℝ) ^ (N - rank) := by
  have h := clippedAnnulus_original_subset hlower.le (hlower.trans_le hinterval).le
    N rank (show lower ∈ Icc lower upper from ⟨le_rfl, hinterval⟩)
  exact ⟨clippedAnnulusLower_pos hlower N rank, h.1.trans h.2⟩

theorem clippedAnnulus_maximal_subset {lower upper : ℝ}
    (hlower : 0 ≤ lower) (hupper : 0 ≤ upper) (N rank : ℕ) :
    Icc (clippedAnnulusLower lower upper N rank) (upper * (2 : ℝ) ^ (N - rank)) ⊆
      Icc (lower / clippedAnnulusStep upper N ^ N) (upper * (2 : ℝ) ^ N) := by
  have hlowerPow : clippedAnnulusStep upper N ^ (N - rank) ≤
      clippedAnnulusStep upper N ^ N :=
    pow_le_pow_right₀ (clippedAnnulusStep_one_le upper N) (Nat.sub_le N rank)
  have hupperPow : (2 : ℝ) ^ (N - rank) ≤ 2 ^ N :=
    pow_le_pow_right₀ (by norm_num) (Nat.sub_le N rank)
  intro y hy
  exact ⟨(div_le_div_of_nonneg_left hlower
      (pow_pos (clippedAnnulusStep_pos upper N) _) hlowerPow).trans hy.1,
    hy.2.trans (mul_le_mul_of_nonneg_left hupperPow hupper)⟩

/-- Any earlier rank enlarges support, also when no strict call occurs. -/
theorem clippedAnnulus_descendant_subset {lower upper : ℝ}
    (hlower : 0 ≤ lower) (hupper : 0 ≤ upper) (N : ℕ) {parent child : ℕ}
    (hearlier : child ≤ parent) :
    Icc (clippedAnnulusLower lower upper N parent) (upper * (2 : ℝ) ^ (N - parent)) ⊆
      Icc (clippedAnnulusLower lower upper N child) (upper * (2 : ℝ) ^ (N - child)) := by
  have hd : N - parent ≤ N - child := by omega
  have hlowerPow := pow_le_pow_right₀ (clippedAnnulusStep_one_le upper N) hd
  have hupperPow := pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) hd
  intro y hy
  exact ⟨(div_le_div_of_nonneg_left hlower
      (pow_pos (clippedAnnulusStep_pos upper N) _) hlowerPow).trans hy.1,
    hy.2.trans (mul_le_mul_of_nonneg_left hupperPow hupper)⟩

theorem clippedAnnulus_reflection_subset {lower upper : ℝ}
    (hlower : 0 ≤ lower) (hlowerSmall : lower ≤ 1 / 2) (hupper : 2 ≤ upper)
    (N rank : ℕ) :
    Icc (1 / 2 : ℝ) 2 ⊆ Icc (clippedAnnulusLower lower upper N rank)
      (upper * (2 : ℝ) ^ (N - rank)) := by
  intro y hy
  exact clippedAnnulus_original_subset hlower (by linarith) N rank
    ⟨hlowerSmall.trans hy.1, hy.2.trans hupper⟩

theorem clippedAnnulusStep_dominates {upper : ℝ} (hupper : 0 ≤ upper)
    (N rank : ℕ) :
    4 * (upper * (2 : ℝ) ^ (N - rank)) ≤ clippedAnnulusStep upper N := by
  apply le_trans _ (le_max_right _ _)
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) (Nat.sub_le N rank)) hupper)
    (by norm_num)

/-- A true rank decrease pays both the plateau expansion and the
actual clipping loss. Natural subtraction requires the parent bound. -/
theorem clippedAnnulus_child_enlargement_bounds {lower upper : ℝ}
    (hlower : 0 ≤ lower) (hupper : 0 < upper) {N parent child : ℕ}
    (hparent : parent ≤ N) (hearlier : child < parent) :
    clippedAnnulusLower lower upper N child ≤
        (clippedAnnulusLower lower upper N parent / 2) /
          (2 * (upper * (2 : ℝ) ^ (N - parent))) ∧
      2 * (upper * (2 : ℝ) ^ (N - parent)) ≤ upper * (2 : ℝ) ^ (N - child) := by
  have hexponent : (N - parent) + 1 ≤ N - child := by omega
  have hstep := clippedAnnulusStep_pos upper N
  have hlowerPow : clippedAnnulusStep upper N ^ (N - parent) *
      clippedAnnulusStep upper N ≤ clippedAnnulusStep upper N ^ (N - child) := by
    simpa only [pow_succ] using
      pow_le_pow_right₀ (clippedAnnulusStep_one_le upper N) hexponent
  have hupperPow : (2 : ℝ) ^ (N - parent) * 2 ≤ 2 ^ (N - child) := by
    simpa only [pow_succ] using
      pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) hexponent
  constructor
  · have hfirst : clippedAnnulusLower lower upper N child ≤
        clippedAnnulusLower lower upper N parent / clippedAnnulusStep upper N := by
      dsimp only [clippedAnnulusLower]
      rw [div_div]
      exact div_le_div_of_nonneg_left hlower (mul_pos (pow_pos hstep _) hstep) hlowerPow
    have hcost : clippedAnnulusLower lower upper N parent / clippedAnnulusStep upper N ≤
        clippedAnnulusLower lower upper N parent /
          (4 * (upper * (2 : ℝ) ^ (N - parent))) :=
      div_le_div_of_nonneg_left (div_nonneg hlower (pow_nonneg hstep.le _))
        (by positivity) (clippedAnnulusStep_dominates hupper.le N parent)
    apply (hfirst.trans hcost).trans_eq
    rw [div_div]
    congr 1
    ring
  · calc
      _ = upper * ((2 : ℝ) ^ (N - parent) * 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hupperPow hupper.le

/-- The exact annulus produced by Mellin preprocessing followed by
active clipping lies in the actual child's scheduled support layer. -/
theorem clippedAnnulus_child_enlargement_subset {lower upper : ℝ}
    (hlower : 0 ≤ lower) (hupper : 0 < upper) {N parent child : ℕ}
    (hparent : parent ≤ N) (hearlier : child < parent) :
    Icc ((clippedAnnulusLower lower upper N parent / 2) /
        (2 * (upper * (2 : ℝ) ^ (N - parent))))
        (2 * (upper * (2 : ℝ) ^ (N - parent))) ⊆
      Icc (clippedAnnulusLower lower upper N child) (upper * (2 : ℝ) ^ (N - child)) := by
  obtain ⟨hlo, hhi⟩ := clippedAnnulus_child_enlargement_bounds hlower hupper hparent hearlier
  intro y hy
  exact ⟨hlo.trans hy.1, hy.2.trans hhi⟩

end HeckeSkeleton.Moments.EngineInduction

#print axioms HeckeSkeleton.Moments.EngineInduction.clippedAnnulus_child_enlargement_subset
