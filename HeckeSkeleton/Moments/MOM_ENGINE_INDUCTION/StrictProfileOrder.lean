import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.FiniteSchwartzProfileBridge
import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.ClippedAnnulusSchedule
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLogProfileBounds
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalFullKappaPrime
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalProfileAtomBounds
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalPrimitiveEngineProfileOrders

/-!
# The exact finite Euler order used by the strict Mellin producer

The child's Euler order first selects its genuine Schwartz seminorms.
The finite exceptional-volume and prime-cancellation orders and the owner's two logarithmic
profile transformations are then included. The source Schwartz-to-Euler
theorem chooses the Mellin output order, and two additional derivatives
pay the actual Mellin preprocessing theorem.

All choices depend only on the fixed maximal positive annulus and the
requested child order. They precede the data, height, rank and frequency.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical SchwartzMap

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField Set HeckeGeneral.Characters HeckeGeneral.Analysis.ConditionalMoments
open HeckeSkeleton.Moments.UniformAmplify EngineStep

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}

/-- A fixed positive profile interval, selected before moving data. -/
structure StrictProfileRange where
  lower : ℝ
  upper : ℝ
  lower_pos : 0 < lower
  interval : lower ≤ upper

namespace StrictProfileRange

def expanded (r : StrictProfileRange) : StrictProfileRange where
  lower := r.lower / 2
  upper := 2 * r.upper
  lower_pos := div_pos r.lower_pos (by norm_num)
  interval := by linarith [r.lower_pos, r.interval]

/-- The maximal child annulus in the existing finite clipping schedule. -/
def ofSchedule (lower upper : ℝ) (hlower : 0 < lower) (hinterval : lower ≤ upper)
    (N : ℕ) : StrictProfileRange where
  lower := lower / clippedAnnulusStep upper N ^ N
  upper := upper * (2 : ℝ) ^ N
  lower_pos := div_pos hlower (pow_pos (clippedAnnulusStep_pos upper N) N)
  interval := by
    have h := clippedAnnulus_original_subset hlower.le (hlower.trans_le hinterval).le N 0
      (show lower ∈ Icc lower upper from ⟨le_rfl, hinterval⟩)
    simpa only [clippedAnnulusLower, Nat.sub_zero] using h.1.trans h.2

/-- Each actual Mellin input annulus lies in the one fixed expanded
annulus used to select all source seminorm orders and constants. -/
theorem expanded_contains_schedule
    (lower upper : ℝ) (hlower : 0 < lower) (hinterval : lower ≤ upper)
    (N rank : ℕ) :
    Icc (clippedAnnulusLower lower upper N rank / 2)
      (2 * (upper * (2 : ℝ) ^ (N - rank))) ⊆
    Icc (ofSchedule lower upper hlower hinterval N).expanded.lower
      (ofSchedule lower upper hlower hinterval N).expanded.upper := by
  have hbounds := clippedAnnulus_bounds hlower hinterval N rank
  have hlow := clippedAnnulus_maximal_subset hlower.le (hlower.trans_le hinterval).le N rank
    (show clippedAnnulusLower lower upper N rank ∈
      Icc (clippedAnnulusLower lower upper N rank) (upper * (2 : ℝ) ^ (N - rank)) from
      ⟨le_rfl, hbounds.2⟩)
  have hhigh := clippedAnnulus_maximal_subset hlower.le (hlower.trans_le hinterval).le N rank
    (show upper * (2 : ℝ) ^ (N - rank) ∈
      Icc (clippedAnnulusLower lower upper N rank) (upper * (2 : ℝ) ^ (N - rank)) from
      ⟨hbounds.2, le_rfl⟩)
  intro y hy
  constructor
  · exact (div_le_div_of_nonneg_right hlow.1 (by norm_num : (0 : ℝ) ≤ 2)).trans hy.1
  · exact hy.2.trans (mul_le_mul_of_nonneg_left hhigh.2 (by norm_num : (0 : ℝ) ≤ 2))

/-- This finite set gives the desired actual child Euler control and
the owner's prime-cancellation inputs at the same time. -/
def childOrders (r : StrictProfileRange) (extraOrders : Finset (ℕ × ℕ)) (J : ℕ) (A : ℝ) : Finset (ℕ × ℕ) :=
  eulerSchwartzOrders (K := K) (ω := ω) (ψ := ψ)
    r.lower r.upper r.lower_pos J A ∪ extraOrders ∪ CanonicalFullKappaPrime.orders

theorem childOrders_euler (r : StrictProfileRange) (extraOrders : Finset (ℕ × ℕ)) (J : ℕ) (A : ℝ) :
    eulerSchwartzOrders (K := K) (ω := ω) (ψ := ψ)
      r.lower r.upper r.lower_pos J A ⊆ r.childOrders (K := K) (ω := ω) (ψ := ψ) extraOrders J A :=
  (Finset.subset_union_left).trans Finset.subset_union_left

theorem childOrders_prime (r : StrictProfileRange) (extraOrders : Finset (ℕ × ℕ)) (J : ℕ) (A : ℝ) :
    CanonicalFullKappaPrime.orders ⊆ r.childOrders (K := K) (ω := ω) (ψ := ψ) extraOrders J A :=
  Finset.subset_union_right

/-- The finite union of the original volume orders is included before
the Euler schedule is chosen. It can cover all finite numerical boxes. -/
theorem childOrders_extra (r : StrictProfileRange) (extraOrders : Finset (ℕ × ℕ))
    (J : ℕ) (A : ℝ) :
    extraOrders ⊆ r.childOrders (K := K) (ω := ω) (ψ := ψ) extraOrders J A :=
  (Finset.subset_union_right).trans Finset.subset_union_left

/-- The exact input set in the authoritative original engine signature. -/
def inputOrders (r : StrictProfileRange) (extraOrders : Finset (ℕ × ℕ)) (J : ℕ) (A : ℝ) : Finset (ℕ × ℕ) :=
  OriginalProfileAtomBounds.profileOrders (r.childOrders (K := K) (ω := ω) (ψ := ψ) extraOrders J A) ∪
    CanonicalLogProfiles.sourceOrders (CanonicalLogProfiles.sourceOrders
      (r.childOrders (K := K) (ω := ω) (ψ := ψ) extraOrders J A))

/-- The order required of the normalized actual Mellin intermediate. -/
def mellinOrder (r : StrictProfileRange) (extraOrders : Finset (ℕ × ℕ)) (J : ℕ) (A : ℝ) : ℕ :=
  schwartzSourceEulerOrder (K := K) (ω := ω) (ψ := ψ)
    r.expanded.lower r.expanded.upper r.expanded.lower_pos r.expanded.interval
    (r.inputOrders (K := K) (ω := ω) (ψ := ψ) extraOrders J A)

/-- This is the precise strict engine order function passed to the
finite backward schedule. The last two derivatives pay Mellin. -/
def engineOrder (r : StrictProfileRange) (extraOrders : Finset (ℕ × ℕ)) (A : ℝ) (J : ℕ) : ℕ :=
  r.mellinOrder (K := K) (ω := ω) (ψ := ψ) extraOrders J A + 2

/-- One common raw amplitude, independent of every Mellin frequency. -/
def amplitude (r : StrictProfileRange) (extraOrders : Finset (ℕ × ℕ)) (J : ℕ) (A : ℝ) : ℝ :=
  max 1 (schwartzSourceCoefficient (K := K) (ω := ω) (ψ := ψ)
    r.expanded.lower r.expanded.upper r.expanded.lower_pos r.expanded.interval
    (r.inputOrders (K := K) (ω := ω) (ψ := ψ) extraOrders J A))

theorem amplitude_one_le (r : StrictProfileRange) (extraOrders : Finset (ℕ × ℕ)) (J : ℕ) (A : ℝ) :
    1 ≤ r.amplitude (K := K) (ω := ω) (ψ := ψ) extraOrders J A := le_max_left _ _

/-- Every genuinely normalized intermediate supplies exactly the
authoritative raw profile input. Its narrow support and all actual
profile functions are retained by the conversion. -/
theorem rawWindow (r : StrictProfileRange) (extraOrders : Finset (ℕ × ℕ)) (J : ℕ) (A lo hi : ℝ)
    (hA : 0 ≤ A) (hinterval : Icc lo hi ⊆ Icc r.expanded.lower r.expanded.upper)
    (d : MomentData K ω ψ) (htime : ProfileTimeIndependent d)
    (hprofiles : ModelProfileControl d (r.mellinOrder (K := K) (ω := ω) (ψ := ψ) extraOrders J A)
      A 1 0 lo hi 0) :
    Nonempty (RawProfileWindow Set.univ Set.univ (Icc lo hi)
      (r.inputOrders (K := K) (ω := ω) (ψ := ψ) extraOrders J A) d
      (r.amplitude (K := K) (ω := ω) (ψ := ψ) extraOrders J A)) := by
  obtain ⟨raw⟩ := modelProfileControl_rawWindow
    r.expanded.lower r.expanded.upper r.expanded.lower_pos r.expanded.interval
    (r.inputOrders (K := K) (ω := ω) (ψ := ψ) extraOrders J A)
    lo hi A 1 hA hinterval d htime hprofiles
  exact ⟨raw.mono (by simpa only [mul_one] using
    (le_max_right 1 (schwartzSourceCoefficient (K := K) (ω := ω) (ψ := ψ)
      r.expanded.lower r.expanded.upper r.expanded.lower_pos r.expanded.interval
      (r.inputOrders (K := K) (ω := ω) (ψ := ψ) extraOrders J A))))⟩

end StrictProfileRange
end HeckeSkeleton.Moments.EngineInduction

#print axioms HeckeSkeleton.Moments.EngineInduction.StrictProfileRange.expanded_contains_schedule
#print axioms HeckeSkeleton.Moments.EngineInduction.StrictProfileRange.rawWindow
