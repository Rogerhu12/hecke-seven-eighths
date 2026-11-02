import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.UniversalNodeFamily

/-!
# A finite support schedule for actual profile preprocessing

The outer depth and the original positive annulus are fixed before any
moving polynomial data.  A node of rank r uses the original annulus
enlarged by 2^(N-r).  A genuine strict rank decrease therefore pays one
further factor-two enlargement, including when several ranks are skipped.
Every layer stays within a single fixed maximal annulus.

The profile-control lemmas below only weaken the support clause. They do
not assert that any transformed child has the required support, and they
leave its genuine function, derivative order, integral weight, coefficient
and height degree unchanged. Quarter centering and its raw comparison
have exactly the same support layer because their actual parameter rank
is equal. No mesh or energy statement is modified.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField Set
open HeckeGeneral.Characters HeckeGeneral.Analysis.ConditionalMoments
open HeckeSkeleton.Moments.UniformAmplify

/-- The lower endpoint in the preselected finite support schedule. -/
def rankedAnnulusLower (a : ℝ) (N rank : ℕ) : ℝ := a / (2 : ℝ) ^ (N - rank)

/-- The upper endpoint in the same schedule. -/
def rankedAnnulusUpper (b : ℝ) (N rank : ℕ) : ℝ := b * (2 : ℝ) ^ (N - rank)

/-- Every layer contains the original annulus, even at the maximal rank. -/
theorem rankedAnnulus_original_subset {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (N rank : ℕ) :
    Icc a b ⊆ Icc (rankedAnnulusLower a N rank) (rankedAnnulusUpper b N rank) := by
  have hp : (1 : ℝ) ≤ 2 ^ (N - rank) := one_le_pow₀ (by norm_num)
  have hlo : a / (2 : ℝ) ^ (N - rank) ≤ a := by
    calc
      _ ≤ a / 1 := div_le_div_of_nonneg_left ha (by norm_num) hp
      _ = a := div_one _
  have hhi : b ≤ b * (2 : ℝ) ^ (N - rank) := by
    calc
      b = b * 1 := (mul_one _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hp hb
  intro y hy
  exact ⟨hlo.trans hy.1, hy.2.trans hhi⟩

/-- The finite support layers are all positive, nonempty annuli. -/
theorem rankedAnnulus_bounds {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (N rank : ℕ) :
    0 < rankedAnnulusLower a N rank ∧
      rankedAnnulusLower a N rank ≤ rankedAnnulusUpper b N rank := by
  have hm := rankedAnnulus_original_subset ha.le (ha.trans_le hab).le N rank
    (show a ∈ Icc a b from ⟨le_rfl, hab⟩)
  exact ⟨div_pos ha (by positivity), hm.1.trans hm.2⟩

/-- One fixed maximal annulus covers every rank, before any data are chosen. -/
theorem rankedAnnulus_maximal_subset {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (N rank : ℕ) :
    Icc (rankedAnnulusLower a N rank) (rankedAnnulusUpper b N rank) ⊆
      Icc (a / (2 : ℝ) ^ N) (b * (2 : ℝ) ^ N) := by
  have hp : (2 : ℝ) ^ (N - rank) ≤ 2 ^ N :=
    pow_le_pow_right₀ (by norm_num) (Nat.sub_le N rank)
  intro y hy
  exact ⟨(div_le_div_of_nonneg_left ha (by positivity) hp).trans hy.1,
    hy.2.trans (mul_le_mul_of_nonneg_left hp hb)⟩

/-- A true rank decrease pays exactly one further factor-two expansion.
The bound on the parent rank is essential: subtraction is natural-valued. -/
theorem rankedAnnulus_child_enlargement_bounds {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) {N parent child : ℕ}
    (hparent : parent ≤ N) (hearlier : child < parent) :
    rankedAnnulusLower a N child ≤ rankedAnnulusLower a N parent / 2 ∧
      2 * rankedAnnulusUpper b N parent ≤ rankedAnnulusUpper b N child := by
  have hexponent : (N - parent) + 1 ≤ N - child := by omega
  have hp : (2 : ℝ) ^ (N - parent) * 2 ≤ 2 ^ (N - child) := by
    simpa only [pow_succ] using pow_le_pow_right₀
      (show (1 : ℝ) ≤ 2 by norm_num) hexponent
  constructor
  · dsimp only [rankedAnnulusLower]
    rw [div_div]
    exact div_le_div_of_nonneg_left ha (by positivity) hp
  · change 2 * (b * (2 : ℝ) ^ (N - parent)) ≤ b * (2 : ℝ) ^ (N - child)
    calc
      _ = b * ((2 : ℝ) ^ (N - parent) * 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hp hb

/-- Exact support consumer for a Mellin plateau on the parent layer. -/
theorem rankedAnnulus_child_enlargement_subset {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) {N parent child : ℕ}
    (hparent : parent ≤ N) (hearlier : child < parent) :
    Icc (rankedAnnulusLower a N parent / 2) (2 * rankedAnnulusUpper b N parent) ⊆
      Icc (rankedAnnulusLower a N child) (rankedAnnulusUpper b N child) := by
  obtain ⟨hlo, hhi⟩ := rankedAnnulus_child_enlargement_bounds ha hb hparent hearlier
  intro y hy
  exact ⟨hlo.trans hy.1, hy.2.trans hhi⟩

/-- The actual ordinary-reflection window [1/2,2] fits every support layer. -/
theorem rankedAnnulus_reflection_subset {a b : ℝ}
    (ha : 0 ≤ a) (haSmall : a ≤ 1 / 2) (hbLarge : 2 ≤ b) (N rank : ℕ) :
    Icc (1 / 2 : ℝ) 2 ⊆
      Icc (rankedAnnulusLower a N rank) (rankedAnnulusUpper b N rank) := by
  intro y hy
  exact rankedAnnulus_original_subset ha (by linarith) N rank
    ⟨haSmall.trans hy.1, hy.2.trans hbLarge⟩

/-- Enlarging the annulus changes only the support clause of the actual
profile estimate. The exact weighted seminorm bound is retained. -/
theorem sliceControl_annulus_mono {f : ℝ → ℂ} {J : ℕ}
    {A C H T a b a' b' : ℝ} (h : SliceControl J A C H a b T f)
    (hinterval : Icc a b ⊆ Icc a' b') : SliceControl J A C H a' b' T f := by
  exact ⟨h.1, fun y hy => hinterval (h.2.1 y hy), h.2.2⟩

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}

/-- Every ideal-test row and every actual prime slot use the same
support inclusion, with no change to their evaluated profiles. -/
theorem modelProfileControl_annulus_mono {d : MomentData K ω ψ} {J : ℕ}
    {A C H T a b a' b' : ℝ} (h : ModelProfileControl d J A C H a b T)
    (hinterval : Icc a b ⊆ Icc a' b') : ModelProfileControl d J A C H a' b' T :=
  fun q => sliceControl_annulus_mono (h q) hinterval

/-- The original uniform profile family enters each scheduled layer
without selecting any new derivative or height constants. -/
theorem modelProfileControl_rankedAnnulus_original {d : MomentData K ω ψ} {J : ℕ}
    {A C H T a b : ℝ} (h : ModelProfileControl d J A C H a b T)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (N rank : ℕ) :
    ModelProfileControl d J A C H
      (rankedAnnulusLower a N rank) (rankedAnnulusUpper b N rank) T :=
  modelProfileControl_annulus_mono h (rankedAnnulus_original_subset ha hb N rank)

/-- Once an actual child has the plateau's support, the genuine rank
decrease places it in its own layer. This is a support transport theorem,
not an assertion of the transform producer's support conclusion. -/
theorem modelProfileControl_rankedAnnulus_child {d : MomentData K ω ψ} {J : ℕ}
    {A C H T a b : ℝ} {N parent child : ℕ}
    (h : ModelProfileControl d J A C H
      (rankedAnnulusLower a N parent / 2) (2 * rankedAnnulusUpper b N parent) T)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hparent : parent ≤ N) (hearlier : child < parent) :
    ModelProfileControl d J A C H
      (rankedAnnulusLower a N child) (rankedAnnulusUpper b N child) T :=
  modelProfileControl_annulus_mono h
    (rankedAnnulus_child_enlargement_subset ha hb hparent hearlier)

/-- Quarter centering keeps the actual parameters, hence the exact
finite-annulus layer, unchanged. -/
theorem Node.rankedAnnulus_quarterCentered (n : Node K ω ψ)
    (a b : ℝ) (N : ℕ) (σ W padding : ℝ) :
    (rankedAnnulusLower a N (parameterCoreRank σ W padding n.quarterCentered.parameters),
      rankedAnnulusUpper b N (parameterCoreRank σ W padding n.quarterCentered.parameters)) =
    (rankedAnnulusLower a N (parameterCoreRank σ W padding n.parameters),
      rankedAnnulusUpper b N (parameterCoreRank σ W padding n.parameters)) := rfl

/-- The raw ordinary comparison has the same real width, slots and
plain-length sum. It therefore uses the identical support layer; only
its subsequent true reflection can spend a rank decrease. -/
theorem Node.rankedAnnulus_comparisonOrdinary (n : Node K ω ψ)
    (a b : ℝ) (N : ℕ) (σ W padding : ℝ) :
    (rankedAnnulusLower a N (parameterCoreRank σ W padding n.comparisonOrdinary.parameters),
      rankedAnnulusUpper b N (parameterCoreRank σ W padding n.comparisonOrdinary.parameters)) =
    (rankedAnnulusLower a N (parameterCoreRank σ W padding n.parameters),
      rankedAnnulusUpper b N (parameterCoreRank σ W padding n.parameters)) := by
  have hrank : parameterCoreRank σ W padding n.comparisonParameters =
      parameterCoreRank σ W padding n.parameters := by
    calc
      _ = parameterCoreRank σ W padding
          (pairedInvariantParameters n.comparisonParameters).parameters :=
        (pairedInvariantParameters_coreRank σ W padding n.comparisonParameters).symm
      _ = parameterCoreRank σ W padding (pairedInvariantParameters n.parameters).parameters := by
        rw [pairedInvariantParameters_comparison]
      _ = _ := pairedInvariantParameters_coreRank σ W padding n.parameters
  change (rankedAnnulusLower a N (parameterCoreRank σ W padding n.comparisonParameters),
      rankedAnnulusUpper b N (parameterCoreRank σ W padding n.comparisonParameters)) = _
  rw [hrank]

end HeckeSkeleton.Moments.EngineInduction
