import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalChildFourierControl
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.HybridNormalizedProduction

/-!
# Original compact profiles for the already chosen canonical child

The original raw Schwartz window is transported through the actual
logarithmic multipliers, the actual clipping, the already selected
slot removal, normalization by its computed radius, and the final
freezing of the original evaluation height.  The clipping bounds come
from one nonzero original source member.  Neither a transformed window
nor an admissibility certificate for the child is an input.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineStep.CanonicalLogProfiles

open NumberField IsDedekindDomain DedekindZetaZeroFree MeasureTheory
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments

namespace OriginalLogProfiles

variable {K : Type} [Field K] [NumberField K]
variable {ω ψ : HeckeCharacter K} {A : SArithmeticData K} {σ : K →+* ℂ}
variable {U E : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {H : Type*} {k : ℕ}
variable {source : ActualAllocatedSource A (WithLp 2 (U × E)) H k}

/-- The same child supplied by the capacity construction has the
original fixed analytic window, both before and after freezing time.
`hradius` is the literal definition of the computed capacity radius.
The original source is only required to belong to the active branch;
its nonzero member is selected internally solely to prove the two
clipping factors lie below the fixed original annulus endpoint. -/
theorem chosen_profile_windows
    (D : OriginalLogProfiles K ω ψ (WithLp 2 (U × E)))
    (cal : source.Calibration (σ := σ) ω ψ) {G : cal.NormalizedCapacityData}
    (out : G.Child)
    (hdata : ∀ ξ, cal.data ξ = D.moving ξ)
    (t : ℝ) (htime : ∀ ξ, cal.height ξ = t)
    {rowDomain : Set (NonzeroIdeal K)} {heightDomain : Set ℝ}
    (a B : ℝ) (ha : 0 < a) (hB : 1 ≤ B) (orders : Finset (ℕ × ℕ))
    {P : ℝ} (hP : 0 ≤ P)
    (w : RawProfileWindow rowDomain heightDomain (Set.Icc a B)
      (sourceOrders orders) D.original P)
    (hleftSupport : ∀ u v, tsupport (w.leftRep u v) ⊆ Set.Icc a B)
    (hrightSupport : ∀ u v, tsupport (w.rightRep u v) ⊆ Set.Icc a B)
    (hslotSupport : ∀ i v, tsupport (w.primeRep i v) ⊆ Set.Icc a B)
    (hrows : ∀ u ∈ pairedRows D.original cal.parameters source.base, u ∈ rowDomain)
    (ht : t ∈ heightDomain)
    (hnonzero : ¬ ∀ ξ, source.energy (σ := σ) ξ = 0)
    (hradius : ∀ z, G.radius (WithLp.toLp 2 z) =
      polynomialProfileRadius (D.amplitude a B ha orders P)
        (orders.sup Prod.snd) (orders.sup Prod.snd) z)
    (z : U × E) :
    InFixedProfileWindow rowDomain heightDomain (Set.Icc (a / B) B) orders
        (out.data (WithLp.toLp 2 z)) ∧
      InFixedProfileWindow rowDomain Set.univ (Set.Icc (a / B) B) orders
        (out.frozenData (WithLp.toLp 2 z)) := by
  obtain ⟨ξ₀, hsource⟩ := not_forall.mp hnonzero
  have henergy : pairedEnergy (D.moving ξ₀) cal.parameters source.base t ≠ 0 := by
    intro he
    have hb := cal.energy_le ξ₀
    rw [hdata ξ₀, htime ξ₀, he, mul_zero] at hb
    exact hsource (le_antisymm hb (source.energy_nonneg (σ := σ) ξ₀))
  have hclipped (ξ : WithLp 2 (U × E)) :
      cal.clippedData ξ = clipPlainData (D.moving ξ) cal.parameters source.base
        (zero_lt_one.trans source.base_gt_one) :=
    congrArg (fun d => clipPlainData d cal.parameters source.base
      (zero_lt_one.trans source.base_gt_one)) (hdata ξ)
  have raw : RawProfileWindow rowDomain heightDomain (Set.Icc (a / B) B) orders
      (cal.clippedData (WithLp.toLp 2 z)) (G.radius (WithLp.toLp 2 z)) := by
    rw [hclipped, hradius z]
    exact clippedPolynomialWindow D.original D.left D.right D.slot
      D.left_positive D.right_positive D.slot_positive cal.parameters source.base t
      source.base_gt_one a B ha hB orders hP w hleftSupport hrightSupport hslotSupport
      hrows ht ξ₀ henergy z
  have hnormalized : InFixedProfileWindow rowDomain heightDomain
      (Set.Icc (a / B) B) orders (out.data (WithLp.toLp 2 z)) := by
    rw [out.data_eq_normalized_raw]
    apply normalizedMomentProfiles_in_fixed_window (G.radius_pos (WithLp.toLp 2 z))
    exact raw.restrictSlots
      (lengthSelection (cal.clippedData (WithLp.toLp 2 z)) source.allocation.keep.card
        (cal.count (WithLp.toLp 2 z)) (Finset.univ \ out.removed))
  refine ⟨hnormalized, ?_⟩
  obtain ⟨normalized⟩ := hnormalized
  exact ⟨normalized.freezeTime (cal.height (WithLp.toLp 2 z))
    (by rw [htime]; exact ht)⟩

end OriginalLogProfiles
end HeckeSkeleton.Moments.EngineStep.CanonicalLogProfiles

#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalLogProfiles.OriginalLogProfiles.chosen_profile_windows
