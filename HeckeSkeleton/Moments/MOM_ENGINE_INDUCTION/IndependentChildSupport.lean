import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.ActiveFamilyAnnulus

/-!
# Support certificates independent of the numerical normalization box

A larger support box may be needed by the exceptional source estimate.
The physical functions still have their original smaller support. This
file propagates that independent support through the actual clipping,
slot selection, normalization and time freeze. The final unit Schwartz
window is the producer's existing window with only its support proof
strengthened; no numerical radius or estimate is replaced.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineInduction.ActiveChildAnnulus

open NumberField IsDedekindDomain
open DedekindZetaZeroFree (SArithmeticData)
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeSkeleton.Moments.EngineStep

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}
variable {rowDomain : Set (NonzeroIdeal K)} {heightDomain window : Set ℝ}
variable {d : MomentData K ω ψ}

/-- Literal positive normalization cannot enlarge support, regardless
of how large its original radius was chosen. -/
theorem ProfileSupport.normalized (h : ProfileSupport rowDomain heightDomain window d)
    (B : ℝ) (hB : 0 < B) :
    ProfileSupport rowDomain heightDomain window (normalizedMomentProfiles d B hB) where
  inverse u hu t ht y hy := by
    change ((B⁻¹ : ℝ) : ℂ) * d.inverseTest.profile u t y ≠ 0 at hy
    exact h.inverse u hu t ht (right_ne_zero_of_mul hy)
  left u hu t ht y hy := by
    change ((B⁻¹ : ℝ) : ℂ) * d.plainTest₁.profile u t y ≠ 0 at hy
    exact h.left u hu t ht (right_ne_zero_of_mul hy)
  right u hu t ht y hy := by
    change ((B⁻¹ : ℝ) : ℂ) * d.plainTest₂.profile u t y ≠ 0 at hy
    exact h.right u hu t ht (right_ne_zero_of_mul hy)
  prime i t ht y hy := by
    change ((B⁻¹ : ℝ) : ℂ) * (d.geometry.slots i).profile t y ≠ 0 at hy
    exact h.prime i t ht (right_ne_zero_of_mul hy)

theorem ProfileSupport.restrictSlots
    (h : ProfileSupport rowDomain heightDomain window d)
    (keep : Finset (Fin d.geometry.slotCount)) :
    ProfileSupport rowDomain heightDomain window (d.restrictSlots keep) where
  inverse := h.inverse
  left := h.left
  right := h.right
  prime i t ht := h.prime (selectedSlotIndex keep i) t ht

theorem ProfileSupport.freeze
    (h : ProfileSupport rowDomain heightDomain window d)
    (time : ℝ) (htime : time ∈ heightDomain) :
    ProfileSupport rowDomain Set.univ window (frozenMomentProfiles d time) where
  inverse u hu t _ y hy := by
    apply h.inverse u hu time htime
    simpa only [frozenMomentProfiles, MomentData.separatedProfiles, IdealTest.freezeTwist,
      profilePower_zero, mul_one] using hy
  left u hu t _ y hy := by
    apply h.left u hu time htime
    simpa only [frozenMomentProfiles, MomentData.separatedProfiles, IdealTest.freezeTwist,
      profilePower_zero, mul_one] using hy
  right u hu t _ y hy := by
    apply h.right u hu time htime
    simpa only [frozenMomentProfiles, MomentData.separatedProfiles, IdealTest.freezeTwist,
      profilePower_zero, mul_one] using hy
  prime i t _ y hy := by
    apply h.prime i time htime
    simpa only [frozenMomentProfiles, MomentData.separatedProfiles, SlotGeometry.freezeTwists,
      PrimeWindow.freezeTwist, profilePower_zero, mul_one] using hy

/-- A nonzero actual row bounds clipping using the independent
physical support, without referring to the normalization window. -/
theorem clipping_factors_le_of_support
    (p : RealParameters) (Z t : ℝ) (hZ : 1 < Z)
    {lo hi : ℝ} (hhi : 1 ≤ hi)
    (h : ProfileSupport rowDomain heightDomain (Set.Icc lo hi) d)
    (hrows : ∀ u ∈ pairedRows d p Z, u ∈ rowDomain) (ht : t ∈ heightDomain)
    (hne : pairedEnergy d p Z t ≠ 0) :
    plainClippingFactor Z p.n₁ ≤ hi ∧ plainClippingFactor Z p.n₂ ≤ hi := by
  obtain ⟨u, hu, hleft, hright⟩ := nonzero_pairedEnergy_plain_witness d p Z t hne
  exact ⟨clipping_factor_le_of_nonempty_support d.plainTest₁ u Z p.n₁ t hi hZ hhi
      (fun y hy => (h.left u (hrows u hu) t ht hy).2)
      (plainPolynomial_support_nonempty d d.plainTest₁ u _ t hleft),
    clipping_factor_le_of_nonempty_support d.plainTest₂ u Z p.n₂ t hi hZ hhi
      (fun y hy => (h.right u (hrows u hu) t ht hy).2)
      (plainPolynomial_support_nonempty d d.plainTest₂ u _ t hright)⟩

section Capacity

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {k : ℕ} {source : ActualAllocatedSource A V H k}
variable {cal : source.Calibration (σ := σ) ω ψ}
variable {capacity : cal.NormalizedCapacityData}

/-- The actual active capacity child has a smaller physical support
regardless of the window used to construct its numerical radius. -/
theorem active_child_support
    (out : capacity.Child) {lo hi : ℝ} (hlo : 0 ≤ lo) (hhi : 1 ≤ hi)
    (original : ∀ ξ, ProfileSupport rowDomain heightDomain (Set.Icc lo hi) (cal.data ξ))
    (hrows : ∀ ξ, ∀ u ∈ pairedRows (cal.data ξ) cal.parameters source.base,
      u ∈ rowDomain)
    (htime : ∀ ξ, cal.height ξ ∈ heightDomain)
    (hactive : ¬ ∀ ξ, source.energy (σ := σ) ξ = 0) (ξ : V) :
    ProfileSupport rowDomain Set.univ (Set.Icc (lo / hi) hi) (out.frozenData ξ) := by
  obtain ⟨ξ₀, hne⟩ := not_forall.mp hactive
  have henergy : pairedEnergy (cal.data ξ₀) cal.parameters source.base (cal.height ξ₀) ≠ 0 := by
    intro hz
    have hbound := cal.energy_le ξ₀
    rw [hz, mul_zero] at hbound
    exact hne (le_antisymm hbound (source.energy_nonneg (σ := σ) ξ₀))
  obtain ⟨hleft, hright⟩ := clipping_factors_le_of_support
    cal.parameters source.base (cal.height ξ₀) source.base_gt_one hhi
    (original ξ₀) (hrows ξ₀) (htime ξ₀) henergy
  have hclipped := clipped_support cal.parameters source.base source.base_gt_one.le
    hlo hhi (original ξ) hleft hright
  have hchild : ProfileSupport rowDomain heightDomain (Set.Icc (lo / hi) hi)
      (out.data ξ) := by
    rw [out.data_eq_normalized_raw]
    exact (hclipped.restrictSlots
      (lengthSelection (cal.clippedData ξ) source.allocation.keep.card
        (cal.count ξ) (Finset.univ \ out.removed))).normalized
      (capacity.radius ξ) (capacity.radius_pos ξ)
  exact hchild.freeze (cal.height ξ) (htime ξ)

end Capacity

/-- Preserve the actual unit representatives and all finite seminorm
bounds, replacing only support by the independently proved smaller set. -/
theorem unitWindow_withSupport {orders : Finset (ℕ × ℕ)} {broad narrow : Set ℝ}
    (w : InFixedProfileWindow rowDomain heightDomain broad orders d)
    (h : ProfileSupport rowDomain heightDomain narrow d) :
    InFixedProfileWindow rowDomain heightDomain narrow orders d := by
  obtain ⟨raw⟩ := w
  exact ⟨windowWithSupport raw h⟩

end HeckeSkeleton.Moments.EngineInduction.ActiveChildAnnulus

#print axioms HeckeSkeleton.Moments.EngineInduction.ActiveChildAnnulus.active_child_support
#print axioms HeckeSkeleton.Moments.EngineInduction.ActiveChildAnnulus.unitWindow_withSupport
