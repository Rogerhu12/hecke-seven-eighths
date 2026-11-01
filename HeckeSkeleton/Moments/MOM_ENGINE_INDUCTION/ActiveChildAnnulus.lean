import HeckeSkeleton.Moments.MOM_ENGINE_STEP.HybridNormalizedProduction

/-!
# Positive annuli for the same active normalized children

The single-step producer uses a zero-inclusive support window so that
its normalization is defined even for an identically zero source.
An active source has a genuine nonzero member. The ideal norm lower
bound then bounds both clipping factors by the original annulus upper
endpoint. Consequently the existing clipped profiles, with the existing
Schwartz representatives and the existing normalization radius, have
support in a positive annulus.

The selected capacity child is retained throughout. Neither its removed
slots, its profiles, its radius, its energy nor its Fourier measure is
changed. Only a support proof is strengthened, first before restriction
and normalization and then at the child's frozen evaluation time.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical NumberField SchwartzMap

namespace HeckeSkeleton.Moments.EngineInduction.ActiveChildAnnulus

open NumberField IsDedekindDomain
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeSkeleton.Moments.EngineStep

variable {K : Type} [Field K] [NumberField K] {ω ψ : HeckeCharacter K}

/-- Support of every literal profile, independent of a choice of
Schwartz representative or seminorm budget. -/
structure ProfileSupport (rowDomain : Set (NonzeroIdeal K))
    (heightDomain window : Set ℝ) (d : MomentData K ω ψ) : Prop where
  inverse : ∀ u ∈ rowDomain, ∀ t ∈ heightDomain,
    Function.support (d.inverseTest.profile u t) ⊆ window
  left : ∀ u ∈ rowDomain, ∀ t ∈ heightDomain,
    Function.support (d.plainTest₁.profile u t) ⊆ window
  right : ∀ u ∈ rowDomain, ∀ t ∈ heightDomain,
    Function.support (d.plainTest₂.profile u t) ⊆ window
  prime : ∀ i, ∀ t ∈ heightDomain,
    Function.support ((d.geometry.slots i).profile t) ⊆ window

variable {rowDomain : Set (NonzeroIdeal K)} {heightDomain window : Set ℝ}
variable {orders : Finset (ℕ × ℕ)} {d : MomentData K ω ψ} {budget : ℝ}

theorem rawWindow_support
    (w : RawProfileWindow rowDomain heightDomain window orders d budget) :
    ProfileSupport rowDomain heightDomain window d where
  inverse u hu t ht y hy := by
    apply w.inverse_support u hu t ht
    simpa only [← w.inverse_eq] using hy
  left u hu t ht y hy := by
    apply w.left_support u hu t ht
    simpa only [← w.left_eq] using hy
  right u hu t ht y hy := by
    apply w.right_support u hu t ht
    simpa only [← w.right_eq] using hy
  prime i t ht y hy := by
    apply w.prime_support i t ht
    simpa only [← w.prime_eq] using hy

/-- A stronger literal support proof keeps all existing representatives
and seminorm bounds. In particular it incurs no normalization cost. -/
def windowWithSupport
    (w : RawProfileWindow rowDomain heightDomain window orders d budget)
    {narrow : Set ℝ} (h : ProfileSupport rowDomain heightDomain narrow d) :
    RawProfileWindow rowDomain heightDomain narrow orders d budget :=
  { w with
    inverse_support := fun u hu t ht y hy =>
      h.inverse u hu t ht (by simpa only [w.inverse_eq] using hy)
    left_support := fun u hu t ht y hy =>
      h.left u hu t ht (by simpa only [w.left_eq] using hy)
    right_support := fun u hu t ht y hy =>
      h.right u hu t ht (by simpa only [w.right_eq] using hy)
    prime_support := fun i t ht y hy =>
      h.prime i t ht (by simpa only [w.prime_eq] using hy) }

private theorem original_subset {lo hi : ℝ} (hlo : 0 ≤ lo) (hhi : 1 ≤ hi) :
    Set.Icc lo hi ⊆ Set.Icc (lo / hi) hi := by
  have hdiv : lo / hi ≤ lo := by
    simpa only [div_one] using
      div_le_div_of_nonneg_left hlo (show (0 : ℝ) < 1 by norm_num) hhi
  intro y hy
  exact ⟨hdiv.trans hy.1, hy.2⟩

private theorem dilation_mem {lo hi c y : ℝ} (hlo : 0 ≤ lo)
    (hhi : 1 ≤ hi) (hc : 1 ≤ c) (hcHi : c ≤ hi)
    (hy : c * y ∈ Set.Icc lo hi) : y ∈ Set.Icc (lo / hi) hi := by
  have hcPos : 0 < c := zero_lt_one.trans_le hc
  have hlow : lo / c ≤ y :=
    (div_le_iff₀ hcPos).mpr (by simpa only [mul_comm] using hy.1)
  have hupp : y ≤ hi / c :=
    (le_div_iff₀ hcPos).mpr (by simpa only [mul_comm] using hy.2)
  have hdiv : hi / c ≤ hi := by
    simpa only [div_one] using
      div_le_div_of_nonneg_left (zero_le_one.trans hhi)
        (show (0 : ℝ) < 1 by norm_num) hc
  exact ⟨(div_le_div_of_nonneg_left hlo hcPos hcHi).trans hlow, hupp.trans hdiv⟩

/-- The actual clipping formula has support in `[lo / hi, hi]` when
both actual dilation factors are at most `hi`. No profile is replaced. -/
theorem clipped_support (p : RealParameters) (Z : ℝ) (hZ : 1 ≤ Z)
    {lo hi : ℝ} (hlo : 0 ≤ lo) (hhi : 1 ≤ hi)
    (h : ProfileSupport rowDomain heightDomain (Set.Icc lo hi) d)
    (hleft : plainClippingFactor Z p.n₁ ≤ hi)
    (hright : plainClippingFactor Z p.n₂ ≤ hi) :
    ProfileSupport rowDomain heightDomain (Set.Icc (lo / hi) hi)
      (clipPlainData d p Z (zero_lt_one.trans_le hZ)) where
  inverse u hu t ht := (h.inverse u hu t ht).trans (original_subset hlo hhi)
  left u hu t ht y hy := by
    change (Real.sqrt (plainClippingFactor Z p.n₁) : ℂ) *
      d.plainTest₁.profile u t (plainClippingFactor Z p.n₁ * y) ≠ 0 at hy
    exact dilation_mem hlo hhi (plainClippingFactor_one_le Z p.n₁ hZ) hleft
      (h.left u hu t ht (right_ne_zero_of_mul hy))
  right u hu t ht y hy := by
    change (Real.sqrt (plainClippingFactor Z p.n₂) : ℂ) *
      d.plainTest₂.profile u t (plainClippingFactor Z p.n₂ * y) ≠ 0 at hy
    exact dilation_mem hlo hhi (plainClippingFactor_one_le Z p.n₂ hZ) hright
      (h.right u hu t ht (right_ne_zero_of_mul hy))
  prime i t ht := (h.prime i t ht).trans (original_subset hlo hhi)

/-- One genuine nonzero original row bounds both dilation factors.
This is the ideal norm bound already used by the single-step owner. -/
theorem clipping_factors_le_of_nonzero
    (p : RealParameters) (Z t : ℝ) (hZ : 1 < Z)
    {lo hi : ℝ} (hhi : 1 ≤ hi)
    (w : RawProfileWindow rowDomain heightDomain (Set.Icc lo hi) orders d budget)
    (hrows : ∀ u ∈ pairedRows d p Z, u ∈ rowDomain) (ht : t ∈ heightDomain)
    (hne : pairedEnergy d p Z t ≠ 0) :
    plainClippingFactor Z p.n₁ ≤ hi ∧ plainClippingFactor Z p.n₂ ≤ hi := by
  obtain ⟨u, hu, hleft, hright⟩ := nonzero_pairedEnergy_plain_witness d p Z t hne
  have hleftAnnulus : ∀ y, d.plainTest₁.profile u t y ≠ 0 → y ≤ hi := by
    intro y hy
    rw [w.left_eq] at hy
    exact (w.left_support u (hrows u hu) t ht hy).2
  have hrightAnnulus : ∀ y, d.plainTest₂.profile u t y ≠ 0 → y ≤ hi := by
    intro y hy
    rw [w.right_eq] at hy
    exact (w.right_support u (hrows u hu) t ht hy).2
  exact ⟨clipping_factor_le_of_nonempty_support d.plainTest₁ u Z p.n₁ t hi hZ hhi
      hleftAnnulus (plainPolynomial_support_nonempty d d.plainTest₁ u _ t hleft),
    clipping_factor_le_of_nonempty_support d.plainTest₂ u Z p.n₂ t hi hZ hhi
      hrightAnnulus (plainPolynomial_support_nonempty d d.plainTest₂ u _ t hright)⟩

/-- Strengthen the support of an already constructed clipped window,
retaining its original radius and its original finite seminorm orders. -/
def narrowClippedWindow (p : RealParameters) (Z : ℝ) (hZ : 1 ≤ Z)
    {lo hi : ℝ} (hlo : 0 ≤ lo) (hhi : 1 ≤ hi)
    (original : RawProfileWindow rowDomain heightDomain (Set.Icc lo hi) orders d budget)
    {clippedOrders : Finset (ℕ × ℕ)} {clippedBudget : ℝ} {broad : Set ℝ}
    (clipped : RawProfileWindow rowDomain heightDomain broad clippedOrders
      (clipPlainData d p Z (zero_lt_one.trans_le hZ)) clippedBudget)
    (hleft : plainClippingFactor Z p.n₁ ≤ hi)
    (hright : plainClippingFactor Z p.n₂ ≤ hi) :
    RawProfileWindow rowDomain heightDomain (Set.Icc (lo / hi) hi) clippedOrders
      (clipPlainData d p Z (zero_lt_one.trans_le hZ)) clippedBudget :=
  windowWithSupport clipped
    (clipped_support p Z hZ hlo hhi (rawWindow_support original) hleft hright)

section ActiveCapacityChild

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {k : ℕ} {source : ActualAllocatedSource A V H k}
variable {cal : source.Calibration (σ := σ) ω ψ}
variable {capacity : cal.NormalizedCapacityData}

/-- Positive normalization does not enlarge any literal prime support. -/
theorem normalized_prime_support (model : MomentData K ω ψ) (B : ℝ) (hB : 0 < B)
    {primeWindow : Set ℝ}
    (h : ∀ i t, Function.support ((model.geometry.slots i).profile t) ⊆ primeWindow) :
    ∀ i t, Function.support
      (((normalizedMomentProfiles model B hB).geometry.slots i).profile t) ⊆ primeWindow := by
  intro i t y hy
  change ((B⁻¹ : ℝ) : ℂ) * (model.geometry.slots i).profile t y ≠ 0 at hy
  exact h i t (right_ne_zero_of_mul hy)

/-- The original prime support survives the same fixed capacity slot
selection and the same literal positive normalization. This holds even
before the inactive-source branches are discarded. -/
theorem child_prime_support (out : capacity.Child) {primeWindow : Set ℝ}
    (h : ∀ ξ i t,
      Function.support (((cal.data ξ).geometry.slots i).profile t) ⊆ primeWindow) :
    ∀ ξ i t, Function.support (((out.data ξ).geometry.slots i).profile t) ⊆ primeWindow := by
  intro ξ
  rw [out.data_eq_normalized_raw]
  apply normalized_prime_support _ (capacity.radius ξ) (capacity.radius_pos ξ)
  intro i t
  exact h ξ
    (selectedSlotIndex
      (lengthSelection (cal.clippedData ξ) source.allocation.keep.card
        (cal.count ξ) (Finset.univ \ out.removed)) i) t

/-- Freezing the actual child retains the stronger original prime
window, including the strict `(1, 2)` window required at the next call. -/
theorem frozen_child_prime_support (out : capacity.Child) {primeWindow : Set ℝ}
    (h : ∀ ξ i t,
      Function.support (((cal.data ξ).geometry.slots i).profile t) ⊆ primeWindow) :
    ∀ ξ i t, Function.support (((out.frozenData ξ).geometry.slots i).profile t) ⊆ primeWindow := by
  intro ξ i t y hy
  change ((out.data ξ).geometry.slots i).profile (cal.height ξ) y *
    profilePower 0 y ≠ 0 at hy
  rw [profilePower_zero, mul_one] at hy
  exact child_prime_support out h ξ i (cal.height ξ) hy

/-- Only support at the actual original evaluation height is needed
for a frozen output. This is the form exposed by the full-kappa input. -/
theorem frozen_child_prime_support_at (out : capacity.Child) {primeWindow : Set ℝ}
    (h : ∀ ξ i, Function.support
      (((cal.data ξ).geometry.slots i).profile (cal.height ξ)) ⊆ primeWindow) :
    ∀ ξ i t, Function.support (((out.frozenData ξ).geometry.slots i).profile t) ⊆ primeWindow := by
  have hchild : ∀ ξ i, Function.support
      (((out.data ξ).geometry.slots i).profile (cal.height ξ)) ⊆ primeWindow := by
    intro ξ
    rw [out.data_eq_normalized_raw]
    intro i y hy
    change (((capacity.radius ξ)⁻¹ : ℝ) : ℂ) *
      ((cal.data ξ).geometry.slots
        (selectedSlotIndex
          (lengthSelection (cal.clippedData ξ) source.allocation.keep.card
            (cal.count ξ) (Finset.univ \ out.removed)) i)).profile (cal.height ξ) y ≠ 0 at hy
    exact h ξ _ (right_ne_zero_of_mul hy)
  intro ξ i t y hy
  change ((out.data ξ).geometry.slots i).profile (cal.height ξ) y *
    profilePower 0 y ≠ 0 at hy
  rw [profilePower_zero, mul_one] at hy
  exact hchild ξ i hy

/-- The active-source predicate supplies the one nonzero member used
to bound clipping. The same factors apply at every Fourier value. -/
theorem active_clipping_factors
    {lo hi : ℝ} (hhi : 1 ≤ hi) {originalBudget : V → ℝ}
    (original : ∀ ξ, RawProfileWindow rowDomain heightDomain (Set.Icc lo hi)
      orders (cal.data ξ) (originalBudget ξ))
    (hrows : ∀ ξ, ∀ u ∈ pairedRows (cal.data ξ) cal.parameters source.base,
      u ∈ rowDomain)
    (htime : ∀ ξ, cal.height ξ ∈ heightDomain)
    (hactive : ¬ ∀ ξ, source.energy (σ := σ) ξ = 0) :
    plainClippingFactor source.base cal.parameters.n₁ ≤ hi ∧
      plainClippingFactor source.base cal.parameters.n₂ ≤ hi := by
  obtain ⟨ξ₀, hne⟩ := not_forall.mp hactive
  have henergy : pairedEnergy (cal.data ξ₀) cal.parameters source.base (cal.height ξ₀) ≠ 0 := by
    intro hz
    have hbound := cal.energy_le ξ₀
    rw [hz, mul_zero] at hbound
    exact hne (le_antisymm hbound (source.energy_nonneg (σ := σ) ξ₀))
  exact clipping_factors_le_of_nonzero cal.parameters source.base (cal.height ξ₀)
    source.base_gt_one hhi (original ξ₀) (hrows ξ₀) (htime ξ₀) henergy

/-- Positive support for the already selected capacity child. The raw
normalization radius and the one fixed removed-slot set are unchanged. -/
theorem active_child_windows
    (out : capacity.Child) {lo hi : ℝ} (hlo : 0 ≤ lo) (hhi : 1 ≤ hi)
    {originalBudget : V → ℝ}
    (original : ∀ ξ, RawProfileWindow rowDomain heightDomain (Set.Icc lo hi)
      orders (cal.data ξ) (originalBudget ξ))
    {childOrders : Finset (ℕ × ℕ)} {broad : Set ℝ}
    (clipped : ∀ ξ, RawProfileWindow rowDomain heightDomain broad childOrders
      (cal.clippedData ξ) (capacity.radius ξ))
    (hrows : ∀ ξ, ∀ u ∈ pairedRows (cal.data ξ) cal.parameters source.base,
      u ∈ rowDomain)
    (htime : ∀ ξ, cal.height ξ ∈ heightDomain)
    (hactive : ¬ ∀ ξ, source.energy (σ := σ) ξ = 0) (ξ : V) :
    InFixedProfileWindow rowDomain heightDomain (Set.Icc (lo / hi) hi)
        childOrders (out.data ξ) ∧
      InFixedProfileWindow rowDomain Set.univ (Set.Icc (lo / hi) hi)
        childOrders (out.frozenData ξ) := by
  obtain ⟨hleft, hright⟩ := active_clipping_factors hhi original hrows htime hactive
  let narrow := narrowClippedWindow cal.parameters source.base source.base_gt_one.le
    hlo hhi (original ξ) (clipped ξ) hleft hright
  have hchild : InFixedProfileWindow rowDomain heightDomain (Set.Icc (lo / hi) hi)
      childOrders (out.data ξ) := by
    rw [out.data_eq_normalized_raw]
    apply normalizedMomentProfiles_in_fixed_window (capacity.radius_pos ξ)
    exact narrow.restrictSlots
      (lengthSelection (cal.clippedData ξ) source.allocation.keep.card
        (cal.count ξ) (Finset.univ \ out.removed))
  refine ⟨hchild, ?_⟩
  obtain ⟨raw⟩ := hchild
  exact ⟨raw.freezeTime (cal.height ξ) (htime ξ)⟩

end ActiveCapacityChild

end HeckeSkeleton.Moments.EngineInduction.ActiveChildAnnulus

#print axioms HeckeSkeleton.Moments.EngineInduction.ActiveChildAnnulus.clipped_support
#print axioms HeckeSkeleton.Moments.EngineInduction.ActiveChildAnnulus.active_child_windows
#print axioms HeckeSkeleton.Moments.EngineInduction.ActiveChildAnnulus.frozen_child_prime_support
