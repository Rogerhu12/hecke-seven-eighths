import HeckeSkeleton.Moments.MOM_ENGINE_INDUCTION.BaseTerminal

/-!
# Polynomial height control for the actual width-floor certificates

The common supremum bounds may grow as `B_j * (1 + T)^H_j`.
This file propagates that growth through the explicit ideal-count and
bounded-slot constants of `BaseTerminal`, without choosing a new constant
at each height or each node.  No derivative or Schwartz-order control is
reproved here: those source controls supply the stated profile suprema.

Both rectangles use each plain profile once, and the energy squares that
amplitude.  At most `cap` slots contribute twice their profile height
degree.  The resulting degree is `2*H₁ + 2*H₂ + (2*cap)*Hslots`.
The actual absolute slot exponent in the scale remains `totalLength`.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.EngineInduction

open NumberField HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckePort.CenteredMomentCounting
open scoped BigOperators Classical

universe v

variable {K : Type} [Field K] [NumberField K]

def baseHeightDegree (cap : ℕ) (H₁ H₂ Hslots : ℝ) : ℝ :=
  2 * H₁ + 2 * H₂ + Hslots * (2 * cap : ℕ)

theorem baseHeightDegree_nonneg (cap : ℕ) {H₁ H₂ Hslots : ℝ}
    (hH₁ : 0 ≤ H₁) (hH₂ : 0 ≤ H₂) (hHslots : 0 ≤ Hslots) :
    0 ≤ baseHeightDegree cap H₁ H₂ Hslots := by
  unfold baseHeightDegree
  positivity

theorem plainAbsoluteConstant_height (B X H : ℝ) :
    plainAbsoluteConstant K (B * X ^ H) = plainAbsoluteConstant K B * X ^ H := by
  unfold plainAbsoluteConstant
  ring

/-- The `max 1` in the slot envelope is compatible with polynomial height
growth because `X^H ≥ 1`. -/
theorem uniformSlotAbsoluteConstant_height_le (cap : ℕ) (B X H : ℝ)
    (hX : 1 ≤ X) (hH : 0 ≤ H) :
    uniformSlotAbsoluteConstant K cap (B * X ^ H) ≤
      uniformSlotAbsoluteConstant K cap B * X ^ (H * (2 * cap : ℕ)) := by
  have hX0 : 0 ≤ X := zero_le_one.trans hX
  have hp : 1 ≤ X ^ H := Real.one_le_rpow hX hH
  have hD : 1 ≤ max 1 (primeAbsoluteCountConstant K * B) := le_max_left _ _
  have hmax : max 1 (primeAbsoluteCountConstant K * (B * X ^ H)) ≤
      max 1 (primeAbsoluteCountConstant K * B) * X ^ H := by
    apply max_le
    · simpa only [one_mul] using
        mul_le_mul hD hp zero_le_one (zero_le_one.trans hD)
    · calc
        _ = (primeAbsoluteCountConstant K * B) * X ^ H := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hX0 _)
  calc
    _ ≤ (max 1 (primeAbsoluteCountConstant K * B) * X ^ H) ^ (2 * cap) :=
      pow_le_pow_left₀ (zero_le_one.trans (le_max_left _ _)) hmax _
    _ = _ := by
      rw [mul_pow, ← Real.rpow_mul_natCast hX0 H (2 * cap)] <;> rfl

/-- Exact height growth of both plain factors, followed by the single
uniform slot-envelope estimate.  The coefficient depends only on the
original three supremum constants and the fixed slot-count cap. -/
theorem uniformBaseConstant_height_le (cap : ℕ) (B₁ B₂ Bslots X H₁ H₂ Hslots : ℝ)
    (hX : 1 ≤ X) (hHslots : 0 ≤ Hslots) :
    uniformBaseConstant K cap (B₁ * X ^ H₁) (B₂ * X ^ H₂) (Bslots * X ^ Hslots) ≤
      uniformBaseConstant K cap B₁ B₂ Bslots * X ^ baseHeightDegree cap H₁ H₂ Hslots := by
  have hXpos : 0 < X := zero_lt_one.trans_le hX
  have hC : 0 ≤ idealCountConstant K := zero_le_one.trans (one_le_idealCountConstant K)
  have hpow (H : ℝ) : (X ^ H) ^ 2 = X ^ (2 * H) := by
    rw [← Real.rpow_mul_natCast hXpos.le H 2]
    congr 1
    norm_num <;> ring
  have hplain :
      idealCountConstant K *
          (2 * plainAbsoluteConstant K (B₁ * X ^ H₁) *
            plainAbsoluteConstant K (B₂ * X ^ H₂)) ^ 2 =
        (idealCountConstant K *
          (2 * plainAbsoluteConstant K B₁ * plainAbsoluteConstant K B₂) ^ 2) *
            X ^ (2 * H₁ + 2 * H₂) := by
    rw [plainAbsoluteConstant_height, plainAbsoluteConstant_height,
      Real.rpow_add hXpos (2 * H₁) (2 * H₂)]
    rw [← hpow H₁, ← hpow H₂]
    ring
  calc
    _ = (idealCountConstant K *
          (2 * plainAbsoluteConstant K B₁ * plainAbsoluteConstant K B₂) ^ 2) *
            X ^ (2 * H₁ + 2 * H₂) *
              uniformSlotAbsoluteConstant K cap (Bslots * X ^ Hslots) := by
      unfold uniformBaseConstant nodeAbsoluteConstant
      rw [hplain]
    _ ≤ ((idealCountConstant K *
          (2 * plainAbsoluteConstant K B₁ * plainAbsoluteConstant K B₂) ^ 2) *
            X ^ (2 * H₁ + 2 * H₂)) *
              (uniformSlotAbsoluteConstant K cap Bslots * X ^ (Hslots * (2 * cap : ℕ))) :=
      mul_le_mul_of_nonneg_left
        (uniformSlotAbsoluteConstant_height_le (K := K) cap Bslots X Hslots hX hHslots)
        (by positivity)
    _ = _ := by
      unfold uniformBaseConstant nodeAbsoluteConstant baseHeightDegree
      rw [Real.rpow_add hXpos (2 * H₁ + 2 * H₂) (Hslots * (2 * cap : ℕ))]
      ring

/-- The constants and the height degree precede the moving height, all
characters, every node and every scale.  Only current-height profile
supremum bounds are required; their dependence on the node is unrestricted
inside the one common envelope. -/
theorem uniform_polynomial_height_base_components (cap : ℕ)
    (B₁ B₂ Bslots H₁ H₂ Hslots ρ padding σ boundary : ℝ)
    (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) (hBslots : 0 ≤ Bslots)
    (hH₁ : 0 ≤ H₁) (hH₂ : 0 ≤ H₂) (hHslots : 0 ≤ Hslots) :
    ∃ C H : ℝ,
      C = uniformBaseConstant K cap B₁ B₂ Bslots ∧
      H = baseHeightDegree cap H₁ H₂ Hslots ∧ 0 ≤ C ∧ 0 ≤ H ∧
      ∀ T : ℝ, 0 ≤ T → ∀ {ω ψ : HeckeCharacter K} (n : Node K ω ψ)
        (U t : ℝ), 1 ≤ U → n.data.geometry.slotCount ≤ cap →
        (∀ u ∈ pairedRows n.data n.parameters U,
          Function.support (n.data.plainTest₁.profile u t) ⊆ Set.Iic (2 : ℝ)) →
        (∀ u ∈ pairedRows n.data n.parameters U,
          Function.support (n.data.plainTest₂.profile u t) ⊆ Set.Iic (2 : ℝ)) →
        (∀ u ∈ pairedRows n.data n.parameters U, ∀ y,
          ‖n.data.plainTest₁.profile u t y‖ ≤ B₁ * (1 + T) ^ H₁) →
        (∀ u ∈ pairedRows n.data n.parameters U, ∀ y,
          ‖n.data.plainTest₂.profile u t y‖ ≤ B₂ * (1 + T) ^ H₂) →
        (∀ i, Function.support ((n.data.geometry.slots i).profile t) ⊆ Set.Ioo (1 : ℝ) 2) →
        (∀ i y, ‖(n.data.geometry.slots i).profile t y‖ ≤ Bslots * (1 + T) ^ Hslots) →
        n.parameters.n₁ + n.parameters.n₂ + n.data.geometry.totalLength ≤ ρ + padding + ρ / 6 →
          Nonempty (TerminalComponents.{v} (n.normalizedEnergy U t) U T C H
            ρ padding σ boundary) := by
  refine ⟨uniformBaseConstant K cap B₁ B₂ Bslots, baseHeightDegree cap H₁ H₂ Hslots,
    rfl, rfl, uniformBaseConstant_nonneg (K := K) cap B₁ B₂ Bslots,
    baseHeightDegree_nonneg cap hH₁ hH₂ hHslots, ?_⟩
  intro T hT ω ψ n U t hU hcount hann₁ hann₂ hprof₁ hprof₂ hannSlots hprofSlots hbase
  have hheight : 1 ≤ 1 + T := by linarith
  have hheight0 : 0 ≤ 1 + T := zero_le_one.trans hheight
  have hb₁ : 0 ≤ B₁ * (1 + T) ^ H₁ := mul_nonneg hB₁ (Real.rpow_nonneg hheight0 _)
  have hb₂ : 0 ≤ B₂ * (1 + T) ^ H₂ := mul_nonneg hB₂ (Real.rpow_nonneg hheight0 _)
  have hbs : 0 ≤ Bslots * (1 + T) ^ Hslots :=
    mul_nonneg hBslots (Real.rpow_nonneg hheight0 _)
  refine ⟨n.absoluteBaseComponents U t T
    (B₁ * (1 + T) ^ H₁) (B₂ * (1 + T) ^ H₂)
    (uniformSlotAbsoluteConstant K cap (Bslots * (1 + T) ^ Hslots))
    n.data.geometry.totalLength (uniformBaseConstant K cap B₁ B₂ Bslots)
    (baseHeightDegree cap H₁ H₂ Hslots) ρ padding σ boundary
    (zero_lt_one.trans_le hU) hb₁ hb₂
    (uniformSlotAbsoluteConstant_nonneg (K := K) cap _) hann₁ hann₂ hprof₁ hprof₂
    (fun u _ => slotProduct_sq_uniform_absolute_bound cap _ hbs n.data hcount u U t hU
      hannSlots hprofSlots) hbase ?_⟩
  exact uniformBaseConstant_height_le (K := K) cap B₁ B₂ Bslots (1 + T) H₁ H₂ Hslots
    hheight hHslots

end HeckeSkeleton.Moments.EngineInduction
