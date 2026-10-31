import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# The arithmetic ledger of one paired fourth-moment descent

These inequalities are the field-independent exponent calculations of §4.8.
The weights in the finite sums may be the actual logarithmic prime norms;
no equal-norm approximation is used.  The first- and second-saving formulas
are adapted from `openai/math`, `Moments/DescentLedger.lean` and
`Moments/SecondLedger.lean`, to an arbitrary nonnegative weighted support.
-/

namespace HeckeSkeleton.Moments.EngineStep

noncomputable section
open scoped BigOperators

/-- The radical indicator for a nonzero exponent modulo six. -/
def exponentRadical (i j : ℕ) : ℝ := if i % 6 = j % 6 then 0 else 1

theorem exponentRadical_cases (i j : ℕ) :
    exponentRadical i j = 0 ∨ exponentRadical i j = 1 := by
  unfold exponentRadical
  split_ifs <;> simp

@[simp] theorem exponentRadical_self (i : ℕ) : exponentRadical i i = 0 := by
  simp [exponentRadical]

theorem exponentRadical_symm (i j : ℕ) : exponentRadical i j = exponentRadical j i := by
  simp [exponentRadical, eq_comm]

/-- The ordered local allowance, including the equal-multiplicity case. -/
theorem local_allowance_ordered (i j : ℕ) (hji : j ≤ i) (hj : 1 ≤ j)
    (r : ℝ) (hr : r = 0 ∨ r = 1) (hdiag : i = j → r = 0) :
    max ((3 * (i : ℝ) - 5 * (j : ℝ) - r) / 6) 0 ≤
      (i : ℝ) + (j : ℝ) - 2 - r := by
  have hir : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast le_trans hj hji
  have hjr : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  rcases hr with rfl | rfl
  · apply max_le <;> linarith
  · have hne : i ≠ j := by
      intro hij
      have := hdiag hij
      norm_num at this
    have hstep : j + 1 ≤ i := by omega
    have hstepr : (j : ℝ) + 1 ≤ (i : ℝ) := by exact_mod_cast hstep
    apply max_le <;> linarith

/-- Both local Cauchy allowances fit in the complete-support saving. -/
theorem local_paired_allowance (i j : ℕ) (hi : 1 ≤ i) (hj : 1 ≤ j)
    (r : ℝ) (hr : r = 0 ∨ r = 1) (hdiag : i = j → r = 0) :
    max ((3 * (i : ℝ) - 5 * (j : ℝ) - r) / 6) 0 +
      max ((3 * (j : ℝ) - 5 * (i : ℝ) - r) / 6) 0 ≤
        (i : ℝ) + (j : ℝ) - 2 - r := by
  have hr0 : 0 ≤ r := by rcases hr with rfl | rfl <;> norm_num
  have hir : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
  have hjr : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  rcases le_total j i with hji | hij
  · have hle : (j : ℝ) ≤ (i : ℝ) := by exact_mod_cast hji
    have hzero : (3 * (j : ℝ) - 5 * (i : ℝ) - r) / 6 ≤ 0 := by linarith
    rw [max_eq_right hzero, add_zero]
    exact local_allowance_ordered i j hji hj r hr hdiag
  · have hle : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
    have hzero : (3 * (i : ℝ) - 5 * (j : ℝ) - r) / 6 ≤ 0 := by linarith
    rw [max_eq_right hzero, zero_add]
    have h := local_allowance_ordered j i hij hi r hr (fun h => hdiag h.symm)
    linarith

/-- The positive-part allowance in the first transform. -/
def firstAllowance (c d R : ℝ) : ℝ := max ((3 * c - 5 * d - R) / 6) 0

theorem firstAllowance_nonneg (c d R : ℝ) : 0 ≤ firstAllowance c d R :=
  le_max_right _ _

theorem weighted_firstAllowance_le {ι : Type*} (S : Finset ι)
    (w c d r : ι → ℝ) (hw : ∀ i ∈ S, 0 ≤ w i) :
    firstAllowance (∑ i ∈ S, w i * c i) (∑ i ∈ S, w i * d i)
        (∑ i ∈ S, w i * r i) ≤
      ∑ i ∈ S, w i * firstAllowance (c i) (d i) (r i) := by
  apply max_le
  · calc
      _ = ∑ i ∈ S, (3 * (w i * c i) - 5 * (w i * d i) - w i * r i) / 6 := by
        simp only [Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum]
      _ = ∑ i ∈ S, w i * ((3 * c i - 5 * d i - r i) / 6) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (le_max_left _ _) (hw i hi)
  · exact Finset.sum_nonneg (fun i hi => mul_nonneg (hw i hi) (firstAllowance_nonneg _ _ _))

/-- Summation with the actual logarithmic prime norms preserves the allowance. -/
theorem weighted_paired_allowance {ι : Type*} (S : Finset ι)
    (w : ι → ℝ) (i j : ι → ℕ)
    (hw : ∀ p ∈ S, 0 ≤ w p) (hi : ∀ p ∈ S, 1 ≤ i p)
    (hj : ∀ p ∈ S, 1 ≤ j p) :
    let c := ∑ p ∈ S, w p * (i p : ℝ)
    let d := ∑ p ∈ S, w p * (j p : ℝ)
    let q := ∑ p ∈ S, w p
    let R := ∑ p ∈ S, w p * exponentRadical (i p) (j p)
    firstAllowance c d R + firstAllowance d c R ≤ c + d - 2 * q - R := by
  dsimp only
  have hc := weighted_firstAllowance_le S w (fun p => (i p : ℝ))
    (fun p => (j p : ℝ)) (fun p => exponentRadical (i p) (j p)) hw
  have hd := weighted_firstAllowance_le S w (fun p => (j p : ℝ))
    (fun p => (i p : ℝ)) (fun p => exponentRadical (i p) (j p)) hw
  calc
    _ ≤ (∑ p ∈ S, w p * firstAllowance (i p) (j p) (exponentRadical (i p) (j p))) +
        (∑ p ∈ S, w p * firstAllowance (j p) (i p) (exponentRadical (i p) (j p))) :=
      add_le_add hc hd
    _ = ∑ p ∈ S, w p * (firstAllowance (i p) (j p) (exponentRadical (i p) (j p)) +
        firstAllowance (j p) (i p) (exponentRadical (i p) (j p))) := by
      simp only [mul_add, Finset.sum_add_distrib]
    _ ≤ ∑ p ∈ S, w p * ((i p : ℝ) + (j p : ℝ) - 2 - exponentRadical (i p) (j p)) := by
      apply Finset.sum_le_sum
      intro p hp
      apply mul_le_mul_of_nonneg_left _ (hw p hp)
      exact local_paired_allowance (i p) (j p) (hi p hp) (hj p hp)
        (exponentRadical (i p) (j p)) (exponentRadical_cases _ _)
        (by intro hij; simp [hij])
    _ = _ := by
      simp only [mul_sub, mul_add, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.sum_mul]
      ring

theorem first_outer_allowance (M c d p R : ℝ)
    (h : firstAllowance c d R + firstAllowance d c R ≤ c + d - 2 * p - R) :
    M + (firstAllowance c d R + firstAllowance d c R - (c + d - 2 * p - R)) / 2 ≤ M := by
  linarith

theorem weighted_first_outer_allowance {ι : Type*} (S : Finset ι)
    (w : ι → ℝ) (i j : ι → ℕ) (M : ℝ)
    (hw : ∀ p ∈ S, 0 ≤ w p) (hi : ∀ p ∈ S, 1 ≤ i p)
    (hj : ∀ p ∈ S, 1 ≤ j p) :
    let c := ∑ p ∈ S, w p * (i p : ℝ)
    let d := ∑ p ∈ S, w p * (j p : ℝ)
    let q := ∑ p ∈ S, w p
    let R := ∑ p ∈ S, w p * exponentRadical (i p) (j p)
    M + (firstAllowance c d R + firstAllowance d c R - (c + d - 2 * q - R)) / 2 ≤ M := by
  exact first_outer_allowance M _ _ _ _ (weighted_paired_allowance S w i j hw hi hj)

/-- Each genuine common prime appears at least once on both sides. -/
theorem weighted_radical_le_half {ι : Type*} (S : Finset ι)
    (w : ι → ℝ) (c d : ι → ℕ) (hw : ∀ i ∈ S, 0 ≤ w i)
    (hc : ∀ i ∈ S, 1 ≤ c i) (hd : ∀ i ∈ S, 1 ≤ d i) :
    (∑ i ∈ S, w i) ≤
      ((∑ i ∈ S, w i * (c i : ℝ)) + (∑ i ∈ S, w i * (d i : ℝ))) / 2 := by
  calc
    _ ≤ ∑ i ∈ S, (w i * (c i : ℝ) + w i * (d i : ℝ)) / 2 := by
      apply Finset.sum_le_sum
      intro i hi
      have hcr : (1 : ℝ) ≤ c i := by exact_mod_cast hc i hi
      have hdr : (1 : ℝ) ≤ d i := by exact_mod_cast hd i hi
      nlinarith [hw i hi]
    _ = _ := by simp only [Finset.sum_div, Finset.sum_add_distrib]

/-- The unit radical lies inside the genuine common gcd. -/
theorem weighted_unit_le_gcd {ι : Type*} (S U : Finset ι) (hU : U ⊆ S)
    (w : ι → ℝ) (c d : ι → ℕ) (hw : ∀ i ∈ S, 0 ≤ w i)
    (hc : ∀ i ∈ S, 1 ≤ c i) (hd : ∀ i ∈ S, 1 ≤ d i) :
    (∑ i ∈ U, w i) ≤ ∑ i ∈ S, w i * (min (c i) (d i) : ℕ) := by
  calc
    _ ≤ ∑ i ∈ S, w i :=
      Finset.sum_le_sum_of_subset_of_nonneg hU (fun i hi hni => hw i hi)
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i hi
      have hm : (1 : ℝ) ≤ (min (c i) (d i) : ℕ) := by
        exact_mod_cast le_min (hc i hi) (hd i hi)
      nlinarith [hw i hi]

/-- The two explicit child lengths have precisely the declared effective width. -/
theorem child_width_identity (A m q c d R E K w wo g g₂ t₂ V : ℝ) :
    let a₀ := A - c - w
    let K₀ := 2 * A - c - d + R + E - m
    let J := d - c + (K₀ - K) - 2 * w + wo
    let m' := 2 * a₀ - K - g - g₂ - V
    let q' := q + R + E + wo + t₂ + V
    m' + q' = m + q + J - g - g₂ + t₂ := by
  dsimp only
  ring

/-- A single enlargement gives a strict descent, independently of slot count. -/
theorem child_width_drop (M J g g₂ t₂ σ m' q' : ℝ)
    (hwidth : m' + q' = M + J - g - g₂ + t₂)
    (hg : J + σ ≤ g) (hcommon : t₂ ≤ g₂) :
    m' + q' ≤ M - σ := by linarith

theorem direct_enlargement_drop (M J g₂ t₂ σ : ℝ) (hcommon : t₂ ≤ g₂) :
    M + J - (max J 0 + σ) - g₂ + t₂ ≤ M - σ := by
  have := le_max_left J 0
  linarith

theorem pool_enlargement_drop (M J g₂ t₂ σ : ℝ) (hcommon : t₂ ≤ g₂) :
    M + J - (max J 0 + 2 * σ) - g₂ + t₂ ≤ M - 2 * σ := by
  have := le_max_left J 0
  linarith

/-- Clipping a nonempty subunit dyad is charged to its actual boundary error. -/
theorem clipped_width_drop (M J g g₂ t₂ σ m' q' δ : ℝ)
    (hwidth : m' + q' = M + J - g - g₂ + t₂)
    (hg : J + σ ≤ g) (hcommon : t₂ ≤ g₂) (hne : 0 ≤ m' + δ) :
    max 0 (m' + δ) + q' ≤ M - σ + δ := by
  rw [max_eq_right hne]
  linarith

theorem clipped_width_drop_half (M J g g₂ t₂ σ m' q' δ : ℝ)
    (hwidth : m' + q' = M + J - g - g₂ + t₂)
    (hg : J + σ ≤ g) (hcommon : t₂ ≤ g₂) (hne : 0 ≤ m' + δ)
    (hδ : δ ≤ σ / 2) :
    max 0 (m' + δ) + q' ≤ M - σ / 2 := by
  have := clipped_width_drop M J g g₂ t₂ σ m' q' δ hwidth hg hcommon hne
  linarith

theorem child_allowance_lower (b₂ p₂ w B ell : ℝ) (hbp : p₂ ≤ b₂) (hB : 0 ≤ B) :
    w + ell ≤ b₂ - p₂ + w + B + ell := by linarith

/-- The exact prefactor computation, retaining the pool density exactly once. -/
theorem inner_allowance_identity (a₀ q wo w B s₀ K g ell p₂ g₂ t₂ b₂ V : ℝ) :
    (a₀ + q + wo + w + B - s₀) - (K + g - ell - a₀ + p₂ - s₀ + g₂ - t₂ - b₂) =
      (2 * a₀ - K - g - g₂ - V) + (q + wo + t₂ + V) +
        (b₂ - p₂ + w + B + ell) := by ring

theorem capacity_removal_cost (κ dz F w ell Δ error η : ℝ)
    (hF : F ≤ 6 * (w + ell) + error)
    (hcost : κ * dz ≤ F / 6 + κ * η) (hΔ : w + ell ≤ Δ) :
    κ * dz ≤ Δ + error / 6 + κ * η := by linarith

/-- Removing a live slot also removes its contribution to the total degree. -/
theorem allocation_pays_live_slots (κ z zlive reduction : ℝ)
    (hκ : 0 ≤ κ) (hlive : zlive ≤ z) (hreduction : z - zlive ≤ reduction) :
    -reduction + (6 * κ - 1) * zlive ≤ (6 * κ - 1) * z := by
  nlinarith

/-- Actual clipping errors are included before measuring the capacity defect. -/
theorem allocated_capacity_defect (A M Mnom Mact Anom Aact z zlive reduction κ
    w ell δ clip : ℝ)
    (hκ : 0 ≤ κ) (hlive : zlive ≤ z) (hreduction : z - zlive ≤ reduction)
    (hparent : A + (6 * κ - 1) * z ≤ M)
    (hshift : Anom - Mnom ≤ A - M + 6 * (w + ell) + δ)
    (hwidth : Mnom ≤ Mact) (hclip : Aact ≤ Anom - reduction + clip)
    (herror : 0 ≤ 6 * (w + ell) + δ + clip) :
    max (Aact - Mact + (6 * κ - 1) * zlive) 0 ≤
      6 * (w + ell) + δ + clip := by
  have hslots := allocation_pays_live_slots κ z zlive reduction hκ hlive hreduction
  apply max_le
  · linarith
  · exact herror

/-- Both Cauchy sides pay for slot removal from the same child allowance. -/
theorem paired_edge_cost (shell width₁ width₂ cost₁ cost₂ w ell δ₁ δ₂ θ κ mesh : ℝ)
    (hs : shell ≤ 2 * θ) (hwidth₁ : width₁ ≤ δ₂) (hwidth₂ : width₂ ≤ δ₂)
    (hc₁ : cost₁ ≤ w + ell + δ₁ / 6 + θ / 3 + κ * mesh)
    (hc₂ : cost₂ ≤ w + ell + δ₁ / 6 + θ / 3 + κ * mesh) :
    shell + (width₁ + width₂) / 2 + (cost₁ + cost₂) / 2 - (w + ell) ≤
      δ₂ + δ₁ / 6 + κ * mesh + 7 * θ / 3 := by linarith

theorem edge_loss_budget (δ₁ δ₂ θ κ mesh ξ η : ℝ)
    (hδ₁ : δ₁ ≤ ξ) (hδ₂ : δ₂ ≤ ξ) (hθ : θ ≤ ξ) (hκ : κ ≤ 1)
    (hm : 0 ≤ mesh) (hmesh : mesh ≤ η) :
    δ₂ + δ₁ / 6 + κ * mesh + 7 * θ / 3 ≤ 7 * ξ / 2 + η := by nlinarith

/-- The three error valuations in one sixth-power prime amplification. -/
inductive AmplifierValuation where
  | one
  | six
  | seven
  deriving DecidableEq

def AmplifierValuation.multiplicity : AmplifierValuation → ℕ
  | .one => 1
  | .six => 6
  | .seven => 7

def AmplifierValuation.movingMultiplicity : AmplifierValuation → ℕ
  | .one => 1
  | .six => 0
  | .seven => 1

/-- These are the squared central coefficients prescribed by the complete local table. -/
def AmplifierValuation.squaredCentral (e : AmplifierValuation) (P : ℝ) : ℝ :=
  match e with
  | .one => P⁻¹
  | .six => (1 - P⁻¹) ^ 2
  | .seven => P⁻¹

theorem amplifier_error_moving_le (e : AmplifierValuation) (ell : ℝ) (hell : 0 ≤ ell) :
    (e.movingMultiplicity : ℝ) * ell ≤ (e.multiplicity : ℝ) * ell := by
  cases e <;> simp only [AmplifierValuation.movingMultiplicity,
    AmplifierValuation.multiplicity, Nat.cast_zero, Nat.cast_one,
    Nat.cast_ofNat, zero_mul, one_mul] <;> linarith

theorem amplifier_error_length_le (e : AmplifierValuation) (ell σ : ℝ)
    (hell : 0 ≤ ell) (hupper : ell ≤ σ / 3) :
    (e.multiplicity : ℝ) * ell ≤ 7 * σ / 3 := by
  cases e <;> simp only [AmplifierValuation.multiplicity, Nat.cast_ofNat,
    Nat.cast_one, one_mul] <;> linarith

theorem amplifier_error_squared_nonneg (e : AmplifierValuation) (P : ℝ) (hP : 0 < P) :
    0 ≤ e.squaredCentral P := by
  cases e <;> simp only [AmplifierValuation.squaredCentral] <;> positivity

theorem amplifier_error_squared_le_one (e : AmplifierValuation) (P : ℝ) (hP : 1 ≤ P) :
    e.squaredCentral P ≤ 1 := by
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have hi0 : 0 ≤ P⁻¹ := inv_nonneg.mpr hPpos.le
  have hi1 : P⁻¹ ≤ 1 := (inv_le_one₀ hPpos).mpr hP
  cases e <;> simp only [AmplifierValuation.squaredCentral]
  · exact hi1
  · nlinarith
  · exact hi1

/-- Exact nominal capacity change: the moving-support term occurs once. -/
theorem nominal_capacity_shift_identity
    (A m q c d R E K w wo g g₂ t₂ V c₂ : ℝ) :
    let K₀ := 2 * A - c - d + R + E - m
    let D₀ := d + K₀ - K
    let m' := 2 * (A - c - w) - K - g - g₂ - V
    let q' := q + R + E + wo + t₂ + V
    (A - c - w - c₂) - (m' + q') - (A - (m + q)) =
      g + w - D₀ - wo + g₂ - t₂ - c₂ := by
  dsimp only
  ring

theorem main_capacity_shift (D₀ c σ δ : ℝ)
    (hc : 0 ≤ c) (hD : -δ ≤ D₀) (hδ : 0 ≤ δ) :
    max (D₀ - c) 0 + 2 * σ - D₀ ≤ 6 * (σ / 3) + δ := by
  by_cases h : 0 ≤ D₀ - c
  · rw [max_eq_left h]
    linarith
  · rw [max_eq_right (le_of_not_ge h)]
    linarith

theorem error_capacity_shift_core (D₀ c w wo σ δ : ℝ)
    (hc : 0 ≤ c) (hw : 0 ≤ w) (hwo : wo ≤ w)
    (hD : -δ ≤ D₀) (hδ : 0 ≤ δ) (hscale : σ ≤ 5 * w + wo) :
    max (D₀ - c - 2 * w + wo) 0 + σ + w - D₀ - wo ≤ 6 * w + δ := by
  by_cases h : 0 ≤ D₀ - c - 2 * w + wo
  · rw [max_eq_left h]
    linarith
  · rw [max_eq_right (le_of_not_ge h)]
    linarith

/-- All three error valuations are paid for without a second pool average. -/
theorem amplifier_error_capacity_shift (e : AmplifierValuation) (D₀ c ell σ δ : ℝ)
    (hc : 0 ≤ c) (hell : 0 ≤ ell) (hpool : σ / 6 ≤ ell)
    (hD : -δ ≤ D₀) (hδ : 0 ≤ δ) :
    let w := (e.multiplicity : ℝ) * ell
    let wo := (e.movingMultiplicity : ℝ) * ell
    max (D₀ - c - 2 * w + wo) 0 + σ + w - D₀ - wo ≤ 6 * w + δ := by
  dsimp only
  apply error_capacity_shift_core D₀ c _ _ σ δ hc
  · exact mul_nonneg (Nat.cast_nonneg _) hell
  · exact amplifier_error_moving_le e ell hell
  · exact hD
  · exact hδ
  · cases e <;> simp only [AmplifierValuation.multiplicity,
      AmplifierValuation.movingMultiplicity, Nat.cast_ofNat,
      Nat.cast_zero, Nat.cast_one, zero_mul, one_mul] <;> linarith

/-- Upper-width uncertainty and the positive-part capacity cost are paid together. -/
theorem width_defect_cost (x B δ : ℝ) (hB : 0 ≤ B) (hδ : 0 ≤ δ) (hx : x ≤ δ) :
    x + max (B - x) 0 / 6 ≤ δ + B / 6 := by
  by_cases h : 0 ≤ B - x
  · rw [max_eq_left h]
    linarith
  · rw [max_eq_right (le_of_not_ge h)]
    linarith

/-- The first saving, with actual lengths rather than idealized dyadic endpoints. -/
def firstSaving (c D₀ w q wo B g ell : ℝ) : ℝ :=
  c / 6 + 5 * D₀ / 6 + w / 3 + q / 6 + wo + B - 5 * g / 6 + ell

theorem firstSaving_lower (c d D₀ w q R wo B g ell σ δ : ℝ)
    (hc : 0 ≤ c) (hw : 0 ≤ w) (hq : 0 ≤ q) (hwo : 0 ≤ wo)
    (hB : 0 ≤ B) (hσ : 0 ≤ σ) (hδ : 0 ≤ δ)
    (hR : R ≤ q) (hBcost : max (3 * c - 5 * d - R) 0 / 6 ≤ B)
    (hD : d - δ ≤ D₀) (hg : g ≤ max (D₀ - c - 2 * w + wo) 0 + 2 * σ)
    (hell : 0 ≤ ell) (hwσ : w ≤ 7 * σ / 3) :
    2 * (c + w) / 3 - 3 * σ - 5 * δ / 6 ≤ firstSaving c D₀ w q wo B g ell := by
  have hraw : 3 * c - 5 * d - R ≤ 6 * B := by
    have hm := le_max_left (3 * c - 5 * d - R) 0
    linarith
  have hmax : max (3 * c - 5 * D₀) 0 / 6 - 5 * δ / 6 ≤ B + q / 6 := by
    have hh : max (3 * c - 5 * D₀) 0 ≤ 6 * (B + q / 6) + 5 * δ := by
      apply max_le
      · linarith
      · positivity
    linarith
  unfold firstSaving
  by_cases hJ : 0 ≤ D₀ - c - 2 * w + wo
  · rw [max_eq_left hJ] at hg
    linarith
  · rw [max_eq_right (le_of_not_ge hJ)] at hg
    have hm := le_max_left (3 * c - 5 * D₀) 0
    linarith

/-- The second-transform saving at one genuine common prime. -/
def secondLocalSaving (c d : ℕ) (nonunit : Prop) [Decidable nonunit] : ℝ :=
  (c + d : ℝ) - 5 * (min c d : ℝ) / 6 - 1 +
    (if c = d ∧ ¬ 6 ∣ c ∧ ¬ nonunit then 1 else 0) +
    (if c = d ∧ ¬ 6 ∣ c ∧ nonunit then 1 / 6 else 0) +
    (if c = d ∧ c = 1 ∧ nonunit then 1 / 3 else 0)

theorem secondLocalSaving_lower (c d : ℕ) (hc : 1 ≤ c) (hd : 1 ≤ d)
    (huneq : c ≠ d → 6 ∣ min c d) (nonunit : Prop) [Decidable nonunit] :
    ((c : ℝ) + d) / 3 ≤ secondLocalSaving c d nonunit := by
  by_cases hcd : c = d
  · subst d
    by_cases h6 : 6 ∣ c
    · have hc6 : 6 ≤ c := Nat.le_of_dvd (by omega) h6
      have hn1 : c ≠ 1 := by omega
      simp only [secondLocalSaving, min_self, h6, not_true_eq_false, false_and,
        and_false, ite_false, hn1, add_zero]
      have hcr : (6 : ℝ) ≤ c := by exact_mod_cast hc6
      linarith
    · by_cases hu : nonunit
      · by_cases hc1 : c = 1
        · subst c
          norm_num [secondLocalSaving, hu]
        · have hc2 : 2 ≤ c := by omega
          simp only [secondLocalSaving, min_self, h6, not_false_eq_true, hu,
            not_true_eq_false, and_self, and_false, false_and, ite_false,
            ite_true, hc1, add_zero]
          have hcr : (2 : ℝ) ≤ c := by exact_mod_cast hc2
          linarith
      · simp only [secondLocalSaving, min_self, h6, not_false_eq_true, hu,
          and_false, and_true, ite_false, ite_true, add_zero]
        have hcr : (1 : ℝ) ≤ c := by exact_mod_cast hc
        linarith
  · have hmin : 6 ≤ min c d :=
      Nat.le_of_dvd (lt_of_lt_of_le Nat.zero_lt_one (le_min hc hd)) (huneq hcd)
    have hmr : (6 : ℝ) ≤ min c d := by exact_mod_cast hmin
    have hmc : ((min c d : ℕ) : ℝ) ≤ c := by exact_mod_cast min_le_left c d
    have hmd : ((min c d : ℕ) : ℝ) ≤ d := by exact_mod_cast min_le_right c d
    simp only [Nat.cast_min] at hmr hmc hmd
    simp only [secondLocalSaving, hcd, false_and, ite_false, add_zero]
    linarith

/-- The full second saving bounds two thirds of the half-product length. -/
theorem weighted_secondSaving_lower {ι : Type*} (S : Finset ι)
    (w : ι → ℝ) (c d : ι → ℕ) (nonunit : ι → Prop) [DecidablePred nonunit]
    (hw : ∀ i ∈ S, 0 ≤ w i) (hc : ∀ i ∈ S, 1 ≤ c i)
    (hd : ∀ i ∈ S, 1 ≤ d i)
    (huneq : ∀ i ∈ S, c i ≠ d i → 6 ∣ min (c i) (d i)) :
    ((∑ i ∈ S, w i * (c i : ℝ)) + (∑ i ∈ S, w i * (d i : ℝ))) / 3 ≤
      ∑ i ∈ S, w i * secondLocalSaving (c i) (d i) (nonunit i) := by
  calc
    _ = ∑ i ∈ S, w i * (((c i : ℝ) + d i) / 3) := by
      simp only [mul_div_assoc, mul_add, Finset.sum_div, Finset.sum_add_distrib]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left
        (secondLocalSaving_lower (c i) (d i) (hc i hi) (hd i hi) (huneq i hi) (nonunit i))
        (hw i hi)

theorem exceptional_excess_identity
    (A m q c d R E K w wo B g ell b₂ p₂ g₂ t₂ V f : ℝ) :
    let a₀ := A - c - w
    let K₀ := 2 * A - c - d + R + E - m
    let m' := 2 * a₀ - K - g - g₂ - V
    let q' := q + R + E + wo + t₂ + V
    (m' - f) / 6 + a₀ - b₂ - (m' + q' + (b₂ - p₂ + w + B + ell)) =
      A - 5 * (m + q) / 6 - firstSaving c (d + K₀ - K) w (q + R + E) wo B g ell -
        (2 * b₂ - 5 * g₂ / 6 - p₂ + t₂ + V / 6 + f / 6) := by
  dsimp only [firstSaving]
  ring

theorem uncentered_exceptional_bound (A M c w b₂ F₁ F₂ σ δ : ℝ)
    (hA : A ≤ 5 * M / 6) (hc : 0 ≤ c) (hw : 0 ≤ w) (hb : 0 ≤ b₂)
    (hF₁ : 2 * (c + w) / 3 - 3 * σ - 5 * δ / 6 ≤ F₁)
    (hF₂ : 2 * b₂ / 3 ≤ F₂) :
    A - 5 * M / 6 - F₁ - F₂ ≤ 3 * σ + 5 * δ / 6 := by linarith

/-- Divisor extraction preserves the common centered saving. -/
theorem centered_divisor_identity (t r₁ r₂ r : ℝ) :
    t - r₁ - r₂ - max (r - r₁) 0 = (t - r₂) - max r r₁ := by
  rcases le_total r r₁ with h | h
  · rw [max_eq_right h, max_eq_right (sub_nonpos.mpr h)]
    ring
  · rw [max_eq_left h, max_eq_left (sub_nonneg.mpr h)]
    ring

theorem centered_divisor_saving (t r₁ r₂ r ω : ℝ) (h : t - r₂ ≤ ω) :
    t - r₁ - r₂ - max (r - r₁) 0 ≤ ω - r := by
  rw [centered_divisor_identity]
  have := le_max_left r r₁
  linarith

/-- The centered exceptional excess is controlled in both slot regimes. -/
theorem centered_exceptional_ledger (A M v : ℝ) :
    A - 5 * M / 6 - 2 * v / 3 - max (M / 4 - v) 0 ≤ max (A - M) 0 := by
  have hmax := le_max_left (A - M) 0
  rcases le_total v (M / 4) with hv | hv
  · rw [max_eq_left (sub_nonneg.mpr hv)]
    linarith
  · rw [max_eq_right (sub_nonpos.mpr hv)]
    linarith

theorem centered_exceptional_padded (A M v σ error padding : ℝ)
    (hA : A ≤ M + padding) (hpadding : 0 ≤ padding) :
    A - 5 * M / 6 - 2 * v / 3 - max (M / 4 - v) 0 + 3 * σ + error ≤
      padding + 3 * σ + error := by
  have h := centered_exceptional_ledger A M v
  have hm : max (A - M) 0 ≤ padding := max_le (by linarith) hpadding
  linarith

end
end HeckeSkeleton.Moments.EngineStep

/-! Standalone kernel audit for the arithmetic ledger. -/
#print axioms HeckeSkeleton.Moments.EngineStep.weighted_paired_allowance
#print axioms HeckeSkeleton.Moments.EngineStep.weighted_first_outer_allowance
#print axioms HeckeSkeleton.Moments.EngineStep.child_width_identity
#print axioms HeckeSkeleton.Moments.EngineStep.amplifier_error_capacity_shift
#print axioms HeckeSkeleton.Moments.EngineStep.allocated_capacity_defect
#print axioms HeckeSkeleton.Moments.EngineStep.firstSaving_lower
#print axioms HeckeSkeleton.Moments.EngineStep.secondLocalSaving_lower
#print axioms HeckeSkeleton.Moments.EngineStep.weighted_secondSaving_lower
#print axioms HeckeSkeleton.Moments.EngineStep.exceptional_excess_identity
#print axioms HeckeSkeleton.Moments.EngineStep.centered_divisor_saving
#print axioms HeckeSkeleton.Moments.EngineStep.centered_exceptional_ledger
