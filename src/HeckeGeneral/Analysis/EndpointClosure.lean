import HeckeGeneral.Analysis.FamilySupremum
import OAI.NumberTheory.DirichletL.Endpoint

/-!
# Conditional family closure at seven eighths

These are real-algebra and supremum theorems. The analytic seed and common
strict improvement are explicit parameters; this file does not prove moment
estimates, Mellin continuation, or an unconditional Hecke zero-free theorem.
The saving in `CommonStrictImprovement` is chosen before the family member.
-/

namespace HeckeGeneral.Analysis

noncomputable section

variable {ι : Type*}

/-- The remaining analytic conclusion. The quantifier order `∃ σ, ∀ i` is essential. -/
def CommonStrictImprovement (zeros : ι → Set ℝ) : Prop :=
  ∀ B : ℝ, 7 / 8 < B → B ≤ 11 / 12 →
    (∀ i r, r ∈ zeros i → 1 / 2 ≤ r → r ≤ 1 → r ≤ B) →
    ∃ σ : ℝ, 0 < σ ∧ σ < (B - 7 / 8) / 2 ∧
      ∀ i r, r ∈ zeros i → 1 / 2 ≤ r → r ≤ 1 → r ≤ B - σ

/-- The manuscript only needs improvement at the actual common family supremum. -/
def SupremumStrictImprovement (zeros : ι → Set ℝ) : Prop :=
  7 / 8 < familySupremum zeros → familySupremum zeros ≤ 11 / 12 →
    ∃ σ : ℝ, 0 < σ ∧ σ < (familySupremum zeros - 7 / 8) / 2 ∧
      ∀ i r, r ∈ zeros i → 1 / 2 ≤ r → r ≤ 1 → r ≤ familySupremum zeros - σ

theorem CommonStrictImprovement.at_supremum (zeros : ι → Set ℝ)
    (himprove : CommonStrictImprovement zeros) : SupremumStrictImprovement zeros := by
  intro hlo hhi
  exact himprove (familySupremum zeros) hlo hhi
    (fun i r hr hrlow hrhigh => zero_le_familySupremum zeros hr hrlow hrhigh)

/-- The squared-energy amplification exponent leaves a strict margin at any `β > 11/12`.
This is precisely the exponent conversion used before the source's dyadic continuation. -/
theorem seed_amplification_exponent_margin {β : ℝ} (hβ : 11 / 12 < β) :
    ∃ c ε : ℝ, 0 < c ∧ 0 < ε ∧ 1 / 2 + (5 * (1 + c) / 6 + ε) / 2 < β := by
  refine ⟨(β - 11 / 12) / 2, (β - 11 / 12) / 2, ?_, ?_, ?_⟩ <;> linarith

/-- The source's seed interval forces exactly the fourth-moment parameter range. -/
theorem dynamic_parameter_bounds {B : ℝ} (hlo : 7 / 8 < B) (hhi : B ≤ 11 / 12) :
    0 < B - 7 / 8 ∧ B - 7 / 8 ≤ 1 / 24 ∧
      3 / 4 < 2 * B - 1 ∧ 2 * B - 1 ≤ 5 / 6 ∧
      2 * B - 1 = 3 / 4 + 2 * (B - 7 / 8) := by
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- `eq-sigma`: a real saving independent of the subsequently chosen member. -/
def closureSaving (Δ : ℝ) (J : ℕ) : ℝ :=
  (1 / 8) * min ((51 / 64) * Δ)
    (min (63 / 800) (min (23 / 960) (min (13 / 9600) (7 / (96 * (J : ℝ))))))

theorem closureSaving_pos {Δ : ℝ} {J : ℕ} (hΔ : 0 < Δ) (hJ : 0 < J) :
    0 < closureSaving Δ J := by
  have hJreal : 0 < (J : ℝ) := by exact_mod_cast hJ
  unfold closureSaving
  positivity

theorem closureSaving_lt_half_gap {Δ : ℝ} {J : ℕ} (hΔ : 0 < Δ) :
    closureSaving Δ J < Δ / 2 := by
  have hm := min_le_left ((51 / 64 : ℝ) * Δ)
    (min (63 / 800 : ℝ) (min (23 / 960) (min (13 / 9600) (7 / (96 * (J : ℝ))))))
  unfold closureSaving
  linarith

/-- The exact capacity loss, before the analytic rounding losses are allocated. -/
theorem dynamic_capacity_cost {m q Δ : ℝ}
    (hmlo : 1 / 3 ≤ m) (hmhi : m ≤ 1 / 2)
    (_hqlo : 0 ≤ q) (hqhi : q ≤ 1 / 2) (hΔ : 0 ≤ Δ) :
    2 * q * (1 - 2 * m) * (2 / 9 - 1 / (9 / 2 + 12 * Δ)) ≤ Δ / 4 := by
  have hD : 0 < (9 / 2 : ℝ) + 12 * Δ := by linarith
  have hgap : (2 / 9 : ℝ) - 1 / (9 / 2 + 12 * Δ) =
      ((8 / 3) * Δ) / (9 / 2 + 12 * Δ) := by
    field_simp [ne_of_gt hD]
    ring
  have hgap0 : 0 ≤ (2 / 9 : ℝ) - 1 / (9 / 2 + 12 * Δ) := by
    rw [hgap]
    positivity
  have hgaphi : (2 / 9 : ℝ) - 1 / (9 / 2 + 12 * Δ) ≤ (16 / 27) * Δ := by
    rw [hgap]
    apply (div_le_iff₀ hD).2
    have hnonneg : 0 ≤ ((16 / 27 : ℝ) * Δ) * (12 * Δ) := by positivity
    nlinarith
  have hm0 : 0 ≤ 1 - 2 * m := by linarith
  have hm1 : 1 - 2 * m ≤ (1 / 3 : ℝ) := by linarith
  have hprod := mul_le_mul hqhi hm1 hm0 (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hA : 2 * q * (1 - 2 * m) ≤ (1 / 3 : ℝ) := by linarith
  have hmul := mul_le_mul hA hgaphi hgap0 (by norm_num : (0 : ℝ) ≤ 1 / 3)
  calc
    2 * q * (1 - 2 * m) * (2 / 9 - 1 / (9 / 2 + 12 * Δ)) ≤
        (1 / 3) * ((16 / 27) * Δ) := hmul
    _ ≤ Δ / 4 := by linarith

/-- The source's moderate-row exponent, measured against the endpoint baseline. -/
def moderateExponent (d δ q R : ℝ) : ℝ :=
  -(1 / 48) + (2 / 3) * δ + q / 6 - (13 / 16) * (1 - R) +
    (d - 13 / 16) * (R + δ / 2 - 17 / 50)

/-- The verified upstream certificate survives the dynamic `Δ / 4` row-count loss. -/
theorem dynamic_endpoint_saving {δ y Δ R : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 5 / 6) (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 2)
    (hR : R ≤ OAI.SevenEighths.Endpoint.balancedRowCount δ y + Δ / 4) :
    moderateExponent (13 / 16) δ (δ * (1 / 2 - y)) R - Δ ≤
      -(49 / 440640) - (51 / 64) * Δ := by
  have hmargin := OAI.SevenEighths.Endpoint.balanced_endpoint_margin hδ0 hδ1 hy0 hy1
  unfold moderateExponent OAI.SevenEighths.Endpoint.balancedExponent at *
  linarith

/-- Strictly improving one common family boundary forces that boundary below `7/8`. -/
theorem familySupremum_le_sevenEighths (zeros : ι → Set ℝ)
    (hseed : SeedBound zeros) (himprove : SupremumStrictImprovement zeros) :
    familySupremum zeros ≤ 7 / 8 := by
  by_contra hnot
  have hB : 7 / 8 < familySupremum zeros := lt_of_not_ge hnot
  obtain ⟨σ, hσpos, hσsmall, himproved⟩ := himprove hB (familySupremum_le_seed zeros hseed)
  have hbaseline : 1 / 2 ≤ familySupremum zeros - σ / 2 := by linarith
  have hwitness : familySupremum zeros - σ / 2 < familySupremum zeros := by linarith
  obtain ⟨i, r, hr, hlo, hhi, hnear⟩ := exists_family_zero_above zeros hbaseline hwitness
  have hfar := himproved i r hr hlo hhi
  linarith

theorem familySupremum_le_sevenEighths_of_common_improvement (zeros : ι → Set ℝ)
    (hseed : SeedBound zeros) (himprove : CommonStrictImprovement zeros) :
    familySupremum zeros ≤ 7 / 8 :=
  familySupremum_le_sevenEighths zeros hseed (CommonStrictImprovement.at_supremum zeros himprove)

/-- The global seed also handles any possible zero above the clipping interval. -/
theorem family_zero_le_sevenEighths (zeros : ι → Set ℝ)
    (hseed : SeedBound zeros) (himprove : SupremumStrictImprovement zeros)
    {i : ι} {r : ℝ} (hr : r ∈ zeros i) : r ≤ 7 / 8 := by
  by_contra hnot
  have hgt : 7 / 8 < r := lt_of_not_ge hnot
  have hlo : 1 / 2 ≤ r := by linarith
  have hhi : r ≤ 1 := by have hs := hseed i r hr; linarith
  have hcommon := zero_le_familySupremum zeros hr hlo hhi
  have hclosed := familySupremum_le_sevenEighths zeros hseed himprove
  linarith

theorem family_zeroFree_sevenEighths (zeros : ι → Set ℝ)
    (hseed : SeedBound zeros) (himprove : SupremumStrictImprovement zeros)
    (i : ι) {r : ℝ} (hr : 7 / 8 < r) : r ∉ zeros i := by
  intro hz
  exact (not_le_of_gt hr) (family_zero_le_sevenEighths zeros hseed himprove hz)

end

end HeckeGeneral.Analysis
