import HeckeSkeleton.Moments.MOM_INV_STEP.PrincipalSource
import HeckeSkeleton.Moments.MOM_INV_STEP.Normalization

/-!
# Label mass and the first principal physical budget

The principal source count is the actual one from PrincipalSource. The
old label measure is estimated from its original divisor-power bound.
The remaining input is a pointwise bound on the original summands, which
can retain the real test values and the original mask and mark losses.
No principal-energy or diagonal-count bound is a hypothesis.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.PrincipalBudget

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.ThetaSkeleton
open HeckeSkeleton.Moments.MOMInvStep FixedTripleFibers PrincipalSource
open DedekindZetaZeroFree.LargeSieve
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset

theorem exterior_card_le_norm_count (L : Finset Ext) (Y : ℝ)
    (hL : ∀ f ∈ L, (f.val.val.absNorm : ℝ) ≤ Y) :
    L.card ≤ (boundedNormIdeals K Y).card := by
  let encode (f : L) : boundedNormIdeals K Y :=
    ⟨f.val.val.val, mem_boundedNormIdeals.mpr (hL f.val f.property)⟩
  have hinj : Function.Injective encode := by
    intro f g he
    have hv := congrArg (fun q : boundedNormIdeals K Y => q.val) he
    change f.val.val.val = g.val.val.val at hv
    exact Subtype.ext (exterior_value_injective K S hv)
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective encode hinj

theorem exists_label_mass_bound (p : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (L : Finset Ext) (w : Ext → ℝ) (A Y : ℝ),
      0 ≤ A → 1 ≤ Y →
      (∀ f ∈ L, (f.val.val.absNorm : ℝ) ≤ Y) →
      (∀ f ∈ L, w f ≤ A * ((idealDivisors f.val.val).card : ℝ) ^ p) →
      (∑ f ∈ L, w f) ≤ C * A * Y ^ (1 + ε) := by
  obtain ⟨B, hB, hcount⟩ := exists_ideal_count_bound K
  obtain ⟨C, hC, hdiv⟩ := exists_divisor_power_bound (K := K) (p + 1) (by omega) ε hε
  refine ⟨B * C, one_le_mul_of_one_le_of_one_le hB hC, ?_⟩
  intro L w A Y hA hY hL hw
  have hYpos : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  have hC0 : 0 ≤ C := le_trans zero_le_one hC
  have hpoint (f : Ext) (hf : f ∈ L) : w f ≤ A * C * Y ^ ε := by
    have hp : ((idealDivisors f.val.val).card : ℝ) ^ p ≤
        C * (f.val.val.absNorm : ℝ) ^ ε := by
      apply le_trans _ (hdiv f.val.val)
      apply pow_le_pow_right₀
      · exact_mod_cast divisor_card_pos f.val.val (nonZeroDivisors.coe_ne_zero f.val)
      · omega
    calc
      w f ≤ A * ((idealDivisors f.val.val).card : ℝ) ^ p := hw f hf
      _ ≤ A * (C * (f.val.val.absNorm : ℝ) ^ ε) := mul_le_mul_of_nonneg_left hp hA
      _ ≤ A * (C * Y ^ ε) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (Nat.cast_nonneg _) (hL f hf) hε.le) hC0) hA
      _ = _ := by ring
  have hcard : (L.card : ℝ) ≤ B * Y := by
    have hc : (L.card : ℝ) ≤ ((boundedNormIdeals K Y).card : ℝ) := by
      exact_mod_cast exterior_card_le_norm_count K S L Y hL
    exact hc.trans (hcount Y hY)
  calc
    _ ≤ ∑ _f ∈ L, A * C * Y ^ ε := Finset.sum_le_sum hpoint
    _ = (L.card : ℝ) * (A * C * Y ^ ε) := by simp
    _ ≤ (B * Y) * (A * C * Y ^ ε) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = (B * C) * A * Y ^ (1 + ε) := by
      rw [Real.rpow_add hYpos, Real.rpow_one]
      ring

variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))

/-- The principal source is counted from its actual local conductor.
The summand input is only a pointwise norm control, not an energy bound. -/
theorem exists_weighted_principal_bound (p : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (B N L : Finset Ext) (H X Y A U : ℝ)
      (w : Ext → ℝ) (a : Ext → (Ext × Ext) × (Ext × Ext) → ℂ),
      1 ≤ H → 1 ≤ X → 1 ≤ Y → 0 ≤ A → 0 ≤ U →
      (∀ n ∈ N, Squarefree n.val.val) →
      (∀ b ∈ B, (b.val.val.absNorm : ℝ) ≤ H) →
      (∀ n ∈ N, (n.val.val.absNorm : ℝ) ≤ X) →
      (∀ f ∈ L, (f.val.val.absNorm : ℝ) ≤ Y) →
      (∀ f ∈ L, 0 ≤ w f) →
      (∀ f ∈ L, w f ≤ A * ((idealDivisors f.val.val).card : ℝ) ^ p) →
      (∀ f ∈ L, ∀ x ∈ principalPairs K S D B N, ‖a f x‖ ≤ U) →
      (∑ f ∈ L, w f * ‖∑ x ∈ principalPairs K S D B N, a f x‖) ≤
        C * A * U * X * H ^ (1 + ε) * Y ^ (1 + ε) := by
  obtain ⟨C₁, hC₁, hpair⟩ := exists_principalPairs_bound K S D ε hε
  obtain ⟨C₂, hC₂, hlabel⟩ := exists_label_mass_bound K S p ε hε
  refine ⟨C₁ * C₂, one_le_mul_of_one_le_of_one_le hC₁ hC₂, ?_⟩
  intro B N L H X Y A U w a hH hX hY hA hU hsf hB hN hL hw0 hw ha
  have hcount := hpair B N H X hH hX hsf hB hN
  have hinner (f : Ext) (hf : f ∈ L) :
      ‖∑ x ∈ principalPairs K S D B N, a f x‖ ≤ C₁ * X * H ^ (1 + ε) * U := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _x ∈ principalPairs K S D B N, U := Finset.sum_le_sum (ha f hf)
      _ = ((principalPairs K S D B N).card : ℝ) * U := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hcount hU
  have hweight : 0 ≤ C₁ * X * H ^ (1 + ε) * U := by
    exact mul_nonneg (mul_nonneg (mul_nonneg (le_trans zero_le_one hC₁)
      (le_trans zero_le_one hX)) (Real.rpow_nonneg (le_trans zero_le_one hH) _)) hU
  calc
    _ ≤ ∑ f ∈ L, w f * (C₁ * X * H ^ (1 + ε) * U) := by
      apply Finset.sum_le_sum
      intro f hf
      exact mul_le_mul_of_nonneg_left (hinner f hf) (hw0 f hf)
    _ = (∑ f ∈ L, w f) * (C₁ * X * H ^ (1 + ε) * U) := (Finset.sum_mul ..).symm
    _ ≤ (C₂ * A * Y ^ (1 + ε)) * (C₁ * X * H ^ (1 + ε) * U) :=
      mul_le_mul_of_nonneg_right (hlabel L w A Y hA hY hL hw) hweight
    _ = (C₁ * C₂) * A * U * X * H ^ (1 + ε) * Y ^ (1 + ε) := by ring

theorem physical_principal_count_identity (Z : ℝ) (hZ : 0 < Z)
    (M r ell V eta eps loss : ℝ) :
    Z ^ (-r - 2 * ell - V) * Z ^ (M + loss) * Z ^ (r + eta) *
      (Z ^ (ell + eta)) ^ (1 + eps) * (Z ^ (V + eta)) ^ (1 + eps) =
      Z ^ (M - ell + 3 * eta + eps * (ell + V + 2 * eta) + loss) := by
  rw [← Real.rpow_mul hZ.le, ← Real.rpow_mul hZ.le,
    ← Real.rpow_add hZ, ← Real.rpow_add hZ, ← Real.rpow_add hZ, ← Real.rpow_add hZ]
  congr 1
  ring

/-- A small-power source loss is absorbed only under its explicit
numerical allowance; no loss is silently removed. -/
theorem physical_principal_budget (Z : ℝ) (hZ : 1 ≤ Z)
    (M r ell V eta eps loss allowance : ℝ)
    (hallow : 3 * eta + eps * (ell + V + 2 * eta) + loss ≤ ell + allowance) :
    Z ^ (-r - 2 * ell - V) * Z ^ (M + loss) * Z ^ (r + eta) *
      (Z ^ (ell + eta)) ^ (1 + eps) * (Z ^ (V + eta)) ^ (1 + eps) ≤
      Z ^ (M + allowance) := by
  rw [physical_principal_count_identity Z (lt_of_lt_of_le zero_lt_one hZ)]
  exact Real.rpow_le_rpow_of_exponent_le hZ (by linarith)

/-- Exact ledger including the two original mark factors and every
actual localized mask, before a numerical allowance is imposed. -/
theorem physical_marked_principal_identity (Z : ℝ) (hZ : 0 < Z)
    (M r ell V eta eps Qexp betaLoss : ℝ) :
    Z ^ (-r - 2 * ell - V) * (Z ^ betaLoss) ^ 2 * Z ^ M * Z ^ (r + eta) *
      (Z ^ (ell + eta)) ^ (1 + eps) * (Z ^ (V + eta)) ^ (1 + eps) *
      (Z ^ Qexp * (Z ^ (r + eta)) ^ 4 * (Z ^ (ell + eta)) ^ 8) ^ eps =
      Z ^ (M - ell + 3 * eta + eps * (Qexp + 4 * r + 9 * ell + V + 14 * eta) +
        2 * betaLoss) := by
  have hp (a : ℝ) (n : ℕ) : (Z ^ a) ^ n = Z ^ (a * n) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hZ.le]
  have hi : Z ^ Qexp * (Z ^ (r + eta)) ^ 4 * (Z ^ (ell + eta)) ^ 8 =
      Z ^ (Qexp + 4 * (r + eta) + 8 * (ell + eta)) := by
    rw [hp, hp, ← Real.rpow_add hZ, ← Real.rpow_add hZ]
    congr 1
    norm_num
    ring
  rw [hi, hp, ← Real.rpow_mul hZ.le, ← Real.rpow_mul hZ.le,
    ← Real.rpow_mul hZ.le]
  repeat rw [← Real.rpow_add hZ]
  congr 1
  norm_num
  ring

theorem physical_marked_principal_budget (Z : ℝ) (hZ : 1 ≤ Z)
    (M r ell V eta eps Qexp betaLoss allowance : ℝ)
    (hallow : 3 * eta + eps * (Qexp + 4 * r + 9 * ell + V + 14 * eta) +
      2 * betaLoss ≤ ell + allowance) :
    Z ^ (-r - 2 * ell - V) * (Z ^ betaLoss) ^ 2 * Z ^ M * Z ^ (r + eta) *
      (Z ^ (ell + eta)) ^ (1 + eps) * (Z ^ (V + eta)) ^ (1 + eps) *
      (Z ^ Qexp * (Z ^ (r + eta)) ^ 4 * (Z ^ (ell + eta)) ^ 8) ^ eps ≤
      Z ^ (M + allowance) := by
  rw [physical_marked_principal_identity Z (lt_of_lt_of_le zero_lt_one hZ)]
  exact Real.rpow_le_rpow_of_exponent_le hZ (by linarith)

end HeckeSkeleton.Moments.MOM_INV_STEP.PrincipalBudget

end
