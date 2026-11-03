import ActualExceptionalSixthOrbitCount
import HeckeGeneral.Analysis.IdealSummability
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
UNCOMPILED / native 0. Actual exceptional frequency-orbit upper shells,
weighted by the two-column trivial mass q_C (Y / (q_C q_d))^2.
The cutoff counts every original sixth-unit sector. Both ideal variables
range over actual nonzero integral ideals; finite exterior subfamilies are
therefore covered without a new distribution or summability hypothesis.

This is a counting-weight consumer. It does not identify the original
chosen-generator Gram integrand with a whole masked annular column sum,
and does not assert a bound on that as-yet untransported complex sum.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HeckeGeneral.Analysis.ActualExceptionalWeightedShellDraft

open NumberField HeckeGeneral.ThetaSkeleton.Physical
open HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.Analysis.ActualGramExceptionalCountDraft
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K))) [Fintype S]

/-- The real mass of the actual exceptional frequency cutoff. For a dyadic
shell with q_C q_k <= H Pa, take T = H Pa. A narrower shell is a subset. -/
def exceptionalShellColumnMass (C d : NonzeroIdeal K) (Y T : ℝ) : ℝ :=
  (Nat.card (ActualExceptionalOrbitCutoff K S C (T / idealNorm K C)) : ℝ) *
    (idealNorm K C * (Y / (idealNorm K C * idealNorm K d)) ^ 2)

/-- The mass is literally the sum over the original exceptional orbit
index, rather than a surrogate count of chosen sixth-power generators. -/
theorem exceptionalShellColumnMass_eq_orbit_sum (P : ProbeData K S)
    (C d : NonzeroIdeal K) (Y T : ℝ) (hT : 0 < T) :
    exceptionalShellColumnMass K S C d Y T =
      ∑' _q : ActualExceptionalOrbitCutoff K S C (T / idealNorm K C),
        idealNorm K C * (Y / (idealNorm K C * idealNorm K d)) ^ 2 := by
  letI := finite_actualExceptionalOrbitCutoff K S P C
    (div_nonneg hT.le (idealNorm_pos K C).le)
  letI := Fintype.ofFinite (ActualExceptionalOrbitCutoff K S C (T / idealNorm K C))
  simp [exceptionalShellColumnMass, tsum_fintype, Nat.card_eq_fintype_card]

/-- The original orbit cutoff is empty below norm one. This supplies the
small-cutoff case omitted by the counting theorem's X >= 1 signature. -/
theorem exceptional_cutoff_card_eq_zero_of_lt_one (C : NonzeroIdeal K)
    (X : ℝ) (hX : X < 1) :
    Nat.card (ActualExceptionalOrbitCutoff K S C X) = 0 := by
  letI : IsEmpty (ActualExceptionalOrbitCutoff K S C X) :=
    ⟨fun q => (not_le_of_gt hX)
      ((one_le_actualSIntegerOrbitNorm K S q.val).trans q.property.1)⟩
  exact Nat.card_of_isEmpty

private theorem column_mass_rpow_identity (C d : NonzeroIdeal K)
    (δ B Y T : ℝ) (hT : 0 < T) :
    (B * idealNorm K C ^ δ * (T / idealNorm K C) ^ (1 / 6 : ℝ)) *
        (idealNorm K C * (Y / (idealNorm K C * idealNorm K d)) ^ 2) =
      B * T ^ (1 / 6 : ℝ) * Y ^ 2 *
        (idealNorm K C ^ (δ - 7 / 6 : ℝ) * idealNorm K d ^ (-2 : ℝ)) := by
  have hC := idealNorm_pos K C
  have hd := idealNorm_pos K d
  have hpow : idealNorm K C ^ (δ - 7 / 6 : ℝ) =
      (idealNorm K C ^ δ / idealNorm K C ^ (1 / 6 : ℝ)) / idealNorm K C := by
    calc
      _ = idealNorm K C ^ ((δ - 1 / 6) - 1) := by congr 1 <;> ring
      _ = idealNorm K C ^ (δ - 1 / 6) / idealNorm K C :=
        Real.rpow_sub_one hC.ne' _
      _ = _ := by rw [Real.rpow_sub hC]
  rw [Real.div_rpow hT.le hC.le, hpow,
    Real.rpow_neg hd.le, Real.rpow_two]
  field_simp [hC.ne', hd.ne', (Real.rpow_pos_of_pos hC (1 / 6 : ℝ)).ne']
  <;> ring

/-- Actual orbit counting gives the exact summable ideal weights. The
constant precedes P and all moving column and shell parameters. -/
theorem exists_exceptionalShellColumnMass_bound {δ : ℝ} (hδ : 0 < δ) :
    ∃ B : ℝ, 0 < B ∧ ∀ (P : ProbeData K S) (C d : NonzeroIdeal K)
      (Y T : ℝ), 0 < T →
      exceptionalShellColumnMass K S C d Y T ≤
        B * T ^ (1 / 6 : ℝ) * Y ^ 2 *
          (idealNorm K C ^ (δ - 7 / 6 : ℝ) * idealNorm K d ^ (-2 : ℝ)) := by
  obtain ⟨B, hB, hb⟩ := actualExceptionalOrbitCutoff_small_power_count K S hδ
  refine ⟨B, hB, ?_⟩
  intro P C d Y T hT
  have hC := idealNorm_pos K C
  have hd := idealNorm_pos K d
  by_cases hcut : 1 ≤ T / idealNorm K C
  · calc
      _ ≤ (B * idealNorm K C ^ δ * (T / idealNorm K C) ^ (1 / 6 : ℝ)) *
          (idealNorm K C * (Y / (idealNorm K C * idealNorm K d)) ^ 2) := by
        exact mul_le_mul_of_nonneg_right (hb P C _ hcut)
          (mul_nonneg (idealNorm_pos K C).le (sq_nonneg _))
      _ = _ := column_mass_rpow_identity K C d δ B Y T hT
  · rw [exceptionalShellColumnMass,
      exceptional_cutoff_card_eq_zero_of_lt_one K S C _ (lt_of_not_ge hcut)]
    simp only [Nat.cast_zero, zero_mul]
    positivity

/-- The weights forced by the exceptional orbit count are summable over
the actual pair of ideals whenever the preliminary loss is below 1/6. -/
theorem summable_exceptional_ideal_weights {δ : ℝ} (hδ : δ < 1 / 6) :
    Summable (fun p : NonzeroIdeal K × NonzeroIdeal K =>
      idealNorm K p.1 ^ (δ - 7 / 6 : ℝ) * idealNorm K p.2 ^ (-2 : ℝ)) := by
  have hC : Summable (fun C : NonzeroIdeal K => idealNorm K C ^ (δ - 7 / 6 : ℝ)) := by
    have h := summable_nonzeroIdeal_norm_rpow K (σ := 7 / 6 - δ) (by linarith)
    simpa only [idealNorm, show -(7 / 6 - δ) = δ - 7 / 6 by ring] using h
  have hd : Summable (fun d : NonzeroIdeal K => idealNorm K d ^ (-2 : ℝ)) := by
    simpa only [idealNorm] using
      (summable_nonzeroIdeal_norm_rpow K (σ := 2) (by norm_num))
  exact hC.mul_of_nonneg hd
    (fun C => Real.rpow_nonneg (idealNorm_pos K C).le _)
    (fun d => Real.rpow_nonneg (idealNorm_pos K d).le _)

/-- Uniform finite C,d summation of the actual exceptional orbit masses,
including the genuine Q/Y^3 prefactor and a common nonnegative profile
factor M. M is a scalar parameter, not a supplied Gram or moment estimate.
Take T = H*Pa to obtain (Q/Y)*(H*Pa)^(1/6); a dyadic upper endpoint 2H*Pa
only changes the fixed constant by 2^(1/6). -/
theorem exists_exceptional_weighted_shell_bound {δ : ℝ}
    (hδ : 0 < δ) (hδsmall : δ < 1 / 6) :
    ∃ C0 : ℝ, 0 < C0 ∧ ∀ (P : ProbeData K S)
      (A D : Finset (NonzeroIdeal K)) (Q Y T M : ℝ),
      0 < Q → 0 < Y → 0 < T → 0 ≤ M →
      (Q / Y ^ 3) * M *
        (∑ C ∈ A, ∑ d ∈ D, exceptionalShellColumnMass K S C d Y T) ≤
        C0 * M * (Q / Y) * T ^ (1 / 6 : ℝ) := by
  obtain ⟨B, hB, hb⟩ := exists_exceptionalShellColumnMass_bound K S hδ
  let w : NonzeroIdeal K × NonzeroIdeal K → ℝ := fun p =>
    idealNorm K p.1 ^ (δ - 7 / 6 : ℝ) * idealNorm K p.2 ^ (-2 : ℝ)
  have hw : Summable w := summable_exceptional_ideal_weights K hδsmall
  have hw0 (p) : 0 ≤ w p := by
    exact mul_nonneg (Real.rpow_nonneg (idealNorm_pos K p.1).le _)
      (Real.rpow_nonneg (idealNorm_pos K p.2).le _)
  let L : ℝ := 1 + ∑' p, w p
  have hL : 0 < L := by
    have : 0 ≤ ∑' p, w p := tsum_nonneg hw0
    dsimp only [L]
    linarith
  refine ⟨B * L, mul_pos hB hL, ?_⟩
  intro P A D Q Y T M hQ hY hT hM
  have hweights : (∑ C ∈ A, ∑ d ∈ D, w (C, d)) ≤ L := by
    calc
      _ = ∑ p ∈ A ×ˢ D, w p := (Finset.sum_product _ _ _).symm
      _ ≤ ∑' p, w p := hw.sum_le_tsum _ (fun p _ => hw0 p)
      _ ≤ L := by dsimp only [L]; linarith
  have hmass : (∑ C ∈ A, ∑ d ∈ D,
      exceptionalShellColumnMass K S C d Y T) ≤
      (B * T ^ (1 / 6 : ℝ) * Y ^ 2) * L := by
    calc
      _ ≤ ∑ C ∈ A, ∑ d ∈ D,
          (B * T ^ (1 / 6 : ℝ) * Y ^ 2) * w (C, d) := by
        apply Finset.sum_le_sum
        intro C _
        apply Finset.sum_le_sum
        intro d _
        exact hb P C d Y T hT
      _ = (B * T ^ (1 / 6 : ℝ) * Y ^ 2) *
          (∑ C ∈ A, ∑ d ∈ D, w (C, d)) := by
        simp only [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hweights (by positivity)
  calc
    _ ≤ (Q / Y ^ 3) * M * ((B * T ^ (1 / 6 : ℝ) * Y ^ 2) * L) :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = _ := by field_simp [hY.ne'] <;> ring

end HeckeGeneral.Analysis.ActualExceptionalWeightedShellDraft
