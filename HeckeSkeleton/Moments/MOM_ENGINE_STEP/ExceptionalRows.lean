import HeckePort.CenteredMoment.Counting
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.Pool
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Counting the actual sixth-power exceptional rows

Once the local finite-character calculation prescribes the sixth-power-free
part `h₀`, the map from a row ideal to its sixth-power factor is injective.
The actual ideal norm identity and the proved linear ideal-counting theorem
give the count.  A separate fiber multiplicity retains all original unit
sectors; it is never silently replaced by one.

The premise `I = h₀ * a^6` is an arithmetic classification, not an analytic
count or moment bound.  Its application to finite inducing characters is a
MOM_BASE input, with the fixed residue-class restrictions retained.
-/

noncomputable section
open scoped NumberField Classical BigOperators

namespace HeckeSkeleton.Moments.EngineStep

open NumberField HeckePort.CenteredMomentCounting

variable {K : Type*} [Field K] [NumberField K]

/-- The complete base norm is paid before counting the sixth-power factor. -/
theorem sixth_factor_norm_bound (base factor : Ideal (𝓞 K))
    (Z m b : ℝ) (hZ : 0 < Z)
    (hbase : Z ^ b ≤ (Ideal.absNorm base : ℝ))
    (hrow : (Ideal.absNorm (base * factor ^ 6) : ℝ) ≤ Z ^ m) :
    (Ideal.absNorm factor : ℝ) ≤ Z ^ ((m - b) / 6) := by
  have he : Z ^ b * (Z ^ ((m - b) / 6)) ^ 6 = Z ^ m := by
    rw [← Real.rpow_mul_natCast hZ.le, ← Real.rpow_add hZ]
    congr 1
    norm_num <;> ring
  have hp : Z ^ b * (Ideal.absNorm factor : ℝ) ^ 6 ≤ Z ^ m := by
    calc
      _ ≤ (Ideal.absNorm base : ℝ) * (Ideal.absNorm factor : ℝ) ^ 6 :=
        mul_le_mul_of_nonneg_right hbase (pow_nonneg (Nat.cast_nonneg _) _)
      _ = (Ideal.absNorm (base * factor ^ 6) : ℝ) := by
        simp only [map_mul, map_pow, Nat.cast_mul, Nat.cast_pow]
      _ ≤ _ := hrow
  rw [← he] at hp
  have hp' := (mul_le_mul_left (Real.rpow_pos_of_pos hZ b)).mp hp
  by_contra hn
  have hlt := pow_lt_pow_left₀ (lt_of_not_ge hn)
    (Real.rpow_nonneg hZ.le ((m - b) / 6)) (by decide : (6 : ℕ) ≠ 0)
  exact (not_lt_of_ge hp') hlt

/-- A finite set with one prescribed sixth-power-free part has the actual
ideal-count bound, including a subunit range (which is necessarily empty). -/
theorem sixth_power_row_ideal_count (rows : Finset (Ideal (𝓞 K)))
    (base : Ideal (𝓞 K)) (hrows : ∀ I ∈ rows, I ≠ 0)
    (hfactor : ∀ I ∈ rows, ∃ a : Ideal (𝓞 K), I = base * a ^ 6)
    (Z m b : ℝ) (hZ : 0 < Z)
    (hbase : Z ^ b ≤ (Ideal.absNorm base : ℝ))
    (hrow : ∀ I ∈ rows, (Ideal.absNorm I : ℝ) ≤ Z ^ m) :
    (rows.card : ℝ) ≤ idealCountConstant K * Z ^ ((m - b) / 6) := by
  let factor : rows → Ideal (𝓞 K) := fun I => Classical.choose (hfactor I.val I.property)
  have hfac (I : rows) : I.val = base * factor I ^ 6 :=
    Classical.choose_spec (hfactor I.val I.property)
  have hinj : Function.Injective factor := by
    intro I J he
    apply Subtype.ext
    rw [hfac I, hfac J, he]
  let factors := rows.attach.image factor
  have hnorm (a : Ideal (𝓞 K)) (ha : a ∈ factors) :
      (Ideal.absNorm a : ℝ) ≤ Z ^ ((m - b) / 6) := by
    obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp ha
    apply sixth_factor_norm_bound base (factor I) Z m b hZ hbase
    rw [← hfac I]
    exact hrow I.val I.property
  have hcard : factors.card = rows.card := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_attach]
  by_cases hne : rows.Nonempty
  · obtain ⟨I, hI⟩ := hne
    let x : rows := ⟨I, hI⟩
    have hfactor0 : factor x ≠ 0 := by
      intro hz
      have he := hfac x
      simp only [hz, zero_pow (by decide : (6 : ℕ) ≠ 0), mul_zero] at he
      exact hrows I hI he
    have hone : (1 : ℝ) ≤ Ideal.absNorm (factor x) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        (fun hz => hfactor0 (Ideal.absNorm_eq_zero_iff.mp hz))
    have hcutoff : 1 ≤ Z ^ ((m - b) / 6) :=
      hone.trans (hnorm (factor x) (Finset.mem_image_of_mem factor (Finset.mem_attach _ _)))
    have hc := card_le_idealCountConstant K factors (Z ^ ((m - b) / 6)) hcutoff hnorm
    rwa [hcard] at hc
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp only [Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg (zero_le_one.trans (one_le_idealCountConstant K))
      (Real.rpow_nonneg hZ.le _)

/-- Every original sector is retained through the actual ideal-map fibers. -/
theorem sixth_power_sector_row_count {H : Type*}
    (rows : Finset H) (ideal : H → Ideal (𝓞 K))
    (base : Ideal (𝓞 K)) (hrows : ∀ h ∈ rows, ideal h ≠ 0)
    (hfactor : ∀ h ∈ rows, ∃ a : Ideal (𝓞 K), ideal h = base * a ^ 6)
    (Z m b sectors : ℝ) (hZ : 0 < Z) (hsectors : 0 ≤ sectors)
    (hbase : Z ^ b ≤ (Ideal.absNorm base : ℝ))
    (hrow : ∀ h ∈ rows, (Ideal.absNorm (ideal h) : ℝ) ≤ Z ^ m)
    (hfiber : ∀ I ∈ rows.image ideal,
      ((rows.filter (fun h => ideal h = I)).card : ℝ) ≤ sectors) :
    (rows.card : ℝ) ≤ sectors * idealCountConstant K * Z ^ ((m - b) / 6) := by
  have hpush := positive_pushforward_bound rows ideal (fun _ => (1 : ℝ)) sectors
    (fun _ _ => zero_le_one) hfiber
  have hcount := sixth_power_row_ideal_count (rows.image ideal) base
    (by
      intro I hI
      obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hI
      exact hrows h hh)
    (by
      intro I hI
      obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hI
      exact hfactor h hh)
    Z m b hZ hbase (by
      intro I hI
      obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hI
      exact hrow h hh)
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hpush
  calc
    _ ≤ sectors * ((rows.image ideal).card : ℝ) := hpush
    _ ≤ sectors * (idealCountConstant K * Z ^ ((m - b) / 6)) :=
      mul_le_mul_of_nonneg_left hcount hsectors
    _ = _ := by ring

/-- The stronger true base-norm saving implies the paper's count after
reserving half of that saving for the other local costs. -/
theorem exceptional_sector_row_count {H : Type*}
    (rows : Finset H) (ideal : H → Ideal (𝓞 K))
    (base : Ideal (𝓞 K)) (hrows : ∀ h ∈ rows, ideal h ≠ 0)
    (hfactor : ∀ h ∈ rows, ∃ a : Ideal (𝓞 K), ideal h = base * a ^ 6)
    (Z m f sectors : ℝ) (hZ : 1 ≤ Z) (hf : 0 ≤ f) (hsectors : 0 ≤ sectors)
    (hbase : Z ^ (2 * f) ≤ (Ideal.absNorm base : ℝ))
    (hrow : ∀ h ∈ rows, (Ideal.absNorm (ideal h) : ℝ) ≤ Z ^ m)
    (hfiber : ∀ I ∈ rows.image ideal,
      ((rows.filter (fun h => ideal h = I)).card : ℝ) ≤ sectors) :
    (rows.card : ℝ) ≤ sectors * idealCountConstant K * Z ^ ((m - f) / 6) := by
  have hc := sixth_power_sector_row_count rows ideal base hrows hfactor
    Z m (2 * f) sectors (zero_lt_one.trans_le hZ) hsectors hbase hrow hfiber
  apply hc.trans
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ (by linarith))
    (mul_nonneg hsectors (zero_le_one.trans (one_le_idealCountConstant K)))

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.exceptional_sector_row_count
