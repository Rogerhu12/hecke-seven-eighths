import HeckeSkeleton.HighBinSupport.HighNormFormSlots
import Mathlib.Data.Nat.Find
import Lean.Elab.Tactic.Omega
/-!
A finite, height-independent amplitude partition.

The binning may be applied to the maximum of each actual prime slot on
its compact retained height interval.  Unlike an arbitrary splitting of
a total integral, these labels give individual upper bounds for every
height.  Positive amplitudes have actual maximizing-value witnesses.

This module does not prove the uniform prime-slot upper estimate supplied
as the independent premise `hupper`.  That premise is the detector/prime
sum input, rather than the norm-form conclusion.
-/

noncomputable section
namespace HighBinVerified.NormForm
open scoped BigOperators

/-- A geometric bucket exists, including the zero-amplitude bucket.  The
last bucket is clipped at the detector cap without losing the upper bound. -/
theorem exists_amplitude_bucket (P theta cap M : ℝ) (N : ℕ)
    (hP : 1 ≤ P) (htheta : 0 < theta) (hcap : 0 ≤ cap)
    (hN : cap ≤ (N : ℝ) * theta)
    (hupper : M ≤ P ^ (cap + theta)) :
    ∃ k : Fin (N + 1),
      let g := min ((k.val : ℝ) * theta) cap
      0 ≤ g ∧ g ≤ cap ∧ M ≤ P ^ (g + theta) ∧
        (0 < g → P ^ g < M) := by
  classical
  have hex : ∃ n : ℕ, n ≤ N ∧ M ≤ P ^ (((n : ℝ) + 1) * theta) := by
    refine ⟨N, le_rfl, hupper.trans ?_⟩
    exact Real.rpow_le_rpow_of_exponent_le hP (by nlinarith)
  let k : ℕ := Nat.find hex
  have hk : k ≤ N ∧ M ≤ P ^ (((k : ℝ) + 1) * theta) := Nat.find_spec hex
  refine ⟨⟨k, by omega⟩, ?_⟩
  dsimp only
  have hkt : 0 ≤ (k : ℝ) * theta := mul_nonneg (Nat.cast_nonneg _) htheta.le
  refine ⟨le_min hkt hcap, min_le_right _ _, ?_, ?_⟩
  · by_cases hkc : (k : ℝ) * theta ≤ cap
    · rw [min_eq_left hkc]
      convert hk.2 using 1 <;> congr 1 <;> ring
    · rw [min_eq_right (le_of_not_ge hkc)]
      exact hupper
  · intro hg
    have hkpos : 0 < k := by
      by_contra hn
      have hk0 : k = 0 := by omega
      simp only [hk0, Nat.cast_zero, zero_mul, min_eq_left hcap] at hg
      linarith
    have hprev : ¬(k - 1 ≤ N ∧ M ≤ P ^ ((((k - 1 : ℕ) : ℝ) + 1) * theta)) :=
      Nat.find_min hex (show k - 1 < k by omega)
    have hkcast : ((k - 1 : ℕ) : ℝ) + 1 = (k : ℝ) := by
      have heq : k - 1 + 1 = k := by omega
      exact_mod_cast heq
    have hstrict : P ^ ((k : ℝ) * theta) < M := by
      apply lt_of_not_ge
      intro hh
      exact hprev ⟨by omega, by simpa only [hkcast] using hh⟩
    exact (Real.rpow_le_rpow_of_exponent_le hP (min_le_left _ _)).trans_lt hstrict

/-- The label type has constant cardinality once the grid and slot system
have been fixed.  It does not grow with the number of physical rows. -/
theorem amplitude_label_card (J N : ℕ) :
    Fintype.card (Fin J → Fin (N + 1)) = (N + 1) ^ J := by
  simp

/-- Simultaneous constructive binning.  Each row receives one finite
amplitude vector; the estimates hold separately in every slot. -/
theorem exists_amplitude_labels {Row : Type*} (J N : ℕ)
    (P : Fin J → ℝ) (M : Row → Fin J → ℝ) (theta cap : ℝ)
    (hP : ∀ i, 1 ≤ P i) (htheta : 0 < theta) (hcap : 0 ≤ cap)
    (hN : cap ≤ (N : ℝ) * theta)
    (hupper : ∀ u i, M u i ≤ P i ^ (cap + theta)) :
    ∃ label : Row → Fin J → Fin (N + 1),
      ∀ u i,
        let g := min (((label u i).val : ℝ) * theta) cap
        0 ≤ g ∧ g ≤ cap ∧ M u i ≤ P i ^ (g + theta) ∧
          (0 < g → P i ^ g < M u i) := by
  have hh := fun u i => exists_amplitude_bucket (P i) theta cap (M u i) N
    (hP i) htheta hcap hN (hupper u i)
  choose label hlabel using hh
  exact ⟨label, hlabel⟩

/-- Mean amplitudes remain in the detector's permitted range. -/
theorem mean_amplitude_range (J : ℕ) (hJ : 0 < J) (g : Fin J → ℝ)
    (cap : ℝ) (hg : ∀ i, 0 ≤ g i ∧ g i ≤ cap) :
    0 ≤ (∑ i, g i) / J ∧ (∑ i, g i) / J ≤ cap := by
  have hJpos : (0 : ℝ) < J := by exact_mod_cast hJ
  constructor
  · exact div_nonneg (Finset.sum_nonneg (fun i _ => (hg i).1)) hJpos.le
  · apply (div_le_iff₀ hJpos).mpr
    calc
      (∑ i, g i) ≤ ∑ _i : Fin J, cap := Finset.sum_le_sum (fun i _ => (hg i).2)
      _ = cap * J := by simp [mul_comm]

end HighBinVerified.NormForm

#print axioms HighBinVerified.NormForm.exists_amplitude_bucket
#print axioms HighBinVerified.NormForm.exists_amplitude_labels
#print axioms HighBinVerified.NormForm.mean_amplitude_range
