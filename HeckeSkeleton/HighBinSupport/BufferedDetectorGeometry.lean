import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Finite buffered detector geometry

The detector uses a finite grid of real parts and a finite list of heights.
One adjacent pair of heights has no newly observed grid level. This is a
finite combinatorial fact; no zero-count estimate or eventual stabilization
assumption is needed.

The arithmetic specialization is in `ActualBoundaryGeometry`.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.HighBinDetectorGeometry

open scoped Classical

/-- Any sequence with values in `0,...,M` has a nonincreasing adjacent step
among its first `M+1` steps. -/
theorem exists_adjacent_nonincrease (M : ℕ) (f : ℕ → ℕ)
    (hbound : ∀ i : ℕ, f i ≤ M) :
    ∃ i : ℕ, i ≤ M ∧ f (i + 1) ≤ f i := by
  by_contra h
  have hstep (i : ℕ) (hi : i ≤ M) : f i < f (i + 1) := by
    exact Nat.lt_of_not_ge (fun hle => h ⟨i, hi, hle⟩)
  have hlower : ∀ i : ℕ, i ≤ M + 1 → i ≤ f i := by
    intro i
    induction i with
    | zero => intro _; exact Nat.zero_le _
    | succ i ih =>
      intro hi
      have hi' : i ≤ M := by omega
      have h₀ := ih (by omega : i ≤ M + 1)
      have h₁ := hstep i hi'
      omega
  have h₀ := hlower (M + 1) le_rfl
  have h₁ := hbound (M + 1)
  omega

/-- The floor level is always retained; positive levels record actual
observations. No observation is inserted at the floor. -/
def observedLevels (M : ℕ) (active : ℕ → ℕ → Prop) (i : ℕ) : Finset ℕ :=
  (Finset.range (M + 1)).filter fun j => j = 0 ∨ active i j

theorem observedLevels_nonempty (M : ℕ) (active : ℕ → ℕ → Prop) (i : ℕ) :
    (observedLevels M active i).Nonempty := by
  refine ⟨0, ?_⟩
  simp [observedLevels]

def observedLevel (M : ℕ) (active : ℕ → ℕ → Prop) (i : ℕ) : ℕ :=
  (observedLevels M active i).max' (observedLevels_nonempty M active i)

theorem observedLevel_spec (M : ℕ) (active : ℕ → ℕ → Prop) (i : ℕ) :
    observedLevel M active i ≤ M ∧
      (observedLevel M active i = 0 ∨ active i (observedLevel M active i)) := by
  have hm := Finset.max'_mem (observedLevels M active i)
    (observedLevels_nonempty M active i)
  change observedLevel M active i ∈ observedLevels M active i at hm
  simp only [observedLevels, Finset.mem_filter, Finset.mem_range] at hm
  exact ⟨by omega, hm.2⟩

theorem le_observedLevel (M : ℕ) (active : ℕ → ℕ → Prop) (i j : ℕ)
    (hj : j ≤ M) (hactive : active i j) : j ≤ observedLevel M active i := by
  apply Finset.le_max'
  simp only [observedLevels, Finset.mem_filter, Finset.mem_range]
  exact ⟨by omega, Or.inr hactive⟩

/-- A selected grid level at one height and absence of the next grid level
at the next height. The two indices have explicit uniform finite bounds. -/
theorem exists_buffered_level (M : ℕ) (active : ℕ → ℕ → Prop)
    (hcap : ∀ i : ℕ, ¬ active i (M + 1)) :
    ∃ i j : ℕ, i ≤ M ∧ j ≤ M ∧
      (j = 0 ∨ active i j) ∧ ¬ active (i + 1) (j + 1) := by
  obtain ⟨i, hi, hnext⟩ := exists_adjacent_nonincrease M (observedLevel M active)
    (fun i => (observedLevel_spec M active i).1)
  let j := observedLevel M active i
  have hj := (observedLevel_spec M active i).1
  have hactive := (observedLevel_spec M active i).2
  refine ⟨i, j, hi, hj, hactive, ?_⟩
  intro hnew
  by_cases hj' : j + 1 ≤ M
  · have hle := le_observedLevel M active (i + 1) (j + 1) hj' hnew
    change observedLevel M active (i + 1) ≤ j at hnext
    omega
  · have heq : j = M := by omega
    exact hcap (i + 1) (by simpa only [heq] using hnew)

/-- Enough levels to cover the full zero-real-part range through one. -/
def detectorDepth (e : ℝ) : ℕ := Nat.ceil (1 / e)

theorem detectorDepth_mul (e : ℝ) (he : 0 < e) :
    1 ≤ (detectorDepth e : ℝ) * e := by
  have h := Nat.le_ceil (1 / e)
  exact (div_le_iff₀ he).mp h

def gridRealPart (e : ℝ) (j : ℕ) : ℝ := 51 / 100 + (j : ℝ) * e

@[simp] theorem gridRealPart_zero (e : ℝ) : gridRealPart e 0 = 51 / 100 := by
  simp [gridRealPart]

theorem gridRealPart_succ (e : ℝ) (j : ℕ) :
    gridRealPart e (j + 1) = gridRealPart e j + e := by
  simp only [gridRealPart, Nat.cast_add, Nat.cast_one]
  ring

theorem gridRealPart_lower (e : ℝ) (he : 0 ≤ e) (j : ℕ) :
    51 / 100 ≤ gridRealPart e j := by
  dsimp [gridRealPart]
  exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg j) he)

theorem gridRealPart_eq_floor_iff (e : ℝ) (he : 0 < e) (j : ℕ) :
    gridRealPart e j = 51 / 100 ↔ j = 0 := by
  constructor
  · intro h
    have hj : (j : ℝ) * e = 0 := by dsimp [gridRealPart] at h; linarith
    have hzero : (j : ℝ) = 0 := (mul_eq_zero.mp hj).resolve_right he.ne'
    exact_mod_cast hzero
  · rintro rfl
    exact gridRealPart_zero e

theorem gridRealPart_cap (e : ℝ) (he : 0 < e) :
    1 < gridRealPart e (detectorDepth e + 1) := by
  have h := detectorDepth_mul e he
  simp only [gridRealPart, Nat.cast_add, Nat.cast_one]
  nlinarith

def selectedHeight (T : ℝ) (i : ℕ) : ℝ := 3 * ((i : ℝ) + 1) * T

def upperHeight (T : ℝ) (i : ℕ) : ℝ := 3 * ((i : ℝ) + 2) * T

def contourHeight (T : ℝ) : ℝ := T / 2

theorem selectedHeight_succ (T : ℝ) (i : ℕ) :
    selectedHeight T (i + 1) = upperHeight T i := by
  simp only [selectedHeight, upperHeight, Nat.cast_add, Nat.cast_one]
  ring

theorem selectedHeight_mono (T : ℝ) (hT : 0 ≤ T) : Monotone (selectedHeight T) := by
  intro i j hij
  have hcast : (i : ℝ) ≤ j := Nat.cast_le.mpr hij
  dsimp [selectedHeight]
  exact mul_le_mul_of_nonneg_right (by linarith) hT

theorem upperHeight_mono (T : ℝ) (hT : 0 ≤ T) : Monotone (upperHeight T) := by
  intro i j hij
  have hcast : (i : ℝ) ≤ j := Nat.cast_le.mpr hij
  dsimp [upperHeight]
  exact mul_le_mul_of_nonneg_right (by linarith) hT

/-- The contour occupies a fixed fraction of the external height, and
every selected detector index supplies the required upper buffer. -/
theorem contourHeight_geometry (T : ℝ) (hT : 1 ≤ T) (i : ℕ) :
    (1 / 2 : ℝ) * T ≤ contourHeight T ∧
      contourHeight T + 3 / 2 ≤ upperHeight T i := by
  have hi : 0 ≤ (i : ℝ) := Nat.cast_nonneg i
  have hiT : 0 ≤ (i : ℝ) * T := mul_nonneg hi (by linarith)
  dsimp [contourHeight, upperHeight]
  constructor <;> nlinarith

/-- All detector choices belong to this explicit finite product. -/
abbrev DetectorIndex (M : ℕ) := Fin (M + 1) × Fin (M + 1)

theorem detectorIndex_card (M : ℕ) :
    Fintype.card (DetectorIndex M) = (M + 1) ^ 2 := by
  simp [DetectorIndex, pow_two]

/-- Pairing the detector with a finite shell list does not add any
dependence on the external height. -/
theorem shellDetectorIndex_card (n M : ℕ) :
    Fintype.card (Fin n × DetectorIndex M) = n * (M + 1) ^ 2 := by
  simp [DetectorIndex, pow_two]

end HeckeSkeleton.HighBinDetectorGeometry

#print axioms HeckeSkeleton.HighBinDetectorGeometry.exists_adjacent_nonincrease
#print axioms HeckeSkeleton.HighBinDetectorGeometry.exists_buffered_level
#print axioms HeckeSkeleton.HighBinDetectorGeometry.detectorDepth_mul
#print axioms HeckeSkeleton.HighBinDetectorGeometry.gridRealPart_cap
#print axioms HeckeSkeleton.HighBinDetectorGeometry.contourHeight_geometry
#print axioms HeckeSkeleton.HighBinDetectorGeometry.shellDetectorIndex_card
