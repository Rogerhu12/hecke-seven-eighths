import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The width-induction schedule and the moment mesh (D-MESH)

Ported from openai/math `DirichletL/Energy/WidthSchedule.lean`, `Energy/WidthRanges.lean`
and `Moments/FirstSecondLossParameters.lean` (`depth`). The definitions and proofs are
purely numeric; only the namespace and the inlined `mesh_cost` step changed.

`momentMeshValue lamA = fineMesh 2 0 1 1 lamA` is the mesh of the bounded real box
used by the skeleton (`HeckeSkeleton.momentMesh`). With κ = 1 it is the smallest of the
meshes `fineMesh 2 0 1 κ lamA`, κ ∈ [3/4, 1], so it serves every κ in that range.
-/

noncomputable section

namespace HeckePort.Schedule

/-- openai `CenteredMomentFirstSecondLossParameters.depth`. -/
def depth (Mcap σ : ℝ) : ℕ := ⌈2 * Mcap / σ⌉₊ + 1

lemma depth_covers (Mcap σ : ℝ) (hσ : 0 < σ) : Mcap < (depth Mcap σ : ℝ) * σ / 2 := by
  have hh := Nat.le_ceil (2 * Mcap / σ)
  have hn : 2 * Mcap ≤ (⌈2 * Mcap / σ⌉₊ : ℝ) * σ := (div_le_iff₀ hσ).mp hh
  simp only [depth, Nat.cast_add, Nat.cast_one]
  nlinarith

def amplification (ε : ℝ) : ℝ := min 1 (ε / 16000)
def count (M ε : ℝ) : ℕ := depth M (amplification ε)
def scale (M B ε : ℝ) : ℝ := (count M ε : ℝ) + M + 10 * B + 30
def reserve (M B ε : ℝ) : ℝ :=
  min (amplification ε / 100) (ε / (1000000 * scale M B ε))
def mesh (M B κ ε : ℝ) : ℝ := reserve M B ε / (κ + 1)
def width (M B ε : ℝ) (k : ℕ) : ℝ := reserve M B ε / 16 + (k : ℝ) * amplification ε / 2
def loss (M B ε : ℝ) (k : ℕ) : ℝ := reserve M B ε + 64 * (k : ℝ) * reserve M B ε

theorem bounds (M B κ ε : ℝ) (hM : 0 ≤ M) (hB : 0 ≤ B) (hκ : 0 ≤ κ) (hε : 0 < ε) :
    0 < amplification ε ∧ amplification ε ≤ 1 ∧ amplification ε ≤ ε / 16000 ∧
    0 < reserve M B ε ∧ 0 < mesh M B κ ε ∧ mesh M B κ ε ≤ reserve M B ε ∧
    κ * mesh M B κ ε ≤ reserve M B ε ∧
    20 * reserve M B ε ≤ amplification ε / 2 ∧
    M < width M B ε (count M ε) ∧
    loss M B ε (count M ε) ≤ ε / 1000 := by
  have hs : 0 < amplification ε := lt_min (by norm_num) (by positivity)
  have hs1 : amplification ε ≤ 1 := min_le_left _ _
  have hse : amplification ε ≤ ε / 16000 := min_le_right _ _
  have hn : 0 ≤ (count M ε : ℝ) := Nat.cast_nonneg _
  have hL : 0 < scale M B ε := by unfold scale; positivity
  have hr : 0 < reserve M B ε := lt_min (by positivity) (by positivity)
  have hrs : reserve M B ε ≤ amplification ε / 100 := min_le_left _ _
  have hre : reserve M B ε ≤ ε / (1000000 * scale M B ε) := min_le_right _ _
  have hp : reserve M B ε * (1000000 * scale M B ε) ≤ ε :=
    (le_div_iff₀ (by positivity)).mp hre
  have hnL : (count M ε : ℝ) ≤ scale M B ε := by unfold scale; linarith
  have h1L : 1 ≤ scale M B ε := by unfold scale; linarith
  have hnR : (count M ε : ℝ) * reserve M B ε ≤ ε / 1000000 := by
    have hh := mul_le_mul_of_nonneg_right hnL hr.le
    nlinarith
  have hR : reserve M B ε ≤ ε / 1000000 := by
    have hh := mul_le_mul_of_nonneg_right h1L hr.le
    nlinarith
  have hm : 0 < mesh M B κ ε := by unfold mesh; positivity
  have hmr : mesh M B κ ε ≤ reserve M B ε := by
    unfold mesh
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hkm : κ * mesh M B κ ε ≤ reserve M B ε := by
    unfold mesh
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith
  have hw : M < width M B ε (count M ε) := by
    have hd := depth_covers M (amplification ε) hs
    change M < (count M ε : ℝ) * amplification ε / 2 at hd
    unfold width
    linarith
  refine ⟨hs, hs1, hse, hr, hm, hmr, hkm, by linarith, hw, ?_⟩
  unfold loss
  linarith

def step (M B L : ℝ) : ℝ := 4 * (L + M + B + 4)
def range (M B L : ℝ) : ℕ → ℝ
  | 0 => max 1 L
  | n + 1 => step M B (range M B L n)
def sourceCap (M B L : ℝ) (n : ℕ) : ℝ := 10 * (range M B L n + M + B + 1)
def finalSourceCap (M B L ε : ℝ) : ℝ := sourceCap M B L (count M ε)
def fineMesh (M B L κ ε : ℝ) : ℝ := mesh M (finalSourceCap M B L ε) κ ε

lemma range_nonneg (M B L : ℝ) (hM : 0 ≤ M) (hB : 0 ≤ B) (n : ℕ) : 0 ≤ range M B L n := by
  induction n with
  | zero => exact zero_le_one.trans (le_max_left _ _)
  | succ n ih => simp only [range, step]; positivity

lemma finalSourceCap_nonneg (M B L ε : ℝ) (hM : 0 ≤ M) (hB : 0 ≤ B) :
    0 ≤ finalSourceCap M B L ε := by
  unfold finalSourceCap sourceCap
  have := range_nonneg M B L hM hB (count M ε)
  positivity

/-- The skeleton's moment mesh: the box (M, B, L) = (2, 0, 1) at κ = 1. -/
def momentMeshValue (lamA : ℝ) : ℝ := fineMesh 2 0 1 1 lamA

theorem momentMeshValue_pos {lamA : ℝ} (h : 0 < lamA) : 0 < momentMeshValue lamA :=
  (bounds 2 (finalSourceCap 2 0 1 lamA) 1 lamA (by norm_num)
    (finalSourceCap_nonneg 2 0 1 lamA (by norm_num) le_rfl) zero_le_one h).2.2.2.2.1

/-- The mesh serves every κ ≤ 1: it is at most the κ-mesh of the same box. -/
theorem momentMeshValue_le_fineMesh {lamA κ : ℝ} (h : 0 < lamA) (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1) :
    momentMeshValue lamA ≤ fineMesh 2 0 1 κ lamA := by
  have hr := (bounds 2 (finalSourceCap 2 0 1 lamA) 1 lamA (by norm_num)
    (finalSourceCap_nonneg 2 0 1 lamA (by norm_num) le_rfl) zero_le_one h).2.2.2.1
  unfold momentMeshValue fineMesh mesh
  exact div_le_div_of_nonneg_left hr.le (by linarith) (by linarith)

end HeckePort.Schedule
