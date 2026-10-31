import HeckeGeneral.Analysis.SIntegerAnnularColumnCount
import Mathlib.Tactic

/-!
UNCOMPILED candidate. Nonzero points of a fixed discrete full lattice have
an exact-dimensional count at every positive scale. The small-scale bound
comes from actual discreteness at zero, not an assumed minimum radius.
-/

noncomputable section

namespace HeckeGeneral.Analysis.NonzeroLatticeAllScaleCountDraft

open MeasureTheory Set
open scoped Topology Classical

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E]
variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

/-- A positive lower bound for the norms of all actual nonzero lattice points. -/
theorem exists_nonzero_lattice_norm_lower_bound :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x : E, x ∈ L → x ≠ 0 → ε ≤ ‖x‖ := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp
    (isOpen_discrete ({(0 : L)} : Set L)) 0 (by simp)
  refine ⟨ε, hε, fun x hx hne => ?_⟩
  by_contra hnot
  have hmem : (⟨x, hx⟩ : L) ∈ Metric.ball 0 ε := by
    rw [Metric.mem_ball, dist_zero_right]
    exact lt_of_not_ge hnot
  have heq : (⟨x, hx⟩ : L) = 0 := hball hmem
  exact hne (congrArg Subtype.val heq)

private theorem finite_full_sublevel (c : ℝ) (hc : 1 ≤ c) :
    Set.Finite ({x : E | ‖x‖ ^ Module.finrank ℝ E ≤ c} ∩ (L : Set E)) := by
  have hd : Module.finrank ℝ E ≠ 0 := (Module.finrank_pos (R := ℝ) (M := E)).ne'
  have hbound : {x : E | ‖x‖ ^ Module.finrank ℝ E ≤ c} ⊆ Metric.closedBall 0 c := by
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right]
    by_cases hnorm : ‖x‖ ≤ 1
    · exact hnorm.trans hc
    · exact (le_self_pow₀ (le_of_not_ge hnorm) hd).trans hx
  have hclosed : IsClosed (L : Set E) :=
    @AddSubgroup.isClosed_of_discreteTopology _ _ _ _ _ L.toAddSubgroup
      (inferInstanceAs (DiscreteTopology L))
  exact Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete
    (Metric.isBounded_closedBall.subset hbound) hclosed

/-- The nonzero sublevel is finite even below the unit scale. -/
theorem finite_nonzero_lattice_norm_power_sublevel (c : ℝ) :
    Set.Finite ({x : E | x ≠ 0 ∧ ‖x‖ ^ Module.finrank ℝ E ≤ c} ∩ (L : Set E)) :=
  (finite_full_sublevel L (max 1 c) (le_max_left _ _)).subset
    (fun _ hx => ⟨hx.1.2.trans (le_max_right _ _), hx.2⟩)

/-- The constant precedes c. Omitting the origin is essential below c = 1. -/
theorem exists_nonzero_lattice_norm_power_count_le :
    ∃ C : ℝ, 0 < C ∧ ∀ c : ℝ, 0 < c →
      (Nat.card ↥(({x : E | x ≠ 0 ∧ ‖x‖ ^ Module.finrank ℝ E ≤ c} : Set E) ∩
        (L : Set E)) : ℝ) ≤ C * c := by
  obtain ⟨ε, hε, hsep⟩ := exists_nonzero_lattice_norm_lower_bound L
  obtain ⟨C0, hC0, hcount⟩ := exists_lattice_norm_power_count_le L
  let d := Module.finrank ℝ E
  let C := C0 * (1 + (ε ^ d)⁻¹)
  have heps : 0 < ε ^ d := pow_pos hε _
  have hC : 0 < C := by dsimp only [C]; positivity
  have hC0C : C0 ≤ C := by
    dsimp only [C]
    nlinarith [inv_pos.mpr heps]
  refine ⟨C, hC, fun c hc => ?_⟩
  let T : Set E := {x : E | x ≠ 0 ∧ ‖x‖ ^ d ≤ c} ∩ (L : Set E)
  change (Nat.card T : ℝ) ≤ C * c
  by_cases hlarge : 1 ≤ c
  · have hmono : Nat.card T ≤
        Nat.card ↥(({x : E | ‖x‖ ^ d ≤ c} : Set E) ∩ (L : Set E)) :=
      Nat.card_mono (finite_full_sublevel L c hlarge) (fun _ hx => ⟨hx.1.2, hx.2⟩)
    have hmonoR : (Nat.card T : ℝ) ≤
        (Nat.card ↥(({x : E | ‖x‖ ^ d ≤ c} : Set E) ∩ (L : Set E)) : ℝ) := by
      exact_mod_cast hmono
    exact hmonoR.trans ((hcount c hlarge).trans
      (mul_le_mul_of_nonneg_right hC0C hc.le))
  · by_cases hempty : T = ∅
    · have h0 : Nat.card T = 0 := by
        rw [hempty]
        exact Nat.card_of_isEmpty
      rw [h0, Nat.cast_zero]
      positivity
    obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hempty
    have hlow : ε ^ d ≤ c :=
      (pow_le_pow_left₀ hε.le (hsep x hx.2 hx.1.1) d).trans hx.1.2
    have hinv : 1 ≤ (ε ^ d)⁻¹ * c := by
      rw [inv_mul_eq_div, le_div_iff₀ heps]
      simpa using hlow
    have hmono : Nat.card T ≤
        Nat.card ↥(({x : E | ‖x‖ ^ d ≤ 1} : Set E) ∩ (L : Set E)) :=
      Nat.card_mono (finite_full_sublevel L 1 le_rfl)
        (fun _ hx => ⟨hx.1.2.trans (le_of_not_ge hlarge), hx.2⟩)
    have hmonoR : (Nat.card T : ℝ) ≤
        (Nat.card ↥(({x : E | ‖x‖ ^ d ≤ 1} : Set E) ∩ (L : Set E)) : ℝ) := by
      exact_mod_cast hmono
    have hsmall : (Nat.card T : ℝ) ≤ C0 := by
      simpa only [mul_one] using hmonoR.trans (hcount 1 le_rfl)
    have hfactor : 1 ≤ (1 + (ε ^ d)⁻¹) * c := by nlinarith
    calc
      _ ≤ C0 := hsmall
      _ = C0 * 1 := (mul_one _).symm
      _ ≤ C0 * ((1 + (ε ^ d)⁻¹) * c) := mul_le_mul_of_nonneg_left hfactor hC0.le
      _ = C * c := by dsimp only [C]; ring

end HeckeGeneral.Analysis.NonzeroLatticeAllScaleCountDraft
