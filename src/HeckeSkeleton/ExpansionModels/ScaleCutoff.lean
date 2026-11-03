import HeckeSkeleton.ExpansionModels.DyadicMomentEnvelope

/-! A single physical cutoff controls every shell d>=1/16. -/

set_option autoImplicit false
noncomputable section

namespace ExpansionRecipe

theorem shell_base_ge_of_physical_cutoff {Z U₀ d : ℝ}
    (hU₀ : 1 ≤ U₀) (hZ : U₀ ^ (16 : ℕ) ≤ Z) (hd : 1 / 16 ≤ d) :
    U₀ ≤ Z ^ d := by
  have hU₀pos : 0 < U₀ := zero_lt_one.trans_le hU₀
  have hZ1 : 1 ≤ Z := (one_le_pow₀ hU₀).trans hZ
  have hroot : (U₀ ^ (16 : ℕ)) ^ (1 / 16 : ℝ) = U₀ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hU₀pos.le]
    norm_num
  calc
    U₀ = (U₀ ^ (16 : ℕ)) ^ (1 / 16 : ℝ) := hroot.symm
    _ ≤ Z ^ (1 / 16 : ℝ) := Real.rpow_le_rpow (by positivity) hZ (by norm_num)
    _ ≤ Z ^ d := Real.rpow_le_rpow_of_exponent_le hZ1 hd

theorem shell_base_ge_two {Z d : ℝ}
    (hZ : (2 : ℝ) ^ (16 : ℕ) ≤ Z) (hd : 1 / 16 ≤ d) :
    2 ≤ Z ^ d := shell_base_ge_of_physical_cutoff (by norm_num) hZ hd

theorem repaired_exponent_in_box_at_physical_cutoff {Z d : ℝ}
    (hZ : (2 : ℝ) ^ (16 : ℕ) ≤ Z) (hd : 1 / 16 ≤ d) :
    1 < dyadicMassExponent (Z ^ d) ∧ dyadicMassExponent (Z ^ d) ≤ 2 := by
  have hU := shell_base_ge_two hZ hd
  exact ⟨dyadicMassExponent_gt_one (by linarith), dyadicMassExponent_le_two hU⟩

end ExpansionRecipe

#print axioms ExpansionRecipe.shell_base_ge_of_physical_cutoff
#print axioms ExpansionRecipe.repaired_exponent_in_box_at_physical_cutoff
