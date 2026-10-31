import ExpansionInterfaces.DyadicShells

/-!
# The actual finite block schedule and its scale guard

The natural block index decodes into a dyadic shell and one fixed buffered
choice.  There is no separate freely chosen shell exponent.  Empty schedules
and zero buffer multiplicity are handled by the finite index itself.
-/

set_option autoImplicit false
noncomputable section

namespace ExpansionRecipe

def scheduledBlockCount (multiplicity : ℕ) (ζ Z : ℝ) : ℕ :=
  ExpansionInterfaces.shellCount Z (1 / 16) (13 / 16 + ζ) * multiplicity

def activeBlockCount (multiplicity : ℕ) (ζ Z T : ℝ) : ℕ :=
  if (2 : ℝ) ^ (16 : ℕ) ≤ Z ∧ 1 ≤ T then scheduledBlockCount multiplicity ζ Z else 0

theorem activeBlockGuard (multiplicity : ℕ) (ζ Z T : ℝ)
    (b : Fin (activeBlockCount multiplicity ζ Z T)) :
    (2 : ℝ) ^ (16 : ℕ) ≤ Z ∧ 1 ≤ T := by
  by_contra h
  have hb := b.isLt
  simp only [activeBlockCount, h, ite_false] at hb
  omega

def rawBlockIndex (multiplicity : ℕ) (ζ Z T : ℝ)
    (b : Fin (activeBlockCount multiplicity ζ Z T)) :
    Fin (scheduledBlockCount multiplicity ζ Z) :=
  ⟨b.val, by simpa only [activeBlockCount, activeBlockGuard multiplicity ζ Z T b, ite_true]
    using b.isLt⟩

theorem multiplicity_pos_of_block (multiplicity : ℕ) (ζ Z T : ℝ)
    (b : Fin (activeBlockCount multiplicity ζ Z T)) : 0 < multiplicity := by
  by_contra h
  have hz : multiplicity = 0 := by omega
  have hb := (rawBlockIndex multiplicity ζ Z T b).isLt
  have hb0 : b.val < 0 := by simpa only [scheduledBlockCount, hz, Nat.mul_zero] using hb
  exact Nat.not_lt_zero _ hb0

def blockShellIndex (multiplicity : ℕ) (ζ Z T : ℝ)
    (b : Fin (activeBlockCount multiplicity ζ Z T)) :
    Fin (ExpansionInterfaces.shellCount Z (1 / 16) (13 / 16 + ζ)) :=
  ⟨b.val / multiplicity,
    (Nat.div_lt_iff_lt_mul (multiplicity_pos_of_block multiplicity ζ Z T b)).mpr
      (rawBlockIndex multiplicity ζ Z T b).isLt⟩

def blockShell (multiplicity : ℕ) (ζ Z T : ℝ)
    (b : Fin (activeBlockCount multiplicity ζ Z T)) : ℝ :=
  ExpansionInterfaces.shellExponent Z (1 / 16) (blockShellIndex multiplicity ζ Z T b).val

theorem blockShell_range (multiplicity : ℕ) (ζ Z T : ℝ)
    (b : Fin (activeBlockCount multiplicity ζ Z T)) :
    1 / 16 ≤ blockShell multiplicity ζ Z T b ∧
      blockShell multiplicity ζ Z T b < 13 / 16 + ζ := by
  have hZ : 1 < Z := (by norm_num : (1 : ℝ) < 2 ^ (16 : ℕ)).trans_le
    (activeBlockGuard multiplicity ζ Z T b).1
  exact ExpansionInterfaces.actualShell_range hZ (blockShellIndex multiplicity ζ Z T b)

theorem activeBlockCount_le (multiplicity : ℕ) (ζ Z T : ℝ) :
    activeBlockCount multiplicity ζ Z T ≤ scheduledBlockCount multiplicity ζ Z := by
  unfold activeBlockCount
  split_ifs <;> omega

theorem activeBlockCount_eq (multiplicity : ℕ) (ζ Z T : ℝ)
    (hZ : (2 : ℝ) ^ (16 : ℕ) ≤ Z) (hT : 1 ≤ T) :
    activeBlockCount multiplicity ζ Z T = scheduledBlockCount multiplicity ζ Z := by
  simp only [activeBlockCount, hZ, hT, and_self, ite_true]

end ExpansionRecipe

#print axioms ExpansionRecipe.activeBlockGuard
#print axioms ExpansionRecipe.multiplicity_pos_of_block
#print axioms ExpansionRecipe.blockShell_range
#print axioms ExpansionRecipe.activeBlockCount_le
#print axioms ExpansionRecipe.activeBlockCount_eq
