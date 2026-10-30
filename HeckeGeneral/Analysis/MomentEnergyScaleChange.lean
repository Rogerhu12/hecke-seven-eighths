import HeckeGeneral.Analysis.MomentSlotScaleChange

/-!
Exact change of base for the complete literal
inverse/paired energies. This is finite-sum algebra, not source calibration
or preservation of canonical admissibility and its uniform constants.
-/

noncomputable section
namespace HeckeGeneral.Analysis.ConditionalMoments

open NumberField IsDedekindDomain HeckeGeneral.Characters
open scoped Classical BigOperators

variable {K : Type} [Field K] [NumberField K]

/-- At the new base Z^d every real length exponent is divided by d.
The endpoint parameter kappa is unchanged. -/
def RealParameters.changeBase (a : RealParameters) (d : ℝ) (_hd : 0 < d) :
    RealParameters where
  m := a.m / d
  r := a.r / d
  z := a.z / d
  q := a.q / d
  n₁ := a.n₁ / d
  n₂ := a.n₂ / d
  κ := a.κ

theorem RealParameters.changeBase_z_eq_zero_iff
    (a : RealParameters) (d : ℝ) (hd : 0 < d) :
    (a.changeBase d hd).z = 0 ↔ a.z = 0 := by
  change a.z / d = 0 ↔ a.z = 0
  simp only [div_eq_zero_iff, hd.ne', or_false]

variable {ω ψ : HeckeCharacter K}

theorem pairedRows_changeBase
    (M : MomentData K ω ψ) (a : RealParameters) (d : ℝ) (hd : 0 < d)
    {Z : ℝ} (hZ : 0 < Z) :
    pairedRows (M.changeSlotBase d hd) (a.changeBase d hd) (Z ^ d) =
      pairedRows M a Z := by
  have hmq : (Z ^ d) ^ (a.m / d + a.q / d) = Z ^ (a.m + a.q) := by
    rw [← add_div]
    exact rpow_changeBaseSlot hd hZ (a.m + a.q)
  have hz : a.z / d = 0 ↔ a.z = 0 := a.changeBase_z_eq_zero_iff d hd
  unfold pairedRows
  change (M.rows ((Z ^ d) ^ (a.m / d + a.q / d))).filter
      (fun u => if a.z / d = 0 then M.plainBackground * M.rowCharacter u ≠ 1
        else M.rowCharacter u ∉ M.theta) =
    (M.rows (Z ^ (a.m + a.q))).filter
      (fun u => if a.z = 0 then M.plainBackground * M.rowCharacter u ≠ 1
        else M.rowCharacter u ∉ M.theta)
  rw [hmq]
  simp only [hz]

theorem inverseEnergy_changeBase
    (M : MomentData K ω ψ) (a : RealParameters) (d : ℝ) (hd : 0 < d)
    {Z : ℝ} (hZ : 0 < Z) (t : ℝ) :
    inverseEnergy (M.changeSlotBase d hd) (a.changeBase d hd) (Z ^ d) t =
      inverseEnergy M a Z t := by
  unfold inverseEnergy
  change (∑ u ∈ M.rows ((Z ^ d) ^ (a.m / d)),
      ‖inversePolynomial (M.changeSlotBase d hd) u ((Z ^ d) ^ (a.r / d)) t *
        slotProduct (M.changeSlotBase d hd) u (Z ^ d) t‖ ^ 2) =
    ∑ u ∈ M.rows (Z ^ a.m),
      ‖inversePolynomial M u (Z ^ a.r) t * slotProduct M u Z t‖ ^ 2
  rw [rpow_changeBaseSlot hd hZ a.m, rpow_changeBaseSlot hd hZ a.r]
  apply Finset.sum_congr rfl
  intro u _hu
  rw [inversePolynomial_changeSlotBase, slotProduct_changeSlotBase M d hd u hZ t]

theorem pairedEnergy_changeBase
    (M : MomentData K ω ψ) (a : RealParameters) (d : ℝ) (hd : 0 < d)
    {Z : ℝ} (hZ : 0 < Z) (t : ℝ) :
    pairedEnergy (M.changeSlotBase d hd) (a.changeBase d hd) (Z ^ d) t =
      pairedEnergy M a Z t := by
  unfold pairedEnergy
  rw [pairedRows_changeBase M a d hd hZ]
  change (∑ u ∈ pairedRows M a Z,
      ‖plainPolynomial (M.changeSlotBase d hd) M.plainTest₁ u
          ((Z ^ d) ^ (a.n₁ / d)) t *
        plainPolynomial (M.changeSlotBase d hd) M.plainTest₂ u
          ((Z ^ d) ^ (a.n₂ / d)) t *
        slotProduct (M.changeSlotBase d hd) u (Z ^ d) t‖ ^ 2) =
    ∑ u ∈ pairedRows M a Z,
      ‖plainPolynomial M M.plainTest₁ u (Z ^ a.n₁) t *
        plainPolynomial M M.plainTest₂ u (Z ^ a.n₂) t * slotProduct M u Z t‖ ^ 2
  rw [rpow_changeBaseSlot hd hZ a.n₁, rpow_changeBaseSlot hd hZ a.n₂]
  apply Finset.sum_congr rfl
  intro u _hu
  rw [plainPolynomial_changeSlotBase, plainPolynomial_changeSlotBase,
    slotProduct_changeSlotBase M d hd u hZ t]

theorem MIRegion_changeBase_iff (a : RealParameters) (d : ℝ) (hd : 0 < d) :
    MIRegion (a.changeBase d hd) ↔ MIRegion a := by
  have hnonneg (x : ℝ) : 0 ≤ x / d ↔ 0 ≤ x := by
    simpa only [zero_div] using
      (div_le_div_iff_of_pos_right hd : (0 : ℝ) / d ≤ x / d ↔ 0 ≤ x)
  change (0 ≤ a.m / d ∧ 0 ≤ a.r / d ∧ 0 ≤ a.z / d ∧
      a.r / d + 2 * (a.z / d) < a.m / d ∧
      2 * (a.r / d) + 8 * (a.z / d) < 3 * (a.m / d)) ↔ MIRegion a
  rw [show a.r / d + 2 * (a.z / d) = (a.r + 2 * a.z) / d by ring,
    show 2 * (a.r / d) + 8 * (a.z / d) = (2 * a.r + 8 * a.z) / d by ring,
    show 3 * (a.m / d) = (3 * a.m) / d by ring]
  simp only [MIRegion, hnonneg, div_lt_div_iff_of_pos_right hd]

theorem PRegion_changeBase_iff (a : RealParameters) (d : ℝ) (hd : 0 < d) :
    PRegion (a.changeBase d hd) ↔ PRegion a := by
  have hz : a.z / d = 0 ↔ a.z = 0 := a.changeBase_z_eq_zero_iff d hd
  change (3 / 4 ≤ a.κ ∧ a.κ ≤ 5 / 6 ∧
      (a.z / d = 0 ∨ (0 < a.z / d ∧
        a.n₁ / d + a.n₂ / d + 6 * a.κ * (a.z / d) ≤ a.m / d + a.q / d))) ↔
    PRegion a
  rw [show a.n₁ / d + a.n₂ / d + 6 * a.κ * (a.z / d) =
      (a.n₁ + a.n₂ + 6 * a.κ * a.z) / d by ring,
    ← add_div]
  simp only [PRegion, hz, div_pos_iff_of_pos_right hd, div_le_div_iff_of_pos_right hd]

end HeckeGeneral.Analysis.ConditionalMoments
