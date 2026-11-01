import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondBranchProduction

/-!
# Exact row partitions before ordinary and exceptional child estimates

The actual complete coefficient, including a centered subtraction, is
unchanged when the original rows are restricted.  The energy is the sum
of the two genuine restricted energies.  Only the square-root inequality
is used after this identity; no incorrect same-class paired inequality
is inferred from a previously applied Cauchy inequality.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree HeckeGeneral.Characters

variable {F : Type} [Field F] [NumberField F]
variable {A : SArithmeticData F} {σ : F →+* ℂ}
variable {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {H ι V : Type*} [Fintype ι] [DecidableEq ι]
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def ActualSecondCorrelationRows.restrictRows (R : ActualSecondCorrelationRows A σ H ι)
    (p : H → Prop) : ActualSecondCorrelationRows A σ H ι :=
  { R with
    rows := R.rows.filter p
    generates := fun h hh => R.generates h (Finset.mem_filter.mp hh).1 }

theorem sqrt_add_le_sqrt_add_sqrt (x y : ℝ) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _), ?_⟩
  have hx : x ≤ (Real.sqrt x) ^ 2 := by
    rw [Real.sq_sqrt']
    exact le_max_left _ _
  have hy : y ≤ (Real.sqrt y) ^ 2 := by
    rw [Real.sq_sqrt']
    exact le_max_left _ _
  nlinarith [mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)]

namespace SecondSideFrame

variable {C : A.GeneralArithmeticContext σ η hS}
variable {R : ActualSecondCorrelationRows A σ H ι}
variable {Ray : Type*} [CommGroup Ray] [Fintype Ray]
variable {side : SecondColumnSide} {k : ℕ}
variable (f : SecondSideFrame (V := V) C R Ray side k)

def restrictRows (p : H → Prop) :
    SecondSideFrame (V := V) C (R.restrictRows p) Ray side k where
  allocation := f.allocation
  characters := f.characters
  phaseCharacter := f.phaseCharacter
  dictionary := f.dictionary
  base_gt_one := f.base_gt_one
  length_pos := f.length_pos
  ideal := f.ideal
  ideal_product := f.ideal_product
  gaussScale₁ := f.gaussScale₁
  gaussScale₂ := f.gaussScale₂
  gaussSlotScale := f.gaussSlotScale
  gaussScale₁_pos := f.gaussScale₁_pos
  gaussScale₂_pos := f.gaussScale₂_pos
  gaussSlotScale_pos := f.gaussSlotScale_pos
  leftLocation := f.leftLocation
  rightLocation := f.rightLocation
  slotLocation := f.slotLocation

theorem energy_partition (p : H → Prop) (ξ : V) :
    (f.restrictRows p).energy ξ + (f.restrictRows (fun h => ¬p h)).energy ξ = f.energy ξ := by
  cases side
  all_goals
    change (∑ h ∈ R.rows.filter p, ‖R.weight h * R.correlation h‖ *
        ‖jointFourierColumn f.allocation.columns (f.coefficient h)
          (rawSourceLocation (f.leftLocation h) (f.rightLocation h) (f.slotLocation h)) ξ‖ ^ 2) +
      (∑ h ∈ R.rows.filter (fun h => ¬p h), ‖R.weight h * R.correlation h‖ *
        ‖jointFourierColumn f.allocation.columns (f.coefficient h)
          (rawSourceLocation (f.leftLocation h) (f.rightLocation h) (f.slotLocation h)) ξ‖ ^ 2) = _
    exact Finset.sum_filter_add_sum_filter_not R.rows p _


/-- The entire subtraction is retained on each part, including every
ramification zero and every slot factor. -/
theorem centered_energy_partition (e : SecondCoefficientComparison f.dictionary)
    (p : H → Prop) (ξ : V) :
    (f.restrictRows p).centeredEnergy e ξ +
      (f.restrictRows (fun h => ¬p h)).centeredEnergy e ξ = f.centeredEnergy e ξ := by
  cases side
  all_goals
    change (∑ h ∈ R.rows.filter p, ‖R.weight h * R.correlation h‖ *
        ‖jointFourierColumn f.allocation.columns (f.centeredCoefficient e h)
          (rawSourceLocation (f.leftLocation h) (f.rightLocation h) (f.slotLocation h)) ξ‖ ^ 2) +
      (∑ h ∈ R.rows.filter (fun h => ¬p h), ‖R.weight h * R.correlation h‖ *
        ‖jointFourierColumn f.allocation.columns (f.centeredCoefficient e h)
          (rawSourceLocation (f.leftLocation h) (f.rightLocation h) (f.slotLocation h)) ξ‖ ^ 2) = _
    exact Finset.sum_filter_add_sum_filter_not R.rows p _


theorem sqrt_energy_partition (p : H → Prop) (ξ : V) :
    Real.sqrt (f.energy ξ) ≤ Real.sqrt ((f.restrictRows p).energy ξ) +
      Real.sqrt ((f.restrictRows (fun h => ¬p h)).energy ξ) := by
  rw [← f.energy_partition p ξ]
  exact sqrt_add_le_sqrt_add_sqrt _ _

end SecondSideFrame
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.SecondSideFrame.centered_energy_partition
