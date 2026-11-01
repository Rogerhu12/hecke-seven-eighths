import HeckeSkeleton.Moments.MOM_ENGINE_STEP.HybridFiniteLeaf

/-!
# The live finite carrier is determined by actual coefficient support

Zero scalar weights and branches with an identically zero left or
right whole column contribute zero to both the exceptional and ordinary
terms.  Removing them is an exact identity before either continuous
Fourier variable.  Each retained leaf supplies actual finite row/column
witnesses, which connect the original coefficient gates to arithmetic
common-support conditions.
-/

noncomputable section
open scoped Classical BigOperators NumberField SchwartzMap
open MeasureTheory

namespace HeckeSkeleton.Moments.EngineStep

variable {K : Type} [Field K] [NumberField K]
variable {H U V : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

namespace ActualHybridLeaf

variable (B : ActualHybridLeaf K H U V)

def LeftPresent : Prop :=
  ∃ h ∈ B.rows, ∃ i ∈ B.left, B.leftCoefficient h i ≠ 0

def RightPresent : Prop :=
  ∃ h ∈ B.rows, ∃ i ∈ B.right, B.rightCoefficient h i ≠ 0

def Live : Prop := B.weight ≠ 0 ∧ B.LeftPresent ∧ B.RightPresent

theorem integrands_zero_of_not_leftPresent (hB : ¬B.LeftPresent) :
    (∀ z, B.exceptionalIntegrand z = 0) ∧ (∀ z, B.ordinaryIntegrand z = 0) := by
  have hc : ∀ h ∈ B.rows, ∀ i ∈ B.left, B.leftCoefficient h i = 0 := by
    intro h hh i hi
    by_contra hne
    exact hB ⟨h, hh, i, hi, hne⟩
  have hp (h : H) (hh : h ∈ B.rows)
      (x : AllocationColumn K B.leftSlots → WithLp 2 (U × V))
      (ξ : WithLp 2 (U × V)) :
      jointFourierColumn B.left (B.leftCoefficient h) x ξ = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [hc h hh i hi, zero_mul]
  constructor
  · intro z
    unfold exceptionalIntegrand jointColumnPairMagnitude
    apply Finset.sum_eq_zero
    intro h hh
    simp only [hp h (Finset.mem_filter.mp hh).1, norm_zero, mul_zero, zero_mul]
  · intro z
    have he : jointColumnEnergy (B.rows.filter fun h => ¬B.exceptional h) B.left
        B.rowWeight B.leftCoefficient
        (fun h i => WithLp.toLp 2 (B.leftFirst h i, B.leftSecond h i))
        (WithLp.toLp 2 z) = 0 := by
      apply Finset.sum_eq_zero
      intro h hh
      simp only [hp h (Finset.mem_filter.mp hh).1, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0),
        mul_zero]
    change Real.sqrt _ * Real.sqrt _ = 0
    rw [he, Real.sqrt_zero, zero_mul]

theorem integrands_zero_of_not_rightPresent (hB : ¬B.RightPresent) :
    (∀ z, B.exceptionalIntegrand z = 0) ∧ (∀ z, B.ordinaryIntegrand z = 0) := by
  have hc : ∀ h ∈ B.rows, ∀ i ∈ B.right, B.rightCoefficient h i = 0 := by
    intro h hh i hi
    by_contra hne
    exact hB ⟨h, hh, i, hi, hne⟩
  have hp (h : H) (hh : h ∈ B.rows)
      (x : AllocationColumn K B.rightSlots → WithLp 2 (U × V))
      (ξ : WithLp 2 (U × V)) :
      jointFourierColumn B.right (fun i => star (B.rightCoefficient h i)) x ξ = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    change star (B.rightCoefficient h i) * jointPhase ξ (x i) = 0
    rw [hc h hh i hi, star_zero, zero_mul]
  constructor
  · intro z
    unfold exceptionalIntegrand jointColumnPairMagnitude
    apply Finset.sum_eq_zero
    intro h hh
    simp only [hp h (Finset.mem_filter.mp hh).1, norm_zero, mul_zero]
  · intro z
    have he : jointColumnEnergy (B.rows.filter fun h => ¬B.exceptional h) B.right
        B.rowWeight (fun h i => star (B.rightCoefficient h i))
        (fun h i => WithLp.toLp 2 (-B.rightFirst h i, B.rightSecond h i))
        (WithLp.toLp 2 z) = 0 := by
      apply Finset.sum_eq_zero
      intro h hh
      simp only [hp h (Finset.mem_filter.mp hh).1, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0),
        mul_zero]
    change Real.sqrt _ * Real.sqrt _ = 0
    rw [he, Real.sqrt_zero, mul_zero]

/-- Both terminal components vanish on every omitted label, not just
their total. -/
theorem costs_zero_of_not_live (hB : ¬B.Live) :
    B.exceptionalCost = 0 ∧ B.ordinaryCost = 0 := by
  by_cases hw : B.weight = 0
  · exact ⟨B.exceptionalCost_eq_zero_of_weight_eq_zero hw,
      B.ordinaryCost_eq_zero_of_weight_eq_zero hw⟩
  have hi : (∀ z, B.exceptionalIntegrand z = 0) ∧ (∀ z, B.ordinaryIntegrand z = 0) := by
    by_cases hl : B.LeftPresent
    · apply B.integrands_zero_of_not_rightPresent
      intro hr
      exact hB ⟨hw, hl, hr⟩
    · exact B.integrands_zero_of_not_leftPresent hl
  constructor
  · simp only [exceptionalCost, funext hi.1, integral_zero, mul_zero]
  · simp only [ordinaryCost, funext hi.2, integral_zero, mul_zero]

theorem cost_zero_of_not_live (hB : ¬B.Live) : B.cost = 0 := by
  rw [cost, (B.costs_zero_of_not_live hB).1, (B.costs_zero_of_not_live hB).2, add_zero]

end ActualHybridLeaf

namespace ActualHybridFamily

variable {ι : Type*} [Fintype ι]
variable (B : ι → ActualHybridLeaf K H U V)

def live : Finset ι := Finset.univ.filter fun i => (B i).Live

theorem sum_cost_eq_live :
    (∑ i, (B i).cost) = ∑ i : live B, (B i.val).cost := by
  refine Eq.trans ?_ (Finset.sum_coe_sort (live B) (fun i => (B i).cost)).symm
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro i _ hi
  apply (B i).cost_zero_of_not_live
  intro hLive
  exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hLive⟩)

theorem sum_exceptionalCost_eq_live :
    (∑ i, (B i).exceptionalCost) = ∑ i : live B, (B i.val).exceptionalCost := by
  refine Eq.trans ?_
    (Finset.sum_coe_sort (live B) (fun i => (B i).exceptionalCost)).symm
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro i _ hi
  apply ((B i).costs_zero_of_not_live _).1
  intro hLive
  exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hLive⟩)

theorem sum_ordinaryCost_eq_live :
    (∑ i, (B i).ordinaryCost) = ∑ i : live B, (B i.val).ordinaryCost := by
  refine Eq.trans ?_
    (Finset.sum_coe_sort (live B) (fun i => (B i).ordinaryCost)).symm
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro i _ hi
  apply ((B i).costs_zero_of_not_live _).2
  intro hLive
  exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hLive⟩)

theorem live_spec (i : live B) : (B i.val).Live :=
  (Finset.mem_filter.mp i.property).2

end ActualHybridFamily
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.ActualHybridLeaf.costs_zero_of_not_live
#print axioms HeckeSkeleton.Moments.EngineStep.ActualHybridFamily.sum_cost_eq_live

