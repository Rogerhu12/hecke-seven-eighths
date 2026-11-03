import HeckeSkeleton.Moments.MOM_ENGINE_STEP.Capacity
import HeckeGeneral.Analysis.SelectedMomentSlots

/-!
# Capacity repair for the repository's actual paired energy

The selected child is `MomentData.restrictSlots`, not a new polynomial
model.  The same row characters, common ideal mask, plain profiles and
finite prime sums are retained.  Updating `z` may change the exceptional
row predicate; `principal_mem_theta` states the precise finite-background
input needed when the last slot is removed.
-/

noncomputable section
open scoped Classical BigOperators

namespace HeckeSkeleton.Moments.EngineStep

open NumberField HeckeGeneral.Characters
open HeckeGeneral.Analysis HeckeGeneral.Analysis.ConditionalMoments

variable {K : Type} [Field K] [NumberField K]
variable {ω ψ : HeckeCharacter K}

def remainingParameters (d : MomentData K ω ψ) (a : RealParameters)
    (keep : Finset (Fin d.geometry.slotCount)) : RealParameters :=
  { a with z := (d.geometry.restrictSlots keep).totalLength }

theorem remainingParameters_z_nonneg (d : MomentData K ω ψ) (a : RealParameters)
    (keep : Finset (Fin d.geometry.slotCount)) :
    0 ≤ (remainingParameters d a keep).z := by
  change 0 ≤ (d.geometry.restrictSlots keep).totalLength
  rw [SlotGeometry.totalLength_restrictSlots]
  exact Finset.sum_nonneg (fun i _ => (d.geometry.slots i).length_pos.le)

theorem remainingParameters_z_le (d : MomentData K ω ψ) (a : RealParameters)
    (keep : Finset (Fin d.geometry.slotCount)) (hz : a.z = d.geometry.totalLength) :
    (remainingParameters d a keep).z ≤ a.z := by
  change (d.geometry.restrictSlots keep).totalLength ≤ a.z
  rw [SlotGeometry.totalLength_restrictSlots, hz]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ keep)
    (fun i _ _ => (d.geometry.slots i).length_pos.le)

theorem pairedRows_subset_after_removal (d : MomentData K ω ψ) (a : RealParameters)
    (keep : Finset (Fin d.geometry.slotCount)) (hz : a.z = d.geometry.totalLength)
    (principal_mem_theta : ∀ u : NonzeroIdeal K,
      d.plainBackground * d.rowCharacter u = 1 → d.rowCharacter u ∈ d.theta) (Z : ℝ) :
    pairedRows d a Z ⊆ pairedRows (d.restrictSlots keep) (remainingParameters d a keep) Z := by
  intro u hu
  have hu' := Finset.mem_filter.mp hu
  apply Finset.mem_filter.mpr
  refine ⟨hu'.1, ?_⟩
  change (if (remainingParameters d a keep).z = 0 then
    d.plainBackground * d.rowCharacter u ≠ 1 else d.rowCharacter u ∉ d.theta)
  by_cases hnew : (remainingParameters d a keep).z = 0
  · rw [if_pos hnew]
    by_cases hold : a.z = 0
    · simpa only [hold, if_true] using hu'.2
    · have hex : d.rowCharacter u ∉ d.theta := by
        simpa only [hold, if_false] using hu'.2
      exact fun hprincipal => hex (principal_mem_theta u hprincipal)
  · rw [if_neg hnew]
    have hold : a.z ≠ 0 := by
      intro heq
      apply hnew
      exact le_antisymm (by simpa only [heq] using remainingParameters_z_le d a keep hz)
        (remainingParameters_z_nonneg d a keep)
    simpa only [hold, if_false] using hu'.2

/-- The admissible successor set and the bound on the actual finite
`pairedEnergy` are obtained by the same single whole-slot removal. -/
theorem actual_paired_capacity_step (d : MomentData K ω ψ) (a : RealParameters)
    (mesh Δ err : ℝ) (hκ : 0 < a.κ) (hmesh : 0 ≤ mesh)
    (hfit : d.geometry.fitsMesh mesh) (hz : a.z = d.geometry.totalLength)
    (principal_mem_theta : ∀ u : NonzeroIdeal K,
      d.plainBackground * d.rowCharacter u = 1 → d.rowCharacter u ∈ d.theta)
    (hdefect : max (a.n₁ + a.n₂ + 6 * a.κ * a.z - (a.m + a.q)) 0 ≤ 6 * Δ + err) :
    ∃ removed : Finset (Fin d.geometry.slotCount),
      let keep := Finset.univ \ removed
      let a' := remainingParameters d a keep
      (a'.z = 0 ∨ a.n₁ + a.n₂ + 6 * a.κ * a'.z ≤ a.m + a.q) ∧
      ∀ Z : ℝ, 1 ≤ Z → ∀ C : Fin d.geometry.slotCount → ℝ,
        (∀ i, 0 ≤ C i) → ∀ t : ℝ,
        (∀ u ∈ pairedRows d a Z, ∀ i,
          ‖primePolynomial d i u Z t‖ ^ 2 ≤ C i * Z ^ (a.κ * (d.geometry.slots i).length)) →
        pairedEnergy d a Z t ≤
          (∏ i ∈ removed, C i) * Z ^ (Δ + err / 6 + a.κ * mesh) *
            pairedEnergy (d.restrictSlots keep) a' Z t := by
  have hdefect' : capacityDefect Finset.univ (fun i => (d.geometry.slots i).length)
      a.n₁ a.n₂ (a.m + a.q) a.κ ≤ 6 * Δ + err := by
    simpa only [capacityDefect, hz, SlotGeometry.totalLength] using hdefect
  obtain ⟨removed, hR, hcap, hbound⟩ := capacity_energy_step
    (H := NonzeroIdeal K) Finset.univ (fun i => (d.geometry.slots i).length)
    a.n₁ a.n₂ (a.m + a.q) a.κ mesh Δ err hκ hmesh
    (fun i _ => (d.geometry.slots i).length_pos.le) (fun i _ => hfit i) hdefect'
  refine ⟨removed, ?_⟩
  dsimp only
  constructor
  · rcases hcap with hremoved | hcapacity
    · left
      simp only [hremoved, Finset.sdiff_self, remainingParameters,
        SlotGeometry.totalLength_restrictSlots, Finset.sum_empty]
    · right
      simpa only [remainingParameters, SlotGeometry.totalLength_restrictSlots] using hcapacity
  · intro Z hZ C hC t hprime
    let keep := Finset.univ \ removed
    let a' := remainingParameters d a keep
    let f : NonzeroIdeal K → ℝ := fun u =>
      ‖plainPolynomial d d.plainTest₁ u (Z ^ a.n₁) t *
        plainPolynomial d d.plainTest₂ u (Z ^ a.n₂) t *
        ∏ i ∈ keep, primePolynomial d i u Z t‖ ^ 2
    have hb := hbound Z hZ C (fun i _ => hC i) (pairedRows d a Z)
      (fun u i => primePolynomial d i u Z t)
      (fun u => plainPolynomial d d.plainTest₁ u (Z ^ a.n₁) t)
      (fun u => plainPolynomial d d.plainTest₂ u (Z ^ a.n₂) t)
      (fun _ => 1) (fun _ _ => zero_le_one) (fun u hu i _ => hprime u hu i)
    simp only [one_mul] at hb
    have hs : (∑ u ∈ pairedRows d a Z, f u) ≤
        ∑ u ∈ pairedRows (d.restrictSlots keep) a' Z, f u :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (pairedRows_subset_after_removal d a keep hz principal_mem_theta Z)
        (fun _ _ _ => sq_nonneg _)
    have hchild : (∑ u ∈ pairedRows (d.restrictSlots keep) a' Z, f u) =
        pairedEnergy (d.restrictSlots keep) a' Z t := by
      symm
      rw [pairedEnergy_restrictSlots]
      rfl
    rw [hchild] at hs
    have hfactor : 0 ≤ (∏ i ∈ removed, C i) * Z ^ (Δ + err / 6 + a.κ * mesh) :=
      mul_nonneg (Finset.prod_nonneg (fun i _ => hC i))
        (Real.rpow_nonneg (zero_le_one.trans hZ) _)
    exact hb.trans (mul_le_mul_of_nonneg_left hs hfactor)

end HeckeSkeleton.Moments.EngineStep
