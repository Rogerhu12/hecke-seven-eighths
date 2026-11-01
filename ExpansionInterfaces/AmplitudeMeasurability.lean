import ExpansionInterfaces.AmplitudePartition
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# Measurability of the actual finite amplitude labels

The zero branch and the natural-floor cap are both retained.  The result is
for arbitrary measurable complex slot functions, with no continuity or
nonvanishing assumption.  This supplies the measurable label sets for the
pointwise partition under the retained contour integral.
-/

noncomputable section
namespace ExpansionInterfaces

variable {X : Type*} [MeasurableSpace X]

/-- Direct proof from the natural-floor interval fibers.  This is the
real specialization of the standard measurable-floor argument. -/
theorem measurable_natFloor_real : Measurable (Nat.floor : ℝ → ℕ) := by
  apply measurable_to_countable'
  intro n
  by_cases hn : n = 0
  · subst n
    simpa only [Nat.preimage_floor_zero] using
      (measurableSet_Iio : MeasurableSet (Set.Iio (1 : ℝ)))
  · simpa only [Nat.preimage_floor_of_ne_zero hn] using
      (measurableSet_Ico : MeasurableSet (Set.Ico (n : ℝ) ((n : ℝ) + 1)))

theorem measurable_amplitudeCode_val (width cap : ℝ) {f : X → ℝ}
    (hf : Measurable f) :
    Measurable (fun x => (amplitudeCode width cap (f x)).val) := by
  exact measurable_const.min (measurable_natFloor_real.comp (hf.div_const width))

theorem measurable_slotCode_val (width cap P : ℝ) {Q : X → ℂ}
    (hQ : Measurable Q) :
    Measurable (fun x => (slotCode width cap P (Q x)).val) := by
  have hz : MeasurableSet {x | Q x = 0} := hQ (measurableSet_singleton 0)
  have hlog : Measurable (fun x => Real.log ‖Q x‖ / Real.log P) :=
    (Real.measurable_log.comp hQ.norm).div_const _
  have hraw := measurable_amplitudeCode_val width cap hlog
  simpa only [slotCode, apply_ite] using Measurable.ite hz measurable_const hraw

theorem measurableSet_slotCode_eq (width cap P : ℝ) {Q : X → ℂ}
    (hQ : Measurable Q) (code : AmplitudeCode width cap) :
    MeasurableSet {x | slotCode width cap P (Q x) = code} := by
  have h := measurable_slotCode_val width cap P hQ (measurableSet_singleton code.val)
  simpa only [Set.preimage, Set.mem_singleton_iff, Fin.ext_iff] using h

/-- Every finite amplitude vector gives a measurable part of the contour domain. -/
theorem measurableSet_amplitudeLabel_eq (J : ℕ) (width cap : ℝ)
    (P : Fin J → ℝ) (Q : Fin J → X → ℂ) (hQ : ∀ i, Measurable (Q i))
    (label : AmplitudeLabels J width cap) :
    MeasurableSet {x | (fun i => slotCode width cap (P i) (Q i x)) = label} := by
  have heq : {x | (fun i => slotCode width cap (P i) (Q i x)) = label} =
      ⋂ i : Fin J, {x | slotCode width cap (P i) (Q i x) = label i} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    exact funext_iff
  rw [heq]
  exact MeasurableSet.iInter fun i => measurableSet_slotCode_eq width cap (P i) (hQ i) (label i)

end ExpansionInterfaces
