import HeckeSkeleton.Moments.MOM_PRIME.AbsoluteBounds
import HeckeGeneral.Analysis.ActualPrimeGeometryAbsoluteBound
import HeckeGeneral.Analysis.MomentSlotScaleChange

/-!
# Endpoint estimates for the fixed physical prime geometry

The compact smooth windows in `PrimeWindowGeometry` supply their own common
profile bound.  Changing the external base and selecting any subset of
slots preserve those profiles.  Consequently a single constant works for
every positive shell length, every selection, every actual row character,
and every common mask.  The exponent is the literal selected TIP length.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_PRIME

open NumberField IsDedekindDomain Set
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Physical HeckeGeneral.ThetaSkeleton.Global
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]

/-- The pointwise κ = 1 estimate for fixed physical prime windows, uniform
also in the row ideal and in its complete original mask. -/
theorem exists_actualSelectedPrimeGeometry_slotProduct_bound (g : PrimeWindowGeometry) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ω ψ : HeckeCharacter K} (d : MomentData K ω ψ)
      (shell : ℝ) (hshell : 0 < shell) (I : Finset (Fin g.slots))
      (u : NonzeroIdeal K) (Z t : ℝ),
      d.geometry = ((momentPrimeGeometry K g).changeBase shell hshell).restrictSlots I →
      1 ≤ Z →
      ‖slotProduct d u Z t‖ ^ 2 ≤
        C * Z ^ (∑ _i ∈ I, HeckeGeneral.ThetaSkeleton.TIP.slotLength g.slots shell) := by
  obtain ⟨B, hB, hprofile⟩ := exists_actualMomentPrimeGeometry_profile_bound K g
  obtain ⟨C, hC, hbound⟩ := exists_slotProductAbsoluteBound K g.slots B hB.le
  refine ⟨C, hC, ?_⟩
  intro ω ψ d shell hshell I u Z t hgeom hZ
  have hn : d.geometry.slotCount ≤ g.slots := by
    rw [hgeom]
    change I.card ≤ g.slots
    simpa only [Fintype.card_fin] using Finset.card_le_univ I
  have hann : ∀ i,
      Function.support ((d.geometry.slots i).profile t) ⊆ Ioo (1 : ℝ) 2 := by
    rw [hgeom]
    intro i
    exact g.support_annular (selectedSlotIndex I i)
  have hprof : ∀ i y, ‖(d.geometry.slots i).profile t y‖ ≤ B * (1 : ℝ) ^ (0 : ℝ) := by
    simp only [Real.rpow_zero, mul_one]
    rw [hgeom]
    intro i y
    exact hprofile (selectedSlotIndex I i) t y
  have hlength : d.geometry.totalLength =
      ∑ _i ∈ I, HeckeGeneral.ThetaSkeleton.TIP.slotLength g.slots shell := by
    rw [hgeom, momentPrimeGeometry_selectedLength_changeBase]
  simpa only [Real.one_rpow, mul_one, hlength] using
    hbound d u Z t 1 0 hZ le_rfl le_rfl hn hann hprof

/-- Full uniformity for the source's fixed windows after a shell change and
selection.  The only identification required of a model is equality of its
prime geometry; its ideal tests, characters, and masks stay arbitrary. -/
theorem exists_actualSelectedPrimeGeometry_absolute_bound (g : PrimeWindowGeometry) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ω ψ : HeckeCharacter K} (d : MomentData K ω ψ)
      (shell : ℝ) (hshell : 0 < shell) (I : Finset (Fin g.slots))
      (a : RealParameters) (Z t : ℝ),
      d.geometry = ((momentPrimeGeometry K g).changeBase shell hshell).restrictSlots I →
      1 ≤ Z → 0 ≤ a.m + a.q →
      (∑ u ∈ pairedRows d a Z, ‖slotProduct d u Z t‖ ^ 2) ≤
        C * Z ^ (a.m + a.q +
          ∑ _i ∈ I, HeckeGeneral.ThetaSkeleton.TIP.slotLength g.slots shell) := by
  obtain ⟨B, hB, hprofile⟩ := exists_actualMomentPrimeGeometry_profile_bound K g
  obtain ⟨C, hC, hbound⟩ := exists_pairedPrimeAbsoluteBound_fixed K g.slots B hB.le
  refine ⟨C, hC, ?_⟩
  intro ω ψ d shell hshell I a Z t hgeom hZ hM
  have hn : d.geometry.slotCount ≤ g.slots := by
    rw [hgeom]
    change I.card ≤ g.slots
    simpa only [Fintype.card_fin] using Finset.card_le_univ I
  have hann : ∀ i,
      Function.support ((d.geometry.slots i).profile t) ⊆ Ioo (1 : ℝ) 2 := by
    rw [hgeom]
    intro i
    exact g.support_annular (selectedSlotIndex I i)
  have hprof : ∀ i y, ‖(d.geometry.slots i).profile t y‖ ≤ B := by
    rw [hgeom]
    intro i y
    exact hprofile (selectedSlotIndex I i) t y
  have hlength : d.geometry.totalLength =
      ∑ _i ∈ I, HeckeGeneral.ThetaSkeleton.TIP.slotLength g.slots shell := by
    rw [hgeom, momentPrimeGeometry_selectedLength_changeBase]
  simpa only [hlength] using hbound d a Z t hZ hM hn hann hprof

/-- The literal data operation installing the fixed geometry and then
changing its base and selecting slots.  All other `MomentData` fields are
inherited from `d`, including the row enumeration and common mask. -/
abbrev actualSelectedPrimeGeometryMomentData {ω ψ : HeckeCharacter K}
    (g : PrimeWindowGeometry) (d : MomentData K ω ψ)
    (χ : Fin g.slots → HeckeCharacter K) (shell : ℝ) (hshell : 0 < shell)
    (I : Finset (Fin g.slots)) : MomentData K ω ψ :=
  ((actualPrimeGeometryMomentData K g d χ).changeSlotBase shell hshell).restrictSlots I

/-- Concrete instantiation of the uniform selected-slot estimate.  In
particular, the empty selection yields the same linear row estimate. -/
theorem exists_actualSelectedPrimeGeometryMomentData_absolute_bound (g : PrimeWindowGeometry) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ω ψ : HeckeCharacter K} (d : MomentData K ω ψ)
      (χ : Fin g.slots → HeckeCharacter K) (shell : ℝ) (hshell : 0 < shell)
      (I : Finset (Fin g.slots)) (a : RealParameters) (Z t : ℝ),
      1 ≤ Z → 0 ≤ a.m + a.q →
      (∑ u ∈ pairedRows (actualSelectedPrimeGeometryMomentData K g d χ shell hshell I) a Z,
        ‖slotProduct (actualSelectedPrimeGeometryMomentData K g d χ shell hshell I) u Z t‖ ^ 2) ≤
        C * Z ^ (a.m + a.q +
          ∑ _i ∈ I, HeckeGeneral.ThetaSkeleton.TIP.slotLength g.slots shell) := by
  obtain ⟨C, hC, hbound⟩ := exists_actualSelectedPrimeGeometry_absolute_bound K g
  refine ⟨C, hC, ?_⟩
  intro ω ψ d χ shell hshell I a Z t hZ hM
  exact hbound (actualSelectedPrimeGeometryMomentData K g d χ shell hshell I)
    shell hshell I a Z t rfl hZ hM

end HeckeSkeleton.Moments.MOM_PRIME
