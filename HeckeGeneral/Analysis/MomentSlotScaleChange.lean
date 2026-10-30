import HeckeGeneral.Analysis.SelectedMomentSlots
import HeckeGeneral.Analysis.MomentPrimeWindows
import HeckeGeneral.Analysis.TIPSources

/-!
Exact change of the external base for actual moment prime slots.
At U = Z^d, dividing every slot length by d preserves the actual prime
scale. Profiles, their exact supports, characters, masks, ideal tests and
all independent witness heights are retained literally. The selected-slot
lengths and mesh are converted exactly, including the empty selection.
No admissibility or moment inequality is asserted.

-/

noncomputable section
namespace HeckeGeneral.Analysis.ConditionalMoments

open NumberField IsDedekindDomain HeckeGeneral.Characters
open scoped Classical BigOperators

variable {K : Type} [Field K] [NumberField K]

/-- A slot at base Z becomes a slot of length length/d at base Z^d.
Its profile, time parameter and exact analytic support are unchanged. -/
abbrev PrimeWindow.changeBase (W : PrimeWindow K) (d : ℝ) (hd : 0 < d) :
    PrimeWindow K :=
  { W with
    length := W.length / d
    length_pos := div_pos W.length_pos hd }

@[simp] theorem PrimeWindow.length_changeBase
    (W : PrimeWindow K) (d : ℝ) (hd : 0 < d) :
    (W.changeBase d hd).length = W.length / d := rfl

@[simp] theorem PrimeWindow.profile_changeBase
    (W : PrimeWindow K) (d : ℝ) (hd : 0 < d) :
    (W.changeBase d hd).profile = W.profile := rfl

@[simp] theorem PrimeWindow.support_changeBase
    (W : PrimeWindow K) (d : ℝ) (hd : 0 < d) :
    (W.changeBase d hd).support = W.support := rfl

abbrev SlotGeometry.changeBase (g : SlotGeometry K) (d : ℝ) (hd : 0 < d) :
    SlotGeometry K where
  slotCount := g.slotCount
  slots i := (g.slots i).changeBase d hd

@[simp] theorem SlotGeometry.slotCount_changeBase
    (g : SlotGeometry K) (d : ℝ) (hd : 0 < d) :
    (g.changeBase d hd).slotCount = g.slotCount := rfl

@[simp] theorem SlotGeometry.length_changeBase
    (g : SlotGeometry K) (d : ℝ) (hd : 0 < d) (i : Fin g.slotCount) :
    ((g.changeBase d hd).slots i).length = (g.slots i).length / d := rfl

theorem SlotGeometry.totalLength_changeBase
    (g : SlotGeometry K) (d : ℝ) (hd : 0 < d) :
    (g.changeBase d hd).totalLength = g.totalLength / d := by
  change (∑ i, (g.slots i).length / d) = (∑ i, (g.slots i).length) / d
  simp only [div_eq_mul_inv, Finset.sum_mul]

/-- Mesh at base Z^d is multiplied by d when expressed at base Z. -/
theorem SlotGeometry.fitsMesh_changeBase_iff
    (g : SlotGeometry K) (d : ℝ) (hd : 0 < d) (mesh : ℝ) :
    (g.changeBase d hd).fitsMesh mesh ↔ g.fitsMesh (mesh * d) := by
  constructor
  · intro h i
    exact (div_le_iff₀ hd).mp (h i)
  · intro h i
    exact (div_le_iff₀ hd).mpr (h i)

theorem SlotGeometry.fitsMesh_changeBase_div_iff
    (g : SlotGeometry K) (d : ℝ) (hd : 0 < d) (mesh : ℝ) :
    (g.changeBase d hd).fitsMesh (mesh / d) ↔ g.fitsMesh mesh := by
  rw [SlotGeometry.fitsMesh_changeBase_iff, div_mul_cancel₀ _ hd.ne']

/-- Selection and changing the base commute without reindexing characters. -/
theorem SlotGeometry.changeBase_restrictSlots
    (g : SlotGeometry K) (d : ℝ) (hd : 0 < d)
    (I : Finset (Fin g.slotCount)) :
    (g.changeBase d hd).restrictSlots I = (g.restrictSlots I).changeBase d hd := rfl

theorem SlotGeometry.selectedLength_changeBase
    (g : SlotGeometry K) (d : ℝ) (hd : 0 < d)
    (I : Finset (Fin g.slotCount)) :
    ((g.changeBase d hd).restrictSlots I).totalLength =
      (∑ i ∈ I, (g.slots i).length) / d := by
  rw [SlotGeometry.changeBase_restrictSlots, SlotGeometry.totalLength_changeBase,
    SlotGeometry.totalLength_restrictSlots]

/-- The converse to the existing sufficient selected-mesh lemma. Empty
selections impose no mesh condition. -/
theorem SlotGeometry.fitsMesh_restrictSlots_iff
    (g : SlotGeometry K) (I : Finset (Fin g.slotCount)) (mesh : ℝ) :
    (g.restrictSlots I).fitsMesh mesh ↔ ∀ i ∈ I, (g.slots i).length ≤ mesh := by
  constructor
  · intro h i hi
    let j : Fin I.card := I.equivFin ⟨i, hi⟩
    have hj : selectedSlotIndex I j = i := by
      exact congrArg Subtype.val (I.equivFin.symm_apply_apply ⟨i, hi⟩)
    have hji := h j
    change (g.slots (selectedSlotIndex I j)).length ≤ mesh at hji
    rw [hj] at hji
    exact hji
  · exact fun h => SlotGeometry.fitsMesh_restrictSlots g I h

theorem SlotGeometry.selectedFitsMesh_changeBase_iff
    (g : SlotGeometry K) (d : ℝ) (hd : 0 < d)
    (I : Finset (Fin g.slotCount)) (mesh : ℝ) :
    ((g.changeBase d hd).restrictSlots I).fitsMesh mesh ↔
      ∀ i ∈ I, (g.slots i).length ≤ mesh * d := by
  rw [SlotGeometry.changeBase_restrictSlots, SlotGeometry.fitsMesh_changeBase_iff,
    SlotGeometry.fitsMesh_restrictSlots_iff]

theorem rpow_changeBaseSlot {d Z : ℝ} (hd : 0 < d) (hZ : 0 < Z) (length : ℝ) :
    (Z ^ d) ^ (length / d) = Z ^ length := by
  have hmul : d * (length / d) = length := by
    rw [mul_comm, div_mul_cancel₀ _ hd.ne']
  rw [← Real.rpow_mul hZ.le, hmul]

variable {ω ψ : HeckeCharacter K}

/-- Only the slot geometry is changed. Inverse/plain scales and all of
their independently selected heights remain available as before. -/
abbrev MomentData.changeSlotBase (M : MomentData K ω ψ) (d : ℝ) (hd : 0 < d) :
    MomentData K ω ψ :=
  { M with
    geometry := M.geometry.changeBase d hd
    slotCoefficient := M.slotCoefficient }

@[simp] theorem MomentData.rowCharacter_changeSlotBase
    (M : MomentData K ω ψ) (d : ℝ) (hd : 0 < d) :
    (M.changeSlotBase d hd).rowCharacter = M.rowCharacter := rfl

@[simp] theorem MomentData.commonMask_changeSlotBase
    (M : MomentData K ω ψ) (d : ℝ) (hd : 0 < d) :
    (M.changeSlotBase d hd).commonMask = M.commonMask := rfl

@[simp] theorem maskValue_changeSlotBase
    (M : MomentData K ω ψ) (d : ℝ) (hd : 0 < d)
    (u : NonzeroIdeal K) (I : Ideal (𝓞 K)) :
    maskValue (M.changeSlotBase d hd) u I = maskValue M u I := rfl

@[simp] theorem inversePolynomial_changeSlotBase
    (M : MomentData K ω ψ) (d : ℝ) (hd : 0 < d)
    (u : NonzeroIdeal K) (D t : ℝ) :
    inversePolynomial (M.changeSlotBase d hd) u D t =
      inversePolynomial M u D t := rfl

@[simp] theorem plainPolynomial_changeSlotBase
    (M : MomentData K ω ψ) (d : ℝ) (hd : 0 < d)
    (W : IdealTest K) (u : NonzeroIdeal K) (N t : ℝ) :
    plainPolynomial (M.changeSlotBase d hd) W u N t =
      plainPolynomial M W u N t := rfl

@[simp] theorem pairedRows_changeSlotBase
    (M : MomentData K ω ψ) (d : ℝ) (hd : 0 < d)
    (a : RealParameters) (Z : ℝ) :
    pairedRows (M.changeSlotBase d hd) a Z = pairedRows M a Z := rfl

theorem primePolynomial_changeSlotBase
    (M : MomentData K ω ψ) (d : ℝ) (hd : 0 < d)
    (u : NonzeroIdeal K) {Z : ℝ} (hZ : 0 < Z) (t : ℝ)
    (i : Fin M.geometry.slotCount) :
    primePolynomial (M.changeSlotBase d hd) i u (Z ^ d) t =
      primePolynomial M i u Z t := by
  simp only [primePolynomial, MomentData.changeSlotBase, SlotGeometry.changeBase,
    PrimeWindow.changeBase, maskValue, rpow_changeBaseSlot hd hZ]

theorem slotProduct_changeSlotBase
    (M : MomentData K ω ψ) (d : ℝ) (hd : 0 < d)
    (u : NonzeroIdeal K) {Z : ℝ} (hZ : 0 < Z) (t : ℝ) :
    slotProduct (M.changeSlotBase d hd) u (Z ^ d) t = slotProduct M u Z t := by
  unfold slotProduct
  apply Finset.prod_congr rfl
  intro i _hi
  exact primePolynomial_changeSlotBase M d hd u hZ t i

theorem MomentData.changeSlotBase_restrictSlots
    (M : MomentData K ω ψ) (d : ℝ) (hd : 0 < d)
    (I : Finset (Fin M.geometry.slotCount)) :
    (M.changeSlotBase d hd).restrictSlots I =
      (M.restrictSlots I).changeSlotBase d hd := rfl

theorem selectedSlotProduct_changeSlotBase
    (M : MomentData K ω ψ) (d : ℝ) (hd : 0 < d)
    (I : Finset (Fin M.geometry.slotCount)) (u : NonzeroIdeal K)
    {Z : ℝ} (hZ : 0 < Z) (t : ℝ) :
    slotProduct ((M.changeSlotBase d hd).restrictSlots I) u (Z ^ d) t =
      ∏ i ∈ I, primePolynomial M i u Z t := by
  rw [slotProduct_restrictSlots (M.changeSlotBase d hd) I u (Z ^ d) t]
  apply Finset.prod_congr rfl
  intro i _hi
  exact primePolynomial_changeSlotBase M d hd u hZ t i

end HeckeGeneral.Analysis.ConditionalMoments

namespace HeckeGeneral.ThetaSkeleton.Physical

open NumberField IsDedekindDomain
open HeckeGeneral.Analysis.ConditionalMoments
open scoped Classical BigOperators

variable (K : Type) [Field K] [NumberField K]

/-- The physical equal slots acquire exactly the existing TIP shell
length, at the new base U = Z^d. -/
theorem momentPrimeGeometry_changeBase_length
    (g : PrimeWindowGeometry) (d : ℝ) (hd : 0 < d) (i : Fin g.slots) :
    (((momentPrimeGeometry K g).changeBase d hd).slots i).length =
      HeckeGeneral.ThetaSkeleton.TIP.slotLength g.slots d := by
  change ((1 / 6 : ℝ) / g.slots) / d = (1 / 6 : ℝ) / (g.slots * d)
  rw [div_div]

theorem momentPrimeGeometry_totalLength_changeBase
    (g : PrimeWindowGeometry) (d : ℝ) (hd : 0 < d) :
    ((momentPrimeGeometry K g).changeBase d hd).totalLength = (1 / 6 : ℝ) / d := by
  rw [SlotGeometry.totalLength_changeBase, momentPrimeGeometry_totalLength]

theorem momentPrimeGeometry_selectedLength_changeBase
    (g : PrimeWindowGeometry) (d : ℝ) (hd : 0 < d)
    (I : Finset (Fin g.slots)) :
    (((momentPrimeGeometry K g).changeBase d hd).restrictSlots I).totalLength =
      ∑ _i ∈ I, HeckeGeneral.ThetaSkeleton.TIP.slotLength g.slots d := by
  calc
    _ = ∑ i ∈ I, (((momentPrimeGeometry K g).changeBase d hd).slots i).length :=
      SlotGeometry.totalLength_restrictSlots ((momentPrimeGeometry K g).changeBase d hd) I
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact momentPrimeGeometry_changeBase_length K g d hd i

theorem momentPrimeGeometry_fitsMesh_changeBase_iff
    (g : PrimeWindowGeometry) (d : ℝ) (hd : 0 < d) (mesh : ℝ) :
    ((momentPrimeGeometry K g).changeBase d hd).fitsMesh mesh ↔
      HeckeGeneral.ThetaSkeleton.TIP.slotLength g.slots d ≤ mesh := by
  constructor
  · intro h
    let i : Fin g.slots := ⟨0, g.slots_pos⟩
    calc
      HeckeGeneral.ThetaSkeleton.TIP.slotLength g.slots d =
          (((momentPrimeGeometry K g).changeBase d hd).slots i).length :=
        (momentPrimeGeometry_changeBase_length K g d hd i).symm
      _ ≤ mesh := h i
  · intro h i
    calc
      (((momentPrimeGeometry K g).changeBase d hd).slots i).length =
          HeckeGeneral.ThetaSkeleton.TIP.slotLength g.slots d :=
        momentPrimeGeometry_changeBase_length K g d hd i
      _ ≤ mesh := h

theorem momentPrimeGeometry_selectedFitsMesh_changeBase_iff
    (g : PrimeWindowGeometry) (d : ℝ) (hd : 0 < d)
    (I : Finset (Fin g.slots)) (mesh : ℝ) :
    (((momentPrimeGeometry K g).changeBase d hd).restrictSlots I).fitsMesh mesh ↔
      ∀ _i ∈ I, HeckeGeneral.ThetaSkeleton.TIP.slotLength g.slots d ≤ mesh := by
  refine (SlotGeometry.fitsMesh_restrictSlots_iff
    ((momentPrimeGeometry K g).changeBase d hd) I mesh).trans ?_
  constructor
  · intro h i hi
    calc
      HeckeGeneral.ThetaSkeleton.TIP.slotLength g.slots d =
          (((momentPrimeGeometry K g).changeBase d hd).slots i).length :=
        (momentPrimeGeometry_changeBase_length K g d hd i).symm
      _ ≤ mesh := h i hi
  · intro h i hi
    calc
      (((momentPrimeGeometry K g).changeBase d hd).slots i).length =
          HeckeGeneral.ThetaSkeleton.TIP.slotLength g.slots d :=
        momentPrimeGeometry_changeBase_length K g d hd i
      _ ≤ mesh := h i hi

end HeckeGeneral.ThetaSkeleton.Physical
