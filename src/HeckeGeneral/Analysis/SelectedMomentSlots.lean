import HeckeGeneral.Analysis.MomentInputs
import Mathlib.Data.Fintype.EquivFin

/-! Exact reindexing of a selected set of actual moment slots. The row
characters, ideal tests and common zero mask are unchanged. This is finite
algebra only: no admissibility, moment bound or exceptional-row claim. -/

noncomputable section
namespace HeckeGeneral.Analysis.ConditionalMoments

open NumberField IsDedekindDomain HeckeGeneral.Characters
open scoped Classical BigOperators

variable {K : Type} [Field K] [NumberField K]

def selectedSlotIndex {n : ℕ} (I : Finset (Fin n)) (j : Fin I.card) : Fin n :=
  (I.equivFin.symm j).val

theorem selectedSlotIndex_mem {n : ℕ} (I : Finset (Fin n)) (j : Fin I.card) :
    selectedSlotIndex I j ∈ I := (I.equivFin.symm j).property

def SlotGeometry.restrictSlots (g : SlotGeometry K) (I : Finset (Fin g.slotCount)) :
    SlotGeometry K where
  slotCount := I.card
  slots j := g.slots (selectedSlotIndex I j)

def MomentData.restrictSlots {ω ψ : HeckeCharacter K} (d : MomentData K ω ψ)
    (I : Finset (Fin d.geometry.slotCount)) : MomentData K ω ψ :=
  { d with
    geometry := d.geometry.restrictSlots I
    slotCoefficient := fun j => d.slotCoefficient (selectedSlotIndex I j) }

theorem primePolynomial_restrictSlots {ω ψ : HeckeCharacter K}
    (d : MomentData K ω ψ) (I : Finset (Fin d.geometry.slotCount))
    (j : Fin I.card) (u : NonzeroIdeal K) (Z t : ℝ) :
    primePolynomial (d.restrictSlots I) j u Z t =
      primePolynomial d (selectedSlotIndex I j) u Z t := rfl

theorem inversePolynomial_restrictSlots {ω ψ : HeckeCharacter K}
    (d : MomentData K ω ψ) (I : Finset (Fin d.geometry.slotCount))
    (u : NonzeroIdeal K) (D t : ℝ) :
    inversePolynomial (d.restrictSlots I) u D t = inversePolynomial d u D t := rfl

theorem plainPolynomial_restrictSlots {ω ψ : HeckeCharacter K}
    (d : MomentData K ω ψ) (I : Finset (Fin d.geometry.slotCount))
    (W : IdealTest K) (u : NonzeroIdeal K) (N t : ℝ) :
    plainPolynomial (d.restrictSlots I) W u N t = plainPolynomial d W u N t := rfl

theorem selectedSlots_prod {n : ℕ} (I : Finset (Fin n)) (f : Fin n → ℂ) :
    (∏ j : Fin I.card, f (selectedSlotIndex I j)) = ∏ i ∈ I, f i := by
  calc
    _ = ∏ i : I, f i.val :=
      Fintype.prod_equiv I.equivFin.symm _ _ (fun _ => rfl)
    _ = _ := Finset.prod_coe_sort I f

theorem selectedSlots_sum {n : ℕ} (I : Finset (Fin n)) (f : Fin n → ℝ) :
    (∑ j : Fin I.card, f (selectedSlotIndex I j)) = ∑ i ∈ I, f i := by
  calc
    _ = ∑ i : I, f i.val :=
      Fintype.sum_equiv I.equivFin.symm _ _ (fun _ => rfl)
    _ = _ := Finset.sum_coe_sort I f

theorem slotProduct_restrictSlots {ω ψ : HeckeCharacter K}
    (d : MomentData K ω ψ) (I : Finset (Fin d.geometry.slotCount))
    (u : NonzeroIdeal K) (Z t : ℝ) :
    slotProduct (d.restrictSlots I) u Z t = ∏ i ∈ I, primePolynomial d i u Z t :=
  selectedSlots_prod I (fun i => primePolynomial d i u Z t)

theorem SlotGeometry.totalLength_restrictSlots (g : SlotGeometry K)
    (I : Finset (Fin g.slotCount)) :
    (g.restrictSlots I).totalLength = ∑ i ∈ I, (g.slots i).length :=
  selectedSlots_sum I (fun i => (g.slots i).length)

theorem SlotGeometry.fitsMesh_restrictSlots (g : SlotGeometry K)
    (I : Finset (Fin g.slotCount)) {mesh : ℝ}
    (h : ∀ i ∈ I, (g.slots i).length ≤ mesh) :
    (g.restrictSlots I).fitsMesh mesh :=
  fun j => h _ (selectedSlotIndex_mem I j)

theorem inverseEnergy_restrictSlots {ω ψ : HeckeCharacter K}
    (d : MomentData K ω ψ) (I : Finset (Fin d.geometry.slotCount))
    (a : RealParameters) (Z t : ℝ) :
    inverseEnergy (d.restrictSlots I) a Z t =
      ∑ u ∈ d.rows (Z ^ a.m),
        ‖inversePolynomial d u (Z ^ a.r) t * ∏ i ∈ I, primePolynomial d i u Z t‖ ^ 2 := by
  unfold inverseEnergy
  apply Finset.sum_congr rfl
  intro u _hu
  rw [inversePolynomial_restrictSlots, slotProduct_restrictSlots]

/-- This preserves pairedRows verbatim; it does not prove that any physical
witness family obeys the exceptional-character exclusion. -/
theorem pairedEnergy_restrictSlots {ω ψ : HeckeCharacter K}
    (d : MomentData K ω ψ) (I : Finset (Fin d.geometry.slotCount))
    (a : RealParameters) (Z t : ℝ) :
    pairedEnergy (d.restrictSlots I) a Z t =
      ∑ u ∈ pairedRows d a Z,
        ‖plainPolynomial d d.plainTest₁ u (Z ^ a.n₁) t *
          plainPolynomial d d.plainTest₂ u (Z ^ a.n₂) t *
          ∏ i ∈ I, primePolynomial d i u Z t‖ ^ 2 := by
  unfold pairedEnergy
  apply Finset.sum_congr rfl
  intro u _hu
  rw [plainPolynomial_restrictSlots, plainPolynomial_restrictSlots,
    slotProduct_restrictSlots]
  rfl

end HeckeGeneral.Analysis.ConditionalMoments
