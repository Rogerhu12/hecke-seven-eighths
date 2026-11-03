import HeckeSkeleton.Moments.MOM_INV_STEP.ActualSourceReindexing
import HeckeSkeleton.Moments.MOM_INV_STEP.FixedTripleEnergy

/-!
# Reconstruction packets constructed from actual source indices

The tuple range is the image of the actual squarefree source and its two
divisor and original prime choices. The retained scalar includes the
original label zeros. Its live support therefore has squarefree labels;
the arithmetic validity, nonzero outer ideals, and child membership are
conclusions of the construction, not input hypotheses.

The coefficient bound here is only a pointwise bound on the finite outer
scalar. It is not an energy estimate. The final signed identity is on
the tuple range. The full original source also contains four residual
columns, and its exact grouping is `ActualSourceReindexing.signed_source_grouped`.
No equality between that four-column source and this packet is asserted.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.ActualReconstructionPacket

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic
open ActualSecondTuple ActualSourceReindexing
open HeckeSkeleton.Moments.MOMInvStep.FixedTripleFibers
open HeckeSkeleton.Moments.MOMInvStep.FixedTripleEnergy
open scoped Classical BigOperators NumberField nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K] {Sector : Type*}
variable {Jo Jn : ℕ}
variable (oldLists : Fin Jo → Finset (HeightOneSpectrum (𝓞 K)))
variable (newLists : Fin Jn → Finset (HeightOneSpectrum (𝓞 K)))

def tupleRange (T : Finset (ExpandedSource oldLists newLists (Sector := Sector))) :
    Finset (SecondTuple K Sector Jo Jn) := T.image fun x => x.2.tuple

theorem tupleRange_eq_tupleSource
    (T : Finset (ExpandedSource oldLists newLists (Sector := Sector))) :
    tupleRange oldLists newLists T = ActualSourceReindexing.tupleSource oldLists newLists T := by
  unfold tupleRange ActualSourceReindexing.tupleSource ActualSourceReindexing.keySource
  rw [Finset.image_image]
  rfl

def liveTuples (T : Finset (ExpandedSource oldLists newLists (Sector := Sector)))
    (scalar : SecondTuple K Sector Jo Jn → ℂ) : Finset (SecondTuple K Sector Jo Jn) :=
  originalSource (tupleRange oldLists newLists T) oldLists newLists
    (fun t => scalar t * labelZero t ≠ 0)

theorem mem_liveTuples
    (T : Finset (ExpandedSource oldLists newLists (Sector := Sector)))
    (scalar : SecondTuple K Sector Jo Jn → ℂ) (t : SecondTuple K Sector Jo Jn) :
    t ∈ liveTuples oldLists newLists T scalar ↔
      ∃ x ∈ T, x.2.tuple = t ∧ scalar t * labelZero t ≠ 0 := by
  simp only [liveTuples, originalSource, Finset.mem_filter]
  constructor
  · rintro ⟨ht, hslots⟩
    obtain ⟨x, hx, he⟩ := Finset.mem_image.mp ht
    exact ⟨x, hx, he, hslots.2.2⟩
  · rintro ⟨x, hx, rfl, hlive⟩
    exact ⟨Finset.mem_image.mpr ⟨x, hx, rfl⟩,
      x.2.original_slot_lists.1, x.2.original_slot_lists.2, hlive⟩

theorem liveTuples_eq_filter
    (T : Finset (ExpandedSource oldLists newLists (Sector := Sector)))
    (scalar : SecondTuple K Sector Jo Jn → ℂ) :
    liveTuples oldLists newLists T scalar =
      (tupleRange oldLists newLists T).filter (fun t => scalar t * labelZero t ≠ 0) := by
  ext t
  rw [mem_liveTuples, Finset.mem_filter]
  constructor
  · rintro ⟨x, hx, he, hlive⟩
    exact ⟨Finset.mem_image.mpr ⟨x, hx, he⟩, hlive⟩
  · rintro ⟨ht, hlive⟩
    obtain ⟨x, hx, he⟩ := Finset.mem_image.mp ht
    exact ⟨x, hx, he, hlive⟩

variable (sectorTransport : Ideal (𝓞 K) → Ideal (𝓞 K) → (Sector ≃ Sector))

theorem secondChild_tuple {B : Source K Sector} (a : Choices B oldLists newLists) :
    secondChild sectorTransport a.tuple = (a.outer, a.newLabel, a.newRow sectorTransport) := rfl

theorem live_valid
    (T : Finset (ExpandedSource oldLists newLists (Sector := Sector)))
    (scalar : SecondTuple K Sector Jo Jn → ℂ)
    (t : SecondTuple K Sector Jo Jn) (ht : t ∈ liveTuples oldLists newLists T scalar) :
    Valid sectorTransport t (secondChild sectorTransport t).1
      (secondChild sectorTransport t).2.1 (secondChild sectorTransport t).2.2 := by
  obtain ⟨x, hx, rfl, hlive⟩ := (mem_liveTuples oldLists newLists T scalar t).mp ht
  exact x.2.valid sectorTransport

theorem live_label_squarefree
    (T : Finset (ExpandedSource oldLists newLists (Sector := Sector)))
    (scalar : SecondTuple K Sector Jo Jn → ℂ)
    (t : SecondTuple K Sector Jo Jn) (ht : t ∈ liveTuples oldLists newLists T scalar) :
    Squarefree (secondChild sectorTransport t).2.1 := by
  obtain ⟨x, hx, rfl, hlive⟩ := (mem_liveTuples oldLists newLists T scalar t).mp ht
  exact x.2.newLabel_squarefree_of_live sectorTransport (scalar x.2.tuple) hlive

theorem live_label_nonzero
    (T : Finset (ExpandedSource oldLists newLists (Sector := Sector)))
    (scalar : SecondTuple K Sector Jo Jn → ℂ)
    (t : SecondTuple K Sector Jo Jn) (ht : t ∈ liveTuples oldLists newLists T scalar) :
    (secondChild sectorTransport t).2.1 ≠ 0 := by
  obtain ⟨x, hx, rfl, hlive⟩ := (mem_liveTuples oldLists newLists T scalar t).mp ht
  exact x.2.newLabel_ne_zero

theorem live_outer_nonzero
    (T : Finset (ExpandedSource oldLists newLists (Sector := Sector)))
    (scalar : SecondTuple K Sector Jo Jn → ℂ)
    (t : SecondTuple K Sector Jo Jn) (ht : t ∈ liveTuples oldLists newLists T scalar) :
    t.outer.q0 ≠ 0 ∧ t.outer.quotient ≠ 0 ∧ t.outer.residual ≠ 0 := by
  obtain ⟨x, hx, rfl, hlive⟩ := (mem_liveTuples oldLists newLists T scalar t).mp ht
  exact x.2.outer_nonzero

def childLabels
    (T : Finset (ExpandedSource oldLists newLists (Sector := Sector)))
    (scalar : SecondTuple K Sector Jo Jn → ℂ) : Finset (Ideal (𝓞 K)) :=
  (liveTuples oldLists newLists T scalar).image fun t => (secondChild sectorTransport t).2.1

def childRows
    (T : Finset (ExpandedSource oldLists newLists (Sector := Sector)))
    (scalar : SecondTuple K Sector Jo Jn → ℂ) : Finset (Ideal (𝓞 K) × Sector) :=
  (liveTuples oldLists newLists T scalar).image fun t => (secondChild sectorTransport t).2.2

/-- The actual arithmetic source supplies every structural field of a
reconstruction packet. Only the original finite coefficient bound and
the two declared slot caps are inputs. -/
def packet
    (T : Finset (ExpandedSource oldLists newLists (Sector := Sector)))
    (scalar : SecondTuple K Sector Jo Jn → ℂ)
    (hscalar : ∀ x ∈ T, ‖scalar x.2.tuple‖ ≤ 1)
    (slotCap : ℕ) (ho : Jo ≤ 2 * slotCap) (hn : Jn ≤ 2 * slotCap) :
    ReconstructionPacket (K := K) (Sector := Sector) sectorTransport slotCap Jo Jn where
  source := tupleRange oldLists newLists T
  oldLists := oldLists
  newLists := newLists
  keep := fun t => scalar t * labelZero t ≠ 0
  labels := childLabels oldLists newLists sectorTransport T scalar
  rows := childRows oldLists newLists sectorTransport T scalar
  scalar := fun t => scalar t * labelZero t
  valid := live_valid oldLists newLists sectorTransport T scalar
  label_squarefree := by
    intro f hf
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hf
    exact live_label_squarefree oldLists newLists sectorTransport T scalar t ht
  label_nonzero := by
    intro f hf
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hf
    exact live_label_nonzero oldLists newLists sectorTransport T scalar t ht
  outer_nonzero := by
    intro γ hγ
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hγ
    exact live_outer_nonzero oldLists newLists T scalar t ht
  child_mem := by
    intro t ht
    exact ⟨Finset.mem_image.mpr ⟨t, ht, rfl⟩, Finset.mem_image.mpr ⟨t, ht, rfl⟩⟩
  old_cap := ho
  new_cap := hn
  scalar_norm := by
    intro t ht
    obtain ⟨x, hx, rfl, hlive⟩ := (mem_liveTuples oldLists newLists T scalar t).mp ht
    calc
      _ = ‖scalar x.2.tuple‖ * ‖labelZero x.2.tuple‖ := norm_mul _ _
      _ ≤ 1 * 1 := mul_le_mul (hscalar x hx) (norm_labelZero_le_one _)
        (norm_nonneg _) (by norm_num)
      _ = 1 := by norm_num

/-- Pruning the exact zero coefficients preserves the finite signed
tuple sum before any norm or positive inequality is taken. -/
theorem signed_sum_eq_live
    (T : Finset (ExpandedSource oldLists newLists (Sector := Sector)))
    (scalar H : SecondTuple K Sector Jo Jn → ℂ) :
    (∑ t ∈ tupleRange oldLists newLists T, scalar t * labelZero t * H t) =
      ∑ t ∈ liveTuples oldLists newLists T scalar, scalar t * labelZero t * H t := by
  rw [liveTuples_eq_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro t ht
  by_cases hz : scalar t * labelZero t = 0 <;> simp [hz]

/-- The packet retains the original tuple scalar and all its zeros.
This equality is deliberately stated on the tuple range; the full
four-column source still uses its separate exact reindexing theorem. -/
theorem packet_signedValue_eq_tuple_sum
    (T : Finset (ExpandedSource oldLists newLists (Sector := Sector)))
    (scalar : SecondTuple K Sector Jo Jn → ℂ)
    (hscalar : ∀ x ∈ T, ‖scalar x.2.tuple‖ ≤ 1)
    (slotCap : ℕ) (ho : Jo ≤ 2 * slotCap) (hn : Jn ≤ 2 * slotCap)
    (F G : SecondChild K Sector → ℂ) :
    (packet oldLists newLists sectorTransport T scalar hscalar slotCap ho hn).signedValue F G =
      ∑ t ∈ tupleRange oldLists newLists T,
        scalar t * labelZero t * F (secondChild sectorTransport t) *
          star (G (secondChild sectorTransport t)) := by
  change (∑ t ∈ liveTuples oldLists newLists T scalar,
      scalar t * labelZero t * F (secondChild sectorTransport t) *
        star (G (secondChild sectorTransport t))) = _
  simpa only [mul_assoc] using
    (signed_sum_eq_live oldLists newLists T scalar (fun t =>
      F (secondChild sectorTransport t) * star (G (secondChild sectorTransport t)))).symm

end HeckeSkeleton.Moments.MOM_INV_STEP.ActualReconstructionPacket

end
