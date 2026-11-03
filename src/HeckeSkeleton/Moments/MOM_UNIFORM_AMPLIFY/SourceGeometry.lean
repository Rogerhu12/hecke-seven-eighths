import HeckeGeneral.Analysis.TIPSources
import Mathlib.Tactic.NormNum

/-!
# Witness geometry supplied by the actual expansion interface

The existing `BlockSource` and `WitnessCover` predicates supply the lower
physical scale, the common bounded range of inverse lengths, and inclusion
of every subdivision in its original amplitude rows.  The theorems here
extract those facts from the actual source definitions.  An arbitrary
`TargetData` supplies its stated `2 * U` row envelope; no concrete admitted
expansion or moment-model choice is used.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.Moments.UniformAmplify

open NumberField IsDedekindDomain
open HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Physical HeckeGeneral.ThetaSkeleton.TIP
open scoped Classical BigOperators

variable {Row : Type} {g : PrimeWindowGeometry}
variable {b : ModerateBlock Row g.slots} {B lam k Z : ℝ}

/-- Every retained subdivision inherits the original row set and the
uniform inverse-length range from the source's `WitnessCover`. -/
theorem blockSource_witness_lengths
    (hb : BlockSource g b B lam k Z) (hbin : 51 / 100 < b.bin)
    (ℓ : b.Label) (t : ℝ) (ht : 1 ≤ t) (ht' : t ≤ 3 / 2)
    (j : Fin ((b.amplitudeSet ℓ).subdivisionCount t)) :
    0 ≤ ((b.amplitudeSet ℓ).subdivision t j).inverseLength ∧
      ((b.amplitudeSet ℓ).subdivision t j).inverseLength ≤ 3 / 2 + lam ∧
      0 ≤ ((b.amplitudeSet ℓ).subdivision t j).plainLength ∧
      ((b.amplitudeSet ℓ).subdivision t j).rows ⊆ (b.amplitudeSet ℓ).rows := by
  have hw := ((hb.2.2.2.2 ℓ).2.2 hbin t ht ht').2.2 j
  exact ⟨hw.2.1, hw.2.2.2.1.trans (_root_.add_le_add ht' (le_rfl : lam ≤ lam)),
    hw.2.2.1, hw.1⟩

/-- A selected subset of the actual uniform slot system has nonnegative
total length because the source shell is positive. -/
theorem blockSource_selected_length_nonneg
    (hb : BlockSource g b B lam k Z) (I : Finset (Fin g.slots)) :
    0 ≤ ∑ _j ∈ I, HeckeGeneral.ThetaSkeleton.TIP.slotLength g.slots b.shell := by
  have hshell : 0 ≤ b.shell :=
    (by norm_num : (0 : ℝ) ≤ 1 / 100).trans hb.1
  apply Finset.sum_nonneg
  intro j hj
  exact div_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 6)
    (mul_nonneg (Nat.cast_nonneg g.slots) hshell)

/-- The source chooses `d = 1/100` and `R = 3/2 + lam` uniformly before a
later label, subdivision, or inverse witness is selected. -/
theorem blockSource_witness_geometry
    (hb : BlockSource g b B lam k Z) (hZ : 1 ≤ Z)
    (hbin : 51 / 100 < b.bin)
    (ℓ : b.Label) (t : ℝ) (ht : 1 ≤ t) (ht' : t ≤ 3 / 2)
    (j : Fin ((b.amplitudeSet ℓ).subdivisionCount t)) :
    1 / 100 ≤ b.shell ∧
      Z ^ (1 / 100 : ℝ) ≤ Z ^ b.shell ∧
      1 ≤ Z ^ b.shell ∧
      0 ≤ ((b.amplitudeSet ℓ).subdivision t j).inverseLength ∧
      ((b.amplitudeSet ℓ).subdivision t j).inverseLength ≤ 3 / 2 + lam ∧
      0 ≤ ((b.amplitudeSet ℓ).subdivision t j).plainLength ∧
      ((b.amplitudeSet ℓ).subdivision t j).rows ⊆ (b.amplitudeSet ℓ).rows := by
  have hshell : 0 ≤ b.shell :=
    (by norm_num : (0 : ℝ) ≤ 1 / 100).trans hb.1
  exact ⟨hb.1, Real.rpow_le_rpow_of_exponent_le hZ hb.1,
    Real.one_le_rpow hZ hshell, blockSource_witness_lengths hb hbin ℓ t ht ht' j⟩

/-- The genuine inverse witness scale is at least one on the source range. -/
theorem blockSource_witness_inverse_scale_one_le
    (hb : BlockSource g b B lam k Z) (hZ : 1 ≤ Z)
    (hbin : 51 / 100 < b.bin)
    (ℓ : b.Label) (t : ℝ) (ht : 1 ≤ t) (ht' : t ≤ 3 / 2)
    (j : Fin ((b.amplitudeSet ℓ).subdivisionCount t)) :
    1 ≤ (Z ^ b.shell) ^ ((b.amplitudeSet ℓ).subdivision t j).inverseLength := by
  obtain ⟨_, _, hbase, hr, _⟩ := blockSource_witness_geometry hb hZ hbin ℓ t ht ht' j
  exact Real.one_le_rpow hbase hr

/-- The actual target-data envelope passes to each witness subdivision.
Its original factor `2` is retained. -/
theorem targetData_witness_rows_in_norm_envelope
    {K : Type} [Field K] [NumberField K] {g : PrimeWindowGeometry}
    (D : TargetData K g) {B lam k Z T : ℝ}
    (hZ : 1 ≤ Z) (hT : 1 ≤ T)
    (b : Fin (D.expansion Z T).blockCount)
    (hb : BlockSource g ((D.expansion Z T).block b) B lam k Z)
    (hbin : 51 / 100 < ((D.expansion Z T).block b).bin)
    (ℓ : ((D.expansion Z T).block b).Label)
    (t : ℝ) (ht : 1 ≤ t) (ht' : t ≤ 3 / 2)
    (j : Fin ((((D.expansion Z T).block b).amplitudeSet ℓ).subdivisionCount t)) :
    ((((D.expansion Z T).block b).amplitudeSet ℓ).subdivision t j).rows ⊆
      frequencyRows K (D.S : Set (HeightOneSpectrum (𝓞 K)))
        (2 * Z ^ ((D.expansion Z T).block b).shell) := by
  exact (blockSource_witness_lengths hb hbin ℓ t ht ht' j).2.2.2.trans
    (D.rows_in_norm_envelope Z T hZ hT b ℓ)

end HeckeSkeleton.Moments.UniformAmplify
