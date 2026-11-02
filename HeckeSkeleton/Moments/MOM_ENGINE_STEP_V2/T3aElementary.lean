import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.ExceptionalRecoveryContracts
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ExceptionalSourceBinding
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalOrbitFibre

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Exact exceptional support and the actual sixth-power decomposition

These elementary parts of T3a do not assume an exceptional volume bound.
The support identity discards a row only when its actual row weight or
one of its original whole finite columns vanishes. The ideal identities
use the already selected extracted row, without choosing a new ideal.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep
open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments UniqueFactorizationMonoid

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

namespace T3a

section Finite

variable {H I J V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Delete precisely the rows with zero weight or an identically zero
whole column. Cancellation inside a nonzero whole column is preserved. -/
theorem pairMagnitude_eq_supported
    (rows : Finset H) (left : Finset I) (right : Finset J)
    (q : H → ℂ) (a : H → I → ℂ) (b : H → J → ℂ)
    (x : H → I → V) (y : H → J → V) (ξ : V) :
    jointColumnPairMagnitude rows left right q a b x y ξ =
      jointColumnPairMagnitude
        (rows.filter (fun h => q h ≠ 0 ∧
          (∃ i ∈ left, a h i ≠ 0) ∧ (∃ j ∈ right, b h j ≠ 0)))
        left right q a b x y ξ := by
  unfold jointColumnPairMagnitude
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro h hh hnot
  have hnot' : ¬ (q h ≠ 0 ∧
      (∃ i ∈ left, a h i ≠ 0) ∧ (∃ j ∈ right, b h j ≠ 0)) := by
    intro hp
    exact hnot (Finset.mem_filter.mpr ⟨hh, hp⟩)
  by_cases hq : q h = 0
  · simp only [hq, norm_zero, zero_mul]
  by_cases ha : ∃ i ∈ left, a h i ≠ 0
  · have hb : ∀ j ∈ right, b h j = 0 := by
      intro j hj
      by_contra hb
      exact hnot' ⟨hq, ha, j, hj, hb⟩
    have hz : jointFourierColumn right (b h) (y h) ξ = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [hb j hj, zero_mul]
    simp only [hz, norm_zero, mul_zero]
  · have hb : ∀ i ∈ left, a h i = 0 := by
      intro i hi
      by_contra hb
      exact ha ⟨i, hi, hb⟩
    have hz : jointFourierColumn left (a h) (x h) ξ = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [hb i hi, zero_mul]
    simp only [hz, norm_zero, mul_zero, zero_mul]

/-- Passing to the subtype of a retained row set is an exact finite
reindexing, before either Fourier integration. -/
theorem pairMagnitude_subtype_filter
    (rows : Finset H) (P : H → Prop) (left : Finset I) (right : Finset J)
    (q : H → ℂ) (a : H → I → ℂ) (b : H → J → ℂ)
    (x : H → I → V) (y : H → J → V) (ξ : V) :
    jointColumnPairMagnitude (rows.filter P) left right q a b x y ξ =
      jointColumnPairMagnitude
        ((Finset.univ : Finset rows).filter (fun h => P h.val)) left right
        (fun h => q h.val) (fun h => a h.val) (fun h => b h.val)
        (fun h => x h.val) (fun h => y h.val) ξ := by
  simp only [jointColumnPairMagnitude, Finset.sum_filter]
  exact (Finset.sum_coe_sort rows (fun h =>
    if P h then ‖q h‖ * ‖jointFourierColumn left (a h) (x h) ξ‖ *
      ‖jointFourierColumn right (b h) (y h) ξ‖ else 0)).symm

end Finite

end T3a

namespace RawLeafPacket

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable (packet : RawLeafPacket call p)

theorem exceptional_leaf_rows : packet.leaf.rows = packet.R.rows := rfl

theorem exceptional_leaf_rowWeight (h : Arithmetic.Orbit c) :
    packet.leaf.rowWeight h = packet.R.weight h * packet.R.correlation h := rfl

/-- The ideal decomposition is the canonical sixth-free decomposition
of the original selected extracted ideal. -/
theorem exceptional_factorization (h : packet.R.live) :
    (packet.R.extractedRow (Arithmetic.context c) h).ideal.val =
      (packet.sixthBase h).val *
        (sixthPowerAmplifierPart
          (packet.R.extractedRow (Arithmetic.context c) h).momentIdeal).val ^ 6 := by
  exact congrArg (fun I : HeckeGeneral.Analysis.NonzeroIdeal K => I.val)
    (sixthPowerFreePart_mul_amplifier_sixth
      (packet.R.extractedRow (Arithmetic.context c) h).momentIdeal).symm

theorem exceptional_base_sixth_free (I : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hI : I ∈ packet.exceptionalBases) : SixthPowerFreeIdeal I := by
  obtain ⟨h, _, rfl⟩ := Finset.mem_image.mp hI
  exact sixthPowerFreePart_isSixthPowerFree
    (packet.R.extractedRow (Arithmetic.context c) h).momentIdeal

/-- Arithmetic valuations from the exceptional character classification
give the fourth-power divisor of the same canonical sixth-free base. -/
theorem exceptional_fourth_power (h : packet.R.live)
    (hclass : ∀ i ∈ multiplicityOneNonunitPrimes (Arithmetic.context c) packet.R.primes
      packet.R.leftMultiplicity packet.R.rightMultiplicity (packet.R.frequency h.val),
      6 ∣ (normalizedFactors (packet.R.originalIdeal h.val).val).count
        (packet.R.primes i).val.asIdeal) :
    (packet.multiplicityOneRadical h).val ^ 4 ∣ (packet.sixthBase h).val ∧
      (Arithmetic.data c).exteriorNorm (packet.multiplicityOneRadical h) ^ 4 ≤
        (Ideal.absNorm (packet.sixthBase h).val : ℝ) := by
  exact (packet.R.exceptionalRow (Arithmetic.context c) h).base_fourth_power
    packet.R.primes_injective hclass (packet.sixthBase h).val
    (sixthPowerAmplifierPart
      (packet.R.extractedRow (Arithmetic.context c) h).momentIdeal).val
    (packet.exceptional_factorization h)

end RawLeafPacket

end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.T3a.pairMagnitude_eq_supported
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.exceptional_factorization
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.exceptional_fourth_power
