import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3bSavings
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3bMaskBounds
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.FirstCommonMass

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Counting the actual exceptional rows over their original sixth bases

The partition is only by the actual sixth-power-free part supplied by
T3a.  All original unit sectors and the original extracted-ideal fibres
are counted.  The fourth-power lower bound uses the same multiplicity-one
nonunit radical on the whole selected original row class.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep
open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments HeckePort.CenteredMomentCounting

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

namespace T3b

def rowCountConstant (c : TargetContext K) : ℝ :=
  ((Expansion.Project.canonicalDetectorTheta K (targetCharacter K c)).card *
      Nat.card (SixthUnitClasses K (places K c)) *
      (Arithmetic.unitSubgroup c).index : ℕ) * idealCountConstant K

theorem rowCountConstant_nonneg (c : TargetContext K) :
    0 ≤ rowCountConstant c :=
  mul_nonneg (Nat.cast_nonneg _) (zero_le_one.trans (one_le_idealCountConstant K))

end T3b

namespace RawLeafPacket

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable (packet : RawLeafPacket call p)

/-- Count one actual sixth-base fibre, with the original ideal fibre
bound from T3a and the paid S5 window. -/
theorem t3b_exceptional_base_count (hpacket : packet.Realizes)
    (recovery : packet.ExceptionalRecovery) (side : Bool) (h₀ : packet.R.live)
    (B : HeckeGeneral.Analysis.NonzeroIdeal K) :
    ((packet.exceptionalRows.filter (fun h => packet.sixthBase h = B)).card : ℝ) ≤
      ((Arithmetic.unitSubgroup c).index : ℝ) * idealCountConstant K *
        call.base ^ (((packet.nominal side).skeleton.nominalRow + 12 * p.loss -
          2 * packet.t3bMultiplicityOneLength h₀) / 6) := by
  let rows := packet.exceptionalRows.filter (fun h => packet.sixthBase h = B)
  apply actual_exceptional_sector_count (Arithmetic.context c) packet.R.primes
    packet.R.primes_injective packet.R.leftMultiplicity packet.R.rightMultiplicity
    rows (fun h => packet.R.originalIdeal h.val) (fun h => packet.R.frequency h.val)
    (packet.R.exceptionalRow (Arithmetic.context c)) B.val
  · intro h hh
    exact recovery.valuations h (Finset.mem_filter.mp hh).1
  · intro h hh
    refine ⟨(sixthPowerAmplifierPart
      (packet.R.extractedRow (Arithmetic.context c) h).momentIdeal).val, ?_⟩
    simpa only [ActualSecondCorrelationRows.exceptionalRow_ideal,
      (Finset.mem_filter.mp hh).2] using
      recovery.factorization h (Finset.mem_filter.mp hh).1
  · exact call.domain.scale.le
  · exact packet.t3bMultiplicityOneLength_nonneg h₀
  · exact Nat.cast_nonneg _
  · intro h hh
    change call.base ^ packet.t3bMultiplicityOneLength h₀ ≤
      (Ideal.absNorm (packet.multiplicityOneRadical h).val : ℝ)
    rw [packet.t3b_multiplicityOneRadical_eq hpacket h h₀]
    exact (rpow_idealLogLength call.base call.domain.scale _
      (packet.multiplicityOneRadical h₀).property.1).le
  · intro h hh
    exact packet.t3b_originalRow_norm_le h hpacket side
  · intro I hI
    obtain ⟨h, hh, hI⟩ := Finset.mem_image.mp hI
    have hsub : rows.filter (fun x =>
        (packet.R.exceptionalRow (Arithmetic.context c) x).ideal.val = I) ⊆
      packet.exceptionalRows.filter (fun x =>
        (packet.R.extractedRow (Arithmetic.context c) x).momentIdeal =
          (packet.R.extractedRow (Arithmetic.context c) h).momentIdeal) := by
      intro x hx
      refine Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1, ?_⟩
      apply Subtype.ext
      exact (Finset.mem_filter.mp hx).2.trans hI.symm
    exact_mod_cast (Finset.card_le_card hsub).trans
      (recovery.extracted_fibres
        (packet.R.extractedRow (Arithmetic.context c) h).momentIdeal)

/-- Summing the actual base fibres introduces exactly the fixed theta
and sixth-unit-sector count.  No separate analytic catalogue is counted. -/
theorem t3b_exceptional_rows_count (hpacket : packet.Realizes)
    (recovery : packet.ExceptionalRecovery) (side : Bool) (h₀ : packet.R.live) :
    (packet.exceptionalRows.card : ℝ) ≤ T3b.rowCountConstant c *
      call.base ^ (((packet.nominal side).skeleton.nominalRow + 12 * p.loss -
        2 * packet.t3bMultiplicityOneLength h₀) / 6) := by
  let U := ((Arithmetic.unitSubgroup c).index : ℝ) * idealCountConstant K *
    call.base ^ (((packet.nominal side).skeleton.nominalRow + 12 * p.loss -
      2 * packet.t3bMultiplicityOneLength h₀) / 6)
  have hU : 0 ≤ U := mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (zero_le_one.trans (one_le_idealCountConstant K)))
    (Real.rpow_nonneg call.base_pos.le _)
  have hmap : ∀ h ∈ packet.exceptionalRows,
      packet.sixthBase h ∈ packet.exceptionalBases :=
    fun h hh => Finset.mem_image_of_mem _ hh
  have hpartition := Finset.card_eq_sum_card_fiberwise hmap
  have hbases : (packet.exceptionalBases.card : ℝ) ≤
      (call.node.data.theta.card * Nat.card (SixthUnitClasses K (places K c)) : ℕ) := by
    exact_mod_cast recovery.bases_card
  calc
    _ = ∑ B ∈ packet.exceptionalBases,
        ((packet.exceptionalRows.filter (fun h => packet.sixthBase h = B)).card : ℝ) := by
      exact_mod_cast hpartition
    _ ≤ ∑ _B ∈ packet.exceptionalBases, U :=
      Finset.sum_le_sum (fun B _ =>
        packet.t3b_exceptional_base_count hpacket recovery side h₀ B)
    _ = (packet.exceptionalBases.card : ℝ) * U := by simp
    _ ≤ (call.node.data.theta.card * Nat.card (SixthUnitClasses K (places K c)) : ℕ) * U :=
      mul_le_mul_of_nonneg_right hbases hU
    _ = _ := by
      rw [call.source.source.theta_eq]
      simp only [T3b.rowCountConstant, Nat.cast_mul, U]
      ring

end RawLeafPacket

end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.t3b_exceptional_rows_count
