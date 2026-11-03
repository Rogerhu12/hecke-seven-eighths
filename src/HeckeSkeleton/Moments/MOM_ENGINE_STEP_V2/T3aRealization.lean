import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.T3aElementary

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-! # Original row classes fix the actual extraction radical -/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep
open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

namespace RawLeafPacket

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable (packet : RawLeafPacket call p)

theorem exceptional_second_realizes (hpacket : packet.Realizes) :
    packet.second.Realizes := by
  rcases hpacket with ⟨trace, geometry, raw, j, htrace, _, _, rfl⟩
  exact htrace.second.stage (raw.index j).val.1.1

theorem exceptional_row_label (h : packet.R.live) :
    packet.chart.rowLabel h.val = SourceClassKey.rowLabel packet.key := by
  exact (Finset.mem_filter.mp (Finset.mem_filter.mp h.property).1).2

theorem exceptional_pattern_eq (hpacket : packet.Realizes) (h k : packet.R.live) :
    actualNonunitPattern (Arithmetic.context c) packet.R.primes
        packet.R.leftMultiplicity packet.R.rightMultiplicity (packet.R.frequency h.val) =
      actualNonunitPattern (Arithmetic.context c) packet.R.primes
        packet.R.leftMultiplicity packet.R.rightMultiplicity (packet.R.frequency k.val) := by
  exact (packet.exceptional_second_realizes hpacket).patternStable
    packet.key.1 packet.key.2.1 h.val k.val
    ((packet.exceptional_row_label h).trans (packet.exceptional_row_label k).symm)

theorem exceptional_nonunit_classification (hpacket : packet.Realizes)
    (h k : packet.R.live) (i : Fin packet.block.primeCount) :
    nonunitFrequencySaving (Arithmetic.context c) (packet.R.primes i)
        (packet.R.leftMultiplicity i) (packet.R.rightMultiplicity i) (packet.R.frequency h.val) ↔
      nonunitFrequencySaving (Arithmetic.context c) (packet.R.primes i)
        (packet.R.leftMultiplicity i) (packet.R.rightMultiplicity i) (packet.R.frequency k.val) := by
  have he := congrFun (packet.exceptional_pattern_eq hpacket h k) i
  constructor
  · intro hh
    by_contra hk
    have hf : true = false := by
      simpa only [actualNonunitPattern, hh, hk, decide_true, decide_false] using he
    cases hf
  · intro hk
    by_contra hh
    have hf : false = true := by
      simpa only [actualNonunitPattern, hh, hk, decide_true, decide_false] using he
    cases hf

theorem exceptional_nonunit_radical_eq (hpacket : packet.Realizes)
    (h k : packet.R.live) :
    nonunitFrequencyRadical (Arithmetic.context c) packet.R.primes
        packet.R.leftMultiplicity packet.R.rightMultiplicity (packet.R.frequency h.val) =
      nonunitFrequencyRadical (Arithmetic.context c) packet.R.primes
        packet.R.leftMultiplicity packet.R.rightMultiplicity (packet.R.frequency k.val) :=
  (packet.R.frequencyRadicals_eq_of_nonunitClassification (Arithmetic.context c) h k
    (packet.exceptional_nonunit_classification hpacket h k)).2

/-- Extraction inside an actual row class creates no new ideal fibres.
The same fixed original unit-subgroup index bounds every resulting fibre. -/
theorem exceptional_extracted_fibres (hpacket : packet.Realizes)
    (I : HeckeGeneral.Analysis.NonzeroIdeal K) :
    (packet.exceptionalRows.filter (fun h =>
      (packet.R.extractedRow (Arithmetic.context c) h).momentIdeal = I)).card ≤
      (Arithmetic.unitSubgroup c).index := by
  let T := packet.exceptionalRows.filter (fun h =>
    (packet.R.extractedRow (Arithmetic.context c) h).momentIdeal = I)
  by_cases hT : T.Nonempty
  · obtain ⟨h₀, hh₀⟩ := hT
    let J : Ideal (𝓞 K) :=
      gcd (primePowerProduct packet.R.primes packet.R.leftMultiplicity).val
          (primePowerProduct packet.R.primes packet.R.rightMultiplicity).val *
        (nonunitFrequencyRadical (Arithmetic.context c) packet.R.primes
          packet.R.leftMultiplicity packet.R.rightMultiplicity
            (packet.R.frequency h₀.val)).val * I.val
    have hsub : T.image Subtype.val ⊆
        packet.R.rows.filter (fun h => (packet.R.originalIdeal h).val = J) := by
      intro h hh
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hh
      refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp x.property).1, ?_⟩
      have hi : (packet.R.extractedRow (Arithmetic.context c) x).ideal.val = I.val :=
        congrArg (fun I : HeckeGeneral.Analysis.NonzeroIdeal K => I.val)
          (Finset.mem_filter.mp hx).2
      rw [packet.R.extractedRow_ideal_factor (Arithmetic.context c) x,
        packet.exceptional_nonunit_radical_eq hpacket x h₀, hi]
    have hcard := packet.chart.actualRows_original_fibers
      packet.second.stage.mask packet.second.stage.cutoff
      packet.second.stage.cutoff_one (SourceClassKey.rowLabel packet.key) J
    calc
      _ = (T.image Subtype.val).card :=
        (Finset.card_image_of_injective T Subtype.val_injective).symm
      _ ≤ (packet.R.rows.filter (fun h => (packet.R.originalIdeal h).val = J)).card :=
        Finset.card_le_card hsub
      _ ≤ (Arithmetic.unitSubgroup c).index := hcard
  · change T.card ≤ _
    rw [Finset.not_nonempty_iff_eq_empty.mp hT, Finset.card_empty]
    exact Nat.zero_le _

end RawLeafPacket

end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.exceptional_extracted_fibres
