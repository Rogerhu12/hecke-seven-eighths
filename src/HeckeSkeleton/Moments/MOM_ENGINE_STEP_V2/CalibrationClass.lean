module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.CanonicalCalibrationData
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.CalibrationOrigin
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.PassivePhaseBridge

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The original second class fixes the child character

The actual row label fixes its nonunit pattern and extracted unit sector.
The ordinary predicate is the original parent-theta exclusion. The first
and pool origin fields identify its complete moving list, and the proved
global pool-character identity transports that exclusion to the paid
recipe without changing theta.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.CalibrationClass

open EngineStep EngineInduction EngineInduction.Source
open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

section SourceMoving

variable {F : FirstPresentation call p} {family : FirstCauchyFamily F}

private def unpaidPoolMoving
    (poolChoice : Option (AmplifierValuation × ExteriorPrime (Arithmetic.data c))) :
    OriginalMovingFactors (Arithmetic.data c) (probeData K c) (momentRowCharacters K c) :=
  match poolChoice with
  | none => OriginalMovingFactors.singleton ⟨1, one_ne_zero⟩ 1
  | some (e, q) => OriginalMovingFactors.singleton
      ⟨generator (Arithmetic.context c) q ^ (2 * e.multiplicity),
        (generator_power_generates (Arithmetic.context c) q (2 * e.multiplicity)).1⟩ 1

private theorem firstMoving_eq (key : FirstCauchyKey F)
    (a : (Arithmetic.data c).R) (ha : a ≠ 0) (he : a = key.firstElement) :
    key.moving = OriginalMovingFactors.singleton
      (P := probeData K c) (R := momentRowCharacters K c) ⟨a, ha⟩ 1 := by
  subst a
  cases hs : key.side <;>
    simp [FirstCauchyKey.moving, FirstCauchyKey.firstElement, hs,
      CanonicalLiteralFirstPhase.leftMoving, CanonicalLiteralFirstPhase.rightMoving]

private theorem expansion_firstElement (expansion : PoolExpansion family)
    (hfamily : family.Realizes) (hexpansion : expansion.Realizes)
    (i : Fin expansion.count) :
    (expansion.source i).first.firstElement =
      (family.index (expansion.firstIndex i)).firstElement := by
  cases expansion with
  | direct => exact hfamily.firstElement i
  | pooled pool count index source =>
    obtain ⟨_, _, horigin⟩ := hexpansion
    change (source i).first.firstElement = (family.index (index i).1).firstElement
    cases hindex : (index i).2 with
    | inl u =>
      have hm : pool.MainOrigin (index i).1 (source i) := by
        simpa only [PoolPresentation.Origin, hindex] using horigin i
      rcases hm with ⟨_, _, _, _, _, _, _, hfirst⟩
      rw [hfirst]
      exact hfamily.firstElement (index i).1
    | inr qe =>
      rcases qe with ⟨q, e⟩
      have he : pool.ErrorOrigin (index i).1 q e (source i) := by
        simpa only [PoolPresentation.Origin, hindex] using horigin i
      rcases he with ⟨_, _, _, _, _, _, _, _, _, _, _, helement, _, _, _, _, _, _⟩
      exact helement.trans (hfamily.firstElement (index i).1)

private theorem expansion_poolMoving (expansion : PoolExpansion family)
    (hfamily : family.Realizes) (hexpansion : expansion.Realizes)
    (i : Fin expansion.count)
    (poolChoice : Option (AmplifierValuation × ExteriorPrime (Arithmetic.data c)))
    (htag : match poolChoice with
      | none => (expansion.source i).first.tag = .direct ∨
          (expansion.source i).first.tag = .main
      | some (e, q) => (expansion.source i).first.tag = .error e q.val) :
    expansion.poolMoving i = unpaidPoolMoving poolChoice := by
  cases expansion with
  | direct =>
    have hp : poolChoice = none := by
      cases hc : poolChoice with
      | none => rfl
      | some eq =>
        rcases eq with ⟨e, q⟩
        have ht : (family.source i).first.tag = .error e q.val := by
          simpa only [hc, PoolExpansion.source] using htag
        rw [hfamily.tag i] at ht
        cases ht
    simp only [PoolExpansion.poolMoving, hp, unpaidPoolMoving]
  | pooled pool count index source =>
    obtain ⟨_, _, horigin⟩ := hexpansion
    cases hindex : (index i).2 with
    | inl u =>
      have hm : pool.MainOrigin (index i).1 (source i) := by
        simpa only [PoolPresentation.Origin, hindex] using horigin i
      rcases hm with ⟨_, _, _, _, _, _, _, hfirst⟩
      have hp : poolChoice = none := by
        cases hc : poolChoice with
        | none => rfl
        | some eq =>
          rcases eq with ⟨e, q⟩
          have ht : (source i).first.tag = .error e q.val := by
            simpa only [hc, PoolExpansion.source] using htag
          rw [hfirst] at ht
          cases ht
      simp only [PoolExpansion.poolMoving, hindex, hp, unpaidPoolMoving]
    | inr qe =>
      rcases qe with ⟨q, e⟩
      have he : pool.ErrorOrigin (index i).1 q e (source i) := by
        simpa only [PoolPresentation.Origin, hindex] using horigin i
      rcases he with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ht, _, _⟩
      cases hc : poolChoice with
      | none =>
        have hh : (source i).first.tag = .direct ∨ (source i).first.tag = .main := by
          simpa only [hc, PoolExpansion.source] using htag
        rw [ht] at hh
        rcases hh with hh | hh <;> cases hh
      | some eq =>
        rcases eq with ⟨e', q'⟩
        have hh : (source i).first.tag = .error e' q'.val := by
          simpa only [hc, PoolExpansion.source] using htag
        have hsame := ht.symm.trans hh
        injection hsame with heq hq
        have hq' : q.val = q' := Subtype.ext hq
        simp only [PoolExpansion.poolMoving, hindex, unpaidPoolMoving, hc, ← heq, ← hq']

private theorem expansion_moving (expansion : PoolExpansion family)
    (hfamily : family.Realizes) (hexpansion : expansion.Realizes)
    (i : Fin expansion.count) (ha : (expansion.source i).first.firstElement ≠ 0)
    (poolChoice : Option (AmplifierValuation × ExteriorPrime (Arithmetic.data c)))
    (htag : match poolChoice with
      | none => (expansion.source i).first.tag = .direct ∨
          (expansion.source i).first.tag = .main
      | some (e, q) => (expansion.source i).first.tag = .error e q.val) :
    expansion.moving i =
      (((call.localizedSource.source.recipe.moving.append
        (OriginalMovingFactors.singleton ⟨(expansion.source i).first.firstElement, ha⟩ 1)).append
          (unpaidPoolMoving poolChoice)).append
            (CanonicalLiteralFixedPhases.emptyDivisorMoving
              (probeData K c) (momentRowCharacters K c))) := by
  unfold PoolExpansion.moving
  rw [firstMoving_eq (family.index (expansion.firstIndex i)) _ ha
    (expansion_firstElement expansion hfamily hexpansion i),
    expansion_poolMoving expansion hfamily hexpansion i poolChoice htag]

end SourceMoving

variable (packet : RawLeafPacket call p)

private theorem secondRealizes (hpacket : packet.Realizes) : packet.second.Realizes := by
  rcases hpacket with ⟨trace, geometry, raw, j, htrace, _, _, rfl⟩
  exact htrace.second.stage (raw.index j).val.1.1

private theorem row_label (h : packet.R.live) :
    packet.chart.rowLabel h.val = SourceClassKey.rowLabel packet.key :=
  (Finset.mem_filter.mp (Finset.mem_filter.mp h.property).1).2

theorem pattern_stable (hpacket : packet.Realizes) (h k : packet.R.live) :
    actualNonunitPattern (Arithmetic.context c) packet.R.primes
        packet.R.leftMultiplicity packet.R.rightMultiplicity (packet.R.frequency h.val) =
      actualNonunitPattern (Arithmetic.context c) packet.R.primes
        packet.R.leftMultiplicity packet.R.rightMultiplicity (packet.R.frequency k.val) :=
  (secondRealizes packet hpacket).patternStable packet.key.1 packet.key.2.1 h.val k.val
    ((row_label packet h).trans (row_label packet k).symm)

theorem sector_stable (hpacket : packet.Realizes) (h k : packet.R.live) :
    (packet.R.extractedRow (Arithmetic.context c) h).sector (probeData K c) =
      (packet.R.extractedRow (Arithmetic.context c) k).sector (probeData K c) :=
  (secondRealizes packet hpacket).sectorStable packet.key.1 packet.key.2.1
    (SourceClassKey.rowLabel packet.key) h k

theorem pattern_eq (hpacket : packet.Realizes) (h : packet.R.live) :
    actualNonunitPattern (Arithmetic.context c) packet.R.primes
      packet.R.leftMultiplicity packet.R.rightMultiplicity (packet.R.frequency h.val) =
        pattern packet := by
  rw [pattern, dif_pos (show Nonempty packet.R.live from ⟨h⟩)]
  exact pattern_stable packet hpacket h _

theorem sector_eq (hpacket : packet.Realizes) (h : packet.R.live) :
    (packet.R.extractedRow (Arithmetic.context c) h).sector (probeData K c) =
      sector packet := by
  rw [sector, dif_pos (show Nonempty packet.R.live from ⟨h⟩)]
  exact sector_stable packet hpacket h _

theorem factor_eq (hpacket : packet.Realizes) (h : packet.R.live) :
    packet.R.factor (Arithmetic.context c) h.val =
      secondSixthRootGenerator (Arithmetic.context c) packet.R.primes
        packet.R.leftMultiplicity packet.R.rightMultiplicity ^ 6 *
      secondActiveFrequencyGenerator (Arithmetic.context c) packet.R.primes
        packet.R.leftMultiplicity packet.R.rightMultiplicity (pattern packet) := by
  rw [packet.R.factor_sixth_active, pattern_eq packet hpacket h]

variable {packet}

theorem ordinary_pattern (O : OrdinaryData packet)
    (hpacket : packet.Realizes) (h : O.rows.live) :
    actualNonunitPattern (Arithmetic.context c) packet.R.primes
      packet.R.leftMultiplicity packet.R.rightMultiplicity (packet.R.frequency h.val) =
        pattern packet :=
  pattern_eq packet hpacket (O.originalLiveRow h)

theorem ordinary_sector (O : OrdinaryData packet)
    (hpacket : packet.Realizes) (h : O.rows.live) :
    (packet.R.extractedRow (Arithmetic.context c) (O.originalLiveRow h)).sector (probeData K c) =
      sector packet :=
  sector_eq packet hpacket (O.originalLiveRow h)

theorem ordinary_factor (O : OrdinaryData packet)
    (hpacket : packet.Realizes) (h : O.rows.live) :
    packet.R.factor (Arithmetic.context c) h.val =
      secondSixthRootGenerator (Arithmetic.context c) packet.R.primes
        packet.R.leftMultiplicity packet.R.rightMultiplicity ^ 6 *
      secondActiveFrequencyGenerator (Arithmetic.context c) packet.R.primes
        packet.R.leftMultiplicity packet.R.rightMultiplicity (pattern packet) :=
  factor_eq packet hpacket (O.originalLiveRow h)

/-- This is the raw row character of the child recipe, without its
unchanged parent plain or slot background. -/
def rowCharacter (P : OriginalPhaseData packet) (h : packet.R.live) : HeckeCharacter K :=
  call.localizedSource.source.recipe.correction *
    ((P.moving true).append
      (secondOriginalMovingFactors (probeData K c) (momentRowCharacters K c)
        (Arithmetic.context c) packet.R.primes packet.R.leftMultiplicity
        packet.R.rightMultiplicity (pattern packet))).character *
    completeIdealRowCharacter K
      ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K)))
      (probeData K c) (momentRowCharacters K c) (sector packet)
        (packet.R.extractedRow (Arithmetic.context c) h).momentIdeal

set_option maxHeartbeats 1000000 in
/-- The original exceptional predicate and the paid child use exactly
the same finite character on every genuine live row. -/
theorem exceptional_iff (P : OriginalPhaseData packet)
    (hpacket : packet.Realizes) (h : packet.R.live) :
    packet.leaf.exceptional h.val ↔ rowCharacter P h ∈ call.node.data.theta := by
  have hpattern := pattern_eq packet hpacket h
  have hsector := sector_eq packet hpacket h
  rcases hpacket with ⟨trace, geometry, raw, j, htrace, _, _, rfl⟩
  let i : Fin trace.expansion.count := (raw.index j).val.1.1
  have hphysical : (raw.packet j).second.physical = trace.expansion.source i :=
    htrace.second.physical i
  have hn : (trace.expansion.source i).first.firstElement ≠ 0 := by
    rw [← hphysical]
    exact P.first_nonzero
  have ht : match P.pool with
      | none => (trace.expansion.source i).first.tag = .direct ∨
          (trace.expansion.source i).first.tag = .main
      | some (e, q) => (trace.expansion.source i).first.tag = .error e q.val := by
    rw [← hphysical]
    exact P.pool_tag
  have hm : trace.expansion.moving i = P.moving false := by
    have he := expansion_moving trace.expansion htrace.cauchy htrace.expansion i hn P.pool ht
    have hpool : unpaidPoolMoving P.pool = P.poolMoving false := by
      cases hp : P.pool with
      | none =>
        simp only [unpaidPoolMoving, OriginalPhaseData.poolMoving, hp]
      | some qe =>
        rcases qe with ⟨e, q⟩
        simp only [unpaidPoolMoving, OriginalPhaseData.poolMoving, hp,
          Bool.false_eq_true, ite_false]
    simpa only [← hphysical, OriginalPhaseData.moving,
      OriginalPhaseData.firstMoving, ← hpool] using he
  change (trace.second.source i).rowCharacter (expansion := trace.expansion) i
      (raw.packet j).key.1 (raw.packet j).key.2.1
      (SourceClassKey.rowLabel (raw.packet j).key) h.val ∈ call.node.data.theta ↔ _
  dsimp only [SecondSource.rowCharacter]
  have hlive : h.val ∈
      ((trace.second.source i).rows (raw.packet j).key.1 (raw.packet j).key.2.1
        (SourceClassKey.rowLabel (raw.packet j).key)).live := by
    change h.val ∈ (raw.packet j).R.live
    exact h.property
  erw [dif_pos hlive]
  change (call.localizedSource.source.recipe.correction *
      ((trace.expansion.moving i).append
        (secondOriginalMovingFactors (probeData K c) (momentRowCharacters K c)
          (Arithmetic.context c) (raw.packet j).R.primes (raw.packet j).R.leftMultiplicity
          (raw.packet j).R.rightMultiplicity
          (actualNonunitPattern (Arithmetic.context c) (raw.packet j).R.primes
            (raw.packet j).R.leftMultiplicity (raw.packet j).R.rightMultiplicity
            ((raw.packet j).R.frequency h.val)))).character *
      completeIdealRowCharacter K
        ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K)))
        (probeData K c) (momentRowCharacters K c)
        (((raw.packet j).R.extractedRow (Arithmetic.context c) h).sector (probeData K c))
        ((raw.packet j).R.extractedRow (Arithmetic.context c) h).momentIdeal) ∈
      call.node.data.theta ↔ rowCharacter P h ∈ call.node.data.theta
  erw [hm, hpattern, hsector]
  unfold rowCharacter
  let D := secondOriginalMovingFactors (probeData K c) (momentRowCharacters K c)
    (Arithmetic.context c) (raw.packet j).R.primes (raw.packet j).R.leftMultiplicity
    (raw.packet j).R.rightMultiplicity (pattern (raw.packet j))
  have hcharacter : ((P.moving false).append D).character =
      ((P.moving true).append D).character := by
    calc
      _ = (P.moving false).character * D.character :=
        OriginalMovingFactors.append_character
          (A := Arithmetic.data c) (P := probeData K c) (R := momentRowCharacters K c)
          (P.moving false) D
      _ = (P.moving true).character * D.character :=
        congrArg (fun χ : HeckeCharacter K => χ * D.character)
          (PassivePhaseBridge.moving_character_paid P)
      _ = _ :=
        (OriginalMovingFactors.append_character
          (A := Arithmetic.data c) (P := probeData K c) (R := momentRowCharacters K c)
          (P.moving true) D).symm
  have hmembership := congrArg (fun χ : HeckeCharacter K =>
    call.localizedSource.source.recipe.correction * χ *
      completeIdealRowCharacter K
        ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K)))
        (probeData K c) (momentRowCharacters K c) (sector (raw.packet j))
        ((raw.packet j).R.extractedRow (Arithmetic.context c) h).momentIdeal ∈
      call.node.data.theta) hcharacter
  exact ⟨Eq.mp hmembership, Eq.mpr hmembership⟩

theorem ordinary_nonexceptional (seed : OrdinarySeed packet)
    (hpacket : packet.Realizes) (h : seed.ordinary.rows.live) :
    rowCharacter seed.phases (seed.ordinary.originalLiveRow h) ∉ call.node.data.theta := by
  have hrestricted : ∀ (predicate : Arithmetic.Orbit c → Prop)
      (row : (packet.R.restrictRows predicate).live), predicate row.val := by
    intro predicate row
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp row.property).1).2
  have hn : ¬packet.leaf.exceptional h.val :=
    hrestricted (fun row => ¬packet.leaf.exceptional row) h
  exact fun hm => hn ((exceptional_iff seed.phases hpacket
    (seed.ordinary.originalLiveRow h)).mpr hm)

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.CalibrationClass

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.CalibrationClass.pattern_eq
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.CalibrationClass.sector_eq
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.CalibrationClass.ordinary_factor
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.CalibrationClass.exceptional_iff
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.CalibrationClass.ordinary_nonexceptional

