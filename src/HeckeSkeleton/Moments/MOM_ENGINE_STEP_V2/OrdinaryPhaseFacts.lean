module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.RawContracts
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.OriginalPhaseData

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The actual first and pool phases of an original raw leaf

The pool choice is read from the source tag.  The canonical first
element and the original empty-divisor unit remain literal factors of
the same moving list that defined the exceptional predicate.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.OrdinaryPhaseFacts

open EngineStep EngineInduction.Source
open NumberField IsDedekindDomain MeasureTheory DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments HeckePort.Moments.Support UniqueFactorizationMonoid
open HeckePort.IdealMobiusDivisorSum

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable {F : FirstPresentation call p} {family : FirstCauchyFamily F}

theorem firstElement_nonzero (key : FirstCauchyKey F) :
    FirstCauchyKey.firstElement key ≠ 0 := by
  let b := FirstCauchyKey.block key
  let delta := sIntegerMaskGenerator K
    ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K))) key.2.1.val
  let D := firstPhysicalDivisorIdeal (A := Arithmetic.data c) key.2.1.val
  have hD : (Arithmetic.data c).Generates D delta.val :=
    originalFrequencyIdeal_generates delta.val delta.property
  change (if FirstCauchyKey.side key then
    CanonicalLiteralFirstPhase.rightElement (Arithmetic.context c)
      b.primes b.leftMultiplicity b.rightMultiplicity delta.val
    else CanonicalLiteralFirstPhase.leftElement (Arithmetic.context c)
      b.primes b.leftMultiplicity b.rightMultiplicity delta.val) ≠ 0
  split_ifs
  · exact (CanonicalLiteralFirstPhase.rightElement_generates (Arithmetic.context c)
      b.primes b.leftMultiplicity b.rightMultiplicity D delta.val hD).1
  · exact (CanonicalLiteralFirstPhase.leftElement_generates (Arithmetic.context c)
      b.primes b.leftMultiplicity b.rightMultiplicity D delta.val hD).1

theorem firstMoving_eq_singleton (key : FirstCauchyKey F) :
    FirstCauchyKey.moving key =
      OriginalMovingFactors.singleton (P := probeData K c) (R := momentRowCharacters K c)
        ⟨FirstCauchyKey.firstElement key, firstElement_nonzero key⟩ 1 := by
  unfold FirstCauchyKey.moving FirstCauchyKey.firstElement
  dsimp only
  split_ifs <;> rfl

def poolOption (expansion : PoolExpansion family) :
    Fin expansion.count → Option (AmplifierValuation × ExteriorPrime (Arithmetic.data c)) :=
  match expansion with
  | .direct => fun _ => none
  | .pooled _ _ index _ => fun i =>
    match (index i).2 with
    | .inl _ => none
    | .inr qe => some (qe.2, qe.1.val)

structure PhaseFacts (source : PhysicalSource call p)
    (first : (Arithmetic.data c).R)
    (pool : Option (AmplifierValuation × ExteriorPrime (Arithmetic.data c))) : Prop where
  first_eq : source.first.firstElement = first
  tag : match pool with
    | none => source.first.tag = .direct ∨ source.first.tag = .main
    | some (e, q) => source.first.tag = .error e q.val
  power : source.first.poolPower = match pool with
    | none => unitExterior (Arithmetic.data c)
    | some (e, q) => powerIdeal q e.multiplicity
  deletion : (∏ I ∈ source.first.fullDeletion, I) ≠ 0

private theorem primeSupport_nonzero (I J : Ideal (𝓞 K)) (hI : I ≠ 0)
    (hJ : J ∈ primeSupport I) : J ≠ 0 := by
  intro hz
  have hd : J ∣ I := dvd_of_mem_normalizedFactors (by
    simpa only [primeSupport, Multiset.mem_toFinset] using hJ)
  rw [hz, zero_dvd_iff] at hd
  exact hI hd

theorem first_phase_facts (hfamily : family.Realizes) (i : Fin family.count) :
    PhaseFacts (family.source i) (FirstCauchyKey.firstElement (family.index i)) none where
  first_eq := hfamily.firstElement i
  tag := Or.inl (hfamily.tag i)
  power := hfamily.poolPower i
  deletion := by
    rw [hfamily.deletion i]
    exact Finset.prod_ne_zero_iff.mpr (fun J hJ =>
      primeSupport_nonzero (family.source i).first.selected.val J
        (nonZeroDivisors.coe_ne_zero _) hJ)

theorem first_deletion_prime (hfamily : family.Realizes) (i : Fin family.count) :
    ∀ Q ∈ (family.source i).first.fullDeletion, Prime Q := by
  intro Q hQ
  rw [hfamily.deletion i] at hQ
  exact ((mem_normalizedFactors_iff
    (nonZeroDivisors.coe_ne_zero (family.source i).first.selected)).mp
      (by simpa only [primeSupport, Multiset.mem_toFinset] using hQ)).1

theorem deletion_prime (hfamily : family.Realizes)
    (expansion : PoolExpansion family) (hexpansion : expansion.Realizes)
    (i : Fin expansion.count) :
    ∀ Q ∈ (expansion.source i).first.fullDeletion, Prime Q := by
  cases expansion with
  | direct => exact first_deletion_prime hfamily i
  | pooled P count index source =>
    rcases hexpansion with ⟨hslots, hP, horigin⟩
    have hf := first_deletion_prime hfamily (index i).1
    have ho := horigin i
    cases he : (index i).2 with
    | inl u =>
      rw [PoolPresentation.Origin, he] at ho
      rcases ho with ⟨hcol, hs, ha, hm, hk, hp, hw, hfirst⟩
      simpa only [PoolExpansion.source, hfirst] using hf
    | inr qe =>
      rw [PoolPresentation.Origin, he] at ho
      rcases ho with ⟨hcol, hs, ha, hm, hk, hp, hw, hselected, hopposite,
        hcomplementary, hresidual, helement, hright, hpower, hscale, htag,
        hdeletion, hpaid⟩
      change ∀ Q ∈ (source i).first.fullDeletion, Prime Q
      rw [hdeletion]
      intro Q hQ
      rcases Finset.mem_union.mp hQ with hQ | hQ
      · exact hf Q hQ
      · rw [Finset.mem_singleton.mp hQ]
        exact qe.1.val.val.prime

theorem phase_facts (hfamily : family.Realizes)
    (expansion : PoolExpansion family) (hexpansion : expansion.Realizes)
    (i : Fin expansion.count) :
    PhaseFacts (expansion.source i)
      (FirstCauchyKey.firstElement (family.index (expansion.firstIndex i)))
      (poolOption expansion i) := by
  cases expansion with
  | direct => exact first_phase_facts hfamily i
  | pooled P count index source =>
    rcases hexpansion with ⟨hslots, hP, horigin⟩
    have hf := first_phase_facts hfamily (index i).1
    have ho := horigin i
    cases he : (index i).2 with
    | inl u =>
      rw [PoolPresentation.Origin, he] at ho
      rcases ho with ⟨hcol, hs, ha, hm, hk, hp, hw, hfirst⟩
      simp only [poolOption, he, PoolExpansion.source, PoolExpansion.firstIndex]
      refine { first_eq := ?_, tag := ?_, power := ?_, deletion := ?_ }
      · simpa only [PoolExpansion.source, PoolExpansion.firstIndex, hfirst]
          using hf.first_eq
      · simp only [poolOption, he, PoolExpansion.source]
        exact Or.inr (by rw [hfirst])
      · change (source i).first.poolPower = _
        simpa only [poolOption, he, hfirst] using hf.power
      · simpa only [PoolExpansion.source, hfirst] using hf.deletion
    | inr qe =>
      rw [PoolPresentation.Origin, he] at ho
      rcases ho with ⟨hcol, hs, ha, hm, hk, hp, hw, hselected, hopposite,
        hcomplementary, hresidual, helement, hright, hpower, hscale, htag,
        hdeletion, hpaid⟩
      simp only [poolOption, he, PoolExpansion.source, PoolExpansion.firstIndex]
      refine { first_eq := ?_, tag := ?_, power := ?_, deletion := ?_ }
      · exact helement.trans hf.first_eq
      · simpa only [poolOption, he, PoolExpansion.source] using htag
      · simpa only [poolOption, he, PoolExpansion.source] using hpower
      · change (∏ I ∈ (source i).first.fullDeletion, I) ≠ 0
        rw [hdeletion]
        apply Finset.prod_ne_zero_iff.mpr
        intro I hI
        rcases Finset.mem_union.mp hI with hI | hI
        · exact (Finset.prod_ne_zero_iff.mp hf.deletion) I hI
        · rw [Finset.mem_singleton.mp hI]
          exact qe.1.val.val.ne_bot

private def ofPhaseFacts (packet : RawLeafPacket call p)
    (first : (Arithmetic.data c).R) (hfirst : first ≠ 0)
    (pool : Option (AmplifierValuation × ExteriorPrime (Arithmetic.data c)))
    (facts : PhaseFacts packet.second.physical first pool) : OriginalPhaseData packet where
  first_nonzero := by
    rw [facts.first_eq]
    exact hfirst
  pool := pool
  pool_tag := by
    cases pool with
    | none => exact facts.tag
    | some ep =>
      rcases ep with ⟨e, q⟩
      exact facts.tag
  pool_power := by
    cases pool with
    | none => exact facts.power
    | some ep =>
      rcases ep with ⟨e, q⟩
      exact facts.power
  deletion_nonzero := facts.deletion

def ofSource (packet : RawLeafPacket call p)
    (family : FirstCauchyFamily F) (hfamily : family.Realizes)
    (expansion : PoolExpansion family) (hexpansion : expansion.Realizes)
    (i : Fin expansion.count)
    (physical : packet.second.physical = expansion.source i) : OriginalPhaseData packet :=
  ofPhaseFacts packet (FirstCauchyKey.firstElement (family.index (expansion.firstIndex i)))
    (firstElement_nonzero _) (poolOption expansion i)
    (by simpa only [physical] using phase_facts hfamily expansion hexpansion i)

theorem ofSource_firstMoving (packet : RawLeafPacket call p)
    (family : FirstCauchyFamily F) (hfamily : family.Realizes)
    (expansion : PoolExpansion family) (hexpansion : expansion.Realizes)
    (i : Fin expansion.count)
    (physical : packet.second.physical = expansion.source i) :
    (ofSource packet family hfamily expansion hexpansion i physical).firstMoving =
      FirstCauchyKey.moving (family.index (expansion.firstIndex i)) := by
  rw [firstMoving_eq_singleton]
  apply congrArg (fun a => OriginalMovingFactors.singleton
    (P := probeData K c) (R := momentRowCharacters K c) a 1)
  apply Subtype.ext
  exact (congrArg (fun s : PhysicalSource call p => s.first.firstElement) physical).trans
    (phase_facts hfamily expansion hexpansion i).first_eq

theorem ofSource_poolMoving_false (packet : RawLeafPacket call p)
    (family : FirstCauchyFamily F) (hfamily : family.Realizes)
    (expansion : PoolExpansion family) (hexpansion : expansion.Realizes)
    (i : Fin expansion.count)
    (physical : packet.second.physical = expansion.source i) :
    (ofSource packet family hfamily expansion hexpansion i physical).poolMoving false =
      expansion.poolMoving i := by
  cases expansion with
  | direct => rfl
  | pooled P count index source =>
    cases he : (index i).2 <;>
      simp only [OriginalPhaseData.poolMoving, ofSource, ofPhaseFacts, poolOption,
        PoolExpansion.poolMoving, he, Bool.false_eq_true, ↓reduceIte]

theorem ofSource_moving_false (packet : RawLeafPacket call p)
    (family : FirstCauchyFamily F) (hfamily : family.Realizes)
    (expansion : PoolExpansion family) (hexpansion : expansion.Realizes)
    (i : Fin expansion.count)
    (physical : packet.second.physical = expansion.source i) :
    (ofSource packet family hfamily expansion hexpansion i physical).moving false =
      expansion.moving i := by
  unfold OriginalPhaseData.moving PoolExpansion.moving
  rw [ofSource_firstMoving, ofSource_poolMoving_false]

def ofRaw (trace : SourceTrace call p) (htrace : trace.Realizes)
    {geometry : GeometryFamily trace.second} (raw : RawFamily geometry)
    (j : Fin raw.count) : OriginalPhaseData (raw.packet j) :=
  ofSource (raw.packet j) trace.cauchy htrace.cauchy trace.expansion htrace.expansion
    (raw.index j).val.1.1 (htrace.second.physical _)

theorem ofRaw_moving_false (trace : SourceTrace call p) (htrace : trace.Realizes)
    {geometry : GeometryFamily trace.second} (raw : RawFamily geometry)
    (j : Fin raw.count) :
    (ofRaw trace htrace raw j).moving false =
      trace.expansion.moving (raw.index j).val.1.1 :=
  ofSource_moving_false (raw.packet j) trace.cauchy htrace.cauchy
    trace.expansion htrace.expansion (raw.index j).val.1.1 (htrace.second.physical _)

theorem ordinaryPhaseData (packet : RawLeafPacket call p) (hpacket : packet.Realizes) :
    Nonempty (OriginalPhaseData packet) := by
  obtain ⟨trace, geometry, raw, j, htrace, hgeometry, hraw, rfl⟩ := hpacket
  exact ⟨ofRaw trace htrace raw j⟩

theorem mask_false (packet : RawLeafPacket call p) (P : OriginalPhaseData packet) :
    P.mask false =
      exteriorMomentIdeal ((P.moving false).effectiveFullSupport
        call.localizedSource.source.recipe.remaining) * P.deletionIdeal := rfl

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.OrdinaryPhaseFacts

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.OrdinaryPhaseFacts.ordinaryPhaseData
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.OrdinaryPhaseFacts.ofRaw_moving_false
