import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.PassiveSourceOrigin
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SourceCharacters

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The paid moving mask is the actual physical paid support

The first factor contains exactly the active first primes and the
physical first divisor. The pool contributes its recorded moving
multiplicity. These facts are transported through the genuine source
trace. Radicals need not equal products with repeated primes, so the
comparison is stated as the exact coprimality equivalence used by each
individual coefficient.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

namespace PassivePaidMask

def firstElementSupport (a : (Arithmetic.data c).R) (ha : a ≠ 0) : Ideal (𝓞 K) :=
  (OriginalMovingFactors.singleton (P := probeData K c) (R := momentRowCharacters K c)
    ⟨a, ha⟩ 1).support.val

def poolSupport (pool : Option (AmplifierValuation × ExteriorPrime (Arithmetic.data c))) :
    Ideal (𝓞 K) :=
  match pool with
  | none => 1
  | some (e, q) => q.val.asIdeal ^ e.movingMultiplicity

private theorem primePowerProduct_coprime {A : SArithmeticData K}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (primes : ι → ExteriorPrime A) (e : ι → ℕ) (he : ∀ i, 0 < e i)
    (J : Ideal (𝓞 K)) :
    IsCoprime J (primePowerProduct primes e).val ↔
      IsCoprime J (primePowerProduct primes (fun _ => 1)).val := by
  change IsCoprime J (∏ i, (primes i).val.asIdeal ^ e i) ↔
    IsCoprime J (∏ i, (primes i).val.asIdeal ^ 1)
  simp only [IsCoprime.prod_right_iff, Finset.mem_univ, forall_const, pow_one]
  exact forall_congr' (fun i => IsCoprime.pow_right_iff (he i))

end PassivePaidMask

namespace FirstCauchyKey

variable {F : FirstPresentation call p} (key : FirstCauchyKey F)

def generatedFirstIdeal : (Arithmetic.data c).Exterior :=
  let b := FirstCauchyKey.block key
  let D := firstPhysicalDivisorIdeal (A := Arithmetic.data c) key.divisor.val
  if key.side then
    CanonicalLiteralFirstPhase.rightIdeal b.primes b.leftMultiplicity b.rightMultiplicity D
  else
    CanonicalLiteralFirstPhase.leftIdeal b.primes b.leftMultiplicity b.rightMultiplicity D

theorem firstElement_generates :
    (Arithmetic.data c).Generates key.generatedFirstIdeal key.firstElement := by
  dsimp only [generatedFirstIdeal, firstElement]
  split
  · exact CanonicalLiteralFirstPhase.rightElement_generates (Arithmetic.context c)
      _ _ _ _ _ (originalFrequencyIdeal_generates _
        (sIntegerMaskGenerator K ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K)))
          key.divisor.val).property)
  · exact CanonicalLiteralFirstPhase.leftElement_generates (Arithmetic.context c)
      _ _ _ _ _ (originalFrequencyIdeal_generates _
        (sIntegerMaskGenerator K ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K)))
          key.divisor.val).property)

theorem generatedFirstIdeal_coprime (J : Ideal (𝓞 K)) :
    IsCoprime J key.generatedFirstIdeal.val ↔
      IsCoprime J (firstActiveIdeal key.block.primes
        key.block.leftMultiplicity key.block.rightMultiplicity).val ∧
      IsCoprime J (firstPhysicalDivisorIdeal (A := Arithmetic.data c) key.divisor.val).val := by
  unfold generatedFirstIdeal
  split
  · change IsCoprime J (_ * (primePowerProduct _
      (CanonicalLiteralFirstPhase.rightExponent _ _)).val) ↔ _
    rw [IsCoprime.mul_right_iff, PassivePaidMask.primePowerProduct_coprime _ _
      (fun i => by unfold CanonicalLiteralFirstPhase.rightExponent; omega) J]
    exact and_comm
  · change IsCoprime J (_ * (primePowerProduct _
      (CanonicalLiteralFirstPhase.leftExponent _ _)).val) ↔ _
    rw [IsCoprime.mul_right_iff, PassivePaidMask.primePowerProduct_coprime _ _
      (fun i => by unfold CanonicalLiteralFirstPhase.leftExponent; omega) J]
    exact and_comm

theorem firstElementSupport_coprime (ha : key.firstElement ≠ 0) (J : Ideal (𝓞 K)) :
    IsCoprime J (PassivePaidMask.firstElementSupport key.firstElement ha) ↔
      IsCoprime J (firstActiveIdeal key.block.primes
        key.block.leftMultiplicity key.block.rightMultiplicity).val ∧
      IsCoprime J (firstPhysicalDivisorIdeal (A := Arithmetic.data c) key.divisor.val).val := by
  unfold PassivePaidMask.firstElementSupport
  rw [OriginalMovingFactors.coprime_support_iff_fullIdeal,
    OriginalMovingFactors.singleton_fullIdeal _ _ key.firstElement_generates 1]
  exact key.generatedFirstIdeal_coprime J

end FirstCauchyKey

namespace FirstCauchyFamily

variable {F : FirstPresentation call p} (family : FirstCauchyFamily F)

theorem paidSupport_coprime (hfamily : family.Realizes) (i : Fin family.count)
    (ha : (family.source i).first.firstElement ≠ 0) (J : Ideal (𝓞 K)) :
    IsCoprime J (family.source i).first.paidSupport.val ↔
      IsCoprime J call.oldSupport.val ∧
        IsCoprime J (PassivePaidMask.firstElementSupport
          (family.source i).first.firstElement ha) := by
  have hkey : (family.index i).firstElement ≠ 0 := by
    simpa only [hfamily.firstElement i] using ha
  have hs := (family.index i).firstElementSupport_coprime hkey J
  rw [hfamily.paid i, hfamily.complementary i,
    IsCoprime.mul_right_iff, IsCoprime.mul_right_iff]
  have hsupport : IsCoprime J (PassivePaidMask.firstElementSupport
      (family.source i).first.firstElement ha) ↔
      IsCoprime J (firstActiveIdeal (family.index i).block.primes
        (family.index i).block.leftMultiplicity (family.index i).block.rightMultiplicity).val ∧
        IsCoprime J (firstPhysicalDivisorIdeal (A := Arithmetic.data c)
          (family.index i).divisor.val).val := by
    simpa only [hfamily.firstElement i] using hs
  rw [hsupport]
  exact and_assoc

end FirstCauchyFamily

namespace PoolExpansion

variable {F : FirstPresentation call p} {family : FirstCauchyFamily F}

theorem paidSupport_coprime (expansion : PoolExpansion family)
    (hfamily : family.Realizes) (hexpansion : expansion.Realizes)
    (i : Fin expansion.count) (ha : (expansion.source i).first.firstElement ≠ 0)
    (poolChoice : Option (AmplifierValuation × ExteriorPrime (Arithmetic.data c)))
    (htag : match poolChoice with
      | none => (expansion.source i).first.tag = .direct ∨
          (expansion.source i).first.tag = .main
      | some (e, q) => (expansion.source i).first.tag = .error e q.val)
    (J : Ideal (𝓞 K)) :
    IsCoprime J (expansion.source i).first.paidSupport.val ↔
      (IsCoprime J call.oldSupport.val ∧
        IsCoprime J (PassivePaidMask.firstElementSupport
          (expansion.source i).first.firstElement ha)) ∧
        IsCoprime J (PassivePaidMask.poolSupport poolChoice) := by
  cases expansion with
  | direct =>
    change IsCoprime J (family.source i).first.paidSupport.val ↔ _
    have hp : poolChoice = none := by
      cases hc : poolChoice with
      | none => rfl
      | some eq =>
        rcases eq with ⟨e, q⟩
        have ht : (family.source i).first.tag = .error e q.val := by
          simpa only [hc] using htag
        rw [hfamily.tag i] at ht
        cases ht
    rw [hp]
    simpa only [PassivePaidMask.poolSupport, isCoprime_one_right, and_true] using
      family.paidSupport_coprime hfamily i ha J
  | pooled pool count index source =>
    obtain ⟨_, _, horigin⟩ := hexpansion
    change (source i).first.firstElement ≠ 0 at ha
    change IsCoprime J (source i).first.paidSupport.val ↔ _
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
            simpa only [hc] using htag
          rw [hfirst] at ht
          cases ht
      have hbase := family.paidSupport_coprime hfamily (index i).1
        (by simpa only [hfirst] using ha) J
      rw [hp]
      simpa only [hfirst, PassivePaidMask.poolSupport, isCoprime_one_right, and_true]
        using hbase
    | inr qe =>
      rcases qe with ⟨q, e⟩
      have he : pool.ErrorOrigin (index i).1 q e (source i) := by
        simpa only [PoolPresentation.Origin, hindex] using horigin i
      rcases he with ⟨_, _, _, _, _, _, _, _, _, _, _, helement, _, _, _, ht, _, hpaid⟩
      have hbase := family.paidSupport_coprime hfamily (index i).1
        (by simpa only [helement] using ha) J
      cases hc : poolChoice with
      | none =>
        have hh : (source i).first.tag = .direct ∨ (source i).first.tag = .main := by
          simpa only [hc] using htag
        rw [ht] at hh
        rcases hh with hh | hh <;> cases hh
      | some eq =>
        rcases eq with ⟨e', q'⟩
        have hh : (source i).first.tag = .error e' q'.val := by
          simpa only [hc] using htag
        have hsame := ht.symm.trans hh
        injection hsame with heq hq
        rw [hpaid, IsCoprime.mul_right_iff, hbase]
        simp only [PassivePaidMask.poolSupport, hc, helement, ← heq, ← hq]

end PoolExpansion

namespace OriginalPhaseData

variable {packet : RawLeafPacket call p} (P : OriginalPhaseData packet)

theorem paidPool_support :
    (P.poolMoving true).support.val = PassivePaidMask.poolSupport P.pool := by
  cases hp : P.pool with
  | none =>
    have hg : (Arithmetic.data c).Generates (unitExterior (Arithmetic.data c))
        (1 : (Arithmetic.data c).R) :=
      ⟨one_ne_zero, by simp [unitExterior, SArithmeticData.extendIdeal]⟩
    simp only [poolMoving, hp, PassivePaidMask.poolSupport,
      OriginalMovingFactors.singleton_support _ _ hg 1]
    simp [CommonSupportMass.commonRadical, unitExterior,
      HeckePort.IdealMobiusDivisorSum.primeSupport]
  | some eq =>
    rcases eq with ⟨e, q⟩
    simpa only [poolMoving, hp, PassivePaidMask.poolSupport, if_true] using
      CanonicalLiteralPassivePhases.activeMoving_support
        (probeData K c) (momentRowCharacters K c) (Arithmetic.context c) q e

theorem paidMask_factors (J : Ideal (𝓞 K)) :
    IsCoprime J (P.mask true).val ↔
      (IsCoprime J call.oldSupport.val ∧
        IsCoprime J (PassivePaidMask.firstElementSupport
          packet.second.physical.first.firstElement P.first_nonzero)) ∧
        IsCoprime J (PassivePaidMask.poolSupport P.pool) := by
  change IsCoprime J
    (((P.moving true).effectiveFullSupport
      call.localizedSource.source.recipe.remaining).val * 1) ↔ _
  rw [mul_one, OriginalMovingFactors.effectiveFullSupport_val]
  unfold moving
  rw [OriginalMovingFactors.coprime_append_fullMaskSupport,
    CanonicalLiteralFixedPhases.emptyDivisorMoving_support,
    and_iff_left isCoprime_one_right,
    OriginalMovingFactors.coprime_append_fullMaskSupport,
    OriginalMovingFactors.coprime_append_fullMaskSupport, P.paidPool_support]
  rfl

/-- The actual paid coefficient mask, occurrence by occurrence. -/
theorem paidMask_coprime (hpacket : packet.Realizes) (J : Ideal (𝓞 K)) :
    IsCoprime J (P.mask true).val ↔
      IsCoprime J packet.second.physical.first.paidSupport.val := by
  rw [P.paidMask_factors J]
  rcases hpacket with ⟨trace, geometry, raw, j, htrace, _, _, hpacket⟩
  subst packet
  let i : Fin trace.expansion.count := (raw.index j).val.1.1
  have hphysical := htrace.second.physical i
  have hn : (trace.expansion.source i).first.firstElement ≠ 0 := by
    rw [← hphysical]
    exact P.first_nonzero
  have ht : match P.pool with
      | none => (trace.expansion.source i).first.tag = .direct ∨
          (trace.expansion.source i).first.tag = .main
      | some (e, q) => (trace.expansion.source i).first.tag = .error e q.val := by
    rw [← hphysical]
    exact P.pool_tag
  have he := trace.expansion.paidSupport_coprime htrace.cauchy htrace.expansion
    i hn P.pool ht J
  simpa only [← hphysical] using he.symm

end OriginalPhaseData
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.OriginalPhaseData.paidMask_coprime
