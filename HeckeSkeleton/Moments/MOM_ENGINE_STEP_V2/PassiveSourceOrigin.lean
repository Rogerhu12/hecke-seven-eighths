import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.RawContracts
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.PassivePhaseBridge

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Residual pool masks are covered by the original deletion

The genuine source trace distinguishes direct, pooled-main and each
valuation error. An error's actual prime belongs to its recorded full
deletion. Thus the passive valuation-six mask in the original/paid phase
identity divides that deletion product; it is not an additional mask
assumption on N2.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep NumberField DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

namespace PoolExpansion

variable {F : FirstPresentation call p} {family : FirstCauchyFamily F}

theorem error_prime_mem_fullDeletion (expansion : PoolExpansion family)
    (hfamily : family.Realizes) (hexpansion : expansion.Realizes)
    (i : Fin expansion.count) (e : AmplifierValuation)
    (q : HeightOneSpectrum (𝓞 K))
    (htag : (expansion.source i).first.tag = .error e q) :
    q.asIdeal ∈ (expansion.source i).first.fullDeletion := by
  cases expansion with
  | direct =>
    have ht := hfamily.tag i
    change (family.source i).first.tag = .error e q at htag
    rw [ht] at htag
    cases htag
  | pooled pool count index source =>
    obtain ⟨_, _, horigin⟩ := hexpansion
    change (source i).first.tag = .error e q at htag
    change q.asIdeal ∈ (source i).first.fullDeletion
    cases hindex : (index i).2 with
    | inl u =>
      have hm : pool.MainOrigin (index i).1 (source i) := by
        simpa only [PoolPresentation.Origin, hindex] using horigin i
      rcases hm with ⟨_, _, _, _, _, _, _, hfirst⟩
      rw [hfirst] at htag
      cases htag
    | inr qe =>
      rcases qe with ⟨q', e'⟩
      have he : pool.ErrorOrigin (index i).1 q' e' (source i) := by
        simpa only [PoolPresentation.Origin, hindex] using horigin i
      rcases he with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, ht, hd, _⟩
      have hq : q'.val.val = q := by
        have hh := ht.symm.trans htag
        injection hh with _ hq
        exact hq
      rw [hd, ← hq]
      exact Finset.mem_union_right _ (Finset.mem_singleton_self _)

end PoolExpansion

namespace RawLeafPacket

theorem error_prime_mem_fullDeletion (packet : RawLeafPacket call p)
    (hpacket : packet.Realizes) (e : AmplifierValuation)
    (q : HeightOneSpectrum (𝓞 K))
    (htag : packet.second.physical.first.tag = .error e q) :
    q.asIdeal ∈ packet.second.physical.first.fullDeletion := by
  rcases hpacket with ⟨trace, geometry, raw, j, htrace, _, _, rfl⟩
  let i : Fin trace.expansion.count := (raw.index j).val.1.1
  have hphysical := htrace.second.physical i
  change (trace.second.source i).physical.first.tag = .error e q at htag
  change q.asIdeal ∈ (trace.second.source i).physical.first.fullDeletion
  rw [hphysical] at htag ⊢
  exact trace.expansion.error_prime_mem_fullDeletion htrace.cauchy
    htrace.expansion i e q htag

end RawLeafPacket

namespace PassivePhaseBridge

variable {packet : RawLeafPacket call p}

/-- The extra passive pool gate is already present in the actual full
deletion. Its removal from the phase identity therefore uses no new
coprimality premise. -/
theorem poolPassiveIdeal_dvd_deletion (P : OriginalPhaseData packet)
    (hpacket : packet.Realizes) :
    (poolPassiveIdeal P).val ∣ P.deletionIdeal.val := by
  cases hp : P.pool with
  | none =>
    simp [poolPassiveIdeal, hp, unitExterior]
  | some qe =>
    rcases qe with ⟨e, q⟩
    have ht : packet.second.physical.first.tag = .error e q.val := by
      simpa only [hp] using P.pool_tag
    have hmem := packet.error_prime_mem_fullDeletion hpacket e q.val ht
    have hdiv : q.val.asIdeal ∣ P.deletionIdeal.val :=
      Finset.dvd_prod_of_mem (fun I : Ideal (𝓞 K) => I) hmem
    simp only [poolPassiveIdeal, hp]
    cases e with
    | one => simp [CanonicalLiteralPassivePhases.passiveIdeal,
        CanonicalLiteralPassivePhases.passiveExponent, powerIdeal]
    | six => simpa only [CanonicalLiteralPassivePhases.passiveIdeal,
        CanonicalLiteralPassivePhases.passiveExponent, powerIdeal, pow_one] using hdiv
    | seven => simp [CanonicalLiteralPassivePhases.passiveIdeal,
        CanonicalLiteralPassivePhases.passiveExponent, powerIdeal]

end PassivePhaseBridge
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.PassivePhaseBridge.poolPassiveIdeal_dvd_deletion
