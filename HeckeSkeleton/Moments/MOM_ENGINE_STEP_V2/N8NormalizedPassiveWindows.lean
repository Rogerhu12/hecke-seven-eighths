import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N8NormalizedFrozenAtoms
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N8SourceResidualWindows

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The actual passive mask inherits the original-column norm window

The full deletion is the original selected support, with the one
original pool prime adjoined on an error. Its squarefree product divides
the full combined extraction. The restored passive mask is a divisor of
that product. Its two real occurrence carriers therefore have the same
uniform subpower cardinal bound before any normalization is selected.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep EngineInduction.Source
open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton.Global
open HeckePort.Moments HeckePort.Moments.Support HeckePort.IdealMobiusDivisorSum
open CommonSupportMass

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable {F : FirstPresentation call p} {family : FirstCauchyFamily F}

namespace FirstCauchyFamily

variable (family : FirstCauchyFamily F)

theorem deletionProduct_dvd_combined (hf : family.Realizes) (i : Fin family.count) :
    (∏ I ∈ (family.source i).first.fullDeletion, I) ∣
      (family.source i).first.selected.val * (family.source i).first.poolPower.val := by
  rw [hf.deletion i, hf.poolPower i]
  simpa only [unitExterior, Ideal.mul_top] using
    (support_product_dvd
      (nonZeroDivisors.coe_ne_zero (family.source i).first.selected)
      (show primeSupport (family.source i).first.selected.val ⊆
          primeSupport (family.source i).first.selected.val from fun _ h => h))

end FirstCauchyFamily

namespace PoolPresentation

variable (pool : PoolPresentation family)

theorem main_deletionProduct_dvd_combined (hf : family.Realizes)
    (i : Fin family.count) (source : PhysicalSource call p)
    (horigin : pool.MainOrigin i source) :
    (∏ I ∈ source.first.fullDeletion, I) ∣ source.first.selected.val * source.first.poolPower.val := by
  rcases horigin with ⟨_, _, _, _, _, _, _, hfirst⟩
  rw [hfirst]
  exact family.deletionProduct_dvd_combined hf i

theorem error_deletionProduct_dvd_combined (hf : family.Realizes)
    (i : Fin family.count) (q : pool.pool.primes) (e : AmplifierValuation)
    (source : PhysicalSource call p) (horigin : pool.ErrorOrigin i q e source) :
    (∏ I ∈ source.first.fullDeletion, I) ∣ source.first.selected.val * source.first.poolPower.val := by
  rcases horigin with
    ⟨_, _, _, _, _, _, _, hselected, _, _, _, _, _, hpower, _, _, hdeletion, _⟩
  rw [hdeletion, hf.deletion i, hselected, hpower]
  change (∏ I ∈ primeSupport (family.source i).first.selected.val ∪ {q.val.val.asIdeal}, I) ∣
    (family.source i).first.selected.val * q.val.val.asIdeal ^ e.multiplicity
  have hprod : (family.source i).first.selected.val * q.val.val.asIdeal ^ e.multiplicity ≠ 0 :=
    mul_ne_zero (nonZeroDivisors.coe_ne_zero (family.source i).first.selected)
      (pow_ne_zero _ q.val.val.ne_bot)
  apply support_product_dvd hprod
  intro I hI
  rcases Finset.mem_union.mp hI with hI | hI
  · have hprime := support_prime hI
    have hdiv := (prime_mem_support_iff_dvd I _ hprime
      (nonZeroDivisors.coe_ne_zero (family.source i).first.selected)).mp hI
    exact (prime_mem_support_iff_dvd I _ hprime hprod).mpr
      (hdiv.trans (dvd_mul_right _ _))
  · have heq := Finset.mem_singleton.mp hI
    subst I
    have hpower : q.val.val.asIdeal ∣ q.val.val.asIdeal ^ e.multiplicity := by
      simpa only [pow_one] using pow_dvd_pow q.val.val.asIdeal
        (show 1 ≤ e.multiplicity by cases e <;> norm_num [AmplifierValuation.multiplicity])
    exact (prime_mem_support_iff_dvd _ _ q.val.val.prime hprod).mpr
      (hpower.trans (dvd_mul_left _ _))

end PoolPresentation

namespace PoolExpansion

variable (expansion : PoolExpansion family)

theorem deletionProduct_dvd_combined (hf : family.Realizes)
    (hexpansion : expansion.Realizes) (i : Fin expansion.count) :
    (∏ I ∈ (expansion.source i).first.fullDeletion, I) ∣
      (expansion.source i).first.selected.val * (expansion.source i).first.poolPower.val := by
  cases expansion with
  | direct => exact family.deletionProduct_dvd_combined hf i
  | pooled pool count index source =>
    cases hi : (index i).2 with
    | inl u =>
      apply pool.main_deletionProduct_dvd_combined hf (index i).1 (source i)
      simpa only [PoolPresentation.Origin, hi] using hexpansion.2.2 i
    | inr qe =>
      apply pool.error_deletionProduct_dvd_combined hf (index i).1 qe.1 qe.2 (source i)
      simpa only [PoolPresentation.Origin, hi] using hexpansion.2.2 i

end PoolExpansion

namespace RawLeafPacket

variable (packet : RawLeafPacket call p)

set_option maxHeartbeats 1000000 in
theorem deletionProduct_dvd_combined (hpacket : packet.Realizes) :
    (∏ I ∈ packet.second.physical.first.fullDeletion, I) ∣
      packet.second.physical.first.selected.val * packet.second.physical.first.poolPower.val := by
  rcases hpacket with ⟨trace, geometry, raw, j, htrace, _, _, rfl⟩
  let property (source : PhysicalSource call p) : Prop :=
    (∏ I ∈ source.first.fullDeletion, I) ∣
      source.first.selected.val * source.first.poolPower.val
  change property (trace.second.source (raw.index j).val.1.1).physical
  have hsource : property (trace.expansion.source (raw.index j).val.1.1) :=
    trace.expansion.deletionProduct_dvd_combined htrace.cauchy htrace.expansion _
  exact Eq.mpr (congrArg property (htrace.second.physical (raw.index j).val.1.1)) hsource

theorem combined_extraction_norm (input : ProfileInput call) (hpacket : packet.Realizes)
    (large : N8Source.normThreshold c call.frame ≤ call.base) :
    (Ideal.absNorm (packet.second.physical.first.selected.val *
      packet.second.physical.first.poolPower.val) : ℝ) ≤ call.base ^ N8Source.columnExponent c := by
  rcases hpacket with ⟨trace, geometry, raw, j, htrace, _, _, rfl⟩
  apply trace.second.combined_extraction_norm input large htrace.first htrace.cauchy
    htrace.expansion htrace.second (raw.index j).val.1.1
  obtain ⟨ij, hij, _⟩ := Finset.mem_image.mp (raw.packet j).key.1.property
  exact ⟨ij.1, (Finset.mem_product.mp hij).1⟩

end RawLeafPacket

namespace OrdinarySeed

variable {packet : RawLeafPacket call p} (seed : OrdinarySeed packet)

theorem passiveMask_dvd_combined (hpacket : packet.Realizes) :
    seed.ordinary.passiveMask ∣
      packet.second.physical.first.selected.val * packet.second.physical.first.poolPower.val :=
  seed.passiveMask_dvd_originalDeletion.trans (packet.deletionProduct_dvd_combined hpacket)

theorem passiveMask_norm (input : ProfileInput call) (hpacket : packet.Realizes)
    (large : N8Source.normThreshold c call.frame ≤ call.base) :
    (Ideal.absNorm seed.ordinary.passiveMask : ℝ) ≤ call.base ^ N8Source.columnExponent c :=
  (norm_le_of_dvd
    (mul_ne_zero (nonZeroDivisors.coe_ne_zero packet.second.physical.first.selected)
      packet.second.physical.first.poolPower.property.1)
    (seed.passiveMask_dvd_combined hpacket)).trans
      (packet.combined_extraction_norm input hpacket large)

end OrdinarySeed

namespace N8Normalized

/-- A fixed coefficient for both actual passive carriers. The call,
its original source and every label occur after the coefficient. -/
theorem passive_label_card_bound (c : TargetContext K) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (call : Call c) (input : ProfileInput call),
      N8Source.normThreshold c call.frame ≤ call.base →
      ∀ (p : SourceParameters c) (packet : RawLeafPacket call p), packet.Realizes →
      ∀ (seed : OrdinarySeed packet) (support : seed.ordinary.PassiveSupport input)
        (side : Bool), ((support.labels side).card : ℝ) ≤ C * call.base ^ ε := by
  obtain ⟨C, hC, hb⟩ := PassiveAllocation.labels_card_power_scale (K := K)
    c.geometry.slots (N8Source.columnExponent c) ε (N8Source.columnExponent_pos c).le hε
  refine ⟨C, hC, ?_⟩
  intro call input large p packet hpacket seed support side
  exact hb call.base call.domain.scale.le seed.ordinary.passiveMask
    (seed.passiveMask_norm input hpacket large) _
    (seed.residualSlotCount_le input support side) (support.carrier side)

theorem passive_label_pair_bound (c : TargetContext K) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (call : Call c) (input : ProfileInput call),
      N8Source.normThreshold c call.frame ≤ call.base →
      ∀ (p : SourceParameters c) (packet : RawLeafPacket call p), packet.Realizes →
      ∀ (seed : OrdinarySeed packet) (support : seed.ordinary.PassiveSupport input),
        ((support.labels false).card : ℝ) * (support.labels true).card ≤
          C * call.base ^ (2 * ε) := by
  obtain ⟨C, hC, hb⟩ := passive_label_card_bound c ε hε
  refine ⟨C ^ 2, sq_pos_of_pos hC, ?_⟩
  intro call input large p packet hpacket seed support
  apply (mul_le_mul (hb call input large p packet hpacket seed support false)
    (hb call input large p packet hpacket seed support true)
    (Nat.cast_nonneg _) (mul_nonneg hC.le (Real.rpow_nonneg call.base_pos.le _))).trans_eq
  rw [show 2 * ε = ε + ε by ring, Real.rpow_add call.base_pos]
  ring

end N8Normalized
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.deletionProduct_dvd_combined
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.OrdinarySeed.passiveMask_norm
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.N8Normalized.passive_label_pair_bound
