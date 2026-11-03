import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N8SourceOuterPool
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.SecondZeroOrbitMultiplicity
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N8NormalizedArithmeticReduction

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The original outer scalar and physical fibre pay the original index

The shared orbit lemmas apply to the actual direct, main and error row
carriers. Their main multiplicity is bounded by the fixed original row
norm window already proved for N8a. The resulting pointwise inequality
keeps both independent Möbius factors and the inner divisor norm.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep EngineInduction.Source
open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open CommonSupportMass HeckePort.IdealMobiusDivisorSum HeckePort.Moments
open HeckeGeneral.ThetaSkeleton.Global Tasks.SecondZeroProof

variable {K : Type} [Field K] [NumberField K]

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable {F : FirstPresentation call p} {family : FirstCauchyFamily F}

namespace N8Source

def orbitBound (c : TargetContext K) (p : SourceParameters c) : ℝ :=
  max 1 (poolMultiplicityBound c p)

theorem orbitBound_one_le (c : TargetContext K) (p : SourceParameters c) :
    1 ≤ orbitBound c p := le_max_left _ _

theorem orbitBound_nonneg (c : TargetContext K) (p : SourceParameters c) :
    0 ≤ orbitBound c p := zero_le_one.trans (orbitBound_one_le c p)

def outerConstant (c : TargetContext K) (p : SourceParameters c) : ℝ :=
  orbitBound c p * orbitalFieldFactor K

theorem outerConstant_nonneg (c : TargetContext K) (p : SourceParameters c) :
    0 ≤ outerConstant c p :=
  mul_nonneg (orbitBound_nonneg c p) (orbitalFieldFactor_nonneg K)

end N8Source

namespace PoolPresentation

variable (pool : PoolPresentation family)

theorem multiplicity_le_bound (input : ProfileInput call)
    (large : N8Source.normThreshold c call.frame ≤ call.base)
    (hF : F.Realizes) (hf : family.Realizes)
    (hw : ∀ i, (family.source i).Windows) (hp : pool.Realizes) (i : Fin family.count) :
    (pool.data i).multiplicity ≤ N8Source.poolMultiplicityBound c p := by
  have hM : (pool.data i).rowExponent ≤ N8Source.firstRowExponent c p := by
    rw [hp.rowExponent i]
    exact family.rowExponent_le input large hF hf i (hw i)
  have hs : 0 < recipeInductionSigma c := (recipeInduction_budget (c := c)).1
  exact div_le_div_of_nonneg_right (add_le_add hM le_rfl) (by positivity)

theorem orbitMultiplicity_le_bound (input : ProfileInput call)
    (large : N8Source.normThreshold c call.frame ≤ call.base)
    (hF : F.Realizes) (hf : family.Realizes)
    (hw : ∀ i, (family.source i).Windows) (hp : pool.Realizes)
    (j : pool.Index) (source : PhysicalSource call p) (horigin : pool.Origin j source) :
    (source.orbitMultiplicity : ℝ) ≤ N8Source.orbitBound c p := by
  rcases j with ⟨i, branch⟩
  cases branch with
  | inl u =>
    exact (main_orbit_multiplicity_le hF hf pool hp i source horigin).trans
      ((pool.multiplicity_le_bound input large hF hf hw hp i).trans (le_max_right _ _))
  | inr qe =>
    have h : (source.orbitMultiplicity : ℝ) ≤ 1 := by
      exact_mod_cast error_orbit_multiplicity_le_one hF hf pool hp i qe.1 qe.2 source horigin
    exact h.trans (N8Source.orbitBound_one_le c p)

end PoolPresentation

namespace PoolExpansion

variable (expansion : PoolExpansion family)

theorem orbitMultiplicity_le_bound (input : ProfileInput call)
    (large : N8Source.normThreshold c call.frame ≤ call.base)
    (hF : F.Realizes) (hf : family.Realizes)
    (hw : ∀ i, (family.source i).Windows) (hexp : expansion.Realizes)
    (i : Fin expansion.count) :
    ((expansion.source i).orbitMultiplicity : ℝ) ≤ N8Source.orbitBound c p := by
  cases expansion with
  | direct =>
    have h : ((family.source i).orbitMultiplicity : ℝ) ≤ 1 := by
      exact_mod_cast first_family_orbit_multiplicity_le_one hF hf i
    exact h.trans (N8Source.orbitBound_one_le c p)
  | pooled pool count index source =>
    exact pool.orbitMultiplicity_le_bound input large hF hf hw hexp.2.1
      (index i) (source i) (hexp.2.2 i)

end PoolExpansion

namespace RawLeafPacket

theorem firstLedgerExponent_eq (packet : RawLeafPacket call p) (hpacket : packet.Realizes) :
    packet.second.physical.firstLedgerExponent = packet.firstOuterExponent := by
  unfold PhysicalSource.firstLedgerExponent PhysicalSource.firstBaseExponent firstOuterExponent
  simp only [OriginalNominalGeometry.skeleton, OriginalNominalGeometry.boundary,
    N4.nominal_first_eq hpacket false, packet.nominal_opposite_eq hpacket false,
    packet.nominal_complementary_eq hpacket false, N4.nominal_tag_eq hpacket false]

end RawLeafPacket

namespace RawFamily

variable (trace : SourceTrace call p) (htrace : trace.Realizes)
variable {geometry : GeometryFamily trace.second}

include htrace in
/-- This is the literal raw index weight, with neither a second first
divisor payment nor an independently chosen reference source. -/
theorem outerArithmeticWeight_le (input : ProfileInput call)
    (large : N8Source.normThreshold c call.frame ≤ call.base)
    (hgeometry : geometry.Realizes) (raw : RawFamily geometry) (hraw : raw.Realizes)
    (j : Fin raw.count) :
    (raw.packet j).outerArithmeticWeight ≤
      N8Source.outerConstant c p * call.base ^ (2 * N8Source.columnExponent c * p.tilt) *
        raw.indexWeight j := by
  let packet := raw.packet j
  let i := raw.sourceIndex j
  have hpacket : packet.Realizes := raw.packet_realizes trace htrace hgeometry hraw j
  have hledger : packet.second.physical.outerWeight *
        call.base ^ packet.second.physical.firstLedgerExponent ≤
      orbitalFieldFactor K * call.base ^ (2 * N8Source.columnExponent c * p.tilt) *
        trace.expansion.indexPrefactor i * packet.second.physical.firstCommonFactor := by
    change (trace.second.source i).physical.outerWeight *
      call.base ^ (trace.second.source i).physical.firstLedgerExponent ≤
        orbitalFieldFactor K * call.base ^ (2 * N8Source.columnExponent c * p.tilt) *
          trace.expansion.indexPrefactor i * (trace.second.source i).physical.firstCommonFactor
    rw [htrace.second.physical i]
    exact trace.expansion.first_ledger_le input large htrace.first htrace.cauchy
      htrace.expansion i
  have hfiber : (packet.second.stage.fiber : ℝ) ≤ N8Source.orbitBound c p := by
    change ((trace.second.source i).stage.fiber : ℝ) ≤ _
    rw [(htrace.second.stage i).fiber, htrace.second.physical i]
    exact trace.expansion.orbitMultiplicity_le_bound input large htrace.first htrace.cauchy
      htrace.firstWindows htrace.expansion i
  have hmajorant : 0 ≤ orbitalFieldFactor K *
      call.base ^ (2 * N8Source.columnExponent c * p.tilt) *
      trace.expansion.indexPrefactor i * packet.second.physical.firstCommonFactor :=
    mul_nonneg (mul_nonneg (mul_nonneg (orbitalFieldFactor_nonneg K)
      (Real.rpow_nonneg call.base_pos.le _)) (trace.expansion.indexPrefactor_nonneg i))
      packet.second.physical.firstCommonFactor_nonneg
  have hboth := mul_le_mul hledger hfiber (Nat.cast_nonneg _) hmajorant
  have htail : 0 ≤ ‖(UniqueFactorizationMonoid.moebius packet.allocation.1.val : ℂ)‖ /
      (Ideal.absNorm (commonRadical packet.key.1.val.1 packet.key.1.val.2) : ℝ) /
      (Ideal.absNorm packet.allocation.1.val : ℝ) := by positivity
  have h := mul_le_mul_of_nonneg_right hboth htail
  have hexp := packet.firstLedgerExponent_eq hpacket
  rw [hexp] at h
  calc
    _ = ((packet.second.physical.outerWeight * call.base ^ packet.firstOuterExponent) *
        (packet.second.stage.fiber : ℝ)) *
        (‖(UniqueFactorizationMonoid.moebius packet.allocation.1.val : ℂ)‖ /
          (Ideal.absNorm (commonRadical packet.key.1.val.1 packet.key.1.val.2) : ℝ) /
          (Ideal.absNorm packet.allocation.1.val : ℝ)) := by
      change packet.outerArithmeticWeight = _
      unfold RawLeafPacket.outerArithmeticWeight
      rw [packet.leaf_weight_eq]
      ring
    _ ≤ _ := h
    _ = _ := by
      unfold N8Source.outerConstant PhysicalSource.firstCommonFactor
        RawFamily.indexWeight RawFamily.commonIndexFactor
      dsimp only [i, packet, RawFamily.innerDivisor]
      ring

end RawFamily
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.PoolExpansion.orbitMultiplicity_le_bound
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawFamily.outerArithmeticWeight_le
