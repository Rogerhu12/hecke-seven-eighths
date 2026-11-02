import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.PassiveCanonicalAtoms
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.PassiveSupportRecovery

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Nonzero original atoms avoid the full second common support

The actual extraction factor contains the generator of every second
common prime with positive multiplicity. Its zero-extended residue
therefore forces every surviving plain and prime occurrence to avoid
that support, before any child calibration or passive allocation.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.PassiveCommonAvoidance

open EngineStep NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.Analysis.ActualSIntegerMoments
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open HeckePort.Moments HeckePort.IdealMobiusDivisorSum

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable {packet : RawLeafPacket call p}

def commonIdeal (packet : RawLeafPacket call p) : (Arithmetic.data c).Exterior :=
  primePowerProduct packet.R.primes
    (fun j => min (packet.R.leftMultiplicity j) (packet.R.rightMultiplicity j))

private theorem common_coprime (I : Ideal (𝓞 K))
    (hI : IsCoprime I (commonIdeal packet).val) :
    IsCoprime I packet.key.1.val.1 := by
  rw [← packet.block.common_left]
  change IsCoprime I (∏ j, (packet.R.primes j).val.asIdeal ^ packet.R.leftMultiplicity j)
  change IsCoprime I (∏ j, (packet.R.primes j).val.asIdeal ^
    min (packet.R.leftMultiplicity j) (packet.R.rightMultiplicity j)) at hI
  apply IsCoprime.prod_right
  intro j _
  have hj := hI.of_prod_right j (Finset.mem_univ j)
  have hm : 0 < min (packet.R.leftMultiplicity j) (packet.R.rightMultiplicity j) :=
    lt_min (packet.block.left_positive j) (packet.block.right_positive j)
  exact ((IsCoprime.pow_right_iff hm).mp hj).pow_right

private theorem original_factor (O : OrdinaryData packet) (side rectangle : Bool)
    (h : O.rows.live) :
    (O.originalSource side rectangle).extractedFactor h =
      if side then -(packet.R.factor (Arithmetic.context c) h.val)
      else packet.R.factor (Arithmetic.context c) h.val := by
  cases side <;> rfl

theorem residue_common_coprime (O : OrdinaryData packet) (side rectangle : Bool)
    (h : O.rows.live) (J : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hn : actualIdealResidue (A := Arithmetic.data c) (σ := Arithmetic.embedding c) J.val
      ((O.originalSource side rectangle).extractedFactor h *
        ((O.originalSource side rectangle).row h).element) ≠ 0) :
    IsCoprime J.val packet.key.1.val.1 := by
  have hpositive : actualIdealResidue (A := Arithmetic.data c) (σ := Arithmetic.embedding c)
      J.val (packet.R.factor (Arithmetic.context c) h.val *
        ((O.originalSource side rectangle).row h).element) ≠ 0 := by
    rw [original_factor] at hn
    cases side
    · exact hn
    · simpa only [if_true, neg_mul, CanonicalOriginalPhaseCalibration.residue_neg] using hn
  apply common_coprime
  apply PassiveSupportRecovery.residue_mul_nonzero_coprime (probeData K c)
    (momentRowCharacters K c) rfl rfl (commonIdeal packet)
    (primePowerProductGenerator (Arithmetic.context c) packet.R.primes
      (fun j => min (packet.R.leftMultiplicity j) (packet.R.rightMultiplicity j)))
    (nonunitFrequencyGenerator (Arithmetic.context c) packet.R.primes
      packet.R.leftMultiplicity packet.R.rightMultiplicity (packet.R.frequency h.val) *
        ((O.originalSource side rectangle).row h).element)
    (primePowerProduct_generates (Arithmetic.context c) packet.R.primes _) J
  simpa only [ActualSecondCorrelationRows.factor, mul_assoc] using hpositive

theorem plainTerm_common_coprime (O : OrdinaryData packet) (side rectangle : Bool)
    (h : O.rows.live) (χ θ : HeckeCharacter K) (mask : Ideal (𝓞 K) →* ℂ)
    (w : HeckeGeneral.Analysis.NonzeroIdeal K → ℂ) (N : ℝ)
    (J : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hn : sourcePlainTerm (σ := Arithmetic.embedding c) χ θ mask
      ((O.originalSource side rectangle).extractedFactor h)
      ((O.originalSource side rectangle).row h).element w N J ≠ 0) :
    IsCoprime J.val packet.key.1.val.1 := by
  apply residue_common_coprime O side rectangle h J
  intro hz
  exact hn (by simp only [sourcePlainTerm, hz, mul_zero, zero_mul])

theorem primeTerm_common_coprime (O : OrdinaryData packet) (side rectangle : Bool)
    (h : O.rows.live) (χ θ : HeckeCharacter K) (mask : Ideal (𝓞 K) →* ℂ)
    (w : HeightOneSpectrum (𝓞 K) → ℂ) (N : ℝ) (q : HeightOneSpectrum (𝓞 K))
    (hn : sourcePrimeTerm (σ := Arithmetic.embedding c) χ θ mask
      ((O.originalSource side rectangle).extractedFactor h)
      ((O.originalSource side rectangle).row h).element w N q ≠ 0) :
    IsCoprime q.asIdeal packet.key.1.val.1 := by
  apply residue_common_coprime O side rectangle h
    (CanonicalOriginalPhaseCalibration.primeIdeal q)
  intro hz
  change actualIdealResidue (A := Arithmetic.data c) (σ := Arithmetic.embedding c) q.asIdeal
    ((O.originalSource side rectangle).extractedFactor h *
      ((O.originalSource side rectangle).row h).element) = 0 at hz
  exact hn (by simp only [sourcePrimeTerm, hz, mul_zero, zero_mul])

theorem raw_common_coprime {k : ℕ} (O : OrdinaryData packet) (side rectangle : Bool)
    (h : O.rows.live) (T : FixedChildCharacters K k) (N₁ N₂ Z : ℝ)
    (length : Fin k → ℝ) (w₁ w₂ : HeckeGeneral.Analysis.NonzeroIdeal K → ℂ)
    (w : Fin k → HeightOneSpectrum (𝓞 K) → ℂ) (i : AllocationColumn K k)
    (hleft : i.1.1 ≠ 0) (hright : i.1.2 ≠ 0)
    (hn : rawSourceCoefficient (σ := Arithmetic.embedding c) T
      ((O.originalSource side rectangle).extractedFactor h)
      ((O.originalSource side rectangle).row h).element
      N₁ N₂ Z length w₁ w₂ w i ≠ 0) :
    IsCoprime i.1.1 packet.key.1.val.1 ∧
      IsCoprime i.1.2 packet.key.1.val.1 ∧
      ∀ j, IsCoprime (i.2 j).asIdeal packet.key.1.val.1 := by
  simp only [rawSourceCoefficient, FixedChildCharacters.coefficient,
    childCartesianCoefficient] at hn
  have hl := plainTerm_common_coprime O side rectangle h T.plain T.plainTwist T.mask
    w₁ N₁ (sourceMomentIdeal i.1.1) (left_ne_zero_of_mul (left_ne_zero_of_mul hn))
  have hr := plainTerm_common_coprime O side rectangle h T.plain T.plainTwist T.mask
    w₂ N₂ (sourceMomentIdeal i.1.2) (right_ne_zero_of_mul (left_ne_zero_of_mul hn))
  have hlval : (sourceMomentIdeal i.1.1).val = i.1.1 := by
    simp only [sourceMomentIdeal, dif_pos hleft]
  have hrval : (sourceMomentIdeal i.1.2).val = i.1.2 := by
    simp only [sourceMomentIdeal, dif_pos hright]
  rw [hlval] at hl
  rw [hrval] at hr
  refine ⟨hl, hr, fun j => ?_⟩
  exact primeTerm_common_coprime O side rectangle h (T.slot j) (T.slotTwist j) T.mask
    (w j) (Z ^ length j) (i.2 j)
      ((Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul hn)) j (Finset.mem_univ j))

/-- Positivity is already part of the actual common-block constructor;
the statement therefore needs no added source-trace hypothesis. -/
theorem canonicalCoefficient_common_coprime (seed : OrdinarySeed packet)
    (input : ProfileInput call) (paid side rectangle : Bool) (h : seed.ordinary.rows.live)
    (i : AllocationColumn K (seed.ordinary.residualSlotCount side))
    (hleft : i.1.1 ≠ 0) (hright : i.1.2 ≠ 0)
    (hn : seed.canonicalCoefficient input paid side rectangle h i ≠ 0) :
    IsCoprime i.1.1 packet.key.1.val.1 ∧
      IsCoprime i.1.2 packet.key.1.val.1 ∧
      ∀ j, IsCoprime (i.2 j).asIdeal packet.key.1.val.1 :=
  raw_common_coprime seed.ordinary side false h _ _ _ _ _ _ _ _ i hleft hright hn

theorem common_prime (I : Ideal (𝓞 K))
    (hI : IsCoprime I packet.key.1.val.1) (P : Ideal (𝓞 K))
    (hP : P ∈ primeSupport packet.key.1.val.1) : IsCoprime I P := by
  have hn : packet.key.1.val.1 ≠ 0 := by
    rw [← packet.block.common_left]
    exact (primePowerProduct packet.R.primes packet.R.leftMultiplicity).property.1
  exact (coprime_support_iff I packet.key.1.val.1 hn).mp hI P hP

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.PassiveCommonAvoidance

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.PassiveCommonAvoidance.residue_common_coprime
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.PassiveCommonAvoidance.raw_common_coprime
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.PassiveCommonAvoidance.canonicalCoefficient_common_coprime

