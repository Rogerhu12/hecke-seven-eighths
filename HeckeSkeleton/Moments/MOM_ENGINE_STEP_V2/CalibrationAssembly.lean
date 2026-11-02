import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.CalibrationConstruction
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.CalibrationSupport
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.OriginalFixedThetaClosure

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The calibrated canonical source

The arithmetic input consists of the original single-ideal and
single-prime identities. The actual paid coefficient zeros recover the
restored carrier, and the actual allocation gives its quotient support.
All tests, finite rows and numerical costs are constructed here.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.CalibrationAssembly

open EngineStep EngineInduction EngineInduction.Source
open NumberField IsDedekindDomain DedekindZetaZeroFree
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
variable {packet : RawLeafPacket call p}
variable (seed : OrdinarySeed packet) (input : ProfileInput call)
variable (support : seed.ordinary.PassiveSupport input)
variable (canonical : seed.CanonicalSupport input support)
variable (masks : seed.ResidualMaskIdentity)
variable (side : Bool) (a : support.labels side) (rectangle : Bool)
variable (moving : OriginalMovingFactors (Arithmetic.data c)
  (probeData K c) (momentRowCharacters K c))
variable (correction : HeckeCharacter K)
variable (hcorr : correction = 1 ∨ correction ∈ call.node.data.theta)
variable (sector : HeckeGeneral.Analysis.NonzeroIdeal K →
  SixthUnitClasses K ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K))))
variable (remaining : HeckeGeneral.Analysis.NonzeroIdeal K)

local notation "s" => seed.canonicalSource input support side a rectangle
local notation "d" => CalibrationConstruction.data seed input support side a rectangle
  moving correction hcorr sector remaining

theorem mask_fixed (ξ : EngineParameter) (u I : HeckeGeneral.Analysis.NonzeroIdeal K)
    (h : maskValue (d ξ) u I.val ≠ 0) : IsCoprime I.val (Arithmetic.data c).cS := by
  have hout : HeckeGeneral.Analysis.SquarefreeAmplification.sexticIdealOutsideS K
      ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K))) I := by
    by_contra hn
    change (if ((decide (HeckeGeneral.Analysis.SquarefreeAmplification.sexticIdealOutsideS K
        ((Arithmetic.data c).Sf : Set (HeightOneSpectrum (𝓞 K))) I ∧
          IsCoprime I.val u.val) && decide (IsCoprime I.val moving.support.val)) &&
        decide (IsCoprime I.val remaining.val)) then (1 : ℂ) else 0) ≠ 0 at h
    simp [hn] at h
  exact (CanonicalOriginalPhaseCalibration.outside_iff_coprime I).mp hout

theorem principal_in_theta (ξ : EngineParameter)
    (u : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hp : (d ξ).plainBackground * (d ξ).rowCharacter u = 1) :
    (d ξ).rowCharacter u ∈ (d ξ).theta := by
  apply OriginalFixedThetaClosure.principal_in_theta (d ξ) _ _ u hp
  · change (1 : HeckeCharacter K) ∈ call.node.data.theta
    rw [call.source.source.theta_eq]
    exact Expansion.Project.one_mem_canonicalDetectorTheta K (targetCharacter K c)
  · intro hf
    change targetCharacter K c ∈ call.node.data.theta ∧
      (targetCharacter K c)⁻¹ ∈ call.node.data.theta
    rw [call.source.source.theta_eq]
    simp [Expansion.Project.canonicalDetectorTheta, hf]

theorem slot_in_theta (ξ : EngineParameter) (i : Fin (d ξ).geometry.slotCount) :
    (d ξ).slotCoefficient i ∈ (d ξ).theta := by
  change call.node.data.slotCoefficient
    (CalibrationConstruction.index seed input support side a i) ∈ call.node.data.theta
  rw [call.source.source.theta_eq]
  exact call.source.source.slot_characters _

variable (atoms : ∀ ξ (h : seed.ordinary.rows.live),
  (((s).characters h).restrictSlots (s).allocation.keep).Calibration
    (σ := Arithmetic.embedding c) (d ξ) rfl
    ((s).row h).momentIdeal ((s).extractedFactor h) ((s).row h).element)

include masks atoms in
theorem plain_gates (ξ : EngineParameter) (h : seed.ordinary.rows.live)
    (I : HeckeGeneral.Analysis.NonzeroIdeal K)
    (hv : heckeIdealCoefficient K ((d ξ).plainBackground *
      (d ξ).rowCharacter ((s).row h).momentIdeal) I *
      maskValue (d ξ) ((s).row h).momentIdeal I.val ≠ 0) :
    IsCoprime I.val (Arithmetic.data c).cS ∧
      IsCoprime I.val packet.second.physical.first.paidSupport.val := by
  refine ⟨mask_fixed seed input support side a rectangle moving correction hcorr sector
    remaining ξ _ I (right_ne_zero_of_mul hv), ?_⟩
  by_contra hn
  have hz := masks.paid_plain_zero side I hn
  rw [(atoms ξ h).plain I] at hv
  change sourcePlainCoefficient
    (seed.phases.characters true (seed.slotIndex side)).plain
    (seed.phases.characters true (seed.slotIndex side)).plainTwist
    (seed.phases.characters true (seed.slotIndex side)).mask I *
      actualIdealResidue (A := Arithmetic.data c) (σ := Arithmetic.embedding c) I.val
        ((s).extractedFactor h) *
      actualIdealResidue (A := Arithmetic.data c) (σ := Arithmetic.embedding c) I.val
        ((s).row h).element ≠ 0 at hv
  rw [hz, zero_mul, zero_mul] at hv
  exact hv rfl

include masks atoms in
theorem prime_gates (ξ : EngineParameter) (h : seed.ordinary.rows.live)
    (i : Fin (d ξ).geometry.slotCount) (q : HeightOneSpectrum (𝓞 K))
    (hv : primeCoefficient K ((d ξ).rowCharacter ((s).row h).momentIdeal *
      (d ξ).slotCoefficient i) q * maskValue (d ξ) ((s).row h).momentIdeal q.asIdeal ≠ 0) :
    IsCoprime q.asIdeal (Arithmetic.data c).cS ∧
      IsCoprime q.asIdeal packet.second.physical.first.paidSupport.val := by
  refine ⟨mask_fixed seed input support side a rectangle moving correction hcorr sector
    remaining ξ _ (CanonicalOriginalPhaseCalibration.primeIdeal q)
      (right_ne_zero_of_mul hv), ?_⟩
  by_contra hn
  let j := SlotRestriction.index (s).allocation.keep i
  have hz := masks.paid_prime_zero side j q hn
  rw [(atoms ξ h).slot i q] at hv
  change sourcePrimeCoefficient
    ((seed.phases.characters true (seed.slotIndex side)).slot j)
    ((seed.phases.characters true (seed.slotIndex side)).slotTwist j)
    (seed.phases.characters true (seed.slotIndex side)).mask q *
      actualIdealResidue (A := Arithmetic.data c) (σ := Arithmetic.embedding c) q.asIdeal
        ((s).extractedFactor h) *
      actualIdealResidue (A := Arithmetic.data c) (σ := Arithmetic.embedding c) q.asIdeal
        ((s).row h).element ≠ 0 at hv
  rw [hz, zero_mul, zero_mul] at hv
  exact hv rfl

include canonical masks atoms in
theorem left_support (ξ : EngineParameter) (h : seed.ordinary.rows.live) :
    EffectivePlainSupport (d ξ) (d ξ).plainTest₁ ((s).row h).momentIdeal
      ((s).scale₁ / idealNorm K ((s).allocation.plainDivisor 0)) 0
      (s).allocation.childPlain₁ := by
  intro I hv
  have hp := right_ne_zero_of_mul (left_ne_zero_of_mul hv)
  have hg := plain_gates seed input support masks side a rectangle moving correction hcorr
    sector remaining atoms ξ h I
    (mul_ne_zero (left_ne_zero_of_mul (left_ne_zero_of_mul hv)) (right_ne_zero_of_mul hv))
  change (seed.plainProfile input side rectangle false).formula.value ξ
    (idealNorm K I / (seed.occurrences.plainScale side rectangle false /
      idealNorm K ((s).allocation.plainDivisor 0))) ≠ 0 at hp
  rw [← canonical.plain side rectangle false] at hp
  have hs := (support.scale_eq side rectangle false).trans
    (seed.plain_scales side rectangle false)
  rw [← hs] at hp
  exact CalibrationSupport.mem_childPlain_of_value_ne_zero (support.side side)
    packet.second.physical.first.paidSupport seed.ordinary.passiveMask a rectangle false
    ξ I hp hg.1 hg.2

include canonical masks atoms in
theorem right_support (ξ : EngineParameter) (h : seed.ordinary.rows.live) :
    EffectivePlainSupport (d ξ) (d ξ).plainTest₂ ((s).row h).momentIdeal
      ((s).scale₂ / idealNorm K ((s).allocation.plainDivisor (Fin.succ 0))) 0
      (s).allocation.childPlain₂ := by
  intro I hv
  have hp := right_ne_zero_of_mul (left_ne_zero_of_mul hv)
  have hg := plain_gates seed input support masks side a rectangle moving correction hcorr
    sector remaining atoms ξ h I
    (mul_ne_zero (left_ne_zero_of_mul (left_ne_zero_of_mul hv)) (right_ne_zero_of_mul hv))
  change (seed.plainProfile input side rectangle true).formula.value ξ
    (idealNorm K I / (seed.occurrences.plainScale side rectangle true /
      idealNorm K ((s).allocation.plainDivisor (Fin.succ 0)))) ≠ 0 at hp
  rw [← canonical.plain side rectangle true] at hp
  have hs := (support.scale_eq side rectangle true).trans
    (seed.plain_scales side rectangle true)
  rw [← hs] at hp
  exact CalibrationSupport.mem_childPlain_of_value_ne_zero (support.side side)
    packet.second.physical.first.paidSupport seed.ordinary.passiveMask a rectangle true
    ξ I hp hg.1 hg.2

include canonical masks atoms in
theorem slot_support (ξ : EngineParameter) (h : seed.ordinary.rows.live)
    (i : Fin (d ξ).geometry.slotCount) :
    EffectivePrimeSupport (d ξ) i ((s).row h).momentIdeal (s).base 0
      ((s).allocation.childSlots i) := by
  intro q hv
  have hp := right_ne_zero_of_mul (left_ne_zero_of_mul hv)
  have hg := prime_gates seed input support masks side a rectangle moving correction hcorr
    sector remaining atoms ξ h i q
    (mul_ne_zero (left_ne_zero_of_mul (left_ne_zero_of_mul hv)) (right_ne_zero_of_mul hv))
  let j := SlotRestriction.index (s).allocation.keep i
  change (seed.primeProfile input side j).formula.value ξ
    ((Ideal.absNorm q.asIdeal : ℝ) /
      call.base ^ (call.node.data.geometry.slots (seed.slotIndex side j)).length) ≠ 0 at hp
  rw [← canonical.prime side j, ← canonical.slots side] at hp
  exact CalibrationSupport.mem_childSlot_of_value_ne_zero (support.side side)
    packet.second.physical.first.paidSupport seed.ordinary.passiveMask a i ξ q hp hg.1 hg.2

variable (parameters : RealParameters)
variable (left_scale : (s).base ^ parameters.n₁ =
  (s).scale₁ / idealNorm K ((s).allocation.plainDivisor 0))
variable (right_scale : (s).base ^ parameters.n₂ =
  (s).scale₂ / idealNorm K ((s).allocation.plainDivisor (Fin.succ 0)))
variable (slot_sum : parameters.z = ∑ i, (s).childLength i)
variable (cutoff : ∀ h ∈ (s).rows, (Arithmetic.data c).exteriorNorm ((s).originalIdeal h) ≤
  (s).normFactor h * (s).base ^ (parameters.m + parameters.q))
variable (ordinary : ∀ h ∈ (s).rows, (d 0).rowCharacter ((s).row h).momentIdeal ∉ call.node.data.theta)

def calibration : (s).Calibration (σ := Arithmetic.embedding c)
    c.family.omega (targetCharacter K c) where
  data := d
  parameters := parameters
  height _ := 0
  count _ := rfl
  lengths _ _ := rfl
  left_scale := left_scale
  right_scale := right_scale
  slot_sum := slot_sum
  dictionary := atoms
  left_support ξ h _ := by
    rw [left_scale]
    exact left_support seed input support canonical masks side a rectangle moving correction
      hcorr sector remaining atoms ξ h
  right_support ξ h _ := by
    rw [right_scale]
    exact right_support seed input support canonical masks side a rectangle moving correction
      hcorr sector remaining atoms ξ h
  slot_support ξ h _ i := slot_support seed input support canonical masks side a rectangle
    moving correction hcorr sector remaining atoms ξ h i
  left_profile ξ h _ I _ := by
    rw [left_scale]
    exact CalibrationConstruction.left_profile seed input support side a rectangle ξ h I
  right_profile ξ h _ I _ := by
    rw [right_scale]
    exact CalibrationConstruction.right_profile seed input support side a rectangle ξ h I
  slot_profile ξ h _ i q _ :=
    CalibrationConstruction.slot_profile seed input support side a rectangle ξ h i q
  allowed ξ h hh := Finset.mem_image.mpr ⟨h, hh, rfl⟩
  cutoff := cutoff
  nonexceptional ξ h hh := by
    split
    · intro hp
      exact ordinary h hh (principal_in_theta seed input support side a rectangle
        moving correction hcorr sector remaining ξ _ hp)
    · exact ordinary h hh
  rowBound := SourceCost.row s
  rowBound_nonneg := SourceCost.row_nonneg s
  row_bound := SourceCost.row_bound s
  scalarBound := SourceCost.scalar s
  scalarBound_nonneg := SourceCost.scalar_nonneg s
  scalar_bound := SourceCost.scalar_bound s
  fiberBound := SourceCost.fiber s
  fibers := SourceCost.fiber_bound s
  principal_in_theta := principal_in_theta seed input support side a rectangle
    moving correction hcorr sector remaining
  slot_in_theta := slot_in_theta seed input support side a rectangle
    moving correction hcorr sector remaining

variable (kappa : parameters.κ = call.node.parameters.κ)

def original : OriginalCalibration call s where
  calibration := calibration seed input support canonical masks side a rectangle moving
    correction hcorr sector remaining atoms parameters left_scale right_scale slot_sum cutoff ordinary
  recipe := CalibrationConstruction.recipe seed input support side a rectangle moving
    correction hcorr sector remaining
  normProfiles := CalibrationConstruction.normProfiles seed input support side a rectangle
    moving correction hcorr sector remaining
  base_eq := rfl
  kappa_eq := kappa
  plain_background _ := rfl
  originalSlots := CalibrationConstruction.originalSlots seed input support side a rectangle
  theta_eq _ := rfl
  slot_characters := slot_in_theta seed input support side a rectangle moving correction hcorr
    sector remaining
  row_cost := rfl
  scalar_cost := rfl
  fiber_cost := rfl

def dictionary :
    (original seed input support canonical masks side a rectangle moving correction hcorr sector
      remaining atoms parameters left_scale right_scale slot_sum cutoff ordinary kappa).RawDictionary
        input CalibrationConstruction.shape 1 call.window :=
  CalibrationConstruction.dictionary seed input support side a rectangle moving correction hcorr
    sector remaining

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.CalibrationAssembly

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.CalibrationAssembly.calibration
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.CalibrationAssembly.original
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.CalibrationAssembly.dictionary
