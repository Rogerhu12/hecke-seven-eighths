import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.PassiveSmoothSupport
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.CalibrationFourierProfiles
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.EffectiveChildSupport

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Effective support after the actual residual allocation

An allocated plain divisor divides the corresponding occurrence of its
own witness. Consequently it preserves both the fixed and the paid
coprimality gates. Nonvanishing of the original smooth profile then
places the reconstructed ideal in the restored carrier, hence the
quotient ideal in this allocation's exact child support.
-/

noncomputable section
open scoped Classical NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.CalibrationSupport

open EngineStep NumberField IsDedekindDomain
open HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open WholeAllocation

variable {K : Type} [Field K] [NumberField K] {k : ℕ}

def plainIndex (k : ℕ) : Bool → Fin (k + 2)
  | false => 0
  | true => Fin.succ 0

def plain (B : ActualColumnAllocation K k) (side : Bool) : Finset (Ideal (𝓞 K)) :=
  if side then B.plain₂ else B.plain₁

def childPlain (B : ActualColumnAllocation K k) (side : Bool) : Finset (NonzeroIdeal K) :=
  if side then B.childPlain₂ else B.childPlain₁

def witnessPlain (B : ActualColumnAllocation K k) (side : Bool) : Ideal (𝓞 K) :=
  if side then B.witness.1.2 else B.witness.1.1

theorem witness_plain (B : ActualColumnAllocation K k) (side : Bool) :
    witnessPlain B side ∈ plain B side ∧
      (B.plainDivisor (plainIndex k side)).val ∣ witnessPlain B side := by
  have hp := Finset.mem_product.mp (Finset.mem_product.mp B.witness_mem).1
  cases side
  · exact Finset.mem_filter.mp hp.1
  · exact Finset.mem_filter.mp hp.2

theorem plainDivisor_coprime (B : ActualColumnAllocation K k) (side : Bool)
    (mask : Ideal (𝓞 K)) (gate : ∀ I ∈ plain B side, IsCoprime I mask) :
    IsCoprime (B.plainDivisor (plainIndex k side)).val mask := by
  have hw := witness_plain B side
  exact (gate _ hw.1).of_isCoprime_of_dvd_left hw.2

theorem mem_childPlain (B : ActualColumnAllocation K k) (side : Bool)
    (I : NonzeroIdeal K) :
    I ∈ childPlain B side ↔
      (B.plainDivisor (plainIndex k side) * I).val ∈ plain B side := by
  cases side
  · exact mem_nonzeroQuotientMomentSupport _ (nonZeroDivisors.coe_ne_zero _) _ I
  · exact mem_nonzeroQuotientMomentSupport _ (nonZeroDivisors.coe_ne_zero _) _ I

theorem mem_idealCarrier (S : Finset (NonzeroIdeal K)) (I : NonzeroIdeal K) :
    I.val ∈ PassiveAllocation.idealCarrier S ↔ I ∈ S := by
  constructor
  · intro h
    obtain ⟨J, hJ, he⟩ := Finset.mem_image.mp h
    exact (Subtype.ext he : J = I) ▸ hJ
  · intro h
    exact Finset.mem_image.mpr ⟨I, h, rfl⟩

variable {c : TargetContext K} {call : Call c} {input : ProfileInput call}
variable (S : SmoothSideSupport input k) (paid : (Arithmetic.data c).Exterior)
variable (mask : Ideal (𝓞 K)) (a : PassiveAllocation.labels (S.carrier paid) mask)

theorem carrier_plain_gate (side : Bool) (I : Ideal (𝓞 K))
    (hI : I ∈ plain (PassiveAllocation.allocation (S.carrier paid) mask a) side) :
    IsCoprime I (Arithmetic.data c).cS ∧ IsCoprime I paid.val := by
  have hm : I ∈ PassiveAllocation.idealCarrier (S.plainCarrier paid side) := by
    cases side <;> exact hI
  obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hm
  exact (Finset.mem_filter.mp hJ).2

theorem allocated_divisor_gates (side : Bool) :
    IsCoprime
        ((PassiveAllocation.allocation (S.carrier paid) mask a).plainDivisor
          (plainIndex k side)).val (Arithmetic.data c).cS ∧
      IsCoprime
        ((PassiveAllocation.allocation (S.carrier paid) mask a).plainDivisor
          (plainIndex k side)).val paid.val := by
  constructor
  · exact plainDivisor_coprime _ side _
      (fun I hI => (carrier_plain_gate S paid mask a side I hI).1)
  · exact plainDivisor_coprime _ side _
      (fun I hI => (carrier_plain_gate S paid mask a side I hI).2)

/-- This uses the exact quotient scale of this residual allocation.
The carrier is the union of the two original comparison supports. -/
theorem mem_childPlain_of_value_ne_zero (rectangle side : Bool)
    (ξ : EngineParameter) (I : NonzeroIdeal K)
    (hvalue : (S.plain rectangle side).formula.value ξ
      (idealNorm K I / (S.plainScale rectangle side /
        idealNorm K ((PassiveAllocation.allocation (S.carrier paid) mask a).plainDivisor
          (plainIndex k side)))) ≠ 0)
    (hfixed : IsCoprime I.val (Arithmetic.data c).cS)
    (hpaid : IsCoprime I.val paid.val) :
    I ∈ childPlain (PassiveAllocation.allocation (S.carrier paid) mask a) side := by
  rw [mem_childPlain]
  have hdiv := allocated_divisor_gates S paid mask a side
  have hprofile := hvalue
  rw [ProfileFormula.divided_scale_argument] at hprofile
  have hs := S.mem_smoothPlain_of_value_ne_zero rectangle side ξ
    ((PassiveAllocation.allocation (S.carrier paid) mask a).plainDivisor
      (plainIndex k side) * I) hprofile
  have hg :
      IsCoprime
          (((PassiveAllocation.allocation (S.carrier paid) mask a).plainDivisor
            (plainIndex k side) * I).val) (Arithmetic.data c).cS ∧
        IsCoprime
          (((PassiveAllocation.allocation (S.carrier paid) mask a).plainDivisor
            (plainIndex k side) * I).val) paid.val :=
    ⟨hdiv.1.mul_left hfixed, hdiv.2.mul_left hpaid⟩
  have hm := (mem_idealCarrier (S.plainCarrier paid side) _).mpr
    (Finset.mem_filter.mpr ⟨hs, hg⟩)
  cases side <;> exact hm

theorem mem_childSlot_of_value_ne_zero
    (i : Fin (PassiveAllocation.allocation (S.carrier paid) mask a).keep.card)
    (ξ : EngineParameter) (q : HeightOneSpectrum (𝓞 K))
    (hvalue : (S.prime
      (SlotRestriction.index (PassiveAllocation.allocation (S.carrier paid) mask a).keep i)).formula.value ξ
      ((Ideal.absNorm q.asIdeal : ℝ) / call.base ^ S.length
        (SlotRestriction.index (PassiveAllocation.allocation (S.carrier paid) mask a).keep i)) ≠ 0)
    (hfixed : IsCoprime q.asIdeal (Arithmetic.data c).cS)
    (hpaid : IsCoprime q.asIdeal paid.val) :
    q ∈ (PassiveAllocation.allocation (S.carrier paid) mask a).childSlots i := by
  exact Finset.mem_filter.mpr
    ⟨S.mem_smoothSlot_of_value_ne_zero _ ξ q hvalue, hfixed, hpaid⟩

/-- Arithmetic gates are read from the actual child's common mask.
No vanishing of the unmasked smooth function is required. -/
theorem effectivePlain
    (d : MomentData K c.family.omega (targetCharacter K c)) (W : IdealTest K)
    (u : NonzeroIdeal K) (height : ℝ) (rectangle side : Bool)
    (ξ : EngineParameter)
    (profile : ∀ x, W.profile u height x = (S.plain rectangle side).formula.value ξ x)
    (gates : ∀ I : NonzeroIdeal K, maskValue d u I.val ≠ 0 →
      IsCoprime I.val (Arithmetic.data c).cS ∧ IsCoprime I.val paid.val) :
    EffectivePlainSupport d W u
      (S.plainScale rectangle side /
        idealNorm K ((PassiveAllocation.allocation (S.carrier paid) mask a).plainDivisor
          (plainIndex k side))) height
      (childPlain (PassiveAllocation.allocation (S.carrier paid) mask a) side) := by
  intro I h
  have hv := right_ne_zero_of_mul (left_ne_zero_of_mul h)
  rw [profile] at hv
  have hg := gates I (right_ne_zero_of_mul h)
  exact mem_childPlain_of_value_ne_zero S paid mask a rectangle side ξ I hv hg.1 hg.2

/-- The logarithmic Fourier phase has unit norm, so the same actual
support proof applies to the constructed global Fourier profile. -/
theorem effectiveLogPlain
    (d : MomentData K c.family.omega (targetCharacter K c)) (W : IdealTest K)
    (u : NonzeroIdeal K) (height : ℝ) (rectangle side : Bool)
    (ξ : EngineParameter) (direction : ℝ × ℝ) (originalScale : ℝ)
    (profile : ∀ x, W.profile u height x =
      ((S.plain rectangle side).formula.atScale direction originalScale).value ξ x)
    (gates : ∀ I : NonzeroIdeal K, maskValue d u I.val ≠ 0 →
      IsCoprime I.val (Arithmetic.data c).cS ∧ IsCoprime I.val paid.val) :
    EffectivePlainSupport d W u
      (S.plainScale rectangle side /
        idealNorm K ((PassiveAllocation.allocation (S.carrier paid) mask a).plainDivisor
          (plainIndex k side))) height
      (childPlain (PassiveAllocation.allocation (S.carrier paid) mask a) side) := by
  intro I h
  have hv := right_ne_zero_of_mul (left_ne_zero_of_mul h)
  rw [profile] at hv
  have hz := ProfileFormula.value_zero_ne_zero_of_atScale _ direction originalScale ξ _ hv
  have hg := gates I (right_ne_zero_of_mul h)
  exact mem_childPlain_of_value_ne_zero S paid mask a rectangle side 0 I hz hg.1 hg.2

theorem effectiveLogPrime
    (d : MomentData K c.family.omega (targetCharacter K c))
    (u : NonzeroIdeal K) (height : ℝ) (i : Fin d.geometry.slotCount)
    (j : Fin (PassiveAllocation.allocation (S.carrier paid) mask a).keep.card)
    (ξ : EngineParameter) (direction : ℝ × ℝ) (originalScale : ℝ)
    (length : (d.geometry.slots i).length =
      S.length (SlotRestriction.index (PassiveAllocation.allocation (S.carrier paid) mask a).keep j))
    (profile : ∀ x, (d.geometry.slots i).profile height x =
      ((S.prime (SlotRestriction.index
        (PassiveAllocation.allocation (S.carrier paid) mask a).keep j)).formula.atScale
        direction originalScale).value ξ x)
    (gates : ∀ q : HeightOneSpectrum (𝓞 K), maskValue d u q.asIdeal ≠ 0 →
      IsCoprime q.asIdeal (Arithmetic.data c).cS ∧ IsCoprime q.asIdeal paid.val) :
    EffectivePrimeSupport d i u call.base height
      ((PassiveAllocation.allocation (S.carrier paid) mask a).childSlots j) := by
  intro q h
  have hv := right_ne_zero_of_mul (left_ne_zero_of_mul h)
  rw [profile, length] at hv
  have hz := ProfileFormula.value_zero_ne_zero_of_atScale _ direction originalScale ξ _ hv
  have hg := gates q (right_ne_zero_of_mul h)
  exact mem_childSlot_of_value_ne_zero S paid mask a j 0 q hz hg.1 hg.2

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.CalibrationSupport

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.CalibrationSupport.allocated_divisor_gates
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.CalibrationSupport.mem_childPlain_of_value_ne_zero
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.CalibrationSupport.mem_childSlot_of_value_ne_zero
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.CalibrationSupport.effectivePlain
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.CalibrationSupport.effectiveLogPlain
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.CalibrationSupport.effectiveLogPrime
