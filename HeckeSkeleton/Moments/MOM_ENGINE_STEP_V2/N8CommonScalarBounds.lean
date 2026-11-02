import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.N8FrozenProfileBounds
import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.OriginalPhaseData
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.ActualCommonAtomBinding

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Actual common scalar bounds with their complete frozen ideals

The original occurrence witnesses determine the exterior ideals used
in the denominator.  Each source atom is bounded before any finite
sum.  The pool factor and the original two-tilt scale are retained
literally in the external scalar bound.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep EngineInduction.Source
open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments HeckeGeneral.ThetaSkeleton.Global
open HeckePort.Moments HeckePort.Moments.Support

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {K : Type} [Field K] [NumberField K]

namespace N8CommonScalar

variable {A : SArithmeticData K} {σ : K →+* ℂ}
variable {η : RayClassCharacter K A.modulus} {hS : A.ContainsTraceBadPlaces}
variable {k : ℕ} {S₁ S₂ : Finset (Ideal (𝓞 K))}
variable {S : Fin k → Finset (HeightOneSpectrum (𝓞 K))}
variable {P : Finset (Ideal (𝓞 K))}
variable {b : SupportCartesianBranch S₁ S₂ S P}
variable {T : FixedChildCharacters K k} {Z : ℝ} {length : Fin k → ℝ}
variable {w : Fin k → HeightOneSpectrum (𝓞 K) → ℂ}

theorem envelope_le_budget (bounds : b.CommonAtomBounds T Z length w)
    (budget : ℝ) (cap : ℕ) (hbudget : 1 ≤ budget) (hcap : k ≤ cap)
    (hatom : ∀ i, bounds.annulus i * bounds.profile i ≤ budget) :
    (bounds.atoms (A := A) (σ := σ) ({()} : Finset Unit)).envelope ≤ budget ^ cap := by
  have hcount : (Finset.univ \ b.keep).card ≤ cap :=
    (Finset.card_le_card (Finset.sdiff_subset :
      Finset.univ \ b.keep ⊆ (Finset.univ : Finset (Fin k)))).trans
      (by simpa using hcap)
  calc
    _ ≤ ∏ _i ∈ Finset.univ \ b.keep, budget :=
      Finset.prod_le_prod
        (fun i _ => mul_nonneg (bounds.annulus_nonneg i) (bounds.profile_nonneg i))
        (fun i _ => hatom i)
    _ = budget ^ (Finset.univ \ b.keep).card := by simp
    _ ≤ budget ^ cap := pow_le_pow_right₀ hbudget hcount

theorem bareCommonScalar_sq_le (bounds : b.CommonAtomBounds T Z length w)
    (C : A.GeneralArithmeticContext σ η hS) (I : A.Exterior)
    (hI : frozenSourceIdeal b.plainDivisor₁ b.plainDivisor₂ b.keep b.witness.2 = I.val)
    (budget : ℝ) (cap : ℕ) (hbudget : 1 ≤ budget) (hcap : k ≤ cap)
    (hatom : ∀ i, bounds.annulus i * bounds.profile i ≤ budget) :
    ‖b.bareCommonScalar T Z length w‖ ^ 2 ≤ budget ^ cap / (Ideal.absNorm I.val : ℝ) := by
  let rows : Finset Unit := {()}
  have h := (bounds.atoms (A := A) (σ := σ) rows).norm_sq_le C ()
    (Finset.mem_singleton_self ())
  have hv := bounds.atoms_value (A := A) (σ := σ) rows I
    (b.frozenSourceIdeal_eq.symm.trans hI) ()
  have hi : (bounds.atoms (A := A) (σ := σ) rows).ideal = I.val := hI
  rw [hv, hi] at h
  exact h.trans (div_le_div_of_nonneg_right
    (envelope_le_budget bounds budget cap hbudget hcap hatom) (Nat.cast_nonneg _))

theorem norm_le_sqrt_of_sq_le (z : ℂ) (bound : ℝ) (h : ‖z‖ ^ 2 ≤ bound) :
    ‖z‖ ≤ Real.sqrt bound := by
  simpa only [Real.sqrt_sq (norm_nonneg z)] using Real.sqrt_le_sqrt h

end N8CommonScalar

variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

namespace OriginalPhaseData

variable {packet : RawLeafPacket call p} (P : OriginalPhaseData packet)

theorem characters_mask_zero_or_one (paid : Bool) {k : ℕ}
    (index : Fin k → Fin call.localizedData.geometry.slotCount) (I : Ideal (𝓞 K)) :
    (P.characters paid index).mask I = 0 ∨ (P.characters paid index).mask I = 1 := by
  change (if IsCoprime I (P.mask paid).val then (1 : ℂ) else 0) = 0 ∨
    (if IsCoprime I (P.mask paid).val then (1 : ℂ) else 0) = 1
  split_ifs <;> simp

end OriginalPhaseData

namespace ProfileInput

variable (input : ProfileInput call)

theorem amplitude_le_frozenAmplitude : input.amplitude ≤ input.frozenAmplitude := by
  simpa only [frozenAmplitude, mul_one] using
    mul_le_mul_of_nonneg_left (le_max_left 1 (call.prepared.lower / 2)⁻¹)
      (zero_le_one.trans input.amplitude_one_le)

theorem commonAnnulus_nonneg : 0 ≤ 2 * call.prepared.upper := by
  have hu := call.prepared.lower_pos.trans_le call.prepared.interval
  positivity

theorem original_slot_window
    (i : Fin call.localizedData.geometry.slotCount) (q : HeightOneSpectrum (𝓞 K))
    (hq : q ∈ call.workingRaw.exteriorSlots i) :
    ((Ideal.absNorm q.asIdeal : ℝ) / call.base ^ call.originalLength i) ∈ call.window := by
  have hq' := (Finset.mem_filter.mp hq).1
  have hprofile := ((call.node.data.geometry.slots i).support_spec 0
    (call.base ^ (call.node.data.geometry.slots i).length) q).mp hq'
  have hrep : input.raw.primeRep i 0
      ((Ideal.absNorm q.asIdeal : ℝ) / call.base ^ call.originalLength i) ≠ 0 := by
    simpa only [input.raw.prime_eq] using hprofile
  exact input.raw.prime_support i 0 (Set.mem_univ _) hrep

end ProfileInput

namespace Call

theorem originalCharacters_mask_zero_or_one (call : Call c) (I : Ideal (𝓞 K)) :
    call.originalCharacters.mask I = 0 ∨ call.originalCharacters.mask I = 1 := by
  change (if IsCoprime I call.localizedSource.source.recipe.arithmeticMask.val
    then (1 : ℂ) else 0) = 0 ∨
    (if IsCoprime I call.localizedSource.source.recipe.arithmeticMask.val
    then (1 : ℂ) else 0) = 1
  split_ifs <;> simp

theorem originalPlainScale_pos (call : Call c) (rectangle plain : Bool) :
    0 < call.originalPlainScale rectangle plain := by
  unfold originalPlainScale
  split_ifs <;> exact Real.rpow_pos_of_pos call.base_pos _

end Call

namespace RawLeafPacket

variable (packet : RawLeafPacket call p)

def firstFrozenExterior (side : Bool) : (Arithmetic.data c).Exterior :=
  extractedExterior
    (call.workingRaw.columnExterior
      (call.workingRaw.originalIndex (packet.firstBranch side).witness))
    packet.second.physical.first.fullDeletion

theorem firstFrozenExterior_val (side : Bool) :
    frozenSourceIdeal (packet.firstBranch side).plainDivisor₁
      (packet.firstBranch side).plainDivisor₂ (packet.firstBranch side).keep
      (packet.firstBranch side).witness.2 = (packet.firstFrozenExterior side).val := by
  change _ = supportExtract
    (call.workingRaw.columnExterior
      (call.workingRaw.originalIndex (packet.firstBranch side).witness)).val
    packet.second.physical.first.fullDeletion
  rw [call.workingRaw.originalIndex_ideal_product (packet.firstBranch side).witness
    ((packet.firstBranch side).original_subset (packet.firstBranch side).witness_mem)]
  exact (packet.firstBranch side).frozenSourceIdeal_eq.trans
    ((packet.firstBranch side).extract_ideal _ (packet.firstBranch side).witness_mem).symm

theorem first_witness_slot (side : Bool) (i : Fin call.localizedData.geometry.slotCount) :
    (packet.firstBranch side).witness.2 i ∈ call.workingRaw.exteriorSlots i :=
  (Finset.mem_filter.mp ((packet.firstBranch side).witness_slots i)).1

def firstCommonAtomBounds (input : ProfileInput call) (horders : (0, 0) ∈ input.orders)
    (side : Bool) :
    (packet.firstBranch side).CommonAtomBounds call.originalCharacters call.base
      call.originalLength call.originalSlotWeight where
  base_pos := call.base_pos
  annulus _ := 2 * call.prepared.upper
  profile _ := input.frozenAmplitude ^ 2
  annulus_nonneg _ := input.commonAnnulus_nonneg
  profile_nonneg _ := sq_nonneg _
  plain₁ := OriginalProfileAtomBounds.sourcePlainCoefficient_norm_le_one _ _ _ _
    (call.originalCharacters_mask_zero_or_one _)
  plain₂ := OriginalProfileAtomBounds.sourcePlainCoefficient_norm_le_one _ _ _ _
    (call.originalCharacters_mask_zero_or_one _)
  prime _ _ := OriginalProfileAtomBounds.sourcePrimeCoefficient_norm_le_one _ _ _ _
    (call.originalCharacters_mask_zero_or_one _)
  prime_annulus i _ :=
    (div_le_iff₀ (Real.rpow_pos_of_pos call.base_pos _)).mp
      (input.original_slot_window i _ (packet.first_witness_slot side i)).2
  slot i _ :=
    pow_le_pow_left₀ (norm_nonneg _)
      ((input.original_prime_norm_le horders i _).trans input.amplitude_le_frozenAmplitude) 2

theorem firstCommonScalar_sq_le (input : ProfileInput call)
    (horders : (0, 0) ∈ input.orders) (side : Bool) :
    ‖packet.firstCommonScalar side‖ ^ 2 ≤
      input.frozenAtomBudget ^ c.geometry.slots /
        (Ideal.absNorm (packet.firstFrozenExterior side).val : ℝ) := by
  exact N8CommonScalar.bareCommonScalar_sq_le (packet.firstCommonAtomBounds input horders side)
    (Arithmetic.context c) (packet.firstFrozenExterior side)
    (packet.firstFrozenExterior_val side) input.frozenAtomBudget c.geometry.slots
    input.frozenAtomBudget_one call.slots_le (fun _ => le_max_right _ _)

theorem firstCommonScalar_norm_le (input : ProfileInput call)
    (horders : (0, 0) ∈ input.orders) (side : Bool) :
    ‖packet.firstCommonScalar side‖ ≤
      Real.sqrt (input.frozenAtomBudget ^ c.geometry.slots /
        (Ideal.absNorm (packet.firstFrozenExterior side).val : ℝ)) :=
  N8CommonScalar.norm_le_sqrt_of_sq_le _ _ (packet.firstCommonScalar_sq_le input horders side)

private theorem firstPlainScale_pos (side rectangle plain : Bool) :
    0 < packet.firstPlainScale side rectangle plain :=
  div_pos (call.originalPlainScale_pos rectangle plain) (idealNorm_pos K _)

private theorem firstScaleProduct_pos (side : Bool) : 0 < packet.firstScaleProduct side :=
  mul_pos (mul_pos (packet.firstPlainScale_pos side false false)
    (packet.firstPlainScale_pos side false true))
    (Finset.prod_pos (fun _ _ => Real.rpow_pos_of_pos call.base_pos _))

theorem poolScalar_norm_le :
    ‖packet.poolScalar‖ ≤
      (Arithmetic.data c).exteriorNorm packet.second.physical.first.poolPower ^ p.tilt := by
  have hp := (Arithmetic.data c).exteriorNorm_pos packet.second.physical.first.poolPower
  rw [poolScalar, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hp _)]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (actualIdealResidue_norm_le_one (Arithmetic.context c) _ _)
    (Real.rpow_nonneg hp.le _)

theorem firstExternalScalar_norm_le (input : ProfileInput call)
    (horders : (0, 0) ∈ input.orders) (side : Bool) :
    ‖packet.firstExternalScalar side‖ ≤
      Real.sqrt (input.frozenAtomBudget ^ c.geometry.slots /
        (Ideal.absNorm (packet.firstFrozenExterior side).val : ℝ)) *
      ((Arithmetic.data c).exteriorNorm packet.second.physical.first.poolPower ^ p.tilt) *
      (packet.firstScaleProduct side ^ (-1 + 2 * p.tilt)) := by
  rw [firstExternalScalar, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos (packet.firstScaleProduct_pos side) _)]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul (packet.firstCommonScalar_norm_le input horders side)
      packet.poolScalar_norm_le (norm_nonneg _) (Real.sqrt_nonneg _))
    (Real.rpow_nonneg (packet.firstScaleProduct_pos side).le _)

end RawLeafPacket
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.firstCommonScalar_sq_le
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.firstExternalScalar_norm_le
