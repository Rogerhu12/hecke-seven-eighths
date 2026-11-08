module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.OrdinaryRawAtomData
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.OrdinaryOriginalCoordinates
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.OrdinaryOriginalTerms
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.OrdinaryNormProfile
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.OrdinaryPhaseCoefficients

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The first extracted original atom formula

The literal original rectangle is extracted along the actual first
support branch. The two norm tilts are distributed over those same
original occurrences, and the actual first, pool and inverse-unit
residues are absorbed into their original characters. Each comparison
rectangle is treated separately, with the absent comparison kept zero.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint

open EngineStep
open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open HeckePort.Moments HeckePort.Moments.Support

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}

namespace OrdinaryAtomTable

theorem term_eq_gate {k : ℕ} (d : OrdinaryAtomTable (K := K) k)
    (r : Bool) (i : AllocationColumn K k) :
    d.term r i = if r && !d.centered then 0 else
      d.normalizer * rawBareSourceCoefficient d.characters
        (d.scale₁ r) (d.scale₂ r) d.base d.length
        (d.leftWeight r) (d.rightWeight r) d.slotWeight i := by
  cases r <;> cases hc : d.centered <;> simp [term_false, term_true, hc]

end OrdinaryAtomTable

namespace OrdinaryFirstAtomFormula

theorem characters_bare_cast {packet : RawLeafPacket call p}
    (phases : OriginalPhaseData packet) {m n : ℕ} (hc : m = n)
    (index : Fin m → Fin call.localizedData.geometry.slotCount)
    (N₁ N₂ Z : ℝ)
    (length : Fin call.localizedData.geometry.slotCount → ℝ)
    (w₁ w₂ : HeckeGeneral.Analysis.NonzeroIdeal K → ℂ)
    (w : Fin call.localizedData.geometry.slotCount → HeightOneSpectrum (𝓞 K) → ℂ)
    (x : AllocationColumn K n) :
    rawBareSourceCoefficient
        (phases.characters false (fun j => index (Fin.cast hc.symm j)))
        N₁ N₂ Z (fun j => length (index (Fin.cast hc.symm j))) w₁ w₂
        (fun j => w (index (Fin.cast hc.symm j))) x =
      rawBareSourceCoefficient (phases.characters false index)
        N₁ N₂ Z (fun j => length (index j)) w₁ w₂ (fun j => w (index j))
        (cast (congrArg (AllocationColumn K) hc.symm) x) := by
  subst n
  rfl

theorem residual_plain_nonzero {k : ℕ}
    {S₁ S₂ : Finset (Ideal (𝓞 K))}
    {S : Fin k → Finset (HeightOneSpectrum (𝓞 K))}
    {P : Finset (Ideal (𝓞 K))} (b : SupportCartesianBranch S₁ S₂ S P)
    (x : AllocationColumn K b.keep.card) (hx : x ∈ b.residualColumns) :
    x.1.1 ≠ 0 ∧ x.1.2 ≠ 0 := by
  have hp := Finset.mem_product.mp (Finset.mem_product.mp hx).1
  constructor
  · obtain ⟨I, _, he⟩ := Finset.mem_image.mp hp.1
    exact he ▸ supportResidual_ne_zero I P
  · obtain ⟨I, _, he⟩ := Finset.mem_image.mp hp.2
    exact he ▸ supportResidual_ne_zero I P

end OrdinaryFirstAtomFormula

namespace RawLeafPacket

variable (packet : RawLeafPacket call p)

def firstPlainWeight (side rectangle plain : Bool)
    (I : HeckeGeneral.Analysis.NonzeroIdeal K) : ℂ :=
  (if plain then call.localizedNormProfiles.right PUnit.unit 0
   else call.localizedNormProfiles.left PUnit.unit 0)
    (idealNorm K I / packet.firstPlainScale side rectangle plain)

/-- The unnormalized profiles on the retained first occurrences,
with an explicitly specified complete character dictionary. -/
def firstRetainedBare (side rectangle : Bool)
    (T : FixedChildCharacters K (packet.firstBranch side).keep.card)
    (x : AllocationColumn K (packet.firstBranch side).keep.card) : ℂ :=
  rawBareSourceCoefficient T
    (packet.firstPlainScale side rectangle false)
    (packet.firstPlainScale side rectangle true)
    call.base (fun j => call.originalLength (SlotRestriction.index (packet.firstBranch side).keep j))
    (packet.firstPlainWeight side rectangle false)
    (packet.firstPlainWeight side rectangle true)
    (fun j => call.originalSlotWeight (SlotRestriction.index (packet.firstBranch side).keep j)) x

/-- The same actual occurrences after the two norm powers have been
put into their single-variable profiles. -/
def firstPhasedBare (phases : OriginalPhaseData packet) (side rectangle : Bool)
    (x : AllocationColumn K (packet.firstBranch side).keep.card) : ℂ :=
  rawBareSourceCoefficient
    (phases.characters false (SlotRestriction.index (packet.firstBranch side).keep))
    (packet.firstPlainScale side rectangle false)
    (packet.firstPlainScale side rectangle true)
    call.base (fun j => call.originalLength (SlotRestriction.index (packet.firstBranch side).keep j))
    (fun I => packet.normProfile false
      (idealNorm K I / packet.firstPlainScale side rectangle false))
    (fun I => packet.normProfile true
      (idealNorm K I / packet.firstPlainScale side rectangle true))
    (fun j q =>
      let original := SlotRestriction.index (packet.firstBranch side).keep j
      call.originalSlotWeight original q *
        ((((Ideal.absNorm q.asIdeal : ℝ) / call.base ^ call.originalLength original) ^
          (-1 + 2 * p.tilt) : ℝ) : ℂ)) x

theorem originalBareRectangle_first_extract (side rectangle : Bool)
    (x : AllocationColumn K (packet.firstBranch side).keep.card)
    (hx : x ∈ (packet.firstBranch side).residualColumns) :
    call.originalBareRectangle rectangle ((packet.firstBranch side).reconstruct x) =
      packet.firstCommonScalar side * packet.firstRetainedBare side rectangle
        (call.originalCharacters.restrictSlots (packet.firstBranch side).keep) x := by
  have hscale (plain : Bool) : 0 < call.originalPlainScale rectangle plain := by
    unfold Call.originalPlainScale
    split_ifs <;> exact Real.rpow_pos_of_pos call.base_pos _
  have hleft :
      (fun I => call.originalPlainWeight rectangle false
        ((packet.firstBranch side).plainDivisor₁ * I)) =
      packet.firstPlainWeight side rectangle false := by
    funext I
    change call.localizedNormProfiles.left PUnit.unit 0
        (idealNorm K ((packet.firstBranch side).plainDivisor₁ * I) /
          call.originalPlainScale rectangle false) =
      call.localizedNormProfiles.left PUnit.unit 0
        (idealNorm K I / (call.originalPlainScale rectangle false /
          idealNorm K (packet.firstBranch side).plainDivisor₁))
    rw [original_norm_quotient _ I _ (hscale false)]
  have hright :
      (fun I => call.originalPlainWeight rectangle true
        ((packet.firstBranch side).plainDivisor₂ * I)) =
      packet.firstPlainWeight side rectangle true := by
    funext I
    change call.localizedNormProfiles.right PUnit.unit 0
        (idealNorm K ((packet.firstBranch side).plainDivisor₂ * I) /
          call.originalPlainScale rectangle true) =
      call.localizedNormProfiles.right PUnit.unit 0
        (idealNorm K I / (call.originalPlainScale rectangle true /
          idealNorm K (packet.firstBranch side).plainDivisor₂))
    rw [original_norm_quotient _ I _ (hscale true)]
  rw [Call.originalBareRectangle, (packet.firstBranch side).raw_bare_extract
    call.originalCharacters _ _ call.base call.originalLength
    (call.originalPlainWeight rectangle false) (call.originalPlainWeight rectangle true)
    call.originalSlotWeight x hx]
  change packet.firstCommonScalar side *
      (packet.firstBranch side).bareResidualCoefficient call.originalCharacters
        _ _ call.base call.originalLength _ _ call.originalSlotWeight x = _
  unfold SupportCartesianBranch.bareResidualCoefficient
  rw [hleft, hright]
  rfl

theorem firstPhasedBare_normalized (phases : OriginalPhaseData packet)
    (side rectangle : Bool) (x : AllocationColumn K (packet.firstBranch side).keep.card)
    (hx : x ∈ (packet.firstBranch side).residualColumns) :
    ((packet.firstScaleProduct side ^ (-1 + 2 * p.tilt) : ℝ) : ℂ) *
        packet.firstPhasedBare phases side rectangle x =
      (((Ideal.absNorm (allocationColumnIdeal x) : ℝ) ^ (-1 + 2 * p.tilt) : ℝ) : ℂ) *
        packet.firstRetainedBare side rectangle
          (phases.characters false (SlotRestriction.index (packet.firstBranch side).keep)) x := by
  have hn := OrdinaryFirstAtomFormula.residual_plain_nonzero (packet.firstBranch side) x hx
  have h := OrdinaryNormProfile.normalized_bare
    (phases.characters false (SlotRestriction.index (packet.firstBranch side).keep))
    (packet.firstPlainScale side rectangle false) (packet.firstPlainScale side rectangle true)
    call.base (fun j => call.originalLength (SlotRestriction.index (packet.firstBranch side).keep j))
    (-1 + 2 * p.tilt) (packet.firstPlainWeight side rectangle false)
    (packet.firstPlainWeight side rectangle true)
    (fun j => call.originalSlotWeight (SlotRestriction.index (packet.firstBranch side).keep j))
    x hn.1 hn.2 (packet.firstPlainScale_pos side rectangle false)
    (packet.firstPlainScale_pos side rectangle true) call.base_pos
  rw [packet.firstScaleProduct_rectangle side rectangle] at h
  exact h

theorem firstAtomTable_term_cast (hpacket : packet.Realizes)
    (phases : OriginalPhaseData packet) (side rectangle : Bool)
    (x : AllocationColumn K (packet.firstAtlas side).slotCount) :
    (packet.firstAtomTable hpacket phases side).term rectangle x =
      if rectangle && !call.node.centered then 0 else
        packet.firstPhasedBare phases side rectangle
          (cast (congrArg (AllocationColumn K) (packet.realizes_firstCount hpacket side).symm) x) := by
  rw [OrdinaryAtomTable.term_eq_gate, packet.firstAtomTable_normalizer hpacket phases, one_mul]
  change (if rectangle && !call.node.centered then 0 else _) = _
  split_ifs
  · rfl
  · exact OrdinaryFirstAtomFormula.characters_bare_cast phases
      (packet.realizes_firstCount hpacket side)
      (SlotRestriction.index (packet.firstBranch side).keep)
      (packet.firstPlainScale side rectangle false) (packet.firstPlainScale side rectangle true)
      call.base call.originalLength
      (fun I => packet.normProfile false (idealNorm K I / packet.firstPlainScale side rectangle false))
      (fun I => packet.normProfile true (idealNorm K I / packet.firstPlainScale side rectangle true))
      (fun j q => call.originalSlotWeight j q *
        ((((Ideal.absNorm q.asIdeal : ℝ) / call.base ^ call.originalLength j) ^
          (-1 + 2 * p.tilt) : ℝ) : ℂ)) x

/-- The complete original coefficient formula after the first
extraction, on the actual source occurrence tuple. -/
theorem firstAtomFormula (hpacket : packet.Realizes)
    (phases : OriginalPhaseData packet) (side rectangle : Bool)
    (x : AllocationColumn K (packet.firstAtlas side).slotCount)
    (hx : x ∈ (packet.firstAtlas side).reindex.cartesian)
    (J : (Arithmetic.data c).Exterior)
    (hJ : J.val = allocationColumnIdeal
      (cast (congrArg (AllocationColumn K) (packet.realizes_firstCount hpacket side).symm) x))
    (hdelete : IsCoprime J.val phases.deletionIdeal.val) :
    packet.firstExternalScalar side * (packet.firstAtomTable hpacket phases side).term rectangle x =
      call.originalRectangleTerm rectangle ((packet.firstBranch side).reconstruct
        (cast (congrArg (AllocationColumn K) (packet.realizes_firstCount hpacket side).symm) x)) *
      (packet.poolScalar * (((Arithmetic.data c).exteriorNorm J ^ (-1 + 2 * p.tilt) : ℝ) : ℂ) *
        actualIdealResidue (A := Arithmetic.data c) (σ := Arithmetic.embedding c)
          J.val packet.second.physical.first.firstElement *
        actualIdealResidue (A := Arithmetic.data c) (σ := Arithmetic.embedding c)
          J.val phases.poolElement *
        actualIdealResidue (A := Arithmetic.data c) (σ := Arithmetic.embedding c)
          J.val (CanonicalLiteralFixedPhases.emptyDivisorInverse (A := Arithmetic.data c))) := by
  let y := cast (congrArg (AllocationColumn K) (packet.realizes_firstCount hpacket side).symm) x
  have hy : y ∈ (packet.firstBranch side).residualColumns :=
    (packet.realizes_firstCartesian hpacket side x).mp hx
  have hnorm : (Arithmetic.data c).exteriorNorm J =
      (Ideal.absNorm (allocationColumnIdeal y) : ℝ) := by
    change (Ideal.absNorm J.val : ℝ) = _
    rw [hJ]
  have hphase := phases.characters_false_bare
    (SlotRestriction.index (packet.firstBranch side).keep)
    (packet.firstPlainScale side rectangle false) (packet.firstPlainScale side rectangle true)
    call.base (fun j => call.originalLength (SlotRestriction.index (packet.firstBranch side).keep j))
    (packet.firstPlainWeight side rectangle false) (packet.firstPlainWeight side rectangle true)
    (fun j => call.originalSlotWeight (SlotRestriction.index (packet.firstBranch side).keep j))
    y J hJ hdelete
  change packet.firstRetainedBare side rectangle
      (phases.characters false (SlotRestriction.index (packet.firstBranch side).keep)) y =
      packet.firstRetainedBare side rectangle
        (call.originalCharacters.restrictSlots (packet.firstBranch side).keep) y * _ * _ * _ at hphase
  rw [packet.firstAtomTable_term_cast hpacket phases, Call.originalRectangleTerm]
  split_ifs
  · simp only [mul_zero, zero_mul]
  · rw [packet.originalBareRectangle_first_extract side rectangle y hy]
    change (packet.firstCommonScalar side * packet.poolScalar *
        ((packet.firstScaleProduct side ^ (-1 + 2 * p.tilt) : ℝ) : ℂ)) *
        packet.firstPhasedBare phases side rectangle y = _
    rw [hnorm]
    calc
      _ = packet.firstCommonScalar side * packet.poolScalar *
          (((packet.firstScaleProduct side ^ (-1 + 2 * p.tilt) : ℝ) : ℂ) *
            packet.firstPhasedBare phases side rectangle y) := by ring
      _ = packet.firstCommonScalar side * packet.poolScalar *
          (((((Ideal.absNorm (allocationColumnIdeal y) : ℝ) ^
              (-1 + 2 * p.tilt) : ℝ) : ℂ)) *
            packet.firstRetainedBare side rectangle
              (phases.characters false (SlotRestriction.index (packet.firstBranch side).keep)) y) := by
        rw [packet.firstPhasedBare_normalized phases side rectangle y hy]
      _ = _ := by rw [hphase]; ring

end RawLeafPacket
end HeckeSkeleton.Moments.EngineStepV2.Blueprint

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.RawLeafPacket.firstAtomFormula
