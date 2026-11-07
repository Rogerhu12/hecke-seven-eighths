module

public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.PassiveSourceOrigin
public import HeckeSkeleton.Moments.MOM_ENGINE_STEP_V2.PassiveEnergy

@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Exact paid phases for a complete restored column

Both plain gates and every prime-occurrence gate multiply to the
coprimality mask of the same whole column ideal.  On the original
smooth carrier its fixed and paid gates are already present.  The
original coefficient is therefore the paid coefficient times exactly
the residual deletion, before a Fourier sum or a norm is taken.
-/

noncomputable section
open scoped Classical BigOperators NumberField nonZeroDivisors

namespace HeckeSkeleton.Moments.EngineStepV2.Blueprint.PassiveColumnBridge

open EngineStep NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.Analysis.ConditionalMoments
open HeckeGeneral.ThetaSkeleton.Global
open CanonicalOriginalPhaseCalibration (originalCoprimeMask)

attribute [local instance]
  sourcePrincipal sourceNormOneSpace sourceNormOneBorel
  Expansion.ActualProbeContext.localCompletionSpace
  Expansion.ActualProbeContext.localCompletionBorel
  Expansion.ActualProbeContext.allLocalMeasures_isAddHaar

variable {K : Type} [Field K] [NumberField K]
variable {c : TargetContext K} {call : Call c} {p : SourceParameters c}
variable {packet : RawLeafPacket call p} (P : OriginalPhaseData packet)
variable {k : ℕ} (index : Fin k → Fin call.localizedData.geometry.slotCount)

private theorem carrier_plain_nonzero (B : PassiveAllocation.Carrier K k)
    (i : AllocationColumn K k) (hi : i ∈ PassiveAllocation.carrierColumns B) :
    i.1.1 ≠ 0 ∧ i.1.2 ≠ 0 := by
  obtain ⟨hp, _⟩ := Finset.mem_product.mp hi
  obtain ⟨hl, hr⟩ := Finset.mem_product.mp hp
  obtain ⟨I, _, hI⟩ := Finset.mem_image.mp hl
  obtain ⟨J, _, hJ⟩ := Finset.mem_image.mp hr
  exact ⟨hI ▸ nonZeroDivisors.coe_ne_zero I, hJ ▸ nonZeroDivisors.coe_ne_zero J⟩

/-- This monoid identity retains every repeated prime occurrence.
No squarefreeness or pairwise-distinctness premise is required. -/
theorem column_mask (M : HeckeGeneral.Analysis.NonzeroIdeal K)
    (i : AllocationColumn K k) :
    originalCoprimeMask M i.1.1 * originalCoprimeMask M i.1.2 *
        (∏ j, originalCoprimeMask M (i.2 j).asIdeal) =
      originalCoprimeMask M (PassiveAllocation.columnIdeal i) := by
  simp only [PassiveAllocation.columnIdeal, map_mul, map_prod]

/-- The full coefficient is transformed atom by atom.  The two
nonzero conditions merely exclude the artificial value assigned to
`sourceMomentIdeal 0`; every actual restored carrier supplies them. -/
theorem raw_fullDeletion
    (hpassive : (PassivePhaseBridge.poolPassiveIdeal P).val ∣ P.deletionIdeal.val)
    (g h : (Arithmetic.data c).R) (N₁ N₂ Z : ℝ) (length : Fin k → ℝ)
    (w₁ w₂ : HeckeGeneral.Analysis.NonzeroIdeal K → ℂ)
    (w : Fin k → HeightOneSpectrum (𝓞 K) → ℂ)
    (i : AllocationColumn K k) (h₁ : i.1.1 ≠ 0) (h₂ : i.1.2 ≠ 0) :
    rawSourceCoefficient (σ := Arithmetic.embedding c) (P.characters false index)
        g h N₁ N₂ Z length w₁ w₂ w i =
      rawSourceCoefficient (σ := Arithmetic.embedding c) (P.characters true index)
        g h N₁ N₂ Z length w₁ w₂ w i *
          originalCoprimeMask P.deletionIdeal (PassiveAllocation.columnIdeal i) := by
  have hleft : (sourceMomentIdeal i.1.1).val = i.1.1 := by
    simp only [sourceMomentIdeal, dif_pos h₁]
  have hright : (sourceMomentIdeal i.1.2).val = i.1.2 := by
    simp only [sourceMomentIdeal, dif_pos h₂]
  simp only [rawSourceCoefficient, FixedChildCharacters.coefficient, childCartesianCoefficient,
    PassivePhaseBridge.plain_term P index hpassive,
    PassivePhaseBridge.prime_term P index hpassive, hleft, hright,
    Finset.prod_mul_distrib]
  rw [← column_mask P.deletionIdeal i]
  ring

variable {input : ProfileInput call}

/-- The support dictionary supplies its own fixed and paid gates.
The amplifier mask certificate is derived from the actual source trace. -/
theorem raw_residual_on_carrier (O : OrdinaryData packet) (S : SmoothSideSupport input k)
    (hpacket : packet.Realizes)
    (g h : (Arithmetic.data c).R) (N₁ N₂ Z : ℝ) (length : Fin k → ℝ)
    (w₁ w₂ : HeckeGeneral.Analysis.NonzeroIdeal K → ℂ)
    (w : Fin k → HeightOneSpectrum (𝓞 K) → ℂ)
    (i : AllocationColumn K k)
    (hi : i ∈ PassiveAllocation.carrierColumns
      (S.carrier packet.second.physical.first.paidSupport)) :
    rawSourceCoefficient (σ := Arithmetic.embedding c) (P.characters false index)
        g h N₁ N₂ Z length w₁ w₂ w i =
      rawSourceCoefficient (σ := Arithmetic.embedding c) (P.characters true index)
        g h N₁ N₂ Z length w₁ w₂ w i *
          (if IsCoprime O.passiveMask (PassiveAllocation.columnIdeal i) then 1 else 0) := by
  have hn := carrier_plain_nonzero _ i hi
  rw [raw_fullDeletion P index (PassivePhaseBridge.poolPassiveIdeal_dvd_deletion P hpacket)
    g h N₁ N₂ Z length w₁ w₂ w i hn.1 hn.2]
  have hp := (S.carrierColumns_fixed_paid packet.second.physical.first.paidSupport i hi).2
  change _ * (if IsCoprime (PassiveAllocation.columnIdeal i)
    (∏ I ∈ packet.second.physical.first.fullDeletion, I) then 1 else 0) = _
  rw [O.residual_coprime_iff _ hp, isCoprime_comm]

/-- Exact restoration of the complex Fourier polynomial.  The shared
location can be the actual two-coordinate source location; no bound on
it and no Fourier integration is used here. -/
theorem polynomial_residual (O : OrdinaryData packet) (S : SmoothSideSupport input k)
    (hpacket : packet.Realizes)
    (g h : (Arithmetic.data c).R) (N₁ N₂ Z : ℝ) (length : Fin k → ℝ)
    (w₁ w₂ : HeckeGeneral.Analysis.NonzeroIdeal K → ℂ)
    (w : Fin k → HeightOneSpectrum (𝓞 K) → ℂ)
    (x : AllocationColumn K k → EngineParameter) (ξ : EngineParameter) :
    jointFourierColumn
        (PassiveAllocation.carrierColumns (S.carrier packet.second.physical.first.paidSupport))
        (rawSourceCoefficient (σ := Arithmetic.embedding c) (P.characters false index)
          g h N₁ N₂ Z length w₁ w₂ w) x ξ =
      jointFourierColumn
        ((PassiveAllocation.carrierColumns (S.carrier packet.second.physical.first.paidSupport)).filter
          (fun i => IsCoprime O.passiveMask (PassiveAllocation.columnIdeal i)))
        (rawSourceCoefficient (σ := Arithmetic.embedding c) (P.characters true index)
          g h N₁ N₂ Z length w₁ w₂ w) x ξ := by
  unfold jointFourierColumn
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  rw [raw_residual_on_carrier P index O S hpacket g h N₁ N₂ Z length w₁ w₂ w i hi]
  by_cases hm : IsCoprime O.passiveMask (PassiveAllocation.columnIdeal i) <;> simp [hm]

/-- N2's finite residual expansion follows from the original complete
coefficient, with the exact Möbius and occurrence signs. -/
theorem polynomial_expansion (O : OrdinaryData packet) (S : SmoothSideSupport input k)
    (hpacket : packet.Realizes)
    (g h : (Arithmetic.data c).R) (N₁ N₂ Z : ℝ) (length : Fin k → ℝ)
    (w₁ w₂ : HeckeGeneral.Analysis.NonzeroIdeal K → ℂ)
    (w : Fin k → HeightOneSpectrum (𝓞 K) → ℂ)
    (x : AllocationColumn K k → EngineParameter) (ξ : EngineParameter) :
    jointFourierColumn
        (PassiveAllocation.carrierColumns (S.carrier packet.second.physical.first.paidSupport))
        (rawSourceCoefficient (σ := Arithmetic.embedding c) (P.characters false index)
          g h N₁ N₂ Z length w₁ w₂ w) x ξ =
      ∑ a : PassiveAllocation.labels (S.carrier packet.second.physical.first.paidSupport)
          O.passiveMask,
        PassiveAllocation.sign a.val *
          jointFourierColumn
            (PassiveAllocation.columns (S.carrier packet.second.physical.first.paidSupport) a.val)
            (rawSourceCoefficient (σ := Arithmetic.embedding c) (P.characters true index)
              g h N₁ N₂ Z length w₁ w₂ w) x ξ := by
  rw [polynomial_residual P index O S hpacket g h N₁ N₂ Z length w₁ w₂ w x ξ]
  exact PassiveAllocation.joint_residual_expansion
    (S.carrier packet.second.physical.first.paidSupport) O.passiveMask
    (O.passiveMask_ne_zero P.deletion_nonzero) _ x ξ

end HeckeSkeleton.Moments.EngineStepV2.Blueprint.PassiveColumnBridge

#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.PassiveColumnBridge.column_mask
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.PassiveColumnBridge.raw_fullDeletion
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.PassiveColumnBridge.raw_residual_on_carrier
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.PassiveColumnBridge.polynomial_residual
#print axioms HeckeSkeleton.Moments.EngineStepV2.Blueprint.PassiveColumnBridge.polynomial_expansion
