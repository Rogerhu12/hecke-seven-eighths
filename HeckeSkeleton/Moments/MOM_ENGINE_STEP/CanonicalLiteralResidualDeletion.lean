import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralAtlasAtoms
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralDeletion

/-!
# The full first deletion is one on the original residual carrier

Every original support prime is removed by the actual occurrence
reconstruction, including the passive primes absent from the first
fixed phase. Thus adding the complete original support mask does not
alter any original residual column. This is a consequence of the
individual ideal recipe, before summation or taking a norm.

The corresponding ideal remains the genuine `literalDeletionIdeal`;
its norm is charged by `literalDeletionIdeal_norm_le`, not discarded.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckePort.Moments HeckePort.Moments.Support
open CanonicalOriginalPhaseCalibration

variable {K : Type} [Field K] [NumberField K]

namespace SupportCartesianBranch

variable {k : ℕ} {S₁ S₂ : Finset (Ideal (𝓞 K))}
variable {slots : Fin k → Finset (HeightOneSpectrum (𝓞 K))}
variable {support : Finset (Ideal (𝓞 K))}
variable (b : SupportCartesianBranch S₁ S₂ slots support)

/-- Exact residualization proves avoidance of the complete original
support, not only the active sextic prime set. -/
theorem residual_whole_avoids (hprime : ∀ p ∈ support, Prime p)
    (i : AllocationColumn K b.keep.card) (hi : i ∈ b.residualColumns) :
    CanonicalLiteralSupport.Avoids (allocationColumnIdeal i) support := by
  have he := b.residual_ideal (b.reconstruct i) (b.reconstruct_mem i hi)
  rw [b.residual_reconstruct i hi] at he
  rw [← he]
  exact CanonicalLiteralSupport.residual_avoids _ support hprime

theorem residual_full_mask_one (hprime : ∀ p ∈ support, Prime p)
    (i : AllocationColumn K b.keep.card) (hi : i ∈ b.residualColumns) :
    originalCoprimeMask (literalDeletionIdeal support hprime) (allocationColumnIdeal i) = 1 := by
  have hc := (literalDeletionIdeal_coprime support hprime _).mpr
    (b.residual_whole_avoids hprime i hi)
  change (if IsCoprime (allocationColumnIdeal i)
    (literalDeletionIdeal support hprime).val then 1 else 0) = 1
  exact if_pos hc

variable {A : SArithmeticData K} {ι : Type*}
variable {columns : Finset ι} {ideal : ι → A.Exterior}
variable (T : SourceCartesianAtlas columns ideal)

/-- The actual existing atlas has the same mask value. Its occurrence
transport preserves the complete product ideal exactly. -/
theorem atlas_full_mask_one (hprime : ∀ p ∈ support, Prime p)
    (index : AllocationColumn K b.keep.card → ι)
    (e : T.literalDictionary =
      ⟨b.keep.card,
        (SupportCartesian.plainResidual S₁ support b.plainExtract₁,
          SupportCartesian.plainResidual S₂ support b.plainExtract₂),
        (fun j => SupportCartesian.primeLive
          (slots (SlotRestriction.index b.keep j)) support), index⟩)
    (i : AllocationColumn K T.slotCount) (hi : i ∈ T.reindex.cartesian) :
    originalCoprimeMask (literalDeletionIdeal support hprime) (allocationColumnIdeal i) = 1 := by
  have he := b.residual_full_mask_one hprime
    (CanonicalLiteralAtlasAtoms.castColumn (congrArg Sigma.fst e) i)
    ((CanonicalLiteralAtlasAtoms.dictionary_membership e i).mp hi)
  simpa only [CanonicalLiteralAtlasAtoms.castColumn_ideal] using he

end SupportCartesianBranch
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.SupportCartesianBranch.atlas_full_mask_one
