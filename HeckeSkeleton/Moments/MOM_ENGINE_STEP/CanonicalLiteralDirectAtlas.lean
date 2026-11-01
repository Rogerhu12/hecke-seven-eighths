import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralAtlasAtoms
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DirectSourceCover

/-!
# Literal occurrence data of the unamplified source cover

This exposes the existing direct cover's actual index and supports.
Only the proof that its finite carrier is the common-support fibre is
transported.  The direct source and its labels are not redefined.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckePort.Moments HeckePort.Moments.Support

variable {K : Type} [Field K] [NumberField K] {A : SArithmeticData K}
variable {ι : Type*}

namespace SourceCartesianAtlas

theorem literalDictionary_cast_columns {S T : Finset ι} {ideal : ι → A.Exterior}
    (h : S = T) (a : SourceCartesianAtlas S ideal) :
    (cast (congrArg (fun cols => SourceCartesianAtlas cols ideal) h) a).literalDictionary =
      a.literalDictionary := by
  cases h
  rfl

end SourceCartesianAtlas

variable {σ : K →+* ℂ} {η : RayClassCharacter K A.modulus}
variable {hS : A.ContainsTraceBadPlaces} {C : A.GeneralArithmeticContext σ η hS}
variable {originalColumns : Finset ι} {originalIdeal : ι → A.Exterior}

namespace DirectGaussData

variable (d : DirectGaussData C ι)
variable (T : SourceCartesianAtlas originalColumns originalIdeal)
variable (S : Finset (Ideal (𝓞 K))) (D : Ideal (𝓞 K))
variable (hcolumns : d.columns =
  originalColumns.filter (fun i => supportExtract (originalIdeal i).val S = D))
variable (hideal : ∀ i, (d.ideal i).val = supportResidual (originalIdeal i).val S)

theorem sourceCartesianCover_literalDictionary (c : ι → ℂ) (a : T.labels S D) :
    ((d.sourceCartesianCover T S D hcolumns hideal c).branch a).literalDictionary =
      ⟨(T.branch S D a).keep.card,
        (SupportCartesian.plainResidual T.reindex.plain₁ S
            (T.branch S D a).plainExtract₁,
          SupportCartesian.plainResidual T.reindex.plain₂ S
            (T.branch S D a).plainExtract₂),
        (fun j => SupportCartesian.primeLive
          (T.reindex.slots (SlotRestriction.index (T.branch S D a).keep j)) S),
        (fun i => T.reindex.index ((T.branch S D a).reconstruct i))⟩ := by
  have hcols : (d.directSource c).columns.filter
      (fun i => T.reindex.supportExtractionLabel S i = a.val) = T.commonFibre S D a := by
    change d.columns.filter _ = _
    rw [hcolumns]
    rfl
  have hne : (T.commonFibre S D a).Nonempty := by
    obtain ⟨i, hi, ha⟩ := Finset.mem_image.mp a.property
    exact ⟨i, Finset.mem_filter.mpr ⟨hi, ha⟩⟩
  change (cast (congrArg (fun cols => SourceCartesianAtlas cols d.ideal) hcols.symm)
    (SourceCartesianAtlas.ofReindex
      (T.residualReindex S D d.ideal (fun i _ => hideal i) a) hne)).literalDictionary = _
  rw [SourceCartesianAtlas.literalDictionary_cast_columns]
  dsimp only [SourceCartesianAtlas.literalDictionary, SourceCartesianAtlas.ofReindex]
  rw [T.residualReindex_plain₁, T.residualReindex_plain₂,
    T.residualReindex_slots, T.residualReindex_index]

end DirectGaussData
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.DirectGaussData.sourceCartesianCover_literalDictionary
