import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SourceCartesianCover
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DirectSourceCover

/-!
# Original support covers inherit the original slot cap

The main, valuation-residual and direct cover constructors transport
the original residual Cartesian dictionary across an exact equality
of column supports.  Such a transport does not change its slot count.
The retained set is a subset of the original `Fin slotCount`, so all
three actual constructors inherit the same earlier cap.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckePort.Moments HeckePort.Moments.Support HeckePort.IdealMobiusDivisorSum

variable {K : Type} [Field K] [NumberField K] {A : SArithmeticData K}
variable {ι : Type*}

namespace SourceCartesianAtlas

theorem slotCount_cast_columns {S T : Finset ι} {ideal : ι → A.Exterior}
    (h : S = T) (a : SourceCartesianAtlas S ideal) :
    (cast (congrArg (fun cols => SourceCartesianAtlas cols ideal) h) a).slotCount =
      a.slotCount := by
  cases h
  rfl

private theorem slotCount_cast {S T : Finset ι} {ideal : ι → A.Exterior}
    (h : S = T) (e : SourceCartesianAtlas S ideal = SourceCartesianAtlas T ideal)
    (a : SourceCartesianAtlas S ideal) :
    (cast e a).slotCount = a.slotCount := by
  cases h
  rfl

end SourceCartesianAtlas

variable {σ : K →+* ℂ} {η : RayClassCharacter K A.modulus}
variable {hS : A.ContainsTraceBadPlaces} {C : A.GeneralArithmeticContext σ η hS}
variable {bad : Finset (HeightOneSpectrum (𝓞 K))} {Z ell eps : ℝ}
variable {P : PowerScaleExteriorPool A bad Z ell eps}
variable {originalColumns : Finset ι} {originalIdeal : ι → A.Exterior}

namespace FirstGaussPoolData

variable (d : FirstGaussPoolData C P ι)
variable (T : SourceCartesianAtlas originalColumns originalIdeal)
variable (S : Finset (Ideal (𝓞 K))) (D : Ideal (𝓞 K))
variable (hcolumns : d.columns =
  originalColumns.filter (fun i => supportExtract (originalIdeal i).val S = D))
variable (hideal : ∀ i, (d.ideal i).val = supportResidual (originalIdeal i).val S)

theorem mainAtlasForLabel_slotCount (c : ι → ℂ) (a : T.labels S D) :
    (d.mainAtlasForLabel T S D hcolumns hideal c a).slotCount =
      (T.branch S D a).keep.card := by
  unfold mainAtlasForLabel
  simp only [eqRec_eq_cast]
  rw [SourceCartesianAtlas.slotCount_cast
    (congrArg (fun t : Finset ι => t.filter
      (fun i => T.reindex.supportExtractionLabel S i = a.val)) hcolumns).symm]
  rfl

theorem mainSourceCartesianCover_slotCount_le (c : ι → ℂ)
    (a : (d.mainSourceCartesianCover T S D hcolumns hideal c).labels) :
    ((d.mainSourceCartesianCover T S D hcolumns hideal c).branch a).slotCount ≤
      T.slotCount := by
  rw [show ((d.mainSourceCartesianCover T S D hcolumns hideal c).branch a).slotCount =
      (T.branch S D a).keep.card from d.mainAtlasForLabel_slotCount T S D hcolumns hideal c a]
  simpa only [Fintype.card_fin] using (Finset.card_le_univ (T.branch S D a).keep)

theorem combinedAtlasForLabel_slotCount (p : ExteriorPrime A) (n : ℕ) (c : ι → ℂ)
    (a : d.combinedLabels T S p n) :
    (d.combinedAtlasForLabel T S D hcolumns hideal p n c a).slotCount =
      (d.combinedBranchForLabel T S D hcolumns p n a).keep.card := by
  let b := d.combinedBranchForLabel T S D hcolumns p n a
  have hb := d.combinedBranchForLabel_spec T S D hcolumns p n a
  have hcols := d.residualSource_branch_filter_of_original_support T S D hcolumns p n b
  rw [hb.1] at hcols
  unfold combinedAtlasForLabel
  simp only [eqRec_eq_cast]
  rw [SourceCartesianAtlas.slotCount_cast hcols]
  rfl

theorem residualSourceCartesianCover_slotCount_le (p : ExteriorPrime A) (n : ℕ) (c : ι → ℂ)
    (a : (d.residualSourceCartesianCover T S D hcolumns hideal p n c).labels) :
    ((d.residualSourceCartesianCover T S D hcolumns hideal p n c).branch a).slotCount ≤
      T.slotCount := by
  rw [show ((d.residualSourceCartesianCover T S D hcolumns hideal p n c).branch a).slotCount =
      (d.combinedBranchForLabel T S D hcolumns p n a).keep.card from
    d.combinedAtlasForLabel_slotCount T S D hcolumns hideal p n c a]
  simpa only [Fintype.card_fin] using
    (Finset.card_le_univ (d.combinedBranchForLabel T S D hcolumns p n a).keep)

end FirstGaussPoolData

namespace DirectGaussData

variable (d : DirectGaussData C ι)
variable (T : SourceCartesianAtlas originalColumns originalIdeal)
variable (S : Finset (Ideal (𝓞 K))) (D : Ideal (𝓞 K))
variable (hcolumns : d.columns =
  originalColumns.filter (fun i => supportExtract (originalIdeal i).val S = D))
variable (hideal : ∀ i, (d.ideal i).val = supportResidual (originalIdeal i).val S)

theorem sourceCartesianCover_slotCount (c : ι → ℂ)
    (a : (d.sourceCartesianCover T S D hcolumns hideal c).labels) :
    ((d.sourceCartesianCover T S D hcolumns hideal c).branch a).slotCount =
      (T.branch S D a).keep.card := by
  have hcols : (d.directSource c).columns.filter
      (fun i => T.reindex.supportExtractionLabel S i = a.val) = T.commonFibre S D a := by
    change d.columns.filter _ = _
    rw [hcolumns]
    dsimp only [SourceCartesianAtlas.commonFibre, SourceCartesianAtlas.commonColumns]
    exact @Finset.filter_congr_decidable _ _ _ _ _
  dsimp only [sourceCartesianCover]
  simp only [eqRec_eq_cast]
  rw [SourceCartesianAtlas.slotCount_cast hcols.symm]
  rfl

theorem sourceCartesianCover_slotCount_le (c : ι → ℂ)
    (a : (d.sourceCartesianCover T S D hcolumns hideal c).labels) :
    ((d.sourceCartesianCover T S D hcolumns hideal c).branch a).slotCount ≤ T.slotCount := by
  rw [d.sourceCartesianCover_slotCount T S D hcolumns hideal c a]
  simpa only [Fintype.card_fin] using (Finset.card_le_univ (T.branch S D a).keep)

end DirectGaussData
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.FirstGaussPoolData.mainSourceCartesianCover_slotCount_le
#print axioms HeckeSkeleton.Moments.EngineStep.FirstGaussPoolData.residualSourceCartesianCover_slotCount_le
#print axioms HeckeSkeleton.Moments.EngineStep.DirectGaussData.sourceCartesianCover_slotCount_le
