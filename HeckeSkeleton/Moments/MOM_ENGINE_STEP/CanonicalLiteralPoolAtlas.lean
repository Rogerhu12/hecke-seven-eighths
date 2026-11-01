import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralAtlas

/-!
# Original occurrence indices in the actual pool cover

The main and valuation sources use the existing Cartesian covers. The
finite-carrier equality transports in those constructors alter only
their proof fields. The package below exposes their computed supports,
slot count and index together, so no arbitrary residual dictionary has
to be supplied when constructing the literal two-stage profiles.

On a valuation branch the original index is lifted to the actual
valuation subtype. Its value on every retained tuple is the original
occurrence reconstruction. The off-support fallback remains the one in
the existing source; no new column or source is selected.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree LocalFiniteSums
open HeckeGeneral.Arithmetic HeckeGeneral.Characters
open HeckePort.Moments HeckePort.Moments.Support

variable {K : Type} [Field K] [NumberField K] {A : SArithmeticData K}
variable {ι : Type*} {columns otherColumns : Finset ι}
variable {ideal : ι → A.Exterior}

namespace SourceCartesianAtlas

/-- The computational part of the actual atlas, packaged independently
of its source carrier. Its slot indices are retained by the sigma. -/
def literalDictionary (T : SourceCartesianAtlas columns ideal) :
    Σ n : ℕ, (Finset (Ideal (𝓞 K)) × Finset (Ideal (𝓞 K))) ×
      (Fin n → Finset (HeightOneSpectrum (𝓞 K))) ×
        (AllocationColumn K n → ι) :=
  ⟨T.slotCount, (T.reindex.plain₁, T.reindex.plain₂), T.reindex.slots, T.reindex.index⟩

private theorem literalDictionary_cast (h : columns = otherColumns)
    (e : SourceCartesianAtlas columns ideal = SourceCartesianAtlas otherColumns ideal)
    (T : SourceCartesianAtlas columns ideal) :
    (cast e T).literalDictionary = T.literalDictionary := by
  cases h
  rfl

end SourceCartesianAtlas

variable {σ : K →+* ℂ} {η : RayClassCharacter K A.modulus}
variable {htrace : A.ContainsTraceBadPlaces}
variable {C : A.GeneralArithmeticContext σ η htrace}
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
variable (c : ι → ℂ)

/-- The existing main cover carries precisely the retained original
plain and prime occurrences and the actual reconstruction index. -/
theorem mainAtlasForLabel_literalDictionary (a : T.labels S D) :
    (d.mainAtlasForLabel T S D hcolumns hideal c a).literalDictionary =
      ⟨(T.branch S D a).keep.card,
        (SupportCartesian.plainResidual T.reindex.plain₁ S
            (T.branch S D a).plainExtract₁,
          SupportCartesian.plainResidual T.reindex.plain₂ S
            (T.branch S D a).plainExtract₂),
        (fun j => SupportCartesian.primeLive
          (T.reindex.slots (SlotRestriction.index (T.branch S D a).keep j)) S),
        (fun i => T.reindex.index ((T.branch S D a).reconstruct i))⟩ := by
  unfold mainAtlasForLabel
  simp only [eqRec_eq_cast]
  rw [SourceCartesianAtlas.literalDictionary_cast
    (congrArg (fun t : Finset ι => t.filter
      (fun i => T.reindex.supportExtractionLabel S i = a.val)) hcolumns).symm]
  dsimp only [SourceCartesianAtlas.literalDictionary, SourceCartesianAtlas.ofReindex]
  rw [T.residualReindex_plain₁, T.residualReindex_plain₂,
    T.residualReindex_slots, T.residualReindex_index]

/-- This is the identical package at the public whole-main cover. -/
theorem mainSourceCartesianCover_literalDictionary (a : T.labels S D) :
    ((d.mainSourceCartesianCover T S D hcolumns hideal c).branch a).literalDictionary =
      ⟨(T.branch S D a).keep.card,
        (SupportCartesian.plainResidual T.reindex.plain₁ S
            (T.branch S D a).plainExtract₁,
          SupportCartesian.plainResidual T.reindex.plain₂ S
            (T.branch S D a).plainExtract₂),
        (fun j => SupportCartesian.primeLive
          (T.reindex.slots (SlotRestriction.index (T.branch S D a).keep j)) S),
        (fun i => T.reindex.index ((T.branch S D a).reconstruct i))⟩ :=
  d.mainAtlasForLabel_literalDictionary T S D hcolumns hideal c a

variable (p : ExteriorPrime A) (n : ℕ)

/-- The actual valuation source lifts its retained tuple into the
original valuation subtype. On the real carrier its value is exact. -/
theorem residualSource_original_support_index_val
    (b : SupportCartesianBranch T.reindex.plain₁ T.reindex.plain₂ T.reindex.slots
      (S ∪ {p.val.asIdeal}))
    (hw : T.reindex.index b.witness ∈ d.valuationColumns p n)
    (i : AllocationColumn K b.keep.card) (hi : i ∈ b.residualColumns) :
    ((d.residualSource_cartesianBranch_of_original_support
      T S D hcolumns hideal p n c b hw).index i).val =
        T.reindex.index (b.reconstruct i) := by
  change ((T.reindex.supportResidualBranch (S ∪ {p.val.asIdeal}) b).subtypeIndex
    (d.valuationColumns p n)
    (d.combinedBranch_subset_valuation T S D hcolumns hideal p n b hw)
    ⟨T.reindex.index b.witness,
      Finset.mem_image.mpr ⟨b.witness, b.witness_mem, rfl⟩⟩ i).val = _
  exact (T.reindex.supportResidualBranch (S ∪ {p.val.asIdeal}) b).subtypeIndex_val
    (d.valuationColumns p n)
    (d.combinedBranch_subset_valuation T S D hcolumns hideal p n b hw)
    ⟨T.reindex.index b.witness,
      Finset.mem_image.mpr ⟨b.witness, b.witness_mem, rfl⟩⟩ i hi

/-- The existing combined-support cover has the actual retained
occurrences. The displayed subtype index is the original constructor,
including its harmless off-carrier default. -/
theorem combinedAtlasForLabel_literalDictionary
    (a : d.combinedLabels T S p n) :
    let b := d.combinedBranchForLabel T S D hcolumns p n a
    let hb := (d.combinedBranchForLabel_spec T S D hcolumns p n a).2
    (d.combinedAtlasForLabel T S D hcolumns hideal p n c a).literalDictionary =
      ⟨b.keep.card,
        (SupportCartesian.plainResidual T.reindex.plain₁ (S ∪ {p.val.asIdeal})
            b.plainExtract₁,
          SupportCartesian.plainResidual T.reindex.plain₂ (S ∪ {p.val.asIdeal})
            b.plainExtract₂),
        (fun j => SupportCartesian.primeLive
          (T.reindex.slots (SlotRestriction.index b.keep j)) (S ∪ {p.val.asIdeal})),
        (d.residualSource_cartesianBranch_of_original_support
          T S D hcolumns hideal p n c b hb).index⟩ := by
  let b := d.combinedBranchForLabel T S D hcolumns p n a
  have hb := d.combinedBranchForLabel_spec T S D hcolumns p n a
  have he := d.residualSource_branch_filter_of_original_support T S D hcolumns p n b
  rw [hb.1] at he
  dsimp only
  unfold combinedAtlasForLabel
  simp only [eqRec_eq_cast]
  rw [SourceCartesianAtlas.literalDictionary_cast he]
  rfl

/-- Both the actual first common support and the pool valuation are
kept in the cover key, before any continuous Fourier parameter. -/
theorem residualSourceCartesianCover_literalDictionary
    (a : d.combinedLabels T S p n) :
    let b := d.combinedBranchForLabel T S D hcolumns p n a
    let hb := (d.combinedBranchForLabel_spec T S D hcolumns p n a).2
    ((d.residualSourceCartesianCover T S D hcolumns hideal p n c).branch a)
        .literalDictionary =
      ⟨b.keep.card,
        (SupportCartesian.plainResidual T.reindex.plain₁ (S ∪ {p.val.asIdeal})
            b.plainExtract₁,
          SupportCartesian.plainResidual T.reindex.plain₂ (S ∪ {p.val.asIdeal})
            b.plainExtract₂),
        (fun j => SupportCartesian.primeLive
          (T.reindex.slots (SlotRestriction.index b.keep j)) (S ∪ {p.val.asIdeal})),
        (d.residualSource_cartesianBranch_of_original_support
          T S D hcolumns hideal p n c b hb).index⟩ :=
  d.combinedAtlasForLabel_literalDictionary T S D hcolumns hideal c p n a

end FirstGaussPoolData
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.FirstGaussPoolData.mainAtlasForLabel_literalDictionary
#print axioms HeckeSkeleton.Moments.EngineStep.FirstGaussPoolData.residualSource_original_support_index_val
#print axioms HeckeSkeleton.Moments.EngineStep.FirstGaussPoolData.combinedAtlasForLabel_literalDictionary
