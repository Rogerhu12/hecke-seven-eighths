import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SourceCartesianCover
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.DirectOriginalData

/-!
# The original direct source has the actual common-support cover

This is the same original occurrence partition used for amplified main
sources, constructed without any prime-pool data. Labels and residual
Cartesian dictionaries follow from the original column atlas alone.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckePort.Moments HeckePort.Moments.Support HeckePort.IdealMobiusDivisorSum

variable {K : Type} [Field K] [NumberField K] {A : SArithmeticData K}
variable {ι κ : Type*}

private theorem directCover_mem_classical_filter_iff {α : Type*} {p : α → Prop}
    [h : DecidablePred p] {s : Finset α} {i : α} :
    i ∈ @Finset.filter α p (fun x => Classical.propDecidable (p x)) s ↔ i ∈ s.filter p :=
  (@Finset.mem_filter α p (fun x => Classical.propDecidable (p x)) s i).trans
    (@Finset.mem_filter α p h s i).symm


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

def sourceCartesianCover (c : ι → ℂ) :
    SourceCartesianCover (d.directSource c).columns (d.directSource c).ideal where
  Label := SupportCartesian.ExtractionKey K T.slotCount
  labels := T.labels S D
  label := T.reindex.supportExtractionLabel S
  maps i hi := by
    apply Finset.mem_image_of_mem
    have hi' : i ∈ d.columns := hi
    rw [hcolumns] at hi'
    exact hi'
  branch a := by
    let B : SourceCartesianAtlas
        ((d.directSource c).columns.filter
          (fun i => T.reindex.supportExtractionLabel S i = a.val))
        (d.directSource c).ideal := by
      have hc : (d.directSource c).columns.filter
          (fun i => T.reindex.supportExtractionLabel S i = a.val) =
          T.commonFibre S D a := by
        change d.columns.filter _ = _
        rw [hcolumns]
        rfl
      rw [hc]
      apply SourceCartesianAtlas.ofReindex
        (T.residualReindex S D d.ideal (fun i _ => hideal i) a)
      obtain ⟨i, hi, ha⟩ := Finset.mem_image.mp a.property
      exact ⟨i, Finset.mem_filter.mpr ⟨hi, ha⟩⟩
    exact {
      slotCount := B.slotCount
      reindex := {
        plain₁ := B.reindex.plain₁
        plain₂ := B.reindex.plain₂
        slots := B.reindex.slots
        index := B.reindex.index
        maps := fun x hx => directCover_mem_classical_filter_iff.mpr (B.reindex.maps x hx)
        injective := B.reindex.injective
        surjective := fun i hi =>
          B.reindex.surjective i (directCover_mem_classical_filter_iff.mp hi)
        ideal_product := B.reindex.ideal_product }
      plain₁_nonzero := B.plain₁_nonzero
      plain₂_nonzero := B.plain₂_nonzero }

end DirectGaussData
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.DirectGaussData.sourceCartesianCover
