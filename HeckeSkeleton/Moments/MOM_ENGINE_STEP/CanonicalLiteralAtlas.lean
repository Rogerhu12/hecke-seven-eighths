import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SourceCartesianCover
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalLiteralExtraction

/-!
# The actual source index after occurrence extraction

The existing source atlas transports its residual dictionary across
equal finite carriers. Those proof transports change no atom support
or original source index. The identities here expose that fact, so the
literal coefficient and location constructions can be applied to the
same already constructed covered leaf.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckePort.Moments HeckePort.Moments.Support

variable {K : Type} [Field K] [NumberField K] {A : SArithmeticData K}
variable {ι : Type*} {columns otherColumns : Finset ι}
variable {ideal : ι → A.Exterior} {k : ℕ}

namespace CartesianSourceReindex

/-- A finite-carrier transport affects only the proof fields of the
actual expansion dictionary. -/
private theorem carrier_cast_plain₁ (h : columns = otherColumns)
    (e : CartesianSourceReindex columns ideal k =
      CartesianSourceReindex otherColumns ideal k)
    (R : CartesianSourceReindex columns ideal k) :
    (cast e R).plain₁ = R.plain₁ := by
  cases h
  rfl

private theorem carrier_cast_plain₂ (h : columns = otherColumns)
    (e : CartesianSourceReindex columns ideal k =
      CartesianSourceReindex otherColumns ideal k)
    (R : CartesianSourceReindex columns ideal k) :
    (cast e R).plain₂ = R.plain₂ := by
  cases h
  rfl

private theorem carrier_cast_slots (h : columns = otherColumns)
    (e : CartesianSourceReindex columns ideal k =
      CartesianSourceReindex otherColumns ideal k)
    (R : CartesianSourceReindex columns ideal k) :
    (cast e R).slots = R.slots := by
  cases h
  rfl

private theorem carrier_cast_index (h : columns = otherColumns)
    (e : CartesianSourceReindex columns ideal k =
      CartesianSourceReindex otherColumns ideal k)
    (R : CartesianSourceReindex columns ideal k) :
    (cast e R).index = R.index := by
  cases h
  rfl

variable (R : CartesianSourceReindex columns ideal k)
variable (P : Finset (Ideal (𝓞 K)))
variable (b : SupportCartesianBranch R.plain₁ R.plain₂ R.slots P)
variable (J : ι → A.Exterior)
variable (hJ : ∀ i ∈ columns, (J i).val = supportResidual (ideal i).val P)

@[simp] theorem supportResidualLabelBranch_plain₁ :
    (R.supportResidualLabelBranch P b J hJ).plain₁ =
      SupportCartesian.plainResidual R.plain₁ P b.plainExtract₁ := by
  unfold supportResidualLabelBranch
  simp only [eqRec_eq_cast]
  exact carrier_cast_plain₁ (R.supportExtractionLabel_fibre P b).symm _ _

@[simp] theorem supportResidualLabelBranch_plain₂ :
    (R.supportResidualLabelBranch P b J hJ).plain₂ =
      SupportCartesian.plainResidual R.plain₂ P b.plainExtract₂ := by
  unfold supportResidualLabelBranch
  simp only [eqRec_eq_cast]
  exact carrier_cast_plain₂ (R.supportExtractionLabel_fibre P b).symm _ _

@[simp] theorem supportResidualLabelBranch_slots :
    (R.supportResidualLabelBranch P b J hJ).slots =
      fun j => SupportCartesian.primeLive (R.slots (SlotRestriction.index b.keep j)) P := by
  unfold supportResidualLabelBranch
  simp only [eqRec_eq_cast]
  exact carrier_cast_slots (R.supportExtractionLabel_fibre P b).symm _ _

@[simp] theorem supportResidualLabelBranch_index :
    (R.supportResidualLabelBranch P b J hJ).index =
      fun i => R.index (b.reconstruct i) := by
  unfold supportResidualLabelBranch
  simp only [eqRec_eq_cast]
  exact carrier_cast_index (R.supportExtractionLabel_fibre P b).symm _ _

end CartesianSourceReindex

namespace SourceCartesianAtlas

variable (T : SourceCartesianAtlas columns ideal)
variable (P : Finset (Ideal (𝓞 K))) (D : Ideal (𝓞 K))
variable (J : ι → A.Exterior)
variable (hJ : ∀ i ∈ columns, (J i).val = supportResidual (ideal i).val P)
variable (a : T.labels P D)

@[simp] theorem residualReindex_plain₁ :
    (T.residualReindex P D J hJ a).plain₁ =
      SupportCartesian.plainResidual T.reindex.plain₁ P (T.branch P D a).plainExtract₁ := by
  unfold residualReindex
  simp only [eqRec_eq_cast]
  rw [CartesianSourceReindex.carrier_cast_plain₁ (T.commonFibre_eq_full P D a).symm]
  rw [CartesianSourceReindex.carrier_cast_plain₁
    (congrArg (fun key => columns.filter
      (fun i => T.reindex.supportExtractionLabel P i = key)) (T.branch_key P D a))]
  exact T.reindex.supportResidualLabelBranch_plain₁ P (T.branch P D a) J hJ

@[simp] theorem residualReindex_plain₂ :
    (T.residualReindex P D J hJ a).plain₂ =
      SupportCartesian.plainResidual T.reindex.plain₂ P (T.branch P D a).plainExtract₂ := by
  unfold residualReindex
  simp only [eqRec_eq_cast]
  rw [CartesianSourceReindex.carrier_cast_plain₂ (T.commonFibre_eq_full P D a).symm]
  rw [CartesianSourceReindex.carrier_cast_plain₂
    (congrArg (fun key => columns.filter
      (fun i => T.reindex.supportExtractionLabel P i = key)) (T.branch_key P D a))]
  exact T.reindex.supportResidualLabelBranch_plain₂ P (T.branch P D a) J hJ

@[simp] theorem residualReindex_slots :
    (T.residualReindex P D J hJ a).slots = fun j =>
      SupportCartesian.primeLive
        (T.reindex.slots (SlotRestriction.index (T.branch P D a).keep j)) P := by
  unfold residualReindex
  simp only [eqRec_eq_cast]
  rw [CartesianSourceReindex.carrier_cast_slots (T.commonFibre_eq_full P D a).symm]
  rw [CartesianSourceReindex.carrier_cast_slots
    (congrArg (fun key => columns.filter
      (fun i => T.reindex.supportExtractionLabel P i = key)) (T.branch_key P D a))]
  exact T.reindex.supportResidualLabelBranch_slots P (T.branch P D a) J hJ

/-- The original column is reconstructed by the actual occurrence map,
not selected anew from an equality of complete ideals. -/
@[simp] theorem residualReindex_index :
    (T.residualReindex P D J hJ a).index =
      fun i => T.reindex.index ((T.branch P D a).reconstruct i) := by
  unfold residualReindex
  simp only [eqRec_eq_cast]
  rw [CartesianSourceReindex.carrier_cast_index (T.commonFibre_eq_full P D a).symm]
  rw [CartesianSourceReindex.carrier_cast_index
    (congrArg (fun key => columns.filter
      (fun i => T.reindex.supportExtractionLabel P i = key)) (T.branch_key P D a))]
  exact T.reindex.supportResidualLabelBranch_index P (T.branch P D a) J hJ

end SourceCartesianAtlas
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.CartesianSourceReindex.supportResidualLabelBranch_index
#print axioms HeckeSkeleton.Moments.EngineStep.SourceCartesianAtlas.residualReindex_index
