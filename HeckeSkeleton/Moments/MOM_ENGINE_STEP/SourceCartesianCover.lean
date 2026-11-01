import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CombinedSupportPoolAtlas

/-!
# Genuine finite Cartesian covers of the original Gauss sources

A cover records the original discrete label of each column and the true
Cartesian dictionary on each resulting fibre.  Its fields are finite
individual-column data, not source inequalities.  The actual main and
valuation-error constructors below derive those dictionaries from the
first original EXPANSION atlas and its exact support quotient recipes.
-/

noncomputable section
open scoped Classical BigOperators NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain DedekindZetaZeroFree
open HeckePort.Moments HeckePort.Moments.Support HeckePort.IdealMobiusDivisorSum

variable {K : Type} [Field K] [NumberField K] {A : SArithmeticData K}
variable {ι κ : Type*}

structure SourceCartesianCover (columns : Finset ι) (ideal : ι → A.Exterior) where
  Label : Type
  labels : Finset Label
  label : ι → Label
  maps : ∀ i ∈ columns, label i ∈ labels
  branch : ∀ a : labels, SourceCartesianAtlas
    (columns.filter (fun i => label i = a.val)) ideal

namespace SourceCartesianCover

variable {columns : Finset ι} {ideal : ι → A.Exterior}
variable (T : SourceCartesianCover columns ideal)

def fibre (a : T.Label) : Finset ι := columns.filter (fun i => T.label i = a)

theorem fibre_subset (a : T.Label) : T.fibre a ⊆ columns := by
  intro i hi
  exact (Finset.mem_filter.mp hi).1

/-- The original complete column sum, with any later individual-column
filter, is exactly partitioned by the actual earlier labels. -/
theorem sum_filtered {M : Type*} [AddCommMonoid M] (P : ι → Prop) (f : ι → M) :
    (∑ i ∈ columns.filter P, f i) =
      ∑ a : T.labels, ∑ i ∈ (T.fibre a.val).filter P, f i := by
  calc
    _ = ∑ a ∈ T.labels,
        ∑ i ∈ (columns.filter P).filter (fun i => T.label i = a), f i :=
      (Finset.sum_fiberwise_of_maps_to
        (fun i hi => T.maps i (Finset.mem_filter.mp hi).1) f).symm
    _ = ∑ a ∈ T.labels, ∑ i ∈ (T.fibre a).filter P, f i := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr
      · ext i
        simp only [fibre, Finset.mem_filter]
        exact ⟨fun ⟨⟨hi, hp⟩, ha⟩ => ⟨⟨hi, ha⟩, hp⟩,
          fun ⟨⟨hi, ha⟩, hp⟩ => ⟨⟨hi, hp⟩, ha⟩⟩
      · intro i _
        rfl
    _ = _ := (Finset.sum_coe_sort _ _).symm

variable {otherColumns : Finset κ} {otherIdeal : κ → A.Exterior}
variable (U : SourceCartesianCover otherColumns otherIdeal)

/-- Both true source covers are split while the coupled complex row
sum is still intact.  The original physical rows and all coefficients
are unchanged. -/
theorem sum_pair_rows {H M : Type*} [AddCommMonoid M]
    (rows : Finset H) (P : ι → Prop) (Q : κ → Prop) (f : H → ι → κ → M) :
    (∑ h ∈ rows, ∑ i ∈ columns.filter P, ∑ j ∈ otherColumns.filter Q, f h i j) =
      ∑ a : T.labels, ∑ b : U.labels,
        ∑ h ∈ rows, ∑ i ∈ (T.fibre a.val).filter P,
          ∑ j ∈ (U.fibre b.val).filter Q, f h i j := by
  calc
    _ = ∑ h ∈ rows, ∑ a : T.labels, ∑ i ∈ (T.fibre a.val).filter P,
        ∑ b : U.labels, ∑ j ∈ (U.fibre b.val).filter Q, f h i j := by
      apply Finset.sum_congr rfl
      intro h _
      rw [T.sum_filtered P]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro i _
      exact U.sum_filtered Q (fun j => f h i j)
    _ = _ := by
      rw [Finset.sum_comm (s := rows) (t := (Finset.univ : Finset T.labels))]
      apply Finset.sum_congr rfl
      intro a _
      simp_rw [Finset.sum_comm (s := (T.fibre a.val).filter P)
        (t := (Finset.univ : Finset U.labels))]
      rw [Finset.sum_comm (s := rows) (t := (Finset.univ : Finset U.labels))]

end SourceCartesianCover

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

/-- True cover of the whole main source, constructed before either
continuous Fourier variable. -/
def mainSourceCartesianCover (c : ι → ℂ) :
    SourceCartesianCover (d.mainSource c).columns (d.mainSource c).ideal where
  Label := SupportCartesian.ExtractionKey K T.slotCount
  labels := T.labels S D
  label := T.reindex.supportExtractionLabel S
  maps i hi := by
    apply Finset.mem_image_of_mem
    have hi' : i ∈ d.columns := hi
    rw [hcolumns] at hi'
    exact hi'
  branch a := d.mainAtlasForLabel T S D hcolumns hideal c a

/-- True cover of the original valuation subtype.  The joint occurrence
key on the first support and the actual prime constructs every branch
through the original residual presentation. -/
def residualSourceCartesianCover (p : ExteriorPrime A) (n : ℕ) (c : ι → ℂ) :
    SourceCartesianCover (d.residualSource p n c).columns
      (d.residualSource p n c).ideal where
  Label := SupportCartesian.ExtractionKey K T.slotCount
  labels := d.combinedLabels T S p n
  label i := T.reindex.supportExtractionLabel (S ∪ {p.val.asIdeal}) i.val
  maps i _ := Finset.mem_image_of_mem
    (T.reindex.supportExtractionLabel (S ∪ {p.val.asIdeal})) i.property
  branch a := d.combinedAtlasForLabel T S D hcolumns hideal p n c a

end FirstGaussPoolData

end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.SourceCartesianCover.sum_pair_rows
#print axioms HeckeSkeleton.Moments.EngineStep.FirstGaussPoolData.mainSourceCartesianCover
#print axioms HeckeSkeleton.Moments.EngineStep.FirstGaussPoolData.residualSourceCartesianCover

