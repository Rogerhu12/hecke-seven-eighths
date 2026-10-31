import HeckeSkeleton.Moments.MOM_INV_STEP.PositiveAssignedSource
import HeckeSkeleton.Moments.MOM_INV_STEP.FirstOuterCenters

/-!
# Actual first and second production indices form the reconstruction source

The first index is exactly FirstParentRows.OuterIndex, after the old
label and row have been removed. Its overlap is the original first
full-Moebius overlap. The fresh second common ideal, actual local mask,
bare frequency with its entire Γ-sector and independent second overlap
are the actual second production indices. A cutoff may depend on the
frozen first data, fresh common ideal and mask, but not on its bare row.

The map into the positive source is injective. Thus restricting to fixed
norm bins or fixed mark subsets and reindexing preserves the whole finite
positive sum before the proved fiber estimate is used.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.ActualPositiveIndex

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open FirstParentEnergy FirstParentRows CanonicalNormPools PositiveAssignedSource
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))] [Γ.FiniteIndex]
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset
variable {σ : Type*}
variable (T : FirstParentEnergy.Data K S (σ := σ))

abbrev Cutoff (X : ℝ) := ∀ o : OuterIndex K S D T,
  FirstOuterCenters.Overlap K S D T o → ∀ g : squarefreePool K Sset (2 * X),
    (SecondSourceMasks.commonMask K S D g.val).powerset → ℝ

abbrev Index (X : ℝ) (H : Cutoff K S D T X) :=
  Σ o : OuterIndex K S D T, Σ e : FirstOuterCenters.Overlap K S D T o,
    Σ g : squarefreePool K Sset (2 * X),
      Σ δ : (SecondSourceMasks.commonMask K S D g.val).powerset,
        Σ z : FirstDualTruncation.sectorCutoff K S D Γ (H o e g δ),
          SecondMobiusGeometry.overlapPool K S X g.val

def bare (hmask : T.mask = ∅) (X : ℝ) (H : Cutoff K S D T X)
    (i : Index K S D Γ T X H) :
    BareSource (K := K) (S := S) (D := D) (Γ := Γ)
      (N := columnPool K S T) (X := X) where
  b₁ := i.1.1.val
  b₂ := i.1.2.1.val
  extraction := i.1.2.2.1.val
  extraction_mem := i.1.2.2.1.property
  quotient := FirstMobiusGeometry.overlapIdeal K S D T.scale
    (outerAnchor K S D T i.1).1 (outerAnchor K S D T i.1).2
    i.1.1.val i.1.2.1.val false i.2.1
  common := i.2.2.1.val
  common_mem := i.2.2.1.property
  overlap := SecondMobiusGeometry.overlapIdeal K S X i.2.2.1.val i.2.2.2.2.2
  overlap_mem := i.2.2.2.2.2.property
  firstDivisor := i.1.2.2.2.val
  first_mem := by
    have h := Finset.mem_powerset.mp i.1.2.2.2.property
    simpa only [FirstParentRetained.actualMask, FirstSourcePartition.actualMask, hmask]
      using h
  secondDivisor := i.2.2.2.1.val
  second_mem := Finset.mem_powerset.mp i.2.2.2.1.property
  frequency := i.2.2.2.2.1.val
  oldAssigned := fun j => Fin.elim0 j
  newAssigned := fun j => Fin.elim0 j
  old_mem := fun j => Fin.elim0 j
  new_mem := fun j => Fin.elim0 j
  old_dvd := fun j => Fin.elim0 j
  new_dvd := fun j => Fin.elim0 j

theorem bare_refs (hmask : T.mask = ∅) (X : ℝ) (H : Cutoff K S D T X)
    (i : Index K S D Γ T X H) :
    (bare K S D Γ T hmask X H i).refs = outerAnchor K S D T i.1 := rfl

theorem bare_firstLabel (hmask : T.mask = ∅) (X : ℝ) (H : Cutoff K S D T X)
    (i : Index K S D Γ T X H) :
    (bare K S D Γ T hmask X H i).firstLabel = CanonicalIdealRow.toExterior K S
      (FirstColumnAssembly.retainedLabel K S (outerAnchor K S D T i.1).1
        (outerAnchor K S D T i.1).2 i.1.1.val i.1.2.1.val) := rfl

/-- All actual first-mask, fresh-common, second-mask and original
sector choices can be recovered. The original residual columns are no
longer part of this source, so no hidden column multiplicity is lost. -/
theorem bare_injective (hmask : T.mask = ∅) (X : ℝ) (H : Cutoff K S D T X) :
    Function.Injective (bare K S D Γ T hmask X H) := by
  rintro ⟨⟨b₁,b₂,κ,δ₁⟩,e,g,δ₂,z,v⟩ ⟨⟨b₁',b₂',κ',δ₁'⟩,e',g',δ₂',z',v'⟩ h
  have hb₁ : b₁ = b₁' := Subtype.ext (congrArg PositiveReconstruction.Source.b₁ h)
  cases hb₁
  have hb₂ : b₂ = b₂' := Subtype.ext (congrArg PositiveReconstruction.Source.b₂ h)
  cases hb₂
  have hκ : κ = κ' := Subtype.ext (congrArg PositiveReconstruction.Source.extraction h)
  cases hκ
  have hδ₁ : δ₁ = δ₁' := Subtype.ext (congrArg PositiveReconstruction.Source.firstDivisor h)
  cases hδ₁
  have he : e = e' := Subtype.ext
    (congrArg (fun B => B.quotient.val.val) h)
  cases he
  have hg : g = g' := Subtype.ext (congrArg PositiveReconstruction.Source.common h)
  cases hg
  have hδ₂ : δ₂ = δ₂' := Subtype.ext (congrArg PositiveReconstruction.Source.secondDivisor h)
  cases hδ₂
  have hz : z = z' := Subtype.ext (congrArg PositiveReconstruction.Source.frequency h)
  cases hz
  have hv : v = v' := Subtype.ext (congrArg (fun B => B.overlap.val.val) h)
  cases hv
  rfl

def source (hmask : T.mask = ∅) (X : ℝ) (H : Cutoff K S D T X)
    (I : Finset (Index K S D Γ T X H)) :
    Finset (BareSource (K := K) (S := S) (D := D) (Γ := Γ)
      (N := columnPool K S T) (X := X)) :=
  I.image (bare K S D Γ T hmask X H)

/-- Exact reindexing for any of the fixed finite arithmetic norm boxes.
There is no equality of source energies in the hypotheses. -/
theorem source_sum {A : Type*} [AddCommMonoid A]
    (hmask : T.mask = ∅) (X : ℝ) (H : Cutoff K S D T X)
    (I : Finset (Index K S D Γ T X H))
    (F : BareSource (K := K) (S := S) (D := D) (Γ := Γ)
      (N := columnPool K S T) (X := X) → A) :
    (∑ B ∈ source K S D Γ T hmask X H I, F B) =
      ∑ i ∈ I, F (bare K S D Γ T hmask X H i) :=
  Finset.sum_image (fun _ _ _ _ h => bare_injective K S D Γ T hmask X H h)

theorem bare_frequency_bound (hmask : T.mask = ∅) (X : ℝ) (H : Cutoff K S D T X)
    (i : Index K S D Γ T X H) :
    height K Sset (bare K S D Γ T hmask X H i).frequency.1 ≤
      H i.1 i.2.1 i.2.2.1 i.2.2.2.1 :=
  (FirstDualTruncation.mem_sectorCutoff K S D Γ _ i.2.2.2.2.1.val).mp
    i.2.2.2.2.1.property

end HeckeSkeleton.Moments.MOM_INV_STEP.ActualPositiveIndex

end
