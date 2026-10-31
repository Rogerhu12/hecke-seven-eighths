import HeckeSkeleton.Moments.MOM_INV_STEP.ActualPositiveIndex
import HeckeSkeleton.Moments.MOM_INV_STEP.DivisorRowMass

/-!
# A counting embedding of the complete first outer source

The original first cubes, extraction key, first mask and full-Moebius
overlap are retained injectively. Completing this record by unit common,
unit overlap, empty second mask and unit frequency is used solely for
the reconstruction count. It is not asserted to be a second Poisson
source or to satisfy a second-frequency cutoff.

For the production orbital mask ∅, the completed source has triple
(q₀,e,1), label CJ and a row divisor of q₀ CJ with its uniquely determined
actual sector transport. Its retained zero is identically one.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.FirstErrorSource

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
  DedekindZetaZeroFree.LargeSieve
open HeckeSkeleton.Moments.MOMInvStep FixedTripleFibers FixedTripleEnergy
open FirstParentEnergy FirstParentRows CanonicalNormPools PositiveAssignedSource
open PositiveReconstruction FirstInversePoisson
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset
local notation "Sector" => CanonicalSectors.UnitClasses K Sset Γ
variable {σ : Type*}
variable (T : FirstParentEnergy.Data K S (σ := σ))

abbrev Index := Σ o : OuterIndex K S D T, FirstOuterCenters.Overlap K S D T o

private theorem unit_mem_common :
    unitIdeal K S ∈ squarefreePool K Sset (2 * (1 : ℝ)) := by
  rw [mem_squarefreePool]
  simp [height]

private theorem unit_mem_overlap :
    (unitIdeal K S).val.val ∈ SecondMobiusGeometry.overlapPool K S 1 (unitIdeal K S) := by
  apply FullMobius.mem_divisorPool
  · change unitIdeal K S ∈ squarefreePool K Sset
      (2 * (1 : ℝ) / height K Sset (unitIdeal K S))
    simpa [height] using unit_mem_common K S
  · exact (mem_idealDivisors (nonZeroDivisors.coe_ne_zero (unitIdeal K S).val)).mpr
      (dvd_refl _)

/-- This completion serves the arithmetic count only. -/
def bare (hmask : T.mask = ∅) (i : Index K S D T) :
    BareSource (K := K) (S := S) (D := D) (Γ := Γ)
      (N := columnPool K S T) (X := 1) where
  b₁ := i.1.1.val
  b₂ := i.1.2.1.val
  extraction := i.1.2.2.1.val
  extraction_mem := i.1.2.2.1.property
  quotient := FirstMobiusGeometry.overlapIdeal K S D T.scale
    (outerAnchor K S D T i.1).1 (outerAnchor K S D T i.1).2
    i.1.1.val i.1.2.1.val false i.2
  common := unitIdeal K S
  common_mem := unit_mem_common K S
  overlap := unitIdeal K S
  overlap_mem := unit_mem_overlap K S
  firstDivisor := i.1.2.2.2.val
  first_mem := by
    have h := Finset.mem_powerset.mp i.1.2.2.2.property
    simpa only [FirstParentRetained.actualMask, FirstSourcePartition.actualMask, hmask]
      using h
  secondDivisor := ∅
  second_mem := Finset.empty_subset _
  frequency := (unitIdeal K S,1)
  oldAssigned := fun j => Fin.elim0 j
  newAssigned := fun j => Fin.elim0 j
  old_mem := fun j => Fin.elim0 j
  new_mem := fun j => Fin.elim0 j
  old_dvd := fun j => Fin.elim0 j
  new_dvd := fun j => Fin.elim0 j

theorem bare_refs (hmask : T.mask = ∅) (i : Index K S D T) :
    (bare K S D Γ T hmask i).refs = outerAnchor K S D T i.1 := rfl

theorem bare_firstLabel (hmask : T.mask = ∅) (i : Index K S D T) :
    (bare K S D Γ T hmask i).firstLabel = CanonicalIdealRow.toExterior K S
      (FirstColumnAssembly.retainedLabel K S (outerAnchor K S D T i.1).1
        (outerAnchor K S D T i.1).2 i.1.1.val i.1.2.1.val) := rfl

theorem bare_injective (hmask : T.mask = ∅) :
    Function.Injective (bare K S D Γ T hmask) := by
  rintro ⟨⟨b₁,b₂,κ,δ⟩,e⟩ ⟨⟨b₁',b₂',κ',δ'⟩,e'⟩ h
  have hb₁ : b₁ = b₁' := Subtype.ext (congrArg PositiveReconstruction.Source.b₁ h)
  cases hb₁
  have hb₂ : b₂ = b₂' := Subtype.ext (congrArg PositiveReconstruction.Source.b₂ h)
  cases hb₂
  have hκ : κ = κ' := Subtype.ext (congrArg PositiveReconstruction.Source.extraction h)
  cases hκ
  have hδ : δ = δ' := Subtype.ext (congrArg PositiveReconstruction.Source.firstDivisor h)
  cases hδ
  have he : e = e' := Subtype.ext (congrArg (fun B => B.quotient.val.val) h)
  cases he
  rfl

theorem secondDivisor_val (hmask : T.mask = ∅) (i : Index K S D T) :
    (bare K S D Γ T hmask i).d₂.val.val = 1 := by
  have hd := (bare K S D Γ T hmask i).d₂_dvd
  change (bare K S D Γ T hmask i).d₂.val.val ∣ (1 : Ideal (𝓞 K)) at hd
  change (bare K S D Γ T hmask i).d₂.val.val = ⊤
  exact top_le_iff.mp (Ideal.dvd_iff_le.mp hd)

theorem commonResidual_val (hmask : T.mask = ∅) (i : Index K S D T) :
    (bare K S D Γ T hmask i).commonResidual.val.val = 1 := by
  have he := (bare K S D Γ T hmask i).d₂_mul_residual
  rw [secondDivisor_val K S D Γ T hmask i, one_mul] at he
  exact he

theorem outer_eq (hmask : T.mask = ∅) (i : Index K S D T) :
    (bare K S D Γ T hmask i).outer =
      ⟨(bare K S D Γ T hmask i).cubeQ,
       (bare K S D Γ T hmask i).quotient.val.val,1⟩ := by
  apply OuterTriple.ext <;> try rfl
  exact commonResidual_val K S D Γ T hmask i

theorem label_eq (hmask : T.mask = ∅) (i : Index K S D T) :
    (bare K S D Γ T hmask i).newLabel =
      (bare K S D Γ T hmask i).firstLabel.val.val := by
  rw [PositiveReconstruction.Source.newLabel,
    secondDivisor_val K S D Γ T hmask i,
    (bare K S D Γ T hmask i).firstLabel_val]
  change (_ * _ * 1 * 1 : Ideal (𝓞 K)) = _
  ring

def rowSector (I : Ideal (𝓞 K)) : Sector :=
  ActualMaskReconstruction.sectorTransport K S D Γ I 1 1

theorem row_eq (hmask : T.mask = ∅) (i : Index K S D T) :
    (bare K S D Γ T hmask i).newRow =
      ((bare K S D Γ T hmask i).dk.val.val,
        rowSector K S D Γ (bare K S D Γ T hmask i).dk.val.val) := by
  unfold PositiveReconstruction.Source.newRow
  rw [secondDivisor_val K S D Γ T hmask i]
  change (_ * 1 * 1, _) = (_, _)
  simp only [mul_one]

theorem row_dvd (hmask : T.mask = ∅) (i : Index K S D T) :
    (bare K S D Γ T hmask i).newRow.1 ∣
      (bare K S D Γ T hmask i).outer.q0 * (bare K S D Γ T hmask i).newLabel := by
  let B := bare K S D Γ T hmask i
  rw [row_eq K S D Γ T hmask i, label_eq K S D Γ T hmask i]
  change B.dk.val.val ∣ B.cubeQ * B.firstLabel.val.val
  calc
    B.dk.val.val ∣ B.firstCommon * (B.b₁.val.val * B.b₂.val.val).radical := B.dk_dvd
    _ ∣ B.firstCommon * (B.cubeQ * B.cubeJ) :=
      mul_dvd_mul_left B.firstCommon B.cube_radical_dvd
    _ = B.cubeQ * B.firstLabel.val.val := by rw [B.firstLabel_val]; ring

theorem counting_test_one (hmask : T.mask = ∅) (i : Index K S D T) :
    DivisorRowMass.test (rowSector K S D Γ)
      ((bare K S D Γ T hmask i).outer,
       (bare K S D Γ T hmask i).newLabel,
       (bare K S D Γ T hmask i).newRow) = 1 := by
  apply DivisorRowMass.test_one
  · exact row_dvd K S D Γ T hmask i
  · rw [row_eq K S D Γ T hmask i]

theorem retainedZero_one (hmask : T.mask = ∅) (i : Index K S D T)
    (R : Ideal (𝓞 K)) : (bare K S D Γ T hmask i).retainedZero R = 1 := by
  unfold PositiveReconstruction.Source.retainedZero
    SecondSourceCharacters.commonZero SecondColumnEnergy.overlapZero
  change (_ * idealCoprimeMask _ (1 : Ideal (𝓞 K))) *
    idealCoprimeMask R (1 : Ideal (𝓞 K)) *
      idealCoprimeMask (1 * _) (1 : Ideal (𝓞 K)) = 1
  simp [idealCoprimeMask]

def source (hmask : T.mask = ∅) (I : Finset (Index K S D T)) :
    Finset (BareSource (K := K) (S := S) (D := D) (Γ := Γ)
      (N := columnPool K S T) (X := 1)) :=
  I.image (bare K S D Γ T hmask)

theorem source_sum {A : Type*} [AddCommMonoid A]
    (hmask : T.mask = ∅) (I : Finset (Index K S D T))
    (F : BareSource (K := K) (S := S) (D := D) (Γ := Γ)
      (N := columnPool K S T) (X := 1) → A) :
    (∑ B ∈ source K S D Γ T hmask I, F B) =
      ∑ i ∈ I, F (bare K S D Γ T hmask i) :=
  Finset.sum_image (fun _ _ _ _ h => bare_injective K S D Γ T hmask h)

theorem oldExtracted_eq (hmask : T.mask = ∅) (i : Index K S D T) (side : Bool) :
    PositiveAssignedSource.oldExtracted (bare K S D Γ T hmask i) side =
      FirstOverlapColumns.markBase K S (outerAnchor K S D T i.1).1
        (outerAnchor K S D T i.1).2 i.1.1.val i.1.2.1.val side
          (FirstMobiusGeometry.overlapIdeal K S D T.scale
            (outerAnchor K S D T i.1).1 (outerAnchor K S D T i.1).2
            i.1.1.val i.1.2.1.val false i.2) := rfl

end HeckeSkeleton.Moments.MOM_INV_STEP.FirstErrorSource

end

