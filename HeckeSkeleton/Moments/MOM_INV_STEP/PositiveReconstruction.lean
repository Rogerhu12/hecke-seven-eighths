import HeckeSkeleton.Moments.MOM_INV_STEP.ActualMaskReconstruction
import HeckeSkeleton.Moments.MOM_INV_STEP.SecondMobiusGeometry
import HeckeSkeleton.Moments.MOM_INV_STEP.FirstColumnAssembly
import HeckeSkeleton.Moments.MOM_INV_STEP.ActualSourceReindexing

/-!
# Reconstruction of the actual positive source after both column steps

The first columns have already been replaced by their extraction key,
and the fresh second columns by their fixed original common ideal. No
historical residual column is recorded here. The new overlap is selected
from the full mutual-Moebius pool, independently of that fixed common.

All divisor and prime choices are still original source choices. The
reconstruction relation and its genuine sector transport are proved
from those choices. The resulting map is injective, so a finite positive
source may be sent to the fixed-triple fibers without merging a hidden
column multiplicity.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.PositiveReconstruction

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep
open FixedTripleFibers FixedTripleEnergy FirstSourceDecomposition IdealMobiusMask
  FirstSourcePartition CanonicalNormPools ActualDivisorSectors ActualMaskReconstruction
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer Sset K
local notation "Ext" => ExteriorIdeal K Sset
local notation "Sector" => CanonicalSectors.UnitClasses K Sset Γ
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
variable {Jo Jn : ℕ}

def actualAnchor (N : Finset Ext) (b₁ b₂ : Ext) (κ : Key K)
    (hκ : κ ∈ keys K S N N b₁ b₂) : Ext × Ext :=
  anchor K S N N b₁ b₂ ⟨κ,hκ⟩

/-- Precisely the source data remaining after the first row fiber and
the fresh second common-factor decomposition. The last two divisibility
conditions refer to original extracted ideals, not to the future child. -/
@[ext] structure Source (N : Finset Ext) (X : ℝ)
    (oldLists : Fin Jo → Finset (HeightOneSpectrum (𝓞 K)))
    (newLists : Fin Jn → Finset (HeightOneSpectrum (𝓞 K))) where
  b₁ : Ext
  b₂ : Ext
  extraction : Key K
  extraction_mem : extraction ∈ keys K S N N b₁ b₂
  quotient : Ext
  common : Ext
  common_mem : common ∈ squarefreePool K Sset (2 * X)
  overlap : Ext
  overlap_mem : overlap.val.val ∈ SecondMobiusGeometry.overlapPool K S X common
  firstDivisor : Finset (HeightOneSpectrum OS)
  first_mem : firstDivisor ⊆ FirstSourcePartition.actualMask K S D ∅
    (actualAnchor K S N b₁ b₂ extraction extraction_mem).1
    (actualAnchor K S N b₁ b₂ extraction extraction_mem).2 b₁ b₂
  secondDivisor : Finset (HeightOneSpectrum OS)
  second_mem : secondDivisor ⊆ SecondSourceMasks.commonMask K S D common
  frequency : Ext × Sector
  oldAssigned : Fin Jo → HeightOneSpectrum (𝓞 K)
  newAssigned : Fin Jn → HeightOneSpectrum (𝓞 K)
  old_mem : ∀ i, oldAssigned i ∈ oldLists i
  new_mem : ∀ i, newAssigned i ∈ newLists i
  old_dvd : ∀ i, (oldAssigned i).asIdeal ∣
    FirstSourceDecomposition.C
      (actualAnchor K S N b₁ b₂ extraction extraction_mem).1.val
      (actualAnchor K S N b₁ b₂ extraction extraction_mem).2.val b₁.val b₂.val *
        (b₁.val.val * b₂.val.val).radical * quotient.val.val
  new_dvd : ∀ i, (newAssigned i).asIdeal ∣ common.val.val * overlap.val.val

variable {K S D Γ}
variable {N : Finset (ExteriorIdeal K (S : Set (HeightOneSpectrum (𝓞 K))))} {X : ℝ}
variable {oldLists : Fin Jo → Finset (HeightOneSpectrum (𝓞 K))}
variable {newLists : Fin Jn → Finset (HeightOneSpectrum (𝓞 K))}

namespace Source

variable (B : Source K S D Γ N X oldLists newLists)

def refs : Ext × Ext := actualAnchor K S N B.b₁ B.b₂ B.extraction B.extraction_mem
def epsilon (n : Ext) (p : HeightOneSpectrum (𝓞 K)) : Bool := decide (p.asIdeal ∣ n.val.val)
def cubeQ : Ideal (𝓞 K) := CubeLabels.q0 B.b₁.val B.b₂.val (epsilon B.refs.1) (epsilon B.refs.2)
def cubeJ : Ideal (𝓞 K) := CubeLabels.J B.b₁.val B.b₂.val (epsilon B.refs.1) (epsilon B.refs.2)
def cubeJ2 : Ideal (𝓞 K) := CubeLabels.J2 B.b₁.val B.b₂.val (epsilon B.refs.1) (epsilon B.refs.2)
def cubeS : Ideal (𝓞 K) := CubeLabels.s B.b₁.val B.b₂.val
def firstCommon : Ideal (𝓞 K) := C B.refs.1.val B.refs.2.val B.b₁.val B.b₂.val
def dk : Ext := divisorIdeal K S (sIntegerMaskGenerator K Sset B.firstDivisor)
def d₂ : Ext := divisorIdeal K S (sIntegerMaskGenerator K Sset B.secondDivisor)
def commonResidual : Ext := SecondOverlapColumns.residual K S B.common B.d₂

theorem common_squarefree : Squarefree B.common.val.val :=
  squarefreePool_squarefree K Sset B.common_mem

theorem overlap_squarefree : Squarefree B.overlap.val.val :=
  SecondMobiusGeometry.overlap_squarefree K S X B.common B.overlap.val.val B.overlap_mem

theorem d₂_dvd : B.d₂.val.val ∣ B.common.val.val :=
  SecondSourceMasks.actual_divisor_dvd K S D B.common B.common_squarefree
    B.secondDivisor B.second_mem

theorem d₂_mul_residual : B.d₂.val.val * B.commonResidual.val.val = B.common.val.val :=
  (FirstSourceDecomposition.squarefree_divisor_decomposition
    B.common.val B.d₂.val B.common_squarefree B.d₂_dvd).1.symm

theorem dk_dvd : B.dk.val.val ∣ B.firstCommon * (B.b₁.val.val * B.b₂.val.val).radical :=
  ActualMaskReconstruction.first_divisor_dvd_common_cube K S D B.refs.1 B.refs.2
    B.b₁ B.b₂ B.firstDivisor B.first_mem

theorem cubeQ_ne_zero : B.cubeQ ≠ 0 := by
  unfold cubeQ CubeLabels.q0 CubeAlgebra.b0Label CubeAlgebra.primeProduct
  exact Finset.prod_ne_zero_iff.mpr fun p _ => pow_ne_zero _ p.ne_bot

theorem cubeJ_ne_zero : B.cubeJ ≠ 0 := by
  unfold cubeJ CubeLabels.J CubeAlgebra.jLabel CubeAlgebra.primeProduct
  exact Finset.prod_ne_zero_iff.mpr fun p _ => pow_ne_zero _ p.ne_bot

theorem cube_radical_dvd : (B.b₁.val.val * B.b₂.val.val).radical ∣ B.cubeQ * B.cubeJ := by
  have hd : B.b₁.val.val * B.b₂.val.val ∣ (B.cubeQ * B.cubeJ) ^ 2 := by
    refine ⟨B.cubeS, ?_⟩
    change (CubeLabels.q0 B.b₁.val B.b₂.val (epsilon B.refs.1) (epsilon B.refs.2) *
      CubeLabels.J B.b₁.val B.b₂.val (epsilon B.refs.1) (epsilon B.refs.2)) ^ 2 =
        B.b₁.val.val * B.b₂.val.val * CubeLabels.s B.b₁.val B.b₂.val
    rw [CubeLabels.J_eq_s_mul_J2, CubeLabels.actual_cube_decomposition]
    ring
  apply Ideal.dvd_iff_le.mpr
  have hh := Ideal.radical_mono (Ideal.dvd_iff_le.mp hd)
  rw [Ideal.radical_pow _ (by decide : (2 : ℕ) ≠ 0)] at hh
  exact Ideal.le_radical.trans hh

theorem A_dvd_radical (n : Ext) :
    A n.val B.b₁.val B.b₂.val ∣ (B.b₁.val.val * B.b₂.val.val).radical := by
  change A n.val B.b₁.val B.b₂.val ∣ (B.b₁.val * B.b₂.val).val.radical
  rw [radical_eq_primeProduct (B.b₁.val * B.b₂.val)]
  exact Finset.prod_dvd_prod_of_subset _ _
    (fun p : HeightOneSpectrum (𝓞 K) => p.asIdeal) Finset.inter_subset_right

def outer : OuterTriple K := ⟨B.cubeQ, B.quotient.val.val, B.commonResidual.val.val⟩
def newLabel : Ideal (𝓞 K) := B.cubeJ * B.firstCommon * B.d₂.val.val * B.overlap.val.val
def newRow : Ideal (𝓞 K) × Sector :=
  (B.dk.val.val * B.d₂.val.val * B.frequency.1.val.val,
    ActualMaskReconstruction.sectorTransport K S D Γ B.dk.val.val B.d₂.val.val B.frequency.2)

/-- This is the retained label actually produced by the first column
assembly, packaged as the exterior ideal used by the second transform. -/
def firstLabel : Ext := CanonicalIdealRow.toExterior K S
  (FirstColumnAssembly.retainedLabel K S B.refs.1 B.refs.2 B.b₁ B.b₂)

theorem firstLabel_val : B.firstLabel.val.val = B.firstCommon * B.cubeJ := by
  change B.firstCommon * (CanonicalCubeLabels.J K S B.b₁ B.b₂
    (ConductorMasks.squarefreeBit K S B.refs.1)
    (ConductorMasks.squarefreeBit K S B.refs.2)).val.val = _
  rw [CanonicalCubeLabels.J_val]
  rfl

theorem firstCommon_coprime_cubeJ : IsCoprime B.firstCommon B.cubeJ := by
  have hc := (FirstSourceDecomposition.first_factors_coprime
    B.refs.1.val B.refs.2.val B.b₁.val B.b₂.val).2.2
  have hc' : IsCoprime B.firstCommon (B.b₁.val.val * B.b₂.val.val).radical :=
    (IsCoprime.mul_left_iff.mp (IsCoprime.mul_left_iff.mp hc).1).1
  have hd : B.cubeJ ∣ B.b₁.val.val * B.b₂.val.val := by
    refine ⟨B.cubeQ ^ 2 * B.cubeJ2, ?_⟩
    change B.b₁.val.val * B.b₂.val.val =
      CubeLabels.J B.b₁.val B.b₂.val (epsilon B.refs.1) (epsilon B.refs.2) *
        (B.cubeQ ^ 2 * B.cubeJ2)
    rw [CubeLabels.J_eq_s_mul_J2, CubeLabels.actual_cube_decomposition]
    unfold cubeQ cubeJ2
    ring
  exact ((isCoprime_radical_right_iff _ _).mp hc').of_isCoprime_of_dvd_right hd

theorem firstLabel_squarefree : Squarefree B.firstLabel.val.val := by
  rw [B.firstLabel_val]
  exact squarefree_mul_iff.mpr ⟨B.firstCommon_coprime_cubeJ.isRelPrime,
    squarefree_primeProduct _, CubeLabels.J_squarefree _ _ _ _⟩

theorem literal_outer :
    SecondCenteredFamily.appendResidual K
      (FirstColumnAssembly.firstTriple K S B.refs.1 B.refs.2 B.b₁ B.b₂ B.quotient)
      (SecondOverlapColumns.residual K S B.common B.d₂).val.val = B.outer := by
  apply OuterTriple.ext
  · exact CanonicalCubeLabels.q0_val K S B.b₁ B.b₂ _ _
  · rfl
  · exact one_mul _

theorem literal_label :
    (SecondCompleteColumns.finalLabel K S B.firstLabel B.d₂ B.overlap).val.val =
      B.newLabel := by
  change (B.firstLabel.val.val * B.d₂.val.val) * B.overlap.val.val = _
  rw [B.firstLabel_val]
  unfold newLabel
  ring

theorem literal_row :
    ((SecondSourceColumns.newRowIdeal K S B.frequency.1
        (sIntegerMaskGenerator K Sset B.firstDivisor)
        (sIntegerMaskGenerator K Sset B.secondDivisor)).val.val,
      SecondSourceColumns.newSector K S Γ D
        (sIntegerMaskGenerator K Sset B.firstDivisor)
        (sIntegerMaskGenerator K Sset B.secondDivisor) B.frequency.2) = B.newRow := by
  apply Prod.ext
  · change B.d₂.val.val * (B.dk.val.val * B.frequency.1.val.val) =
      B.dk.val.val * B.d₂.val.val * B.frequency.1.val.val
    ring
  · exact (ActualMaskReconstruction.sectorTransport_actual K S D Γ
      B.firstDivisor B.secondDivisor B.frequency.2).symm

def tuple : SecondTuple K Sector Jo Jn where
  outer := B.outer
  core := ![B.cubeJ, B.firstCommon, B.d₂.val.val, B.cubeS, B.b₁.val.val,
    A B.refs.1.val B.b₁.val B.b₂.val, A B.refs.2.val B.b₁.val B.b₂.val, B.dk.val.val]
  commonResidual := B.overlap.val.val
  cubeResidual := B.cubeJ2
  secondCube := B.b₂.val.val
  extractedCommon := B.common.val.val
  frequency := (B.frequency.1.val.val,B.frequency.2)
  oldAssigned := B.oldAssigned
  newAssigned := B.newAssigned

theorem oldExtracted_dvd :
    B.firstCommon * (B.b₁.val.val * B.b₂.val.val).radical * B.quotient.val.val ∣
      B.outer.q0 * B.newLabel * B.outer.quotient := by
  calc
    _ ∣ (B.firstCommon * (B.cubeQ * B.cubeJ)) * B.quotient.val.val :=
      mul_dvd_mul_right (mul_dvd_mul_left B.firstCommon B.cube_radical_dvd) B.quotient.val.val
    _ ∣ _ := by
      refine ⟨B.d₂.val.val * B.overlap.val.val, ?_⟩
      unfold outer newLabel
      ring

theorem newExtracted_dvd : B.common.val.val * B.overlap.val.val ∣
    B.newLabel * B.outer.residual := by
  refine ⟨B.cubeJ * B.firstCommon, ?_⟩
  change (B.cubeJ * B.firstCommon * B.d₂.val.val * B.overlap.val.val) *
    B.commonResidual.val.val = (B.common.val.val * B.overlap.val.val) * (B.cubeJ * B.firstCommon)
  rw [← B.d₂_mul_residual]
  ring

/-- Every field of the fiber relation is proved for the literal
positive source, including the actual ideal-indexed sector transport. -/
theorem valid : Valid (ActualMaskReconstruction.sectorTransport K S D Γ)
    B.tuple B.outer B.newLabel B.newRow := by
  refine {
    outer_eq := rfl
    label := rfl
    j_split := ?_
    b_split := ?_
    a1 := B.A_dvd_radical B.refs.1
    a2 := B.A_dvd_radical B.refs.2
    d := B.dk_dvd
    extracted_eq := B.d₂_mul_residual
    row_eq := rfl
    sector_eq := rfl
    old_dvd := fun i => (B.old_dvd i).trans B.oldExtracted_dvd
    new_dvd := fun i => (B.new_dvd i).trans B.newExtracted_dvd }
  · exact (CubeLabels.J_eq_s_mul_J2 B.b₁.val B.b₂.val (epsilon B.refs.1) (epsilon B.refs.2)).symm
  · exact CubeLabels.actual_cube_decomposition B.b₁.val B.b₂.val
      (epsilon B.refs.1) (epsilon B.refs.2)

theorem child_eq : secondChild (ActualMaskReconstruction.sectorTransport K S D Γ) B.tuple =
    (B.outer,B.newLabel,B.newRow) := rfl

theorem outer_nonzero : B.outer.q0 ≠ 0 ∧ B.outer.quotient ≠ 0 ∧ B.outer.residual ≠ 0 :=
  ⟨B.cubeQ_ne_zero, nonZeroDivisors.coe_ne_zero B.quotient.val,
    nonZeroDivisors.coe_ne_zero B.commonResidual.val⟩

theorem newLabel_ne_zero : B.newLabel ≠ 0 :=
  mul_ne_zero (mul_ne_zero (mul_ne_zero B.cubeJ_ne_zero (primeProduct_ne_bot _))
    (nonZeroDivisors.coe_ne_zero B.d₂.val)) (nonZeroDivisors.coe_ne_zero B.overlap.val)

theorem label_squarefree_of_live (h : labelZero B.tuple ≠ 0) : Squarefree B.newLabel := by
  apply valid_label_squarefree_of_scalar_ne_zero B.valid
    (CubeLabels.J_squarefree B.b₁.val B.b₂.val (epsilon B.refs.1) (epsilon B.refs.2))
    (squarefree_primeProduct _) B.common_squarefree B.overlap_squarefree 1
  simpa only [one_mul] using h

/-- The squarefree-label zero is exactly the two zeros still present
in the genuine common-slice and positive-overlap source. -/
theorem labelZero_eq : labelZero B.tuple =
    idealCoprimeMask B.firstLabel.val.val B.common.val.val *
      SecondColumnEnergy.overlapZero K S B.common B.firstLabel B.overlap := by
  change (idealCoprimeMask B.firstCommon B.cubeJ *
    idealCoprimeMask (B.firstCommon * B.cubeJ) B.common.val.val) *
      idealCoprimeMask (B.common.val.val * B.firstCommon * B.cubeJ) B.overlap.val.val = _
  have hmask : idealCoprimeMask B.firstCommon B.cubeJ = 1 := by
    simp only [idealCoprimeMask, if_pos B.firstCommon_coprime_cubeJ.symm]
  rw [hmask, one_mul]
  unfold SecondColumnEnergy.overlapZero
  rw [B.firstLabel_val, mul_assoc]

def retainedZero (R : Ideal (𝓞 K)) : ℂ :=
  SecondSourceCharacters.commonZero K S B.common B.firstLabel
    (sIntegerMaskGenerator K Sset B.firstDivisor).val *
      idealCoprimeMask R B.common.val.val *
      SecondColumnEnergy.overlapZero K S B.common B.firstLabel B.overlap

/-- Multiplying by the label zero preserves the actual source scalar.
No new pruning or coprimality hypothesis is introduced. -/
theorem retainedZero_labelZero (R : Ideal (𝓞 K)) :
    B.retainedZero R * labelZero B.tuple = B.retainedZero R := by
  rw [B.labelZero_eq]
  by_cases hg : IsCoprime B.common.val.val B.firstLabel.val.val <;>
    by_cases hv : IsCoprime B.overlap.val.val
      (B.common.val.val * B.firstLabel.val.val) <;>
    simp [retainedZero, SecondSourceCharacters.commonZero,
      SecondColumnEnergy.overlapZero, idealCoprimeMask, hg, hv]

theorem norm_retainedZero_le_one (R : Ideal (𝓞 K)) : ‖B.retainedZero R‖ ≤ 1 := by
  unfold retainedZero SecondSourceCharacters.commonZero SecondColumnEnergy.overlapZero
    idealCoprimeMask
  split_ifs <;> norm_num

theorem label_squarefree_of_retainedZero (R : Ideal (𝓞 K))
    (hlive : B.retainedZero R ≠ 0) : Squarefree B.newLabel := by
  apply B.label_squarefree_of_live
  intro hz
  have he := B.retainedZero_labelZero R
  rw [hz, mul_zero] at he
  exact hlive he.symm

theorem core_first_support : B.tuple.core 5 = primeProduct B.extraction.1 := by
  have h := anchor_key K S N N B.b₁ B.b₂ ⟨B.extraction,B.extraction_mem⟩
  exact congrArg primeProduct (congrArg Prod.fst h)

theorem core_second_support : B.tuple.core 6 = primeProduct B.extraction.2.1 := by
  have h := anchor_key K S N N B.b₁ B.b₂ ⟨B.extraction,B.extraction_mem⟩
  exact congrArg primeProduct (congrArg (fun t : Key K => t.2.1) h)

theorem core_common_support : B.tuple.core 1 = primeProduct B.extraction.2.2 := by
  have h := anchor_key K S N N B.b₁ B.b₂ ⟨B.extraction,B.extraction_mem⟩
  exact congrArg primeProduct (congrArg (fun t : Key K => t.2.2) h)

end Source

/-- The residual columns have been eliminated before this map is
formed. Its actual key, mask choices and overlap can all be recovered
from the displayed reconstruction tuple. -/
theorem tuple_injective : Function.Injective
    (Source.tuple (K := K) (S := S) (D := D) (Γ := Γ)
      (N := N) (X := X) (oldLists := oldLists) (newLists := newLists)) := by
  intro B A h
  have hc (i : Fin 8) : B.tuple.core i = A.tuple.core i := congrArg (fun t => t.core i) h
  apply Source.ext
  · apply Subtype.ext
    apply Subtype.ext
    exact hc 4
  · apply Subtype.ext
    apply Subtype.ext
    exact congrArg SecondTuple.secondCube h
  · apply Prod.ext
    · apply ActualSourceReindexing.primeProduct_injective
      rw [← B.core_first_support, ← A.core_first_support]
      exact hc 5
    · apply Prod.ext
      · apply ActualSourceReindexing.primeProduct_injective
        rw [← B.core_second_support, ← A.core_second_support]
        exact hc 6
      · apply ActualSourceReindexing.primeProduct_injective
        rw [← B.core_common_support, ← A.core_common_support]
        exact hc 1
  · apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun t => t.outer.quotient) h
  · apply Subtype.ext
    apply Subtype.ext
    exact congrArg SecondTuple.extractedCommon h
  · apply Subtype.ext
    apply Subtype.ext
    exact congrArg SecondTuple.commonResidual h
  · apply ActualMaskReconstruction.maskIdeal_injective K S
    exact hc 7
  · apply ActualMaskReconstruction.maskIdeal_injective K S
    exact hc 2
  · apply Prod.ext
    · apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun t => t.frequency.1) h
    · exact congrArg (fun t => t.frequency.2) h
  · exact congrArg SecondTuple.oldAssigned h
  · exact congrArg SecondTuple.newAssigned h

end HeckeSkeleton.Moments.MOM_INV_STEP.PositiveReconstruction

end
