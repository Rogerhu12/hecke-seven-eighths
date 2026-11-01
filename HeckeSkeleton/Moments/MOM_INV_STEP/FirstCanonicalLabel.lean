import HeckeSkeleton.Moments.MOM_INV_STEP.FirstLabelFibers
import HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalSectorRows

/-!
# The first positive canonical energy loses its old label

The source consists of the actual exterior old label, the actual exterior
frequency ideal, and every original unit sector. The column coefficient
is literally μ times the fixed admissible background, the fixed puncture,
the new fourth-power label, the surviving original marks, and the norm
test. There is no free coefficient on its moving column.

The old fourth-power label character is absorbed into the actual row
ideal f² E h. The canonical character identity preserves the sector
label; it does not assert that arbitrary subgroup orbits are unchanged
by literal dilation. The proved old-label fiber bound then removes both
f and h from the positive energy while keeping their original support
and the original common weight w(f).
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.FirstCanonicalLabel

open NumberField IsDedekindDomain UniqueFactorizationMonoid
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis HeckeGeneral.ThetaSkeleton
open HeckeGeneral.ThetaSkeleton.Global
open DedekindZetaZeroFree.LargeSieve
open HeckeSkeleton.Moments.MOMInvStep
open FixedTripleFibers CanonicalChildren CanonicalSectorRows
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable (hallowed : AllowedGeneratorInput K (S : Set (HeightOneSpectrum (𝓞 K))) D)

local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset
local notation "Sector" => CanonicalSectors.UnitClasses K Sset Γ

/-- Actual exterior source ideals, with the original unit sector. -/
abbrev SourcePair := Ext × (Ext × Sector)

def encode (x : SourcePair K S Γ) : FirstLabelFibers.SourcePair K Sector :=
  ⟨x.1.val.val, (x.2.1.val.val, x.2.2)⟩

theorem encode_injective : Function.Injective (encode K S Γ) := by
  intro x y hxy
  have hf : x.1.val.val = y.1.val.val :=
    congrArg FirstLabelFibers.SourcePair.label hxy
  have hh : x.2.1.val.val = y.2.1.val.val :=
    congrArg (fun z : FirstLabelFibers.SourcePair K Sector => z.frequency.1) hxy
  have hξ : x.2.2 = y.2.2 :=
    congrArg (fun z : FirstLabelFibers.SourcePair K Sector => z.frequency.2) hxy
  exact Prod.ext (Subtype.ext (Subtype.ext hf))
    (Prod.ext (Subtype.ext (Subtype.ext hh)) hξ)

/-- The sector label is unchanged at the level of the actual canonical
column values, by `first_label_absorb`. -/
def unchangedSector : Ideal (𝓞 K) → Ideal (𝓞 K) → (Sector ≃ Sector) :=
  fun _ _ => Equiv.refl _

def newRow (E : Ext) (x : SourcePair K S Γ) : Ideal (𝓞 K) × Sector :=
  FirstLabelFibers.newRow (unchangedSector K S Γ) E.val.val (encode K S Γ x)

theorem newRow_eq (E : Ext) (x : SourcePair K S Γ) :
    newRow K S Γ E x =
      ((firstRowIdeal K S x.1 E x.2.1).val.val, x.2.2) := by
  simp only [newRow, FirstLabelFibers.newRow, encode, unchangedSector,
    Equiv.refl_apply, firstRowIdeal_val]

theorem newRow_ne_zero (E : Ext) (x : SourcePair K S Γ) :
    (newRow K S Γ E x).1 ≠ 0 := by
  rw [newRow_eq]
  exact nonZeroDivisors.coe_ne_zero (firstRowIdeal K S x.1 E x.2.1).val

variable {σ : Type*} {Θ : Subgroup (HeckeCharacter K)} {ψ : HeckeCharacter K}

/-- The first inverse coefficient, with all data fixed over its moving
row and old label. Its new averaged label j also remains fixed here. -/
def inverseCoefficient (C : ColumnFamily K Sset σ Θ ψ)
    (γ : OuterTriple K) (j : Ideal (𝓞 K)) (n : Ext) : ℂ :=
  (moebius n.val.val : ℂ) * heckeIdealCoefficient K (C.background γ) n.val *
    (if IsCoprime n.val.val (childPuncture C.originalPuncture γ) then 1 else 0) *
    labelRow K Sset D n j ^ 4 *
    divisorMark (C.survivors γ) C.primeLists C.primeWeights n.val.val *
    C.cutoff γ ((n.val.val.absNorm : ℝ) / C.base ^ C.columnLength γ)

def inverseColumn (C : ColumnFamily K Sset σ Θ ψ)
    (γ : OuterTriple K) (j : Ideal (𝓞 K)) (y : Ideal (𝓞 K) × Sector) : ℂ :=
  ∑ n ∈ C.columns γ, inverseCoefficient K S D C γ j n *
    star (sectorRow K Sset D (CanonicalSectors.sectorUnit K Sset Γ) n y)

/-- The old label character and the old frequency still occur in this
literal source column, before positive old-label reindexing. -/
def oldAmplitude (C : ColumnFamily K Sset σ Θ ψ)
    (γ : OuterTriple K) (j : Ideal (𝓞 K)) (E : Ext)
    (x : SourcePair K S Γ) : ℂ :=
  ∑ n ∈ C.columns γ, inverseCoefficient K S D C γ j n *
    idealSymbol K Sset D n (D.generator x.1) ^ 4 *
    star (sectorCharacter K S Γ D n (exteriorMul K Sset E x.2.1) x.2.2)

include hallowed in
/-- Exact absorption into the actual canonical row, including all
coprimality zeros and every original sector. -/
theorem oldAmplitude_eq (C : ColumnFamily K Sset σ Θ ψ)
    (γ : OuterTriple K) (j : Ideal (𝓞 K)) (E : Ext)
    (x : SourcePair K S Γ) :
    oldAmplitude K S Γ D C γ j E x =
      inverseColumn K S Γ D C γ j (newRow K S Γ E x) := by
  unfold oldAmplitude inverseColumn
  apply Finset.sum_congr rfl
  intro n hn
  rw [newRow_eq, child_sectorRow]
  rw [mul_assoc, first_label_absorb K S Γ D hallowed]

include hallowed in
/-- The first actual positive inverse energy has no old label or old
frequency after reindexing. The old support may retain all masks and
annular conditions, and its weight is still one function of f alone.
Only the new row acquires the proved divisor weight. -/
theorem first_source_energy (C : ColumnFamily K Sset σ Θ ψ)
    (γ : OuterTriple K) (j : Ideal (𝓞 K)) (E : Ext)
    (T : Finset (SourcePair K S Γ))
    (w : Ideal (𝓞 K) → ℝ) (d : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hw : ∀ x ∈ T, w x.1.val.val ≤ A * ((idealDivisors x.1.val.val).card : ℝ) ^ d) :
    (∑ x ∈ T, w x.1.val.val * ‖oldAmplitude K S Γ D C γ j E x‖ ^ 2) ≤
      ∑ y ∈ T.image (newRow K S Γ E),
        (A * ((idealDivisors y.1).card : ℝ) ^ (d + 1)) *
          ‖inverseColumn K S Γ D C γ j y‖ ^ 2 := by
  let T' := T.image (encode K S Γ)
  have hw' : ∀ x ∈ T', w x.label ≤ A * ((idealDivisors x.label).card : ℝ) ^ d := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    exact hw z hz
  have hrow' : ∀ x ∈ T',
      (FirstLabelFibers.newRow (unchangedSector K S Γ) E.val.val x).1 ≠ 0 := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    exact newRow_ne_zero K S Γ E z
  have hb := FirstLabelFibers.source_energy_bound
    (sectorTransport := unchangedSector K S Γ) T' E.val.val w d A hA hw' hrow'
    (fun y => ‖inverseColumn K S Γ D C γ j y‖ ^ 2) (fun _ _ => sq_nonneg _)
  have hsum :
      (∑ x ∈ T', w x.label *
        ‖inverseColumn K S Γ D C γ j
          (FirstLabelFibers.newRow (unchangedSector K S Γ) E.val.val x)‖ ^ 2) =
      ∑ x ∈ T, w x.1.val.val * ‖oldAmplitude K S Γ D C γ j E x‖ ^ 2 := by
    dsimp only [T']
    rw [Finset.sum_image (fun _ _ _ _ h => encode_injective K S Γ h)]
    apply Finset.sum_congr rfl
    intro x hx
    rw [oldAmplitude_eq K S Γ D hallowed]
    rfl
  rw [hsum] at hb
  refine hb.trans_eq ?_
  apply Finset.sum_congr ?_ (fun _ _ => rfl)
  ext y
  simp only [T', Finset.mem_image]
  constructor
  · rintro ⟨x, ⟨z, hz, rfl⟩, he⟩
    exact ⟨z, hz, he⟩
  · rintro ⟨z, hz, he⟩
    exact ⟨encode K S Γ z, ⟨z, hz, rfl⟩, he⟩

end HeckeSkeleton.Moments.MOM_INV_STEP.FirstCanonicalLabel

end
