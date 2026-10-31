import HeckeSkeleton.Moments.MOM_INV_STEP.FirstParentCentering
import HeckeSkeleton.Moments.MOM_INV_STEP.FirstCenteredSpectralFiber

/-!
# The actual old-label and frequency rows of the whole first parent

The finite source index is split into its frozen arithmetic data and
its original frequency ideal with Γ sector. Changing only the original
label leaves the frozen index and all actual center assignments fixed.
The resulting row is exactly f² times the cube dilation times h.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.FirstParentRows

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.Analysis HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
  MeasureTheory DedekindZetaZeroFree.LargeSieve
open FirstParentEnergy FirstSourcePartition FirstDualTruncation FirstColumnAssembly
  FirstRowGeometry CanonicalNormPools
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset
variable {σ : Type*}

def relabel (T : FirstParentEnergy.Data K S (σ := σ)) (f : Ext) :
    FirstParentEnergy.Data K S (σ := σ) := { T with label := f }

/-- Extend an original exterior-ideal weight only to use the proved
ideal-valued fiber theorem. Its value on every true source is unchanged. -/
def idealWeight (w : Ext → ℝ) (I : Ideal (𝓞 K)) : ℝ :=
  if h : I ≠ 0 ∧ ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ I → p ∉ Sset then
    w ⟨⟨I, mem_nonZeroDivisors_of_ne_zero h.1⟩, h.2⟩
  else 0

@[simp] theorem idealWeight_apply (w : Ext → ℝ) (f : Ext) :
    idealWeight K S w f.val.val = w f := by
  rw [idealWeight, dif_pos ⟨nonZeroDivisors.coe_ne_zero f.val, f.property⟩]

variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))] [Γ.FiniteIndex]
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
local notation "Sector" => CanonicalSectors.UnitClasses K Sset Γ

/-- Every frozen first-source choice, with the moving frequency omitted. -/
abbrev OuterIndex (T : FirstParentEnergy.Data K S (σ := σ)) :=
  Σ b₁ : T.cubes, Σ b₂ : T.cubes,
    Σ κ : keys K S (columnPool K S T) (columnPool K S T) b₁.val b₂.val,
      (FirstParentRetained.actualMask K S D T.mask
        (anchor K S (columnPool K S T) (columnPool K S T) b₁.val b₂.val κ).1
        (anchor K S (columnPool K S T) (columnPool K S T) b₁.val b₂.val κ).2
        b₁.val b₂.val).powerset

def rowIndex (T : FirstParentEnergy.Data K S (σ := σ))
    (i : OuterIndex K S D T) (z : sectorCutoff K S D Γ T.frequencyBound) :
    FirstParentEnergy.Index K S D Γ T :=
  ⟨i.1, i.2.1, i.2.2.1, i.2.2.2, z⟩

def outerIndex (T : FirstParentEnergy.Data K S (σ := σ))
    (i : FirstParentEnergy.Index K S D Γ T) : OuterIndex K S D T :=
  ⟨i.1, i.2.1, i.2.2.1, i.2.2.2.1⟩

theorem sum_index {A : Type*} [AddCommMonoid A]
    (T : FirstParentEnergy.Data K S (σ := σ))
    (F : FirstParentEnergy.Index K S D Γ T → A) :
    (∑ i : FirstParentEnergy.Index K S D Γ T, F i) =
      ∑ i : OuterIndex K S D T, ∑ z : sectorCutoff K S D Γ T.frequencyBound,
        F (rowIndex K S D Γ T i z) := by
  simp only [FirstParentEnergy.Index, OuterIndex, Fintype.sum_sigma, rowIndex]

def outerAnchor (T : FirstParentEnergy.Data K S (σ := σ))
    (i : OuterIndex K S D T) : Ext × Ext :=
  anchor K S (columnPool K S T) (columnPool K S T) i.1.val i.2.1.val i.2.2.1

def cubeDilation (r₁ r₂ b₁ b₂ : Ext) : Ext :=
  CanonicalIdealRow.toExterior K S
    (CanonicalCubeLabels.dilation K S b₁ b₂
      (CanonicalConductor.squarefreeBit K S r₁) (CanonicalConductor.squarefreeBit K S r₂))

/-- This is an equality of the actual ideals used in the two source
constructions, not a fresh character or orbit identification premise. -/
theorem firstRow_eq (r₁ r₂ b₁ b₂ f z : Ext) :
    CanonicalIdealRow.toExterior K S
      (FirstColumnAssembly.firstRow K S r₁ r₂ b₁ b₂
        (CanonicalIdealRow.ofExterior K S f) (CanonicalIdealRow.ofExterior K S z)) =
      CanonicalSectorRows.firstRowIdeal K S f (cubeDilation K S r₁ r₂ b₁ b₂) z := by
  apply Subtype.ext
  apply Subtype.ext
  rw [CanonicalSectorRows.firstRowIdeal_val]
  change z.val.val * f.val.val ^ 2 *
      (CanonicalCubeLabels.dilation K S b₁ b₂
        (CanonicalConductor.squarefreeBit K S r₁) (CanonicalConductor.squarefreeBit K S r₂)).val.val =
    f.val.val ^ 2 *
      (CanonicalCubeLabels.dilation K S b₁ b₂
        (CanonicalConductor.squarefreeBit K S r₁) (CanonicalConductor.squarefreeBit K S r₂)).val.val * z.val.val
  ring

def sourceRows (L : Finset Ext) (H : ℝ) : Finset (FirstCanonicalLabel.SourcePair K S Γ) :=
  L ×ˢ sectorCutoff K S D Γ H

def rowCap (E : Ext) (F H : {r : ℝ // 0 < r}) : {r : ℝ // 0 < r} :=
  ⟨F.val ^ 2 * height K Sset E * H.val,
    mul_pos (mul_pos (sq_pos_of_pos F.property) (height_pos K Sset E)) H.property⟩

theorem sourceRows_row_bound (L : Finset Ext) (E : Ext)
    (F H : {r : ℝ // 0 < r}) (hL : ∀ f ∈ L, height K Sset f ≤ F.val)
    (y : Ext × Sector) (hy : y ∈ (sourceRows K S D Γ L H.val).image (row K S Γ E)) :
    (y.1.val.val.absNorm : ℝ) ≤ (rowCap K S E F H).val := by
  apply image_row_norm_le K S Γ E (sourceRows K S D Γ L H.val) F.val H.val
  · intro x hx
    exact hL x.1 (Finset.mem_product.mp hx).1
  · intro x hx
    have hz : x.2 ∈ sectorCutoff K S D Γ H.val := (Finset.mem_product.mp hx).2
    simpa only [sectorCutoff, orbitCutoff, Finset.mem_preimage,
      Set.Finite.mem_toFinset, Set.mem_setOf_eq, CanonicalSectors.rowOrbit_norm] using hz
  · exact hy

/-- The old beta factors remain part of the original common label weight. -/
def pairWeight (C : CanonicalBlock.ColumnData K S σ) (b₁ b₂ : Ext) (w : Ext → ℝ) : Ext → ℝ :=
  fun f => w f * ‖C.labelWeight b₁ f‖ * ‖C.labelWeight b₂ f‖

theorem pairWeight_nonneg (C : CanonicalBlock.ColumnData K S σ) (b₁ b₂ : Ext)
    (w : Ext → ℝ) (hw : ∀ f, 0 ≤ w f) (f : Ext) :
    0 ≤ pairWeight K S C b₁ b₂ w f := by
  exact mul_nonneg (mul_nonneg (hw f) (norm_nonneg _)) (norm_nonneg _)

theorem pairWeight_bound (C : CanonicalBlock.ColumnData K S σ) (b₁ b₂ : Ext)
    (L : Finset Ext) (w : Ext → ℝ) (a p : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hw : ∀ f ∈ L, w f ≤ A * ((idealDivisors f.val.val).card : ℝ) ^ a)
    (hβ₁ : ∀ f ∈ L, ‖C.labelWeight b₁ f‖ ≤ ((idealDivisors f.val.val).card : ℝ) ^ p)
    (hβ₂ : ∀ f ∈ L, ‖C.labelWeight b₂ f‖ ≤ ((idealDivisors f.val.val).card : ℝ) ^ p)
    (f : Ext) (hf : f ∈ L) :
    pairWeight K S C b₁ b₂ w f ≤ A * ((idealDivisors f.val.val).card : ℝ) ^ (a + 2 * p) := by
  unfold pairWeight
  calc
    _ ≤ (A * ((idealDivisors f.val.val).card : ℝ) ^ a) *
        ((idealDivisors f.val.val).card : ℝ) ^ p *
        ((idealDivisors f.val.val).card : ℝ) ^ p :=
      mul_le_mul (mul_le_mul (hw f hf) (hβ₁ f hf) (norm_nonneg _)
        (mul_nonneg hA (pow_nonneg (Nat.cast_nonneg _) _)))
        (hβ₂ f hf) (norm_nonneg _)
        (mul_nonneg (mul_nonneg hA (pow_nonneg (Nat.cast_nonneg _) _))
          (pow_nonneg (Nat.cast_nonneg _) _))
    _ = _ := by rw [show a + 2 * p = a + p + p by omega, pow_add, pow_add]; ring

end HeckeSkeleton.Moments.MOM_INV_STEP.FirstParentRows

end
