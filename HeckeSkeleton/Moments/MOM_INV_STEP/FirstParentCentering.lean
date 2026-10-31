import HeckeSkeleton.Moments.MOM_INV_STEP.FirstParentProduction
import HeckeSkeleton.Moments.MOM_INV_STEP.FirstExtractedGeometry
import HeckeSkeleton.Moments.MOM_INV_STEP.DyadicSourcePartition

/-!
# The actual fixed grid for the first parent

The grid depends only on the base and two uniform exponent bounds. Every
actual extracted factor and every overlap divisor merely selects a bin
of that fixed grid. The two source columns share the left overlap pool;
the proof does not assume that its divisors occur in the right pool.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.FirstParentCentering

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.Analysis HeckeGeneral.Bridge HeckeGeneral.ThetaSkeleton
  HeckeGeneral.ThetaSkeleton.Global MeasureTheory
open FirstParentEnergy FirstNormPoolEnergy FirstMobiusGeometry FirstColumnAssembly
  FirstExtractedGeometry CanonicalNormPools
open scoped Classical BigOperators nonZeroDivisors

abbrev CenterIndex (Z lengthCap eta : ℝ) :=
  DyadicSourcePartition.Index Z (2 * lengthCap) (2 * eta)

/-- Every center is fixed before the source data and its extraction keys. -/
def grid (Z lengthCap eta : ℝ) (j : CenterIndex Z lengthCap eta) :
    {r : ℝ // 0 < r} :=
  ⟨DyadicSourcePartition.center j.val, DyadicSourcePartition.center_pos j.val⟩

theorem grid_one_le (Z lengthCap eta : ℝ) (j : CenterIndex Z lengthCap eta) :
    1 ≤ (grid Z lengthCap eta j).val := DyadicSourcePartition.one_le_center _

theorem exists_grid_count_bound (lengthCap eta pi : ℝ)
    (hcap : 0 ≤ lengthCap + eta) (hpi : 0 < pi) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ Z : ℝ, 1 ≤ Z →
      (Fintype.card (CenterIndex Z lengthCap eta) : ℝ) ≤ C * Z ^ pi :=
  DyadicSourcePartition.exists_bin_count_bound (2 * lengthCap) (2 * eta) pi
    (by linarith) hpi

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
  [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))] [Γ.FiniteIndex]
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
variable {σ : Type*}

local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))

abbrev Overlap (T : FirstParentEnergy.Data K S (σ := σ))
    (i : FirstParentEnergy.Index K S D Γ T) :=
  overlapPool K S T.scale (selectedAnchor K S D Γ T i).1
    (selectedAnchor K S D Γ T i).2 i.1.val i.2.1.val false

def extractedNorm (T : FirstParentEnergy.Data K S (σ := σ)) (side : Bool)
    (i : FirstParentEnergy.Index K S D Γ T) (e : Overlap K S D Γ T i) : ℝ :=
  extractedHeight K S (selectedAnchor K S D Γ T i).1
    (selectedAnchor K S D Γ T i).2 i.1.val i.2.1.val side
    (overlapIdeal K S D T.scale (selectedAnchor K S D Γ T i).1
      (selectedAnchor K S D Γ T i).2 i.1.val i.2.1.val false e)

theorem selectedAnchor_mem (T : FirstParentEnergy.Data K S (σ := σ))
    (i : FirstParentEnergy.Index K S D Γ T) :
    (selectedAnchor K S D Γ T i).1 ∈ dyadicPool K Sset T.scale.val ∧
      (selectedAnchor K S D Γ T i).2 ∈ dyadicPool K Sset T.scale.val := by
  exact FirstSourcePartition.anchor_mem K S (columnPool K S T) (columnPool K S T)
    i.1.val i.2.1.val i.2.2.1

theorem extractedNorm_one_le (T : FirstParentEnergy.Data K S (σ := σ)) (side : Bool)
    (i : FirstParentEnergy.Index K S D Γ T) (e : Overlap K S D Γ T i) :
    1 ≤ extractedNorm K S D Γ T side i e :=
  extractedHeight_one_le K S _ _ _ _ side _

theorem extractedNorm_le_square (T : FirstParentEnergy.Data K S (σ := σ)) (side : Bool)
    (i : FirstParentEnergy.Index K S D Γ T) (e : Overlap K S D Γ T i) :
    extractedNorm K S D Γ T side i e ≤ (2 * T.scale.val) ^ 2 := by
  obtain ⟨hleft, hright⟩ := selectedAnchor_mem K S D Γ T i
  exact extractedHeight_le_square K S D T.scale _ _ _ _ hleft hright side e

def assignment (Z lengthCap eta : ℝ) (T : FirstParentEnergy.Data K S (σ := σ))
    (side : Bool) (i : FirstParentEnergy.Index K S D Γ T)
    (e : Overlap K S D Γ T i) : CenterIndex Z lengthCap eta :=
  DyadicSourcePartition.label Z (2 * lengthCap) (2 * eta)
    (extractedNorm K S D Γ T side i e)

theorem assignment_bounds (Z lengthCap eta : ℝ) (hZ : 0 < Z)
    (hwidth : 2 ≤ Z ^ eta) (T : FirstParentEnergy.Data K S (σ := σ))
    (hscale : T.scale.val ≤ Z ^ lengthCap) (side : Bool)
    (i : FirstParentEnergy.Index K S D Γ T) (e : Overlap K S D Γ T i) :
    (grid Z lengthCap eta (assignment K S D Γ Z lengthCap eta T side i e)).val ≤
        extractedNorm K S D Γ T side i e ∧
      extractedNorm K S D Γ T side i e ≤
        2 * (grid Z lengthCap eta (assignment K S D Γ Z lengthCap eta T side i e)).val :=
  DyadicSourcePartition.quadratic_source_label_bounds Z lengthCap eta T.scale.val
    (extractedNorm K S D Γ T side i e) hZ hwidth T.scale.property.le hscale
    (extractedNorm_one_le K S D Γ T side i e)
    (extractedNorm_le_square K S D Γ T side i e)

/-- A constructed production centering, with no geometric or energy
input beyond the actual original source window. -/
def centering (Z lengthCap eta : ℝ) (hZ : 0 < Z) (hwidth : 2 ≤ Z ^ eta)
    (T : FirstParentEnergy.Data K S (σ := σ)) (hscale : T.scale.val ≤ Z ^ lengthCap) :
    FirstParentProduction.Centering K S D Γ T (grid Z lengthCap eta) where
  assignment := assignment K S D Γ Z lengthCap eta T
  lower := fun side i e =>
    (assignment_bounds K S D Γ Z lengthCap eta hZ hwidth T hscale side i e).1
  upper := fun side i e =>
    (assignment_bounds K S D Γ Z lengthCap eta hZ hwidth T hscale side i e).2

theorem assignment_ratio (Z lengthCap eta : ℝ) (hZ : 0 < Z)
    (hwidth : 2 ≤ Z ^ eta) (T : FirstParentEnergy.Data K S (σ := σ))
    (hscale : T.scale.val ≤ Z ^ lengthCap) (side : Bool)
    (i : FirstParentEnergy.Index K S D Γ T) (e : Overlap K S D Γ T i) :
    extractedNorm K S D Γ T side i e /
        (grid Z lengthCap eta (assignment K S D Γ Z lengthCap eta T side i e)).val ∈
      Set.Icc (1 : ℝ) 2 := by
  obtain ⟨hl, hu⟩ := assignment_bounds K S D Γ Z lengthCap eta hZ hwidth T hscale side i e
  have hp := (grid Z lengthCap eta (assignment K S D Γ Z lengthCap eta T side i e)).property
  exact ⟨(le_div_iff₀ hp).mpr (by simpa only [one_mul] using hl),
    (div_le_iff₀ hp).mpr hu⟩

end HeckeSkeleton.Moments.MOM_INV_STEP.FirstParentCentering

end
