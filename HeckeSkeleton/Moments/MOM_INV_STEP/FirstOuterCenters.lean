import HeckeSkeleton.Moments.MOM_INV_STEP.FirstParentRows

/-! # Fixed first column centers before any old label or dual frequency -/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.FirstOuterCenters

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open FirstParentRows FirstMobiusGeometry FirstColumnAssembly FirstExtractedGeometry
  CanonicalNormPools
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
variable {σ ι : Type*} [Fintype ι]

abbrev Overlap (T : FirstParentEnergy.Data K S (σ := σ)) (o : OuterIndex K S D T) :=
  overlapPool K S T.scale (outerAnchor K S D T o).1 (outerAnchor K S D T o).2
    o.1.val o.2.1.val false

def extractedNorm (T : FirstParentEnergy.Data K S (σ := σ)) (side : Bool)
    (o : OuterIndex K S D T) (e : Overlap K S D T o) : ℝ :=
  extractedHeight K S (outerAnchor K S D T o).1 (outerAnchor K S D T o).2
    o.1.val o.2.1.val side
    (overlapIdeal K S D T.scale (outerAnchor K S D T o).1 (outerAnchor K S D T o).2
      o.1.val o.2.1.val false e)

structure Centering (T : FirstParentEnergy.Data K S (σ := σ))
    (grid : ι → {r : ℝ // 0 < r}) where
  assignment : ∀ side : Bool, ∀ o : OuterIndex K S D T, Overlap K S D T o → ι
  lower : ∀ side o e, (grid (assignment side o e)).val ≤ extractedNorm K S D T side o e
  upper : ∀ side o e, extractedNorm K S D T side o e ≤ 2 * (grid (assignment side o e)).val

def Centering.at (T : FirstParentEnergy.Data K S (σ := σ))
    (grid : ι → {r : ℝ // 0 < r}) (centers : Centering K S D T grid)
    (side : Bool) (o : OuterIndex K S D T) :
    FirstCenteredPositiveEnergy.Centering K S D ι T.scale
      (outerAnchor K S D T o).1 (outerAnchor K S D T o).2 o.1.val o.2.1.val side where
  center := grid
  assignment := centers.assignment side o
  lower := centers.lower side o
  upper := centers.upper side o

theorem anchor_mem (T : FirstParentEnergy.Data K S (σ := σ)) (o : OuterIndex K S D T) :
    (outerAnchor K S D T o).1 ∈ dyadicPool K (S : Set (HeightOneSpectrum (𝓞 K))) T.scale.val ∧
      (outerAnchor K S D T o).2 ∈ dyadicPool K (S : Set (HeightOneSpectrum (𝓞 K))) T.scale.val :=
  FirstSourcePartition.anchor_mem K S (FirstParentEnergy.columnPool K S T)
    (FirstParentEnergy.columnPool K S T) o.1.val o.2.1.val o.2.2.1

theorem extractedNorm_bounds (T : FirstParentEnergy.Data K S (σ := σ)) (side : Bool)
    (o : OuterIndex K S D T) (e : Overlap K S D T o) :
    1 ≤ extractedNorm K S D T side o e ∧
      extractedNorm K S D T side o e ≤ (2 * T.scale.val) ^ 2 := by
  obtain ⟨h₁, h₂⟩ := anchor_mem K S D T o
  exact ⟨extractedHeight_one_le K S _ _ _ _ side _,
    extractedHeight_le_square K S D T.scale _ _ _ _ h₁ h₂ side e⟩

/-- This assignment is constructed from the actual extracted ideal norm.
The complete grid is fixed before all labels and frequency rows. -/
def canonical (Z cap eta : ℝ) (hZ : 0 < Z) (hwidth : 2 ≤ Z ^ eta)
    (T : FirstParentEnergy.Data K S (σ := σ)) (hscale : T.scale.val ≤ Z ^ cap) :
    Centering K S D T (FirstParentCentering.grid Z cap eta) where
  assignment := fun side o e => DyadicSourcePartition.label Z (2 * cap) (2 * eta)
    (extractedNorm K S D T side o e)
  lower := fun side o e =>
    (DyadicSourcePartition.quadratic_source_label_bounds Z cap eta T.scale.val
      (extractedNorm K S D T side o e) hZ hwidth T.scale.property.le hscale
      (extractedNorm_bounds K S D T side o e).1
      (extractedNorm_bounds K S D T side o e).2).1
  upper := fun side o e =>
    (DyadicSourcePartition.quadratic_source_label_bounds Z cap eta T.scale.val
      (extractedNorm K S D T side o e) hZ hwidth T.scale.property.le hscale
      (extractedNorm_bounds K S D T side o e).1
      (extractedNorm_bounds K S D T side o e).2).2

end HeckeSkeleton.Moments.MOM_INV_STEP.FirstOuterCenters

end
