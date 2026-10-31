import HeckeSkeleton.Moments.MOM_INV_STEP.FirstColumnAssembly
import HeckeSkeleton.Moments.MOM_INV_STEP.FirstMobiusGeometry

/-!
# Actual bounds for the first extracted center parameter

The extracted factor divides an original source ideal. Every overlap
divisor divides a true left residual column. These two facts give the
uniform finite center range directly from the original annulus.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.FirstExtractedGeometry

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open FirstSourceColumns FirstColumnAssembly FirstNormPoolEnergy FirstMobiusGeometry
  CanonicalNormPools
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset

theorem extractedFactor_height_le_source (r₁ r₂ b₁ b₂ : Ext)
    (hr₁ : Squarefree r₁.val.val) (hr₂ : Squarefree r₂.val.val) (side : Bool) :
    ((extractedFactor K S r₁ r₂ b₁ b₂ side).val.val.absNorm : ℝ) ≤
      height K Sset (sourceIdeal K S r₁ r₂ side) := by
  have hf := congrArg (height K Sset)
    (source_factorization K S D r₁ r₂ b₁ b₂ hr₁ hr₂ side)
  rw [height_mul] at hf
  have he := (height_pos K Sset
    (CanonicalIdealRow.toExterior K S (extractedFactor K S r₁ r₂ b₁ b₂ side))).le
  have hu := height_one_le K Sset (residualIdeal K S D r₁ r₂ b₁ b₂ side)
  exact (le_mul_of_one_le_right he hu).trans_eq hf

theorem extractedFactor_height_le (X : {r : ℝ // 0 < r}) (r₁ r₂ b₁ b₂ : Ext)
    (hr₁ : r₁ ∈ dyadicPool K Sset X.val) (hr₂ : r₂ ∈ dyadicPool K Sset X.val)
    (side : Bool) :
    ((extractedFactor K S r₁ r₂ b₁ b₂ side).val.val.absNorm : ℝ) ≤ 2 * X.val := by
  have hsource : sourceIdeal K S r₁ r₂ side ∈ dyadicPool K Sset X.val := by
    cases side <;> assumption
  exact (extractedFactor_height_le_source K S D r₁ r₂ b₁ b₂
    (dyadicPool_squarefree K Sset hr₁) (dyadicPool_squarefree K Sset hr₂) side).trans
    ((mem_dyadicPool K Sset X.val _).mp hsource).2.2

theorem residualScale_le (X : {r : ℝ // 0 < r}) (r₁ r₂ b₁ b₂ : Ext) (side : Bool) :
    (residualScale K S X r₁ r₂ b₁ b₂ side).val ≤ X.val := by
  have he := height_pos K Sset
    (CanonicalIdealRow.toExterior K S (extractedFactor K S r₁ r₂ b₁ b₂ side))
  have heone := height_one_le K Sset
    (CanonicalIdealRow.toExterior K S (extractedFactor K S r₁ r₂ b₁ b₂ side))
  exact (div_le_iff₀ he).mpr (le_mul_of_one_le_right X.property.le heone)

theorem overlap_height_le (X : {r : ℝ // 0 < r}) (r₁ r₂ b₁ b₂ : Ext)
    (e : overlapPool K S X r₁ r₂ b₁ b₂ false) :
    height K Sset (overlapIdeal K S D X r₁ r₂ b₁ b₂ false e) ≤ 2 * X.val := by
  exact (overlap_norm_le K S D X r₁ r₂ b₁ b₂ false e.val e.property).trans
    (mul_le_mul_of_nonneg_left (residualScale_le K S X r₁ r₂ b₁ b₂ false)
      (by norm_num : (0 : ℝ) ≤ 2))

theorem extractedHeight_one_le (r₁ r₂ b₁ b₂ : Ext) (side : Bool) (e : Ext) :
    1 ≤ extractedHeight K S r₁ r₂ b₁ b₂ side e := by
  have he := height_one_le K Sset e
  have ha := height_one_le K Sset
    (CanonicalIdealRow.toExterior K S (extractedFactor K S r₁ r₂ b₁ b₂ side))
  change (1 : ℝ) ≤
    height K Sset (CanonicalIdealRow.toExterior K S (extractedFactor K S r₁ r₂ b₁ b₂ side)) *
      height K Sset e
  nlinarith

/-- A common norm range for both first positive energies, including the
right energy's divisors inherited from the full left Möbius pool. -/
theorem extractedHeight_le_square (X : {r : ℝ // 0 < r}) (r₁ r₂ b₁ b₂ : Ext)
    (hr₁ : r₁ ∈ dyadicPool K Sset X.val) (hr₂ : r₂ ∈ dyadicPool K Sset X.val)
    (side : Bool) (e : overlapPool K S X r₁ r₂ b₁ b₂ false) :
    extractedHeight K S r₁ r₂ b₁ b₂ side
      (overlapIdeal K S D X r₁ r₂ b₁ b₂ false e) ≤ (2 * X.val) ^ 2 := by
  have hleft := extractedFactor_height_le K S D X r₁ r₂ b₁ b₂ hr₁ hr₂ side
  have hright := overlap_height_le K S D X r₁ r₂ b₁ b₂ e
  exact (mul_le_mul hleft hright
    (height_pos K Sset (overlapIdeal K S D X r₁ r₂ b₁ b₂ false e)).le
    (by positivity : (0 : ℝ) ≤ 2 * X.val)).trans_eq (by ring)

end HeckeSkeleton.Moments.MOM_INV_STEP.FirstExtractedGeometry

end
