import HeckeSkeleton.Moments.MOM_INV_STEP.FirstCanonicalLabel
import HeckeSkeleton.Moments.MOM_INV_STEP.CanonicalNormPools

/-!
# Actual height geometry of the first positive rows

The row is the literal exterior ideal f² E h with its original Γ sector.
Only multiplication of actual ideal norms is used; the first mask
divisor remains in the column and does not create an extra d⁵ factor.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.FirstRowGeometry

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open CanonicalNormPools CanonicalSectorRows
open scoped Classical BigOperators nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K))

local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset
local notation "Sector" => CanonicalSectors.UnitClasses K Sset Γ

def row (E : Ext) (x : FirstCanonicalLabel.SourcePair K S Γ) : Ext × Sector :=
  (firstRowIdeal K S x.1 E x.2.1, x.2.2)

def forget (y : Ext × Sector) : Ideal (𝓞 K) × Sector := (y.1.val.val, y.2)

theorem forget_injective : Function.Injective (forget K S Γ) := by
  rintro ⟨I,ξ⟩ ⟨J,η⟩ h
  apply Prod.ext
  · exact Subtype.ext (Subtype.ext
      (congrArg (fun y : Ideal (𝓞 K) × Sector => y.1) h))
  · exact congrArg (fun y : Ideal (𝓞 K) × Sector => y.2) h

theorem newRow_eq (E : Ext) (x : FirstCanonicalLabel.SourcePair K S Γ) :
    FirstCanonicalLabel.newRow K S Γ E x = forget K S Γ (row K S Γ E x) :=
  FirstCanonicalLabel.newRow_eq K S Γ E x

theorem image_newRow (E : Ext) (T : Finset (FirstCanonicalLabel.SourcePair K S Γ)) :
    T.image (FirstCanonicalLabel.newRow K S Γ E) =
      (T.image (row K S Γ E)).image (forget K S Γ) := by
  rw [Finset.image_image]
  congr 1
  funext x
  exact newRow_eq K S Γ E x

theorem row_norm (E : Ext) (x : FirstCanonicalLabel.SourcePair K S Γ) :
    ((row K S Γ E x).1.val.val.absNorm : ℝ) =
      (x.1.val.val.absNorm : ℝ) ^ 2 * (E.val.val.absNorm : ℝ) *
        (x.2.1.val.val.absNorm : ℝ) := by
  change ((firstRowIdeal K S x.1 E x.2.1).val.val.absNorm : ℝ) = _
  rw [firstRowIdeal_val]
  simp only [map_mul, map_pow, Nat.cast_mul, Nat.cast_pow]

theorem row_norm_le (E : Ext) (x : FirstCanonicalLabel.SourcePair K S Γ)
    (F H : ℝ) (hF : (x.1.val.val.absNorm : ℝ) ≤ F)
    (hH : (x.2.1.val.val.absNorm : ℝ) ≤ H) :
    ((row K S Γ E x).1.val.val.absNorm : ℝ) ≤
      F ^ 2 * (E.val.val.absNorm : ℝ) * H := by
  rw [row_norm]
  exact mul_le_mul
    (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (Nat.cast_nonneg _) hF 2) (Nat.cast_nonneg _))
    hH (Nat.cast_nonneg _) (mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _))

theorem image_row_norm_le (E : Ext) (T : Finset (FirstCanonicalLabel.SourcePair K S Γ))
    (F H : ℝ)
    (hF : ∀ x ∈ T, (x.1.val.val.absNorm : ℝ) ≤ F)
    (hH : ∀ x ∈ T, (x.2.1.val.val.absNorm : ℝ) ≤ H)
    (y : Ext × Sector) (hy : y ∈ T.image (row K S Γ E)) :
    (y.1.val.val.absNorm : ℝ) ≤ F ^ 2 * (E.val.val.absNorm : ℝ) * H := by
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
  exact row_norm_le K S Γ E x F H (hF x hx) (hH x hx)

end HeckeSkeleton.Moments.MOM_INV_STEP.FirstRowGeometry

end

