import HeckeSkeleton.Moments.MOM_INV_STEP.FirstCenteredPositiveEnergy
import HeckeSkeleton.Moments.MOM_INV_STEP.FirstPoissonNormalization
import HeckeSkeleton.Moments.MOM_INV_STEP.Normalization

/-!
# The actual first prefactor at a fixed center

The overlap norm and the centered inverse square-root norm cancel
against the original extracted factor. This connects the literal
Poisson and Mellin factors to the numerical kappa budget, without a
separately assumed physical prefactor identity.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.FirstActualPrefactor

open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Analysis
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep
open FirstSourceColumns FirstColumnAssembly FirstCenteredPositiveEnergy
  FirstPoissonNormalization CanonicalNormPools
open scoped Classical

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "Ext" => ExteriorIdeal K Sset
local notation "OS" => Set.integer Sset K

def columnScale (X v : {r : ℝ // 0 < r}) (e : Ext) : ℝ :=
  (height K Sset e)⁻¹ * ((centerScale X v).val ^ (-(1 / 2 : ℝ))) ^ 2

theorem columnScale_eq (X v : {r : ℝ // 0 < r}) (e : Ext) :
    columnScale K S X v e = v.val / (height K Sset e * X.val) := by
  have hU : ((centerScale X v).val ^ (-(1 / 2 : ℝ))) ^ 2 =
      (centerScale X v).val⁻¹ := by
    rw [Real.rpow_neg (centerScale X v).property.le, inv_pow,
      ← Real.sqrt_eq_rpow, Real.sq_sqrt (centerScale X v).property.le]
  rw [columnScale, hU]
  dsimp only [centerScale]
  field_simp [(height_pos K Sset e).ne', X.property.ne', v.property.ne']
  <;> ring

theorem columnScale_le (X v : {r : ℝ // 0 < r}) (r₁ r₂ b₁ b₂ e : Ext)
    (side : Bool) (hv : v.val ≤ extractedHeight K S r₁ r₂ b₁ b₂ side e) :
    columnScale K S X v e ≤
      ((extractedFactor K S r₁ r₂ b₁ b₂ side).val.val.absNorm : ℝ) / X.val := by
  rw [columnScale_eq]
  apply (div_le_div_of_nonneg_right hv
    (mul_nonneg (height_pos K Sset e).le X.property.le)).trans_eq
  unfold extractedHeight
  field_simp [(height_pos K Sset e).ne', X.property.ne']

variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))

def normalizedScalar (Z r ell V : ℝ) (radius X v : {r : ℝ // 0 < r})
    (d : NonzeroRingElements OS) (r₁ r₂ b₁ b₂ e : Ext) : ℝ :=
  Z ^ (-r - 2 * ell - V) * outerFactor K S D radius d r₁ r₂ b₁ b₂ *
    columnScale K S X v e

/-- Each first Cauchy side has the stated kappa budget, directly from
the actual mask, cube conductor, extracted norm and centered Mellin
factor. The allowance is the paper's 9 eta / 2 first-side cost. -/
theorem normalizedScalar_le (Z M r ell V delta A B R eta : ℝ)
    (hZ : 1 ≤ Z) (heta : 0 ≤ eta) (radius X v : {r : ℝ // 0 < r})
    (d : NonzeroRingElements OS) (r₁ r₂ b₁ b₂ e : Ext) (side : Bool)
    (hradius : radius.val = Z ^ (-M)) (hX : X.val = Z ^ r)
    (hv : v.val ≤ extractedHeight K S r₁ r₂ b₁ b₂ side e)
    (hd : Z ^ (delta - eta) ≤ (sIntegerElementNorm K Sset d).val)
    (hR : Z ^ (R - eta) ≤ cubeNorm K S D r₁ r₂ b₁ b₂)
    (hA : ((extractedFactor K S r₁ r₂ b₁ b₂ side).val.val.absNorm : ℝ) ≤
      Z ^ (A + B + 2 * eta)) :
    normalizedScalar K S D Z r ell V radius X v d r₁ r₂ b₁ b₂ e ≤
      ActualPoissonScale.fieldConstant K *
        Z ^ (firstKappa M r ell V delta A B R + 9 * eta / 2) := by
  have hZpos : 0 < Z := zero_lt_one.trans_le hZ
  have hc := columnScale_le K S X v r₁ r₂ b₁ b₂ e side hv
  have hc' : columnScale K S X v e ≤ Z ^ (A + B + 2 * eta) / Z ^ r := by
    apply hc.trans
    rw [hX]
    exact div_le_div_of_nonneg_right hA (Real.rpow_nonneg hZpos.le r)
  have hsqrt : Z ^ ((R - eta) / 2) ≤ Real.sqrt (cubeNorm K S D r₁ r₂ b₁ b₂) := by
    have h := Real.sqrt_le_sqrt hR
    simpa only [Real.sqrt_eq_rpow, ← Real.rpow_mul hZpos.le,
      div_eq_mul_inv, one_mul] using h
  have hden :
      Z ^ (-M) * Z ^ (delta - eta) * Z ^ ((R - eta) / 2) ≤
      radius.val * (sIntegerElementNorm K Sset d).val *
        Real.sqrt (cubeNorm K S D r₁ r₂ b₁ b₂) := by
    rw [hradius]
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left hd (Real.rpow_nonneg hZpos.le _))
      hsqrt (Real.rpow_nonneg hZpos.le _)
      (mul_nonneg (Real.rpow_nonneg hZpos.le _)
        (sIntegerElementNorm K Sset d).property.le)
  have hout : outerFactor K S D radius d r₁ r₂ b₁ b₂ ≤
      ActualPoissonScale.fieldConstant K /
        (Z ^ (-M) * Z ^ (delta - eta) * Z ^ ((R - eta) / 2)) :=
    div_le_div_of_nonneg_left (ActualPoissonScale.fieldConstant_nonneg K)
      (by positivity) hden
  have hsc : 0 ≤ columnScale K S X v e := by
    unfold columnScale
    exact mul_nonneg (inv_nonneg.mpr (height_pos K Sset e).le) (sq_nonneg _)
  have hbound := mul_le_mul hout hc' hsc (by
    exact div_nonneg (ActualPoissonScale.fieldConstant_nonneg K) (by positivity))
  have hn : Z ^ (-r - 2 * ell - V) *
      ((ActualPoissonScale.fieldConstant K /
        (Z ^ (-M) * Z ^ (delta - eta) * Z ^ ((R - eta) / 2))) *
        (Z ^ (A + B + 2 * eta) / Z ^ r)) =
      ActualPoissonScale.fieldConstant K *
        Z ^ (firstKappa M r ell V delta A B R + 7 * eta / 2) := by
    have hi : (Z ^ (-M) * Z ^ (delta - eta) * Z ^ ((R - eta) / 2))⁻¹ =
        Z ^ (M - delta + eta - (R - eta) / 2) := by
      rw [← Real.rpow_add hZpos, ← Real.rpow_add hZpos, ← Real.rpow_neg hZpos.le]
      congr 1
      ring
    calc
      _ = ActualPoissonScale.fieldConstant K *
          (Z ^ (-r - 2 * ell - V) *
            (Z ^ (-M) * Z ^ (delta - eta) * Z ^ ((R - eta) / 2))⁻¹ *
            (Z ^ (A + B + 2 * eta) / Z ^ r)) := by ring
      _ = _ := by
        rw [hi, ← Real.rpow_sub hZpos, ← Real.rpow_add hZpos, ← Real.rpow_add hZpos]
        congr 2
        unfold firstKappa
        ring
  calc
    normalizedScalar K S D Z r ell V radius X v d r₁ r₂ b₁ b₂ e ≤
      Z ^ (-r - 2 * ell - V) *
        ((ActualPoissonScale.fieldConstant K /
          (Z ^ (-M) * Z ^ (delta - eta) * Z ^ ((R - eta) / 2))) *
          (Z ^ (A + B + 2 * eta) / Z ^ r)) := by
      simpa only [normalizedScalar, mul_assoc] using
        mul_le_mul_of_nonneg_left hbound (Real.rpow_nonneg hZpos.le _)
    _ = _ := hn
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ (by linarith))
      (ActualPoissonScale.fieldConstant_nonneg K)

end HeckeSkeleton.Moments.MOM_INV_STEP.FirstActualPrefactor

end

