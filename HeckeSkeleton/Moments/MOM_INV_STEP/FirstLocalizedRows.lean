import HeckeSkeleton.Moments.MOM_INV_STEP.FirstCubeDilationGeometry
import HeckeSkeleton.Moments.MOM_INV_STEP.FirstLocalizedCutoff
import HeckeSkeleton.Moments.MOM_INV_STEP.Normalization

/-!
# The actual first rows fit the fixed second-Poisson scale

The cube digit table cancels the two extracted A factors against the
true first-conductor/cube-dilation product. Thus the free row majorant
may be chosen at the fixed annular upper endpoint before the second
Poisson transform. The later physical radius is the inverse of this
chosen endpoint, rather than the inverse of a varying source norm.
-/

noncomputable section
namespace HeckeSkeleton.Moments.MOM_INV_STEP.FirstLocalizedRows
open NumberField IsDedekindDomain HeckeGeneral.Arithmetic HeckeGeneral.Characters
  HeckeGeneral.Analysis HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
  MeasureTheory
open FirstParentRows FirstSourceColumns FirstPoissonNormalization FirstNormPoolEnergy
  FirstLocalizedCutoff CanonicalNormPools
open HeckeSkeleton.Moments.MOMInvStep
open scoped Classical BigOperators nonZeroDivisors

private theorem ratio_bound (E R J B A₁ A₂ C : ℝ)
    (hA₁ : 0 < A₁) (hA₂ : 0 < A₂) (hC : 0 < C) (hJ : 0 < J)
    (h : E * R * J ≤ B ^ 2 * A₁ * A₂) :
    E * R / ((A₁ * C) * (A₂ * C)) ≤ B ^ 2 / (C ^ 2 * J) := by
  apply (div_le_div_iff₀
    (mul_pos (mul_pos hA₁ hC) (mul_pos hA₂ hC))
    (mul_pos (sq_pos_of_pos hC) hJ)).mpr
  have hh := mul_le_mul_of_nonneg_right h (sq_nonneg C)
  convert hh using 1 <;> ring

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable (D : ThetaArithmeticData K (S : Set (HeightOneSpectrum (𝓞 K))))
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer Sset K
local notation "Ext" => ExteriorIdeal K Sset

def aNorm (r₁ r₂ b₁ b₂ : Ext) (side : Bool) : ℝ :=
  ((CanonicalCubeLabels.A K S b₁ b₂
    (CanonicalConductor.squarefreeBit K S (sourceIdeal K S r₁ r₂ side))).val.val.absNorm : ℝ)

def commonNorm (r₁ r₂ b₁ b₂ : Ext) : ℝ :=
  height K Sset (commonIdeal K S r₁ r₂ b₁ b₂)

def labelNorm (r₁ r₂ b₁ b₂ : Ext) : ℝ :=
  ((CanonicalCubeLabels.J K S b₁ b₂
    (CanonicalConductor.squarefreeBit K S r₁)
    (CanonicalConductor.squarefreeBit K S r₂)).val.val.absNorm : ℝ)

theorem aNorm_pos (r₁ r₂ b₁ b₂ : Ext) (side : Bool) :
    0 < aNorm K S r₁ r₂ b₁ b₂ side := by
  unfold aNorm
  exact_mod_cast (Ideal.absNorm_pos_of_nonZeroDivisors
    (CanonicalCubeLabels.A K S b₁ b₂
      (CanonicalConductor.squarefreeBit K S (sourceIdeal K S r₁ r₂ side))).val)

theorem commonNorm_pos (r₁ r₂ b₁ b₂ : Ext) : 0 < commonNorm K S r₁ r₂ b₁ b₂ :=
  height_pos K Sset (commonIdeal K S r₁ r₂ b₁ b₂)

theorem labelNorm_pos (r₁ r₂ b₁ b₂ : Ext) : 0 < labelNorm K S r₁ r₂ b₁ b₂ := by
  unfold labelNorm
  exact_mod_cast (Ideal.absNorm_pos_of_nonZeroDivisors
    (CanonicalCubeLabels.J K S b₁ b₂
      (CanonicalConductor.squarefreeBit K S r₁) (CanonicalConductor.squarefreeBit K S r₂)).val)

theorem extracted_norm (r₁ r₂ b₁ b₂ : Ext) (side : Bool) :
    ((extractedFactor K S r₁ r₂ b₁ b₂ side).val.val.absNorm : ℝ) =
      aNorm K S r₁ r₂ b₁ b₂ side * commonNorm K S r₁ r₂ b₁ b₂ := by
  change (((CanonicalCubeLabels.A K S b₁ b₂
    (CanonicalConductor.squarefreeBit K S (sourceIdeal K S r₁ r₂ side))).val.val *
      (commonIdeal K S r₁ r₂ b₁ b₂).val.val).absNorm : ℝ) = _
  simp only [map_mul, Nat.cast_mul, aNorm, commonNorm, height]

/-- The cancellation uses the actual local cube table and both actual
extracted factors. No logarithmic exponent identity is assumed. -/
theorem fine_row_bound (r X F : {r : ℝ // 0 < r}) (Z tau : ℝ) (hZ : 0 < Z)
    (r₁ r₂ b₁ b₂ : Ext) (δ : Finset (HeightOneSpectrum OS)) :
    F.val ^ 2 * height K Sset (cubeDilation K S r₁ r₂ b₁ b₂) *
      fineCutoff K S D r X Z tau r₁ r₂ b₁ b₂ δ ≤
    4 * F.val ^ 2 * r.val * (sIntegerElementNorm K Sset (sIntegerMaskGenerator K Sset δ)).val *
      (height K Sset b₁ * height K Sset b₂) ^ 2 * X.val ^ 2 /
        (commonNorm K S r₁ r₂ b₁ b₂ ^ 2 * labelNorm K S r₁ r₂ b₁ b₂) * Z ^ tau := by
  let E := height K Sset (cubeDilation K S r₁ r₂ b₁ b₂)
  let R := cubeNorm K S D r₁ r₂ b₁ b₂
  let J := labelNorm K S r₁ r₂ b₁ b₂
  let B := height K Sset b₁ * height K Sset b₂
  let A₁ := aNorm K S r₁ r₂ b₁ b₂ false
  let A₂ := aNorm K S r₁ r₂ b₁ b₂ true
  let C := commonNorm K S r₁ r₂ b₁ b₂
  let d := (sIntegerElementNorm K Sset (sIntegerMaskGenerator K Sset δ)).val
  have hA₁ : 0 < A₁ := aNorm_pos K S r₁ r₂ b₁ b₂ false
  have hA₂ : 0 < A₂ := aNorm_pos K S r₁ r₂ b₁ b₂ true
  have hC : 0 < C := commonNorm_pos K S r₁ r₂ b₁ b₂
  have hJ : 0 < J := labelNorm_pos K S r₁ r₂ b₁ b₂
  have hd : 0 < d := (sIntegerElementNorm K Sset (sIntegerMaskGenerator K Sset δ)).property
  have hb : E * R * J ≤ B ^ 2 * A₁ * A₂ :=
    FirstCubeDilationGeometry.norm_bound K S D r₁ r₂ b₁ b₂
  have hratio := ratio_bound E R J B A₁ A₂ C hA₁ hA₂ hC hJ hb
  have hfactor : 0 ≤ 4 * F.val ^ 2 * r.val * d * X.val ^ 2 * Z ^ tau :=
    mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (sq_nonneg F.val))
            r.property.le)
          hd.le)
        (sq_nonneg X.val))
      (Real.rpow_nonneg hZ.le tau)
  calc
    _ = (4 * F.val ^ 2 * r.val * d * X.val ^ 2 * Z ^ tau) *
        (E * R / ((A₁ * C) * (A₂ * C))) := by
      unfold fineCutoff FirstCommonEnvelope.radialScale residualScale
      rw [extracted_norm, extracted_norm]
      dsimp only [A₁, A₂, C, E, R, d]
      field_simp [(aNorm_pos K S r₁ r₂ b₁ b₂ false).ne',
        (aNorm_pos K S r₁ r₂ b₁ b₂ true).ne', (commonNorm_pos K S r₁ r₂ b₁ b₂).ne']
      <;> ring
    _ ≤ (4 * F.val ^ 2 * r.val * d * X.val ^ 2 * Z ^ tau) * (B ^ 2 / (C ^ 2 * J)) :=
      mul_le_mul_of_nonneg_left hratio hfactor
    _ = _ := by dsimp only [B, C, J, d]; ring

/-- With ordinary width-eta source annuli, the fixed free row endpoint
has exactly the first physical exponent plus its twelve eta allowance. -/
theorem fine_row_rpow_bound (radius X F : {r : ℝ // 0 < r})
    (Z M r ell V delta B j eta tau : ℝ) (hZ : 1 ≤ Z) (hη : 0 ≤ eta)
    (hwidth : 2 ≤ Z ^ eta)
    (hr : radius.val = Z ^ (-M)) (hX : X.val = Z ^ r)
    (hF : F.val ≤ Z ^ (V + eta))
    (r₁ r₂ b₁ b₂ : Ext) (δ : Finset (HeightOneSpectrum OS))
    (hd : (sIntegerElementNorm K Sset (sIntegerMaskGenerator K Sset δ)).val ≤
      Z ^ (delta + eta))
    (hb₁ : height K Sset b₁ ≤ Z ^ (ell + eta))
    (hb₂ : height K Sset b₂ ≤ Z ^ (ell + eta))
    (hC : Z ^ (B - eta) ≤ commonNorm K S r₁ r₂ b₁ b₂)
    (hJ : Z ^ (j - eta) ≤ labelNorm K S r₁ r₂ b₁ b₂) :
    F.val ^ 2 * height K Sset (cubeDilation K S r₁ r₂ b₁ b₂) *
      fineCutoff K S D radius X Z tau r₁ r₂ b₁ b₂ δ ≤
      Z ^ (firstPhysicalHeight M r ell V delta B j + 12 * eta + tau) := by
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  have hc := commonNorm_pos K S r₁ r₂ b₁ b₂
  have hj := labelNorm_pos K S r₁ r₂ b₁ b₂
  have hsquare (u : ℝ) : (Z ^ u) ^ 2 = Z ^ (2 * u) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hz.le]
    congr 1
    ring
  have hformula :
      4 * (Z ^ (V + eta)) ^ 2 * Z ^ (-M) * Z ^ (delta + eta) *
        (Z ^ (ell + eta) * Z ^ (ell + eta)) ^ 2 * (Z ^ r) ^ 2 /
          ((Z ^ (B - eta)) ^ 2 * Z ^ (j - eta)) * Z ^ tau =
        4 * Z ^ (firstPhysicalHeight M r ell V delta B j + 10 * eta + tau) := by
    rw [← Real.rpow_add hz, hsquare, hsquare, hsquare, hsquare]
    calc
      _ = 4 * (Z ^ (2 * (V + eta)) * Z ^ (-M) * Z ^ (delta + eta) *
          Z ^ (2 * (ell + eta + (ell + eta))) * Z ^ (2 * r) /
          (Z ^ (2 * (B - eta)) * Z ^ (j - eta)) * Z ^ tau) := by ring
      _ = _ := by
        simp only [← Real.rpow_add hz, ← Real.rpow_sub hz]
        congr 1
        unfold firstPhysicalHeight
        congr 1
        ring
  have hfour : 4 ≤ Z ^ (2 * eta) := by
    calc
      (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
      _ ≤ (Z ^ eta) ^ 2 := pow_le_pow_left₀ (by norm_num) hwidth 2
      _ = _ := hsquare eta
  apply (fine_row_bound K S D radius X F Z tau hz r₁ r₂ b₁ b₂ δ).trans
  calc
    _ ≤ 4 * (Z ^ (V + eta)) ^ 2 * Z ^ (-M) * Z ^ (delta + eta) *
        (Z ^ (ell + eta) * Z ^ (ell + eta)) ^ 2 * (Z ^ r) ^ 2 /
          ((Z ^ (B - eta)) ^ 2 * Z ^ (j - eta)) * Z ^ tau := by
      rw [hr, hX]
      have hF0 : 0 ≤ F.val := F.property.le
      have hd0 : 0 ≤ (sIntegerElementNorm K Sset (sIntegerMaskGenerator K Sset δ)).val :=
        (sIntegerElementNorm K Sset (sIntegerMaskGenerator K Sset δ)).property.le
      have hb₁0 : 0 ≤ height K Sset b₁ := (height_pos K Sset b₁).le
      have hb₂0 : 0 ≤ height K Sset b₂ := (height_pos K Sset b₂).le
      gcongr
    _ = _ := hformula
    _ ≤ Z ^ (2 * eta) *
        Z ^ (firstPhysicalHeight M r ell V delta B j + 10 * eta + tau) :=
      mul_le_mul_of_nonneg_right hfour (Real.rpow_nonneg hz.le _)
    _ = _ := by
      rw [← Real.rpow_add hz]
      congr 1
      ring

end HeckeSkeleton.Moments.MOM_INV_STEP.FirstLocalizedRows
end

