import HeckeSkeleton.Moments.MOM_INV_STEP.SecondAdaptiveRetained

/-!
# Child row length from the genuine second local cutoff

The factor N(g)⁻² is retained until the actual second divisor and
frequency have been reconstructed. The resulting child row is d₁d₂k;
its norm bound follows from that equality and the literal fine cutoff.
-/

noncomputable section

namespace HeckeSkeleton.Moments.MOM_INV_STEP.SecondAdaptiveRows

open NumberField IsDedekindDomain HeckePort.Moments
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Characters
  HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.Moments.MOMInvStep
open CanonicalNormPools ActualDivisorSectors SecondSourceColumns
  SecondAdaptiveCutoff SecondAdaptiveRetained SecondParentRows
open scoped Classical nonZeroDivisors

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]
local notation "Sset" => (S : Set (HeightOneSpectrum (𝓞 K)))
local notation "OS" => Set.integer Sset K
local notation "Ext" => ExteriorIdeal K Sset

theorem fineCutoff_rpow_bound (ρ : {r : ℝ // 0 < r}) (X Z tau c R L g d : ℝ)
    (hX : 0 < X) (hZ : 0 < Z) (G : Ext) (δ : Finset (HeightOneSpectrum OS))
    (hc : (16 : ℝ) ≤ Z ^ c) (hρ : ρ.val ≤ Z ^ R) (hL : X ≤ Z ^ L)
    (hg : Z ^ g ≤ height K Sset G)
    (hd : (sIntegerElementNorm K Sset (sIntegerMaskGenerator K Sset δ)).val ≤ Z ^ d) :
    fineCutoff K S ρ X Z tau G δ ≤ Z ^ (c + R + d + 2 * (L - g) + tau) := by
  have hg0 := height_pos K Sset G
  have hquot : X / height K Sset G ≤ Z ^ (L - g) := by
    apply (div_le_iff₀ hg0).mpr
    calc
      X ≤ Z ^ L := hL
      _ = Z ^ (L - g) * Z ^ g := by rw [← Real.rpow_add hZ]; congr 1; ring
      _ ≤ Z ^ (L - g) * height K Sset G :=
        mul_le_mul_of_nonneg_left hg (Real.rpow_nonneg hZ.le _)
  unfold fineCutoff fineScale
  calc
    _ ≤ Z ^ c * Z ^ R * Z ^ d * (Z ^ (L - g)) ^ 2 * Z ^ tau := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hZ.le _)
      apply mul_le_mul _ (pow_le_pow_left₀ (div_pos hX hg0).le hquot 2) (sq_nonneg _)
        (mul_nonneg (mul_nonneg (Real.rpow_nonneg hZ.le _) (Real.rpow_nonneg hZ.le _))
          (Real.rpow_nonneg hZ.le _))
      exact mul_le_mul
        (mul_le_mul hc hρ ρ.property.le (Real.rpow_nonneg hZ.le _)) hd
        (sIntegerElementNorm K Sset _).property.le
        (mul_nonneg (Real.rpow_nonneg hZ.le _) (Real.rpow_nonneg hZ.le _))
    _ = _ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hZ.le]
      repeat rw [← Real.rpow_add hZ]
      congr 1
      norm_num
      ring

/-- An actual bare-frequency membership bound produces the reconstructed
row bound, including both copies of the second-divisor length. -/
theorem newRow_fine_rpow_bound (ρ : {r : ℝ // 0 < r})
    (X Z tau c R L g d₁ d₂ : ℝ) (hX : 0 < X) (hZ : 0 < Z)
    (G k : Ext) (d : NonzeroRingElements OS) (δ : Finset (HeightOneSpectrum OS))
    (hc : (16 : ℝ) ≤ Z ^ c) (hρ : ρ.val ≤ Z ^ R) (hL : X ≤ Z ^ L)
    (hg : Z ^ g ≤ height K Sset G)
    (hd₁ : (sIntegerElementNorm K Sset d).val ≤ Z ^ d₁)
    (hd₂ : (sIntegerElementNorm K Sset (sIntegerMaskGenerator K Sset δ)).val ≤ Z ^ d₂)
    (hk : height K Sset k ≤ fineCutoff K S ρ X Z tau G δ) :
    height K Sset (newRowIdeal K S k d (sIntegerMaskGenerator K Sset δ)) ≤
      Z ^ (d₁ + 2 * d₂ + c + R + 2 * (L - g) + tau) := by
  have hk' := hk.trans
    (fineCutoff_rpow_bound K S ρ X Z tau c R L g d₂ hX hZ G δ hc hρ hL hg hd₂)
  rw [newRow_norm]
  calc
    _ ≤ Z ^ d₁ * Z ^ d₂ * Z ^ (c + R + d₂ + 2 * (L - g) + tau) :=
      mul_le_mul (mul_le_mul hd₁ hd₂ (sIntegerElementNorm K Sset _).property.le
        (Real.rpow_nonneg hZ.le _)) hk' (height_pos K Sset k).le
        (mul_nonneg (Real.rpow_nonneg hZ.le _) (Real.rpow_nonneg hZ.le _))
    _ = _ := by
      rw [← Real.rpow_add hZ, ← Real.rpow_add hZ]
      congr 1
      ring

/-- The numerical padding belongs to the selected first row majorant.
Under that actual radius and the stated source annuli, the fine second
cutoff yields the canonical childM length without a free row hypothesis. -/
theorem actual_child_row_bound (ρ : {r : ℝ // 0 < r})
    (X Z M r ell V delta A B j t g theta eta tau : ℝ)
    (hX : 0 < X) (hZ : 1 ≤ Z) (heta : 0 ≤ eta) (hwidth : 2 ≤ Z ^ eta)
    (G k : Ext) (d : NonzeroRingElements OS) (δ : Finset (HeightOneSpectrum OS))
    (hρ : ρ.val ≤ Z ^ (-(firstPhysicalHeight M r ell V delta B j + 12 * eta + tau)))
    (hL : X ≤ Z ^ (r - A - B - t + eta))
    (hg : Z ^ (g - eta) ≤ height K Sset G)
    (hd₁ : (sIntegerElementNorm K Sset d).val ≤ Z ^ (delta + eta))
    (hd₂ : (sIntegerElementNorm K Sset (sIntegerMaskGenerator K Sset δ)).val ≤
      Z ^ (theta + eta))
    (hk : height K Sset k ≤ fineCutoff K S ρ X Z tau G δ) :
    height K Sset (newRowIdeal K S k d (sIntegerMaskGenerator K Sset δ)) ≤
      Z ^ (childM M ell A t g theta V j eta) := by
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  have h16 : (16 : ℝ) ≤ Z ^ (4 * eta) := by
    calc
      (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) := by norm_num
      _ ≤ (Z ^ eta) ^ (4 : ℕ) := pow_le_pow_left₀ (by norm_num) hwidth 4
      _ = Z ^ (4 * eta) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hz.le]
        congr 1
        norm_num
        ring
  apply (newRow_fine_rpow_bound K S ρ X Z tau (4 * eta)
    (-(firstPhysicalHeight M r ell V delta B j + 12 * eta + tau))
    (r - A - B - t + eta) (g - eta) (delta + eta) (theta + eta)
    hX hz G k d δ h16 hρ hL hg hd₁ hd₂ hk).trans
  apply Real.rpow_le_rpow_of_exponent_le hZ
  unfold firstPhysicalHeight childM decrease
  linarith

end HeckeSkeleton.Moments.MOM_INV_STEP.SecondAdaptiveRows

end
