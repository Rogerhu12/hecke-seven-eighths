import HeckeSkeleton.Moments.MOM_INV_STEP.SecondAdaptiveRows
import HeckeSkeleton.Moments.MOM_INV_STEP.ActualCenterGeometry

/-!
# The fine second row bound with actual first centers

The first column scale is allowed its full +4h error from the fixed
dyadic center.  The genuine second cutoff then gives childM with +5h.
The row is the reconstructed ideal d₁d₂k and k is bounded by the
cutoff for its actual common factor and actual second divisor.
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

theorem centered_child_row_bound (ρ : {r : ℝ // 0 < r})
    (X Z M r ell V delta A B j t g theta h tau : ℝ)
    (hX : 0 < X) (hZ : 1 ≤ Z) (hwidth : 2 ≤ Z ^ h)
    (G k : Ext) (d : NonzeroRingElements OS) (δ : Finset (HeightOneSpectrum OS))
    (hρ : ρ.val ≤ Z ^ (-(firstPhysicalHeight M r ell V delta B j + 12 * h + tau)))
    (hL : X ≤ Z ^ (r - A - B - t + 4 * h))
    (hg : Z ^ (g - h) ≤ height K Sset G)
    (hd₁ : (sIntegerElementNorm K Sset d).val ≤ Z ^ (delta + h))
    (hd₂ : (sIntegerElementNorm K Sset (sIntegerMaskGenerator K Sset δ)).val ≤
      Z ^ (theta + h))
    (hk : height K Sset k ≤ fineCutoff K S ρ X Z tau G δ) :
    height K Sset (newRowIdeal K S k d (sIntegerMaskGenerator K Sset δ)) ≤
      Z ^ (childM M ell A t g theta V j (5 * h)) := by
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  have h16 : (16 : ℝ) ≤ Z ^ (4 * h) := by
    calc
      (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) := by norm_num
      _ ≤ (Z ^ h) ^ (4 : ℕ) := pow_le_pow_left₀ (by norm_num) hwidth 4
      _ = Z ^ (4 * h) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hz.le]
        congr 1
        norm_num
        ring
  have hrow := newRow_fine_rpow_bound K S ρ X Z tau (4 * h)
    (-(firstPhysicalHeight M r ell V delta B j + 12 * h + tau))
    (r - A - B - t + 4 * h) (g - h) (delta + h) (theta + h)
    hX hz G k d δ h16 hρ hL hg hd₁ hd₂ hk
  have hexp :
      (delta + h) + 2 * (theta + h) + 4 * h +
          (-(firstPhysicalHeight M r ell V delta B j + 12 * h + tau)) +
          2 * ((r - A - B - t + 4 * h) - (g - h)) + tau =
        childM M ell A t g theta V j (5 * h) := by
    unfold firstPhysicalHeight childM decrease
    ring
  rwa [hexp] at hrow

/-- The column-scale hypothesis is supplied by the actual first center
and the three norm annuli, with no separate formal-length assertion. -/
theorem centered_child_row_bound_of_center (ρ : {r : ℝ // 0 < r})
    (Z M r ell V delta A B j t g theta h tau NA NC Ne c : ℝ)
    (hZ : 1 ≤ Z) (hc : 0 < c) (hwidth : 2 ≤ Z ^ h)
    (hA : Z ^ (A - h) ≤ NA ∧ NA ≤ Z ^ (A + h))
    (hC : Z ^ (B - h) ≤ NC ∧ NC ≤ Z ^ (B + h))
    (he : Z ^ (t - h) ≤ Ne ∧ Ne ≤ Z ^ (t + h))
    (hbin : c ≤ NA * NC * Ne ∧ NA * NC * Ne ≤ 2 * c)
    (G k : Ext) (d : NonzeroRingElements OS) (δ : Finset (HeightOneSpectrum OS))
    (hρ : ρ.val ≤ Z ^ (-(firstPhysicalHeight M r ell V delta B j + 12 * h + tau)))
    (hg : Z ^ (g - h) ≤ height K Sset G)
    (hd₁ : (sIntegerElementNorm K Sset d).val ≤ Z ^ (delta + h))
    (hd₂ : (sIntegerElementNorm K Sset (sIntegerMaskGenerator K Sset δ)).val ≤
      Z ^ (theta + h))
    (hk : height K Sset k ≤ fineCutoff K S ρ (Z ^ r / c) Z tau G δ) :
    height K Sset (newRowIdeal K S k d (sIntegerMaskGenerator K Sset δ)) ≤
      Z ^ (childM M ell A t g theta V j (5 * h)) := by
  have hz : 0 < Z := zero_lt_one.trans_le hZ
  have hscale := ActualCenterGeometry.first_scale_bounds Z r A B t h NA NC Ne c
    hz hc hwidth hA hC he hbin
  exact centered_child_row_bound K S ρ (Z ^ r / c) Z M r ell V delta A B j t g theta h tau
    (div_pos (Real.rpow_pos_of_pos hz r) hc) hZ hwidth G k d δ
    hρ hscale.2 hg hd₁ hd₂ hk

end HeckeSkeleton.Moments.MOM_INV_STEP.SecondAdaptiveRows

end
