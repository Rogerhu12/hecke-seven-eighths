import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalFirstLogBounds
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.CanonicalSecondLogChart
import HeckeSkeleton.Moments.MOM_ENGINE_STEP.SecondCommonNormalization

/-!
# The second logarithmic tilt is paid by original norm windows

The actual second row radius can be smaller than one.  Its negative
Mellin power is paid using the original upper window for the primal
radius times its actual mask-generator norm.  Every original orbit has
norm at least one, so this gives a uniform lower window for the row
radius before the physical cutoff or any row partition is chosen.

The positive column powers use the two actual modulus norms.  Their
combined cost is an arbitrarily small power after a single tilt is
chosen from the fixed norm-window exponents.  The original Poisson
scalar and its inverse dilation norm remain explicit throughout.
-/

noncomputable section
open scoped Classical NumberField

namespace HeckeSkeleton.Moments.EngineStep

open NumberField IsDedekindDomain
open HeckeGeneral.Arithmetic HeckeGeneral.Analysis HeckeGeneral.Characters

/-- The tilt is fixed before the scale, rows, masks and columns. -/
theorem exists_original_log_tilt (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧ B * δ ≤ ε := by
  let δ := min (1 / 2 : ℝ) (ε / (B + 1))
  have hden : 0 < B + 1 := by linarith
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hε hden)
  refine ⟨δ, hδ, min_le_left _ _, ?_⟩
  have hp : δ * (B + 1) ≤ ε :=
    (le_div_iff₀ hden).mp (min_le_right (1 / 2 : ℝ) (ε / (B + 1)))
  nlinarith

namespace CanonicalSecondLogChart

variable {K : Type} [Field K] [NumberField K]
variable {S : Finset (HeightOneSpectrum (𝓞 K))}
variable {Γ : Subgroup ((S : Set (HeightOneSpectrum (𝓞 K))).unit K)}
variable [IsPrincipalIdealRing (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)]

variable (r : {r : ℝ // 0 < r})
variable (D : Finset (HeightOneSpectrum (Set.integer (S : Set (HeightOneSpectrum (𝓞 K))) K)))
variable (q : SIntegerOrbits K (S : Set (HeightOneSpectrum (𝓞 K))) Γ)

/-- The literal second radius has a lower window, even when it is
less than one.  No transformed coefficient or finite row count occurs. -/
theorem rowRadius_lower_of_norm_window {Z B : ℝ} (hZ : 0 < Z)
    (hwindow : r.val * (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
      (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D)).val ≤ Z ^ B) :
    Z ^ (-B) ≤ (rowRadius r D q).val := by
  let u := sIntegerMaskDilationRadius K S r
    (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D)
  let N := sIntegerOrbitNorm K (S : Set (HeightOneSpectrum (𝓞 K))) Γ q
  have hu : u.val ≤ Z ^ B := hwindow
  have hN : 1 ≤ N.val := one_le_sIntegerOrbitNorm q
  change Z ^ (-B) ≤ N.val / u.val
  calc
    _ = (Z ^ B)⁻¹ := Real.rpow_neg hZ.le B
    _ ≤ u.val⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le u.property hu
    _ ≤ N.val / u.val := by
      simpa only [div_eq_mul_inv, one_mul] using
        mul_le_mul_of_nonneg_right hN (inv_nonneg.mpr u.property.le)

theorem rowRadius_neg_pow_le_of_norm_window {Z B δ : ℝ}
    (hZ : 0 < Z) (hδ : 0 ≤ δ)
    (hwindow : r.val * (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
      (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D)).val ≤ Z ^ B) :
    (rowRadius r D q).val ^ (-δ) ≤ Z ^ (B * δ) := by
  calc
    _ ≤ (Z ^ (-B)) ^ (-δ) := Real.rpow_le_rpow_of_nonpos
      (Real.rpow_pos_of_pos hZ _) (rowRadius_lower_of_norm_window r D q hZ hwindow)
      (neg_nonpos.mpr hδ)
    _ = Z ^ ((-B) * (-δ)) := (Real.rpow_mul hZ.le (-B) (-δ)).symm
    _ = _ := by congr 1 <;> ring

theorem rowTilt_norm_le_of_norm_window {Z B δ : ℝ}
    (hZ : 0 < Z) (hδ : 0 ≤ δ)
    (hwindow : r.val * (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
      (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D)).val ≤ Z ^ B) :
    ‖(((rowRadius r D q).val ^ (-δ) : ℝ) : ℂ)‖ ≤ Z ^ (B * δ) := by
  rw [CanonicalFirstLog.tiltScalar_norm (rowRadius r D q).property]
  exact rowRadius_neg_pow_le_of_norm_window r D q hZ hδ hwindow

/-- Multiplying the original row scalar pays only the additional
Mellin power.  Its existing arithmetic normalization is unchanged. -/
theorem orbitalScalar_tilt_norm_le_of_norm_window {Z B δ : ℝ}
    (hZ : 0 < Z) (hδ : 0 ≤ δ)
    (hwindow : r.val * (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
      (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D)).val ≤ Z ^ B) :
    ‖secondOrbitalScalar (K := K) (S := S) r D *
      (((rowRadius r D q).val ^ (-δ) : ℝ) : ℂ)‖ ≤
        ‖secondOrbitalScalar (K := K) (S := S) r D‖ * Z ^ (B * δ) := by
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left
    (rowTilt_norm_le_of_norm_window r D q hZ hδ hwindow) (norm_nonneg _)

/-- The genuine inverse primal dilation norm remains visible after
paying the negative row power. -/
theorem orbitalScalar_tilt_norm_le_inverse_dilation {Z B δ : ℝ}
    (hZ : 0 < Z) (hδ : 0 ≤ δ)
    (hwindow : r.val * (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
      (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D)).val ≤ Z ^ B) :
    ‖secondOrbitalScalar (K := K) (S := S) r D *
      (((rowRadius r D q).val ^ (-δ) : ℝ) : ℂ)‖ ≤
        (orbitalFieldFactor K /
          (r.val * (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
            (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D)).val)) *
          Z ^ (B * δ) :=
  (orbitalScalar_tilt_norm_le_of_norm_window r D q hZ hδ hwindow).trans
    (mul_le_mul_of_nonneg_right (secondOrbitalScalar_norm_le r D)
      (Real.rpow_nonneg hZ.le _))

/-- All three factors are precisely the ones in secondProfile_log.
The row and both columns retain their original norm windows. -/
theorem profile_tilt_norm_le_of_norm_windows
    (c d : OrbitalGaussColumn K S Γ) {Z Bρ BL BR δ : ℝ}
    (hZ : 0 < Z) (hδ : 0 ≤ δ)
    (hrow : r.val * (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
      (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D)).val ≤ Z ^ Bρ)
    (hleft : columnNorm c ≤ Z ^ BL) (hright : columnNorm d ≤ Z ^ BR) :
    ‖(((rowRadius r D q).val ^ (-δ) : ℝ) : ℂ) *
      ((((columnNorm c) ^ δ : ℝ) : ℂ) * star (((columnNorm d) ^ δ : ℝ) : ℂ))‖ ≤
        Z ^ ((Bρ + BL + BR) * δ) := by
  rw [norm_mul, norm_mul, norm_star,
    CanonicalFirstLog.tiltScalar_norm (rowRadius r D q).property,
    CanonicalFirstLog.tiltScalar_norm (columnNorm_pos c),
    CanonicalFirstLog.tiltScalar_norm (columnNorm_pos d)]
  calc
    _ ≤ Z ^ (Bρ * δ) * (Z ^ (BL * δ) * Z ^ (BR * δ)) :=
      mul_le_mul (rowRadius_neg_pow_le_of_norm_window r D q hZ hδ hrow)
        (mul_le_mul (CanonicalFirstLog.tilt_le_of_norm_window (columnNorm_pos c) hZ hδ hleft)
          (CanonicalFirstLog.tilt_le_of_norm_window (columnNorm_pos d) hZ hδ hright)
          (Real.rpow_nonneg (columnNorm_pos d).le _) (Real.rpow_nonneg hZ.le _))
        (mul_nonneg (Real.rpow_nonneg (columnNorm_pos c).le _)
          (Real.rpow_nonneg (columnNorm_pos d).le _))
        (Real.rpow_nonneg hZ.le _)
    _ = _ := by
      rw [← Real.rpow_add hZ, ← Real.rpow_add hZ]
      congr 1 <;> ring

theorem profile_tilt_norm_le_small_power
    (c d : OrbitalGaussColumn K S Γ) {Z Bρ BL BR δ ε : ℝ}
    (hZ : 1 ≤ Z) (hδ : 0 ≤ δ) (hpaid : (Bρ + BL + BR) * δ ≤ ε)
    (hrow : r.val * (sIntegerElementNorm K (S : Set (HeightOneSpectrum (𝓞 K)))
      (sIntegerMaskGenerator K (S : Set (HeightOneSpectrum (𝓞 K))) D)).val ≤ Z ^ Bρ)
    (hleft : columnNorm c ≤ Z ^ BL) (hright : columnNorm d ≤ Z ^ BR) :
    ‖(((rowRadius r D q).val ^ (-δ) : ℝ) : ℂ) *
      ((((columnNorm c) ^ δ : ℝ) : ℂ) * star (((columnNorm d) ^ δ : ℝ) : ℂ))‖ ≤ Z ^ ε :=
  (profile_tilt_norm_le_of_norm_windows r D q c d (zero_lt_one.trans_le hZ) hδ
    hrow hleft hright).trans (Real.rpow_le_rpow_of_exponent_le hZ hpaid)

end CanonicalSecondLogChart
end HeckeSkeleton.Moments.EngineStep

#print axioms HeckeSkeleton.Moments.EngineStep.exists_original_log_tilt
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalSecondLogChart.rowRadius_lower_of_norm_window
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalSecondLogChart.orbitalScalar_tilt_norm_le_inverse_dilation
#print axioms HeckeSkeleton.Moments.EngineStep.CanonicalSecondLogChart.profile_tilt_norm_le_small_power
