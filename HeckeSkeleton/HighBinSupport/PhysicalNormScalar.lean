import HeckeSkeleton.HighBinSupport.HighNormFormKernel

/-!
# The physical norm form with the repeated-prime allocation kept joint

The source amplitudes measure the main prime polynomials.  A bound for
the full slot product is consequently paired with the conductor radical
before the remaining factors are multiplied.  The fixed height envelope
is not absorbed into a power of the external scale.
-/

set_option autoImplicit false
noncomputable section
namespace HeckeSkeleton.HighBinPhysicalNorm

open HighBinVerified
open scoped BigOperators

theorem joint_pointwise_normForm_of_factors
    (Z N R d a q e etaL etaE etaS mesh nu D : ℝ)
    (CP CL CE CS CN height : ℝ)
    (s w z profile ratio euler slots normalizerInv : ℂ)
    (hZ : 0 < Z) (hNlo : Z ^ d ≤ N) (hNhi : N ≤ 2 * Z ^ d)
    (hR : 0 < R) (hRN : R ≤ N) (hetaL : 0 ≤ etaL)
    (hD : 0 ≤ D)
    (hpower : a - 1 / 2 + 6 * e + (etaL + etaE + etaS) - 17 / 50 ≤ D)
    (hCP : 0 ≤ CP) (hCL : 0 ≤ CL) (hCE : 0 ≤ CE) (hCS : 0 ≤ CS)
    (hCN : 0 ≤ CN) (hheight : 0 ≤ height)
    (hs : s.re = a + 16 * e) (hw : w.re = 1 - a - 6 * e) (hz : z.re = 17 / 50)
    (hprofile : ‖profile‖ ≤ CP)
    (hratio : ‖ratio‖ ≤ CL * R ^ (a - 1 / 2 + 6 * e + etaL) * height)
    (heuler : ‖euler‖ ≤ CE * N ^ etaE)
    (hslots : R ^ (a - 1 / 2 + 6 * e) * ‖slots‖ ≤
      CS * N ^ (a - 1 / 2 + 6 * e + etaS) *
        Z ^ (-2 / 75 + q / 6 + mesh / 6))
    (hnormalizer : ‖normalizerInv‖ ≤ CN * Z ^ nu) :
    ‖NormForm.geometricFactor Z N s w z * profile * ratio * euler * slots * normalizerInv‖ ≤
      (CP * CL * CE * CS * CN * (2 : ℝ) ^ D) *
        Z ^ (NormForm.rowExponent d a q + (105 / 8 + 6 * d) * e +
          d * (etaL + etaE + etaS) + (mesh / 6 + nu)) * height := by
  have hN : 0 < N := (Real.rpow_pos_of_pos hZ d).trans_le hNlo
  have hgeo := NormForm.geometricFactor_norm Z N a e hZ hN s w z hs hw hz
  have hjoint : ‖ratio‖ * ‖slots‖ ≤
      (CL * CS * height) * N ^ (a - 1 / 2 + 6 * e + etaL + etaS) *
        Z ^ (-2 / 75 + q / 6 + mesh / 6) := by
    calc
      _ ≤ (CL * R ^ (a - 1 / 2 + 6 * e + etaL) * height) * ‖slots‖ :=
        mul_le_mul_of_nonneg_right hratio (norm_nonneg _)
      _ = (CL * height * R ^ etaL) *
          (R ^ (a - 1 / 2 + 6 * e) * ‖slots‖) := by
        rw [Real.rpow_add hR]
        ring
      _ ≤ (CL * height * N ^ etaL) *
          (CS * N ^ (a - 1 / 2 + 6 * e + etaS) *
            Z ^ (-2 / 75 + q / 6 + mesh / 6)) :=
        mul_le_mul
          (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hR.le hRN hetaL)
            (mul_nonneg hCL hheight)) hslots
          (mul_nonneg (Real.rpow_nonneg hR.le _) (norm_nonneg _))
          (mul_nonneg (mul_nonneg hCL hheight) (Real.rpow_nonneg hN.le _))
      _ = _ := by
        rw [show a - 1 / 2 + 6 * e + etaL + etaS =
          etaL + (a - 1 / 2 + 6 * e + etaS) by ring, Real.rpow_add hN]
        ring
  have hmajor :
      ‖NormForm.geometricFactor Z N s w z * profile * ratio * euler * slots * normalizerInv‖ ≤
        (NormForm.geometricMajorant Z a e * N ^ (-17 / 50 : ℝ)) * CP *
          ((CL * CS * height) * N ^ (a - 1 / 2 + 6 * e + etaL + etaS) *
            Z ^ (-2 / 75 + q / 6 + mesh / 6)) *
          (CE * N ^ etaE) * (CN * Z ^ nu) := by
    calc
      _ = ‖NormForm.geometricFactor Z N s w z‖ * ‖profile‖ *
          (‖ratio‖ * ‖slots‖) * ‖euler‖ * ‖normalizerInv‖ := by
        simp only [norm_mul]
        ring
      _ ≤ _ := by
        rw [hgeo]
        gcongr
  let loss := etaL + etaE + etaS
  have hscale := NormForm.dyadic_full_scale_bound Z N d a q e loss
    (mesh / 6 + nu) D hZ hNlo hNhi hD hpower
  apply hmajor.trans
  calc
    _ = (CP * CL * CE * CS * CN * height) *
        (NormForm.geometricMajorant Z a e *
          N ^ (a - 1 / 2 + 6 * e + loss - 17 / 50) *
          Z ^ (-2 / 75 + q / 6 + (mesh / 6 + nu))) := by
      rw [show a - 1 / 2 + 6 * e + loss - 17 / 50 =
        (-17 / 50) + (a - 1 / 2 + 6 * e + etaL + etaS) + etaE by
          dsimp only [loss]; ring,
        Real.rpow_add hN, Real.rpow_add hN,
        show -2 / 75 + q / 6 + (mesh / 6 + nu) =
          (-2 / 75 + q / 6 + mesh / 6) + nu by ring,
        Real.rpow_add hZ]
      ring
    _ ≤ (CP * CL * CE * CS * CN * height) *
        ((2 : ℝ) ^ D * Z ^ (NormForm.rowExponent d a q +
          (105 / 8 + 6 * d) * e + d * loss + (mesh / 6 + nu))) :=
      mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = _ := by ring

end HeckeSkeleton.HighBinPhysicalNorm

#print axioms HeckeSkeleton.HighBinPhysicalNorm.joint_pointwise_normForm_of_factors
