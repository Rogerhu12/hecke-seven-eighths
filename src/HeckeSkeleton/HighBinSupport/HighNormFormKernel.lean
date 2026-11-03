import HeckeSkeleton.HighBinSupport.HighNormFormDeficit
import Mathlib.Tactic.GCongr
/-!
Pointwise norm form from separately bounded physical factors.

The hypotheses concern the test/profile factor, the reflected Hecke ratio,
the unselected Euler product, the finite prime slots, and the normalizer.
No hypothesis is a row integral estimate or a high-bin estimate.  In
particular the repeated-prime cost is combined with the actual conductor
radical before the row norm is substituted.
-/

noncomputable section
namespace HighBinVerified.NormForm
open scoped BigOperators

/-- The literal scale factor extracted in the supplied project's
`compensatedRowMellinKernel_factorization`. -/
def geometricFactor (Z N : ℝ) (s w z : ℂ) : ℂ :=
  ((Z ^ (17 / 48 : ℝ) : ℝ) : ℂ) ^ (1 / 2 - z) *
    (Z : ℂ) ^ (s + z - 1) *
    ((Z ^ (23 / 48 : ℝ) : ℝ) : ℂ) ^ (w - 1) * (N : ℂ) ^ (-z)

def geometricMajorant (Z a e : ℝ) : ℝ :=
  (Z ^ (17 / 48 : ℝ)) ^ (1 / 2 - 17 / 50 : ℝ) *
    Z ^ (a + 16 * e + 17 / 50 - 1) *
    (Z ^ (23 / 48 : ℝ)) ^ (-a - 6 * e)

theorem geometricMajorant_nonneg (Z a e : ℝ) (hZ : 0 < Z) :
    0 ≤ geometricMajorant Z a e := by
  unfold geometricMajorant
  positivity

/-- The norm computation is uniform in all three imaginary coordinates,
and allows a=1 (hence negative Re(w)). -/
theorem geometricFactor_norm (Z N a e : ℝ) (hZ : 0 < Z) (hN : 0 < N)
    (s w z : ℂ) (hs : s.re = a + 16 * e) (hw : w.re = 1 - a - 6 * e)
    (hz : z.re = 17 / 50) :
    ‖geometricFactor Z N s w z‖ = geometricMajorant Z a e * N ^ (-17 / 50 : ℝ) := by
  unfold geometricFactor geometricMajorant
  simp only [norm_mul]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (Real.rpow_pos_of_pos hZ _),
    Complex.norm_cpow_eq_rpow_re_of_pos hZ,
    Complex.norm_cpow_eq_rpow_re_of_pos (Real.rpow_pos_of_pos hZ _),
    Complex.norm_cpow_eq_rpow_re_of_pos hN]
  simp only [Complex.sub_re, Complex.add_re, Complex.neg_re, Complex.one_re, hs, hw, hz]
  rw [show (1 - a - 6 * e - 1 : ℝ) = -a - 6 * e by ring]
  norm_num

/-- Joint conductor and repeated-prime estimate before any rowwise
absolute bound discards the radical deficit. -/
theorem radical_selected_power_bound (N R M lam eta : ℝ)
    (hN : 0 < N) (hR : 0 < R) (hRN : R ≤ N) (hM : 0 ≤ M)
    (hMR : M * R ≤ N) (hlam : 0 ≤ lam) (heta : 0 ≤ eta) :
    R ^ (lam + eta) * M ^ lam ≤ N ^ (lam + eta) := by
  rw [Real.rpow_add hR, Real.rpow_add hN]
  calc
    (R ^ lam * R ^ eta) * M ^ lam = (M * R) ^ lam * R ^ eta := by
      rw [Real.mul_rpow hM hR.le]
      ring
    _ ≤ N ^ lam * N ^ eta :=
      mul_le_mul (Real.rpow_le_rpow (mul_nonneg hM hR.le) hMR hlam)
        (Real.rpow_le_rpow hR.le hRN heta) (Real.rpow_nonneg hR.le _)
        (Real.rpow_nonneg hN.le _)

/-- Separately bounded factors imply the row-count-free pointwise norm
form.  `D` bounds the signed row-norm exponent on the dyadic shell;
`etaL,etaE` and `mesh/6+nu` are the explicit small losses. -/
theorem pointwise_normForm_of_factors
    (Z N R M d a q e etaL etaE mesh nu D : ℝ)
    (CP CL CE CS CN envelope : ℝ)
    (s w z profile ratio euler slots normalizerInv : ℂ)
    (hZ : 0 < Z) (hNlo : Z ^ d ≤ N) (hNhi : N ≤ 2 * Z ^ d)
    (hR : 0 < R) (hRN : R ≤ N) (hM : 0 ≤ M) (hMR : M * R ≤ N)
    (hlam : 0 ≤ a - 1 / 2 + 6 * e) (hetaL : 0 ≤ etaL)
    (hD : 0 ≤ D) (hpower : a - 1 / 2 + 6 * e + (etaL + etaE) - 17 / 50 ≤ D)
    (hCP : 0 ≤ CP) (hCL : 0 ≤ CL) (hCE : 0 ≤ CE) (hCS : 0 ≤ CS)
    (hCN : 0 ≤ CN) (henvelope : 0 ≤ envelope)
    (hs : s.re = a + 16 * e) (hw : w.re = 1 - a - 6 * e) (hz : z.re = 17 / 50)
    (hprofile : ‖profile‖ ≤ CP * envelope)
    (hratio : ‖ratio‖ ≤ CL * R ^ (a - 1 / 2 + 6 * e + etaL))
    (heuler : ‖euler‖ ≤ CE * N ^ etaE)
    (hslots : ‖slots‖ ≤ CS * M ^ (a - 1 / 2 + 6 * e) *
      Z ^ (-2 / 75 + q / 6 + mesh / 6))
    (hnormalizer : ‖normalizerInv‖ ≤ CN * Z ^ nu) :
    ‖geometricFactor Z N s w z * profile * ratio * euler * slots * normalizerInv‖ ≤
      (CP * CL * CE * CS * CN * (2 : ℝ) ^ D) *
        Z ^ (rowExponent d a q + (105 / 8 + 6 * d) * e +
          d * (etaL + etaE) + (mesh / 6 + nu)) * envelope := by
  have hN : 0 < N := (Real.rpow_pos_of_pos hZ d).trans_le hNlo
  have hg : 0 ≤ geometricMajorant Z a e := geometricMajorant_nonneg Z a e hZ
  have hrad := radical_selected_power_bound N R M (a - 1 / 2 + 6 * e) etaL
    hN hR hRN hM hMR hlam hetaL
  have hnorm := geometricFactor_norm Z N a e hZ hN s w z hs hw hz
  have hmajor :
      ‖geometricFactor Z N s w z * profile * ratio * euler * slots * normalizerInv‖ ≤
        (geometricMajorant Z a e * N ^ (-17 / 50 : ℝ)) * (CP * envelope) *
          (CL * R ^ (a - 1 / 2 + 6 * e + etaL)) * (CE * N ^ etaE) *
          (CS * M ^ (a - 1 / 2 + 6 * e) * Z ^ (-2 / 75 + q / 6 + mesh / 6)) *
          (CN * Z ^ nu) := by
    simp only [norm_mul]
    rw [hnorm]
    gcongr
  have hbudget :
      (geometricMajorant Z a e * N ^ (-17 / 50 : ℝ)) * (CP * envelope) *
          (CL * R ^ (a - 1 / 2 + 6 * e + etaL)) * (CE * N ^ etaE) *
          (CS * M ^ (a - 1 / 2 + 6 * e) * Z ^ (-2 / 75 + q / 6 + mesh / 6)) *
          (CN * Z ^ nu) ≤
        (CP * CL * CE * CS * CN * envelope) * geometricMajorant Z a e *
          N ^ (a - 1 / 2 + 6 * e + (etaL + etaE) - 17 / 50) *
          Z ^ (-2 / 75 + q / 6 + (mesh / 6 + nu)) := by
    calc
      _ = (CP * CL * CE * CS * CN * envelope) * geometricMajorant Z a e *
          (R ^ (a - 1 / 2 + 6 * e + etaL) * M ^ (a - 1 / 2 + 6 * e)) *
          (N ^ etaE * N ^ (-17 / 50 : ℝ)) *
          (Z ^ (-2 / 75 + q / 6 + mesh / 6) * Z ^ nu) := by ring
      _ ≤ (CP * CL * CE * CS * CN * envelope) * geometricMajorant Z a e *
          N ^ (a - 1 / 2 + 6 * e + etaL) *
          (N ^ etaE * N ^ (-17 / 50 : ℝ)) *
          (Z ^ (-2 / 75 + q / 6 + mesh / 6) * Z ^ nu) := by gcongr
      _ = _ := by
        rw [← Real.rpow_add hN, ← Real.rpow_add hZ]
        rw [show (CP * CL * CE * CS * CN * envelope) * geometricMajorant Z a e *
            N ^ (a - 1 / 2 + 6 * e + etaL) * N ^ (etaE + (-17 / 50)) =
            ((CP * CL * CE * CS * CN * envelope) * geometricMajorant Z a e) *
              (N ^ (a - 1 / 2 + 6 * e + etaL) * N ^ (etaE + (-17 / 50))) by ring]
        rw [← Real.rpow_add hN]
        congr 2 <;> ring
  have hscale := dyadic_full_scale_bound Z N d a q e (etaL + etaE) (mesh / 6 + nu) D
    hZ hNlo hNhi hD hpower
  apply hmajor.trans (hbudget.trans ?_)
  calc
    _ = (CP * CL * CE * CS * CN * envelope) *
        (geometricMajorant Z a e *
          N ^ (a - 1 / 2 + 6 * e + (etaL + etaE) - 17 / 50) *
          Z ^ (-2 / 75 + q / 6 + (mesh / 6 + nu))) := by ring
    _ ≤ (CP * CL * CE * CS * CN * envelope) *
        ((2 : ℝ) ^ D * Z ^ (rowExponent d a q + (105 / 8 + 6 * d) * e +
          d * (etaL + etaE) + (mesh / 6 + nu))) := by
      exact mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = _ := by ring

end HighBinVerified.NormForm

#print axioms HighBinVerified.NormForm.geometricFactor_norm
#print axioms HighBinVerified.NormForm.radical_selected_power_bound
#print axioms HighBinVerified.NormForm.pointwise_normForm_of_factors
