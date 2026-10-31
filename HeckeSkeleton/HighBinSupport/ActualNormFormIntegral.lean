import HeckeSkeleton.HighBinSupport.ActualNormFormKernel
import HeckeSkeleton.HighBinSupport.ActualBoundaryIntegrability
import Mathlib.MeasureTheory.Integral.Prod

/-!
The actual three-line row integral satisfies the sharp norm form.

Integrability is proved from the constructed actual Euler product and
the original buffered detector before Fubini is used. The original
(2 pi)^(-3) normalization and all three finite integration intervals are
retained. The fixed box-volume loss is explicitly 3 kappa; no row count
or integral estimate is an input. This sharp route inherits PR-WINDOW-PIT
through its original prime normalizer.
-/

set_option autoImplicit false
noncomputable section
namespace HighBinVerified.NormFormIntegral

open NumberField IsDedekindDomain MeasureTheory Set
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.HighBinContinuation HeckeSkeleton.HighBinActualEuler
open HighBinBoundary HighBinBoundary.ActualIntegrability
open NormFormActual NormFormFullCorrection NormFormAmplitudes NormFormAmplitudeGrid
open scoped Classical BigOperators Topology

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "S₀" => (S : Set (HeightOneSpectrum (𝓞 K)))
variable [MeasurableSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
variable [BorelSpace (sLocalNormOneGroup K (S : Set (HeightOneSpectrum (𝓞 K))))]
variable [∀ p : (S : Set (HeightOneSpectrum (𝓞 K))), MeasurableSpace (p.val.adicCompletion K)]
variable [∀ p : (S : Set (HeightOneSpectrum (𝓞 K))), BorelSpace (p.val.adicCompletion K)]
variable (μ : (p : (S : Set (HeightOneSpectrum (𝓞 K)))) → Measure (p.val.adicCompletion K))
variable [∀ p : (S : Set (HeightOneSpectrum (𝓞 K))), (μ p).IsAddHaarMeasure]

/-- The iterated line measure is the literal restricted product volume. -/
theorem heightBoxMeasure_eq (H : ℝ) :
    ((volume.restrict (Icc (-H) H)).prod (twoHeightMeasure H)) =
      (volume : Measure (ℝ × (ℝ × ℝ))).restrict (heightBox H) := by
  simp only [heightBox, twoHeightMeasure, Measure.prod_restrict]

theorem heightBox_volume_real (H : ℝ) (hH : 0 ≤ H) :
    (volume : Measure (ℝ × (ℝ × ℝ))).real (heightBox H) = 8 * H ^ 3 := by
  change ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod volume)).real
    (Icc (-H) H ×ˢ (Icc (-H) H ×ˢ Icc (-H) H)) = _
  rw [measureReal_prod_prod, measureReal_prod_prod]
  simp only [Measure.real, Real.volume_Icc,
    ENNReal.toReal_ofReal (show 0 ≤ H - -H by linarith)]
  ring

/-- Fubini identifies the original row contour with its integral over
the real three-height box. The hypothesis is actual integrability. -/
theorem rowContourBox_eq_heightBox_integral
    (P : ProbeData K S₀) (psi : HeckeCharacter K) (E : RowEulerData K S₀ P)
    (g : PrimeWindowGeometry) (T : Finset (HeckeCharacter K))
    (u : FrequencyRow K S₀) (Z H sigma nu : ℝ)
    (hi : Integrable (fun x : ℝ × (ℝ × ℝ) =>
      compensatedRowMellinKernel K S₀ μ P psi E g T u Z
        (sLine sigma x) (wLine nu x) (zLine x))
      ((volume.restrict (Icc (-H) H)).prod (twoHeightMeasure H))) :
    rowContourBox K S₀ μ P psi E g T u Z H sigma nu (17 / 50) =
      (2 * (Real.pi : ℂ)) ^ (-(3 : ℤ)) *
        ∫ x in heightBox H, compensatedRowMellinKernel K S₀ μ P psi E g T u Z
          (sLine sigma x) (wLine nu x) (zLine x) := by
  let f : (ℝ × (ℝ × ℝ)) → ℂ := fun x =>
    compensatedRowMellinKernel K S₀ μ P psi E g T u Z
      (sLine sigma x) (wLine nu x) (zLine x)
  have hFubini : (∫ x, f x ∂((volume.restrict (Icc (-H) H)).prod (twoHeightMeasure H))) =
      ∫ ts in Icc (-H) H, ∫ tw in Icc (-H) H, ∫ tz in Icc (-H) H,
        f (ts, tw, tz) := by
    rw [integral_prod _ hi]
    apply integral_congr_ae
    filter_upwards [hi.prod_right_ae] with ts hts
    exact integral_prod _ hts
  rw [← heightBoxMeasure_eq H]
  change rowContourBox K S₀ μ P psi E g T u Z H sigma nu (17 / 50) =
    _ * ∫ x, f x ∂((volume.restrict (Icc (-H) H)).prod (twoHeightMeasure H))
  rw [hFubini]
  simp only [rowContourBox, f, sLine, wLine, zLine,
    Complex.ofReal_div, Complex.ofReal_ofNat]

/-- A rowwise norm form for the actual rowContourBox, with the finite
full-slot amplitude constructed in the conclusion. All constants and
thresholds are fixed before the scale, height, shell, bin and row. -/
theorem exists_actual_rowContour_normForm
    (psi : HeckeCharacter K) (companions : Finset (HeckeCharacter K))
    (hcomp : (1 : HeckeCharacter K) ∈ companions)
    (P : ProbeData K S₀) (g : PrimeWindowGeometry)
    (hcal : ThetaCalibrationInput K S₀ P.arithmetic P.Lambda P.G)
    (hpsi : ∀ p : ExteriorPrime K S₀, UnramifiedAt K psi p.val)
    {e eps eta kappa theta nu : ℝ} (he : 0 < e) (he1 : e ≤ 1 / 10000)
    (heps : 0 < eps) (heta : 0 < eta) (hkappa : 0 < kappa) (htheta : 0 < theta)
    (hnu : 0 < nu)
    (hbudget : eps + eta + kappa *
        (((2 * Fintype.card (InfinitePlace K) : ℕ) : ℝ) * eps) +
        ((1 / 6 : ℝ) / g.slots) * (8 * e + eta) ≤
      ((1 / 6 : ℝ) / g.slots) * theta / 2)
    (N : ℕ) (hN : (1 / 2 : ℝ) ≤ (N : ℝ) * theta) :
    ∃ C Z0 : ℝ, 0 < C ∧ 1 ≤ Z0 ∧ ∀ Z T : ℝ, Z0 ≤ Z → 1 ≤ T → T ≤ Z ^ kappa →
      ∀ d : ℝ, (1 / 16 : ℝ) ≤ d → d ≤ 1 →
      ∀ u : FrequencyRow K S₀, Z ^ d ≤ frequencyRowNorm K S₀ u →
        frequencyRowNorm K S₀ u ≤ 2 * Z ^ d →
      ∀ a : ℝ, 51 / 100 ≤ a → a ≤ 1 →
      rowZeroBelow K S₀ psi companions P (arithmeticHighEulerData K S₀ P psi) u
        (2 * NormForm.internalHeight Z T kappa + 2) (a + 2 * e) →
      ∃ A : ActualFullSlotAmplitude K S₀ P psi g u Z a e
          (NormForm.internalHeight Z T kappa) theta N,
        Integrable (fun x : ℝ × (ℝ × ℝ) =>
          compensatedRowMellinKernel K S₀ μ P psi (arithmeticHighEulerData K S₀ P psi) g ∅ u Z
            (sLine (a + 16 * e) x) (wLine (1 - a - 6 * e) x) (zLine x))
          ((volume.restrict (Icc (-NormForm.internalHeight Z T kappa)
            (NormForm.internalHeight Z T kappa))).prod
              (twoHeightMeasure (NormForm.internalHeight Z T kappa))) ∧
        ‖rowContourBox K S₀ μ P psi (arithmeticHighEulerData K S₀ P psi) g ∅ u Z
            (NormForm.internalHeight Z T kappa) (a + 16 * e) (1 - a - 6 * e) (17 / 50)‖ ≤
          C * Z ^ (NormForm.rowExponent d a (ActualFullSlotAmplitude.mean K S₀ A) +
            (105 / 8 + 6 * d) * e + d * (2 * eps + eta) + (theta / 6 + nu) +
            kappa * (((2 * Fintype.card (InfinitePlace K) : ℕ) : ℝ) +
              2 * ((2 * Fintype.card (InfinitePlace K) : ℕ) : ℝ) * eps + 3)) := by
  obtain ⟨C, ZK, hC, hZK, hkernel⟩ := NormFormKernel.exists_actual_kernel_normForm
    K S μ psi companions hcomp P g hcal hpsi he he1 heps heta hkappa htheta hnu hbudget N hN
  let E := arithmeticHighEulerData K S₀ P psi
  obtain ⟨ZI, hZI, hint⟩ := eventually_compensatedRowMellinKernel_integrable_heightBox
    K S μ P psi E g ∅ companions hcomp
  let cpi : ℂ := (2 * (Real.pi : ℂ)) ^ (-(3 : ℤ))
  refine ⟨8 * (‖cpi‖ + 1) * C, max ZK ZI, by positivity,
    hZK.trans (le_max_left _ _), ?_⟩
  intro Z T hZ hT hTceiling d hd hd1 u hu hu1 a ha ha1 hbelow
  have hZZK : ZK ≤ Z := (le_max_left _ _).trans hZ
  have hZZI : ZI ≤ Z := (le_max_right _ _).trans hZ
  have hZ1 : 1 ≤ Z := hZK.trans hZZK
  have hZ0 : 0 < Z := zero_lt_one.trans_le hZ1
  let H : ℝ := NormForm.internalHeight Z T kappa
  let U : ℝ := 2 * H + 2
  let μH : Measure (ℝ × (ℝ × ℝ)) :=
    (volume.restrict (Icc (-H) H)).prod (twoHeightMeasure H)
  let f : (ℝ × (ℝ × ℝ)) → ℂ := fun x =>
    compensatedRowMellinKernel K S₀ μ P psi E g ∅ u Z
      (sLine (a + 16 * e) x) (wLine (1 - a - 6 * e) x) (zLine x)
  have hHid : H = Z ^ kappa := max_eq_right hTceiling
  have hH1 : 1 ≤ H := by rw [hHid]; exact Real.one_le_rpow hZ1 hkappa.le
  have hH0 : 0 ≤ H := zero_le_one.trans hH1
  have hcorr (Q : Finset (ExteriorPrime K S₀)) :
      ContinuousOn (fun x => rowCorrection K S₀ P psi E Q u
        (sLine (a + 16 * e) x) (wLine (1 - a - 6 * e) x) (zLine x)) (heightBox H) := by
    apply (rowCorrection_continuousOn_sweptTube K S₀ P psi Q u ha ha1 he he1).comp
    · exact ((continuous_sLine _).prodMk
        ((continuous_wLine _).prodMk continuous_zLine)).continuousOn
    · intro x hx
      apply swept_contour_mem_tube he le_rfl
      · simp [sLine]
      · simp [wLine]
      · norm_num [zLine]
  have hi : Integrable f μH := hint Z hZZI d hd u hu H U (a + 2 * e)
    (a + 16 * e) (1 - a - 6 * e) (by dsimp only [U]; linarith)
    (by linarith) (by linarith) hbelow hcorr
  obtain ⟨A, hA⟩ := hkernel Z T hZZK hT hTceiling d hd hd1 u hu hu1 a ha ha1 hbelow
  refine ⟨A, hi, ?_⟩
  let b : ℝ := NormForm.rowExponent d a (ActualFullSlotAmplitude.mean K S₀ A) +
    (105 / 8 + 6 * d) * e + d * (2 * eps + eta) + (theta / 6 + nu) +
    kappa * (((2 * Fintype.card (InfinitePlace K) : ℕ) : ℝ) +
      2 * ((2 * Fintype.card (InfinitePlace K) : ℕ) : ℝ) * eps)
  have hmem : ∀ᵐ x ∂μH, x ∈ heightBox H := by
    simpa only [μH, heightBox, twoHeightMeasure, Measure.prod_restrict] using
      (ae_restrict_mem (μ := (volume : Measure (ℝ × (ℝ × ℝ))))
        (measurableSet_Icc.prod (measurableSet_Icc.prod measurableSet_Icc)))
  letI : IsFiniteMeasure μH := by dsimp only [μH]; infer_instance
  have hb : ‖∫ x, f x ∂μH‖ ≤ (C * Z ^ b) * μH.real univ :=
    norm_integral_le_of_norm_le_const (hmem.mono fun x hx => hA x hx)
  have hmass : μH.real univ = 8 * H ^ 3 := by
    dsimp only [μH]
    rw [← univ_prod_univ, measureReal_prod_prod, twoHeightMeasure_mass H hH0]
    simp only [Measure.real, Measure.restrict_apply_univ, Real.volume_Icc,
      ENNReal.toReal_ofReal (show 0 ≤ H - -H by linarith)]
    ring
  have hFubini : (∫ x, f x ∂μH) =
      ∫ ts in Icc (-H) H, ∫ tw in Icc (-H) H, ∫ tz in Icc (-H) H,
        f (ts, tw, tz) := by
    rw [integral_prod _ hi]
    apply integral_congr_ae
    filter_upwards [hi.prod_right_ae] with ts hts
    exact integral_prod _ hts
  have hbox : rowContourBox K S₀ μ P psi E g ∅ u Z H
      (a + 16 * e) (1 - a - 6 * e) (17 / 50) = cpi * ∫ x, f x ∂μH := by
    rw [hFubini]
    simp only [rowContourBox, f, cpi, sLine, wLine, zLine,
      Complex.ofReal_div, Complex.ofReal_ofNat]
  have hHpower : H ^ 3 = Z ^ (3 * kappa) := by
    rw [hHid, ← Real.rpow_natCast, ← Real.rpow_mul hZ0.le]
    congr 1
    ring
  change ‖rowContourBox K S₀ μ P psi E g ∅ u Z H
    (a + 16 * e) (1 - a - 6 * e) (17 / 50)‖ ≤ _
  rw [hbox, norm_mul]
  calc
    _ ≤ (‖cpi‖ + 1) * ((C * Z ^ b) * μH.real univ) :=
      mul_le_mul (by linarith : ‖cpi‖ ≤ ‖cpi‖ + 1) hb (norm_nonneg _) (by positivity)
    _ = (8 * (‖cpi‖ + 1) * C) * (Z ^ b * Z ^ (3 * kappa)) := by
      rw [hmass, hHpower]
      ring
    _ = (8 * (‖cpi‖ + 1) * C) * Z ^ (b + 3 * kappa) := by
      rw [← Real.rpow_add hZ0]
    _ = _ := by
      congr 2
      dsimp only [b]
      ring

/-- All auxiliary small parameters are chosen from the original
lambda-margin. Only the original e <= lambda/100 condition remains;
the actual amplitude grid and the positive height ceiling are outputs. -/
theorem exists_actual_rowContour_normForm_quarter_loss
    (psi : HeckeCharacter K) (companions : Finset (HeckeCharacter K))
    (hcomp : (1 : HeckeCharacter K) ∈ companions)
    (P : ProbeData K S₀) (g : PrimeWindowGeometry)
    (hcal : ThetaCalibrationInput K S₀ P.arithmetic P.Lambda P.G)
    (hpsi : ∀ p : ExteriorPrime K S₀, UnramifiedAt K psi p.val)
    {e lam : ℝ} (he : 0 < e) (he1 : e ≤ 1 / 10000)
    (hlam : 0 < lam) (heLam : e ≤ lam / 100) :
    ∃ kappa theta : ℝ, ∃ N : ℕ, ∃ C Z0 : ℝ,
      0 < kappa ∧ 0 < theta ∧ 0 < C ∧ 1 ≤ Z0 ∧
      ∀ Z T : ℝ, Z0 ≤ Z → 1 ≤ T → T ≤ Z ^ kappa →
      ∀ d : ℝ, (1 / 16 : ℝ) ≤ d → d ≤ 1 →
      ∀ u : FrequencyRow K S₀, Z ^ d ≤ frequencyRowNorm K S₀ u →
        frequencyRowNorm K S₀ u ≤ 2 * Z ^ d →
      ∀ a : ℝ, 51 / 100 ≤ a → a ≤ 1 →
      rowZeroBelow K S₀ psi companions P (arithmeticHighEulerData K S₀ P psi) u
        (2 * NormForm.internalHeight Z T kappa + 2) (a + 2 * e) →
      ∃ A : ActualFullSlotAmplitude K S₀ P psi g u Z a e
          (NormForm.internalHeight Z T kappa) theta N,
        ‖rowContourBox K S₀ μ P psi (arithmeticHighEulerData K S₀ P psi) g ∅ u Z
            (NormForm.internalHeight Z T kappa) (a + 16 * e) (1 - a - 6 * e) (17 / 50)‖ ≤
          C * Z ^ (NormForm.rowExponent d a (ActualFullSlotAmplitude.mean K S₀ A) + lam / 4) := by
  obtain ⟨eps, eta, kappa, theta, nu, N, heps, heta, hkappa, htheta, hnu, hN, hbudget, hloss⟩ :=
    NormForm.exists_full_normForm_parameter_budget g.slots g.slots_pos
      (((2 * Fintype.card (InfinitePlace K) : ℕ) : ℝ)) lam e
        (Nat.cast_nonneg _) hlam he.le heLam
  obtain ⟨C, Z0, hC, hZ0, hrow⟩ := exists_actual_rowContour_normForm K S μ
    psi companions hcomp P g hcal hpsi he he1 heps heta hkappa htheta hnu hbudget N hN
  refine ⟨kappa, theta, N, C, Z0, hkappa, htheta, hC, hZ0, ?_⟩
  intro Z T hZ hT hTceiling d hd hd1 u hu hu1 a ha ha1 hbelow
  obtain ⟨A, hi, hb⟩ := hrow Z T hZ hT hTceiling d hd hd1 u hu hu1 a ha ha1 hbelow
  refine ⟨A, hb.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply Real.rpow_le_rpow_of_exponent_le (hZ0.trans hZ)
  have h := hloss d (by linarith) hd1
  linarith

end HighBinVerified.NormFormIntegral

#print axioms HighBinVerified.NormFormIntegral.exists_actual_rowContour_normForm
#print axioms HighBinVerified.NormFormIntegral.exists_actual_rowContour_normForm_quarter_loss
#print axioms HighBinVerified.NormFormIntegral.rowContourBox_eq_heightBox_integral
