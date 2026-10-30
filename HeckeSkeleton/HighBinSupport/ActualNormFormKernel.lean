import HeckeSkeleton.HighBinSupport.ActualNormFormAmplitudeGrid
import HeckeSkeleton.HighBinSupport.ActualNormFormSharpFactors
import HeckeSkeleton.HighBinSupport.ActualNormFormNormalization
import HeckeSkeleton.HighBinSupport.ActualKernelEnvelope
import HeckeSkeleton.HighBinSupport.HighNormFormKernel

/-!
The pointwise norm form for the literal compensated Mellin kernel.

The amplitude object is constructed from the actual complete slots.
The three deleted L-factors, arithmetic Euler product, Mellin tests,
geometric powers and original normalizer are all instantiated below.
No kernel bound, slot estimate, conductor estimate or arbitrary
presentation is an input. The sharp normalizer step inherits the named
upstream PR-WINDOW-PIT admission, as isolated in ActualNormFormNormalization.
-/

set_option autoImplicit false
noncomputable section
namespace HighBinVerified.NormFormKernel

open NumberField IsDedekindDomain MeasureTheory Set
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Physical HeckeGeneral.ThetaSkeleton.Global
open HeckeSkeleton.HighBinContinuation HeckeSkeleton.HighBinActualEuler
open HighBinBoundary.ActualIntegrability
open NormFormActual NormFormFullCorrection NormFormAmplitudes NormFormAmplitudeGrid
open scoped Classical BigOperators Topology

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "S₀" => (S : Set (HeightOneSpectrum (𝓞 K)))
variable [MeasurableSpace (sLocalNormOneGroup K S₀)] [BorelSpace (sLocalNormOneGroup K S₀)]
variable [∀ p : S₀, MeasurableSpace (p.val.adicCompletion K)]
variable [∀ p : S₀, BorelSpace (p.val.adicCompletion K)]
variable (μ : (p : S₀) → Measure (p.val.adicCompletion K))
variable [∀ p : S₀, (μ p).IsAddHaarMeasure]

/-- A fixed bound for the original Gaussian and both Mellin tests on
the actual contour strips. The physical residue normalizer is fixed
data and is included with its original totalized inverse. -/
theorem exists_actual_profile_bound (P : ProbeData K S₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ s w z : ℂ,
      1 / 2 ≤ s.re → s.re ≤ 2 → -1 ≤ w.re → w.re ≤ 1 → z.re = 17 / 50 →
      ‖Complex.exp ((s + z - 1) ^ 2) * additiveMellin K S₀ μ P.additive z *
          mellin P.denominator.toFun w / physicalResidueNormalizer K S₀ μ P‖ ≤ C := by
  letI : IsTotallyComplex K :=
    ⟨HeckeSkeleton.HeckeFiniteBackgroundControl.all_complex_of_primitive12
      K P.arithmetic.primitive12⟩
  obtain ⟨D, hD, hden⟩ := HighBinBoundary.ActualDenominator.exists_mellin_uniform_strip_bound
    P.denominator (-1) 1 0
  obtain ⟨A, hA, hadd⟩ := HighBinBoundary.ActualAdditiveBorel.exists_additiveMellin_rapid_bound_actualBorel
    K S (fun p => inferInstance) (fun p => inferInstance) μ (fun p => inferInstance)
      P.additive (17 / 50) (by norm_num) (by norm_num) 0
  let C : ℝ := Real.exp 4 * A * D * (‖(physicalResidueNormalizer K S₀ μ P)⁻¹‖ + 1)
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro s w z hs0 hs1 hw0 hw1 hz
  have hG := HighBinBoundary.ActualKernel.gaussian_swept_bound s z hs0 hs1 hz
  have hGauss : ‖Complex.exp ((s + z - 1) ^ 2)‖ ≤ Real.exp 4 := hG.trans
    (mul_le_of_le_one_right (Real.exp_pos 4).le
      (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _))))
  have hzline : (17 / 50 : ℂ) + z.im * Complex.I = z := by
    simpa only [hz] using Complex.re_add_im z
  have hAdd : ‖additiveMellin K S₀ μ P.additive z‖ ≤ A := by
    simpa only [pow_zero, one_mul, hzline] using hadd z.im
  have hDen : ‖mellin P.denominator.toFun w‖ ≤ D := by
    simpa only [pow_zero, one_mul, Complex.re_add_im] using hden w.re w.im hw0 hw1
  have hNorm : ‖(physicalResidueNormalizer K S₀ μ P)⁻¹‖ ≤
      ‖(physicalResidueNormalizer K S₀ μ P)⁻¹‖ + 1 := by linarith
  rw [div_eq_mul_inv]
  simp only [norm_mul]
  exact mul_le_mul
    (mul_le_mul (mul_le_mul hGauss hAdd (norm_nonneg _) (Real.exp_pos 4).le)
      hDen (norm_nonneg _) (mul_nonneg (Real.exp_pos 4).le hA.le))
    hNorm (norm_nonneg _) (mul_nonneg (mul_nonneg (Real.exp_pos 4).le hA.le) hD.le)

/-- The actual compensated kernel satisfies the row-count-free norm
form with a constructed full-correction amplitude. The height loss is
explicit and can be made small by choosing kappa before Z and T. -/
theorem exists_actual_kernel_normForm
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
        ∀ x ∈ heightBox (NormForm.internalHeight Z T kappa),
          ‖compensatedRowMellinKernel K S₀ μ P psi (arithmeticHighEulerData K S₀ P psi) g ∅ u Z
            (sLine (a + 16 * e) x) (wLine (1 - a - 6 * e) x) (zLine x)‖ ≤
            C * Z ^ (NormForm.rowExponent d a (ActualFullSlotAmplitude.mean K S₀ A) +
              (105 / 8 + 6 * d) * e + d * (2 * eps + eta) + (theta / 6 + nu) +
              kappa * (((2 * Fintype.card (InfinitePlace K) : ℕ) : ℝ) +
                2 * ((2 * Fintype.card (InfinitePlace K) : ℕ) : ℝ) * eps)) := by
  obtain ⟨ZA, hZA, hamp⟩ := exists_actualFullSlotAmplitude K S₀ psi companions hcomp P g
    hcal hpsi he he1 heps heta hkappa htheta hbudget N hN
  obtain ⟨CL, ZL, hCL, hZL, hratio⟩ := NormFormSharpFactors.exists_actual_threeLFactor_radical_bound
    K S₀ psi companions hcomp P he he1 heps
  obtain ⟨CE, hCE, heuler⟩ := exists_uniform_rowCorrection_subpower K S₀ he he1 heta
  obtain ⟨CN, ZN, hCN, hZN, hnormalizer⟩ :=
    NormFormNormalization.exists_actual_primeNormalizer_inverse_subpower K S₀ g hnu
  obtain ⟨ZF, hZF, hfactor⟩ := exists_actualFullCorrection_product_cutoff K S₀ g he he1
  obtain ⟨CP, hCP, hprofile⟩ := exists_actual_profile_bound K S μ P
  let deg : ℝ := ((2 * Fintype.card (InfinitePlace K) : ℕ) : ℝ) +
    2 * ((2 * Fintype.card (InfinitePlace K) : ℕ) : ℝ) * eps
  let D : ℝ := 2 + 2 * eps + eta
  let C : ℝ := CP * CL * CE * CN * (2 : ℝ) ^ D * (6 : ℝ) ^ deg
  have hdeg : 0 ≤ deg := by dsimp only [deg]; positivity
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, max ZA (max ZL (max ZN ZF)), hC, hZA.trans (le_max_left _ _), ?_⟩
  intro Z T hZ hT hTceiling d hd hd1 u hu hu1 a ha ha1 hbelow
  have hZZA : ZA ≤ Z := (le_max_left _ _).trans hZ
  have hZZL : ZL ≤ Z := (le_max_left _ _).trans ((le_max_right _ _).trans hZ)
  have hZZN : ZN ≤ Z := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hZ))
  have hZZF : ZF ≤ Z := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hZ))
  have hZ1 : 1 ≤ Z := hZA.trans hZZA
  have hZ0 : 0 < Z := zero_lt_one.trans_le hZ1
  obtain ⟨A⟩ := hamp Z T hZZA hT hTceiling d hd hd1 u hu hu1 a ha ha1 hbelow
  refine ⟨A, ?_⟩
  intro x hx
  let E := arithmeticHighEulerData K S₀ P psi
  let H : ℝ := NormForm.internalHeight Z T kappa
  let U : ℝ := 2 * H + 2
  let s : ℂ := sLine (a + 16 * e) x
  let w : ℂ := wLine (1 - a - 6 * e) x
  let z : ℂ := zLine x
  let profile : ℂ := Complex.exp ((s + z - 1) ^ 2) * additiveMellin K S₀ μ P.additive z *
    mellin P.denominator.toFun w / physicalResidueNormalizer K S₀ μ P
  let ratio : ℂ := heckeDeletedContinuation K 1 (exceptionalPrimes K S₀) (6 * z) *
    heckeDeletedContinuation K (E.rows.character u) (exceptionalPrimes K S₀) w /
    heckeDeletedContinuation K (psi * conjugate (E.rows.character u)) (exceptionalPrimes K S₀) s
  let euler : ℂ := rowCorrection K S₀ P psi E ∅ u s w z
  let slots : ℂ := ∏ i : Fin g.slots, actualFullCorrectionSlot K S₀ P psi g ∅ u Z s w z i
  have hs : s.re = a + 16 * e := by simp [s, sLine]
  have hw : w.re = 1 - a - 6 * e := by simp [w, wLine]
  have hz : z.re = 17 / 50 := by norm_num [z, zLine]
  have hHid : H = Z ^ kappa := max_eq_right hTceiling
  have hH1 : 1 ≤ H := by rw [hHid]; exact Real.one_le_rpow hZ1 hkappa.le
  have hH0 : 0 ≤ H := zero_le_one.trans hH1
  have hHU : H + 3 / 2 ≤ U := by dsimp only [U]; linarith
  have hU0 : 0 ≤ 2 + U := by dsimp only [U]; linarith
  have hsi : |s.im| ≤ H := by simpa [s, sLine] using abs_le.mpr hx.1
  have hwi : |w.im| ≤ H := by simpa [w, wLine] using abs_le.mpr hx.2.1
  have hv : (s, w, z) ∈ sweptTube a e := swept_contour_mem_tube he le_rfl s w z hs hw hz
  have hRpos : 0 < (u.ideal.val.val.radical.absNorm : ℝ) :=
    zero_lt_one.trans_le (NormFormSharpFactors.one_le_actual_radicalNorm K S₀ u)
  have hRle : (u.ideal.val.val.radical.absNorm : ℝ) ≤ frequencyRowNorm K S₀ u := by
    simpa only [Finset.prod_empty, one_mul] using
      actual_selected_repeated_product_mul_radicalNorm_le K u.ideal.val ∅ (by simp)
  have hprof : ‖profile‖ ≤ CP * (1 : ℝ) := by
    simpa only [mul_one] using hprofile s w z (by linarith) (by linarith)
      (by linarith) (by linarith) hz
  have hrat : ‖ratio‖ ≤ (CL * (2 + U) ^ deg) *
      (u.ideal.val.val.radical.absNorm : ℝ) ^ (a - 1 / 2 + 6 * e + 2 * eps) := by
    have h := hratio Z hZZL d hd u hu a H U ha ha1 hH0 hHU hbelow s w z
      hs.ge (by linarith) hw hz hsi hwi
    exact h.trans_eq (by ring)
  have heul : ‖euler‖ ≤ CE * frequencyRowNorm K S₀ u ^ eta := by
    simpa only [Finset.card_empty, pow_zero, mul_one] using
      heuler P psi ∅ u a ha ha1 (s, w, z) hv
  have hslots : ‖slots‖ ≤ 1 * (1 : ℝ) ^ (a - 1 / 2 + 6 * e) *
      Z ^ (-2 / 75 + ActualFullSlotAmplitude.mean K S₀ A / 6 + theta / 6) := by
    have h := NormForm.uniform_slot_product_bound g.slots g.slots_pos Z theta 1
      (ActualFullSlotAmplitude.amplitude K S₀ A)
      (fun i => actualFullCorrectionSlot K S₀ P psi g ∅ u Z s w z i) hZ0
      (fun i => by simpa only [one_mul] using A.upper i x hx)
    simpa only [slots, ActualFullSlotAmplitude.mean, one_pow, Real.one_rpow, one_mul] using h
  have hnorm := NormForm.pointwise_normForm_of_factors
    Z (frequencyRowNorm K S₀ u) (u.ideal.val.val.radical.absNorm : ℝ) 1 d a
    (ActualFullSlotAmplitude.mean K S₀ A) e (2 * eps) eta theta nu D
    CP (CL * (2 + U) ^ deg) CE 1 CN 1 s w z profile ratio euler slots
    (primeNormalizer K S₀ g ∅ Z)⁻¹ hZ0 hu hu1 hRpos hRle (by norm_num)
    (by simpa only [one_mul] using hRle) (by linarith) (by positivity) hD
    (by dsimp only [D]; linarith) hCP.le
    (mul_nonneg hCL.le (Real.rpow_nonneg hU0 _)) hCE.le (by norm_num) hCN.le (by norm_num)
    hs hw hz hprof hrat heul hslots (hnormalizer Z hZZN)
  have hid : compensatedRowMellinKernel K S₀ μ P psi E g ∅ u Z s w z =
      NormForm.geometricFactor Z (frequencyRowNorm K S₀ u) s w z *
        profile * ratio * euler * slots * (primeNormalizer K S₀ g ∅ Z)⁻¹ := by
    rw [compensatedRowMellinKernel_factorization K S₀ μ P psi E g ∅ u Z hZ0 s w z,
      hfactor Z hZZF P psi ∅ u a ha ha1 s w z hv]
    dsimp only [NormForm.geometricFactor, profile, ratio, euler, slots]
    simp only [div_eq_mul_inv, mul_inv]
    ring
  have hheight : (2 + U) ^ deg ≤ (6 : ℝ) ^ deg * Z ^ (kappa * deg) := by
    calc
      _ ≤ (6 * Z ^ kappa) ^ deg := by
        apply Real.rpow_le_rpow hU0 _ hdeg
        dsimp only [U]
        rw [← hHid]
        linarith
      _ = _ := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 6) (Real.rpow_nonneg hZ0.le kappa),
          ← Real.rpow_mul hZ0.le]
  change ‖compensatedRowMellinKernel K S₀ μ P psi E g ∅ u Z s w z‖ ≤ _
  rw [hid]
  apply hnorm.trans
  let b : ℝ := NormForm.rowExponent d a (ActualFullSlotAmplitude.mean K S₀ A) +
    (105 / 8 + 6 * d) * e + d * (2 * eps + eta) + (theta / 6 + nu)
  calc
    _ = (CP * CL * CE * CN * (2 : ℝ) ^ D) * (2 + U) ^ deg * Z ^ b := by
      dsimp only [b]
      ring
    _ ≤ (CP * CL * CE * CN * (2 : ℝ) ^ D) *
        ((6 : ℝ) ^ deg * Z ^ (kappa * deg)) * Z ^ b :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hheight (by positivity)) (Real.rpow_nonneg hZ0.le _)
    _ = C * (Z ^ b * Z ^ (kappa * deg)) := by dsimp only [C]; ring
    _ = C * Z ^ (b + kappa * deg) := by rw [← Real.rpow_add hZ0]
    _ = _ := rfl

end HighBinVerified.NormFormKernel

#print axioms HighBinVerified.NormFormKernel.exists_actual_profile_bound
#print axioms HighBinVerified.NormFormKernel.exists_actual_kernel_normForm
