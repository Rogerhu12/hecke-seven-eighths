import HeckeSkeleton.HighBinSupport.ActualPhysicalSlotBound
import HeckeSkeleton.HighBinSupport.PhysicalNormScalar
import HeckeSkeleton.HighBinSupport.ActualNormFormSharpFactors
import HeckeSkeleton.HighBinSupport.ActualKernelEnvelope
import Expansion.ActualPrimeNormalizer

/-!
# The full physical kernel at the original retained height

The height is the original `T`, and the zero detector is the original
`3(h+2)T`.  A fixed polynomial in `1+T` controls the Hecke and test factors.
The prime-slot amplitudes are not changed; their pointwise main-slot bound
is combined with all correction terms and the actual conductor deficit.
The normalizer is the proved actual prime-window normalizer, and the
physical Poisson scalar is included in the test factor.
-/

set_option autoImplicit false
noncomputable section

namespace HeckeSkeleton.HighBinPhysicalNorm

open NumberField IsDedekindDomain MeasureTheory Set
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton.Global HeckeGeneral.ThetaSkeleton.Physical
open HighBinVerified HighBinVerified.NormFormActual
open HighBinVerified.NormFormFullCorrection
open HeckeSkeleton.HighBinActualEuler HeckeSkeleton.HighBinContinuation
open HighBinBoundary.ActualIntegrability
open scoped Classical BigOperators Topology

variable (K : Type) [Field K] [NumberField K]
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "S₀" => (S : Set (HeightOneSpectrum (𝓞 K)))
variable [MeasurableSpace (sLocalNormOneGroup K S₀)] [BorelSpace (sLocalNormOneGroup K S₀)]
variable [∀ p : S₀, MeasurableSpace (p.val.adicCompletion K)]
variable [∀ p : S₀, BorelSpace (p.val.adicCompletion K)]
variable (mu : (p : S₀) → Measure (p.val.adicCompletion K))
variable [∀ p : S₀, (mu p).IsAddHaarMeasure]

/-- The original profiles with the corrected, fixed Poisson factor. -/
theorem exists_physical_profile_bound (P : ProbeData K S₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ s w z : ℂ,
      1 / 2 ≤ s.re → s.re ≤ 2 → -1 ≤ w.re → w.re ≤ 1 → z.re = 17 / 50 →
      ‖(physicalPoissonScalar K : ℂ) * Complex.exp ((s + z - 1) ^ 2) *
          additiveMellin K S₀ mu P.additive z * mellin P.denominator.toFun w /
            physicalResidueNormalizer K S₀ mu P‖ ≤ C := by
  letI : IsTotallyComplex K :=
    ⟨HeckeSkeleton.HeckeFiniteBackgroundControl.all_complex_of_primitive12
      K P.arithmetic.primitive12⟩
  obtain ⟨D, hD, hden⟩ := HighBinBoundary.ActualDenominator.exists_mellin_uniform_strip_bound
    P.denominator (-1) 1 0
  obtain ⟨A, hA, hadd⟩ := HighBinBoundary.ActualAdditiveBorel.exists_additiveMellin_rapid_bound_actualBorel
    K S (fun p => inferInstance) (fun p => inferInstance) mu (fun p => inferInstance)
      P.additive (17 / 50) (by norm_num) (by norm_num) 0
  let C := (‖(physicalPoissonScalar K : ℂ)‖ + 1) * Real.exp 4 * A * D *
    (‖(physicalResidueNormalizer K S₀ mu P)⁻¹‖ + 1)
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro s w z hs0 hs1 hw0 hw1 hz
  have hG := HighBinBoundary.ActualKernel.gaussian_swept_bound s z hs0 hs1 hz
  have hGauss : ‖Complex.exp ((s + z - 1) ^ 2)‖ ≤ Real.exp 4 := hG.trans
    (mul_le_of_le_one_right (Real.exp_pos 4).le
      (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _))))
  have hzline : ((17 / 50 : ℝ) : ℂ) + z.im * Complex.I = z := by
    simpa only [hz] using Complex.re_add_im z
  have hAdd : ‖additiveMellin K S₀ mu P.additive z‖ ≤ A := by
    simpa only [pow_zero, one_mul, hzline] using hadd z.im
  have hDen : ‖mellin P.denominator.toFun w‖ ≤ D := by
    simpa only [pow_zero, one_mul, Complex.re_add_im] using hden w.re w.im hw0 hw1
  rw [div_eq_mul_inv]
  simp only [norm_mul]
  dsimp only [C]
  exact mul_le_mul
    (mul_le_mul
      (mul_le_mul
        (mul_le_mul (by linarith : ‖(physicalPoissonScalar K : ℂ)‖ ≤
          ‖(physicalPoissonScalar K : ℂ)‖ + 1) hGauss
          (norm_nonneg _) (by positivity))
        hAdd (norm_nonneg _) (by positivity))
      hDen (norm_nonneg _) (by positivity))
    (by linarith : ‖(physicalResidueNormalizer K S₀ mu P)⁻¹‖ ≤
      ‖(physicalResidueNormalizer K S₀ mu P)⁻¹‖ + 1)
    (norm_nonneg _) (by positivity)

/-- All factors other than the main prime amplitudes are estimated from
the actual arithmetic data.  Constants and the height degree precede every
scale, bin, row, physical point and positive power-height exponent. -/
theorem exists_actual_physical_kernel_normForm_of_main
    (P : ProbeData K S₀) (psi : HeckeCharacter K) (g : PrimeWindowGeometry)
    (hcal : ThetaCalibrationInput K S₀ P.arithmetic P.Lambda P.G)
    (hpsi : ∀ p : ExteriorPrime K S₀, UnramifiedAt K psi p.val)
    (heightCount : ℕ) {e eps eta nu width : ℝ}
    (he : 0 < e) (he1 : e ≤ 1 / 10000) (heps : 0 < eps)
    (heta : 0 < eta) (hnu : 0 < nu) (hwidth : 0 ≤ width) :
    ∃ A C Z0 : ℝ, 0 ≤ A ∧ 0 < C ∧ 1 ≤ Z0 ∧
      ∀ Z T : ℝ, Z0 ≤ Z → 1 ≤ T →
      ∀ d : ℝ, 1 / 16 ≤ d → d ≤ 1 →
      ∀ u : FrequencyRow K S₀, Z ^ d ≤ frequencyRowNorm K S₀ u →
        frequencyRowNorm K S₀ u ≤ 2 * Z ^ d →
      ∀ a : ℝ, 51 / 100 ≤ a → a ≤ 1 →
      ∀ h : ℕ, h ≤ heightCount →
      rowZeroBelow K S₀ psi {1} P (arithmeticHighEulerData K S₀ P psi) u
        (3 * ((h : ℝ) + 2) * T) (a + 2 * e) →
      ∀ amplitude : Fin g.slots → ℝ, (∀ i, 0 ≤ amplitude i) →
      ∀ s w z : ℂ, s.re = a + 16 * e → w.re = 1 - a - 6 * e → z.re = 17 / 50 →
        |s.im| ≤ T → |w.im| ≤ T →
        (∀ i, ‖actualCompensationMainSlot K S₀ P g ∅ u Z z i‖ ≤
          (primeScale g Z) ^ (-(4 / 25 : ℝ) + amplitude i + width)) →
        ‖compensatedRowMellinKernel K S₀ mu P psi (arithmeticHighEulerData K S₀ P psi)
          g ∅ u Z s w z‖ ≤
          C * Z ^ (NormForm.rowExponent d a ((∑ i, amplitude i) / g.slots) +
            (105 / 8 + 6 * d) * e + d * (2 * eps + (g.slots + 2) * eta) +
              ((width + eta) / 6 + nu)) * (1 + T) ^ A := by
  obtain ⟨CP, hCP, hprofile⟩ := exists_physical_profile_bound K S mu P
  obtain ⟨CL, ZL, hCL, hZL, hratio⟩ := NormFormSharpFactors.exists_actual_threeLFactor_radical_bound
    K S₀ psi {1} (Finset.mem_singleton_self 1) P he he1 heps
  obtain ⟨CE, hCE, heuler⟩ := exists_uniform_rowCorrection_subpower K S₀ he he1 heta
  obtain ⟨CS, ZS, hCS, hZS, hslot⟩ := exists_actualFullSlot_bound_of_main K S₀ g he he1 heta
  obtain ⟨ZF, hZF, hfactor⟩ := exists_actualFullCorrection_product_cutoff K S₀ g he he1
  have hcomplex := HeckeSkeleton.HeckeFiniteBackgroundControl.all_complex_of_primitive12
    K P.arithmetic.primitive12
  obtain ⟨ZN, hZN, hnormalizer⟩ := Expansion.Project.exists_actual_primeNormalizer_inverse_bound
    K S₀ hcomplex g nu hnu
  let A : ℝ := ((2 * Fintype.card (InfinitePlace K) : ℕ) : ℝ) +
    2 * ((2 * Fintype.card (InfinitePlace K) : ℕ) : ℝ) * eps
  let H : ℝ := (3 * ((heightCount : ℝ) + 2) + 2) ^ A
  let D : ℝ := 2 + 2 * eps + (g.slots + 2) * eta
  let CQ : ℝ := CS ^ g.slots * repeatedProductConstant g.slots eta
  let C : ℝ := CP * (CL * H) * CE * CQ * (2 : ℝ) ^ D
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hH : 0 < H := by dsimp only [H]; positivity
  have hCQ : 0 < CQ := mul_pos (pow_pos hCS _) (repeatedProductConstant_pos _ heta)
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  refine ⟨A, C, max ZL (max ZS (max ZF ZN)), hA,
    by dsimp only [C]; positivity, hZL.trans (le_max_left _ _), ?_⟩
  intro Z T hZ hT d hd hd1 u hu hu1 a ha ha1 h hh hbelow amplitude hamp
    s w z hs hw hz hsi hwi hmain
  have hZZL : ZL ≤ Z := (le_max_left _ _).trans hZ
  have hZZS : ZS ≤ Z := (le_max_left _ _).trans ((le_max_right _ _).trans hZ)
  have hZZF : ZF ≤ Z := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hZ))
  have hZZN : ZN ≤ Z := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hZ))
  have hZ1 : 1 ≤ Z := hZL.trans hZZL
  have hZ0 : 0 < Z := zero_lt_one.trans_le hZ1
  let E := arithmeticHighEulerData K S₀ P psi
  let U : ℝ := 3 * ((h : ℝ) + 2) * T
  let profile : ℂ := (physicalPoissonScalar K : ℂ) * Complex.exp ((s + z - 1) ^ 2) *
    additiveMellin K S₀ mu P.additive z * mellin P.denominator.toFun w /
      physicalResidueNormalizer K S₀ mu P
  let ratio : ℂ := heckeDeletedContinuation K 1 (exceptionalPrimes K S₀) (6 * z) *
    heckeDeletedContinuation K (E.rows.character u) (exceptionalPrimes K S₀) w /
    heckeDeletedContinuation K (psi * conjugate (E.rows.character u))
      (exceptionalPrimes K S₀) s
  let euler : ℂ := rowCorrection K S₀ P psi E ∅ u s w z
  let slots : ℂ := ∏ i : Fin g.slots, actualFullCorrectionSlot K S₀ P psi g ∅ u Z s w z i
  have hU0 : 0 ≤ 2 + U := by dsimp only [U]; positivity
  have hTU : T + 3 / 2 ≤ U := by dsimp only [U]; nlinarith [Nat.cast_nonneg h]
  have hheight : (2 + U) ^ A ≤ H * (1 + T) ^ A := by
    have hh' : (h : ℝ) ≤ heightCount := by exact_mod_cast hh
    calc
      _ ≤ ((3 * ((heightCount : ℝ) + 2) + 2) * (1 + T)) ^ A := by
        apply Real.rpow_le_rpow hU0 _ hA
        dsimp only [U]
        nlinarith [Nat.cast_nonneg h, Nat.cast_nonneg heightCount]
      _ = _ := Real.mul_rpow (by positivity) (by positivity)
  have hprof : ‖profile‖ ≤ CP := hprofile s w z (by linarith) (by linarith)
    (by linarith) (by linarith) hz
  have hrat : ‖ratio‖ ≤ (CL * H) *
      (u.ideal.val.val.radical.absNorm : ℝ) ^ (a - 1 / 2 + 6 * e + 2 * eps) *
        (1 + T) ^ A := by
    have hr := hratio Z hZZL d hd u hu a T U ha ha1 (by linarith) hTU hbelow
      s w z hs.ge (by linarith) hw hz hsi hwi
    exact hr.trans ((mul_le_mul_of_nonneg_left hheight
      (mul_nonneg hCL.le (Real.rpow_nonneg (Nat.cast_nonneg _) _))).trans_eq (by ring))
  have heul : ‖euler‖ ≤ CE * frequencyRowNorm K S₀ u ^ eta := by
    simpa only [Finset.card_empty, pow_zero, mul_one] using
      heuler P psi ∅ u a ha ha1 (s, w, z) (swept_contour_mem_tube he le_rfl s w z hs hw hz)
  have hprod : (u.ideal.val.val.radical.absNorm : ℝ) ^ (a - 1 / 2 + 6 * e) * ‖slots‖ ≤
      CQ * frequencyRowNorm K S₀ u ^ (a - 1 / 2 + 6 * e + (g.slots + 1) * eta) *
        Z ^ (-2 / 75 + ((∑ i, amplitude i) / g.slots) / 6 + (width + eta) / 6) :=
    fullSlot_product_of_physical_bounds K S₀ u g ∅ Z CS (width + eta)
      (a - 1 / 2 + 6 * e) eta amplitude
      (fun i => actualFullCorrectionSlot K S₀ P psi g ∅ u Z s w z i)
      hZ0 hCS.le (by linarith) heta
      (fun i => hslot Z hZZS P psi hcal hpsi ∅ u a width ha ha1 hwidth
        s w z hs hw hz i (amplitude i) (hamp i) (hmain i))
  have hR : 0 < (u.ideal.val.val.radical.absNorm : ℝ) :=
    zero_lt_one.trans_le (NormFormSharpFactors.one_le_actual_radicalNorm K S₀ u)
  have hRN : (u.ideal.val.val.radical.absNorm : ℝ) ≤ frequencyRowNorm K S₀ u := by
    simpa only [Finset.prod_empty, one_mul] using
      actual_selected_repeated_product_mul_radicalNorm_le K u.ideal.val ∅ (by simp)
  have hnorm := joint_pointwise_normForm_of_factors Z (frequencyRowNorm K S₀ u)
    (u.ideal.val.val.radical.absNorm : ℝ) d a ((∑ i, amplitude i) / g.slots) e
    (2 * eps) eta ((g.slots + 1) * eta) (width + eta) nu D
    CP (CL * H) CE CQ 1 ((1 + T) ^ A) s w z profile ratio euler slots
    (primeNormalizer K S₀ g ∅ Z)⁻¹ hZ0 hu hu1 hR hRN (by positivity) hD
    (by dsimp only [D]; nlinarith) hCP.le (mul_nonneg hCL.le hH.le) hCE.le hCQ.le
    (by norm_num) (Real.rpow_nonneg (by linarith) _) hs hw hz hprof hrat heul hprod
    (by simpa only [one_mul] using (hnormalizer Z hZZN).2)
  have hid : compensatedRowMellinKernel K S₀ mu P psi E g ∅ u Z s w z =
      NormForm.geometricFactor Z (frequencyRowNorm K S₀ u) s w z * profile * ratio *
        euler * slots * (primeNormalizer K S₀ g ∅ Z)⁻¹ := by
    rw [compensatedRowMellinKernel_factorization K S₀ mu P psi E g ∅ u Z hZ0 s w z,
      hfactor Z hZZF P psi ∅ u a ha ha1 s w z
        (swept_contour_mem_tube he le_rfl s w z hs hw hz)]
    dsimp only [NormForm.geometricFactor, profile, ratio, euler, slots]
    simp only [div_eq_mul_inv, mul_inv]
    ring
  rw [hid]
  convert hnorm using 1 <;> dsimp only [C] <;> congr 2 <;> ring

end HeckeSkeleton.HighBinPhysicalNorm

#print axioms HeckeSkeleton.HighBinPhysicalNorm.exists_physical_profile_bound
#print axioms HeckeSkeleton.HighBinPhysicalNorm.exists_actual_physical_kernel_normForm_of_main
