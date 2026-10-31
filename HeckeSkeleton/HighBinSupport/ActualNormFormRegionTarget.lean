import HeckeSkeleton.HighBinSupport.ActualNormFormRegionPacket
import HeckeSkeleton.HighBinSupport.ActualNormFormTarget
import HeckeSkeleton.HighBinSupport.ActualEulerUniqueness

/-!
The original `HighShiftedNormForm` consumes the computed restricted-height
pieces and their label means. Calibrated row characters identify the zero
detector, so no equality of `RowEulerData` records is assumed.

The remaining data are genuine presentation identifications: its chosen
heights, a grid code for each original label, the label's original mean,
and its actual shifted piece. The theorem proves all analytic estimates
internally, including the proved actual prime-window normalization. The
named physical presentation uses the main-polynomial amplitude transport
route in `ActualPhysicalScheduledNorm`; this remains a complete-slot adapter.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HeckeSkeleton.HighBinNormFormRegionTarget

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.HighBinActualEuler HeckeSkeleton.HighBinBoundaryPresentation
open HeckeSkeleton.HighBinEulerUniqueness HeckeSkeleton.HighBinNormFormTarget
open HighBinVerified HighBinVerified.NormFormRegions HighBinVerified.NormFormRegionIntegral
open scoped Classical BigOperators Topology

variable (K : Type) [Field K] [NumberField K]

local instance regionTargetNormOneMeasurable (c : TargetContext K) :
    MeasurableSpace (sLocalNormOneGroup K
      ((targetData K c).S : Set (HeightOneSpectrum (𝓞 K)))) :=
  (targetData K c).measures.normOneSpace

local instance regionTargetNormOneBorel (c : TargetContext K) :
    BorelSpace (sLocalNormOneGroup K
      ((targetData K c).S : Set (HeightOneSpectrum (𝓞 K)))) :=
  (targetData K c).measures.normOneBorel

local instance regionTargetLocalMeasurable (c : TargetContext K)
    (p : ((targetData K c).S : Set (HeightOneSpectrum (𝓞 K)))) :
    MeasurableSpace (p.val.adicCompletion K) :=
  (targetData K c).measures.localSpace p

local instance regionTargetLocalBorel (c : TargetContext K)
    (p : ((targetData K c).S : Set (HeightOneSpectrum (𝓞 K)))) :
    BorelSpace (p.val.adicCompletion K) :=
  (targetData K c).measures.localBorel p

local instance regionTargetLocalHaar (c : TargetContext K)
    (p : ((targetData K c).S : Set (HeightOneSpectrum (𝓞 K)))) :
    ((targetData K c).measures.haar p).IsAddHaarMeasure :=
  (targetData K c).measures.haar_isAddHaar p

/-- A structural interpretation of each original label in the fixed grid.
It is independent of the row and of the integration point. -/
abbrev PresentationRegionLabels (c : TargetContext K) (N : ℕ) :=
  ∀ Z T : ℝ, (b : HighBlockIndex K c Z T) →
    HighLabel K c Z T b → Fin c.geometry.slots → Fin (N + 1)

/-- The exact original norm-form conclusion, now for genuine restricted
pieces. Only height and label/piece identifications remain as hypotheses;
no desired norm, slot, prime, or conductor estimate is supplied. -/
theorem exists_target_highShiftedNormForm_region_connection
    (c : TargetContext K) (P : ActualHighPresentation K c)
    (hcomp : (1 : HeckeCharacter K) ∈ P.companions) :
    ∃ kappa theta : ℝ, ∃ N : ℕ, ∃ C Z0 : ℝ,
      0 < kappa ∧ 0 < theta ∧ 0 < C ∧ 1 ≤ Z0 ∧
      ((∀ Z T : ℝ, Z0 ≤ Z → 1 ≤ T → T ≤ Z ^ kappa →
        ∀ b : HighBlockIndex K c Z T,
          P.contourHeight Z T b = NormForm.internalHeight Z T kappa) →
      (∀ Z T : ℝ, Z0 ≤ Z → 1 ≤ T → T ≤ Z ^ kappa →
        ∀ b : HighBlockIndex K c Z T,
          2 * NormForm.internalHeight Z T kappa + 2 ≤ P.upperHeight Z T b) →
      ∀ code : PresentationRegionLabels K c N,
        (∀ (Z T : ℝ), Z0 ≤ Z → 1 ≤ T → T ≤ Z ^ kappa →
          ∀ (b : HighBlockIndex K c Z T) (label : HighLabel K c Z T b),
          label ∈ P.labels Z T b →
          ((((targetData K c).expansion Z T).block b).amplitudeSet label).mean =
            actualRegionMean c.geometry (((targetData K c).expansion Z T).block b).bin
              theta N (code Z T b label)) →
        (∀ (Z T : ℝ), Z0 ≤ Z → 1 ≤ T → T ≤ Z ^ kappa →
          ∀ (b : HighBlockIndex K c Z T) (label : HighLabel K c Z T b),
          label ∈ P.labels Z T b → ∀ u : HighRow K c,
          u ∈ ((((targetData K c).expansion Z T).block b).amplitudeSet label).rows →
          P.shiftedPiece Z T b label u =
            actualRegionPiece K (targetData K c).S (targetData K c).measures.haar
              (targetData K c).probe (targetCharacter K c) c.geometry u Z
              (((targetData K c).expansion Z T).block b).bin P.e
              (P.contourHeight Z T b) theta N (code Z T b label)) →
        HighShiftedNormForm K c P) := by
  classical
  have heLam : P.e ≤ c.lamB / 100 := by
    linarith [P.e_small, min_le_right c.family.lamA c.lamB]
  obtain ⟨kappa, theta, N, C, Z0, hkappa, htheta, hC, hZ0, hrow⟩ :=
    exists_actual_region_normForm_quarter_loss K (targetData K c).S
      (targetData K c).measures.haar (targetCharacter K c) P.companions hcomp
      (targetData K c).probe c.geometry (arithmeticCalibration K c)
      (fun p => target_unramified_outside K c p.val p.property)
      P.e_pos (presentation_e_small K c P) c.lamB_pos heLam
  refine ⟨kappa, theta, N, C, Z0, hkappa, htheta, hC, hZ0, ?_⟩
  intro hheight hupper code hmean hpiece
  apply HighShiftedNormForm.of_uniform K c P
  refine ⟨0, C, kappa, Z0, le_rfl, hC, hkappa, hZ0, ?_⟩
  intro Z T hZ hT hTcap b label hlabel
  have hZ1 : 1 ≤ Z := hZ0.trans hZ
  calc
    (∑ u ∈ ((((targetData K c).expansion Z T).block b).amplitudeSet label).rows,
      ‖P.shiftedPiece Z T b label u‖) ≤
        ∑ _u ∈ ((((targetData K c).expansion Z T).block b).amplitudeSet label).rows,
          C * Z ^ (highRowExponent K c Z T b label + c.lamB / 4) := by
      apply Finset.sum_le_sum
      intro u hu
      have hmem := P.rows_in_bin Z T hZ1 hT b label hu
      have hdata := highFixedRowBin_member_data K c (targetData K c).probe P.euler
        P.companions (P.selectedHeight Z T b) (P.upperHeight Z T b)
        (Z ^ (((targetData K c).expansion Z T).block b).shell)
        (2 * Z ^ (((targetData K c).expansion Z T).block b).shell)
        (((targetData K c).expansion Z T).block b).bin P.e u hmem
      have hNu : frequencyRowNorm K _ u ≤
          2 * Z ^ (((targetData K c).expansion Z T).block b).shell :=
        HighBinBoundary.ActualEstimate.frequencyRowNorm_le_of_mem_rows K _
          (mul_nonneg (by norm_num) (Real.rpow_nonneg (zero_le_one.trans hZ1) _)) u hdata.1
      have hbelowOld : rowZeroBelow K _ (targetCharacter K c) P.companions
          (targetData K c).probe
          (arithmeticHighEulerData K _ (targetData K c).probe (targetCharacter K c))
          u (P.upperHeight Z T b)
          ((((targetData K c).expansion Z T).block b).bin + 2 * P.e) :=
        (rowZeroBelow_iff_of_calibrated K _ (targetData K c).probe
          (targetCharacter K c) P.companions P.euler _ u (P.upperHeight Z T b)
          ((((targetData K c).expansion Z T).block b).bin + 2 * P.e)).mp hdata.2.2
      have hbelow : rowZeroBelow K _ (targetCharacter K c) P.companions
          (targetData K c).probe
          (arithmeticHighEulerData K _ (targetData K c).probe (targetCharacter K c))
          u (2 * NormForm.internalHeight Z T kappa + 2)
          ((((targetData K c).expansion Z T).block b).bin + 2 * P.e) := by
        intro chi hchi rho hord hlo hhi him
        exact hbelowOld chi hchi rho hord hlo hhi
          (him.trans (hupper Z T hZ hT hTcap b))
      have hrowu := hrow Z T hZ hT hTcap
        (((targetData K c).expansion Z T).block b).shell
        (P.shell_range Z T hZ1 hT b).1 (presentation_shell_le_one K c P Z T hZ1 hT b)
        u hdata.2.1.le hNu (((targetData K c).expansion Z T).block b).bin
        (P.bin_range Z T hZ1 hT b).1
        ((P.bin_range Z T hZ1 hT b).2.trans c.family.B_upper) hbelow
      have hb := (hrowu.1 (code Z T b label)).2.2.2
      rw [← hmean Z T hZ hT hTcap b label hlabel,
        actual_rowExponent_eq_highRowExponent K c Z T b label] at hb
      rw [hpiece Z T hZ hT hTcap b label hlabel u hu,
        hheight Z T hZ hT hTcap b]
      exact hb
    _ = C * (((((targetData K c).expansion Z T).block b).amplitudeSet label).rows.card : ℝ) *
        Z ^ (highRowExponent K c Z T b label + c.lamB / 4) * (1 + T) ^ (0 : ℝ) := by
      simp only [Finset.sum_const, nsmul_eq_mul, Real.rpow_zero, mul_one]
      ring

end HeckeSkeleton.HighBinNormFormRegionTarget

#print axioms HeckeSkeleton.HighBinNormFormRegionTarget.exists_target_highShiftedNormForm_region_connection
