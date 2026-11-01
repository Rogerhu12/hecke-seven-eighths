import HeckeSkeleton.HighBinSupport.ActualNormFormIntegral
import HeckeSkeleton.HighBinSupport.ActualBoundaryPresentation

/-!
# The norm form for the repository's actual target

The target's ray filter is definitionally empty. The actual probe, Haar
measures, target character, arithmetic calibration, and unramified-outside-S
theorem therefore instantiate the complete-slot integral estimate directly.

The final theorem constructs the amplitude witnesses on the original
presentation's retained label rows. Its remaining assumptions identify the
chosen heights, the original label means, and the literal shifted pieces.
No row estimate, integral estimate, or externally supplied amplitude bound
is a premise. The conclusion is the original `HighShiftedNormForm` type.

This is a conditional adapter for complete-slot amplitudes. Its original
prime normalizer is now bounded by the proved actual prime-window theorem.
The named physical presentation uses the separate main-amplitude transport
route in `ActualPhysicalScheduledNorm`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HeckeSkeleton.HighBinNormFormTarget

open NumberField IsDedekindDomain MeasureTheory
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.HighBinActualEuler HeckeSkeleton.HighBinBoundaryPresentation
open HighBinVerified HighBinVerified.NormFormAmplitudeGrid
open scoped Classical BigOperators Topology

variable (K : Type) [Field K] [NumberField K]

local instance targetNormOneMeasurable (c : TargetContext K) :
    MeasurableSpace (sLocalNormOneGroup K
      ((targetData K c).S : Set (HeightOneSpectrum (𝓞 K)))) :=
  (targetData K c).measures.normOneSpace

local instance targetNormOneBorel (c : TargetContext K) :
    BorelSpace (sLocalNormOneGroup K
      ((targetData K c).S : Set (HeightOneSpectrum (𝓞 K)))) :=
  (targetData K c).measures.normOneBorel

local instance targetLocalMeasurable (c : TargetContext K)
    (p : ((targetData K c).S : Set (HeightOneSpectrum (𝓞 K)))) :
    MeasurableSpace (p.val.adicCompletion K) :=
  (targetData K c).measures.localSpace p

local instance targetLocalBorel (c : TargetContext K)
    (p : ((targetData K c).S : Set (HeightOneSpectrum (𝓞 K)))) :
    BorelSpace (p.val.adicCompletion K) :=
  (targetData K c).measures.localBorel p

local instance targetLocalHaar (c : TargetContext K)
    (p : ((targetData K c).S : Set (HeightOneSpectrum (𝓞 K)))) :
    ((targetData K c).measures.haar p).IsAddHaarMeasure :=
  (targetData K c).measures.haar_isAddHaar p

/-- The actual target uses all primes outside S. No extra finite-character
filter remains to be estimated. -/
@[simp] theorem targetData_rayFilter_eq_empty (c : TargetContext K) :
    (targetData K c).rayFilter = (∅ : Finset (HeckeCharacter K)) := rfl

/-- The literal target row integral, with its original ray filter. All
arithmetic calibration and outside-S unramifiedness inputs are discharged
by the target's own constructors. -/
theorem exists_target_rowContour_normForm_quarter_loss
    (c : TargetContext K) (companions : Finset (HeckeCharacter K))
    (hcomp : (1 : HeckeCharacter K) ∈ companions)
    {e : ℝ} (he : 0 < e) (he1 : e ≤ 1 / 10000) (heLam : e ≤ c.lamB / 100) :
    ∃ kappa theta : ℝ, ∃ N : ℕ, ∃ C Z0 : ℝ,
      0 < kappa ∧ 0 < theta ∧ 0 < C ∧ 1 ≤ Z0 ∧
      ∀ Z T : ℝ, Z0 ≤ Z → 1 ≤ T → T ≤ Z ^ kappa →
      ∀ d : ℝ, (1 / 16 : ℝ) ≤ d → d ≤ 1 →
      ∀ u : HighRow K c, Z ^ d ≤ frequencyRowNorm K _ u →
        frequencyRowNorm K _ u ≤ 2 * Z ^ d →
      ∀ a : ℝ, 51 / 100 ≤ a → a ≤ 1 →
      rowZeroBelow K _ (targetCharacter K c) companions (targetData K c).probe
        (arithmeticHighEulerData K _ (targetData K c).probe (targetCharacter K c)) u
        (2 * NormForm.internalHeight Z T kappa + 2) (a + 2 * e) →
      ∃ A : ActualFullSlotAmplitude K _ (targetData K c).probe
          (targetCharacter K c) c.geometry u Z a e
          (NormForm.internalHeight Z T kappa) theta N,
        ‖rowContourBox K _ (targetData K c).measures.haar (targetData K c).probe
            (targetCharacter K c)
            (arithmeticHighEulerData K _ (targetData K c).probe (targetCharacter K c))
            c.geometry (targetData K c).rayFilter u Z
            (NormForm.internalHeight Z T kappa) (a + 16 * e) (1 - a - 6 * e) (17 / 50)‖ ≤
          C * Z ^ (NormForm.rowExponent d a (ActualFullSlotAmplitude.mean K _ A) + c.lamB / 4) := by
  exact NormFormIntegral.exists_actual_rowContour_normForm_quarter_loss
    K (targetData K c).S (targetData K c).measures.haar
    (targetCharacter K c) companions hcomp (targetData K c).probe c.geometry
    (arithmeticCalibration K c)
    (fun p => target_unramified_outside K c p.val p.property)
    he he1 c.lamB_pos heLam

/-- Only a dependent family of actual complete-slot amplitude witnesses.
The theorem below constructs this family; callers do not supply its upper
or lower analytic fields. The indices are the original retained rows. -/
abbrev PresentationFullSlotAmplitudes
    (c : TargetContext K) (P : ActualHighPresentation K c)
    (kappa theta : ℝ) (N : ℕ) (Z0 : ℝ) :=
  ∀ Z T : ℝ, Z0 ≤ Z → 1 ≤ T → T ≤ Z ^ kappa →
    ∀ b : HighBlockIndex K c Z T,
    ∀ ℓ : HighLabel K c Z T b, ℓ ∈ P.labels Z T b →
    ∀ u : HighRow K c,
      u ∈ ((((targetData K c).expansion Z T).block b).amplitudeSet ℓ).rows →
      ActualFullSlotAmplitude K _ (targetData K c).probe (targetCharacter K c)
        c.geometry u Z (((targetData K c).expansion Z T).block b).bin P.e
        (NormForm.internalHeight Z T kappa) theta N

/-- Agreement with the repository's exact moderate-row exponent. -/
theorem actual_rowExponent_eq_highRowExponent
    (c : TargetContext K) (Z T : ℝ) (b : HighBlockIndex K c Z T)
    (ℓ : HighLabel K c Z T b) :
    NormForm.rowExponent (((targetData K c).expansion Z T).block b).shell
        (((targetData K c).expansion Z T).block b).bin
        ((((targetData K c).expansion Z T).block b).amplitudeSet ℓ).mean =
      highRowExponent K c Z T b ℓ := by
  unfold NormForm.rowExponent highRowExponent HeckeGeneral.Analysis.moderateExponent
  ring

/-- A consumer with the original `HighShiftedNormForm` conclusion.

The parameters and constants are chosen first. Once the presentation's
contour and detector heights agree with this choice, its retained rows
receive actual full-slot witnesses, constructed by the integral theorem.
Only the original label-mean identity and literal row-piece identity remain
as assumptions. In particular neither the desired row bound nor any field
of `ActualFullSlotAmplitude` is supplied as a premise.

Labels are allowed to overlap, as in the original presentation. The proof
estimates each label's original finite row sum separately, without assuming
a partition or adding any row-count estimate. -/
theorem exists_target_highShiftedNormForm_connection
    (c : TargetContext K) (P : ActualHighPresentation K c)
    (hEuler : P.euler = arithmeticHighEulerData K _
      (targetData K c).probe (targetCharacter K c))
    (hcomp : (1 : HeckeCharacter K) ∈ P.companions) :
    ∃ kappa theta : ℝ, ∃ N : ℕ, ∃ C Z0 : ℝ,
      0 < kappa ∧ 0 < theta ∧ 0 < C ∧ 1 ≤ Z0 ∧
      ((∀ Z T : ℝ, Z0 ≤ Z → 1 ≤ T → T ≤ Z ^ kappa →
        ∀ b : HighBlockIndex K c Z T,
          P.contourHeight Z T b = NormForm.internalHeight Z T kappa) →
      (∀ Z T : ℝ, Z0 ≤ Z → 1 ≤ T → T ≤ Z ^ kappa →
        ∀ b : HighBlockIndex K c Z T,
          2 * NormForm.internalHeight Z T kappa + 2 ≤ P.upperHeight Z T b) →
      ∃ A : PresentationFullSlotAmplitudes K c P kappa theta N Z0,
        (∀ (Z T : ℝ) (hZ : Z0 ≤ Z) (hT : 1 ≤ T) (hTcap : T ≤ Z ^ kappa)
          (b : HighBlockIndex K c Z T) (ℓ : HighLabel K c Z T b)
          (hℓ : ℓ ∈ P.labels Z T b) (u : HighRow K c)
          (hu : u ∈ ((((targetData K c).expansion Z T).block b).amplitudeSet ℓ).rows),
          ((((targetData K c).expansion Z T).block b).amplitudeSet ℓ).mean =
            ActualFullSlotAmplitude.mean K _ (A Z T hZ hT hTcap b ℓ hℓ u hu)) →
        (∀ (Z T : ℝ) (_hZ : Z0 ≤ Z) (_hT : 1 ≤ T) (_hTcap : T ≤ Z ^ kappa)
          (b : HighBlockIndex K c Z T) (ℓ : HighLabel K c Z T b)
          (_hℓ : ℓ ∈ P.labels Z T b) (u : HighRow K c)
          (_hu : u ∈ ((((targetData K c).expansion Z T).block b).amplitudeSet ℓ).rows),
          P.shiftedPiece Z T b ℓ u =
            rowContourBox K _ (targetData K c).measures.haar (targetData K c).probe
              (targetCharacter K c) P.euler c.geometry (targetData K c).rayFilter u Z
              (P.contourHeight Z T b)
              ((((targetData K c).expansion Z T).block b).bin + 16 * P.e)
              (1 - (((targetData K c).expansion Z T).block b).bin - 6 * P.e) (17 / 50)) →
        HighShiftedNormForm K c P) := by
  classical
  have heLam : P.e ≤ c.lamB / 100 := by
    linarith [P.e_small, min_le_right c.family.lamA c.lamB]
  obtain ⟨kappa, theta, N, C, Z0, hkappa, htheta, hC, hZ0, hrow⟩ :=
    exists_target_rowContour_normForm_quarter_loss K c P.companions hcomp
      P.e_pos (presentation_e_small K c P) heLam
  refine ⟨kappa, theta, N, C, Z0, hkappa, htheta, hC, hZ0, ?_⟩
  intro hheight hupper
  have hrowChosen (Z T : ℝ) (hZ : Z0 ≤ Z) (hT : 1 ≤ T)
      (hTcap : T ≤ Z ^ kappa) (b : HighBlockIndex K c Z T)
      (ℓ : HighLabel K c Z T b) (hℓ : ℓ ∈ P.labels Z T b)
      (u : HighRow K c)
      (hu : u ∈ ((((targetData K c).expansion Z T).block b).amplitudeSet ℓ).rows) :
      ∃ A : ActualFullSlotAmplitude K _ (targetData K c).probe
          (targetCharacter K c) c.geometry u Z
          (((targetData K c).expansion Z T).block b).bin P.e
          (NormForm.internalHeight Z T kappa) theta N,
        ‖rowContourBox K _ (targetData K c).measures.haar (targetData K c).probe
            (targetCharacter K c)
            (arithmeticHighEulerData K _ (targetData K c).probe (targetCharacter K c))
            c.geometry (targetData K c).rayFilter u Z
            (NormForm.internalHeight Z T kappa)
            ((((targetData K c).expansion Z T).block b).bin + 16 * P.e)
            (1 - (((targetData K c).expansion Z T).block b).bin - 6 * P.e) (17 / 50)‖ ≤
          C * Z ^ (NormForm.rowExponent
            (((targetData K c).expansion Z T).block b).shell
            (((targetData K c).expansion Z T).block b).bin
            (ActualFullSlotAmplitude.mean K _ A) + c.lamB / 4) := by
    have hZ1 : 1 ≤ Z := hZ0.trans hZ
    have hmem := P.rows_in_bin Z T hZ1 hT b ℓ hu
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
        ((((targetData K c).expansion Z T).block b).bin + 2 * P.e) := by
      simpa only [hEuler] using hdata.2.2
    have hbelow : rowZeroBelow K _ (targetCharacter K c) P.companions
        (targetData K c).probe
        (arithmeticHighEulerData K _ (targetData K c).probe (targetCharacter K c))
        u (2 * NormForm.internalHeight Z T kappa + 2)
        ((((targetData K c).expansion Z T).block b).bin + 2 * P.e) := by
      intro chi hchi rho hord hlo hhi him
      exact hbelowOld chi hchi rho hord hlo hhi
        (him.trans (hupper Z T hZ hT hTcap b))
    exact hrow Z T hZ hT hTcap
      (((targetData K c).expansion Z T).block b).shell
      (P.shell_range Z T hZ1 hT b).1 (presentation_shell_le_one K c P Z T hZ1 hT b)
      u hdata.2.1.le hNu (((targetData K c).expansion Z T).block b).bin
      (P.bin_range Z T hZ1 hT b).1
      ((P.bin_range Z T hZ1 hT b).2.trans c.family.B_upper) hbelow
  choose A hA using hrowChosen
  refine ⟨A, ?_⟩
  intro hmean hpiece
  apply HighShiftedNormForm.of_uniform K c P
  refine ⟨0, C, kappa, Z0, le_rfl, hC, hkappa, hZ0, ?_⟩
  intro Z T hZ hT hTcap b ℓ hℓ
  calc
    (∑ u ∈ ((((targetData K c).expansion Z T).block b).amplitudeSet ℓ).rows,
      ‖P.shiftedPiece Z T b ℓ u‖) ≤
        ∑ _u ∈ ((((targetData K c).expansion Z T).block b).amplitudeSet ℓ).rows,
          C * Z ^ (highRowExponent K c Z T b ℓ + c.lamB / 4) := by
      apply Finset.sum_le_sum
      intro u hu
      have hb := hA Z T hZ hT hTcap b ℓ hℓ u hu
      rw [← hmean Z T hZ hT hTcap b ℓ hℓ u hu,
        actual_rowExponent_eq_highRowExponent K c Z T b ℓ] at hb
      rw [hpiece Z T hZ hT hTcap b ℓ hℓ u hu,
        hEuler, hheight Z T hZ hT hTcap b]
      exact hb
    _ = C * (((((targetData K c).expansion Z T).block b).amplitudeSet ℓ).rows.card : ℝ) *
        Z ^ (highRowExponent K c Z T b ℓ + c.lamB / 4) * (1 + T) ^ (0 : ℝ) := by
      simp only [Finset.sum_const, nsmul_eq_mul, Real.rpow_zero, mul_one]
      ring

end HeckeSkeleton.HighBinNormFormTarget

#print axioms HeckeSkeleton.HighBinNormFormTarget.targetData_rayFilter_eq_empty
#print axioms HeckeSkeleton.HighBinNormFormTarget.exists_target_rowContour_normForm_quarter_loss
#print axioms HeckeSkeleton.HighBinNormFormTarget.actual_rowExponent_eq_highRowExponent
#print axioms HeckeSkeleton.HighBinNormFormTarget.exists_target_highShiftedNormForm_connection
