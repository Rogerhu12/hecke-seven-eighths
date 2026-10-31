import HeckeSkeleton.HighBinSupport.ActualTargetEuler
import HeckeSkeleton.HighBinSupport.ActualBoundaryPresentation
import HeckeSkeleton.HighBinSupport.ActualEulerVerticalAE

/-!
# Boundary transport from the original initial calibration

An existing presentation can use the constructed arithmetic Euler tables
without changing its small parameters, companions, heights, labels, or
pieces. Character uniqueness preserves every fixed row bin; the proved
almost-everywhere contour identity preserves the final-block identification
and the original initial-minus-final boundary.

Consequently the strongest height-free boundary consumer needs the original
`RowEulerCalibrationInput`, rather than equality of provider records. The
companions, height coverage, and retained-block count still have to come
from the genuine expansion construction. No named admitted presentation
is constructed or altered here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HeckeSkeleton.HighBinBoundaryPresentation

open NumberField IsDedekindDomain MeasureTheory Set
open HeckeGeneral.Arithmetic HeckeGeneral.Characters HeckeGeneral.Analysis
open HeckeGeneral.ThetaSkeleton HeckeGeneral.ThetaSkeleton.Physical
open HeckeSkeleton.HighBinContinuation HeckeSkeleton.HighBinActualEuler
open HeckeSkeleton.HighBinActualInitial HeckeSkeleton.HighBinEulerUniqueness
open scoped Classical BigOperators Topology

variable (K : Type) [Field K] [NumberField K]

attribute [local instance] presentationNormOneMeasurable presentationNormOneBorel
  presentationLocalMeasurable presentationLocalBorel presentationLocalHaar

/-- Both original branches of the buffered high bin depend on the
provider only through its already-calibrated row character. -/
theorem highFixedRowBin_eq_of_calibrated (c : TargetContext K)
    (D : ProbeData K ((targetData K c).S : Set (HeightOneSpectrum (𝓞 K))))
    (E₁ E₂ : RowEulerData K _ D) (Θ : Finset (HeckeCharacter K))
    (selectedHeight upperHeight normLower normUpper a e : ℝ) :
    highFixedRowBin K c D E₁ Θ selectedHeight upperHeight normLower normUpper a e =
      highFixedRowBin K c D E₂ Θ selectedHeight upperHeight normLower normUpper a e := by
  unfold highFixedRowBin bufferedPhysicalRowBin
  simp_rw [rowZeroBelow_iff_of_calibrated K _ D (targetCharacter K c) Θ E₁ E₂,
    rowZeroAbove_iff_of_calibrated K _ D (targetCharacter K c) Θ E₁ E₂]

private theorem presentationContour_eq_arithmetic
    (c : TargetContext K) (P : ActualHighPresentation K c)
    (hinit : RowEulerCalibrationInput K _ (targetData K c).probe
      (targetCharacter K c) P.euler)
    (Z T : ℝ) (hZ : 1 ≤ Z) (hT : 1 ≤ T) (b : HighBlockIndex K c Z T)
    (u : HighRow K c) (σ : ℝ)
    (hσ : (((targetData K c).expansion Z T).block b).bin + 15 * P.e < σ) :
    rowContourBox K _ (targetData K c).measures.haar (targetData K c).probe
      (targetCharacter K c) P.euler c.geometry (targetData K c).rayFilter u Z
      (P.contourHeight Z T b) σ
      (1 - (((targetData K c).expansion Z T).block b).bin - 6 * P.e) (17 / 50) =
    rowContourBox K _ (targetData K c).measures.haar (targetData K c).probe
      (targetCharacter K c)
      (arithmeticHighEulerData K _ (targetData K c).probe (targetCharacter K c))
      c.geometry (targetData K c).rayFilter u Z (P.contourHeight Z T b) σ
      (1 - (((targetData K c).expansion Z T).block b).bin - 6 * P.e) (17 / 50) := by
  refine rowContourBox_eq_of_calibrated_sweptTube
    K _ (targetData K c).measures.haar (targetData K c).probe (targetCharacter K c)
    P.euler _ hinit (targetRowEulerCalibrationInput K c)
    c.geometry (targetData K c).rayFilter u Z (P.contourHeight Z T b) σ
    (1 - (((targetData K c).expansion Z T).block b).bin - 6 * P.e) (17 / 50)
    (P.bin_range Z T hZ hT b).1
    ((P.bin_range Z T hZ hT b).2.trans c.family.B_upper)
    P.e_pos (presentation_e_small K c P) ?_
  change (((targetData K c).expansion Z T).block b).bin + 15 * P.e < σ ∧
    1 - (((targetData K c).expansion Z T).block b).bin - 7 * P.e <
      1 - (((targetData K c).expansion Z T).block b).bin - 6 * P.e ∧
    17 / 50 - P.e < 17 / 50
  exact ⟨hσ, by linarith [P.e_pos], by linarith [P.e_pos]⟩

/-- Replace only the Euler provider of an existing calibrated presentation.
All original numeric, row-label, and shifted-piece data remain literally
the same. Its two provider-dependent structural fields are transported
using character uniqueness and equality of the actual contour integrals. -/
def arithmeticPresentationOfCalibration
    (c : TargetContext K) (P : ActualHighPresentation K c)
    (hinit : RowEulerCalibrationInput K _ (targetData K c).probe
      (targetCharacter K c) P.euler) : ActualHighPresentation K c :=
  { P with
    euler := arithmeticHighEulerData K _ (targetData K c).probe (targetCharacter K c)
    rows_in_bin := by
      intro Z T hZ hT b label hlabel
      rw [← highFixedRowBin_eq_of_calibrated K c (targetData K c).probe P.euler
        (arithmeticHighEulerData K _ (targetData K c).probe (targetCharacter K c))
        P.companions (P.selectedHeight Z T b) (P.upperHeight Z T b)
        (Z ^ (((targetData K c).expansion Z T).block b).shell)
        (2 * Z ^ (((targetData K c).expansion Z T).block b).shell)
        (((targetData K c).expansion Z T).block b).bin P.e]
      exact P.rows_in_bin Z T hZ hT b label hlabel
    shifted_identification := by
      intro Z T hZ hT b
      apply (P.shifted_identification Z T hZ hT b).trans
      rw [← highFixedRowBin_eq_of_calibrated K c (targetData K c).probe P.euler
        (arithmeticHighEulerData K _ (targetData K c).probe (targetCharacter K c))
        P.companions (P.selectedHeight Z T b) (P.upperHeight Z T b)
        (Z ^ (((targetData K c).expansion Z T).block b).shell)
        (2 * Z ^ (((targetData K c).expansion Z T).block b).shell)
        (((targetData K c).expansion Z T).block b).bin P.e]
      apply Finset.sum_congr rfl
      intro u _
      exact presentationContour_eq_arithmetic K c P hinit Z T hZ hT b u
        ((((targetData K c).expansion Z T).block b).bin + 16 * P.e)
        (by linarith [P.e_pos]) }

/-- The original initial contour is also preserved by the same provider
transport, while every height and fixed arithmetic row set is unchanged. -/
theorem presentationInitialBlock_eq_arithmeticPresentation
    (c : TargetContext K) (P : ActualHighPresentation K c)
    (hinit : RowEulerCalibrationInput K _ (targetData K c).probe
      (targetCharacter K c) P.euler)
    (Z T : ℝ) (hZ : 1 ≤ Z) (hT : 1 ≤ T) (b : HighBlockIndex K c Z T) :
    presentationInitialBlock K c P Z T b =
      presentationInitialBlock K c (arithmeticPresentationOfCalibration K c P hinit) Z T b := by
  unfold presentationInitialBlock
  dsimp only [arithmeticPresentationOfCalibration]
  rw [← highFixedRowBin_eq_of_calibrated K c (targetData K c).probe P.euler
    (arithmeticHighEulerData K _ (targetData K c).probe (targetCharacter K c))
    P.companions (P.selectedHeight Z T b) (P.upperHeight Z T b)
    (Z ^ (((targetData K c).expansion Z T).block b).shell)
    (2 * Z ^ (((targetData K c).expansion Z T).block b).shell)
    (((targetData K c).expansion Z T).block b).bin P.e]
  apply Finset.sum_congr rfl
  intro u _
  exact presentationContour_eq_arithmetic K c P hinit Z T hZ hT b u
    (c.family.B + 20 * P.e) (by linarith [(P.bin_range Z T hZ hT b).2, P.e_pos])

/-- The actual boundary keeps its original initial-minus-final sign.
Both presentations identify the final sum with the same original block
values, so preservation of the initial sum preserves the whole boundary. -/
theorem wholeBinBoundary_eq_arithmeticPresentation
    (c : TargetContext K) (P : ActualHighPresentation K c)
    (hinit : RowEulerCalibrationInput K _ (targetData K c).probe
      (targetCharacter K c) P.euler)
    (Z T : ℝ) (hZ : 1 ≤ Z) (hT : 1 ≤ T) :
    wholeBinBoundary K c P Z T =
      wholeBinBoundary K c (arithmeticPresentationOfCalibration K c P hinit) Z T := by
  rw [wholeBinBoundary_eq_initialSum_sub_blocks K c P Z T hZ hT,
    wholeBinBoundary_eq_initialSum_sub_blocks K c
      (arithmeticPresentationOfCalibration K c P hinit) Z T hZ hT]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  exact presentationInitialBlock_eq_arithmeticPresentation K c P hinit Z T hZ hT b

/-- Original boundary-control quantifiers, using only the original initial
Euler calibration and the remaining genuine expansion geometry. The old
provider-record equality is discharged by the contour transport above.
The N+k height absorption and retained-block count are inherited unchanged. -/
theorem highBoundaryControl_of_calibrated_lower_geometry
    (c : TargetContext K) (P : ActualHighPresentation K c)
    (hinit : RowEulerCalibrationInput K _ (targetData K c).probe
      (targetCharacter K c) P.euler)
    (hcompanions : 1 ∈ P.companions) (δ : ℝ) (hδ : 0 < δ)
    (AB RB ceiling : ℝ) (hAB : 0 ≤ AB) (hceiling : 0 < ceiling)
    (hgeometry : ∀ τ : ℝ, 0 < τ → τ ≤ ceiling →
      ∃ Cb Zg : ℝ, 0 < Cb ∧ 1 ≤ Zg ∧ ∀ Z : ℝ, Zg ≤ Z →
        (((targetData K c).expansion Z (Z ^ τ)).blockCount : ℝ) ≤
            Cb * Z ^ RB * (1 + Z ^ τ) ^ AB ∧
        ∀ b : HighBlockIndex K c Z (Z ^ τ),
          δ * (Z ^ τ) ≤ P.contourHeight Z (Z ^ τ) b ∧
          P.contourHeight Z (Z ^ τ) b + 3 / 2 ≤ P.upperHeight Z (Z ^ τ) b) :
    HighBoundaryControl K c P := by
  let P' := arithmeticPresentationOfCalibration K c P hinit
  have hb : HighBoundaryControl K c P' :=
    highBoundaryControl_of_arithmetic_lower_geometry K c P' rfl
      hcompanions δ hδ AB RB ceiling hAB hceiling hgeometry
  obtain ⟨A, R, ceiling', hA, hceiling', hbound⟩ := hb
  refine ⟨A, R, ceiling', hA, hceiling', ?_⟩
  intro τ hτ hτc N
  obtain ⟨C, Z0, hC, hZ0, h⟩ := hbound τ hτ hτc N
  refine ⟨C, Z0, hC, hZ0, ?_⟩
  intro Z hZ
  rw [wholeBinBoundary_eq_arithmeticPresentation K c P hinit Z (Z ^ τ)
    (hZ0.trans hZ) (Real.one_le_rpow (hZ0.trans hZ) hτ.le)]
  exact h Z hZ

#print axioms highFixedRowBin_eq_of_calibrated
#print axioms arithmeticPresentationOfCalibration
#print axioms presentationInitialBlock_eq_arithmeticPresentation
#print axioms wholeBinBoundary_eq_arithmeticPresentation
#print axioms highBoundaryControl_of_calibrated_lower_geometry

end HeckeSkeleton.HighBinBoundaryPresentation
